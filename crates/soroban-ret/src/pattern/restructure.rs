//! Exact re-structuring of multi-level forward branches (issue #74).
//!
//! The lifter walks a structured body in order. A `br`/`br_if` it has no
//! special handler for is consumed as a no-op (`lift_instruction`), so the
//! branch's condition, the exit it takes and the code it skips all vanish —
//! and the code after an unconditional `br` runs as if it followed on the same
//! path. The handlers it does have cover a `br_if 0` at the top of a block
//! body; a branch out of a NESTED construct (`br k`, `k >= 1`) — what LLVM
//! emits for nested `if`s whose paths join, and for a guard deep in a body —
//! has none. `test_liquidity_pool`'s `deposit` rendered one straight path
//! through code that has six, transferring `desired_a * reserve_b /
//! reserve_a` on every path, with all four of its `panic!` guards gone and no
//! `todo!()` anywhere.
//!
//! This pass rewrites the joins such branches make into a shape the lifter
//! handles. A `block` that a multi-level branch reaches, and whose
//! continuation does not just trap, is a join of several paths. Its body is
//! rewritten into an equivalent branch-free tree of straight-line runs and
//! `IfElse` nodes (marked [`EXACT_IF`]), which the lifter lifts per arm and
//! merges exactly (`reconcile_exact_branch_locals`). Inside it, a branch to an
//! outer label whose continuation only traps becomes `if c { <that trap tail>
//! }`; a branch to any other outer label makes the region refuse.
//!
//! The caller chooses which regions to rewrite (`user_call`); the lifter
//! passes "calls an `i128` soft-arith helper", because every other
//! multi-level join in the corpus is an SDK idiom its recognizers read off
//! the original shape. A guard (a multi-level branch to a trapping label)
//! outside a rewritten region is left alone for the same reason: the SDK's
//! own overflow and marshalling checks take that shape too. The lifter also
//! keeps a rewrite only when the lift of the rewritten body passes its
//! acceptance checks (see `lift_function_body`).
//!
//! The region rewrite is a pure control-flow transformation: the body becomes
//! a CFG of straight-line runs, and each conditional branch is emitted as
//! `if c { taken-arm } else { fall-arm }` followed by the code from the
//! branch's immediate post-dominator onwards. Paths that can only end in a
//! trap are left out of the post-dominator computation, so a guard becomes
//! `if c { …; unreachable }` and the code after it stays at the same level. A
//! node reached on more than one path that is not a join point is copied into
//! each arm — still exact, since exactly one path runs. Anything that cannot
//! be modelled exactly (a loop a branch leaves, `br_table`, a value-typed
//! block, a copy budget overrun) refuses, and the body is left as it was.

use std::collections::HashMap;

use super::structurize::StructuredBlock;
use crate::wasm::ir::{BlockType, WasmInstr};

/// The block type every `IfElse` this pass creates carries, so the lifter can
/// tell its arms are exact paths (see `reconcile_exact_branch_locals`).
/// `FuncType(u32::MAX)` names no real type and reads as "no result" to every
/// check that looks for `Value(_)`.
pub const EXACT_IF: BlockType = BlockType::FuncType(u32::MAX);

/// True when `bt` is [`EXACT_IF`].
pub fn is_exact_if(bt: &BlockType) -> bool {
    matches!(bt, BlockType::FuncType(u32::MAX))
}

/// True when an arm this pass emitted cannot fall through: it ends in a
/// `return` or a trap (every arm ends at a join, an exit, or one of those).
pub fn arm_terminates(arm: &[StructuredBlock]) -> bool {
    match arm.last() {
        Some(StructuredBlock::Instruction(WasmInstr::Return | WasmInstr::Unreachable))
        | Some(StructuredBlock::SafetyNetUnreachable) => true,
        Some(StructuredBlock::IfElse {
            block_type,
            then_body,
            else_body,
        }) if is_exact_if(block_type) => arm_terminates(then_body) && arm_terminates(else_body),
        _ => false,
    }
}

/// How a straight-line run ends.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Term {
    /// Falls through / jumps to another node.
    Goto(usize),
    /// `br_if`/`if`: pops a condition; non-zero → `taken`, zero → `fall`.
    Cond { taken: usize, fall: usize },
    /// `br_table` (analysis only).
    Multi(Vec<usize>),
    /// A loop kept whole, with the labels it can leave to (analysis only).
    Opaque(Vec<usize>),
    /// `return`, or the end of the function body.
    Return,
    /// Falls out of the region being rewritten.
    Exit,
    /// `unreachable` (or a safety-net trap).
    Trap,
    /// An outer label a rewritten region may not branch to.
    Refuse,
}

impl Term {
    fn succs(&self) -> Vec<usize> {
        match self {
            Term::Goto(s) => vec![*s],
            Term::Cond { taken, fall } => vec![*taken, *fall],
            Term::Multi(v) | Term::Opaque(v) => v.clone(),
            Term::Return | Term::Exit | Term::Trap | Term::Refuse => Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
struct Node {
    instrs: Vec<StructuredBlock>,
    term: Term,
}

/// Why a region rewrite refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refusal {
    BrTable,
    ValueBlock,
    EscapingLoop,
    OuterJoin,
    CopyBudget,
}

/// A label on the builder's stack: the node a branch to it reaches, and the
/// `block` it belongs to (`None` for the function end, an `if` or a loop).
#[derive(Clone, Copy)]
struct Label {
    node: usize,
    block: Option<*const StructuredBlock>,
}

/// A multi-level branch found while building.
#[derive(Clone, Copy)]
struct Far {
    target: Label,
}

struct Builder {
    nodes: Vec<Node>,
    /// Analysis mode tolerates everything (it only feeds the must-trap and
    /// label maps); exact mode refuses what it cannot rewrite.
    analysis: bool,
    far: Vec<Far>,
}

impl Builder {
    fn push(&mut self, instrs: Vec<StructuredBlock>, term: Term) -> usize {
        self.nodes.push(Node { instrs, term });
        self.nodes.len() - 1
    }

    /// Build the nodes for `seq`, continuing at node `next` when it falls off
    /// its end. `labels[labels.len() - 1 - k]` is what a `br k` reaches.
    /// Returns the entry node of `seq`. Nodes are created successors-first,
    /// so ascending index order is a reverse topological order.
    fn build(
        &mut self,
        seq: &[StructuredBlock],
        next: usize,
        labels: &mut Vec<Label>,
    ) -> Result<usize, Refusal> {
        // Walk backwards, so every successor exists before its predecessor.
        let mut instrs: Vec<StructuredBlock> = Vec::new();
        let mut term = Term::Goto(next);
        let at = |labels: &Vec<Label>, k: u32| -> Label { labels[labels.len() - 1 - k as usize] };
        for item in seq.iter().rev() {
            match item {
                StructuredBlock::Instruction(WasmInstr::Return) => {
                    // Whatever followed is dead.
                    instrs = vec![item.clone()];
                    term = Term::Return;
                }
                StructuredBlock::Instruction(WasmInstr::Unreachable)
                | StructuredBlock::SafetyNetUnreachable => {
                    instrs = vec![item.clone()];
                    term = Term::Trap;
                }
                StructuredBlock::Instruction(WasmInstr::Br(k)) => {
                    let target = at(labels, *k);
                    if *k >= 1 {
                        self.far.push(Far { target });
                    }
                    instrs = Vec::new();
                    term = Term::Goto(target.node);
                }
                StructuredBlock::Instruction(WasmInstr::BrIf(k)) => {
                    let target = at(labels, *k);
                    if *k >= 1 {
                        self.far.push(Far { target });
                    }
                    instrs.reverse();
                    let fall = self.push(std::mem::take(&mut instrs), term);
                    term = Term::Cond {
                        taken: target.node,
                        fall,
                    };
                }
                StructuredBlock::Instruction(WasmInstr::BrTable { targets, default }) => {
                    if !self.analysis {
                        return Err(Refusal::BrTable);
                    }
                    instrs = Vec::new();
                    term = Term::Multi(
                        targets
                            .iter()
                            .chain(std::iter::once(default))
                            .map(|k| at(labels, *k).node)
                            .collect(),
                    );
                }
                StructuredBlock::Instruction(_) => instrs.push(item.clone()),
                StructuredBlock::Block { block_type, body } => {
                    if !self.analysis && !matches!(block_type, BlockType::Empty) {
                        return Err(Refusal::ValueBlock);
                    }
                    instrs.reverse();
                    let after = self.push(std::mem::take(&mut instrs), term);
                    labels.push(Label {
                        node: after,
                        block: Some(item),
                    });
                    let entry = self.build(body, after, labels);
                    labels.pop();
                    term = Term::Goto(entry?);
                }
                StructuredBlock::IfElse {
                    block_type,
                    then_body,
                    else_body,
                } => {
                    if !self.analysis && !matches!(block_type, BlockType::Empty) {
                        return Err(Refusal::ValueBlock);
                    }
                    instrs.reverse();
                    let after = self.push(std::mem::take(&mut instrs), term);
                    labels.push(Label {
                        node: after,
                        block: None,
                    });
                    let taken = self.build(then_body, after, labels);
                    let fall = self.build(else_body, after, labels);
                    labels.pop();
                    term = Term::Cond {
                        taken: taken?,
                        fall: fall?,
                    };
                }
                StructuredBlock::Loop { body, .. } => {
                    // A loop is kept whole, as an opaque instruction. That is
                    // exact only when nothing inside it leaves it by branch.
                    let mut escapes = Vec::new();
                    loop_escapes(body, 0, &mut escapes);
                    if escapes.is_empty() {
                        instrs.push(item.clone());
                    } else if self.analysis {
                        instrs.reverse();
                        let after = self.push(std::mem::take(&mut instrs), term);
                        let mut succs = vec![after];
                        succs.extend(
                            escapes
                                .iter()
                                .map(|j| labels[labels.len() - 1 - *j as usize].node),
                        );
                        instrs = vec![item.clone()];
                        term = Term::Opaque(succs);
                        let id = self.push(std::mem::take(&mut instrs), term);
                        term = Term::Goto(id);
                    } else {
                        return Err(Refusal::EscapingLoop);
                    }
                }
            }
        }
        instrs.reverse();
        Ok(self.push(instrs, term))
    }
}

/// Outer labels (0 = innermost outside the loop) that a branch inside a loop
/// body leaves to. `depth` counts labels between the branch and the loop's own
/// label (which is depth 0 at the loop body's top level).
fn loop_escapes(body: &[StructuredBlock], depth: u32, out: &mut Vec<u32>) {
    fn note(k: u32, depth: u32, out: &mut Vec<u32>) {
        if k > depth {
            let j = k - depth - 1;
            if !out.contains(&j) {
                out.push(j);
            }
        }
    }
    for b in body {
        match b {
            StructuredBlock::Instruction(WasmInstr::Br(k) | WasmInstr::BrIf(k)) => {
                note(*k, depth, out)
            }
            StructuredBlock::Instruction(WasmInstr::BrTable { targets, default }) => {
                for k in targets.iter().chain(std::iter::once(default)) {
                    note(*k, depth, out);
                }
            }
            StructuredBlock::Block { body, .. } | StructuredBlock::Loop { body, .. } => {
                loop_escapes(body, depth + 1, out)
            }
            StructuredBlock::IfElse {
                then_body,
                else_body,
                ..
            } => {
                loop_escapes(then_body, depth + 1, out);
                loop_escapes(else_body, depth + 1, out);
            }
            _ => {}
        }
    }
}

/// `must_trap[i]`: every path from node `i` ends in a trap.
fn must_trap(nodes: &[Node]) -> Vec<bool> {
    let mut mt = vec![false; nodes.len()];
    for i in 0..nodes.len() {
        mt[i] = match &nodes[i].term {
            Term::Trap => true,
            Term::Return | Term::Exit | Term::Refuse | Term::Opaque(_) => false,
            t => t.succs().iter().all(|&s| mt[s]),
        };
    }
    mt
}

/// The straight-line instructions from `node` to the trap that ends them, if
/// that is all there is (no branch on the way).
fn trap_tail(nodes: &[Node], mut node: usize) -> Option<Vec<StructuredBlock>> {
    let mut out = Vec::new();
    loop {
        out.extend(nodes[node].instrs.iter().cloned());
        match nodes[node].term {
            Term::Goto(s) => node = s,
            Term::Trap => return Some(out),
            _ => return None,
        }
    }
}

/// Emit the branch-free tree for the nodes reachable from `entry`, as
/// described in the module docs.
fn emit_tree(nodes: &[Node], entry: usize) -> Result<Vec<StructuredBlock>, Refusal> {
    let n = nodes.len();
    let mt = must_trap(nodes);
    if (0..n).any(|i| {
        nodes[i]
            .term
            .succs()
            .iter()
            .any(|&s| nodes[s].term == Term::Refuse)
    }) {
        // Only reachable nodes matter, but an unreachable predecessor of a
        // refused label is rare enough to refuse on as well.
        return Err(Refusal::OuterJoin);
    }

    // Post-dominator sets over the graph with every edge into a must-trap
    // node removed (a guard's trap arm is not a path the join waits for).
    const EXIT: usize = usize::MAX;
    let mut pdom: Vec<Option<Vec<bool>>> = vec![None; n];
    for i in 0..n {
        if mt[i] {
            continue;
        }
        let live: Vec<usize> = nodes[i]
            .term
            .succs()
            .into_iter()
            .filter(|&s| !mt[s])
            .collect();
        let mut set = if live.is_empty() {
            vec![false; n]
        } else {
            let mut acc = pdom[live[0]].clone().expect("live successor has pdom");
            for &s in &live[1..] {
                let other = pdom[s].as_ref().expect("live successor has pdom");
                for (a, o) in acc.iter_mut().zip(other) {
                    *a &= *o;
                }
            }
            acc
        };
        set[i] = true;
        pdom[i] = Some(set);
    }
    let sizes: Vec<usize> = pdom
        .iter()
        .map(|s| s.as_ref().map_or(0, |s| s.iter().filter(|x| **x).count()))
        .collect();
    // Immediate post-dominator: the strict post-dominator with the largest
    // post-dominator set (they form a chain).
    let ipdom = |i: usize| -> usize {
        let Some(set) = &pdom[i] else { return EXIT };
        let mut best = EXIT;
        for (j, &in_set) in set.iter().enumerate() {
            if j != i && in_set && (best == EXIT || sizes[j] > sizes[best]) {
                best = j;
            }
        }
        best
    };

    let original: usize = nodes.iter().map(|nd| nd.instrs.len()).sum();
    let mut budget = original.saturating_mul(4).max(256);
    fn emit(
        nodes: &[Node],
        ipdom: &dyn Fn(usize) -> usize,
        mut at: usize,
        stop: usize,
        budget: &mut usize,
    ) -> Result<Vec<StructuredBlock>, Refusal> {
        let mut out = Vec::new();
        loop {
            if at == stop {
                return Ok(out);
            }
            let node = &nodes[at];
            *budget = budget
                .checked_sub(node.instrs.len() + 1)
                .ok_or(Refusal::CopyBudget)?;
            out.extend(node.instrs.iter().cloned());
            match &node.term {
                Term::Return | Term::Trap | Term::Exit => return Ok(out),
                Term::Goto(s) => at = *s,
                Term::Cond { taken, fall } => {
                    let join = ipdom(at);
                    let then_body = emit(nodes, ipdom, *taken, join, budget)?;
                    let else_body = emit(nodes, ipdom, *fall, join, budget)?;
                    out.push(StructuredBlock::IfElse {
                        block_type: EXACT_IF,
                        then_body,
                        else_body,
                    });
                    if join == usize::MAX {
                        return Ok(out);
                    }
                    at = join;
                }
                Term::Multi(_) | Term::Opaque(_) | Term::Refuse => {
                    unreachable!("exact mode never builds these")
                }
            }
        }
    }
    emit(nodes, &ipdom, entry, EXIT, &mut budget)
}

/// What an outer label means inside a region being rewritten.
#[derive(Clone)]
enum Outer {
    /// Its continuation only traps; a branch to it runs this tail.
    Trap(Vec<StructuredBlock>),
    /// A real join outside the region.
    Refuse,
}

/// Rewrite one region (a `block`'s body) into a branch-free tree. `outer`
/// describes the labels outside the region, outermost first.
fn rewrite_region(
    body: &[StructuredBlock],
    outer: &[Outer],
) -> Result<Vec<StructuredBlock>, Refusal> {
    let mut b = Builder {
        nodes: Vec::new(),
        analysis: false,
        far: Vec::new(),
    };
    let mut labels: Vec<Label> = outer
        .iter()
        .map(|o| {
            let node = match o {
                Outer::Trap(tail) => b.push(tail.clone(), Term::Trap),
                Outer::Refuse => b.push(Vec::new(), Term::Refuse),
            };
            Label { node, block: None }
        })
        .collect();
    let exit = b.push(Vec::new(), Term::Exit);
    labels.push(Label {
        node: exit,
        block: None,
    });
    let entry = b.build(body, exit, &mut labels)?;
    emit_tree(&b.nodes, entry)
}

/// What [`restructure_regions`] did.
#[derive(Debug, Default)]
pub struct Outcome {
    /// Join regions rewritten.
    pub regions: usize,
    /// Join regions left alone, and why.
    pub refused: Vec<Refusal>,
}

/// True when `seq` calls a function `user_call` accepts.
fn calls_user_code(seq: &[StructuredBlock], user_call: &dyn Fn(u32) -> bool) -> bool {
    seq.iter().any(|b| match b {
        StructuredBlock::Instruction(WasmInstr::Call(f)) => user_call(*f),
        StructuredBlock::Block { body, .. } | StructuredBlock::Loop { body, .. } => {
            calls_user_code(body, user_call)
        }
        StructuredBlock::IfElse {
            then_body,
            else_body,
            ..
        } => calls_user_code(then_body, user_call) || calls_user_code(else_body, user_call),
        _ => false,
    })
}

/// Rewrite the multi-level branches of a function body (see the module docs).
///
/// Only join regions that call a function `user_call` accepts are rewritten
/// (the caller passes "a local function that is not a bare trap helper"):
/// that is user code. The SDK's own inline joins — the small/object split
/// of a `Val` encode or decode, an integer overflow check — call host
/// functions or nothing, and the lifter has dedicated handling for them.
pub fn restructure_regions(
    body: &mut Vec<StructuredBlock>,
    user_call: &dyn Fn(u32) -> bool,
) -> Outcome {
    let mut out = Outcome::default();

    // Whole-body analysis: which labels only trap, and where every
    // multi-level branch goes.
    let mut a = Builder {
        nodes: Vec::new(),
        analysis: true,
        far: Vec::new(),
    };
    let end = a.push(Vec::new(), Term::Return);
    let mut labels = vec![Label {
        node: end,
        block: None,
    }];
    if a.build(body, end, &mut labels).is_err() {
        return out;
    }
    let mt = must_trap(&a.nodes);
    if a.far.is_empty() {
        return out;
    }

    // Every `block`: where it sits, the labels outside it, the blocks around
    // it. Blocks are identified by address while `body` is borrowed
    // immutably; nothing is dereferenced through an address.
    let rewritten = {
        let mut blocks: HashMap<*const StructuredBlock, BlockInfo<'_>> = HashMap::new();
        collect_block_contexts(body, &mut vec![labels[0]], &mut Vec::new(), &a, &mut blocks);

        // Join regions: blocks a multi-level branch reaches, whose
        // continuation does not only trap. Outermost first.
        let mut regions: Vec<*const StructuredBlock> = Vec::new();
        for f in &a.far {
            if let Some(bp) = f.target.block
                && !mt[f.target.node]
                && !regions.contains(&bp)
            {
                regions.push(bp);
            }
        }
        regions.sort_by_key(|bp| blocks.get(bp).map_or(usize::MAX, |b| b.labels.len()));

        let outer_of = |labels: &[Label]| -> Vec<Outer> {
            labels
                .iter()
                .map(|l| {
                    // A label no multi-level branch reaches has no node here;
                    // no branch inside the region reaches it either.
                    if l.node != usize::MAX
                        && mt[l.node]
                        && let Some(tail) = trap_tail(&a.nodes, l.node)
                    {
                        Outer::Trap(tail)
                    } else {
                        Outer::Refuse
                    }
                })
                .collect()
        };

        let mut rewritten: HashMap<*const StructuredBlock, Vec<StructuredBlock>> = HashMap::new();
        for bp in &regions {
            let Some(info) = blocks.get(bp) else {
                continue;
            };
            // Inside a region already rewritten: covered by it.
            if info.ancestors.iter().any(|a| rewritten.contains_key(a)) {
                continue;
            }
            let StructuredBlock::Block { body: rbody, .. } = info.item else {
                continue;
            };
            if !calls_user_code(rbody, user_call) {
                continue;
            }
            match rewrite_region(rbody, &outer_of(&info.labels)) {
                Ok(new_body) => {
                    rewritten.insert(*bp, new_body);
                    out.regions += 1;
                }
                Err(e) => out.refused.push(e),
            }
        }
        rewritten
    };

    // A guard outside a rewritten region is left to the lifter: the SDK's
    // own checks (parameter tags, integer overflow) reach a trap the same
    // way, and rendering them needs their conditions classified first.
    if !rewritten.is_empty() {
        apply(body, &rewritten);
    }
    out
}

/// What [`restructure_regions`] knows about one `block`.
struct BlockInfo<'a> {
    item: &'a StructuredBlock,
    /// The labels outside it, outermost first (as [`Builder::build`] sees
    /// them).
    labels: Vec<Label>,
    /// The `block`s it is nested in.
    ancestors: Vec<*const StructuredBlock>,
}

/// Record every `block` in `seq` (see [`BlockInfo`]), mirroring
/// [`Builder::build`]'s label stack.
fn collect_block_contexts<'a>(
    seq: &'a [StructuredBlock],
    labels: &mut Vec<Label>,
    ancestors: &mut Vec<*const StructuredBlock>,
    a: &Builder,
    out: &mut HashMap<*const StructuredBlock, BlockInfo<'a>>,
) {
    for item in seq {
        match item {
            StructuredBlock::Block { body, .. } => {
                let p: *const StructuredBlock = item;
                out.insert(
                    p,
                    BlockInfo {
                        item,
                        labels: labels.clone(),
                        ancestors: ancestors.clone(),
                    },
                );
                // The block's own label: the node its `br 0` reaches. Find it
                // from a recorded far branch, or leave a placeholder that is
                // never must-trap (a `br 0` to it is not a far branch).
                let node = a
                    .far
                    .iter()
                    .find(|f| f.target.block == Some(p))
                    .map_or(usize::MAX, |f| f.target.node);
                labels.push(Label {
                    node,
                    block: Some(p),
                });
                ancestors.push(p);
                collect_block_contexts(body, labels, ancestors, a, out);
                ancestors.pop();
                labels.pop();
            }
            StructuredBlock::IfElse {
                then_body,
                else_body,
                ..
            } => {
                labels.push(Label {
                    node: usize::MAX,
                    block: None,
                });
                collect_block_contexts(then_body, labels, ancestors, a, out);
                collect_block_contexts(else_body, labels, ancestors, a, out);
                labels.pop();
            }
            // Loops are opaque to the rewrite.
            _ => {}
        }
    }
}

/// Splice the rewritten regions into `seq`: a rewritten region has no branch
/// left to its label, so its body replaces the `block`. Items are matched by
/// the address they had when the regions were computed; moving a `Vec` does
/// not move its elements, so the addresses of nested items still match.
fn apply(
    seq: &mut Vec<StructuredBlock>,
    regions: &HashMap<*const StructuredBlock, Vec<StructuredBlock>>,
) {
    let old = std::mem::take(seq);
    let addrs: Vec<*const StructuredBlock> = old.iter().map(|b| b as *const _).collect();
    for (item, addr) in old.into_iter().zip(addrs) {
        if let Some(r) = regions.get(&addr) {
            seq.extend(r.iter().cloned());
            continue;
        }
        seq.push(match item {
            StructuredBlock::Block {
                block_type,
                mut body,
            } => {
                apply(&mut body, regions);
                StructuredBlock::Block { block_type, body }
            }
            StructuredBlock::IfElse {
                block_type,
                mut then_body,
                mut else_body,
            } => {
                apply(&mut then_body, regions);
                apply(&mut else_body, regions);
                StructuredBlock::IfElse {
                    block_type,
                    then_body,
                    else_body,
                }
            }
            other => other,
        });
    }
}

/// True when `seq` contains a `br`/`br_if` (outside loops).
#[cfg(test)]
fn has_forward_branch(seq: &[StructuredBlock]) -> bool {
    seq.iter().any(|b| match b {
        StructuredBlock::Instruction(WasmInstr::Br(_) | WasmInstr::BrIf(_)) => true,
        StructuredBlock::Block { body, .. } => has_forward_branch(body),
        StructuredBlock::IfElse {
            then_body,
            else_body,
            ..
        } => has_forward_branch(then_body) || has_forward_branch(else_body),
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pattern::structurize::structurize;
    use WasmInstr::*;

    fn blk() -> WasmInstr {
        Block {
            block_type: BlockType::Empty,
        }
    }

    /// `block { block { c; br_if 0; A; br 1 } B } C` — the inner `br 1`
    /// joins the two paths at the outer block's end.
    #[test]
    fn diamond_joins_after_both_arms() {
        let mut body = structurize(&[
            blk(),
            blk(),
            LocalGet(0),
            BrIf(0),
            Call(1),
            LocalSet(1),
            Br(1),
            End,
            I32Const(2),
            LocalSet(1),
            End,
            LocalGet(1),
            Drop,
        ]);
        let o = restructure_regions(&mut body, &|_| true);
        assert_eq!(o.regions, 1, "{o:?}");
        assert!(!has_forward_branch(&body), "{body:#?}");
        assert!(
            matches!(body[0], StructuredBlock::Instruction(LocalGet(0))),
            "{body:#?}"
        );
        let StructuredBlock::IfElse {
            then_body,
            else_body,
            ..
        } = &body[1]
        else {
            panic!("{body:#?}")
        };
        assert!(matches!(
            then_body[..],
            [StructuredBlock::Instruction(I32Const(2)), _]
        ));
        assert!(matches!(
            else_body[..],
            [StructuredBlock::Instruction(Call(1)), _]
        ));
        assert!(matches!(body[2], StructuredBlock::Instruction(LocalGet(1))));
    }

    /// A nested guard to a trapping continuation outside any join region is
    /// left to the lifter.
    #[test]
    fn far_guard_outside_a_region_is_left_alone() {
        let mut body = structurize(&[
            blk(),
            blk(),
            LocalGet(0),
            BrIf(0),
            LocalGet(1),
            BrIf(1),
            End,
            I32Const(7),
            Return,
            End,
            Call(9),
            Unreachable,
        ]);
        let o = restructure_regions(&mut body, &|_| true);
        assert_eq!(o.regions, 0, "{o:?}");
        assert!(has_forward_branch(&body));
    }

    /// Inside a join region, a branch to a trapping outer label runs the
    /// trap tail in place.
    #[test]
    fn guard_inside_a_region_runs_the_trap_tail() {
        let mut body = structurize(&[
            blk(),
            blk(),
            blk(),
            LocalGet(0),
            BrIf(2),
            LocalGet(1),
            BrIf(0),
            Call(5),
            Br(1),
            End,
            Call(6),
            End,
            LocalGet(2),
            Return,
            End,
            Call(9),
            Unreachable,
        ]);
        let o = restructure_regions(&mut body, &|_| true);
        assert_eq!(o.regions, 1, "{o:?}");
        let StructuredBlock::Block { body: outer, .. } = &body[0] else {
            panic!("{body:#?}")
        };
        assert!(!has_forward_branch(outer), "{body:#?}");
        let StructuredBlock::IfElse { then_body, .. } = &outer[1] else {
            panic!("{body:#?}")
        };
        assert!(
            matches!(
                then_body[..],
                [
                    StructuredBlock::Instruction(Call(9)),
                    StructuredBlock::Instruction(Unreachable)
                ]
            ),
            "{body:#?}"
        );
    }

    /// A region that calls no user code is left to the lifter.
    #[test]
    fn region_without_user_calls_is_left_alone() {
        let mut body = structurize(&[
            blk(),
            blk(),
            LocalGet(0),
            BrIf(0),
            Call(3),
            Br(1),
            End,
            Call(4),
            End,
        ]);
        let o = restructure_regions(&mut body, &|f| f >= 10);
        assert_eq!(o.regions, 0, "{o:?}");
    }

    /// No multi-level branch: nothing changes.
    #[test]
    fn top_level_br_if_is_left_alone() {
        let mut body = structurize(&[blk(), LocalGet(0), BrIf(0), I32Const(1), Drop, End]);
        let o = restructure_regions(&mut body, &|_| true);
        assert_eq!(o.regions, 0);
        assert!(has_forward_branch(&body));
    }

    #[test]
    fn br_table_in_a_region_refuses() {
        let mut body = structurize(&[
            blk(),
            blk(),
            Call(1),
            LocalGet(0),
            BrIf(1),
            LocalGet(0),
            BrTable {
                targets: vec![0],
                default: 0,
            },
            End,
            End,
            LocalGet(1),
            Drop,
        ]);
        let o = restructure_regions(&mut body, &|_| true);
        assert_eq!(o.refused, vec![Refusal::BrTable]);
    }
}
