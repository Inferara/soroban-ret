//! WASM-level control-flow analysis over `StructuredBlock` trees.
//!
//! Distinguishes two kinds of `unreachable` instruction:
//!
//! 1. **User panic** — the compiler emits `call $panic_helper; unreachable` (or
//!    the function body is *just* `unreachable`, which is the panic helper
//!    itself). The unreachable here carries the user's `panic!()` semantics.
//! 2. **Compiler safety net** — every control-flow path reaching the
//!    `unreachable` has already terminated via `return`, `br`/`br_table` out
//!    of the enclosing block, or a call to a `-> !` helper. The compiler emits
//!    the trailing `unreachable` to satisfy WASM validation (a typed body must
//!    end in a typed value or an `unreachable`), not because any executable
//!    path actually reaches it.
//!
//! The lifter must treat (1) as `SorobanExpr::Panic` and (2) as a no-op.
//! Conflating them produces the issue #8 / #11 truncation: an inlined helper
//! with a trailing safety-net `unreachable` leaks an orphan `Expr(Panic)` to
//! the caller, where `remove_dead_code` treats it as a strong terminator and
//! drops the real continuation.
//!
//! This module's [`classify_safety_net_unreachables`] rewrites every
//! safety-net `Instruction(WasmInstr::Unreachable)` into the dedicated
//! `StructuredBlock::SafetyNetUnreachable` variant before lifting. The lifter
//! emits IR for the original `Instruction(Unreachable)` (user panics) and
//! nothing for `SafetyNetUnreachable`.

use super::structurize::StructuredBlock;
use crate::wasm::ir::WasmInstr;
use crate::wasm::parser::WasmModule;

/// Rewrite every safety-net `unreachable` in `blocks` to
/// [`StructuredBlock::SafetyNetUnreachable`]. Idempotent.
pub(crate) fn classify_safety_net_unreachables(
    blocks: &mut Vec<StructuredBlock>,
    wasm_module: &WasmModule,
) {
    classify_seq(blocks, wasm_module);
}

/// Post-order: classify inner bodies first so the predicate that asks
/// `terminates(body[i-1])` sees their final (rewritten) shape.
fn classify_seq(body: &mut Vec<StructuredBlock>, module: &WasmModule) {
    for sb in body.iter_mut() {
        match sb {
            StructuredBlock::Block { body, .. } | StructuredBlock::Loop { body, .. } => {
                classify_seq(body, module);
            }
            StructuredBlock::IfElse {
                then_body,
                else_body,
                ..
            } => {
                classify_seq(then_body, module);
                classify_seq(else_body, module);
            }
            StructuredBlock::Instruction(_) | StructuredBlock::SafetyNetUnreachable => {}
        }
    }

    for i in 0..body.len() {
        if !matches!(
            body[i],
            StructuredBlock::Instruction(WasmInstr::Unreachable)
        ) {
            continue;
        }
        // A solo-`unreachable` body is the panic helper pattern itself — keep
        // it as a user panic so `is_unreachable_only_function` callers and the
        // lifter's Unreachable handler still emit `SorobanExpr::Panic`.
        let body_is_just_unreachable = body.len() == 1 && i == 0;
        if body_is_just_unreachable {
            continue;
        }
        let preceded_by_terminator = i > 0 && terminates(&body[i - 1], module);
        if preceded_by_terminator {
            body[i] = StructuredBlock::SafetyNetUnreachable;
        }
    }
}

/// `true` iff control cannot fall through this structured node into its
/// sequential successor in the same body — i.e. every path leaving the node
/// leaves via `return`, `br`/`br_table` (to an outer label), an `unreachable`,
/// or a call to a `-> !` helper.
fn terminates(sb: &StructuredBlock, module: &WasmModule) -> bool {
    match sb {
        StructuredBlock::Instruction(instr) => match instr {
            WasmInstr::Return | WasmInstr::Unreachable => true,
            // Unconditional branch out of the current body: nothing in the
            // tail of this sequence executes after it.
            WasmInstr::Br(_) => true,
            // `br_table` selects an outer label for every input value (no
            // fall-through). Treat as unconditional branch out.
            WasmInstr::BrTable { .. } => true,
            WasmInstr::Call(idx) => super::lifter::is_unreachable_only_function(module, *idx),
            _ => false,
        },
        StructuredBlock::SafetyNetUnreachable => true,
        StructuredBlock::Block { body, .. } => seq_terminates(body, module),
        StructuredBlock::Loop { body, .. } => seq_terminates(body, module),
        StructuredBlock::IfElse {
            then_body,
            else_body,
            ..
        } => {
            // If there is no `else`, the falsy path falls through to the
            // sequence's next instruction; the IfElse as a whole does not
            // terminate.
            !else_body.is_empty()
                && seq_terminates(then_body, module)
                && seq_terminates(else_body, module)
        }
    }
}

fn seq_terminates(body: &[StructuredBlock], module: &WasmModule) -> bool {
    body.iter().any(|sb| terminates(sb, module))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm::data::DataSection;
    use crate::wasm::exports::ExportTable;
    use crate::wasm::imports::ImportTable;
    use crate::wasm::ir::{BlockType, WasmFunction, WasmInstr};
    use crate::wasm::parser::WasmModule;
    use std::collections::HashMap;

    fn empty_module() -> WasmModule {
        WasmModule {
            custom_sections: HashMap::new(),
            imports: ImportTable::new(),
            exports: ExportTable::new(),
            functions: Vec::new(),
            data_sections: DataSection::new(),
            types: Vec::new(),
            num_imported_functions: 0,
            parse_diagnostics: Vec::new(),
            dwarf_names: HashMap::new(),
        }
    }

    fn module_with_function(body: Vec<WasmInstr>) -> WasmModule {
        let mut module = empty_module();
        module.functions.push(WasmFunction {
            index: 0,
            type_index: 0,
            locals: Vec::new(),
            body,
        });
        module
    }

    /// Module whose function index 0 is a one-instruction `unreachable` panic
    /// helper — `is_unreachable_only_function` returns true for it.
    fn module_with_panic_helper() -> WasmModule {
        module_with_function(vec![WasmInstr::Unreachable, WasmInstr::End])
    }

    fn instr(i: WasmInstr) -> StructuredBlock {
        StructuredBlock::Instruction(i)
    }

    #[test]
    fn solo_unreachable_stays_user_panic() {
        let module = empty_module();
        let mut blocks = vec![instr(WasmInstr::Unreachable)];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(
            blocks[0],
            StructuredBlock::Instruction(WasmInstr::Unreachable)
        ));
    }

    #[test]
    fn non_diverging_predecessor_keeps_user_panic() {
        let module = empty_module();
        let mut blocks = vec![instr(WasmInstr::I32Const(7)), instr(WasmInstr::Unreachable)];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(
            blocks[1],
            StructuredBlock::Instruction(WasmInstr::Unreachable)
        ));
    }

    #[test]
    fn return_predecessor_marks_safety_net() {
        let module = empty_module();
        let mut blocks = vec![instr(WasmInstr::Return), instr(WasmInstr::Unreachable)];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(blocks[1], StructuredBlock::SafetyNetUnreachable));
    }

    #[test]
    fn br_predecessor_marks_safety_net() {
        let module = empty_module();
        let mut blocks = vec![instr(WasmInstr::Br(0)), instr(WasmInstr::Unreachable)];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(blocks[1], StructuredBlock::SafetyNetUnreachable));
    }

    #[test]
    fn br_table_predecessor_marks_safety_net() {
        let module = empty_module();
        let mut blocks = vec![
            instr(WasmInstr::BrTable {
                targets: vec![0, 1],
                default: 1,
            }),
            instr(WasmInstr::Unreachable),
        ];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(blocks[1], StructuredBlock::SafetyNetUnreachable));
    }

    #[test]
    fn call_to_panic_helper_predecessor_marks_safety_net() {
        let module = module_with_panic_helper();
        let mut blocks = vec![instr(WasmInstr::Call(0)), instr(WasmInstr::Unreachable)];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(blocks[1], StructuredBlock::SafetyNetUnreachable));
    }

    #[test]
    fn call_to_normal_function_keeps_user_panic() {
        // Function 0 is a non-panic-helper (body has more than just Unreachable):
        // `is_unreachable_only_function` returns false → Call is not a terminator.
        let module = module_with_function(vec![
            WasmInstr::I32Const(42),
            WasmInstr::Return,
            WasmInstr::End,
        ]);
        let mut blocks = vec![instr(WasmInstr::Call(0)), instr(WasmInstr::Unreachable)];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(
            blocks[1],
            StructuredBlock::Instruction(WasmInstr::Unreachable)
        ));
    }

    #[test]
    fn ifelse_both_diverge_marks_safety_net() {
        let module = empty_module();
        let mut blocks = vec![
            StructuredBlock::IfElse {
                block_type: BlockType::Empty,
                then_body: vec![instr(WasmInstr::Return)],
                else_body: vec![instr(WasmInstr::Return)],
            },
            instr(WasmInstr::Unreachable),
        ];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(blocks[1], StructuredBlock::SafetyNetUnreachable));
    }

    #[test]
    fn ifelse_empty_else_keeps_user_panic() {
        let module = empty_module();
        let mut blocks = vec![
            StructuredBlock::IfElse {
                block_type: BlockType::Empty,
                then_body: vec![instr(WasmInstr::Return)],
                else_body: Vec::new(),
            },
            instr(WasmInstr::Unreachable),
        ];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(
            blocks[1],
            StructuredBlock::Instruction(WasmInstr::Unreachable)
        ));
    }

    #[test]
    fn ifelse_one_branch_diverges_keeps_user_panic() {
        let module = empty_module();
        let mut blocks = vec![
            StructuredBlock::IfElse {
                block_type: BlockType::Empty,
                then_body: vec![instr(WasmInstr::Return)],
                else_body: vec![instr(WasmInstr::I32Const(1))],
            },
            instr(WasmInstr::Unreachable),
        ];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(
            blocks[1],
            StructuredBlock::Instruction(WasmInstr::Unreachable)
        ));
    }

    #[test]
    fn block_with_diverging_body_marks_safety_net() {
        let module = empty_module();
        let mut blocks = vec![
            StructuredBlock::Block {
                block_type: BlockType::Empty,
                body: vec![instr(WasmInstr::I32Const(1)), instr(WasmInstr::Return)],
            },
            instr(WasmInstr::Unreachable),
        ];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(blocks[1], StructuredBlock::SafetyNetUnreachable));
    }

    #[test]
    fn block_with_non_diverging_body_keeps_user_panic() {
        let module = empty_module();
        let mut blocks = vec![
            StructuredBlock::Block {
                block_type: BlockType::Empty,
                body: vec![instr(WasmInstr::I32Const(1))],
            },
            instr(WasmInstr::Unreachable),
        ];
        classify_safety_net_unreachables(&mut blocks, &module);
        assert!(matches!(
            blocks[1],
            StructuredBlock::Instruction(WasmInstr::Unreachable)
        ));
    }

    #[test]
    fn nested_unreachables_classified_recursively() {
        // Inner block: [Return, Unreachable]  -> inner Unreachable becomes safety-net.
        // Outer body:  [InnerBlock, Unreachable]  -> outer Unreachable also safety-net
        //   (inner block terminates because its body has Return).
        let module = empty_module();
        let mut blocks = vec![
            StructuredBlock::Block {
                block_type: BlockType::Empty,
                body: vec![instr(WasmInstr::Return), instr(WasmInstr::Unreachable)],
            },
            instr(WasmInstr::Unreachable),
        ];
        classify_safety_net_unreachables(&mut blocks, &module);
        if let StructuredBlock::Block { body, .. } = &blocks[0] {
            assert!(matches!(body[1], StructuredBlock::SafetyNetUnreachable));
        } else {
            panic!("expected Block");
        }
        assert!(matches!(blocks[1], StructuredBlock::SafetyNetUnreachable));
    }

    #[test]
    fn idempotent() {
        let module = empty_module();
        let mut blocks = vec![instr(WasmInstr::Return), instr(WasmInstr::Unreachable)];
        classify_safety_net_unreachables(&mut blocks, &module);
        let after_first = format!("{:?}", blocks);
        classify_safety_net_unreachables(&mut blocks, &module);
        let after_second = format!("{:?}", blocks);
        assert_eq!(after_first, after_second);
    }
}
