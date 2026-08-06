//! Per-contract recovery signals — how much of *this* contract was recovered.
//!
//! Everything here is computed from the contract in front of you: no corpus, no
//! reference source, no baseline. That is the point. The project's published
//! aggregates (corpus mean restoration, corpus behavioral-match rate) are
//! *corpus* metrics and do not transfer to an individual contract; quoting them
//! on a contract page overstates what is known about that contract.
//!
//! # What this measures, and what it does not
//!
//! These counts grade **completeness**, not correctness. A function reported
//! [`FnStatus::Clean`] contains no unrecovered nodes — it does *not* follow that
//! the recovered logic is right. Nothing short of the functional-equivalence
//! harness (recompile + differential execution against the original under
//! `soroban-env-host`) speaks to correctness, and that harness can only run on
//! output that recompiles.
//!
//! Consumers surfacing this in a UI should therefore pair it with an
//! "experimental / reconstruction" caveat, and should prefer **counts** over a
//! single headline percentage — which is why [`RecoveryReport`] deliberately
//! exposes no aggregate "recovered %" field. "38 of 75 functions fully
//! recovered · 379 unresolved holes" is verifiable and hard to misread; a bare
//! "92 % recovered" invites exactly the misreading this module exists to avoid.
//!
//! # Two views of the same thing
//!
//! - [`RecoveryReport::functions`] — a per-function verdict ([`FnStatus`]),
//!   derived by walking the lifted IR. This is the useful signal: it tells you
//!   *which* functions to distrust. [`FnStatus::LogicLost`] and
//!   [`FnStatus::Missing`] are the loud ones.
//! - [`RecoveryReport::artifacts`] — hole counts by category, derived by
//!   counting markers in the emitted source. This is the headline number a UI
//!   can show next to the contract.

use std::collections::BTreeMap;

use stellar_xdr::curr::ScSpecTypeDef;

use crate::ir::high_level_ir::{ContractFn, ContractModule};
use crate::ir::soroban_ir::{MatchPattern, SorobanExpr, SorobanStmt};
use crate::spec::registry::TypeRegistry;

// ---------------------------------------------------------------------------
// Artifact counts
// ---------------------------------------------------------------------------

/// Unrecovered-value markers in emitted source, by category.
///
/// Each one renders as a `todo!()` (or a `var_N` placeholder name) and marks a
/// value the decompiler could not prove. They are deliberate holes: the
/// alternative — emitting a plausible-looking stand-in — produces output that
/// compiles and is silently wrong, which this project treats as a bug class.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub struct ArtifactCounts {
    /// `todo!("unknown value")` — a value whose definition was lost.
    pub unknown_value: usize,
    /// `todo!("host call …")` — a host call the lifter did not model.
    pub host_call: usize,
    /// `todo!("decompiled function body")` — a whole body that did not lift.
    pub stub: usize,
    /// `var_N` — a local the namer could not give a meaningful name.
    pub var_n: usize,
    /// Sum of the above.
    pub total: usize,
}

/// Count unrecovered-value markers in generated source, by category.
///
/// Matches both the compact `todo!(` and the space-separated `todo !(` form:
/// `prettyplease` emits the latter in some positions, and matching only one
/// spelling silently undercounts.
pub fn count_artifacts(src: &str) -> ArtifactCounts {
    let count_both = |a: &str, b: &str| src.matches(a).count() + src.matches(b).count();
    let unknown_value = count_both("todo!(\"unknown value\")", "todo !(\"unknown value\")");
    let host_call = count_both("todo!(\"host call", "todo !(\"host call");
    let stub = count_both(
        "todo!(\"decompiled function body\")",
        "todo !(\"decompiled function body\")",
    );

    let mut var_n = 0;
    for word in src.split(|c: char| !c.is_alphanumeric() && c != '_') {
        if word.len() > 4
            && word.starts_with("var_")
            && word[4..].chars().all(|c| c.is_ascii_digit())
        {
            var_n += 1;
        }
    }

    ArtifactCounts {
        unknown_value,
        host_call,
        stub,
        var_n,
        total: unknown_value + host_call + stub + var_n,
    }
}

// ---------------------------------------------------------------------------
// Per-function verdict
// ---------------------------------------------------------------------------

/// Recovery verdict for a single exported function.
///
/// Marked `#[non_exhaustive]`: further verdicts may be distinguished later
/// (e.g. splitting `Partial` by which node class was lost). Match with a
/// wildcard arm.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(rename_all = "snake_case")
)]
#[non_exhaustive]
pub enum FnStatus {
    /// Body lifted with zero unrecovered nodes.
    Clean,
    /// Body present, but some nodes did not lift.
    Partial,
    /// The body is empty but the function cannot be a no-op — either the lifter
    /// saw host calls, or the function returns a value it therefore cannot
    /// produce (codegen renders such a body as
    /// `todo!("decompiled function body")`, which traps at runtime). Real logic
    /// was lost. Not an identity passthrough; treat with suspicion.
    LogicLost,
    /// Empty body, no host calls, and no value to return — a genuine
    /// no-op/passthrough. Nothing to restore, so this counts as fully
    /// recovered.
    Trivial,
    /// Declared in the contract's own `contractspecv0`, but absent from the
    /// lifted module entirely.
    Missing,
}

impl FnStatus {
    /// Whether nothing was lost for this function (`Clean` or `Trivial`).
    pub fn is_fully_recovered(self) -> bool {
        matches!(self, FnStatus::Clean | FnStatus::Trivial)
    }

    /// Whether the function's logic is *gone* rather than merely incomplete
    /// (`LogicLost` or `Missing`). These are the ones a UI should surface
    /// loudly — the body on screen does not represent the on-chain behavior.
    pub fn is_lost(self) -> bool {
        matches!(self, FnStatus::LogicLost | FnStatus::Missing)
    }

    /// Short human-readable label, suitable for a UI badge.
    pub fn label(self) -> &'static str {
        match self {
            FnStatus::Clean => "recovered",
            FnStatus::Partial => "partial",
            FnStatus::LogicLost => "logic lost",
            FnStatus::Trivial => "trivial",
            FnStatus::Missing => "missing",
        }
    }
}

/// Per-function recovery record.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub struct FnRecovery {
    /// Function name as declared in `contractspecv0`.
    pub name: String,
    pub status: FnStatus,
    /// Recovery fraction in `0.0..=1.0` — `(total - unknown) / total` nodes.
    ///
    /// Exposed per function on purpose. Averaging these into one contract-level
    /// percentage is what produces the misleading headline number; if you need
    /// an aggregate, prefer the counts on [`RecoveryReport`].
    pub score: f64,
    /// Expression nodes visited in the body.
    pub total_nodes: usize,
    /// Of those, nodes that did not lift (each renders as a `todo!()`).
    pub unknown_nodes: usize,
    /// Distinct `module::function` host calls the lifter left unrecovered.
    pub missing_host_calls: Vec<String>,
}

// ---------------------------------------------------------------------------
// Contract report
// ---------------------------------------------------------------------------

/// Per-contract recovery summary.
///
/// Note the absence of any aggregate "recovered %" — see the module docs. Use
/// [`fully_recovered`](Self::fully_recovered) / [`spec_functions`](Self::spec_functions)
/// / [`holes`](Self::holes) to render counts.
#[derive(Clone, Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub struct RecoveryReport {
    /// One record per function in the contract's public interface, in the order
    /// the spec declares them.
    pub functions: Vec<FnRecovery>,
    /// Hole counts over the emitted source.
    pub artifacts: ArtifactCounts,
}

impl RecoveryReport {
    /// Size of the contract's public interface — the denominator for every
    /// count below. Taken from `contractspecv0` when present, so functions the
    /// lifter dropped entirely still count against it.
    pub fn spec_functions(&self) -> usize {
        self.functions.len()
    }

    /// Functions with nothing lost (`Clean` + `Trivial`).
    pub fn fully_recovered(&self) -> usize {
        self.functions
            .iter()
            .filter(|f| f.status.is_fully_recovered())
            .count()
    }

    /// Functions lifted with some nodes missing.
    pub fn partial(&self) -> usize {
        self.count(FnStatus::Partial)
    }

    /// Functions whose logic is gone (`LogicLost` + `Missing`).
    pub fn lost(&self) -> usize {
        self.functions.iter().filter(|f| f.status.is_lost()).count()
    }

    /// Functions with exactly this status.
    pub fn count(&self, status: FnStatus) -> usize {
        self.functions.iter().filter(|f| f.status == status).count()
    }

    /// Total unresolved holes in the emitted source.
    pub fn holes(&self) -> usize {
        self.artifacts.total
    }

    /// Functions whose logic is gone — the ones worth surfacing loudly.
    pub fn lost_functions(&self) -> impl Iterator<Item = &FnRecovery> {
        self.functions.iter().filter(|f| f.status.is_lost())
    }

    /// One-line summary suitable for a UI subtitle.
    ///
    /// e.g. `"38 of 75 functions fully recovered · 379 unresolved holes"`.
    pub fn summary(&self) -> String {
        format!(
            "{} of {} functions fully recovered · {} unresolved hole{}",
            self.fully_recovered(),
            self.spec_functions(),
            self.holes(),
            if self.holes() == 1 { "" } else { "s" }
        )
    }
}

/// Build the recovery report for a decompiled contract.
///
/// The denominator is the contract's own `contractspecv0` function list — the
/// authoritative public interface — so a function the lifter dropped is
/// reported [`FnStatus::Missing`] rather than silently vanishing. Contracts
/// with no spec (non-Rust SDKs) fall back to the lifted function set.
pub fn report(module: &ContractModule, registry: &TypeRegistry, source: &str) -> RecoveryReport {
    let lifted: BTreeMap<&str, &ContractFn> = module
        .functions
        .iter()
        .map(|f| (f.name.as_str(), f))
        .collect();

    let names: Vec<String> = if !registry.functions.is_empty() {
        registry.functions.keys().cloned().collect()
    } else {
        module.functions.iter().map(|f| f.name.clone()).collect()
    };

    let functions = names
        .iter()
        .map(|name| match lifted.get(name.as_str()) {
            Some(f) => score_fn(name, f),
            None => FnRecovery {
                name: name.clone(),
                status: FnStatus::Missing,
                score: 0.0,
                total_nodes: 0,
                unknown_nodes: 0,
                missing_host_calls: Vec::new(),
            },
        })
        .collect();

    RecoveryReport {
        functions,
        artifacts: count_artifacts(source),
    }
}

/// Whether codegen will render an empty body as a
/// `todo!("decompiled function body")` stub rather than as an empty block.
///
/// Mirrors the condition in `codegen::module`: a function that declares a
/// non-`Void` return type has no value to return once its body is empty, so the
/// emitted body is a stub that traps. Such a function is *not* a passthrough,
/// however innocuous the empty IR body looks.
fn returns_a_value(f: &ContractFn) -> bool {
    if let Some(sig) = &f.wasm_signature {
        return !sig.results.is_empty();
    }
    f.return_type
        .as_ref()
        .is_some_and(|rt| !matches!(rt, ScSpecTypeDef::Void))
}

/// Grade one lifted function's recovery.
///
/// - empty body + `had_host_calls` → [`FnStatus::LogicLost`], score `0.0`
/// - empty body + returns a value  → [`FnStatus::LogicLost`], score `0.0`
///   (the body renders as a `todo!()` stub and traps — see [`returns_a_value`])
/// - empty body, otherwise         → [`FnStatus::Trivial`], score `1.0`
/// - non-empty body                → `clean_nodes / total_nodes`
pub fn score_fn(name: &str, f: &ContractFn) -> FnRecovery {
    if f.body.is_empty() {
        let (status, score) = if f.had_host_calls || returns_a_value(f) {
            (FnStatus::LogicLost, 0.0)
        } else {
            (FnStatus::Trivial, 1.0)
        };
        return FnRecovery {
            name: name.to_string(),
            status,
            score,
            total_nodes: 0,
            unknown_nodes: 0,
            missing_host_calls: Vec::new(),
        };
    }

    let mut s = NodeStats::default();
    walk_body(&f.body, &mut s);
    let score = if s.total == 0 {
        // Control flow / comments only — no expression nodes, nothing lost.
        1.0
    } else {
        (s.total - s.unknown) as f64 / s.total as f64
    };
    let status = if s.unknown == 0 {
        FnStatus::Clean
    } else {
        FnStatus::Partial
    };
    s.host_calls.sort();
    s.host_calls.dedup();
    FnRecovery {
        name: name.to_string(),
        status,
        score,
        total_nodes: s.total,
        unknown_nodes: s.unknown,
        missing_host_calls: s.host_calls,
    }
}

// ---------------------------------------------------------------------------
// IR traversal
// ---------------------------------------------------------------------------

/// Accumulated traversal statistics for one function body.
#[derive(Default)]
struct NodeStats {
    /// Total expression nodes visited.
    total: usize,
    /// Nodes the decompiler could not lift (each renders as a `todo!()`):
    /// `UnknownVal`, `CyclicSlot`, `RawHostCall`.
    unknown: usize,
    /// `module::function` of each unrecovered `RawHostCall`.
    host_calls: Vec<String>,
}

fn walk_body(body: &[SorobanStmt], s: &mut NodeStats) {
    for st in body {
        walk_stmt(st, s);
    }
}

fn walk_stmt(st: &SorobanStmt, s: &mut NodeStats) {
    match st {
        SorobanStmt::Expr(e) => walk_expr(e, s),
        SorobanStmt::Let { value, .. } => walk_expr(value, s),
        SorobanStmt::Assign { value, .. } => walk_expr(value, s),
        SorobanStmt::Return(Some(e)) => walk_expr(e, s),
        SorobanStmt::Return(None) => {}
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            walk_expr(condition, s);
            walk_body(then_body, s);
            walk_body(else_body, s);
        }
        SorobanStmt::Match { scrutinee, arms } => {
            walk_expr(scrutinee, s);
            for arm in arms {
                if let MatchPattern::Literal(e) = &arm.pattern {
                    walk_expr(e, s);
                }
                walk_body(&arm.body, s);
            }
        }
        SorobanStmt::Loop { body } => walk_body(body, s),
        SorobanStmt::For {
            start, end, body, ..
        } => {
            walk_expr(start, s);
            walk_expr(end, s);
            walk_body(body, s);
        }
        SorobanStmt::Block(b) => walk_body(b, s),
        SorobanStmt::Comment(_) | SorobanStmt::Break | SorobanStmt::Continue => {}
    }
}

/// Visit every expression node, counting totals and the unrecovered markers.
///
/// The match is exhaustive on purpose: if `SorobanExpr` gains a variant, this
/// fails to compile and forces the metric to account for it.
fn walk_expr(e: &SorobanExpr, s: &mut NodeStats) {
    s.total += 1;
    match e {
        // Unrecovered markers (each renders as a `todo!()`).
        SorobanExpr::UnknownVal | SorobanExpr::CyclicSlot { .. } => s.unknown += 1,
        SorobanExpr::RawHostCall {
            module,
            function,
            args,
        } => {
            s.unknown += 1;
            s.host_calls.push(format!("{module}::{function}"));
            for a in args {
                walk_expr(a, s);
            }
        }

        // Leaves with no expression children.
        SorobanExpr::U32Literal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::I64Literal(_)
        | SorobanExpr::U128Literal(_)
        | SorobanExpr::I128Literal(_)
        | SorobanExpr::BoolLiteral(_)
        | SorobanExpr::SymbolLiteral(_)
        | SorobanExpr::StringLiteral(_)
        | SorobanExpr::BytesLiteral(_)
        | SorobanExpr::Void
        | SorobanExpr::None
        | SorobanExpr::Param(_)
        | SorobanExpr::Local(_)
        | SorobanExpr::NamedLocal(_)
        | SorobanExpr::Env
        | SorobanExpr::ContractError { .. }
        | SorobanExpr::Panic
        | SorobanExpr::LedgerSequence
        | SorobanExpr::LedgerTimestamp
        | SorobanExpr::LedgerNetworkId
        | SorobanExpr::CurrentContractAddress
        | SorobanExpr::MaxLiveUntilLedger
        | SorobanExpr::CollectionNew(_)
        | SorobanExpr::ValTagName(_) => {}

        // Single child.
        SorobanExpr::Some(b)
        | SorobanExpr::Not(b)
        | SorobanExpr::RequireAuth(b)
        | SorobanExpr::AuthorizeAsCurrContract(b)
        | SorobanExpr::ErrorFromCode(b)
        | SorobanExpr::PanicWithError(b)
        | SorobanExpr::CryptoSha256(b)
        | SorobanExpr::CryptoKeccak256(b)
        | SorobanExpr::PrngReseed(b)
        | SorobanExpr::PrngBytesNew(b)
        | SorobanExpr::PrngVecShuffle(b)
        | SorobanExpr::StrkeyToAddress(b)
        | SorobanExpr::AddressToStrkey(b)
        | SorobanExpr::SretResult(b)
        | SorobanExpr::ValTag(b)
        | SorobanExpr::ValConvert { value: b, .. }
        | SorobanExpr::CastAs { value: b, .. }
        | SorobanExpr::Try(b) => walk_expr(b, s),

        // Two children.
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Shl(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Rem(a, b)
        | SorobanExpr::Eq(a, b)
        | SorobanExpr::Ne(a, b)
        | SorobanExpr::Lt(a, b)
        | SorobanExpr::Le(a, b)
        | SorobanExpr::Gt(a, b)
        | SorobanExpr::Ge(a, b)
        | SorobanExpr::And(a, b)
        | SorobanExpr::Or(a, b)
        | SorobanExpr::RequireAuthForArgs {
            address: a,
            args: b,
        }
        | SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold: a,
            extend_to: b,
        }
        | SorobanExpr::VecTryIterFold { vec: a, init: b } => {
            walk_expr(a, s);
            walk_expr(b, s);
        }

        // Storage.
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => walk_expr(key, s),
        SorobanExpr::StorageSet { key, value, .. } => {
            walk_expr(key, s);
            walk_expr(value, s);
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            walk_expr(key, s);
            walk_expr(threshold, s);
            walk_expr(extend_to, s);
        }

        // Events / calls.
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics {
                walk_expr(t, s);
            }
            walk_expr(data, s);
        }
        SorobanExpr::InvokeContract {
            address,
            function,
            args,
            ..
        }
        | SorobanExpr::TryInvokeContract {
            address,
            function,
            args,
            ..
        } => {
            walk_expr(address, s);
            walk_expr(function, s);
            for a in args {
                walk_expr(a, s);
            }
        }

        // Constructors / access.
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields {
                walk_expr(v, s);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for v in fields {
                walk_expr(v, s);
            }
        }
        SorobanExpr::TupleConstruct(items)
        | SorobanExpr::VecConstruct(items)
        | SorobanExpr::Log(items) => {
            for v in items {
                walk_expr(v, s);
            }
        }
        SorobanExpr::MapConstruct(pairs) => {
            for (k, v) in pairs {
                walk_expr(k, s);
                walk_expr(v, s);
            }
        }
        SorobanExpr::FieldAccess { object, .. } => walk_expr(object, s),
        SorobanExpr::MethodCall { object, args, .. } => {
            walk_expr(object, s);
            for a in args {
                walk_expr(a, s);
            }
        }

        // Crypto with multiple children.
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            walk_expr(public_key, s);
            walk_expr(message, s);
            walk_expr(signature, s);
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            walk_expr(msg_digest, s);
            walk_expr(signature, s);
            walk_expr(recovery_id, s);
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            walk_expr(low, s);
            walk_expr(high, s);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_both_todo_spellings() {
        let src = r#"
            let a = todo!("unknown value");
            let b = todo !("unknown value");
            let c = todo!("host call: foo");
            fn f() { todo!("decompiled function body") }
            let d = var_12 + var_3;
        "#;
        let c = count_artifacts(src);
        assert_eq!(c.unknown_value, 2, "both todo spellings must count");
        assert_eq!(c.host_call, 1);
        assert_eq!(c.stub, 1);
        assert_eq!(c.var_n, 2);
        assert_eq!(c.total, 6);
    }

    #[test]
    fn var_n_requires_digits_only() {
        // `var_x` and a bare `var_` are not placeholder names.
        let c = count_artifacts("var_x var_ var_1a var_7");
        assert_eq!(c.var_n, 1);
    }

    #[test]
    fn clean_source_counts_zero() {
        let c = count_artifacts("pub fn add(a: u32, b: u32) -> u32 { a + b }");
        assert_eq!(c.total, 0);
    }

    fn empty_fn(return_type: Option<ScSpecTypeDef>, had_host_calls: bool) -> ContractFn {
        ContractFn {
            name: "f".into(),
            params: Vec::new(),
            return_type,
            body: Vec::new(),
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls,
            wasm_param_base: 0,
            wasm_signature: None,
        }
    }

    /// An empty body that must still return a value is rendered by codegen as
    /// `todo!("decompiled function body")` and traps at runtime — grading it
    /// `Trivial`/"fully recovered" is the deceptively-clean bug class.
    ///
    /// Regression: `digicus::version` (`-> u32`) was graded `Trivial` while the
    /// equivalence harness independently recorded it diverging (original
    /// returns `U32(0)`, recompiled traps `Error(Context, InvalidAction)`).
    #[test]
    fn empty_body_returning_a_value_is_logic_lost_not_trivial() {
        let f = empty_fn(Some(ScSpecTypeDef::U32), false);
        let r = score_fn("version", &f);
        assert_eq!(r.status, FnStatus::LogicLost);
        assert_eq!(r.score, 0.0);
        assert!(r.status.is_lost());
        assert!(!r.status.is_fully_recovered());
    }

    #[test]
    fn empty_body_returning_nothing_is_trivial() {
        // No return type at all, and a `Void` return, are both genuine no-ops.
        for rt in [None, Some(ScSpecTypeDef::Void)] {
            let r = score_fn("noop", &empty_fn(rt, false));
            assert_eq!(r.status, FnStatus::Trivial);
            assert_eq!(r.score, 1.0);
        }
    }

    #[test]
    fn host_calls_still_dominate() {
        // Lost logic is lost regardless of return type.
        let r = score_fn("f", &empty_fn(Some(ScSpecTypeDef::Void), true));
        assert_eq!(r.status, FnStatus::LogicLost);
    }

    #[test]
    fn status_classification() {
        assert!(FnStatus::Clean.is_fully_recovered());
        assert!(FnStatus::Trivial.is_fully_recovered());
        assert!(!FnStatus::Partial.is_fully_recovered());
        assert!(FnStatus::LogicLost.is_lost());
        assert!(FnStatus::Missing.is_lost());
        assert!(!FnStatus::Partial.is_lost());
    }

    #[test]
    fn summary_pluralizes_and_counts() {
        let r = RecoveryReport {
            functions: vec![
                FnRecovery {
                    name: "a".into(),
                    status: FnStatus::Clean,
                    score: 1.0,
                    total_nodes: 3,
                    unknown_nodes: 0,
                    missing_host_calls: vec![],
                },
                FnRecovery {
                    name: "b".into(),
                    status: FnStatus::LogicLost,
                    score: 0.0,
                    total_nodes: 0,
                    unknown_nodes: 0,
                    missing_host_calls: vec![],
                },
            ],
            artifacts: ArtifactCounts {
                total: 1,
                ..Default::default()
            },
        };
        assert_eq!(r.spec_functions(), 2);
        assert_eq!(r.fully_recovered(), 1);
        assert_eq!(r.lost(), 1);
        assert_eq!(
            r.summary(),
            "1 of 2 functions fully recovered · 1 unresolved hole"
        );
        assert_eq!(r.lost_functions().count(), 1);
    }
}
