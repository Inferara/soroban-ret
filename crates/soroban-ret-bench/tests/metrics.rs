//! Metric edge-case + corpus-invariant tests.

use std::path::Path;

use soroban_ret::ir::{ContractFn, SorobanExpr, SorobanStmt};
use soroban_ret_bench::metrics::{self, FnStatus};

fn mk_fn(name: &str, body: Vec<SorobanStmt>, had_host_calls: bool) -> ContractFn {
    ContractFn {
        name: name.to_string(),
        params: Vec::new(),
        return_type: None,
        body,
        takes_env: false,
        is_constructor: false,
        is_check_auth: false,
        wrapper_panics: false,
        had_host_calls,
        wasm_param_base: 0,
        wasm_signature: None,
    }
}

#[test]
fn empty_body_with_host_calls_is_logic_lost() {
    let f = mk_fn("x", vec![], true);
    let r = metrics::score_fn("x", &f);
    assert_eq!(r.status, FnStatus::LogicLost);
    assert_eq!(r.score, 0.0);
}

#[test]
fn empty_body_without_host_calls_is_trivial() {
    let f = mk_fn("x", vec![], false);
    let r = metrics::score_fn("x", &f);
    assert_eq!(r.status, FnStatus::Trivial);
    assert_eq!(r.score, 1.0);
}

#[test]
fn clean_body_scores_one() {
    let body = vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(5)))];
    let r = metrics::score_fn("x", &mk_fn("x", body, false));
    assert_eq!(r.status, FnStatus::Clean);
    assert_eq!(r.score, 1.0);
    assert_eq!(r.unknown_nodes, 0);
}

#[test]
fn partial_body_is_clean_fraction() {
    // Add(U32Literal, UnknownVal): 3 nodes, 1 unknown -> 2/3.
    let body = vec![SorobanStmt::Expr(SorobanExpr::Add(
        Box::new(SorobanExpr::U32Literal(1)),
        Box::new(SorobanExpr::UnknownVal),
    ))];
    let r = metrics::score_fn("x", &mk_fn("x", body, false));
    assert_eq!(r.status, FnStatus::Partial);
    assert_eq!(r.total_nodes, 3);
    assert_eq!(r.unknown_nodes, 1);
    assert!((r.score - 2.0 / 3.0).abs() < 1e-9);
}

#[test]
fn raw_host_call_is_unrecovered_and_named() {
    let body = vec![SorobanStmt::Expr(SorobanExpr::RawHostCall {
        module: "l".to_string(),
        function: "0".to_string(),
        args: vec![],
    })];
    let r = metrics::score_fn("x", &mk_fn("x", body, false));
    assert_eq!(r.status, FnStatus::Partial);
    assert_eq!(r.score, 0.0);
    assert_eq!(r.missing_host_calls, vec!["l::0".to_string()]);
}

#[test]
fn artifact_counting_matches_categories() {
    let src = r#"
        fn a() { todo!("unknown value"); }
        fn b() -> u32 { todo!("host call: l.0"); }
        fn c() { todo!("decompiled function body") }
        fn d() { let var_3 = var_12 + 1; }
    "#;
    let a = metrics::count_artifacts(src);
    assert_eq!(a.unknown_value, 1);
    assert_eq!(a.host_call, 1);
    assert_eq!(a.stub, 1);
    assert_eq!(a.var_n, 2);
    assert_eq!(a.total, 5);
}

/// Run against the in-repo SDK fixtures and assert structural invariants.
#[test]
fn corpus_run_invariants() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures");
    let report = metrics::run(&fixtures).expect("read fixtures dir");
    assert!(!report.contracts.is_empty(), "expected fixture wasm files");
    assert!((0.0..=100.0).contains(&report.overall_restoration));

    for c in &report.contracts {
        assert!((0.0..=100.0).contains(&c.restoration_pct), "{}", c.file);
        // Every spec function lands in exactly one status bucket.
        assert_eq!(
            c.fn_clean + c.fn_partial + c.fn_logic_lost,
            c.spec_functions,
            "bucket sum mismatch for {}",
            c.file
        );
        assert_eq!(c.functions.len(), c.spec_functions, "{}", c.file);
        assert_eq!(
            c.artifacts.total,
            c.artifacts.unknown_value
                + c.artifacts.host_call
                + c.artifacts.stub
                + c.artifacts.var_n,
            "{}",
            c.file
        );
    }
}
