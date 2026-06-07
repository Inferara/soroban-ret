//! Pins the verdict boundary semantics of `diff()`.
//!
//! Restoration percentages are quantized to 0.1 pp at source (metrics.rs), so
//! `diff()` rounds `c - b` to the same quantum before classifying. These tests
//! guard against "classify the unrounded delta" refactors: for over half of
//! all 1-dp pairs exactly one quantum apart, the f64 subtraction lands epsilon
//! above 0.1 (e.g. `0.4 - 0.3 = 0.10000000000000003`), which would flip an
//! at-tolerance NoChange into a false Improved/Reduced.

use soroban_ret_bench::diff::{Verdict, diff};
use soroban_ret_bench::metrics::{
    ArtifactCounts, Baseline, BaselineContract, BenchReport, ContractBench,
};

fn contract(file: &str, pct: f64) -> ContractBench {
    ContractBench {
        file: file.to_string(),
        entity: None,
        contract_id: None,
        wasm_size: 0,
        restoration_pct: pct,
        spec_functions: 0,
        fn_clean: 0,
        fn_partial: 0,
        fn_logic_lost: 0,
        artifacts: ArtifactCounts::default(),
        disasm_ms: 0.0,
        total_ms: 0.0,
        sdk_version: None,
        standard_interfaces: vec![],
        diagnostics: vec![],
        error: None,
        functions: vec![],
    }
}

fn baseline_contract(file: &str, pct: f64) -> BaselineContract {
    BaselineContract {
        file: file.to_string(),
        entity: None,
        restoration_pct: pct,
        spec_functions: 0,
        fn_clean: 0,
        fn_partial: 0,
        fn_logic_lost: 0,
        artifacts_total: 0,
        wasm_size: 0,
        error: None,
    }
}

/// A delta of exactly one quantum (0.1 pp) is *within* the ±0.1 tolerance and
/// must classify NoChange for every 1-dp pair in 0..=100, regardless of float
/// representation noise in the subtraction.
#[test]
fn exact_tolerance_delta_is_no_change_despite_float_noise() {
    let files: Vec<String> = (0..=1000).map(|i| format!("c{i:04}.wasm")).collect();
    let report = BenchReport {
        corpus: "test".into(),
        overall_restoration: 50.1,
        contracts: files
            .iter()
            .enumerate()
            .map(|(i, f)| contract(f, (i as f64 + 1.0) / 10.0))
            .collect(),
    };
    let baseline = Baseline {
        corpus: "test".into(),
        overall_restoration: 50.0,
        contracts: files
            .iter()
            .enumerate()
            .map(|(i, f)| baseline_contract(f, i as f64 / 10.0))
            .collect(),
    };

    let d = diff(&report, &baseline, 0.1);
    assert_eq!(
        (d.improved, d.reduced, d.no_change),
        (0, 0, 1001),
        "an exactly-at-tolerance delta must never count as improved/reduced"
    );
    assert_eq!(d.overall_verdict, Verdict::NoChange);
    assert!(
        d.deltas
            .iter()
            .all(|x| x.verdict == Verdict::NoChange && x.delta == 0.1),
        "every per-contract delta must round to exactly one quantum"
    );
}

/// One quantum beyond tolerance classifies; at/below does not.
#[test]
fn two_quantum_delta_classifies() {
    let report = BenchReport {
        corpus: "test".into(),
        overall_restoration: 90.0,
        contracts: vec![
            contract("up.wasm", 90.4),   // +0.2 → Improved
            contract("down.wasm", 90.1), // -0.2 → Reduced
            contract("flat.wasm", 90.3), //  0.0 → NoChange
        ],
    };
    let baseline = Baseline {
        corpus: "test".into(),
        overall_restoration: 90.0,
        contracts: vec![
            baseline_contract("up.wasm", 90.2),
            baseline_contract("down.wasm", 90.3),
            baseline_contract("flat.wasm", 90.3),
        ],
    };

    let d = diff(&report, &baseline, 0.1);
    assert_eq!((d.improved, d.reduced, d.no_change), (1, 1, 1));
    let by_file = |f: &str| d.deltas.iter().find(|x| x.file == f).unwrap().verdict;
    assert_eq!(by_file("up.wasm"), Verdict::Improved);
    assert_eq!(by_file("down.wasm"), Verdict::Reduced);
    assert_eq!(by_file("flat.wasm"), Verdict::NoChange);
}
