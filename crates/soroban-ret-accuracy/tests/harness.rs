//! End-to-end and serialization tests for the accuracy harness.
//!
//! - `serde_round_trip` locks the on-disk contract of `accuracy-baseline.json`:
//!   the `--against` regression gate deserializes exactly what `--json` wrote, so
//!   the persisted fields (contracts/levels/overall) must round-trip unchanged.
//! - `e2e_known_anchors` exercises the real discover→decompile→score pipeline over
//!   the committed fixtures and pins a few invariants. It skips cleanly when the
//!   `vendor/rs-soroban-sdk` submodule is absent so a fresh checkout still builds.

use std::collections::BTreeMap;
use std::path::PathBuf;

use soroban_ret_accuracy::metrics::{AccuracyReport, ContractReport};
use soroban_ret_accuracy::report::render_json;
use soroban_ret_accuracy::test_harness::{discover_contracts, run_accuracy};

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."))
}

#[test]
fn serde_round_trip_preserves_persisted_fields() {
    let mut contracts = BTreeMap::new();
    contracts.insert(
        "sample".to_string(),
        ContractReport {
            name: "sample".to_string(),
            level: 3,
            types_score: 100.0,
            signatures_score: 90.0,
            annotations_score: 80.0,
            bodies_score: 70.0,
            structure_score: 60.0,
            overall_score: 84.0,
            artifact_score: 100.0,
            functions: BTreeMap::new(),
            error: None,
        },
    );
    let report = AccuracyReport::from_contracts(contracts);

    let json = render_json(&report);
    let restored: AccuracyReport =
        serde_json::from_str(&json).expect("baseline JSON must deserialize");

    // The fields the `--against` gate relies on must survive the round-trip.
    assert_eq!(restored.overall_score, report.overall_score);
    assert_eq!(restored.contracts.len(), report.contracts.len());
    let orig = &report.contracts["sample"];
    let back = &restored.contracts["sample"];
    assert_eq!(back.overall_score, orig.overall_score);
    assert_eq!(back.level, orig.level);
    assert_eq!(back.bodies_score, orig.bodies_score);
    assert_eq!(restored.levels.get(&3).map(|l| l.average), Some(84.0));
}

#[test]
fn e2e_known_anchors() {
    let root = project_root();
    let fixtures_dir = root.join("tests").join("fixtures");
    let sdk_tests_dir = root.join("vendor").join("rs-soroban-sdk").join("tests");

    if !sdk_tests_dir.is_dir() {
        eprintln!(
            "skipping e2e_known_anchors: submodule not checked out at {}",
            sdk_tests_dir.display()
        );
        return;
    }

    let contracts = discover_contracts(&fixtures_dir, &sdk_tests_dir);
    assert!(
        contracts.len() >= 30,
        "expected the full fixture set, found {}",
        contracts.len()
    );

    let report = run_accuracy(&contracts, None);

    // A healthy scored set, with the one source-less fixture surfaced as skipped
    // rather than silently dropped (guards against a missing-submodule false high).
    assert!(
        report.scored_count >= 30,
        "implausibly few contracts scored: {}",
        report.scored_count
    );
    assert!(
        report.skipped.contains(&"liquidity_pool".to_string()),
        "liquidity_pool (no reference source) should be reported as skipped, got {:?}",
        report.skipped
    );

    // Anchors that must hold after the v26.0.1 decompiler fixes.
    let errors = report
        .contracts
        .get("errors")
        .expect("errors contract must be scored");
    assert!(
        errors.overall_score >= 99.0,
        "errors regressed to {}",
        errors.overall_score
    );
    let fuzz = report
        .contracts
        .get("fuzz")
        .expect("fuzz contract must be scored");
    assert!(
        fuzz.overall_score >= 99.0,
        "fuzz regressed to {}",
        fuzz.overall_score
    );

    // Every complexity level must still meet its target on average.
    for (level, summary) in &report.levels {
        assert!(
            summary.meets_target,
            "level {} below target: avg {} < {}",
            level, summary.average, summary.target
        );
    }
    assert!(
        report.overall_score >= 95.0,
        "overall accuracy regressed to {}",
        report.overall_score
    );
}
