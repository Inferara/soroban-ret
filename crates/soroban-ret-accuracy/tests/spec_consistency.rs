//! Spec-consistency gate (RFP "spec-consistent").
//!
//! For every fixture and mainnet corpus contract, decompiles and asserts the
//! generated Rust is consistent with the contract's own `contractspecv0`:
//!
//! - **Hard, per set:** no exported spec function is dropped or emitted with the
//!   wrong arity, and no extra exported functions are invented. Fixtures must be
//!   perfectly consistent (0 violations); the corpus is a downward ratchet.
//! - **Ratchet:** aggregate signature/type similarity scores stay at or above a
//!   measured floor.
//!
//! Fast (decompile + `syn`, no wasm build), so it runs in the default
//! `cargo test` — no env gate.

// Several ratchet ceilings are legitimately zero today and may rise later; the
// `count <= CEILING` comparisons that produces (`<= 0`) are intentional ratchets,
// not absurd comparisons.
#![allow(clippy::absurd_extreme_comparisons)]

use std::fs;
use std::path::{Path, PathBuf};

use soroban_ret_accuracy::spec_compare::check_spec_consistency;

// --- Ratchets (drive consistency up; never loosen without understanding why) ---
// Calibrated from the first measured run (62 contracts: 38 fixtures + 24 corpus):
// 0 fn-violations / 0 extra fns on BOTH sets; mean signatures 98.9%, types 98.6%.
/// Fixtures are the controlled set: they must be perfectly spec-consistent.
const FIXTURE_FN_VIOLATIONS_MAX: usize = 0;
const FIXTURE_EXTRA_FNS_MAX: usize = 0;
/// Even the mainnet corpus currently emits every spec function with correct
/// arity and invents none — hold that hard guarantee at zero.
const CORPUS_FN_VIOLATIONS_MAX: usize = 0;
const CORPUS_EXTRA_FNS_MAX: usize = 0;
/// Aggregate similarity floors (mean across all contracts), percent. Set just
/// below the measured means to absorb float noise; raise as recovery improves.
const SIGNATURES_SCORE_FLOOR: f64 = 98.0;
const TYPES_SCORE_FLOOR: f64 = 98.0;

#[test]
fn spec_consistency_within_floor() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../");

    let fixtures = collect(&root.join("tests/fixtures"), "test_", ".wasm");
    let corpus = collect(&root.join("benchmark-data/mainnet"), "", ".wasm");
    assert!(!fixtures.is_empty(), "no fixtures found");
    assert!(!corpus.is_empty(), "no corpus contracts found");

    let mut fixture_violations = 0usize;
    let mut fixture_extra = 0usize;
    let mut corpus_violations = 0usize;
    let mut corpus_extra = 0usize;
    let mut sig_sum = 0.0;
    let mut types_sum = 0.0;
    let mut scored = 0usize;
    let mut detail = Vec::new();

    for (label, set, is_fixture) in [("fixture", &fixtures, true), ("corpus", &corpus, false)] {
        for (name, path) in set {
            let wasm = fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            let ir = match soroban_ret::decompile_to_ir(&wasm) {
                Ok(ir) => ir,
                Err(e) => panic!("{label} {name}: decompile failed: {e:?}"),
            };
            let report = check_spec_consistency(&ir.registry, &ir.source)
                .unwrap_or_else(|e| panic!("{label} {name}: extract failed: {e}"));

            sig_sum += report.signatures_score;
            types_sum += report.types_score;
            scored += 1;

            if is_fixture {
                fixture_violations += report.fn_violations.len();
                fixture_extra += report.extra_fns.len();
            } else {
                corpus_violations += report.fn_violations.len();
                corpus_extra += report.extra_fns.len();
            }

            if !report.fn_violations.is_empty() || !report.extra_fns.is_empty() {
                detail.push(format!(
                    "{label} {name}: {} fn-violations {:?}, {} extra {:?} (sig {:.1}, types {:.1})",
                    report.fn_violations.len(),
                    report.fn_violations,
                    report.extra_fns.len(),
                    report.extra_fns,
                    report.signatures_score,
                    report.types_score,
                ));
            }
        }
    }

    let sig_mean = sig_sum / scored as f64;
    let types_mean = types_sum / scored as f64;

    eprintln!("\n=== spec-consistency summary ({scored} contracts) ===");
    eprintln!("fixture fn-violations: {fixture_violations}, extra fns: {fixture_extra}");
    eprintln!("corpus  fn-violations: {corpus_violations}, extra fns: {corpus_extra}");
    eprintln!("mean signatures score: {sig_mean:.1}%");
    eprintln!("mean types score:      {types_mean:.1}%");
    for d in &detail {
        eprintln!("  {d}");
    }

    assert!(
        fixture_violations <= FIXTURE_FN_VIOLATIONS_MAX,
        "fixtures have {fixture_violations} spec fn-violations (max {FIXTURE_FN_VIOLATIONS_MAX})"
    );
    assert!(
        fixture_extra <= FIXTURE_EXTRA_FNS_MAX,
        "fixtures have {fixture_extra} extra (non-spec) functions (max {FIXTURE_EXTRA_FNS_MAX})"
    );
    assert!(
        corpus_violations <= CORPUS_FN_VIOLATIONS_MAX,
        "corpus has {corpus_violations} spec fn-violations (ceiling {CORPUS_FN_VIOLATIONS_MAX})"
    );
    assert!(
        corpus_extra <= CORPUS_EXTRA_FNS_MAX,
        "corpus has {corpus_extra} extra (non-spec) functions (ceiling {CORPUS_EXTRA_FNS_MAX})"
    );
    assert!(
        sig_mean >= SIGNATURES_SCORE_FLOOR,
        "mean signature score {sig_mean:.1}% below floor {SIGNATURES_SCORE_FLOOR}%"
    );
    assert!(
        types_mean >= TYPES_SCORE_FLOOR,
        "mean type score {types_mean:.1}% below floor {TYPES_SCORE_FLOOR}%"
    );
}

fn collect(dir: &Path, prefix: &str, suffix: &str) -> Vec<(String, PathBuf)> {
    let mut out = Vec::new();
    if let Ok(entries) = fs::read_dir(dir) {
        for e in entries.flatten() {
            let p = e.path();
            let fname = p.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if fname.starts_with(prefix) && fname.ends_with(suffix) {
                out.push((fname.trim_end_matches(suffix).to_string(), p));
            }
        }
    }
    out.sort();
    out
}
