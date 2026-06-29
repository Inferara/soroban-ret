//! Structural-plausibility ratchet (RFP "structurally plausible").
//!
//! Turns the corpus restoration numbers — previously *report-only* in
//! `benchmark.yml` — into an asserted gate. Decompiles every mainnet corpus
//! contract and compares its per-contract recovery against the committed
//! `benchmark-data/baseline.json`, FAILING if any contract regresses:
//!
//! - fewer clean functions (`fn_clean` down),
//! - more functions whose real logic was lost (`fn_logic_lost` up), or
//! - more decompilation artifacts (`artifacts.total` up).
//!
//! Improvements always pass. An intentional change that legitimately alters
//! these counts must refresh the baseline in the same PR
//! (`scripts/rebuild-benchmark-baseline.sh`) — the same workflow as the
//! `corpus_soundness` ceiling. Decompilation is deterministic, so the
//! comparison is exact (no tolerance).
//!
//! Fast (decompile only, no wasm build) → runs in the default `cargo test`.

use std::collections::BTreeMap;
use std::path::PathBuf;

use soroban_ret_bench::metrics::{Baseline, run};

#[test]
fn corpus_plausibility_no_regression() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../");
    let corpus = root.join("benchmark-data/mainnet");
    let baseline_path = root.join("benchmark-data/baseline.json");

    let report = run(&corpus).expect("benchmark run failed");

    let baseline_text =
        std::fs::read_to_string(&baseline_path).expect("read benchmark-data/baseline.json");
    let baseline: Baseline =
        serde_json::from_str(&baseline_text).expect("parse benchmark-data/baseline.json");
    let by_file: BTreeMap<&str, _> = baseline
        .contracts
        .iter()
        .map(|c| (c.file.as_str(), c))
        .collect();

    let mut regressions = Vec::new();
    let mut checked = 0usize;

    for c in &report.contracts {
        let Some(base) = by_file.get(c.file.as_str()) else {
            // A newly-added corpus contract with no baseline entry: skip (the
            // baseline refresh on main will pick it up). Don't fail on it.
            eprintln!(
                "{}: no baseline entry (new contract) — not ratcheted",
                c.file
            );
            continue;
        };
        checked += 1;

        if c.fn_clean < base.fn_clean {
            regressions.push(format!(
                "{}: clean functions {} -> {} (regressed)",
                c.file, base.fn_clean, c.fn_clean
            ));
        }
        if c.fn_logic_lost > base.fn_logic_lost {
            regressions.push(format!(
                "{}: logic-lost functions {} -> {} (regressed)",
                c.file, base.fn_logic_lost, c.fn_logic_lost
            ));
        }
        if c.artifacts.total > base.artifacts_total {
            regressions.push(format!(
                "{}: artifacts {} -> {} (regressed)",
                c.file, base.artifacts_total, c.artifacts.total
            ));
        }
    }

    eprintln!(
        "\n=== corpus structural-plausibility ratchet ===\n\
         contracts checked: {checked}\nregressions: {}",
        regressions.len()
    );
    for r in &regressions {
        eprintln!("  {r}");
    }

    assert!(
        checked > 0,
        "no corpus contracts matched the baseline — wrong path or empty baseline?"
    );
    assert!(
        regressions.is_empty(),
        "{} structural-plausibility regression(s) vs benchmark-data/baseline.json — a change made \
         decompiled output less complete; investigate, or refresh the baseline if intentional",
        regressions.len()
    );
}
