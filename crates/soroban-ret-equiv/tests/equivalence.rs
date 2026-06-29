//! Functional-equivalence gate (RFP "run through soroban-env-host, compare
//! outputs against original").
//!
//! For every fixture (and the clean mainnet corpus contracts), decompiles →
//! recompiles → registers both the original and recompiled contract in a
//! `soroban-sdk` test host → invokes each scalar-invocable exported function
//! with boundary + seeded-random inputs → compares the two contracts' outcomes.
//!
//! A divergence (same inputs → different result/error/trap) is a decompiler
//! correctness limitation. Some are known and expected (e.g. the decompiler
//! lowers `a.checked_add(b).ok_or(E)` to `Ok(a + b)`, which traps instead of
//! returning `Err` on overflow), so the gate is a **ratchet on the divergence
//! count** — like `corpus_soundness` — plus a behavioral-match metric and a
//! coverage floor. New divergences fail; drive the ceiling down as the
//! decompiler recovers more behavior.
//!
//! Skipped unless `SOROBAN_RET_EQUIV=1` (it `cargo build`s `soroban-sdk` for
//! `wasm32v1-none` — slow). One sequential test on purpose: the recompile step
//! shares a single build-cache dir.
//!
//! ```text
//! SOROBAN_RET_EQUIV=1 cargo test -p soroban-ret-equiv --test equivalence -- --nocapture
//! ```

// `ERRORED_MAX` is a deliberate zero ratchet; the `<= 0` comparison it produces
// is intentional, not an absurd comparison.
#![allow(clippy::absurd_extreme_comparisons)]

use std::fs;
use std::panic::AssertUnwindSafe;
use std::path::PathBuf;

use soroban_ret_equiv::{EquivError, check_equivalence};

/// Max tolerated behavioral divergences (input cases where the original and
/// recompiled contracts differ). A ratchet: drive DOWN as the decompiler
/// recovers more behavior; never raise without understanding the new divergence.
///
/// Measured baseline = 75, all genuine decompiler limitations the harness
/// surfaced (61 fns / 424 cases executed; 62 contracts checked — 38 fixtures +
/// 24 corpus, of which 22 do not yet recompile — 82.3% match):
///   - `test_add_u64` (15): `safe_add`/`safe_add_two` lower
///     `a.checked_add(b).ok_or(E)` to `Ok(a + b)`, so overflow inputs trap on
///     the recompiled contract instead of returning `Err(Overflow)`.
///   - `test_alloc` (4): `num_list` loses its `alloc`-vec population loop and
///     returns an empty `Vec` instead of `[0..count]`.
///   - `unknown-oracle` (56): empty-storage error paths return a host
///     `Context/InvalidAction` error instead of the original's contract error.
const DIVERGENCE_CEILING: usize = 75;

/// Minimum functions differentially executed. Guards against silent coverage
/// collapse (a change that stops recompilation or scalar-signature recovery).
/// Measured 61; floored with headroom.
const EXECUTED_FN_FLOOR: usize = 55;

/// Max contracts that may hard-panic the harness (should be zero).
const ERRORED_MAX: usize = 0;

#[test]
fn equivalence_within_ceiling() {
    if std::env::var("SOROBAN_RET_EQUIV").as_deref() != Ok("1") {
        eprintln!(
            "skipping equivalence: set SOROBAN_RET_EQUIV=1 to run the recompile→host→diff gate \
             (cargo build for wasm32v1-none)"
        );
        return;
    }

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../");
    let targets = collect_targets(&root);
    assert!(!targets.is_empty(), "no target wasm contracts found");

    // The harness deliberately provokes host traps/budget-exhaustion, which the
    // host reports by panicking with a verbose event log. Those panics are
    // caught and recorded; silence the default hook so the output stays
    // readable. Restored before the asserts so a genuine failure still prints.
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let mut exec_fns = 0usize;
    let mut exec_cases = 0usize;
    let mut matched = 0usize;
    let mut divergences = Vec::new();
    let mut not_recompilable = Vec::new();
    let mut errored = Vec::new();

    for (name, path) in &targets {
        let wasm = fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        // Isolate each contract: a hard panic in one must not abort the gate.
        let result = std::panic::catch_unwind(AssertUnwindSafe(|| check_equivalence(&wasm)));
        match result {
            Ok(Ok(rep)) => {
                exec_fns += rep.executed_fns;
                exec_cases += rep.executed_cases;
                matched += rep.matched_cases;
                eprintln!(
                    "{name}: {} fns / {} cases, {:.1}% match, {} skipped, {} divergences",
                    rep.executed_fns,
                    rep.executed_cases,
                    rep.behavioral_match_pct(),
                    rep.skipped_fns.len(),
                    rep.divergences.len(),
                );
                for d in &rep.divergences {
                    eprintln!(
                        "    DIVERGE {name}::{} inputs={} orig={} recomp={}",
                        d.function, d.inputs, d.original, d.recompiled
                    );
                    divergences.push(name.clone());
                }
            }
            Ok(Err(EquivError::NotRecompilable(reason))) => {
                not_recompilable.push((name.clone(), reason));
            }
            Ok(Err(e)) => errored.push((name.clone(), format!("{e}"))),
            Err(p) => {
                let msg = p
                    .downcast_ref::<&str>()
                    .map(|s| s.to_string())
                    .or_else(|| p.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "<non-string panic>".to_string());
                errored.push((name.clone(), format!("panic: {msg}")));
            }
        }
    }

    std::panic::set_hook(prev_hook);

    let match_pct = if exec_cases == 0 {
        100.0
    } else {
        matched as f64 / exec_cases as f64 * 100.0
    };

    eprintln!("\n=== functional-equivalence summary ===");
    eprintln!("contracts checked:   {}", targets.len());
    eprintln!("not recompilable:    {}", not_recompilable.len());
    for (n, r) in &not_recompilable {
        eprintln!("    - {n}: {r}");
    }
    eprintln!("errored:             {}", errored.len());
    for (n, r) in &errored {
        eprintln!("    - {n}: {r}");
    }
    eprintln!("functions executed:  {exec_fns}");
    eprintln!("cases executed:      {exec_cases}");
    eprintln!("behavioral match:    {match_pct:.1}%");
    eprintln!(
        "divergences:         {} (ceiling {DIVERGENCE_CEILING})",
        divergences.len()
    );

    assert!(
        errored.len() <= ERRORED_MAX,
        "{} contract(s) errored/panicked the harness (max {ERRORED_MAX})",
        errored.len()
    );
    assert!(
        divergences.len() <= DIVERGENCE_CEILING,
        "{} behavioral divergence(s) exceed ceiling {DIVERGENCE_CEILING} — a decompiler change \
         introduced new semantic differences between original and recompiled contracts",
        divergences.len()
    );
    assert!(
        exec_fns >= EXECUTED_FN_FLOOR,
        "differential coverage collapsed: only {exec_fns} functions executed (floor {EXECUTED_FN_FLOOR})"
    );
}

/// Fixtures (`tests/fixtures/test_*.wasm`) plus every mainnet corpus contract.
/// Corpus contracts whose decompiled output does not (yet) recompile are routed
/// to the `not_recompilable` bucket by the harness rather than excluded here, so
/// newly-recompilable contracts are picked up and executed automatically.
fn collect_targets(root: &std::path::Path) -> Vec<(String, PathBuf)> {
    let mut out = Vec::new();

    let fixtures = root.join("tests/fixtures");
    if let Ok(entries) = fs::read_dir(&fixtures) {
        let mut fs_paths: Vec<PathBuf> = entries
            .flatten()
            .map(|e| e.path())
            .filter(|p| {
                p.extension().is_some_and(|e| e == "wasm")
                    && p.file_name()
                        .and_then(|n| n.to_str())
                        .is_some_and(|n| n.starts_with("test_"))
            })
            .collect();
        fs_paths.sort();
        for p in fs_paths {
            let name = p.file_stem().unwrap().to_string_lossy().into_owned();
            out.push((name, p));
        }
    }

    // Every corpus contract: the harness recompiles each and drops the ones that
    // do not rebuild into `not_recompilable` (not a failure), so only the
    // recompilable ones are actually executed. This auto-discovery future-proofs
    // the gate — as the decompiler improves and more corpus contracts rebuild,
    // they are executed automatically (today: fxdao-oracle + unknown-oracle), and
    // any new divergence they surface trips the ceiling.
    let mainnet = root.join("benchmark-data/mainnet");
    if let Ok(entries) = fs::read_dir(&mainnet) {
        let mut corpus: Vec<PathBuf> = entries
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|e| e == "wasm"))
            .collect();
        corpus.sort();
        for p in corpus {
            let name = p
                .file_name()
                .unwrap()
                .to_string_lossy()
                .trim_end_matches(".wasm")
                .to_string();
            out.push((name, p));
        }
    }

    out
}
