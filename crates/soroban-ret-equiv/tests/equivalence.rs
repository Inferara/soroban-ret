//! Functional-equivalence gate (RFP "run through soroban-env-host, compare
//! outputs against original").
//!
//! For every fixture (and the clean mainnet corpus contracts), decompiles →
//! recompiles → registers both the original and recompiled contract in a
//! `soroban-sdk` test host → invokes each exported function with generated
//! inputs of every spec type, with auth enforced and with auth mocked →
//! compares the two contracts' outcomes.
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

use soroban_ret_equiv::{EquivError, SkipReason, check_equivalence};

/// Max tolerated behavioral divergences (input cases where the original and
/// recompiled contracts differ). A ratchet: drive DOWN as the decompiler
/// recovers more behavior; never raise without understanding the new divergence.
///
/// Measured baseline = 0 (74 fns / 490 cases executed; 63 contracts checked —
/// 39 fixtures + 24 corpus — 100% match): every function the harness can
/// execute behaves like the original on every generated case.
///
/// Previously 2 (issue #69 stages 2–4: digicus `get_repos` /
/// `get_repos_and_issues` read the `repos` map through its proven
/// `unwrap_or(Map::new(&env))` default; that became possible once the
/// `for x in vec.iter()` loops consuming the same map were rebuilt from the
/// proven iterator protocol, so digicus keeps compiling).
/// Previously 4 (issue #69: `version` — a looped parse of a static string —
/// is evaluated as the constant it is; `clear_repos`'s admin check renders
/// its real `panic_with_error!(Error::Unauthorized)` instead of `.unwrap()`).
/// Previously 6 (issue #38 t24 closed the 2 `test_alloc` overflow cases:
/// the byte-count `i32.shl` now renders wrapping-exact `count << 2` instead
/// of `count * 4`, and the vestigial never-read byte-offset counter — whose
/// checked `var_4 + 4` trapped where the original's wrapping add did not —
/// is removed by `remove_dead_carried_counters`; both sides now exhaust the
/// host budget identically on overflow inputs). Previously 8 (t21: the vec
/// accumulator recovered, `count = 0` matched; t23's populate→push value
/// relay then recovered the pushed VALUE, making every in-range case return
/// the correct full vec); 9 before that (t19 unmask: `num_list` first became
/// compilable in this harness, exposing 5 divergences hidden behind a
/// unit-never-type-fallback compile error); before that 4 (digicus); 60 → 4
/// came from the fallible-storage-get recovery
/// (`detect_fallible_storage_get_helper`) eliminating `unknown-oracle`'s 56
/// empty-storage divergences; 75 → 60 from the `checked_add`/`checked_sub`
/// recovery (`recover_checked_arith_from_body`).
///
/// Still 0 after campaign stage 1b, under a much stronger gate: every argument
/// type is generated and each case runs with auth enforced and mocked. The
/// first such run had 404 diverging cases in 11 functions that the
/// integer-only gate had reported as matching (`errors::hello`,
/// `import_contract::safe_add_with*`, unknown-oracle `set_admin` /
/// `set_price` / `upgrade`, fxdao-oracle `init` / `price` / `prices` /
/// `lastprice`, soroswap factory `initialize`). Each was fixed or turned into
/// an honest hole; a case that reaches a `todo!()` is now counted separately
/// ("reached a hole"), neither a match nor a divergence. fxdao-oracle and the
/// soroswap factory no longer recompile (their truncated bodies came back,
/// partly unrecovered), so they are not executed until they compile again.
const DIVERGENCE_CEILING: usize = 0;

/// Minimum functions differentially executed. Guards against silent coverage
/// collapse (a change that stops recompilation or scalar-signature recovery).
/// Measured 146 of the 149 functions in the contracts that recompile (the
/// three others are `__constructor`, `__check_auth` and one function behind
/// a constructor that needs arguments); floored with headroom.
const EXECUTED_FN_FLOOR: usize = 140;

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
    let mut value_cases = 0usize;
    let mut value_fns = 0usize;
    let mut hole_cases = 0usize;
    let mut hole_fns: Vec<String> = Vec::new();
    let mut divergences = Vec::new();
    let mut not_recompilable = Vec::new();
    let mut errored = Vec::new();
    let mut skipped_total = 0usize;
    // Unsupported parameter type → functions it blocks (in recompilable
    // contracts): what a new argument generator would un-skip.
    let mut blocked_by_type: std::collections::BTreeMap<String, usize> = Default::default();
    let mut skipped_by_kind: std::collections::BTreeMap<&'static str, usize> = Default::default();
    let mut json_contracts: Vec<serde_json::Value> = Vec::new();

    for (name, path) in &targets {
        let wasm = fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        // Isolate each contract: a hard panic in one must not abort the gate.
        let result = std::panic::catch_unwind(AssertUnwindSafe(|| check_equivalence(&wasm)));
        match result {
            Ok(Ok(rep)) => {
                exec_fns += rep.executed_fns;
                exec_cases += rep.executed_cases;
                matched += rep.matched_cases;
                value_cases += rep.value_cases;
                value_fns += rep.value_fns;
                hole_cases += rep.hole_cases;
                hole_fns.extend(rep.hole_fns.iter().map(|f| format!("{name}::{f}")));
                eprintln!(
                    "{name}: {} fns / {} cases, {:.1}% match, {} skipped, {} divergences",
                    rep.executed_fns,
                    rep.executed_cases,
                    rep.behavioral_match_pct(),
                    rep.skipped_fns.len(),
                    rep.divergences.len(),
                );
                skipped_total += rep.skipped_fns.len();
                for s in &rep.skipped_fns {
                    eprintln!("    SKIP {name}::{} — {}", s.function, s.reason);
                    *skipped_by_kind.entry(s.reason.kind()).or_insert(0) += 1;
                    if let SkipReason::UnsupportedParamTypes(types) = &s.reason {
                        for t in types {
                            *blocked_by_type.entry(t.clone()).or_insert(0) += 1;
                        }
                    }
                }
                json_contracts.push(serde_json::json!({
                    "contract": name,
                    "status": "executed",
                    "executed_fns": rep.executed_fns,
                    "executed_cases": rep.executed_cases,
                    "matched_cases": rep.matched_cases,
                    "value_cases": rep.value_cases,
                    "value_fns": rep.value_fns,
                    "hole_cases": rep.hole_cases,
                    "hole_fns": rep.hole_fns,
                    "skipped": rep.skipped_fns.iter().map(|s| serde_json::json!({
                        "function": s.function,
                        "kind": s.reason.kind(),
                        "reason": s.reason.to_string(),
                        "unsupported_types": match &s.reason {
                            SkipReason::UnsupportedParamTypes(t) => t.clone(),
                            _ => Vec::new(),
                        },
                    })).collect::<Vec<_>>(),
                    "divergences": rep.divergences.iter().map(|d| serde_json::json!({
                        "function": d.function,
                        "inputs": d.inputs,
                        "original": d.original,
                        "recompiled": d.recompiled,
                    })).collect::<Vec<_>>(),
                }));
                for d in &rep.divergences {
                    eprintln!(
                        "    DIVERGE {name}::{} inputs={} orig={} recomp={}",
                        d.function, d.inputs, d.original, d.recompiled
                    );
                    divergences.push(name.clone());
                }
            }
            Ok(Err(EquivError::NotRecompilable(reason))) => {
                json_contracts.push(serde_json::json!({
                    "contract": name, "status": "not_recompilable", "reason": reason,
                }));
                not_recompilable.push((name.clone(), reason));
            }
            Ok(Err(e)) => {
                json_contracts.push(serde_json::json!({
                    "contract": name, "status": "errored", "reason": format!("{e}"),
                }));
                errored.push((name.clone(), format!("{e}")))
            }
            Err(p) => {
                let msg = p
                    .downcast_ref::<&str>()
                    .map(|s| s.to_string())
                    .or_else(|| p.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "<non-string panic>".to_string());
                json_contracts.push(serde_json::json!({
                    "contract": name, "status": "errored", "reason": format!("panic: {msg}"),
                }));
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
    eprintln!(
        "functions executed:  {exec_fns} of {} in recompilable contracts",
        exec_fns + skipped_total
    );
    eprintln!("functions skipped:   {skipped_total}");
    for (kind, n) in &skipped_by_kind {
        eprintln!("    - {kind}: {n}");
    }
    // Most-blocking types first: the order in which new argument generators
    // pay off. A function with several unsupported types counts under each.
    let mut blockers: Vec<(&String, &usize)> = blocked_by_type.iter().collect();
    blockers.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    eprintln!("blocked by parameter type (functions):");
    for (t, n) in &blockers {
        eprintln!("    - {t}: {n}");
    }
    eprintln!("cases executed:      {exec_cases}");
    eprintln!("behavioral match:    {match_pct:.1}%");
    // How much of the match is real work: the rest agree only on failing
    // (no state is initialised, so most calls stop at the first storage read).
    eprintln!(
        "matched on a value:  {value_cases} cases, in {value_fns} of {exec_fns} executed functions"
    );
    // Cases that stopped at a `todo!()` in the recompiled contract: declared
    // unrecovered by the decompiler, so not comparable.
    eprintln!(
        "reached a hole:      {hole_cases} cases, in {} functions",
        hole_fns.len()
    );
    for f in &hole_fns {
        eprintln!("    - {f}");
    }
    eprintln!(
        "divergences:         {} (ceiling {DIVERGENCE_CEILING})",
        divergences.len()
    );

    // Opt-in machine-readable report of everything above.
    if let Ok(path) = std::env::var("SOROBAN_RET_EQUIV_REPORT") {
        let report = serde_json::json!({
            "contracts_checked": targets.len(),
            "not_recompilable": not_recompilable.len(),
            "errored": errored.len(),
            "functions_executed": exec_fns,
            "functions_skipped": skipped_total,
            "cases_executed": exec_cases,
            "cases_matched": matched,
            "cases_matched_on_value": value_cases,
            "functions_with_a_value_case": value_fns,
            "cases_reaching_a_hole": hole_cases,
            "functions_reaching_a_hole": hole_fns,
            "divergences": divergences.len(),
            "skipped_by_kind": skipped_by_kind,
            "blocked_by_param_type": blocked_by_type,
            "contracts": json_contracts,
        });
        let text = serde_json::to_string_pretty(&report).expect("report serializes");
        fs::write(&path, text).unwrap_or_else(|e| panic!("write {path}: {e}"));
        eprintln!("report written:      {path}");
    }

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
