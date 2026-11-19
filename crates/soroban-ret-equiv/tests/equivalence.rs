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

use soroban_ret_equiv::{EquivError, Options, SkipReason, check_equivalence_with};

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
///
/// Still 0 after campaign stage 1c, where every function also runs in states
/// the original contract reaches (and callees exist behind an address). The
/// first such run had 17 diverging cases in 3 functions: digicus `config`
/// accepted a second initialisation (a guard whose error path a branch skips
/// was dropped; fixed in the lifter, which also restored guards in eleven
/// other outputs), and unknown-oracle `get_admin` / `get_price` read a stored
/// struct as a bare scalar (now honest holes).
///
/// Campaign stage 1d (a case matches only if the call's effects match too:
/// events, ledger, lifetimes, authorizations) found 100 diverging cases in 3
/// functions that all matched on the return value: `test_errors::hello`
/// stored the integer `1` where the original stores `true` (fixed, with six
/// corpus outputs), and `transfer` in both events fixtures published
/// `to_muxed_id: None` for a muxed address (now an honest hole).
const DIVERGENCE_CEILING: usize = 0;

/// Minimum functions differentially executed. Guards against silent coverage
/// collapse (a change that stops recompilation or signature recovery).
/// Measured 147 of the 149 functions in the contracts that recompile (the
/// two others are `__constructor` and `__check_auth`); floored with headroom.
const EXECUTED_FN_FLOOR: usize = 140;

/// Maximum cases that may reach a `todo!()` hole. A case that reaches a hole
/// is not compared, so without this limit a change that turns working bodies
/// into holes would remove their checks while every other number stayed
/// green. Lower it when holes are filled, and raise it only with the reason
/// recorded here.
///
/// 630 at campaign stage 1c, up from 262: each case now also runs in up to
/// three built states, which multiplies the cases of the functions that
/// already reached a hole (unknown-oracle's four admin-gated setters, 488 of
/// the 630), and three unknown-oracle getters reach their hole only now that
/// the key exists (see [`HOLE_FN_CEILING`]).
///
/// 918 at campaign stage 1d, up from 630: the three events functions below
/// (96 cases each).
const HOLE_CASE_CEILING: usize = 918;

/// Maximum functions with at least one case reaching a hole. Unlike the case
/// count this does not grow with the number of states.
///
/// 9 at campaign stage 1c, up from 6: unknown-oracle `get_price` and
/// `get_admin` were rebuilt as a scalar read of a stored struct and failed on
/// every stored value, so their value is now an honest hole; and
/// `get_transaction_gas_cost_in_usd` always had one, hidden while every call
/// stopped at "no data for chain".
///
/// 12 at campaign stage 1d, up from 9: `test_events::transfer` and
/// `test_events_ref::transfer` published a constant `None` as the muxed id
/// (wrong for every muxed address; seen once events were compared), and
/// `test_events_ref::failed_transfer` got its correct `None` from the same
/// "an unknown value in an `Option` slot is `None`" guess, which is gone.
const HOLE_FN_CEILING: usize = 12;

/// Minimum executed functions with at least one case where both sides
/// returned the same value (not the same error). The second guard against
/// the same loss: a body that degrades to "always fails" on both sides still
/// "matches". 129 of 147 at campaign stage 1c (118 of 146 at stage 1b, before
/// functions ran against built state and reachable callees). 127 at stage
/// 1d: the two `transfer` functions above now stop at a hole.
const VALUE_FN_FLOOR: usize = 127;

/// Minimum functions that match on a returned value in a BUILT state (not
/// the freshly registered one). Guards the state machinery itself: if state
/// discovery or the code swap stops working, every such case silently falls
/// back to comparing "not initialised". Measured 15 (digicus 10,
/// `test_contract_data` 3, unknown-oracle 1, `test_errors` 1).
const STATEFUL_VALUE_FN_FLOOR: usize = 15;

/// Minimum functions with a matched case whose compared effects contained
/// the named effect (campaign stage 1d). "Effects are compared" is only a
/// claim about the cases that had one: these floors keep the comparison from
/// silently shrinking to "two empty lists are equal".
///
/// Measured: writes 9 (digicus 6, `test_contract_data` 2, `test_errors` 1),
/// authorizations 8 (digicus 6, `test_auth` 2).
///
/// Events and lifetime-only changes are at 0, and that is a real gap, not a
/// formality: the only functions in recompilable contracts that publish an
/// event and return are the two `transfer`s, which now stop at a hole (the
/// comparison did run on them: it is what found the wrong muxed id), and
/// every function that extends a lifetime is either a hole or also writes.
/// Raise these as soon as a publishing function compares again.
const EVENT_FN_FLOOR: usize = 0;
const WRITE_FN_FLOOR: usize = 9;
const LIFETIME_FN_FLOOR: usize = 0;
const AUTH_FN_FLOOR: usize = 8;

/// Contracts whose cross-contract calls expect a specific callee. The harness
/// registers it behind the first `Address` candidate; every other contract
/// gets a second copy of itself there.
const CALLEES: &[(&str, &str)] = &[("test_import_contract", "test_add_u64")];

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

    // Development aid: `SOROBAN_RET_EQUIV_ONLY=digicus,test_udt` runs only the
    // contracts whose name contains one of the parts. The coverage floors are
    // not checked on such a partial run; the ceilings still are.
    let only = std::env::var("SOROBAN_RET_EQUIV_ONLY").ok();
    let mut stateful_cases = 0usize;
    let mut stateful_value_cases = 0usize;
    let mut stateful_value_fns = 0usize;
    let mut effects = soroban_ret_equiv::EffectCoverage::default();
    let mut contracts_with_state = 0usize;
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
        if only
            .as_ref()
            .is_some_and(|o| !o.split(',').any(|part| name.contains(part)))
        {
            continue;
        }
        let wasm = fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        // Isolate each contract: a hard panic in one must not abort the gate.
        let callee = CALLEES.iter().find(|(c, _)| c == name).map(|(_, callee)| {
            let p = root.join("tests/fixtures").join(format!("{callee}.wasm"));
            fs::read(&p).unwrap_or_else(|e| panic!("read callee {}: {e}", p.display()))
        });
        let options = Options {
            callee: callee.as_deref(),
        };
        let result =
            std::panic::catch_unwind(AssertUnwindSafe(|| check_equivalence_with(&wasm, &options)));
        match result {
            Ok(Ok(rep)) => {
                exec_fns += rep.executed_fns;
                exec_cases += rep.executed_cases;
                matched += rep.matched_cases;
                value_cases += rep.value_cases;
                value_fns += rep.value_fns;
                hole_cases += rep.hole_cases;
                hole_fns.extend(rep.hole_fns.iter().map(|f| format!("{name}::{f}")));
                stateful_cases += rep.stateful_cases;
                stateful_value_cases += rep.stateful_value_cases;
                stateful_value_fns += rep.stateful_value_fns;
                effects.add(rep.effects);
                if !rep.states.is_empty() {
                    contracts_with_state += 1;
                }
                eprintln!(
                    "{name}: {} fns / {} cases, {:.1}% match, {} skipped, {} divergences",
                    rep.executed_fns,
                    rep.executed_cases,
                    rep.behavioral_match_pct(),
                    rep.skipped_fns.len(),
                    rep.divergences.len(),
                );
                for (i, st) in rep.states.iter().enumerate() {
                    let shown: String = st.chars().take(300).collect();
                    eprintln!("    STATE {} {name}: {shown}", i + 1);
                }
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
                    "states": rep.states,
                    "stateful_cases": rep.stateful_cases,
                    "stateful_value_cases": rep.stateful_value_cases,
                    "stateful_value_fns": rep.stateful_value_fns,
                    "effects": effects_json(&rep.effects),
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
    eprintln!(
        "in a built state:    {stateful_cases} cases in {contracts_with_state} contracts; \
         {stateful_value_cases} matched on a value, in {stateful_value_fns} functions"
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
        "matched on a value:  {value_cases} cases, in {value_fns} of {exec_fns} executed functions (floor {VALUE_FN_FLOOR})"
    );
    // What the compared effects of those cases contained.
    eprintln!("effects compared (matched cases / functions that had one):");
    for (label, c, floor) in [
        ("published an event", effects.events, EVENT_FN_FLOOR),
        ("wrote to the ledger", effects.writes, WRITE_FN_FLOOR),
        (
            "extended a lifetime only",
            effects.lifetimes,
            LIFETIME_FN_FLOOR,
        ),
        ("recorded an authorization", effects.auths, AUTH_FN_FLOOR),
    ] {
        eprintln!(
            "  {label:<26} {} cases, {} functions (floor {floor})",
            c.cases, c.fns
        );
    }
    // Cases that stopped at a `todo!()` in the recompiled contract: declared
    // unrecovered by the decompiler, so not comparable.
    eprintln!(
        "reached a hole:      {hole_cases} cases (ceiling {HOLE_CASE_CEILING}), in {} functions",
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
            "cases_in_a_built_state": stateful_cases,
            "cases_matched_on_value_in_a_built_state": stateful_value_cases,
            "functions_with_a_value_case_in_a_built_state": stateful_value_fns,
            "contracts_with_a_built_state": contracts_with_state,
            "effects": effects_json(&effects),
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
        hole_cases <= HOLE_CASE_CEILING,
        "{hole_cases} cases reach a `todo!()` hole (ceiling {HOLE_CASE_CEILING}): a decompiler \
         change replaced compared behaviour with holes"
    );
    assert!(
        hole_fns.len() <= HOLE_FN_CEILING,
        "{} functions reach a `todo!()` hole (ceiling {HOLE_FN_CEILING})",
        hole_fns.len()
    );
    if only.is_some() {
        eprintln!("partial run (SOROBAN_RET_EQUIV_ONLY): coverage floors not checked");
        return;
    }
    assert!(
        exec_fns >= EXECUTED_FN_FLOOR,
        "differential coverage collapsed: only {exec_fns} functions executed (floor {EXECUTED_FN_FLOOR})"
    );
    assert!(
        stateful_value_fns >= STATEFUL_VALUE_FN_FLOOR,
        "only {stateful_value_fns} functions match on a value in a built state \
         (floor {STATEFUL_VALUE_FN_FLOOR}): state discovery or the code swap regressed"
    );
    assert!(
        value_fns >= VALUE_FN_FLOOR,
        "only {value_fns} functions match on a returned value (floor {VALUE_FN_FLOOR}): \
         compared behaviour was lost"
    );
    for (label, c, floor) in [
        ("publish an event", effects.events, EVENT_FN_FLOOR),
        ("write to the ledger", effects.writes, WRITE_FN_FLOOR),
        (
            "only extend a lifetime",
            effects.lifetimes,
            LIFETIME_FN_FLOOR,
        ),
        ("record an authorization", effects.auths, AUTH_FN_FLOOR),
    ] {
        assert!(
            c.fns >= floor,
            "only {} functions match on a case that does {label} (floor {floor}): \
             compared effects were lost",
            c.fns
        );
    }
}

fn effects_json(e: &soroban_ret_equiv::EffectCoverage) -> serde_json::Value {
    let one =
        |c: soroban_ret_equiv::Covered| serde_json::json!({"cases": c.cases, "functions": c.fns});
    serde_json::json!({
        "published_an_event": one(e.events),
        "wrote_to_the_ledger": one(e.writes),
        "extended_a_lifetime_only": one(e.lifetimes),
        "recorded_an_authorization": one(e.auths),
    })
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
