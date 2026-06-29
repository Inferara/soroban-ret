//! Functional-equivalence harness for `soroban-ret`.
//!
//! Closes the "functional equivalence" gap: instead of merely *type-checking*
//! the decompiled Rust (what `scripts/check-compilable.sh` does), this harness
//!
//! 1. decompiles the original WASM to Rust ([`soroban_ret::decompile_to_ir`]),
//! 2. **recompiles** that Rust to a real `.wasm` contract
//!    ([`recompile_to_wasm`], via `cargo build --target wasm32v1-none`), and
//! 3. registers each of the original and recompiled contract in its own fresh
//!    `soroban-sdk` test [`Env`] (which runs on `soroban-env-host`) per
//!    invocation, invokes each executable exported function with the same
//!    generated inputs, and compares the outcomes (lowered to env-independent
//!    canonical [`ScVal`], so per-side envs are sound — see [`run_side`]).
//!
//! A divergence (same inputs → different result/error/trap on the two
//! contracts) is a decompiler **correctness bug**. The harness also reports a
//! behavioral-match % and coverage so the honest behavioral number is visible.
//!
//! ## Intrinsic coverage limits (by design, documented)
//!
//! Only functions invocable with generated **scalar** arguments
//! (`bool`/`u32`/`i32`/`u64`/`i64`/`u128`/`i128`) and no required storage/auth
//! state are executed. Functions taking aggregate/custom args (`Vec`/`Map`/UDTs/
//! `Address`/`Bytes`/`String`) are skipped, as are `__constructor`/`__check_auth`
//! (the decompiler renames them, so their exports no longer match the original).
//! Contracts whose decompiled output does not recompile are skipped wholesale.
//! This is a correctness sanity-check + behavioral-match metric, **not** a
//! full-corpus differential test.

use std::path::PathBuf;
use std::process::Command;

use soroban_sdk::testutils::EnvTestConfig;
use soroban_sdk::xdr::{Int128Parts, ScVal, UInt128Parts};
use soroban_sdk::{Env, Symbol, TryFromVal, Val, Vec as SVec};
use stellar_xdr::curr::ScSpecTypeDef;

/// A test [`Env`] that does NOT write a snapshot JSON on drop (the harness
/// creates many envs; the default would litter `test_snapshots/`).
fn fresh_env() -> Env {
    Env::new_with_config(EnvTestConfig {
        capture_snapshot_at_drop: false,
    })
}

/// Maximum input vectors generated per function (caps cartesian blow-up).
const MAX_CASES_PER_FN: usize = 48;

/// Errors that abort equivalence checking for a single contract.
#[derive(Debug)]
pub enum EquivError {
    /// The original WASM failed to decompile.
    Decompile(String),
    /// The decompiled Rust did not recompile to a `.wasm` (so it cannot run).
    /// Carries a short reason / compiler stderr tail.
    NotRecompilable(String),
}

impl std::fmt::Display for EquivError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EquivError::Decompile(m) => write!(f, "decompile failed: {m}"),
            EquivError::NotRecompilable(m) => write!(f, "recompile failed: {m}"),
        }
    }
}

impl std::error::Error for EquivError {}

/// A single observed behavioral divergence between original and recompiled.
#[derive(Debug, Clone)]
pub struct Divergence {
    pub function: String,
    pub inputs: String,
    pub original: String,
    pub recompiled: String,
}

/// Result of checking one contract.
#[derive(Debug, Default)]
pub struct EquivReport {
    /// Functions that were invoked on both contracts.
    pub executed_fns: usize,
    /// (function, reason) for each function that could not be executed.
    pub skipped_fns: Vec<(String, String)>,
    /// Total (function, input-vector) cases invoked.
    pub executed_cases: usize,
    /// Cases where original and recompiled produced the same outcome.
    pub matched_cases: usize,
    /// Every observed divergence (an empty vec is the pass condition).
    pub divergences: Vec<Divergence>,
}

impl EquivReport {
    /// Behavioral-match percentage over executed cases (100.0 if none executed).
    pub fn behavioral_match_pct(&self) -> f64 {
        if self.executed_cases == 0 {
            100.0
        } else {
            self.matched_cases as f64 / self.executed_cases as f64 * 100.0
        }
    }

    fn skip(&mut self, name: &str, reason: &str) {
        self.skipped_fns
            .push((name.to_string(), reason.to_string()));
    }
}

/// Outcome of invoking one function with one input vector. `Eq` so the two
/// sides can be compared directly; `ScVal` (XDR) carries the canonical value.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Outcome {
    Value(ScVal),
    /// Returned value could not be lowered to `ScVal` (rare; non-representable).
    Unconvertible,
    /// Contract returned a Soroban `Error` (debug-formatted for stable compare).
    ContractError(String),
    /// Host-level `InvokeError` (wrong arity, missing fn, trap surfaced as error).
    InvokeError(String),
    /// A panic escaped the invocation (caught; the host trapped/aborted).
    Panic,
}

/// Scalar parameter kinds the harness can synthesize inputs for.
#[derive(Clone, Copy)]
enum ParamKind {
    Bool,
    U32,
    I32,
    U64,
    I64,
    U128,
    I128,
}

fn classify(td: &ScSpecTypeDef) -> Option<ParamKind> {
    match td {
        ScSpecTypeDef::Bool => Some(ParamKind::Bool),
        ScSpecTypeDef::U32 => Some(ParamKind::U32),
        ScSpecTypeDef::I32 => Some(ParamKind::I32),
        ScSpecTypeDef::U64 => Some(ParamKind::U64),
        ScSpecTypeDef::I64 => Some(ParamKind::I64),
        ScSpecTypeDef::U128 => Some(ParamKind::U128),
        ScSpecTypeDef::I128 => Some(ParamKind::I128),
        _ => None,
    }
}

fn u128_scval(v: u128) -> ScVal {
    ScVal::U128(UInt128Parts {
        hi: (v >> 64) as u64,
        lo: v as u64,
    })
}

fn i128_scval(v: i128) -> ScVal {
    ScVal::I128(Int128Parts {
        hi: (v >> 64) as i64,
        lo: v as u64,
    })
}

/// Tiny deterministic LCG so fuzz inputs are reproducible without `rand`.
fn lcg(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state
}

/// Candidate inputs for one parameter: boundary values plus a few seeded-random.
fn candidates(kind: ParamKind, seed: &mut u64) -> Vec<ScVal> {
    let r = |s: &mut u64| lcg(s);
    match kind {
        ParamKind::Bool => vec![ScVal::Bool(false), ScVal::Bool(true)],
        ParamKind::U32 => {
            let mut v = vec![0u32, 1, 2, u32::MAX];
            v.push(r(seed) as u32);
            v.into_iter().map(ScVal::U32).collect()
        }
        ParamKind::I32 => {
            let mut v = vec![i32::MIN, -1, 0, 1, i32::MAX];
            v.push(r(seed) as i32);
            v.into_iter().map(ScVal::I32).collect()
        }
        ParamKind::U64 => {
            let mut v = vec![0u64, 1, 2, u64::MAX];
            v.push(r(seed));
            v.into_iter().map(ScVal::U64).collect()
        }
        ParamKind::I64 => {
            let mut v = vec![i64::MIN, -1, 0, 1, i64::MAX];
            v.push(r(seed) as i64);
            v.into_iter().map(ScVal::I64).collect()
        }
        ParamKind::U128 => {
            let mut v = vec![0u128, 1, u128::MAX];
            v.push(((r(seed) as u128) << 64) | r(seed) as u128);
            v.into_iter().map(u128_scval).collect()
        }
        ParamKind::I128 => {
            let mut v = vec![i128::MIN, -1, 0, 1, i128::MAX];
            v.push((((r(seed) as u128) << 64) | r(seed) as u128) as i128);
            v.into_iter().map(i128_scval).collect()
        }
    }
}

/// Build input vectors (cartesian of per-param candidates, capped + sampled).
fn gen_cases(fn_name: &str, kinds: &[ParamKind]) -> Vec<Vec<ScVal>> {
    // Seed from the function name so cases are stable per function across runs.
    let mut seed = fn_name.bytes().fold(0xcbf29ce484222325u64, |h, b| {
        (h ^ b as u64).wrapping_mul(0x100000001b3)
    });
    let per_param: Vec<Vec<ScVal>> = kinds.iter().map(|k| candidates(*k, &mut seed)).collect();

    let mut out: Vec<Vec<ScVal>> = vec![vec![]];
    for cand in &per_param {
        let mut next = Vec::new();
        for prefix in &out {
            for v in cand {
                let mut p = prefix.clone();
                p.push(v.clone());
                next.push(p);
            }
        }
        out = next;
        // Keep the intermediate product bounded.
        if out.len() > MAX_CASES_PER_FN * 8 {
            out.truncate(MAX_CASES_PER_FN * 8);
        }
    }
    if out.len() > MAX_CASES_PER_FN {
        let step = (out.len() / MAX_CASES_PER_FN).max(1);
        out = out
            .into_iter()
            .step_by(step)
            .take(MAX_CASES_PER_FN)
            .collect();
    }
    out
}

/// Recompile decompiled Rust source to a contract `.wasm`.
///
/// Mirrors `scripts/check-compilable.sh` but `cargo build`s (not `check`s) for
/// `wasm32v1-none` so a real artifact is produced. The verify crate lives in
/// `$HOME/.cache/soroban-ret-equiv-verify` so the heavy `soroban-sdk` build is
/// cached across runs; only the tiny `lib.rs` recompiles each call.
///
/// NOTE: the cache dir is shared to preserve that dependency-build cache, so
/// callers must recompile **sequentially**. The sole caller is the single
/// sequential `equivalence_within_ceiling` `#[test]`, so no two recompiles ever
/// race — including under `cargo nextest` (one test ⇒ one caller). Per-contract
/// cache dirs would make it hermetic but rebuild `soroban-sdk` for wasm on every
/// call, which is the dominant cost; that trade-off is deliberately not taken.
pub fn recompile_to_wasm(source: &str) -> Result<Vec<u8>, EquivError> {
    let dir: PathBuf = cache_dir();
    std::fs::create_dir_all(dir.join("src"))
        .map_err(|e| EquivError::NotRecompilable(format!("mkdir: {e}")))?;

    std::fs::write(
        dir.join("Cargo.toml"),
        r#"[package]
name = "equiv-verify"
version = "0.0.0"
edition = "2021"

[dependencies]
soroban-sdk = "=26.0.1"

[lib]
crate-type = ["cdylib"]

# Match the canonical Soroban release profile so overflow semantics line up
# with the original contract (otherwise overflow inputs would "diverge" for a
# reason unrelated to decompilation).
[profile.release]
overflow-checks = true

[workspace]
"#,
    )
    .map_err(|e| EquivError::NotRecompilable(format!("write Cargo.toml: {e}")))?;

    std::fs::write(dir.join("src/lib.rs"), source)
        .map_err(|e| EquivError::NotRecompilable(format!("write lib.rs: {e}")))?;

    let output = Command::new("cargo")
        .current_dir(&dir)
        // Decompiled output legitimately carries warnings (unused vars/imports).
        // Clear any inherited `-D warnings` so they don't fail the recompile.
        .env_remove("RUSTFLAGS")
        .args(["build", "--target", "wasm32v1-none", "--release", "--quiet"])
        .output()
        .map_err(|e| EquivError::NotRecompilable(format!("spawn cargo: {e}")))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let tail: String = stderr.lines().rev().take(6).collect::<Vec<_>>().join(" | ");
        return Err(EquivError::NotRecompilable(tail));
    }

    let artifact = dir.join("target/wasm32v1-none/release/equiv_verify.wasm");
    std::fs::read(&artifact).map_err(|e| {
        EquivError::NotRecompilable(format!("read artifact {}: {e}", artifact.display()))
    })
}

fn cache_dir() -> PathBuf {
    let home = std::env::var("HOME")
        .or_else(|_| std::env::var("USERPROFILE"))
        .unwrap_or_else(|_| ".".to_string());
    PathBuf::from(home).join(".cache/soroban-ret-equiv-verify")
}

/// Fully isolated single invocation: a fresh [`Env`] is created, the contract
/// registered, the function invoked, and the result lowered to a canonical
/// [`ScVal`] — ALL inside one `catch_unwind`, so the env is also dropped inside
/// it. This means a host panic (budget exceeded, trap escalation) OR a
/// poisoned-env drop panic becomes [`Outcome::Panic`] rather than escaping and
/// aborting the whole run. Because the comparison is on env-independent
/// `ScVal`, separate envs per side are correct.
fn run_side(wasm: &[u8], func: &str, inputs: &[ScVal]) -> Outcome {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let env = fresh_env();
        let addr = env.register(wasm, ());
        let mut args = SVec::new(&env);
        for sc in inputs {
            match Val::try_from_val(&env, sc) {
                Ok(v) => args.push_back(v),
                Err(_) => return Outcome::Unconvertible,
            }
        }
        let sym = Symbol::new(&env, func);
        // `try_invoke_contract::<Val, _>` returns
        // `Result<Result<Val, _>, Result<Error, InvokeError>>`. The OUTER result
        // discriminates "the returned `Val` was an error" (`Err`) from "was a
        // normal value" (`Ok`) — the SDK decodes the return value and routes an
        // error Val to the `Err` side. So a contract-returned Soroban error is
        // `Err(Ok(e))`, NOT `Ok(Err(..))`.
        match env.try_invoke_contract::<Val, soroban_sdk::Error>(&addr, &sym, args) {
            Ok(Ok(v)) => match ScVal::try_from_val(&env, &v) {
                Ok(sc) => Outcome::Value(sc),
                Err(_) => Outcome::Unconvertible,
            },
            // Normal value that failed `Val`-conversion. Unreachable for `T = Val`
            // (`Val: TryFromVal<Env, Val>` is infallible — `Ok(*val)`); kept only
            // for match exhaustiveness. This is NOT a contract-error path.
            Ok(Err(_conv)) => Outcome::Unconvertible,
            // Contract / host error. The error value is preserved in the string,
            // so two *different* contract errors compare unequal (a real
            // divergence) rather than collapsing to one bucket.
            Err(Ok(e)) => Outcome::ContractError(format!("{e:?}")),
            Err(Err(ie)) => Outcome::InvokeError(format!("{ie:?}")),
        }
    }))
    .unwrap_or(Outcome::Panic)
}

/// Can this WASM be registered at all (no constructor-arg requirement)? Probed
/// once per contract so constructor-needing contracts are skipped wholesale
/// rather than counted as all-panic "matches".
fn can_register(wasm: &[u8]) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let env = fresh_env();
        let _ = env.register(wasm, ());
    }))
    .is_ok()
}

/// Decompile `original_wasm`, recompile it, then differentially execute every
/// scalar-invocable exported function on both contracts.
pub fn check_equivalence(original_wasm: &[u8]) -> Result<EquivReport, EquivError> {
    let ir = soroban_ret::decompile_to_ir(original_wasm)
        .map_err(|e| EquivError::Decompile(format!("{e:?}")))?;
    let recompiled = recompile_to_wasm(&ir.source)?;

    let mut report = EquivReport::default();

    // Probe registration once (it is contract-level). A constructor that needs
    // args makes `register(wasm, ())` panic on both sides — skip such contracts.
    let registrable = can_register(original_wasm) && can_register(&recompiled);

    for (name, spec_fn) in &ir.registry.functions {
        if name.starts_with("__") {
            report.skip(name, "constructor/check_auth: export renamed by decompiler");
            continue;
        }
        let kinds: Option<Vec<ParamKind>> =
            spec_fn.inputs.iter().map(|i| classify(&i.type_)).collect();
        let Some(kinds) = kinds else {
            report.skip(name, "non-scalar parameter(s)");
            continue;
        };
        if !registrable {
            report.skip(name, "contract not registrable (constructor needs args?)");
            continue;
        }

        let cases = gen_cases(name, &kinds);
        report.executed_fns += 1;

        for inputs in &cases {
            // Each side runs in its own fully-isolated env (see `run_side`).
            let out_orig = run_side(original_wasm, name, inputs);
            let out_recomp = run_side(&recompiled, name, inputs);

            report.executed_cases += 1;
            if out_orig == out_recomp {
                report.matched_cases += 1;
            } else {
                report.divergences.push(Divergence {
                    function: name.clone(),
                    inputs: format!("{inputs:?}"),
                    original: format!("{out_orig:?}"),
                    recompiled: format!("{out_recomp:?}"),
                });
            }
        }
    }

    Ok(report)
}
