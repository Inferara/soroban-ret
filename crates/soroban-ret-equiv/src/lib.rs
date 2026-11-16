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
//! Arguments of every spec type are generated (see `args`), and each case runs
//! under both [`AuthMode`]s. What is NOT covered: every invocation runs on a
//! fresh instance with **empty storage** and no other contract registered, so a
//! function that needs initialised state is compared only up to its first
//! storage read or cross-contract call; and only the **return outcome** is
//! compared, not events or storage. `__constructor`/`__check_auth` are skipped
//! (not callable as ordinary functions); every skip is reported with its
//! reason ([`SkipReason`]). A case that reaches a `todo!()` hole in the
//! recompiled contract is counted as unverified, not as a match (`mark_holes`).
//! Contracts whose decompiled output does not recompile are skipped wholesale.
//! This is a correctness sanity-check + behavioral-match metric, **not** a
//! full-corpus differential test.

use std::path::PathBuf;
use std::process::Command;

use soroban_sdk::testutils::EnvTestConfig;
use soroban_sdk::xdr::ScVal;
use soroban_sdk::{Address, Env, Symbol, TryFromVal, Val, Vec as SVec};
use stellar_xdr::curr::{ContractId, Hash, ScAddress, ScSpecTypeDef};

mod args;

use args::{Generator, SELF_CONTRACT_ID, select_cases};

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
    /// Each function that could not be executed, and why.
    pub skipped_fns: Vec<SkippedFn>,
    /// Total (function, input-vector, [`AuthMode`]) cases invoked.
    pub executed_cases: usize,
    /// Cases where original and recompiled produced the same outcome.
    pub matched_cases: usize,
    /// Matched cases where both sides returned a value (not an error or a
    /// trap). The rest of the matches agree only on *failing*: without
    /// initialised state most calls stop at the first storage read.
    pub value_cases: usize,
    /// Executed functions with at least one value-returning matched case.
    pub value_fns: usize,
    /// Cases where the recompiled contract reached a `todo!()` hole: the
    /// decompiler declared the value unrecovered, so there is nothing to
    /// compare. Neither a match nor a divergence.
    pub hole_cases: usize,
    /// Executed functions with at least one case that reached a hole.
    pub hole_fns: Vec<String>,
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

    fn skip(&mut self, name: &str, reason: SkipReason) {
        self.skipped_fns.push(SkippedFn {
            function: name.to_string(),
            reason,
        });
    }
}

/// A function the harness did not execute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SkippedFn {
    pub function: String,
    pub reason: SkipReason,
}

/// Why a function was not executed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SkipReason {
    /// `__constructor` / `__check_auth`: not callable as an ordinary function.
    NotDirectlyCallable,
    /// At least one parameter has a type the harness cannot generate values
    /// for. Carries the distinct unsupported parameter types, in signature
    /// order (`Address`, `Vec<String>`, `MyStruct`, …).
    UnsupportedParamTypes(Vec<String>),
    /// The contract cannot be registered without constructor arguments.
    NotRegistrable,
}

impl SkipReason {
    /// A short machine-readable tag for reports.
    pub fn kind(&self) -> &'static str {
        match self {
            SkipReason::NotDirectlyCallable => "not_directly_callable",
            SkipReason::UnsupportedParamTypes(_) => "unsupported_param_types",
            SkipReason::NotRegistrable => "not_registrable",
        }
    }
}

impl std::fmt::Display for SkipReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SkipReason::NotDirectlyCallable => {
                write!(f, "constructor/check_auth: not directly callable")
            }
            SkipReason::UnsupportedParamTypes(t) => {
                write!(f, "unsupported parameter type(s): {}", t.join(", "))
            }
            SkipReason::NotRegistrable => {
                write!(f, "contract not registrable (constructor needs args?)")
            }
        }
    }
}

/// A readable name for a spec type, for skip reasons and reports.
pub fn type_label(td: &ScSpecTypeDef) -> String {
    use ScSpecTypeDef as T;
    match td {
        T::Val => "Val".into(),
        T::Bool => "bool".into(),
        T::Void => "()".into(),
        T::Error => "Error".into(),
        T::U32 => "u32".into(),
        T::I32 => "i32".into(),
        T::U64 => "u64".into(),
        T::I64 => "i64".into(),
        T::Timepoint => "Timepoint".into(),
        T::Duration => "Duration".into(),
        T::U128 => "u128".into(),
        T::I128 => "i128".into(),
        T::U256 => "U256".into(),
        T::I256 => "I256".into(),
        T::Bytes => "Bytes".into(),
        T::String => "String".into(),
        T::Symbol => "Symbol".into(),
        T::Address => "Address".into(),
        T::MuxedAddress => "MuxedAddress".into(),
        T::Option(o) => format!("Option<{}>", type_label(&o.value_type)),
        T::Result(r) => format!(
            "Result<{}, {}>",
            type_label(&r.ok_type),
            type_label(&r.error_type)
        ),
        T::Vec(v) => format!("Vec<{}>", type_label(&v.element_type)),
        T::Map(m) => format!(
            "Map<{}, {}>",
            type_label(&m.key_type),
            type_label(&m.value_type)
        ),
        T::Tuple(t) => format!(
            "({})",
            t.value_types
                .iter()
                .map(type_label)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        T::BytesN(b) => format!("BytesN<{}>", b.n),
        T::Udt(u) => u
            .name
            .to_utf8_string()
            .unwrap_or_else(|_| "<udt>".to_string()),
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

impl Outcome {
    /// Did the (recompiled) contract stop at a `todo!()` hole? See [`mark_holes`].
    fn is_hole(&self) -> bool {
        matches!(self, Outcome::ContractError(e) if *e == format!("Error(Contract, #{HOLE_ERROR_CODE})"))
    }
}

/// Contract error code a reached hole fails with in the recompiled contract
/// (see [`mark_holes`]). Far outside any code a real contract declares, and
/// below `i32::MAX` because the host prints contract codes as signed.
const HOLE_ERROR_CODE: u32 = 2_000_000_001;

/// Make every `todo!()` in decompiled source observable at run time.
///
/// A hole is the decompiler saying "this value was not recovered". Compiled
/// as is, reaching one traps exactly like a `panic!()`, so the harness could
/// not tell an honest hole from wrong recovered code. This shadows `todo!`
/// with a macro that fails with [`HOLE_ERROR_CODE`] instead, so a case that
/// reaches a hole is counted as *unverified* ([`EquivReport::hole_cases`])
/// rather than as a match or a divergence.
fn mark_holes(source: &str) -> String {
    let shadow = format!(
        "#[allow(unused_macros)]\nmacro_rules! todo {{ ($($t:tt)*) => {{ \
         soroban_sdk::panic_with_error!(&soroban_sdk::Env::default(), \
         soroban_sdk::Error::from_contract_error({HOLE_ERROR_CODE})) }}; }}\n"
    );
    // Inner attributes (`#![no_std]`) must stay first; the macro must precede
    // its first use, so it goes right after the last of them.
    let mut insert_at = 0;
    let mut offset = 0;
    for line in source.split_inclusive('\n') {
        offset += line.len();
        if line.trim_start().starts_with("#![") {
            insert_at = offset;
        }
    }
    format!("{}{shadow}{}", &source[..insert_at], &source[insert_at..])
}

/// How authorization is handled for one invocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuthMode {
    /// No authorization is provided: every `require_auth` fails.
    Enforced,
    /// Every `require_auth` succeeds (`mock_all_auths_allowing_non_root_auth`),
    /// so the code behind an auth check runs.
    Mocked,
}

impl AuthMode {
    const ALL: [AuthMode; 2] = [AuthMode::Enforced, AuthMode::Mocked];

    /// A short tag for reports.
    pub fn label(self) -> &'static str {
        match self {
            AuthMode::Enforced => "auth enforced",
            AuthMode::Mocked => "auth mocked",
        }
    }
}

/// Seed for a function's inputs: stable per function name across runs.
fn fn_seed(fn_name: &str) -> u64 {
    fn_name.bytes().fold(0xcbf29ce484222325u64, |h, b| {
        (h ^ b as u64).wrapping_mul(0x100000001b3)
    })
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
fn run_side(wasm: &[u8], func: &str, inputs: &[ScVal], auth: AuthMode) -> Outcome {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let env = fresh_env();
        let addr = register(&env, wasm);
        if auth == AuthMode::Mocked {
            env.mock_all_auths_allowing_non_root_auth();
        }
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
        let _ = register(&env, wasm);
    }))
    .is_ok()
}

/// Register `wasm` at the fixed harness address ([`SELF_CONTRACT_ID`]), so the
/// contract's own address is the same on both sides and can be passed as an
/// argument.
fn register(env: &Env, wasm: &[u8]) -> Address {
    let sc = ScVal::Address(ScAddress::Contract(ContractId(Hash(SELF_CONTRACT_ID))));
    let addr = Address::try_from_val(env, &sc).expect("fixed contract address converts");
    env.register_at(&addr, wasm, ())
}

/// Decompile `original_wasm`, recompile it, then differentially execute every
/// exported function on both contracts.
pub fn check_equivalence(original_wasm: &[u8]) -> Result<EquivReport, EquivError> {
    let ir = soroban_ret::decompile_to_ir(original_wasm)
        .map_err(|e| EquivError::Decompile(format!("{e:?}")))?;
    let recompiled = recompile_to_wasm(&mark_holes(&ir.source))?;

    let mut report = EquivReport::default();

    // Probe registration once (it is contract-level). A constructor that needs
    // args makes `register(wasm, ())` panic on both sides — skip such contracts.
    let registrable = can_register(original_wasm) && can_register(&recompiled);

    for (name, spec_fn) in &ir.registry.functions {
        if name.starts_with("__") {
            report.skip(name, SkipReason::NotDirectlyCallable);
            continue;
        }
        let mut generator = Generator::new(&ir.registry, fn_seed(name));
        let mut per_param: Vec<Vec<ScVal>> = Vec::new();
        let mut unsupported: Vec<String> = Vec::new();
        for input in spec_fn.inputs.iter() {
            match generator.values(&input.type_) {
                Some(values) if !values.is_empty() => per_param.push(values),
                _ => {
                    let label = type_label(&input.type_);
                    if !unsupported.contains(&label) {
                        unsupported.push(label);
                    }
                }
            }
        }
        if !unsupported.is_empty() {
            report.skip(name, SkipReason::UnsupportedParamTypes(unsupported));
            continue;
        }
        if !registrable {
            report.skip(name, SkipReason::NotRegistrable);
            continue;
        }

        let mut seed = fn_seed(name) ^ 0x9e3779b97f4a7c15;
        let cases = select_cases(&per_param, MAX_CASES_PER_FN, &mut seed);
        report.executed_fns += 1;
        let mut returned_a_value = false;
        let mut reached_a_hole = false;

        for inputs in &cases {
            for auth in AuthMode::ALL {
                // Each side runs in its own fully-isolated env (see `run_side`).
                let out_orig = run_side(original_wasm, name, inputs, auth);
                let out_recomp = run_side(&recompiled, name, inputs, auth);

                report.executed_cases += 1;
                if out_recomp.is_hole() {
                    report.hole_cases += 1;
                    reached_a_hole = true;
                } else if out_orig == out_recomp {
                    report.matched_cases += 1;
                    if matches!(out_orig, Outcome::Value(_)) {
                        report.value_cases += 1;
                        returned_a_value = true;
                    }
                } else {
                    report.divergences.push(Divergence {
                        function: name.clone(),
                        inputs: format!("{inputs:?} [{}]", auth.label()),
                        original: format!("{out_orig:?}"),
                        recompiled: format!("{out_recomp:?}"),
                    });
                }
            }
        }
        if returned_a_value {
            report.value_fns += 1;
        }
        if reached_a_hole {
            report.hole_fns.push(name.clone());
        }
    }

    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use stellar_xdr::curr::{
        ScSpecTypeBytesN, ScSpecTypeMap, ScSpecTypeOption, ScSpecTypeTuple, ScSpecTypeUdt,
        ScSpecTypeVec,
    };

    #[test]
    fn type_labels_name_nested_and_user_types() {
        let vec_of_string = ScSpecTypeDef::Vec(Box::new(ScSpecTypeVec {
            element_type: Box::new(ScSpecTypeDef::String),
        }));
        assert_eq!(type_label(&vec_of_string), "Vec<String>");
        assert_eq!(
            type_label(&ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 32 })),
            "BytesN<32>"
        );
        let map = ScSpecTypeDef::Map(Box::new(ScSpecTypeMap {
            key_type: Box::new(ScSpecTypeDef::Address),
            value_type: Box::new(ScSpecTypeDef::Option(Box::new(ScSpecTypeOption {
                value_type: Box::new(ScSpecTypeDef::I128),
            }))),
        }));
        assert_eq!(type_label(&map), "Map<Address, Option<i128>>");
        let tuple = ScSpecTypeDef::Tuple(Box::new(ScSpecTypeTuple {
            value_types: vec![ScSpecTypeDef::U32, ScSpecTypeDef::Symbol]
                .try_into()
                .unwrap(),
        }));
        assert_eq!(type_label(&tuple), "(u32, Symbol)");
        let udt = ScSpecTypeDef::Udt(ScSpecTypeUdt {
            name: "ConfigData".try_into().unwrap(),
        });
        assert_eq!(type_label(&udt), "ConfigData");
    }

    #[test]
    fn skip_reason_names_the_blocking_types() {
        let r = SkipReason::UnsupportedParamTypes(vec!["Address".into(), "Vec<String>".into()]);
        assert_eq!(
            r.to_string(),
            "unsupported parameter type(s): Address, Vec<String>"
        );
        assert_eq!(r.kind(), "unsupported_param_types");
        assert_eq!(SkipReason::NotRegistrable.kind(), "not_registrable");
    }
}
