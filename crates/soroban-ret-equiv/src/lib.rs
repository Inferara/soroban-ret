//! Functional-equivalence harness for `soroban-ret`.
//!
//! Closes the "functional equivalence" gap: instead of merely *type-checking*
//! the decompiled Rust (what `scripts/check-compilable.sh` does), this harness
//!
//! 1. decompiles the original WASM to Rust ([`soroban_ret::decompile_to_ir`]),
//! 2. **recompiles** that Rust to a real `.wasm` contract
//!    ([`recompile_to_wasm`], via `cargo build --target wasm32v1-none`), and
//! 3. runs every exported function on both contracts with the same generated
//!    inputs, **from the same ledger state**, and compares the outcomes
//!    (lowered to canonical [`ScVal`]).
//!
//! A divergence (same inputs → different result/error/trap on the two
//! contracts) is a decompiler **correctness bug**. The harness also reports a
//! behavioral-match % and coverage so the honest behavioral number is visible.
//!
//! ## States
//!
//! A call on a freshly registered contract mostly compares "not initialised".
//! So each function is run in several states: as registered, and in up to
//! `MAX_STATES` further states found by calling the **original** contract
//! (`discover_states`: a call that returns a value and changes the ledger
//! builds the next state). The recompiled contract is then put in the
//! original's place in that same ledger (`state`), so a hole in a recompiled
//! setter does not stop its getters from being compared against real data,
//! and a recompiled contract that reads stored data differently diverges
//! visibly. Values stored by the state-building calls are offered first as
//! later arguments, so a getter is asked about a key that exists.
//!
//! A callee contract is registered behind the first `Address` candidate
//! ([`Options::callee`]), and a constructor that needs arguments is given
//! generated ones.
//!
//! ## Intrinsic coverage limits (by design, documented)
//!
//! Arguments of every spec type are generated (see `args`), and each case runs
//! under both [`AuthMode`]s. What is NOT covered: the states are the ones a
//! short greedy search reaches, not every reachable state; and only the
//! **return outcome** is compared, not events or the resulting storage (a
//! wrong write is seen only if a later-compared read returns it, and the
//! state for that read is built by the original). `__constructor` /
//! `__check_auth` are not called as ordinary functions; every skip is reported
//! with its reason ([`SkipReason`]). A case that reaches a `todo!()` hole in
//! the recompiled contract is counted as unverified, not as a match
//! (`mark_holes`). Contracts whose decompiled output does not recompile are
//! skipped wholesale. This is a correctness sanity-check + behavioral-match
//! metric, **not** a full-corpus differential test.

use std::path::PathBuf;
use std::process::Command;

use soroban_sdk::xdr::ScVal;
use stellar_xdr::curr::ScSpecTypeDef;

mod args;
mod state;

use args::{CALLEE_CONTRACT_ID, Generator, Preferred, remember, select_cases};
use state::{Callee, World};

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
    /// The states built beyond the freshly registered one, each described
    /// by the calls on the original contract that led to it.
    pub states: Vec<String>,
    /// Cases run in one of [`Self::states`] (the rest ran as registered).
    pub stateful_cases: usize,
    /// Value-returning matched cases in one of [`Self::states`].
    pub stateful_value_cases: usize,
    /// Executed functions with a value-returning match in one of
    /// [`Self::states`].
    pub stateful_value_fns: usize,
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

/// How many states beyond the freshly registered one are built per contract.
const MAX_STATES: usize = 3;

/// Constructor argument vectors tried before giving up on registration.
const MAX_CONSTRUCTOR_TRIES: usize = 16;

/// What the harness registers next to the contract under test.
#[derive(Default)]
pub struct Options<'a> {
    /// The contract behind the first `Address` candidate, for cross-contract
    /// calls. Defaults to a second copy of the original contract (the same
    /// callee on both sides, so only the caller differs).
    pub callee: Option<&'a [u8]>,
}

/// One state the contract is exercised in.
struct State {
    /// The calls that built it, for reports. Empty for the registered state.
    label: String,
    world: World,
}

/// Input vectors for `spec_fn`, or the labels of the parameter types that
/// cannot be generated.
fn cases_for(
    reg: &soroban_ret::TypeRegistry,
    name: &str,
    inputs: &[ScSpecTypeDef],
    preferred: &Preferred,
) -> Result<Vec<Vec<ScVal>>, Vec<String>> {
    let mut generator = Generator::new(reg, fn_seed(name)).with_context(preferred, &[]);
    let mut per_param: Vec<Vec<ScVal>> = Vec::new();
    let mut unsupported: Vec<String> = Vec::new();
    for td in inputs {
        match generator.values(td) {
            Some(values) if !values.is_empty() => per_param.push(values),
            _ => {
                let label = type_label(td);
                if !unsupported.contains(&label) {
                    unsupported.push(label);
                }
            }
        }
    }
    if !unsupported.is_empty() {
        return Err(unsupported);
    }
    let mut seed = fn_seed(name) ^ 0x9e3779b97f4a7c15;
    Ok(select_cases(&per_param, MAX_CASES_PER_FN, &mut seed))
}

/// Register the original contract: with no constructor arguments if that
/// works, otherwise with the first generated argument vector its constructor
/// accepts. Returns the world, the arguments used, and whether the callee
/// was registered next to it.
fn register_original(
    wasm: &[u8],
    reg: &soroban_ret::TypeRegistry,
    callee: &[u8],
) -> Option<(World, Vec<ScVal>, bool)> {
    let with_callee = [Callee {
        id: CALLEE_CONTRACT_ID,
        wasm: callee,
    }];
    // A callee that cannot be registered on its own (its constructor needs
    // arguments) is left out rather than blocking the contract under test.
    let callee_sets: [&[Callee<'_>]; 2] = [&with_callee, &[]];
    let ctor_inputs: Vec<ScSpecTypeDef> = reg
        .functions
        .iter()
        .find(|(n, _)| n.as_str() == "__constructor")
        .map(|(_, f)| f.inputs.iter().map(|i| i.type_.clone()).collect())
        .unwrap_or_default();
    let arg_sets: Vec<Vec<ScVal>> = if ctor_inputs.is_empty() {
        vec![Vec::new()]
    } else {
        let mut sets = cases_for(reg, "__constructor", &ctor_inputs, &Preferred::new()).ok()?;
        sets.truncate(MAX_CONSTRUCTOR_TRIES);
        sets
    };
    for callees in callee_sets {
        for args in &arg_sets {
            if let Some(world) = World::new(wasm, args, callees) {
                return Some((world, args.clone(), !callees.is_empty()));
            }
        }
    }
    None
}

/// Find states the contract reaches. From the current state, every function
/// is called on the ORIGINAL contract with its generated cases under mocked
/// auth; a call that returns a value and changes the ledger builds the next
/// state. Functions not used yet are preferred, then the call that changes
/// the most entries, then spec order. The arguments of each chosen call are
/// remembered so later calls can refer to what was stored.
fn discover_states(
    base: World,
    reg: &soroban_ret::TypeRegistry,
    preferred: &mut Preferred,
) -> Vec<State> {
    let mut states = vec![State {
        label: String::new(),
        world: base,
    }];
    let mut used: Vec<String> = Vec::new();
    for _ in 0..MAX_STATES {
        let current = states.last().expect("at least the registered state");
        // (function already used, entries changed) — smaller is better for
        // the first, larger for the second.
        let mut best: Option<(bool, usize, String, Vec<ScVal>, World)> = None;
        for (name, spec_fn) in &reg.functions {
            if name.starts_with("__") {
                continue;
            }
            let inputs: Vec<ScSpecTypeDef> =
                spec_fn.inputs.iter().map(|i| i.type_.clone()).collect();
            let Ok(cases) = cases_for(reg, name, &inputs, preferred) else {
                continue;
            };
            let reused = used.contains(name);
            for case in cases {
                let (out, after) = current.world.call(name, &case, AuthMode::Mocked);
                let (Outcome::Value(_), Some(after)) = (out, after) else {
                    continue;
                };
                let changed = current.world.entries_changed(&after);
                if changed == 0 {
                    continue;
                }
                let better = match &best {
                    None => true,
                    Some((b_reused, b_changed, ..)) => {
                        (!reused && *b_reused) || (reused == *b_reused && changed > *b_changed)
                    }
                };
                if better {
                    best = Some((reused, changed, name.clone(), case, after));
                }
            }
        }
        let Some((_, _, name, case, world)) = best else {
            break;
        };
        if let Some((_, spec_fn)) = reg.functions.iter().find(|(n, _)| **n == name) {
            for (input, value) in spec_fn.inputs.iter().zip(&case) {
                remember(preferred, &input.type_, value);
            }
        }
        let step = format!("{name}({case:?})");
        let label = if current.label.is_empty() {
            step
        } else {
            format!("{}; {step}", current.label)
        };
        used.push(name);
        states.push(State { label, world });
    }
    states
}

/// Decompile `original_wasm`, recompile it, then differentially execute every
/// exported function on both contracts, in every state the original reaches
/// (see [`discover_states`]).
pub fn check_equivalence(original_wasm: &[u8]) -> Result<EquivReport, EquivError> {
    check_equivalence_with(original_wasm, &Options::default())
}

/// [`check_equivalence`] with explicit [`Options`].
pub fn check_equivalence_with(
    original_wasm: &[u8],
    options: &Options<'_>,
) -> Result<EquivReport, EquivError> {
    let ir = soroban_ret::decompile_to_ir(original_wasm)
        .map_err(|e| EquivError::Decompile(format!("{e:?}")))?;
    let recompiled = recompile_to_wasm(&mark_holes(&ir.source))?;
    let reg = &ir.registry;

    let mut report = EquivReport::default();

    // Registration is contract-level. The original is registered once (with
    // constructor arguments if it needs them); every state descends from that.
    let callee = options.callee.unwrap_or(original_wasm);
    let registered = register_original(original_wasm, reg, callee);
    let mut preferred = Preferred::new();
    let states = match registered {
        Some((world, ctor_args, with_callee)) => {
            if let Some((_, ctor)) = reg
                .functions
                .iter()
                .find(|(n, _)| n.as_str() == "__constructor")
            {
                for (input, value) in ctor.inputs.iter().zip(&ctor_args) {
                    remember(&mut preferred, &input.type_, value);
                }
            }
            // The recompiled contract must register with the same arguments
            // in the same surroundings (its own constructor runs here, and
            // may call the callee; everything else starts from the
            // original's state).
            let callees = [Callee {
                id: CALLEE_CONTRACT_ID,
                wasm: callee,
            }];
            let callees: &[Callee<'_>] = if with_callee { &callees } else { &[] };
            if !ctor_args.is_empty() && World::new(&recompiled, &ctor_args, callees).is_none() {
                report.divergences.push(Divergence {
                    function: "__constructor".to_string(),
                    inputs: format!("{ctor_args:?}"),
                    original: "registered".to_string(),
                    recompiled: "registration failed".to_string(),
                });
            }
            // The recompiled contract must be installable in that world.
            if world.with_code(&recompiled).is_none() {
                Vec::new()
            } else {
                discover_states(world, reg, &mut preferred)
            }
        }
        None => Vec::new(),
    };
    report.states = states.iter().skip(1).map(|s| s.label.clone()).collect();

    for (name, spec_fn) in &reg.functions {
        if name.starts_with("__") {
            report.skip(name, SkipReason::NotDirectlyCallable);
            continue;
        }
        let inputs: Vec<ScSpecTypeDef> = spec_fn.inputs.iter().map(|i| i.type_.clone()).collect();
        let cases = match cases_for(reg, name, &inputs, &preferred) {
            Ok(cases) => cases,
            Err(unsupported) => {
                report.skip(name, SkipReason::UnsupportedParamTypes(unsupported));
                continue;
            }
        };
        if states.is_empty() {
            report.skip(name, SkipReason::NotRegistrable);
            continue;
        }

        report.executed_fns += 1;
        let mut returned_a_value = false;
        let mut returned_a_value_with_state = false;
        let mut reached_a_hole = false;

        for (state_no, state) in states.iter().enumerate() {
            let Some(recompiled_world) = state.world.with_code(&recompiled) else {
                continue;
            };
            for inputs in &cases {
                for auth in AuthMode::ALL {
                    // Both sides start from the same ledger, built by the
                    // original contract; each call runs in its own env.
                    let (out_orig, _) = state.world.call(name, inputs, auth);
                    let (out_recomp, _) = recompiled_world.call(name, inputs, auth);

                    report.executed_cases += 1;
                    if state_no > 0 {
                        report.stateful_cases += 1;
                    }
                    if out_recomp.is_hole() {
                        report.hole_cases += 1;
                        reached_a_hole = true;
                    } else if out_orig == out_recomp {
                        report.matched_cases += 1;
                        if matches!(out_orig, Outcome::Value(_)) {
                            report.value_cases += 1;
                            returned_a_value = true;
                            if state_no > 0 {
                                report.stateful_value_cases += 1;
                                returned_a_value_with_state = true;
                            }
                        }
                    } else {
                        let state_label = if state.label.is_empty() {
                            "as registered".to_string()
                        } else {
                            format!("after {}", state.label)
                        };
                        report.divergences.push(Divergence {
                            function: name.clone(),
                            inputs: format!("{inputs:?} [{}] [{state_label}]", auth.label()),
                            original: format!("{out_orig:?}"),
                            recompiled: format!("{out_recomp:?}"),
                        });
                    }
                }
            }
        }
        if returned_a_value {
            report.value_fns += 1;
        }
        if returned_a_value_with_state {
            report.stateful_value_fns += 1;
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

    fn fixture(name: &str) -> Vec<u8> {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures")
            .join(name);
        std::fs::read(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
    }

    fn labels(wasm: &[u8]) -> (Vec<String>, Preferred) {
        let reg = soroban_ret::TypeRegistry::from_wasm(wasm).expect("spec");
        let (world, _, _) = register_original(wasm, &reg, wasm).expect("registers");
        let mut preferred = Preferred::new();
        let states = discover_states(world, &reg, &mut preferred);
        (states.into_iter().map(|s| s.label).collect(), preferred)
    }

    /// A storing call builds a state, the search is deterministic, and what
    /// was stored is remembered for later arguments.
    #[test]
    fn a_storing_call_builds_a_state() {
        let wasm = fixture("test_contract_data.wasm");
        let (first, preferred) = labels(&wasm);
        assert_eq!(first[0], "", "the registered state comes first");
        assert!(first.len() > 1, "a state was built: {first:?}");
        assert!(first[1].starts_with("put("), "built by `put`: {}", first[1]);
        assert!(
            preferred.get("Symbol").is_some_and(|v| !v.is_empty()),
            "the stored key is remembered"
        );
        assert_eq!(labels(&wasm).0, first, "deterministic");
    }

    /// A contract that stores nothing has only the registered state.
    #[test]
    fn a_pure_contract_has_no_built_state() {
        let (states, _) = labels(&fixture("test_add_u64.wasm"));
        assert_eq!(states, vec![String::new()]);
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
