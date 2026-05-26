pub mod codegen;
pub mod dynamic_hints;
pub mod ir;
pub mod pattern;
pub mod pipeline;
pub mod spec;
pub mod wasm;

pub use dynamic_hints::{
    AuthHint, DecompileHints, EventHint, FunctionHints, HintValue, InvokeHint, StorageHint,
};
pub use spec::{registry::TypeRegistry, standard_interfaces::StandardInterface};
pub use wasm::{
    DataSection, DiagnosticCategory, DiagnosticSeverity, ExportTable, HostFunction, HostModule,
    ImportTable, SorobanDiagnostic, ValidationReport, WasmFunction, WasmInstr, WasmModule,
    WasmType,
};

use thiserror::Error;

/// Controls whether the decompiler assumes Soroban contract semantics or
/// treats the input as generic WASM.
///
/// Marked `#[non_exhaustive]` so additional modes (e.g. for non-Rust SDK
/// contracts) can be added without a breaking change. Match against this
/// enum with a wildcard arm: `_ => …`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub enum DecompileMode {
    /// Auto-detect from binary content (contractspecv0 section or Soroban host imports)
    #[default]
    Auto,
    /// Force Soroban contract decompilation
    Soroban,
    /// Force generic WASM decompilation (no Soroban assumptions)
    Generic,
}

/// Errors returned by the public decompilation API.
///
/// Marked `#[non_exhaustive]` because the decompiler may classify additional
/// failure modes in future releases (e.g. distinguishing "not a WASM file"
/// from "WASM with no `contractspecv0`"). Always include a wildcard arm
/// when matching.
#[derive(Error, Debug)]
#[non_exhaustive]
pub enum DecompileError {
    #[error("WASM parsing error: {0}")]
    WasmParse(String),
    #[error("spec extraction error: {0}")]
    SpecExtraction(#[from] crate::spec::registry::RegistryError),
    #[error("pattern matching error: {0}")]
    PatternMatch(String),
    #[error("code generation error: {0}")]
    CodeGen(String),
    #[error("formatting error: {0}")]
    Format(String),
    /// An internal invariant was violated (an `unwrap`/`unreachable!`/explicit
    /// `panic!` in pipeline code triggered while processing this input). The
    /// top-level entry points catch these so that embedders are not killed by
    /// a single bad contract; please report the input that produced this.
    #[error("internal decompiler panic: {0}")]
    InternalPanic(String),
}

/// Options controlling the public decompilation API.
///
/// Marked `#[non_exhaustive]` so new options can be added without a breaking
/// change. Construct via `DecompileOptions::default()` and update individual
/// fields, rather than via positional initialiser.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct DecompileOptions {
    /// Only output type definitions and function signatures (no bodies)
    pub spec_only: bool,
    /// Pre-optimize WASM with wasm-opt before decompilation.
    /// Requires `wasm-opt` binary installed (from binaryen).
    pub pre_optimize: bool,
    /// Decompilation mode: Auto (default), Soroban, or Generic.
    pub mode: DecompileMode,
    /// Optional runtime-free hints for conservative IR repairs.
    pub hints: Option<DecompileHints>,
}

/// Result of a decompilation call exposing the source and metadata.
///
/// Marked `#[non_exhaustive]` so future additions (e.g. confidence
/// annotations, diagnostic summary) don't require a breaking release.
/// Access fields directly (`result.source`); do not destructure.
#[derive(Debug)]
#[non_exhaustive]
pub struct DecompileResult {
    /// The decompiled Rust source code
    pub source: String,
    /// SDK version extracted from metadata, if available
    pub sdk_version: Option<String>,
    /// Standard interfaces detected
    pub standard_interfaces: Vec<String>,
    /// Soroban compliance validation report
    pub validation: ValidationReport,
}

/// Full intermediate results from the decompilation pipeline.
/// Exposes all stage outputs for testing and analysis.
///
/// Marked `#[non_exhaustive]` for the same reason as `DecompileResult`.
#[derive(Debug)]
#[non_exhaustive]
pub struct DecompileIR {
    /// Stage 3+4 output: lifted and optimized contract module
    pub contract_module: ir::ContractModule,
    /// Stage 2 output: type registry with full XDR spec
    pub registry: spec::TypeRegistry,
    /// Stage 1b output: Soroban compliance diagnostics (the Stage 1a is a WASM parsing)
    pub validation: ValidationReport,
    /// Stage 5 output: formatted Rust source
    pub source: String,
    /// SDK version from metadata
    pub sdk_version: Option<String>,
    /// Standard interfaces detected (SEP-41, etc.)
    pub standard_interfaces: Vec<String>,
}

/// Decompile a Soroban WASM binary to Rust source code.
pub fn decompile(wasm: &[u8]) -> Result<String, DecompileError> {
    let result = decompile_with_options(wasm, &DecompileOptions::default())?;
    Ok(result.source)
}

/// Decompile a Soroban WASM binary with options.
///
/// The entire pipeline runs inside a `catch_unwind` so that residual panics
/// from internal `unwrap`/`unreachable!` paths surface as
/// `DecompileError::InternalPanic` rather than killing the embedding process.
pub fn decompile_with_options(
    wasm: &[u8],
    options: &DecompileOptions,
) -> Result<DecompileResult, DecompileError> {
    catch_decompile_panic(|| pipeline::run(wasm, options))
}

/// Decompile and return full intermediate representations.
///
/// Unlike `decompile()` and `decompile_with_options()`, this function preserves
/// the `ContractModule` and `TypeRegistry` from intermediate pipeline stages,
/// enabling deep inspection for testing and analysis.
pub fn decompile_to_ir(wasm: &[u8]) -> Result<DecompileIR, DecompileError> {
    decompile_to_ir_with_options(wasm, &DecompileOptions::default())
}

/// Decompile with options and return full intermediate representations.
///
/// Like [`decompile_with_options`], runs inside `catch_unwind` so internal
/// panics surface as `DecompileError::InternalPanic`.
pub fn decompile_to_ir_with_options(
    wasm: &[u8],
    options: &DecompileOptions,
) -> Result<DecompileIR, DecompileError> {
    catch_decompile_panic(|| pipeline::run_to_ir(wasm, options))
}

/// Run the decompilation pipeline under `catch_unwind`.
///
/// Internal `unwrap`/`unreachable!`/`panic!` sites in optimizer and pipeline
/// passes assume invariants set by earlier passes; an unusual input that
/// violates those invariants would otherwise abort the process. We catch the
/// panic here, extract a best-effort message, and translate to
/// `DecompileError::InternalPanic`.
fn catch_decompile_panic<F, T>(f: F) -> Result<T, DecompileError>
where
    F: FnOnce() -> Result<T, DecompileError>,
{
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    match result {
        Ok(r) => r,
        Err(payload) => {
            let msg = if let Some(s) = payload.downcast_ref::<&'static str>() {
                (*s).to_string()
            } else if let Some(s) = payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "non-string panic payload".to_string()
            };
            Err(DecompileError::InternalPanic(msg))
        }
    }
}

/// Convert a WASM binary to WAT text format for debugging and analysis.
///
/// Requires the `wasmprinter` feature.
#[cfg(feature = "wasmprinter")]
pub fn wasm_to_wat(wasm: &[u8]) -> Result<String, DecompileError> {
    wasmprinter::print_bytes(wasm)
        .map_err(|e| DecompileError::WasmParse(format!("WAT conversion: {e}")))
}

#[cfg(test)]
mod catch_unwind_tests {
    use super::*;

    #[test]
    fn panics_in_pipeline_become_internal_panic_errors() {
        // Drive a panic inside the closure to confirm the wrapper translates
        // it into DecompileError::InternalPanic instead of aborting.
        let result: Result<DecompileResult, DecompileError> =
            catch_decompile_panic(|| panic!("simulated invariant violation"));
        match result {
            Err(DecompileError::InternalPanic(msg)) => {
                assert!(msg.contains("simulated invariant violation"), "got: {msg}");
            }
            other => panic!("expected InternalPanic, got {other:?}"),
        }
    }

    #[test]
    fn panics_with_owned_string_become_internal_panic_errors() {
        // panic!("{}", String) yields a String payload (vs &'static str).
        let result: Result<DecompileResult, DecompileError> =
            catch_decompile_panic(|| panic!("{}", String::from("dynamic message")));
        match result {
            Err(DecompileError::InternalPanic(msg)) => {
                assert!(msg.contains("dynamic message"), "got: {msg}");
            }
            other => panic!("expected InternalPanic, got {other:?}"),
        }
    }

    #[test]
    fn panics_with_non_string_payload_become_internal_panic_errors() {
        // panic_any with a non-string payload exercises the fallback arm.
        let result: Result<DecompileResult, DecompileError> =
            catch_decompile_panic(|| std::panic::panic_any(42_u32));
        match result {
            Err(DecompileError::InternalPanic(msg)) => {
                assert_eq!(msg, "non-string panic payload");
            }
            other => panic!("expected InternalPanic, got {other:?}"),
        }
    }

    #[test]
    fn ok_result_is_passed_through() {
        let result: Result<u32, DecompileError> = catch_decompile_panic(|| Ok(7));
        assert!(matches!(result, Ok(7)));
    }

    #[test]
    fn err_result_is_passed_through() {
        let result: Result<u32, DecompileError> =
            catch_decompile_panic(|| Err(DecompileError::WasmParse("boom".to_string())));
        match result {
            Err(DecompileError::WasmParse(msg)) => assert_eq!(msg, "boom"),
            other => panic!("expected WasmParse, got {other:?}"),
        }
    }
}
