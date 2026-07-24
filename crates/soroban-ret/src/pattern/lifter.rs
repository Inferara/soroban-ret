/// Function lifter.
///
/// Lifts WASM function bodies into Soroban-aware IR by:
/// 1. Resolving exports to spec entries
/// 2. Analyzing instruction sequences for host call patterns
/// 3. Producing SorobanStmt sequences for each contract function
///
/// For Phase 1-2: produces spec-only output (signatures without bodies).
/// Function body lifting will be enhanced in Phase 3.
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use stellar_xdr::ScSpecTypeDef;
use stellar_xdr::curr as stellar_xdr;

// Soroban Val tag constants (low byte of a 64-bit packed Val).
// See: https://github.com/stellar/rs-soroban-env/blob/main/soroban-env-common/src/val.rs
//
// Small-value tags (< 64) pack their payload directly in the upper bits; object
// tags (>= 64) carry a 32-bit handle in the major field that must be resolved
// through a host call. Names match the upstream `Tag` enum.
const TAG_FALSE: u64 = 0x00;
const TAG_TRUE: u64 = 0x01;
const TAG_VOID: u64 = 0x02;
const TAG_ERROR: u64 = 0x03;
const TAG_U32: u64 = 0x04;
const TAG_I32: u64 = 0x05;
const TAG_U64_SMALL: u64 = 0x06;
const TAG_I64_SMALL: u64 = 0x07;
const TAG_TIMEPOINT_SMALL: u64 = 0x08;
const TAG_DURATION_SMALL: u64 = 0x09;
const TAG_U128_SMALL: u64 = 0x0a;
const TAG_I128_SMALL: u64 = 0x0b;
const TAG_U256_SMALL: u64 = 0x0c;
const TAG_I256_SMALL: u64 = 0x0d;
const TAG_SYMBOL_SMALL: u64 = 0x0e;

// Object tags (low byte 0x40..=0x7f): the major field is a 32-bit object handle.
const TAG_U64_OBJECT: u64 = 64;
const TAG_I64_OBJECT: u64 = 65;
const TAG_TIMEPOINT_OBJECT: u64 = 66;
const TAG_DURATION_OBJECT: u64 = 67;
const TAG_U128_OBJECT: u64 = 68;
const TAG_I128_OBJECT: u64 = 69;
const TAG_U256_OBJECT: u64 = 70;
const TAG_I256_OBJECT: u64 = 71;
const TAG_BYTES_OBJECT: u64 = 72;
const TAG_STRING_OBJECT: u64 = 73;
const TAG_SYMBOL_OBJECT: u64 = 74;
const TAG_VEC_OBJECT: u64 = 75;
const TAG_MAP_OBJECT: u64 = 76;
const TAG_ADDRESS_OBJECT: u64 = 77;
const TAG_MUXED_ADDRESS_OBJECT: u64 = 78;

use crate::codegen::types as codegen_types;
use crate::ir::high_level_ir::{
    ContractFn, ContractModule, CryptoUsage, FnParam, TypeDef, TypeDefKind, WasmFnSignature,
};
use crate::ir::soroban_ir::{MatchArm, MatchPattern, SorobanExpr, SorobanStmt, StorageType};
use crate::spec::registry::TypeRegistry;
use crate::spec::standard_interfaces::detect_standard_interfaces;
use crate::wasm::imports::{HostFunction, HostModule};
use crate::wasm::{WasmModule, WasmType};

use super::dispatch::{resolve_exports, resolve_exports_generic};

/// A tracked i64.store operation for struct reconstruction.
#[derive(Debug, Clone)]
struct MemoryStore {
    offset: u32,
    value: StackVal,
}

/// Map a WASM value type to the closest ScSpecTypeDef placeholder.
/// Used for generic WASM decompilation where no spec is available.
fn wasm_type_to_spec(wt: &WasmType) -> ScSpecTypeDef {
    match wt {
        WasmType::I32 => ScSpecTypeDef::I32,
        WasmType::I64 => ScSpecTypeDef::I64,
        // Floats have no ScSpecTypeDef equivalent; use i32/i64 as placeholders.
        // Codegen uses wasm_signature when available.
        WasmType::F32 => ScSpecTypeDef::I32,
        WasmType::F64 => ScSpecTypeDef::I64,
    }
}

/// Combine a frame-slot base with a WASM memory offset, widening through i64
/// so that adversarially large `offset` values (WASM permits up to u32::MAX)
/// cannot panic in debug builds or silently wrap in release. Returns `None`
/// when the result does not fit in the i32 used as the slot-tracker key; the
/// frame-slot tracker is best-effort recovery so out-of-range slots are safely
/// ignored.
fn frame_slot_key(base: i32, offset: u32) -> Option<i32> {
    let combined = i64::from(base).checked_add(i64::from(offset))?;
    i32::try_from(combined).ok()
}

/// The WASM local index backing a symbolic loop-index value, if any. Loop
/// counters appear as a loop-carried phi, a promoted let-binding, or a raw
/// parameter.
fn sym_index_local(val: &StackVal) -> Option<u32> {
    match val {
        StackVal::LoopPhi(idx) | StackVal::LetBinding(idx) | StackVal::WasmParam(idx) => Some(*idx),
        _ => None,
    }
}

/// True when a match scrutinee carries no usable discriminant value — either genuinely
/// unknown, or a *folded discriminant constant* left by a UDT-enum (`union`) dispatch
/// that didn't go through `symbol_index_in_linear_memory` (e.g. `udt::add`'s 4-way
/// `match`, where the discriminant collapsed to a large Val literal like `134217736`).
/// In both cases the real scrutinee is the matched parameter, which the caller recovers
/// from its declared type. The `>= 64` bound excludes small result-selector indices
/// (`match <computed int>` br_tables switch on 0..N), so genuine integer matches are
/// left untouched.
fn is_recoverable_scrutinee(scrutinee: &SorobanExpr) -> bool {
    match scrutinee {
        SorobanExpr::UnknownVal => true,
        // `udt::add`'s discriminant folds to a seeded `I64(0)` that decodes to
        // `BoolLiteral(false)`; a genuine bool match is an `if`, never a multi-way
        // br_table, so a br_table on a bool is always a collapsed discriminant.
        SorobanExpr::BoolLiteral(_) => true,
        SorobanExpr::I64Literal(v) => *v >= 64,
        _ => false,
    }
}

/// A small positive constant stride/shift amount (i32 or i64), restricted to a
/// sane range so an adversarial module cannot synthesize pathological terms.
fn as_small_stride(val: &StackVal) -> Option<u32> {
    let v = match val {
        StackVal::I32(v) => i64::from(*v),
        StackVal::I64(v) => *v,
        _ => return None,
    };
    (1..=0xFFFF).contains(&v).then_some(v as u32)
}

/// Recognize a `StackVal` as an affine loop-index term `coeff * index_local`:
/// the bare index (coeff 1), `index * const` / `const * index`, or
/// `index << shift` (coeff = `1 << shift`). Returns `None` for anything else,
/// so `FrameSlot + <unrecognized>` falls through to ordinary `BinOp` handling.
fn affine_index_term(val: &StackVal) -> Option<SymTerm> {
    if let Some(index_local) = sym_index_local(val) {
        return Some(SymTerm {
            index_local,
            coeff: 1,
        });
    }
    let StackVal::BinOp(a, op, b) = val else {
        return None;
    };
    match op {
        BinOper::Mul => sym_index_local(a)
            .zip(as_small_stride(b))
            .or_else(|| sym_index_local(b).zip(as_small_stride(a)))
            .map(|(index_local, coeff)| SymTerm { index_local, coeff }),
        BinOper::Shl => {
            let index_local = sym_index_local(a)?;
            let shift = as_small_stride(b)?;
            (shift < 31).then(|| SymTerm {
                index_local,
                coeff: 1u32 << shift,
            })
        }
        _ => None,
    }
}

/// Maximum recursion depth for inlining callee bodies into the caller's stmts.
/// Bounds stack usage and prevents pathological mutual-recursion lifting.
/// Single source of truth — both `lift_instruction` (entry) and
/// `lift_inline_call` (recursive callee) check against this.
const MAX_INLINE_CALL_DEPTH: u32 = 5;

/// Lift all contract functions from WASM module into a ContractModule.
pub fn lift_functions(
    wasm_module: &WasmModule,
    registry: &TypeRegistry,
    spec_only: bool,
    is_soroban: bool,
) -> ContractModule {
    let mut contract = ContractModule::new("Contract".to_string());
    contract.is_soroban = is_soroban;

    if is_soroban {
        // Generate type definitions from spec
        generate_types(registry, &mut contract);

        // Detect standard interfaces
        let interfaces = detect_standard_interfaces(registry);
        contract.standard_interfaces = interfaces.iter().map(|i| format!("{:?}", i)).collect();
    }

    // Resolve exports
    let resolved = if is_soroban {
        resolve_exports(wasm_module, registry)
    } else {
        resolve_exports_generic(wasm_module)
    };

    // Build contract functions
    for resolved_fn in &resolved {
        let func_name = &resolved_fn.export_name;

        if !is_soroban {
            // Generic WASM path: build function from WASM type signature
            let func = wasm_module
                .functions
                .iter()
                .find(|f| f.index == resolved_fn.func_index);
            let func_type = func.and_then(|f| wasm_module.types.get(f.type_index as usize));

            let (params, return_type, wasm_sig) = if let Some(ft) = func_type {
                let params: Vec<FnParam> = ft
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, wt)| FnParam {
                        name: format!("arg{}", i),
                        type_def: wasm_type_to_spec(wt),
                    })
                    .collect();
                let return_type = ft.results.first().map(wasm_type_to_spec);
                let wasm_sig = WasmFnSignature {
                    params: ft.params.clone(),
                    results: ft.results.clone(),
                };
                (params, return_type, Some(wasm_sig))
            } else {
                (Vec::new(), None, None)
            };

            let lift_result = if spec_only {
                LiftBodyResult {
                    stmts: Vec::new(),
                    found_host_calls: false,
                }
            } else {
                lift_function_body(
                    wasm_module,
                    registry,
                    resolved_fn.func_index,
                    &params,
                    &return_type,
                )
            };

            contract.functions.push(ContractFn {
                name: func_name.clone(),
                params,
                return_type,
                body: lift_result.stmts,
                takes_env: false,
                is_constructor: false,
                is_check_auth: false,
                wrapper_panics: false,
                had_host_calls: lift_result.found_host_calls,
                wasm_param_base: 0,
                wasm_signature: wasm_sig,
            });
            continue;
        }

        if let Some(spec_fn) = registry.get_function(func_name) {
            let params: Vec<FnParam> = spec_fn
                .inputs
                .iter()
                .filter_map(|input| {
                    let name = input.name.to_utf8_string().ok()?;
                    Some(FnParam {
                        name,
                        type_def: input.type_.clone(),
                    })
                })
                .collect();

            let return_type = spec_fn.outputs.to_option();
            let wasm_param_count = wasm_module
                .get_func_type(resolved_fn.func_index)
                .map(|ft| ft.params.len())
                .unwrap_or(0);
            let wasm_param_base = wasm_param_count.saturating_sub(params.len()) as u32;

            // Assume all Soroban contract functions take Env. The SDK injects it
            // implicitly; with LTO the param may be eliminated from the WASM
            // signature but the function still uses env via host imports.
            // Stage 4g (stmts_use_env) removes env when the body doesn't reference it.
            let takes_env = true;

            let lift_result = if spec_only {
                LiftBodyResult {
                    stmts: Vec::new(),
                    found_host_calls: false,
                }
            } else {
                lift_function_body(
                    wasm_module,
                    registry,
                    resolved_fn.func_index,
                    &params,
                    &return_type,
                )
            };

            // Debug affordance: map exported function names to their WASM func
            // index, so `DBG_INLINE_STRUCT=<idx>` / `DBG_STRUCT=<idx>` can target a
            // specific function (those hooks key on the numeric index, not name).
            if std::env::var("DBG_NAMEIDX").is_ok() {
                eprintln!("[DBG_NAMEIDX] {} = {}", func_name, resolved_fn.func_index);
            }
            // Check if the wrapper function calls a bare `unreachable` trap function,
            // indicating the original source ends with `panic!()`.
            let wrapper_panics = wrapper_has_panic_call(wasm_module, resolved_fn.func_index);

            contract.functions.push(ContractFn {
                name: func_name.clone(),
                params,
                return_type,
                body: lift_result.stmts,
                takes_env,
                is_constructor: resolved_fn.is_constructor,
                is_check_auth: resolved_fn.is_check_auth,
                wrapper_panics,
                had_host_calls: lift_result.found_host_calls,
                wasm_param_base,
                wasm_signature: None,
            });
        }
    }

    contract.has_constructor = resolved.iter().any(|r| r.is_constructor);

    // Detect crypto module usage and re-generate struct tokens with type aliases
    contract.crypto_usage = detect_crypto_usage(&contract);
    if contract.crypto_usage.has_any() {
        regenerate_crypto_struct_tokens(registry, &mut contract);
    }

    contract
}

/// Generate type definitions from the type registry.
fn generate_types(registry: &TypeRegistry, contract: &mut ContractModule) {
    // Structs
    for spec in registry.structs.values() {
        let name = spec.name.to_utf8_string().unwrap_or_default();
        let is_tuple = spec.fields.iter().all(|f| {
            f.name
                .to_utf8_string()
                .map(|n| n.parse::<usize>().is_ok())
                .unwrap_or(false)
        });
        let tokens = codegen_types::generate_struct(spec);
        contract.types.push(TypeDef {
            kind: if is_tuple {
                TypeDefKind::TupleStruct
            } else {
                TypeDefKind::Struct
            },
            name,
            generated_tokens: Some(tokens),
        });
    }

    // Unions (complex enums)
    for spec in registry.unions.values() {
        let name = spec.name.to_utf8_string().unwrap_or_default();
        let tokens = codegen_types::generate_union(spec);
        contract.types.push(TypeDef {
            kind: TypeDefKind::Union,
            name,
            generated_tokens: Some(tokens),
        });
    }

    // Integer enums
    for spec in registry.enums.values() {
        let name = spec.name.to_utf8_string().unwrap_or_default();
        let tokens = codegen_types::generate_enum(spec);
        contract.types.push(TypeDef {
            kind: TypeDefKind::Enum,
            name,
            generated_tokens: Some(tokens),
        });
    }

    // Error enums
    for spec in registry.error_enums.values() {
        let name = spec.name.to_utf8_string().unwrap_or_default();
        let tokens = codegen_types::generate_error_enum(spec);
        contract.error_enums.push(TypeDef {
            kind: TypeDefKind::ErrorEnum,
            name,
            generated_tokens: Some(tokens),
        });
    }

    // Events
    for spec in registry.events.values() {
        let name = spec.name.to_utf8_string().unwrap_or_default();
        let tokens = codegen_types::generate_event(spec);
        contract.events.push(TypeDef {
            kind: TypeDefKind::Event,
            name,
            generated_tokens: Some(tokens),
        });
    }

    // Sort all type vecs by name for deterministic output
    contract.types.sort_by(|a, b| a.name.cmp(&b.name));
    contract.error_enums.sort_by(|a, b| a.name.cmp(&b.name));
    contract.events.sort_by(|a, b| a.name.cmp(&b.name));
}

/// Detect crypto submodule usage by scanning all function bodies.
fn detect_crypto_usage(contract: &ContractModule) -> CryptoUsage {
    let mut usage = CryptoUsage::default();
    for func in &contract.functions {
        for stmt in &func.body {
            scan_stmt_for_crypto(stmt, &mut usage);
        }
    }
    usage
}

fn scan_stmt_for_crypto(stmt: &SorobanStmt, usage: &mut CryptoUsage) {
    match stmt {
        SorobanStmt::Expr(e)
        | SorobanStmt::Return(Some(e))
        | SorobanStmt::Let { value: e, .. }
        | SorobanStmt::Assign { value: e, .. } => {
            scan_expr_for_crypto(e, usage);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            scan_expr_for_crypto(condition, usage);
            for s in then_body {
                scan_stmt_for_crypto(s, usage);
            }
            for s in else_body {
                scan_stmt_for_crypto(s, usage);
            }
        }
        SorobanStmt::Match { scrutinee, arms } => {
            scan_expr_for_crypto(scrutinee, usage);
            for arm in arms {
                for s in &arm.body {
                    scan_stmt_for_crypto(s, usage);
                }
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            for s in body {
                scan_stmt_for_crypto(s, usage);
            }
        }
        _ => {}
    }
}

fn scan_expr_for_crypto(expr: &SorobanExpr, usage: &mut CryptoUsage) {
    match expr {
        SorobanExpr::MethodCall {
            object,
            method: _,
            args,
        } => {
            // Detect .crypto().bn254().* or .crypto().bls12_381().*
            if let SorobanExpr::MethodCall {
                object: inner,
                method: submod,
                ..
            } = object.as_ref()
                && let SorobanExpr::MethodCall {
                    method: crypto_method,
                    ..
                } = inner.as_ref()
                && crypto_method == "crypto"
            {
                if submod == "bn254" {
                    usage.uses_bn254 = true;
                }
                if submod == "bls12_381" {
                    usage.uses_bls12_381 = true;
                }
            }
            scan_expr_for_crypto(object, usage);
            for a in args {
                scan_expr_for_crypto(a, usage);
            }
        }
        // Recurse into sub-expressions
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Rem(a, b)
        | SorobanExpr::Eq(a, b)
        | SorobanExpr::Ne(a, b)
        | SorobanExpr::Lt(a, b)
        | SorobanExpr::Le(a, b)
        | SorobanExpr::Gt(a, b)
        | SorobanExpr::Ge(a, b)
        | SorobanExpr::And(a, b)
        | SorobanExpr::Or(a, b) => {
            scan_expr_for_crypto(a, usage);
            scan_expr_for_crypto(b, usage);
        }
        SorobanExpr::Not(a) => scan_expr_for_crypto(a, usage),
        SorobanExpr::FieldAccess { object, .. } => scan_expr_for_crypto(object, usage),
        _ => {}
    }
}

/// Re-generate struct tokens with crypto type aliases when crypto is detected.
fn regenerate_crypto_struct_tokens(registry: &TypeRegistry, contract: &mut ContractModule) {
    for type_def in &mut contract.types {
        if !matches!(type_def.kind, TypeDefKind::Struct) {
            continue;
        }
        // Find matching spec by name
        if let Some(spec) = registry
            .structs
            .values()
            .find(|s| s.name.to_utf8_string().unwrap_or_default() == type_def.name)
        {
            // Check if this struct has any crypto-aliasable fields
            let has_crypto_fields = spec.fields.iter().any(|f| {
                matches!(&f.type_, ScSpecTypeDef::BytesN(_) | ScSpecTypeDef::U256)
                    || matches!(&f.type_, ScSpecTypeDef::Vec(v) if matches!(
                        &*v.element_type,
                        ScSpecTypeDef::BytesN(_) | ScSpecTypeDef::U256
                    ))
            });
            if has_crypto_fields {
                type_def.generated_tokens = Some(codegen_types::generate_struct_with_crypto(
                    spec,
                    &contract.crypto_usage,
                ));
            }
        }
    }
}

/// State for lifting a single WASM function body into Soroban IR.
/// A fallible storage-get helper call observed in the top-level function body:
/// its missing-key path returns the contract error `error_code`. Recorded at the
/// inline call site (clean key from the lifted args) and consumed by
/// `lift_function_body` to rebuild `env.storage().<dur>().get(&key).ok_or(Error::V)`
/// instead of the lossy `has`/`extend_ttl` + `todo!()` husk. See
/// [`detect_fallible_storage_get_helper`].
struct FallibleGetRecord {
    key: SorobanExpr,
    storage_type: StorageType,
    error_code: u32,
    err_type: ScSpecTypeDef,
}

/// Debug-flag caches, read once per process: `std::env::var` takes a
/// process-global lock, and these guards sit on the per-frame-slot-load and
/// per-`IfElse` hot paths (greptile P2).
static DBG_SLOTMISS: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| std::env::var("DBG_SLOTMISS").is_ok());
static DBG_JOIN: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| std::env::var("DBG_JOIN").is_ok());
static DBG_SLOTJOIN: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| std::env::var("DBG_SLOTJOIN").is_ok());
static DBG_SLOTREAD: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| std::env::var("DBG_SLOTREAD").is_ok());
/// Issue #38 census probe: report loop-body generic slot reads that a LATER
/// store in the same body overwrites — the back-edge use-before-def class
/// (iteration 2+ observes iteration 1's value; the linear sim shows the
/// pre-loop value). Measurement-only; no behavior change.
static DBG_LOOPRBW: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| std::env::var("DBG_LOOPRBW").is_ok());
static DBG_FDK: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| std::env::var("DBG_FDK").is_ok());
static DBG_DKTRACE: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| std::env::var("DBG_DKTRACE").is_ok());

/// Issue #34 phase 2: classification of a frame slot whose abstract value was
/// produced by the then arm of a shared-map `IfElse` join, from the
/// perspective of code that reads it afterwards. PR #48 proved the write-side
/// conflict class is empty (divergent = 0) and left "then-survives" as a
/// 42,587-case *upper bound* because value snapshots cannot see reads. This
/// taint tracks the actual reads: the generic load path degrades a read that
/// observes a tainted value to `Unknown` (the sound-join read poison), and
/// `DBG_SLOTREAD` reports each poisoned read's class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SlotTaintKind {
    /// Set between the arms: the then arm wrote this slot, the else arm is
    /// about to be lifted against the same map. An else-arm read observing
    /// this value is a phantom cross-arm read (at runtime the else path never
    /// sees then-path writes).
    CrossArm,
    /// Set at the join when neither arm terminated and the else arm never
    /// overwrote the slot: downstream code reading it observes the then value
    /// unconditionally, but at runtime the slot holds the pre-if value on
    /// else executions.
    Conditional,
    /// Set at the join when the THEN arm terminated (returned/trapped): all
    /// fall-through code runs on the else path, so a downstream read of a
    /// surviving then-write observes a value from a path that provably did
    /// not fall through.
    DeadThen,
    /// Set after a loop body lifts against the shared slot map: the map holds
    /// ONE-ITERATION values for every slot the body wrote — wrong for a loop
    /// that runs zero times (the slot holds its pre-loop value at runtime)
    /// and for 2+ iterations (later iterations overwrite). A post-loop read
    /// observing the exact one-iteration value is unsound; proven-exact loop
    /// models (the memory-copy extension) are excluded at the stamp site.
    /// (Issue #38 substrate: in-body back-edge reads — iteration 2+ observing
    /// iteration 1 state — are the remaining unmeasured half.)
    LoopVariant,
}

/// A tainted slot: the classification plus the exact value the then arm
/// wrote. Reads are poisoned only when the observed value still EQUALS the
/// tainted value — a recognizer seed or any other writer that has since
/// replaced the value makes the read self-consistent, not a join leak.
#[derive(Clone, Debug)]
struct SlotTaint {
    kind: SlotTaintKind,
    val: StackVal,
}

struct LiftContext<'a> {
    wasm_module: &'a WasmModule,
    registry: &'a TypeRegistry,
    params: &'a [FnParam],
    return_type: &'a Option<ScSpecTypeDef>,
    stack: Vec<StackVal>,
    locals: Vec<StackVal>,
    stmts: Vec<SorobanStmt>,
    found_host_calls: bool,
    memory_stores: Vec<MemoryStore>,
    /// Number of WASM-level parameters (env + contract params). Used to distinguish
    /// body-local slots (idx >= num_wasm_params) from parameter slots.
    num_wasm_params: u32,
    /// Recursion depth for function inlining. Zero at the top-level call site;
    /// incremented each time we inline into a callee. Capped at 2 to avoid
    /// unbounded expansion.
    inline_depth: u32,
    /// Maps (frame_id, byte_offset) to stored StackVal.
    /// Shared across all child contexts and inline callees via Rc<RefCell>.
    frame_slots: Rc<RefCell<HashMap<(u32, i32), StackVal>>>,
    /// Monotonically increasing counter for allocating unique frame IDs.
    next_frame_id: Rc<RefCell<u32>>,
    /// Variant names from the most recent `symbol_index_in_linear_memory` call.
    /// Used by `try_recognize_match()` to map numeric br_table arms to enum variants.
    enum_cases: Option<Vec<String>>,
    /// The scrutinee expression for enum match recovery (the parameter being matched on).
    enum_match_scrutinee: Option<SorobanExpr>,
    /// Counter for cycling through parameters of the same enum/union type
    /// when recovering match scrutinees. Keyed by type name.
    /// Shared across all child contexts via Rc<RefCell>.
    enum_match_counter: Rc<RefCell<HashMap<String, usize>>>,
    /// Locals protected by phi-merge: post-match merge code should not overwrite
    /// these locals because the phi-merge already captured per-arm values.
    /// Set by `try_recognize_match` after phi-merge fires, cleared by `lift_structured`.
    phi_protected_locals: Vec<u32>,
    /// Locals recovered as loop-carried by the loop dataflow analysis. While
    /// lifting a loop body, `LocalSet`/`LocalTee` to one of these emits an
    /// `Assign { target: var_idx, value }` statement (the loop mutates a real
    /// `let mut` variable) instead of the usual silent abstract update.
    /// Populated only for the duration of a recognized loop body.
    loop_carried_locals: Vec<u32>,
    /// Frame slots promoted to a synthetic scalar variable by loop-carried
    /// recovery: maps a `(frame_id, offset)` slot key to the synthetic local
    /// index naming its `let mut var_{idx}`. A load from a promoted slot reads
    /// the variable; a store emits `var_{idx} = <value>`. Lets an accumulator
    /// spilled to the shadow stack (the aquarius case) survive the loop instead
    /// of degrading to a self-referential `UnknownVal`. The index is allocated by
    /// extending `locals`, so it never collides with a real WASM local.
    promoted_slots: HashMap<(u32, i32), u32>,
    /// Frame writes through a *dynamic* (loop-indexed) offset `base + coeff*i`,
    /// which a single static `(frame_id, offset)` key cannot represent. Keyed by
    /// `(frame_id, term, static_base)` so a later load with the *same* symbolic
    /// term and base reads the value back (indexed read-after-write within a
    /// loop body). Shared via `Rc<RefCell>` like `frame_slots`. A load whose term
    /// finds no entry degrades to `Unknown`, exactly as before.
    dynamic_slots: Rc<RefCell<DynamicSlotMap>>,
    /// Depth of guard-error-path blocks we're nested inside. When > 0, the flat
    /// BrIf(0) handler can safely treat constant-true conditions as pass-through
    /// (instead of no-ops) because the enclosing block has an error path.
    guard_block_depth: u32,
    /// First fallible storage-get helper observed in the top-level function (only
    /// recorded at `inline_depth == 0`). Shared across same-function child
    /// contexts via `Rc<RefCell>` so a record made while lifting a nested block
    /// reaches `lift_function_body`. See [`FallibleGetRecord`].
    fallible_get_recovery: Rc<RefCell<Option<FallibleGetRecord>>>,
    /// Count of fallible storage-get helpers the top-level function calls (also
    /// only at `inline_depth == 0`, shared like `fallible_get_recovery`). When
    /// `> 1` the getter reads more than one key, so it cannot be rebuilt as a
    /// single value-returning `get(..).ok_or(..)` tail (that would return the
    /// FIRST key's value/error and silently drop the rest); `lift_function_body`
    /// downgrades it to the always-faithful early-return guard form instead.
    fallible_get_count: Rc<RefCell<u32>>,
    /// Journal of every REAL store to a static frame slot (issue #34 slice):
    /// unlike `frame_slots` (the current abstract state, which invalidation and
    /// overwrites erase), this only ever appends. A load whose slot the state
    /// map lost consults it: exactly ONE recorded def that is provably pure and
    /// loop-invariant → the load reads that def (a unique reaching definition);
    /// anything else → `Unknown`, exactly as before. Shared via `Rc` like
    /// `frame_slots`; throwaway simulation contexts swap in a fresh copy so
    /// speculative lifts cannot pollute it.
    slot_defs: Rc<RefCell<SlotDefJournal>>,
    /// Depth of structured-loop bodies currently being lifted. The journal fill
    /// never fires at `loop_depth > 0`: a load inside a loop body may observe a
    /// later iteration's store, which single-pass journaling cannot see.
    loop_depth: u32,
    /// Ordered log of every generic static-slot store (issue #34 phase 2):
    /// `(key, previous_value, new_value)` in simulation order. Unlike
    /// `slot_defs` (per-key, unordered across keys) this preserves the
    /// interleaving needed to segment writes by `IfElse` arm, and the recorded
    /// previous value gives each arm's writes their pre-if baseline without
    /// snapshotting the whole map. Drives the sound-join slot poison (live)
    /// and the `DBG_SLOTREAD` taint measurement. Recognizer seeds that insert
    /// into `frame_slots` directly are deliberately NOT logged — the poison's
    /// current-value equality check leaves them untouched. Shared via `Rc`
    /// like `slot_defs`; throwaway simulation contexts swap in a detached
    /// copy.
    slot_write_log: Rc<RefCell<SlotWriteLog>>,
    /// Slots currently holding a value the abstract state took from a then
    /// arm (see [`SlotTaintKind`]). A generic load that observes a tainted
    /// slot's exact value degrades it to `Unknown` (and reports the class
    /// under `DBG_SLOTREAD`); any store clears the taint. Shared/detached
    /// like `slot_write_log`.
    slot_taints: Rc<RefCell<HashMap<(u32, i32), SlotTaint>>>,
    /// Issue #38 census probe (`DBG_LOOPRBW` only): generic slot reads as
    /// `(key, write-log length at read time)`, so a loop site can report
    /// body reads that a LATER body store overwrites (the back-edge
    /// use-before-def class — iteration 2+ observes iteration 1's value,
    /// the linear sim shows the pre-loop value). Empty unless the flag is
    /// set; measurement-only, never changes lifting behavior.
    slot_read_log: Rc<RefCell<SlotReadLog>>,
}

/// `(slot key, write-log length at read time)` — see `slot_read_log`.
type SlotReadLog = Vec<((u32, i32), usize)>;

impl<'a> LiftContext<'a> {
    fn new(
        wasm_module: &'a WasmModule,
        registry: &'a TypeRegistry,
        params: &'a [FnParam],
        return_type: &'a Option<ScSpecTypeDef>,
        locals: Vec<StackVal>,
        num_wasm_params: u32,
    ) -> Self {
        Self {
            wasm_module,
            registry,
            params,
            return_type,
            stack: Vec::new(),
            locals,
            stmts: Vec::new(),
            found_host_calls: false,
            memory_stores: Vec::new(),
            num_wasm_params,
            inline_depth: 0,
            frame_slots: Rc::new(RefCell::new(HashMap::new())),
            next_frame_id: Rc::new(RefCell::new(0)),
            enum_cases: None,
            enum_match_scrutinee: None,
            enum_match_counter: Rc::new(RefCell::new(HashMap::new())),
            phi_protected_locals: Vec::new(),
            loop_carried_locals: Vec::new(),
            promoted_slots: HashMap::new(),
            dynamic_slots: Rc::new(RefCell::new(HashMap::new())),
            guard_block_depth: 0,
            fallible_get_recovery: Rc::new(RefCell::new(None)),
            fallible_get_count: Rc::new(RefCell::new(0)),
            slot_defs: Rc::new(RefCell::new(HashMap::new())),
            loop_depth: 0,
            slot_write_log: Rc::new(RefCell::new(Vec::new())),
            slot_taints: Rc::new(RefCell::new(HashMap::new())),
            slot_read_log: Rc::new(RefCell::new(Vec::new())),
        }
    }

    /// Create a child context that shares state but collects stmts separately.
    fn child_context(&self) -> LiftContext<'a> {
        LiftContext {
            wasm_module: self.wasm_module,
            registry: self.registry,
            params: self.params,
            return_type: self.return_type,
            stack: self.stack.clone(),
            locals: self.locals.clone(),
            stmts: Vec::new(),
            found_host_calls: false,
            memory_stores: self.memory_stores.clone(),
            num_wasm_params: self.num_wasm_params,
            inline_depth: self.inline_depth,
            frame_slots: Rc::clone(&self.frame_slots),
            next_frame_id: Rc::clone(&self.next_frame_id),
            enum_cases: self.enum_cases.clone(),
            enum_match_scrutinee: self.enum_match_scrutinee.clone(),
            enum_match_counter: Rc::clone(&self.enum_match_counter),
            phi_protected_locals: Vec::new(),
            loop_carried_locals: self.loop_carried_locals.clone(),
            promoted_slots: self.promoted_slots.clone(),
            dynamic_slots: Rc::clone(&self.dynamic_slots),
            guard_block_depth: self.guard_block_depth,
            // Shared so a record made in a nested block reaches the top-level ctx.
            fallible_get_recovery: Rc::clone(&self.fallible_get_recovery),
            fallible_get_count: Rc::clone(&self.fallible_get_count),
            slot_defs: Rc::clone(&self.slot_defs),
            loop_depth: self.loop_depth,
            slot_write_log: Rc::clone(&self.slot_write_log),
            slot_taints: Rc::clone(&self.slot_taints),
            slot_read_log: Rc::clone(&self.slot_read_log),
        }
    }

    /// Emit `var_{idx} = <value>` for a loop-carried local and rebind the local
    /// to `var_{idx}` so later reads (in the body and after the loop) reference
    /// the mutable variable the Loop arm declared before the loop. If `value` is
    /// a host call that was speculatively emitted as a trailing `Expr(call)`,
    /// rewrite that statement in place rather than duplicating the call.
    fn emit_loop_carried_assign(&mut self, idx: u32, val: &StackVal) {
        let value = {
            let slots = self.frame_slots.borrow();
            stack_val_to_expr(val, self.params, self.registry, Some(&slots))
        };
        let assign = SorobanStmt::Assign {
            target: format!("var_{}", idx),
            value: value.clone(),
        };
        // Only rewrite the trailing `Expr` in place when it is exactly the call
        // that produced this value (same guard as the implicit-return path);
        // otherwise an unrelated speculative side-effecting call would be dropped.
        if matches!(val, StackVal::HostCallResult(_))
            && matches!(self.stmts.last(), Some(SorobanStmt::Expr(e)) if *e == value)
        {
            *self.stmts.last_mut().unwrap() = assign;
        } else {
            self.stmts.push(assign);
        }
        if let Some(local) = self.locals.get_mut(idx as usize) {
            *local = StackVal::LetBinding(idx);
        }
    }

    /// Record a store of `value` to frame slot `(id, slot)`. If the slot has been
    /// promoted to a loop-carried scalar, emit `var_{idx} = <value>` (the loop
    /// mutates the synthetic `let mut` declared before it) and keep the slot
    /// bound to that variable so later loads read it; otherwise update the
    /// abstract frame-slot map as usual.
    fn store_frame_slot(&mut self, id: u32, slot: i32, value: StackVal, width: u32) {
        if !self.promoted_slots.contains_key(&(id, slot)) {
            // Ordered write log for the IfElse join poison and the
            // frame-descriptor key fold: record what the slot held before
            // this store (join no-op detection) and the real store width
            // (descriptor seeding). Promoted (loop-carried) slots are
            // excluded: their store renders a real `var_N = ..` assignment,
            // so the abstract binding is sound on every path.
            let prev = self.frame_slots.borrow().get(&(id, slot)).cloned();
            self.slot_write_log.borrow_mut().push(SlotWrite {
                key: (id, slot),
                prev,
                new: value.clone(),
                width,
                depth: self.inline_depth,
            });
            // After this store the slot holds a value this path produced
            // itself, so any join taint is lifted.
            self.slot_taints.borrow_mut().remove(&(id, slot));
        }
        self.slot_defs
            .borrow_mut()
            .entry((id, slot))
            .or_default()
            .push(value.clone());
        if let Some(&var_idx) = self.promoted_slots.get(&(id, slot)) {
            let expr = {
                let slots = self.frame_slots.borrow();
                stack_val_to_expr(&value, self.params, self.registry, Some(&slots))
            };
            self.stmts.push(SorobanStmt::Assign {
                target: format!("var_{}", var_idx),
                value: expr,
            });
            self.frame_slots
                .borrow_mut()
                .insert((id, slot), StackVal::LetBinding(var_idx));
        } else {
            self.frame_slots.borrow_mut().insert((id, slot), value);
        }
    }

    /// Issue #38 substrate — loop-variant slot taints. After a loop body
    /// lifts against the shared slot map, every slot the body wrote (at this
    /// inline depth) holds a ONE-ITERATION value: wrong when the loop runs
    /// zero times (at runtime the slot keeps its pre-loop value) and when it
    /// runs 2+ times (later iterations overwrite). Stamp the survivors so a
    /// generic post-loop load observing the exact one-iteration value
    /// degrades to `Unknown` — the same read-time discipline as the t9 join
    /// poison: the map itself is NEVER poisoned, a later writer clears the
    /// taint in `store_frame_slot`, and the value-equality check at the load
    /// shields recognizer-adopted values. Net no-op rewrites (final value ==
    /// pre-loop value, e.g. save/restore) are dropped as sound.
    fn taint_loop_variant_slots(&self, pre_wpos: usize) {
        // Census probe: report body reads that a LATER body store overwrites
        // (back-edge use-before-def — the sim gave iteration-1 code the
        // pre-loop value, but iteration 2+ observes iteration 1's write).
        if *DBG_LOOPRBW {
            let reads = self.slot_read_log.borrow();
            let log = self.slot_write_log.borrow();
            for (rk, wpos) in reads.iter() {
                // Only reads issued during THIS body (write-log position at
                // read time within the body segment), overwritten afterwards.
                if *wpos >= pre_wpos
                    && log[*wpos..]
                        .iter()
                        .any(|w| w.key == *rk && w.depth == self.inline_depth)
                {
                    eprintln!(
                        "[LOOPRBW] frame=({},{}) loop={} inline={}",
                        rk.0, rk.1, self.loop_depth, self.inline_depth
                    );
                }
            }
        }
        let per_key: Vec<((u32, i32), Option<StackVal>, StackVal)> = {
            let log = self.slot_write_log.borrow();
            let mut per_key: Vec<((u32, i32), Option<StackVal>, StackVal)> = Vec::new();
            for w in &log[pre_wpos..] {
                // Same-depth entries only (t10 lesson): an inlined helper's
                // internal stores are its own scratch, not this loop's state.
                if w.depth != self.inline_depth {
                    continue;
                }
                match per_key.iter_mut().find(|(pk, _, _)| *pk == w.key) {
                    Some((_, _, last)) => *last = w.new.clone(),
                    None => per_key.push((w.key, w.prev.clone(), w.new.clone())),
                }
            }
            per_key
        };
        if per_key.is_empty() {
            return;
        }
        let mut taints = self.slot_taints.borrow_mut();
        for (k, first_prev, last_new) in per_key {
            if first_prev.as_ref() == Some(&last_new) {
                continue;
            }
            taints.insert(
                k,
                SlotTaint {
                    kind: SlotTaintKind::LoopVariant,
                    val: last_new,
                },
            );
        }
    }

    /// Lower a classified i128/u128 soft-arith helper call to a clean `Mul`/`Div`.
    /// Reconstructs the two 128-bit operands from their limb-pair args; if either
    /// is degraded (limb-soup) returns `None` so the caller falls back to inlining.
    /// On success, writes the result — as a `(lo, hi)` limb pair — to every frame
    /// slot the helper points at, so a later load (whole value or re-decomposed
    /// limbs) recovers it and chained helpers compose.
    fn try_lower_i128_intrinsic(
        &mut self,
        intr: &I128Intrinsic,
        args: &[StackVal],
    ) -> Option<bool> {
        let (a, a_clean) = reconstruct_i128_operand(args.get(intr.a_lo)?, args.get(intr.a_hi)?)?;
        let (b, b_clean) = reconstruct_i128_operand(args.get(intr.b_lo)?, args.get(intr.b_hi)?)?;
        // Require at least one genuinely limb-tracked operand: this confirms we are
        // in real i128 dataflow (share-math), not a multiply whose operands are
        // both constants/handles we'd otherwise fabricate from Val encodings.
        if !(a_clean || b_clean) {
            return None;
        }
        let (a_expr, b_expr) = {
            let slots = self.frame_slots.borrow();
            (
                force_i128_type(stack_val_to_expr(
                    &a,
                    self.params,
                    self.registry,
                    Some(&slots),
                )),
                force_i128_type(stack_val_to_expr(
                    &b,
                    self.params,
                    self.registry,
                    Some(&slots),
                )),
            )
        };
        let result_expr = match intr.op {
            I128Op::Mul => SorobanExpr::Mul(Box::new(a_expr), Box::new(b_expr)),
            I128Op::Div => SorobanExpr::Div(Box::new(a_expr), Box::new(b_expr)),
            // `a / b + (a % b != 0) as i128`: truncating quotient plus 1 when the
            // division is inexact (the round-up wrapper's verified semantics).
            I128Op::DivCeil => SorobanExpr::Add(
                Box::new(SorobanExpr::Div(
                    Box::new(a_expr.clone()),
                    Box::new(b_expr.clone()),
                )),
                Box::new(SorobanExpr::CastAs {
                    value: Box::new(SorobanExpr::Ne(
                        Box::new(SorobanExpr::Rem(Box::new(a_expr), Box::new(b_expr))),
                        Box::new(SorobanExpr::I128Literal(0)),
                    )),
                    target_type: "i128".to_string(),
                }),
            ),
        };
        let result = StackVal::HostCallResult(Box::new(result_expr));
        // Write the result back to every result-pointer frame slot, as a limb pair,
        // at the helper's own result layout (`intr.res_*_off`): unchecked helpers
        // write `{lo@0, hi@8}`; checked `Result<i128,E>` helpers write `{lo@8, hi@16}`
        // with the success/Err discriminant at `+0`. The discriminant slot is left
        // unmodeled (Unknown) on purpose — its success polarity is inconsistent
        // across helpers (some write `0` on Ok, some `1`); an Unknown branch
        // condition is resolved by `fold_checked_result_branch` selecting the
        // value-producing arm, so we recover the value without guessing the polarity.
        for arg in args {
            if let StackVal::FrameSlot(id, base) = arg
                && base.is_static()
            {
                let mut slots = self.frame_slots.borrow_mut();
                slots.insert(
                    (*id, base.base + intr.res_lo_off),
                    StackVal::I128Limb {
                        value: Box::new(result.clone()),
                        hi: false,
                    },
                );
                slots.insert(
                    (*id, base.base + intr.res_hi_off),
                    StackVal::I128Limb {
                        value: Box::new(result.clone()),
                        hi: true,
                    },
                );
            }
        }
        self.found_host_calls = true;
        Some(true)
    }

    /// Reconstruct a fully-clean i128 from the two result-limb slots at
    /// `(id, base+lo_off)` / `(base+hi_off)` as a clean-arith expression, or `None`
    /// if a slot is missing or the value isn't fully recovered. Accepts not only a
    /// direct `I128Limb` pair but also an open-coded add/sub of recovered limbs (via
    /// `reconstruct_i128_operand`) — e.g. the `+ 1` Soroswap's `get_amount_in`
    /// applies to its rounded quotient before storing the result.
    fn recover_clean_i128(
        &self,
        id: u32,
        base: i32,
        lo_off: i32,
        hi_off: i32,
    ) -> Option<SorobanExpr> {
        let (lo, hi) = {
            let slots = self.frame_slots.borrow();
            (
                slots.get(&(id, base + lo_off))?.clone(),
                slots.get(&(id, base + hi_off))?.clone(),
            )
        };
        let (val, clean) = reconstruct_i128_operand(&lo, &hi)?;
        if !clean {
            return None;
        }
        let expr = {
            let slots = self.frame_slots.borrow();
            stack_val_to_expr(&val, self.params, self.registry, Some(&slots))
        };
        expr_is_clean_arith(&expr).then_some(expr)
    }

    /// If the i128 result limbs at `(id, base)` are fully recovered to a clean
    /// arithmetic value (no `UnknownVal`), return their `(lo_off, hi_off)`. Checks
    /// both the unchecked (`lo@0, hi@8`) and checked (`lo@8, hi@16`) result layouts;
    /// `None` if neither is clean. Gate for the checked-arith husk drop.
    fn clean_i128_result_layout(&self, id: u32, base: i32) -> Option<(i32, i32)> {
        if self.recover_clean_i128(id, base, 8, 16).is_some() {
            Some((8, 16))
        } else if self.recover_clean_i128(id, base, 0, 8).is_some() {
            Some((0, 8))
        } else {
            None
        }
    }

    /// Recognize the SDK `Result<i128,E>::unwrap`-and-pack helper and return the
    /// recovered i128 value directly, instead of inlining its multi-level
    /// discriminant-check + `obj_from_i128_pieces` chain (which underflows to
    /// `todo!` four or five inline levels deep). The helper `(i32 ptr, ..) -> i64`
    /// reads a `Result<i128,E>` at `ptr` (disc@0, value@8/16) and returns the value
    /// packed as a host `Val`, panicking on `Err`; it is identified by transitively
    /// reaching `obj_from_i128_pieces`. When `ptr` is a frame slot already holding a
    /// fully-recovered i128 — left there by a checked-arith composite whose husks
    /// were dropped — return that value. Faithful: the happy-path result, with the
    /// unwrap's `Err` panic dropped, and gated on a clean i128 so it can only fire
    /// when the value was genuinely reconstructed.
    fn try_lower_result_unwrap_pack(
        &mut self,
        target_idx: u32,
        args: &[StackVal],
        num_results: usize,
    ) -> Option<bool> {
        use crate::wasm::ir::WasmType;
        if num_results != 1 {
            return None;
        }
        let ft = self.wasm_module.get_func_type(target_idx)?;
        if ft.params.first() != Some(&WasmType::I32) || ft.results.as_slice() != [WasmType::I64] {
            return None;
        }
        if !(func_reaches_host(
            self.wasm_module,
            target_idx,
            HostModule::Int,
            "obj_from_i128_pieces",
            0,
        ) || func_reaches_host(
            self.wasm_module,
            target_idx,
            HostModule::Int,
            "obj_from_u128_pieces",
            0,
        )) {
            return None;
        }
        let StackVal::FrameSlot(id, base) = args.first()? else {
            return None;
        };
        if !base.is_static() {
            return None;
        }
        let (id, base) = (*id, base.base);
        // The Result's i128 value lives at ptr+8 / ptr+16 (after the discriminant
        // at +0). Only fire when both limbs reconstruct to a fully-recovered i128.
        let value = self.recover_clean_i128(id, base, 8, 16)?;
        self.stack.push(StackVal::HostCallResult(Box::new(value)));
        self.found_host_calls = true;
        Some(true)
    }

    /// Lower a `Symbol`-from-linear-memory builder call to the recovered symbol.
    ///
    /// `Call(builder)[result_ptr, str_ptr, str_len]` where `str_ptr`/`str_len` are
    /// constants reads the static UTF-8 string at `(str_ptr, str_len)` and writes
    /// `Symbol::new(name)` to the builder's result pointer — the `Ok` symbol at
    /// `result_ptr + 8`, the `0` discriminant at `result_ptr + 0` — so the caller's
    /// `i32.load 0; br_if` (error check) and `i64.load 8` (symbol) recover the key.
    /// Mirrors how `symbol_new_from_linear_memory` is already lifted, but reaches it
    /// when the encoder sits past the inlining depth limit (the inlined
    /// `DataKey::into_val` dispatch). Returns `None` (falls back to inlining) unless
    /// the builder is recognized, both string args are constants, the bytes decode to
    /// a plausible symbol name, and the result pointer is a static frame slot.
    fn try_lower_symbol_builder(&mut self, target_idx: u32, args: &[StackVal]) -> Option<bool> {
        if !is_symbol_from_lm_builder(self.wasm_module, target_idx) {
            return None;
        }
        let str_ptr = to_u64(args.get(1)?)? as u32;
        let str_len = to_u64(args.get(2)?)? as u32;
        let name = self
            .wasm_module
            .data_sections
            .read_string(str_ptr, str_len)?;
        // A Soroban symbol is `[a-zA-Z0-9_]+`; reject anything else so we never
        // fabricate a symbol from a misclassified builder or stray constant args.
        if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            return None;
        }
        let StackVal::FrameSlot(id, base) = args.first()? else {
            return None;
        };
        if !base.is_static() {
            return None;
        }
        let symbol = StackVal::HostCallResult(Box::new(SorobanExpr::SymbolLiteral(name)));
        self.store_frame_slot(*id, base.base + 8, symbol, 8);
        self.store_frame_slot(*id, base.base, StackVal::I32(0), 4);
        self.found_host_calls = true;
        Some(true)
    }

    /// Recover the SDK `Option<u32>` decode of a `Vec::first_index_of` result.
    ///
    /// The decoder (see [`detect_option_decode_helper`]) writes a `{tag, value}`
    /// struct, and the caller `br_table`s on `tag` (`0 = None`, `1 = Some(small)`,
    /// `2 = Some(obj)`), routing `None`/`obj` to a `SafetyNetUnreachable` and only
    /// `Some(small)` to the live continuation — i.e. an `.unwrap()`. Without
    /// modeling, the tag load reads an untracked frame slot, degrades to
    /// `UnknownVal`, the `br_table` match is discarded, and the body renders the
    /// downstream as `todo!("unknown value")` (the aquarius `estimate_swap` case).
    ///
    /// Seed the decoder's output so the existing dataflow recovers it: the value
    /// slot with `first_index_of(..).unwrap()`, and the tag slot with the
    /// `Some(small)` discriminant (`1`) so the `br_table` folds to that arm and the
    /// dead arms drop — mirroring [`seed_sret_success_status`], which likewise seeds
    /// the convention-live discriminant.
    ///
    /// Narrowly gated on the exact decoder shape and a `first_index_of` operand.
    /// This assumes the `.unwrap()` lowering — the `None`/element-absent arm is
    /// unreachable, as it is for every `first_index_of` site in the corpus (the
    /// `br_table` routes `None`/object to a `SafetyNetUnreachable`). A contract that
    /// genuinely handled the missing element would have its `None` branch folded
    /// away; recovering that as a real `match`/`if let` (verifying the `None` arm's
    /// liveness from the consuming `br_table`) is tracked as follow-up. Even so this
    /// is no worse than the prior output, which discarded the whole dispatch as an
    /// unresolved `todo!("unknown value")`.
    fn try_lower_option_decode(&mut self, target_idx: u32, args: &[StackVal]) -> Option<bool> {
        let layout = detect_option_decode_helper(self.wasm_module, target_idx)?;
        let StackVal::FrameSlot(id, base) = args.first()? else {
            return None;
        };
        if !base.is_static() {
            return None;
        }
        let (id, base) = (*id, base.base);
        let opt_expr = {
            let slots = self.frame_slots.borrow();
            stack_val_to_expr(args.get(1)?, self.params, self.registry, Some(&slots))
        };
        if !expr_is_first_index_of(&opt_expr) {
            return None;
        }
        let unwrapped = SorobanExpr::MethodCall {
            object: Box::new(opt_expr),
            method: "unwrap".to_string(),
            args: Vec::new(),
        };
        self.store_frame_slot(
            id,
            base + layout.val_off,
            StackVal::HostCallResult(Box::new(unwrapped)),
            8,
        );
        self.store_frame_slot(id, base + layout.tag_off, StackVal::I32(1), 4);
        self.found_host_calls = true;
        cov_mark::hit!(option_decode_first_index_of);
        Some(true)
    }

    /// Observe a fallible storage-get helper call (see
    /// [`detect_fallible_storage_get_helper`]) and record the FIRST one in the
    /// top-level function for `lift_function_body` to rebuild as
    /// `env.storage().<dur>().get(&key).ok_or(Error::V)` — instead of the lossy
    /// `has`/`extend_ttl` + `todo!()` husk the inliner produces. Pure observer:
    /// does not consume the call (it still inlines as before; the husk is replaced
    /// wholesale only for a direct-return getter).
    fn note_fallible_storage_get(&mut self, target_idx: u32, args: &[StackVal]) {
        // Only the top-level function's own getters.
        if self.inline_depth != 0 {
            return;
        }
        // `.ok_or(..)` needs a `Result<_, E>` return to graft the error onto.
        let Some(ScSpecTypeDef::Result(r)) = self.return_type else {
            return;
        };
        let Some(info) =
            detect_fallible_storage_get_helper(self.wasm_module, self.registry, target_idx)
        else {
            return;
        };
        // Count EVERY fallible-get the function performs so `lift_function_body`
        // can tell a single-read getter (rebuildable as a value-returning tail)
        // from a multi-read one (only its leading early-return is faithful).
        // Record only the genuine FIRST: if its key is unrecoverable we record
        // nothing (husk unchanged) rather than grafting a later, possibly
        // out-of-order read's error onto the return.
        let is_first = *self.fallible_get_count.borrow() == 0;
        *self.fallible_get_count.borrow_mut() += 1;
        if !is_first {
            return;
        }
        let key = if let Some(k) = info.const_key {
            k
        } else {
            // Parameter-keyed getter: the key is the helper's 2nd argument — NOT
            // the husk's separate `has(&7)` read (a different, lost load).
            let slots = self.frame_slots.borrow();
            stack_val_to_expr(
                args.get(1).unwrap_or(&StackVal::Unknown),
                self.params,
                self.registry,
                Some(&slots),
            )
        };
        // Don't record a fabricated/unknown key (would render `get(&todo!())`).
        if matches!(key, SorobanExpr::UnknownVal | SorobanExpr::Void) {
            return;
        }
        *self.fallible_get_recovery.borrow_mut() = Some(FallibleGetRecord {
            key,
            storage_type: info.storage_type,
            error_code: info.error_code,
            err_type: (*r.error_type).clone(),
        });
    }

    /// Recover a `DataKey` storage key built from a *constant descriptor pointer*.
    ///
    /// Some SDK key accessors don't pass an immediate variant index to the key
    /// constructor (the `did_key_construct` path); instead they pass a pointer
    /// to a 1-byte enum-discriminant segment in the data section, and the
    /// `(i32 desc_ptr) -> i64` constructor reads the discriminant and `br_table`s
    /// over it to build the key `Symbol`. That dispatch chain
    /// (`126 → 270 → 66 → 64 → 134 → encoder` in aquarius) is inlined and
    /// constant-folded correctly, but the recovered symbol lands in a dead `var_N`
    /// binding while the key the storage op reads degrades to `UnknownVal` — so the
    /// accessor renders `get(&todo!())`.
    ///
    /// When the constructor's arg is a constant pointer `P` into the data section,
    /// read the discriminant `D = data[P]` and resolve the variant name directly
    /// from the constructor's own ordered `(ptr, len)` string table (the arms appear
    /// in discriminant order, so the table is indexed by `D`). Push
    /// `vec![&env, Symbol::new(&env, name)]` as the constructor's result, so the
    /// whole downstream chain (and any `.get/.has/.set/.remove`) resolves through
    /// the existing dataflow.
    ///
    /// Tightly gated so it can only fire on a genuine symbol-key constructor with a
    /// readable static discriminant resolving to a valid symbol name — otherwise it
    /// returns `false` and the call falls through to normal inlining (`todo!`,
    /// never a fabricated value).
    fn try_push_descriptor_key(&mut self, target_idx: u32, first_arg_i32: Option<i32>) -> bool {
        let Some(ptr) = first_arg_i32 else {
            return false;
        };
        let Some(key) = descriptor_key_from_ptr(self.wasm_module, target_idx, ptr) else {
            return false;
        };
        self.stack.push(StackVal::HostCallResult(Box::new(key)));
        true
    }

    /// Fold a *frame-descriptor* DataKey constructor call — the `(i32) -> i64`
    /// descriptor-pointer form of the DataKey dispatcher where the descriptor
    /// row lives in the CALLER's shadow-stack frame, built just before the
    /// call (`i32.store` selector at `+0`, `i64.store` runtime payload Vals at
    /// `+8`, `+16`, …). This is the SDK's keyed-variant lowering
    /// (`DataKey::UserRewardData(user)`), and the reason the whole
    /// `has/set/get/extend_ttl` protocol around user-keyed storage lifted with
    /// `todo!()` keys: the const-pointer paths (`load_struct_const_key`,
    /// `try_push_descriptor_key`) require static descriptors.
    ///
    /// The recovery is by EXECUTION, the same proof the dispatcher fold uses:
    /// seed the micro-evaluator's memory with the descriptor row exactly as
    /// the lift context knows it abstractly — constant slots concretely, the
    /// runtime payload slots as opaque [`DkVal::Arg`] tokens — and run the
    /// ctor's real bytecode. The evaluator's discipline makes the proof
    /// airtight: `Arg` participates in nothing but moves (any arithmetic or
    /// comparison on it bails), unseeded slots fail their loads, and store
    /// widths must match load widths exactly, so a completed eval proves the
    /// selector picked its arm and the payload Vals flowed untouched into the
    /// key vector. `dk_result_to_key_expr` then renders `Arg` payloads
    /// through the caller's actual `StackVal`s — an unrecovered payload
    /// stays an honest `todo!()` hole inside the proven key shape.
    fn try_fold_frame_descriptor_key(&mut self, target_idx: u32, args: &[StackVal]) -> bool {
        use crate::wasm::ir::WasmType;
        let [StackVal::FrameSlot(id, off)] = args else {
            return false;
        };
        if off.term.is_some() {
            return false;
        }
        let Some(ft) = self.wasm_module.get_func_type(target_idx) else {
            return false;
        };
        if ft.params.as_slice() != [WasmType::I32] || ft.results.as_slice() != [WasmType::I64] {
            return false;
        }
        if !is_datakey_dispatcher(self.wasm_module, target_idx) {
            return false;
        }
        // A synthetic address for the descriptor row, far above the shadow
        // stack the ctor grows downward from `StackPtr(0)` — the evaluator's
        // memory is entry-SP-relative, so the row can never collide with any
        // interpreted frame.
        const DESC_BASE: i32 = 1 << 20;
        // Descriptor rows are one selector plus at most a few payload Vals;
        // 64 bytes covers every observed layout with slack.
        const DESC_BYTES: i32 = 64;
        // PROVENANCE GATE (the audit that killed the naive frame_slots
        // read): the abstract slot map is ACCUMULATED state — a slot can
        // hold an unlogged recognizer seed (blend's `I128Limb` in a
        // descriptor row) whose runtime overwrite the lifter missed, and
        // embedding one fabricates a key payload. A descriptor slot is
        // seeded only when its current abstract value IS its last entry in
        // the ordered store log (t9's `slot_write_log`): the value then
        // provably comes from a real, modeled `i32/i64.store` that nothing
        // the lifter saw has shadowed. Unjustified slots stay unseeded — if
        // the ctor's arm loads one, the eval's load misses and the fold
        // refuses (an honest `todo!()`, never a stale key). Stale CONSTANT
        // Vals that pass this gate (a logged scalar the runtime later
        // overwrote through an unmodeled path) are de-fanged at the render
        // layer: `dk_result_to_key_expr` embeds False/True only for the
        // exact 0/1 words and refuses object-tagged constants outright.
        let mut fresh: HashMap<i32, (StackVal, u32)> = HashMap::new();
        {
            let slots = self.frame_slots.borrow();
            let log = self.slot_write_log.borrow();
            let mut seen: Vec<i32> = Vec::new();
            // Same-frame stores encountered so far in the reverse walk —
            // i.e. stores that happened AFTER the walk's current point in
            // time — as `(offset, width)` byte ranges. A candidate slot
            // whose range any of them overlaps at a DIFFERENT offset has
            // had bytes clobbered without its own `(frame, offset)` log/map
            // entries changing (an `i64.store` at `+4` rewriting half of
            // the payload at `+8` — greptile P1), so it is refused.
            let mut later_writes: Vec<(i32, u32)> = Vec::new();
            let total = (0..DESC_BYTES / 8)
                .filter(|k| slots.contains_key(&(*id, off.base + 8 * k)))
                .count();
            for w in log.iter().rev() {
                if seen.len() >= total {
                    break;
                }
                let (sid, soff) = w.key;
                if sid != *id {
                    continue;
                }
                let k = soff - off.base;
                if !(0..DESC_BYTES).contains(&k) || seen.contains(&k) {
                    // Out-of-window and shadowed same-frame stores still
                    // participate in the overlap test (a store just below
                    // the window can clobber its first slot).
                    later_writes.push((soff, w.width));
                    continue;
                }
                seen.push(k);
                let clobbered = later_writes.iter().any(|(j, jw)| {
                    *j != soff && *j < soff + w.width as i32 && j + *jw as i32 > soff
                });
                // Last logged write for this slot: justified only if the
                // abstract map still holds exactly that value AND no later
                // store overlapped its bytes.
                if !clobbered && slots.get(&w.key) == Some(&w.new) {
                    fresh.insert(k, (w.new.clone(), w.width));
                }
                later_writes.push((soff, w.width));
            }
        }
        if fresh.is_empty() {
            return false;
        }
        let mut mem = HashMap::new();
        let mut payloads: Vec<StackVal> = Vec::new();
        // Offset order, so payload `Arg` indices are deterministic.
        let mut fresh: Vec<(i32, (StackVal, u32))> = fresh.into_iter().collect();
        fresh.sort_by_key(|(k, _)| *k);
        for (k, (v, width)) in &fresh {
            // The seeded cell's width is the REAL store instruction's width
            // from the log; a mismatch with what the ctor actually loads
            // fails the evaluator's exact-width check and refuses the fold —
            // never a wrong recovery. Sub-word stores never seed (descriptor
            // fields are i32/i64), and constants stored at the other width
            // seed as the runtime memory actually holds them.
            let dv = match (v, width) {
                (StackVal::I32(c), 4) => DkVal::I32(*c),
                (StackVal::I64(c), 8) => DkVal::I64(*c),
                // An `i64.store` of a zero/sign-extended i32: for the
                // non-negative values descriptors hold, both extensions
                // agree; a negative value's extension is ambiguous here, so
                // it stays unseeded.
                (StackVal::I32(c), 8) if *c >= 0 => DkVal::I64(*c as i64),
                (StackVal::I32(_), 8) => continue,
                (StackVal::I64(c), 4) => DkVal::I32(*c as i32),
                (_, 1 | 2) => continue,
                (other, _) => {
                    payloads.push(other.clone());
                    DkVal::Arg(payloads.len() - 1)
                }
            };
            mem.insert(DESC_BASE + k, (dv, *width));
        }
        if *DBG_FDK {
            eprintln!(
                "[FDK] ctor={target_idx} frame=({id},{}) mem={mem:?} payloads={payloads:?}",
                off.base
            );
        }
        let mut ev = DkEval {
            module: self.wasm_module,
            mem,
            sp: DkVal::StackPtr(0),
            steps: 0,
            gap_zero: None,
        };
        let Some(Some(result)) = ev.eval_call(target_idx, vec![DkVal::StackPtr(DESC_BASE)], 0)
        else {
            if *DBG_FDK {
                eprintln!(
                    "[FDK] ctor={target_idx} eval bailed (window base {})",
                    off.base
                );
            }
            return false;
        };
        let Some(key) = self.dk_result_to_key_expr(&result, &payloads) else {
            if *DBG_FDK {
                eprintln!("[FDK] ctor={target_idx} result not a key: {result:?}");
            }
            return false;
        };
        if *DBG_FDK {
            eprintln!("[FDK] ctor={target_idx} FOLDED -> {key:?}");
        }
        cov_mark::hit!(frame_descriptor_key_folded);
        self.stack.push(StackVal::HostCallResult(Box::new(key)));
        // Deliberately NOT `found_host_calls = true` (unlike the dispatcher
        // fold): the ctor is a pure key derivation, and claiming a host call
        // here flips an enclosing pure helper's inline onto the effectful
        // statement-splice path, breaking its value threading (observed as
        // blend-emitter losing its `LastDistro` getter recoveries).
        true
    }

    /// Fold a constant-selector call to a *DataKey dispatcher* — the SDK's
    /// `DataKey::into_val` lowering for a multi-variant storage-key enum:
    /// `(i64 selector, i64 payload…) -> i64 Val`, a `br_table` over the
    /// selector where each arm builds its variant's key from linear-memory
    /// strings (see the `DkEval` module comment for why structural matching
    /// is unsafe here).
    ///
    /// The arm the constant selector picks is resolved by micro-evaluating
    /// the dispatcher's real bytecode with payload args held abstract: the
    /// symbol bytes come from the data section, the key shape from the actual
    /// `vec_new_from_linear_memory` window — reconstruction by execution,
    /// never by guessing. Anything unmodeled bails to normal inlining (an
    /// honest `todo!`).
    fn try_fold_datakey_dispatcher(&mut self, target_idx: u32, args: &[StackVal]) -> bool {
        use crate::wasm::ir::WasmType;
        let dbg = std::env::var("DBG_DK").is_ok();
        if args.is_empty() {
            return false;
        }
        let Some(ft) = self.wasm_module.get_func_type(target_idx) else {
            return false;
        };
        if ft.results.as_slice() != [WasmType::I64]
            || ft.params.is_empty()
            || ft.params.iter().any(|p| *p != WasmType::I64)
            || ft.params.len() != args.len()
        {
            return false;
        }
        // The selector must be a compile-time constant; payloads may be
        // anything (they pass through the evaluator abstractly).
        if !matches!(args[0], StackVal::I64(_)) {
            if dbg {
                eprintln!(
                    "[DBG_DK] func {target_idx}: selector not const: {:?}",
                    args[0]
                );
            }
            return false;
        }
        if !is_datakey_dispatcher(self.wasm_module, target_idx) {
            if dbg {
                eprintln!("[DBG_DK] func {target_idx}: not a dispatcher (shape gate)");
            }
            return false;
        }
        let dk_args: Vec<DkVal> = args
            .iter()
            .enumerate()
            .map(|(i, a)| match a {
                StackVal::I64(v) => DkVal::I64(*v),
                _ => DkVal::Arg(i),
            })
            .collect();
        let mut ev = DkEval {
            module: self.wasm_module,
            mem: HashMap::new(),
            sp: DkVal::StackPtr(0),
            steps: 0,
            gap_zero: None,
        };
        let Some(Some(result)) = ev.eval_call(target_idx, dk_args, 0) else {
            if dbg {
                eprintln!(
                    "[DBG_DK] func {target_idx}: eval bailed (selector {:?})",
                    args[0]
                );
            }
            return false;
        };
        let Some(key) = self.dk_result_to_key_expr(&result, args) else {
            if dbg {
                eprintln!("[DBG_DK] func {target_idx}: result not a key: {result:?}");
            }
            return false;
        };
        if dbg {
            eprintln!(
                "[DBG_DK] func {target_idx}: FOLDED {:?} -> {key:?}",
                args[0]
            );
        }
        self.stack.push(StackVal::HostCallResult(Box::new(key)));
        self.found_host_calls = true;
        true
    }

    /// Convert a `DkEval` result into a storage-key expression. Accepts only
    /// genuine key shapes: a `Symbol` Val, or a `Vec` headed by a `Symbol`
    /// (the SDK vec-wraps unit variants too — `DataKey::Admin` ⇒
    /// `Vec[Symbol("Admin")]`). Abstract `Arg(i)` elements (the payloads)
    /// render through the caller's actual `StackVal`s — an unrecovered
    /// payload stays an honest `todo!` *inside* the proven key shape.
    fn dk_result_to_key_expr(&self, result: &DkVal, args: &[StackVal]) -> Option<SorobanExpr> {
        let sym_of = |v: &DkVal| -> Option<String> {
            match v {
                DkVal::I64(raw) => crate::wasm::data::DataSection::decode_symbol_val(*raw as u64),
                DkVal::SymObj(name) => Some(name.clone()),
                _ => None,
            }
        };
        // A payload expression is embedded only when it is a plausible runtime
        // key component. Error-tagged Vals are the SDK's conversion-failure
        // sentinels — branch-sequential lifting leaves them in caller locals,
        // and embedding one would fabricate a key payload. The variant name
        // stays proven; the payload degrades to an honest `UnknownVal` hole.
        let payload_or_hole = |ex: SorobanExpr| -> SorobanExpr {
            match &ex {
                SorobanExpr::ContractError { .. } | SorobanExpr::ErrorFromCode(_) => {
                    SorobanExpr::UnknownVal
                }
                _ => ex,
            }
        };
        match result {
            DkVal::I64(_) | DkVal::SymObj(_) => Some(SorobanExpr::SymbolLiteral(sym_of(result)?)),
            DkVal::VecVal(elems) => {
                let (head, rest) = elems.split_first()?;
                let mut out = vec![SorobanExpr::SymbolLiteral(sym_of(head)?)];
                for e in rest {
                    out.push(match e {
                        DkVal::Arg(i) => payload_or_hole(stack_val_to_expr(
                            args.get(*i)?,
                            self.params,
                            self.registry,
                            Some(&self.frame_slots.borrow()),
                        )),
                        DkVal::I64(v) => {
                            // Constant payload Val: only small-value tags are
                            // plausible static key components (False/True and
                            // the 4..=14 small range). Tag 3 is Error — the
                            // ConversionError sentinel lands here. False/True
                            // are only genuine when the WHOLE word is 0 or 1:
                            // a stale scalar whose low byte happens to be zero
                            // (blend's SCALAR_12 = 0xE8D4A51000) is NOT a
                            // False Val and must not render as one.
                            let tag = (*v as u64) & 0xff;
                            let bad_bool = matches!(tag, 0 | 1) && *v != tag as i64;
                            if bad_bool || !matches!(tag, 0 | 1 | 4..=14) {
                                SorobanExpr::UnknownVal
                            } else {
                                let ex = stack_val_to_expr(
                                    &StackVal::I64(*v),
                                    self.params,
                                    self.registry,
                                    None,
                                );
                                if matches!(ex, SorobanExpr::UnknownVal) {
                                    return None;
                                }
                                ex
                            }
                        }
                        DkVal::SymObj(n) => SorobanExpr::SymbolLiteral(n.clone()),
                        _ => return None,
                    });
                }
                Some(SorobanExpr::VecConstruct(out))
            }
            _ => None,
        }
    }

    /// A dynamic (loop-indexed) write `frame[base + coeff*i]` may land on any
    /// static slot whose offset is `>= base` and congruent to `base` modulo
    /// `coeff`. Since the analyzer doesn't know the loop bound, conservatively
    /// drop every such static slot in this frame so a later static load can't
    /// return a value the loop may have overwritten. (Soundness hardening; on
    /// the current fixtures no dynamic term ever forms, so this is a no-op.)
    fn invalidate_static_aliases(&self, id: u32, term: SymTerm, base: i32) {
        let coeff = term.coeff as i32;
        if coeff <= 0 {
            return;
        }
        let mut removed: Vec<(u32, i32)> = Vec::new();
        self.frame_slots.borrow_mut().retain(|&(sid, off), _| {
            let aliased = sid == id && off >= base && (off - base).rem_euclid(coeff) == 0;
            if aliased {
                removed.push((sid, off));
            }
            !aliased
        });
        // Poison the store journal for every invalidated slot: the dynamic
        // write may have overwritten it at runtime with a value the static
        // journal never saw, so the unique-reaching-def fill must refuse to
        // resurrect the stale pre-invalidation store (greptile P1).
        let mut journal = self.slot_defs.borrow_mut();
        for key in removed {
            journal.entry(key).or_default().push(StackVal::Unknown);
        }
    }

    /// Model the `Result` discriminant of an sret (struct-return) call: a void
    /// helper that received `result_ptr` (frame slot `(id, base)`) and produced a
    /// cross-contract call result it stored at `result_ptr + 8`, but left no usable
    /// discriminant at `result_ptr + 0`. Seed `+0` with `SretResult(<call>)` so a
    /// subsequent `i32.load; br_table` on it reconstructs the `Ok`/`Err` dispatch
    /// (and the success-arm return) instead of seeing `Unknown` and being dropped.
    ///
    /// Tightly gated to avoid false positives: fires only when the payload slot
    /// holds a genuine cross-contract invoke and the discriminant slot isn't
    /// already a meaningful call result.
    fn model_sret_discriminant(&self, id: u32, base: i32) {
        let mut slots = self.frame_slots.borrow_mut();
        // A discriminant already modeled as a call result — leave it.
        if matches!(slots.get(&(id, base)), Some(StackVal::HostCallResult(_))) {
            return;
        }
        let Some(StackVal::HostCallResult(payload)) = slots.get(&(id, base + 8)).cloned() else {
            return;
        };
        // The helper's payload may wrap a cross-contract invoke in decoders /
        // method chains (ValConvert / MethodCall / FieldAccess / ValTag), so look
        // for it anywhere in the expression tree, not just at the root.
        if expr_contains_invoke_contract(&payload) {
            slots.insert(
                (id, base),
                StackVal::HostCallResult(Box::new(SorobanExpr::SretResult(payload))),
            );
            cov_mark::hit!(sret_discriminant_modeled);
        }
    }

    /// For a void helper that received a `result_ptr` frame slot and transitively
    /// performs a cross-contract call, seed `result_ptr + 0` with the success
    /// status byte (`I64(0)`) when nothing has populated it yet. SDK helpers use
    /// the convention `result_ptr+0 = 0 (Ok) / 1 (Err)` followed by
    /// `i64.load; i64.const 1; i64.eq; br_if @outer` (an "if Err panic" guard).
    /// With `+0 = 0` the guard folds to "don't branch" and the success path —
    /// including the load of the payload at `+8` and the function's return —
    /// inlines instead of being dropped as an unresolved scrutinee. Tightly gated
    /// on the cross-contract-call signal to avoid misfiring on scratch buffers.
    fn seed_sret_success_status(&self, id: u32, base: i32, target_idx: u32) {
        let mut slots = self.frame_slots.borrow_mut();
        if !matches!(slots.get(&(id, base)), None | Some(StackVal::Unknown)) {
            return;
        }
        let chains_call = function_calls_host_in_chain(
            self.wasm_module,
            target_idx,
            HostModule::Call,
            "try_call",
            MAX_INLINE_CALL_DEPTH,
        ) || function_calls_host_in_chain(
            self.wasm_module,
            target_idx,
            HostModule::Call,
            "call",
            MAX_INLINE_CALL_DEPTH,
        );
        if !chains_call {
            return;
        }
        slots.insert((id, base), StackVal::I64(0));
        cov_mark::hit!(sret_success_status_seeded);
    }

    /// For a void helper that received a `result_ptr` frame slot and implements
    /// the fallible storage-decode protocol — reaches BOTH `has_contract_data`
    /// and `get_contract_data`, writing `[disc@0, value@8]` with the `Option`
    /// convention `0 = missing/None, 1 = present/Some` — seed `result_ptr + 0`
    /// with the [`StackVal::OptionDecodeDisc`] marker when nothing has
    /// populated it (issue #35).
    ///
    /// The marker is deliberately NOT a constant: only the consumer knows
    /// whether a branch on the discriminant is the `.unwrap()`'s redundant
    /// None-panic (foldable — the IfElse handler folds the bare-trap shape) or
    /// real control flow (an `unwrap_or` default arm, a kill-switch check, a
    /// `panic_with_error!` with a specific code — all of which must survive;
    /// the marker then degrades to `UnknownVal`, exactly today's honest
    /// `todo!()`). Note the convention is the INVERSE of the cross-contract
    /// sret seed above (`0 = Ok` there); the two are mutually exclusive — a
    /// helper that both invokes and stores is ambiguous and stays unmodeled.
    /// Returns `true` when the marker was seeded by THIS call (the gate matched
    /// and the slot was unmodeled), so the caller can run follow-on modeling
    /// that is only valid for a freshly-recognized option-decode wrapper.
    fn seed_option_decode_status(&self, id: u32, base: i32, target_idx: u32) -> bool {
        let mut slots = self.frame_slots.borrow_mut();
        if !matches!(slots.get(&(id, base)), None | Some(StackVal::Unknown)) {
            return false;
        }
        let chains_get = function_calls_host_in_chain(
            self.wasm_module,
            target_idx,
            HostModule::Ledger,
            "get_contract_data",
            MAX_INLINE_CALL_DEPTH,
        );
        let chains_has = function_calls_host_in_chain(
            self.wasm_module,
            target_idx,
            HostModule::Ledger,
            "has_contract_data",
            MAX_INLINE_CALL_DEPTH,
        );
        let chains_call = function_calls_host_in_chain(
            self.wasm_module,
            target_idx,
            HostModule::Call,
            "call",
            MAX_INLINE_CALL_DEPTH,
        ) || function_calls_host_in_chain(
            self.wasm_module,
            target_idx,
            HostModule::Call,
            "try_call",
            MAX_INLINE_CALL_DEPTH,
        );
        if !(chains_get && chains_has) || chains_call {
            return false;
        }
        slots.insert((id, base), StackVal::OptionDecodeDisc);
        cov_mark::hit!(option_decode_status_seeded);
        true
    }

    /// After [`seed_option_decode_status`] fires for a fallible has+get storage
    /// wrapper, link the VALUE slot (`result_ptr + 8`) to the loaded value
    /// (issue #34 slice). The helper's internal branch join collapsed the store
    /// to `Unknown`, so every later load of `+8` rendered `todo!()` — even
    /// though the inline emitted the very `get(..)` that produced the value, as
    /// a discarded orphan statement. Promote that unique orphan to a
    /// `let var_N` binding and seed `+8` with the binding, so consumers read
    /// `var_N`: the once-loaded value. Never re-issue the get at a consumer —
    /// a second host call could observe a different value across storage
    /// mutations.
    ///
    /// Airtight gates, any failure → byte-identical output:
    /// - the value slot is still unmodeled;
    /// - the helper chain decodes nothing (no Int-module conversion, no
    ///   map/vec unpack) — its `+8` slot therefore holds the raw loaded `Val`,
    ///   not a scalar limb / error-code layout;
    /// - the inlined statements contain EXACTLY ONE top-level storage get
    ///   (an orphan `Expr` or an existing `Let`) with a recovered (non-hole)
    ///   key.
    fn link_option_decode_value(
        &mut self,
        id: u32,
        base: i32,
        target_idx: u32,
        stmts: &mut [SorobanStmt],
    ) {
        {
            let slots = self.frame_slots.borrow();
            if !matches!(slots.get(&(id, base + 8)), None | Some(StackVal::Unknown)) {
                return;
            }
        }
        // Decoding getters (scalar limbs, struct unpack) use a different
        // out-slot layout — `+8` is an error code or a limb there, never the
        // raw loaded Val. Any conversion/unpack in the chain → stay honest.
        if function_calls_module_in_chain(
            self.wasm_module,
            target_idx,
            HostModule::Int,
            MAX_INLINE_CALL_DEPTH,
        ) || function_calls_host_in_chain(
            self.wasm_module,
            target_idx,
            HostModule::Map,
            "map_unpack_to_linear_memory",
            MAX_INLINE_CALL_DEPTH,
        ) || function_calls_host_in_chain(
            self.wasm_module,
            target_idx,
            HostModule::Vec,
            "vec_unpack_to_linear_memory",
            MAX_INLINE_CALL_DEPTH,
        ) {
            return;
        }
        // A single top-level storage get, orphan or already-bound.
        enum GetSite {
            Orphan(usize),
            Bound(String),
        }
        let mut site: Option<GetSite> = None;
        for (i, stmt) in stmts.iter().enumerate() {
            let (key, bound) = match stmt {
                SorobanStmt::Expr(SorobanExpr::StorageGet { key, .. }) => (key, None),
                SorobanStmt::Let {
                    name,
                    value: SorobanExpr::StorageGet { key, .. },
                    ..
                } => (key, Some(name.clone())),
                _ => continue,
            };
            if matches!(key.as_ref(), SorobanExpr::UnknownVal) || site.is_some() {
                return; // hole-keyed or ambiguous → stay honest
            }
            site = Some(match bound {
                Some(name) => GetSite::Bound(name),
                None => GetSite::Orphan(i),
            });
        }
        let seed = match site {
            None => return,
            Some(GetSite::Bound(name)) => {
                StackVal::HostCallResult(Box::new(SorobanExpr::NamedLocal(name)))
            }
            Some(GetSite::Orphan(i)) => {
                let var_idx = self.locals.len() as u32;
                self.locals.push(StackVal::LetBinding(var_idx));
                let placeholder = SorobanStmt::Expr(SorobanExpr::Void);
                let SorobanStmt::Expr(get_expr) = std::mem::replace(&mut stmts[i], placeholder)
                else {
                    return;
                };
                stmts[i] = SorobanStmt::Let {
                    name: format!("var_{var_idx}"),
                    mutable: false,
                    value: get_expr,
                };
                StackVal::LetBinding(var_idx)
            }
        };
        self.frame_slots.borrow_mut().insert((id, base + 8), seed);
        cov_mark::hit!(option_decode_value_linked);
    }

    /// Seed the out slots of a recognized defaulting-u128 getter (issue #34
    /// tranche 2): a void has+get helper that writes the decoded u128 as
    /// `[lo@0, hi@8]` with 0 for both limbs when the key is missing — the SDK
    /// shape of `get::<_, u128>(&key).unwrap_or(0)` (an accumulator read).
    /// The helper's internal tag-split join collapsed both limb stores to
    /// `Unknown`; instead of modeling the joins, rewrite the unique inlined
    /// get into the faithful defaulting form bound to a `let var_N`, and seed
    /// BOTH limb slots as that binding's `I128Limb` halves so the existing
    /// (lo, hi) re-pair machinery reconstructs `var_N` at every consumer.
    ///
    /// The caller must have proven the helper class first
    /// ([`detect_defaulting_u128_getter`]); this method adds the state gates:
    /// both limb slots still unmodeled, and EXACTLY ONE top-level storage get
    /// with a recovered key among the inlined statements. Any failure →
    /// byte-identical output. Returns whether the slots were seeded.
    fn seed_defaulting_u128_getter(
        &mut self,
        id: u32,
        base: i32,
        stmts: &mut Vec<SorobanStmt>,
    ) -> bool {
        // NOTE: no "slot still unmodeled" gate here, deliberately. The inline
        // of this very call just wrote both slots, and its branch-sequential
        // simulation of the helper's internal default/decode split leaves
        // MISMATCHED halves (e.g. the literal-0 default at `+0` beside the
        // decoded hi limb at `+8`) that can never re-pair. The detector proved
        // the helper's semantic — both slots are exactly the limbs of
        // `get(..).unwrap_or(0)` — so replacing the simulation artifacts with
        // that proven value is strictly more faithful.
        let Some(protocol) = collect_getter_protocol(stmts) else {
            return false;
        };
        let (storage_type, key) = protocol.get;
        // Resolve a local-variable key through the husk's own binding.
        let key = match &key {
            SorobanExpr::Local(n) => {
                let name = format!("var_{n}");
                match unique_binding_value(&protocol.bindings, &name) {
                    Some(v) => v,
                    None => return false,
                }
            }
            SorobanExpr::NamedLocal(name) => match unique_binding_value(&protocol.bindings, name) {
                Some(v) => v,
                None => return false,
            },
            SorobanExpr::UnknownVal => return false,
            k => k.clone(),
        };
        if expr_contains_unknown(&key) {
            return false;
        }
        // APPEND the faithful defaulting get as a fresh binding, leaving the
        // husk statements untouched. Removing/rewriting them regresses output:
        // several downstream passes key off the husk's exact shape (return-tail
        // extraction of a trailing get, `resolve_unknown_key_field_access`'s
        // binding scan, husk folds). The appended read duplicates the husk's
        // own adjacent read of the SAME key with no store in between (the
        // protocol walk proved the husk contains no writes), so it observes
        // the same value; if no consumer resolves to the binding, dead-store
        // and orphan-call passes clean it up.
        let var_idx = self.locals.len() as u32;
        self.locals.push(StackVal::LetBinding(var_idx));
        stmts.push(SorobanStmt::Let {
            name: format!("var_{var_idx}"),
            mutable: false,
            value: SorobanExpr::CastAs {
                value: Box::new(SorobanExpr::StorageGet {
                    storage_type,
                    key: Box::new(key),
                    unwrap: false,
                    on_missing: Some(Box::new(SorobanExpr::U128Literal(0))),
                }),
                target_type: "u128".to_string(),
            },
        });
        let limb_source = StackVal::LetBinding(var_idx);
        let mut slots = self.frame_slots.borrow_mut();
        slots.insert(
            (id, base),
            StackVal::I128Limb {
                value: Box::new(limb_source.clone()),
                hi: false,
            },
        );
        slots.insert(
            (id, base + 8),
            StackVal::I128Limb {
                value: Box::new(limb_source),
                hi: true,
            },
        );
        cov_mark::hit!(defaulting_u128_getter_seeded);
        true
    }

    /// Seed the payload slots of a proven `TryFromVal` decode helper (issue
    /// #34 tranche 2) with the conversion of its operand. The helper's
    /// small/object tag split collapsed the payload stores at the lifter's
    /// joins, but [`detect_tryfromval_decode_helper`] proved the payload slots
    /// hold exactly `decode(operand)` — so consumers (limb re-pairs, scalar
    /// reads) resolve to the operand's conversion instead of `todo!()`. The
    /// operand must be pure (a parameter or binding reference) so re-reading
    /// it at a consumer duplicates no effect. The discriminant slot is
    /// path-dependent and stays untouched (honest).
    fn seed_decode_helper_result(
        &mut self,
        id: u32,
        base: i32,
        class: DecodeHelperClass,
        operand: &StackVal,
    ) {
        if !stack_val_is_pure(operand) {
            return;
        }
        let target = match class {
            DecodeHelperClass::U64 => "u64",
            DecodeHelperClass::U128 => "u128",
            DecodeHelperClass::I128 => "i128",
        };
        let conv = StackVal::HostCallResult(Box::new(SorobanExpr::ValConvert {
            value: Box::new(stack_val_to_expr(
                operand,
                self.params,
                self.registry,
                Some(&self.frame_slots.borrow()),
            )),
            target_type: target.to_string(),
        }));
        let mut slots = self.frame_slots.borrow_mut();
        match class {
            DecodeHelperClass::U64 => {
                slots.insert((id, base + 8), conv);
            }
            DecodeHelperClass::U128 | DecodeHelperClass::I128 => {
                slots.insert(
                    (id, base + 16),
                    StackVal::I128Limb {
                        value: Box::new(conv.clone()),
                        hi: false,
                    },
                );
                slots.insert(
                    (id, base + 24),
                    StackVal::I128Limb {
                        value: Box::new(conv),
                        hi: true,
                    },
                );
            }
        }
        cov_mark::hit!(decode_helper_result_seeded);
    }

    /// Find the loop-carried locals of a structured loop body: body-local locals
    /// (idx >= num_wasm_params) whose value flows across the back edge — i.e.
    /// their post-body abstract value transitively references their own loop-head
    /// value. Seeds every body-written local with `LoopPhi(idx)`, lifts the body
    /// once on a throwaway context (with a deep-cloned `frame_slots` so it can't
    /// corrupt real state), and keeps the locals whose result still references
    /// their seed. Returns the carried indices in body-write order.
    fn analyze_loop_carried_locals(
        &self,
        body: &[super::structurize::StructuredBlock],
    ) -> Vec<(u32, StackVal)> {
        use crate::wasm::ir::WasmInstr;

        let mut instrs = Vec::new();
        collect_instrs(body, &mut instrs);
        let mut written: Vec<u32> = Vec::new();
        for &i in &instrs {
            if let WasmInstr::LocalSet(idx) | WasmInstr::LocalTee(idx) = i
                && *idx >= self.num_wasm_params
                && !written.contains(idx)
            {
                written.push(*idx);
            }
        }
        if written.is_empty() {
            return Vec::new();
        }

        let mut sim = self.child_context();
        sim.frame_slots = Rc::new(RefCell::new(self.frame_slots.borrow().clone()));
        sim.next_frame_id = Rc::new(RefCell::new(*self.next_frame_id.borrow()));
        // Detach shared mutable state so this throwaway pass can't perturb the
        // real lift's enum-variant disambiguation counter.
        sim.enum_match_counter = Rc::new(RefCell::new(HashMap::new()));
        // Detach the store journal too: speculative stores must not pollute the
        // real lift's unique-reaching-def index. The sim lifts a loop BODY, so
        // it also runs at loop depth (no journal fills).
        sim.slot_defs = Rc::new(RefCell::new(self.slot_defs.borrow().clone()));
        // Same for the read-journal measurement state (issue #34 phase 2).
        sim.slot_write_log = Rc::new(RefCell::new(self.slot_write_log.borrow().clone()));
        sim.slot_taints = Rc::new(RefCell::new(self.slot_taints.borrow().clone()));
        sim.slot_read_log = Rc::new(RefCell::new(Vec::new()));
        sim.loop_depth += 1;
        for &l in &written {
            if let Some(slot) = sim.locals.get_mut(l as usize) {
                *slot = StackVal::LoopPhi(l);
            }
        }
        sim.lift_structured_loop(body);

        written
            .into_iter()
            .filter_map(|l| {
                let v = sim.locals.get(l as usize)?;
                // Exclude a local left as its bare `LoopPhi` seed (written with an
                // identity value) — it isn't genuinely loop-carried.
                let modified = !matches!(v, StackVal::LoopPhi(i) if *i == l);
                (modified && stackval_references_loop_phi(v, l)).then(|| (l, v.clone()))
            })
            .collect()
    }

    /// Find loop-carried frame slots: shadow-stack slots whose value flows across
    /// the back edge (an accumulator spilled to the frame, the aquarius case).
    /// Seeds every slot live at loop entry with `FrameSlotPhi`, lifts the body
    /// once on a throwaway deep-cloned context, and keeps the slots whose
    /// post-body stored value references their own seed and is a genuine
    /// accumulator (not a pure counter, and not a plain copy of another slot —
    /// those don't self-reference). Returns `(slot_key, pre_loop_value)` pairs.
    fn analyze_loop_carried_slots(
        &self,
        body: &[super::structurize::StructuredBlock],
    ) -> Vec<((u32, i32), StackVal)> {
        use crate::wasm::ir::WasmInstr;

        let mut pre_keys: Vec<(u32, i32)> = self.frame_slots.borrow().keys().copied().collect();
        if pre_keys.is_empty() {
            return Vec::new();
        }
        // Sort for deterministic output: `frame_slots` is a HashMap, and the
        // order here decides synthetic spill-variable index allocation. Without
        // sorting, two runs could name the same promoted slots differently.
        pre_keys.sort_unstable();

        let mut sim = self.child_context();
        let mut seeded = self.frame_slots.borrow().clone();
        for &(id, off) in &pre_keys {
            seeded.insert((id, off), StackVal::FrameSlotPhi(id, off));
        }
        sim.frame_slots = Rc::new(RefCell::new(seeded));
        sim.next_frame_id = Rc::new(RefCell::new(*self.next_frame_id.borrow()));
        sim.enum_match_counter = Rc::new(RefCell::new(HashMap::new()));
        sim.slot_defs = Rc::new(RefCell::new(self.slot_defs.borrow().clone()));
        sim.slot_write_log = Rc::new(RefCell::new(self.slot_write_log.borrow().clone()));
        sim.slot_taints = Rc::new(RefCell::new(self.slot_taints.borrow().clone()));
        sim.slot_read_log = Rc::new(RefCell::new(Vec::new()));
        sim.loop_depth += 1;
        // Also seed body-written locals with LoopPhi so an accumulator that adds
        // the counter (`acc += i`) stays symbolic — otherwise the counter's
        // pre-loop constant would make the slot look like a pure `acc + const`
        // counter and wrongly disqualify it.
        let mut instrs = Vec::new();
        collect_instrs(body, &mut instrs);
        for &i in &instrs {
            if let WasmInstr::LocalSet(idx) | WasmInstr::LocalTee(idx) = i
                && *idx >= self.num_wasm_params
                && let Some(slot) = sim.locals.get_mut(*idx as usize)
            {
                *slot = StackVal::LoopPhi(*idx);
            }
        }
        sim.lift_structured_loop(body);

        let result = sim.frame_slots.borrow();
        pre_keys
            .into_iter()
            .filter_map(|(id, off)| {
                let v = result.get(&(id, off))?;
                // Carried iff the body actually rewrote the slot into a value that
                // references its own seed. A slot left untouched still holds its
                // bare `FrameSlotPhi` seed — that "references its phi" trivially
                // but is not loop-carried, so exclude the bare-seed case.
                let modified = !matches!(v, StackVal::FrameSlotPhi(i, o) if *i == id && *o == off);
                let carried = modified
                    && stackval_references_frame_slot_phi(v, id, off)
                    && !is_pure_counter_slot_update(v, id, off);
                // The pre-loop value is what the slot held before the loop.
                carried.then(|| {
                    (
                        (id, off),
                        self.frame_slots.borrow().get(&(id, off)).cloned(),
                    )
                })
            })
            .filter_map(|(k, v)| v.map(|v| (k, v)))
            .collect()
    }

    fn lift_instruction(&mut self, instr: &crate::wasm::ir::WasmInstr) {
        use crate::wasm::ir::WasmInstr;

        match instr {
            // Constants
            WasmInstr::I32Const(v) => self.stack.push(StackVal::I32(*v)),
            WasmInstr::I64Const(v) => self.stack.push(StackVal::I64(*v)),

            // Local access
            WasmInstr::LocalGet(idx) => {
                let val = self
                    .locals
                    .get(*idx as usize)
                    .cloned()
                    .unwrap_or(StackVal::Unknown);
                self.stack.push(val);
            }
            WasmInstr::LocalSet(idx) => {
                let val = self.stack.pop().unwrap_or(StackVal::Unknown);
                // Skip writes to phi-merge-protected locals: the merge code after
                // a br_table block chain recomputes the same value the phi-merge
                // already captured. Allowing the write would overwrite LetBinding(N)
                // with a stale branch-corrupted value, causing the return expression
                // to reference the wrong variable. EXCEPTION: a value that
                // references a phi var is the legitimate post-match composition
                // (udt::add's `a + b`), so let it write through.
                if self.phi_protected_locals.contains(idx) && !stack_val_references_letbinding(&val)
                {
                    return;
                }
                // Loop-carried locals: emit `var_idx = <value>` so the loop body
                // mutates the `let mut var_idx` the Loop arm declared before the
                // loop, and keep the local bound to `var_idx` for later reads.
                if self.loop_carried_locals.contains(idx) {
                    self.emit_loop_carried_assign(*idx, &val);
                    return;
                }
                // For host-call results stored into body-local slots: convert the preceding
                // Expr(call) statement into a Let binding so the call appears only once.
                // Multiple LocalGet(idx) uses will all read the same `var_{idx}` binding.
                if *idx >= self.num_wasm_params
                    && let StackVal::HostCallResult(ref expr) = val
                {
                    let let_stmt = SorobanStmt::Let {
                        name: format!("var_{}", idx),
                        mutable: false,
                        value: (**expr).clone(),
                    };
                    // Replace the speculatively-emitted Expr(call) with a Let binding,
                    // preventing the call from appearing as both Expr and Let.
                    if matches!(self.stmts.last(), Some(SorobanStmt::Expr(_))) {
                        *self.stmts.last_mut().unwrap() = let_stmt;
                    } else {
                        // No preceding Expr (e.g., call was in a nested scope), add Let.
                        self.stmts.push(let_stmt);
                    }
                    if let Some(local) = self.locals.get_mut(*idx as usize) {
                        *local = StackVal::LetBinding(*idx);
                    }
                    return;
                }
                // All other cases: eager inlining (safe for literals, params, arithmetic).
                if let Some(local) = self.locals.get_mut(*idx as usize) {
                    *local = val;
                }
            }
            WasmInstr::LocalTee(idx) => {
                // If the top of stack is FrameBase, allocate a new frame ID and convert to FrameSlot.
                if let Some(StackVal::FrameBase(_)) = self.stack.last() {
                    let frame_id = {
                        let mut fid = self.next_frame_id.borrow_mut();
                        let id = *fid;
                        *fid += 1;
                        id
                    };
                    let slot = StackVal::FrameSlot(frame_id, SlotOffset::at(0));
                    if let Some(local) = self.locals.get_mut(*idx as usize) {
                        *local = slot.clone();
                    }
                    *self.stack.last_mut().unwrap() = slot;
                    return;
                }
                // Skip writes to phi-merge-protected locals (same as LocalSet),
                // except the post-match composition write (value references a phi var).
                if self.phi_protected_locals.contains(idx)
                    && !self
                        .stack
                        .last()
                        .map(stack_val_references_letbinding)
                        .unwrap_or(false)
                {
                    return;
                }
                // Loop-carried locals: emit `var_idx = <value>` and keep the
                // value on the stack (tee). Leave the local bound to `var_idx`.
                if self.loop_carried_locals.contains(idx) {
                    let val = self.stack.last().cloned().unwrap_or(StackVal::Unknown);
                    self.emit_loop_carried_assign(*idx, &val);
                    if let Some(slot) = self.stack.last_mut() {
                        *slot = StackVal::LetBinding(*idx);
                    }
                    return;
                }
                // Existing handler:
                let val = self.stack.last().cloned().unwrap_or(StackVal::Unknown);
                if let Some(local) = self.locals.get_mut(*idx as usize) {
                    *local = val;
                }
            }

            // Global access (stack pointer etc.)
            WasmInstr::GlobalGet(0) => self.stack.push(StackVal::StackPtrRef),
            WasmInstr::GlobalGet(_) => self.stack.push(StackVal::Unknown),
            WasmInstr::GlobalSet(_) => {
                self.stack.pop();
            }

            // Call instructions - the core of lifting
            WasmInstr::Call(target_idx) => {
                if let Some(host_fn) = self.wasm_module.imports.get_by_index(*target_idx) {
                    // Determine how many args this host function expects
                    let host_type = self.wasm_module.get_func_type(*target_idx);
                    let num_args = host_type.map(|ft| ft.params.len()).unwrap_or(0);
                    let num_results = host_type.map(|ft| ft.results.len()).unwrap_or(0);

                    // Pop args from stack as raw StackVals first (preserves Val-encoding)
                    let mut raw_args: Vec<StackVal> = Vec::new();
                    for _ in 0..num_args {
                        raw_args.push(self.stack.pop().unwrap_or(StackVal::Unknown));
                    }
                    raw_args.reverse();

                    // 128-bit limb tracking (i128/u128 soft-arith reconstruction).
                    // `obj_to_*128_lo64/hi64` extract a limb of a 128-bit value;
                    // tag it with its source so a matching `(lo, hi)` pair can be
                    // re-paired (here by `obj_from_*128_pieces`, elsewhere by a
                    // soft-arith helper operand). This replaces the lossy lowering
                    // where lo and hi both collapsed to an identical `ValConvert`.
                    if host_fn.module == HostModule::Int {
                        match host_fn.name.as_str() {
                            "obj_to_i128_lo64" | "obj_to_u128_lo64" => {
                                let src = raw_args.into_iter().next().unwrap_or(StackVal::Unknown);
                                self.stack.push(StackVal::I128Limb {
                                    value: Box::new(src),
                                    hi: false,
                                });
                                return;
                            }
                            "obj_to_i128_hi64" | "obj_to_u128_hi64" => {
                                let src = raw_args.into_iter().next().unwrap_or(StackVal::Unknown);
                                self.stack.push(StackVal::I128Limb {
                                    value: Box::new(src),
                                    hi: true,
                                });
                                return;
                            }
                            // `obj_from_*128_pieces(hi, lo)` recomposes the value: if
                            // both args are limbs of the SAME source, recover it whole.
                            "obj_from_i128_pieces" | "obj_from_u128_pieces" => {
                                if let [
                                    StackVal::I128Limb {
                                        value: hv,
                                        hi: true,
                                    },
                                    StackVal::I128Limb {
                                        value: lv,
                                        hi: false,
                                    },
                                ] = raw_args.as_slice()
                                    && hv == lv
                                {
                                    self.stack.push((**hv).clone());
                                    return;
                                }
                                // else fall through to the generic ValConvert lowering.
                            }
                            _ => {}
                        }
                    }

                    // Try existing SorobanExpr-based path first (preserves TupleConstruct
                    // behavior for contracts that already work), then fall back to raw
                    // StackVal path which can decode Val-encoded BinOp args.
                    let args: Vec<SorobanExpr> = raw_args
                        .iter()
                        .map(|sv| {
                            stack_val_to_expr(
                                sv,
                                self.params,
                                self.registry,
                                Some(&self.frame_slots.borrow()),
                            )
                        })
                        .collect();
                    let (expr, is_struct_construct) = if let Some(e) =
                        self.try_lift_linear_memory_call(host_fn, &args)
                    {
                        (e, true)
                    } else if let Some(e) = self.try_lift_linear_memory_call_raw(host_fn, &raw_args)
                    {
                        (e, true)
                    } else {
                        (super::host_calls::lift_host_call(host_fn, args), false)
                    };

                    // Push result(s) onto stack
                    for _ in 0..num_results {
                        self.stack
                            .push(StackVal::HostCallResult(Box::new(expr.clone())));
                    }

                    // Struct constructs are value expressions, not side-effecting statements.
                    // They are consumed via the stack when used as arguments or return values.
                    if is_struct_construct {
                        self.found_host_calls = true;
                    } else {
                        // Only emit meaningful expressions
                        match &expr {
                            SorobanExpr::ValConvert { .. } => {} // Skip raw type conversions
                            SorobanExpr::RawHostCall { module, .. } if module == "Int" => {} // Skip int conversions
                            // obj_cmp is a pure comparison — result stays on the stack to
                            // participate in the subsequent i32.ne/i32.lt_s comparison.
                            // Emitting it as a statement would produce an orphaned
                            // `{ todo!("host call") };` before the if-block.
                            SorobanExpr::RawHostCall { function, .. } if function == "obj_cmp" => {
                                self.found_host_calls = true;
                            }
                            _ => {
                                self.stmts.push(SorobanStmt::Expr(expr));
                                self.found_host_calls = true;
                            }
                        }
                    }
                } else {
                    // Internal function call — attempt depth-limited inlining
                    let callee_type = self.wasm_module.get_func_type(*target_idx);
                    let num_args = callee_type.map(|ft| ft.params.len()).unwrap_or(0);
                    let num_results = callee_type.map(|ft| ft.results.len()).unwrap_or(0);

                    let mut args = Vec::new();
                    for _ in 0..num_args {
                        args.push(self.stack.pop().unwrap_or(StackVal::Unknown));
                    }
                    args.reverse();

                    // Save first arg for enum key constructor correction (used later
                    // if the inline result needs variant index remapping).
                    let first_arg_i32 = match args.first() {
                        Some(StackVal::I32(v)) => Some(*v),
                        _ => None,
                    };

                    // Enum key constructor: (i32) → i64 functions that construct
                    // a DataKey enum variant from a variant index. When the caller
                    // passes a constant i32, resolve the correct variant directly
                    // instead of inlining (which picks the wrong variant due to
                    // branch-sequential execution in the dispatch).
                    let did_key_construct = if let Some(variant_idx) = first_arg_i32 {
                        let variant_idx = variant_idx as usize;
                        self.wasm_module
                            .get_func_type(*target_idx)
                            .and_then(|ft| {
                                if ft.params.len() == 1
                                    && ft.params[0] == crate::wasm::ir::WasmType::I32
                                    && ft.results.len() == 1
                                    && ft.results[0] == crate::wasm::ir::WasmType::I64
                                    && function_calls_host_in_chain(
                                        self.wasm_module,
                                        *target_idx,
                                        HostModule::Buf,
                                        "symbol_new_from_linear_memory",
                                        3,
                                    )
                                {
                                    // Read string references from the function's body
                                    // to determine which union it constructs for.
                                    // The key constructor calls string helpers with
                                    // (ptr, len) pairs pointing to variant names in
                                    // the data section.
                                    let func_strings =
                                        extract_data_strings(self.wasm_module, *target_idx);

                                    // Match strings against union variant names
                                    let mut matched_variants: Option<Vec<String>> = None;
                                    for spec in self.registry.unions.values() {
                                        let variants: Vec<String> = spec
                                            .cases
                                            .iter()
                                            .filter_map(|c| match c {
                                                stellar_xdr::ScSpecUdtUnionCaseV0::VoidV0(v) => {
                                                    v.name.to_utf8_string().ok()
                                                }
                                                stellar_xdr::ScSpecUdtUnionCaseV0::TupleV0(t) => {
                                                    t.name.to_utf8_string().ok()
                                                }
                                            })
                                            .collect();
                                        if variant_idx < variants.len() {
                                            // Check if the function's strings match
                                            // this union's variant names
                                            let matches = !func_strings.is_empty()
                                                && variants
                                                    .iter()
                                                    .all(|v| func_strings.contains(v));
                                            if matches {
                                                matched_variants = Some(variants);
                                                break;
                                            }
                                        }
                                    }

                                    // Fallback: if no string match, try unambiguous
                                    if matched_variants.is_none() {
                                        let mut candidates: Vec<Vec<String>> = Vec::new();
                                        for spec in self.registry.unions.values() {
                                            let variants: Vec<String> = spec
                                                .cases
                                                .iter()
                                                .filter_map(|c| match c {
                                                    stellar_xdr::ScSpecUdtUnionCaseV0::VoidV0(
                                                        v,
                                                    ) => v.name.to_utf8_string().ok(),
                                                    stellar_xdr::ScSpecUdtUnionCaseV0::TupleV0(
                                                        t,
                                                    ) => t.name.to_utf8_string().ok(),
                                                })
                                                .collect();
                                            if variant_idx < variants.len() {
                                                candidates.push(variants);
                                            }
                                        }
                                        if candidates.len() == 1 {
                                            matched_variants = Some(candidates.remove(0));
                                        }
                                    }

                                    if let Some(variants) = matched_variants {
                                        let sym = SorobanExpr::SymbolLiteral(
                                            variants[variant_idx].clone(),
                                        );
                                        self.stack.push(StackVal::HostCallResult(Box::new(
                                            SorobanExpr::VecConstruct(vec![sym]),
                                        )));
                                        return Some(true);
                                    }
                                    None
                                } else {
                                    None
                                }
                            })
                            .is_some()
                    } else {
                        false
                    };

                    // Constant *descriptor-pointer* DataKey constructor: the variant
                    // index is a pointer to a 1-byte discriminant in static data
                    // rather than an immediate (the `did_key_construct` case above).
                    let did_key_construct = did_key_construct
                        || self.try_push_descriptor_key(*target_idx, first_arg_i32);

                    // *Frame-descriptor* DataKey constructor: the same `(i32) ->
                    // i64` ctor, but the descriptor row was built at runtime in
                    // the caller's frame (keyed variants — selector at `+0`,
                    // payload Vals at `+8`…). Folded by executing the ctor over
                    // the abstractly-known row.
                    let did_key_construct =
                        did_key_construct || self.try_fold_frame_descriptor_key(*target_idx, &args);

                    // Immediate-selector DataKey *dispatcher*: `(i64 selector, …)
                    // -> i64` br_table'ing over the selector (neither `(i32) ->
                    // i64` case above matches it). A constant selector resolves
                    // the key by micro-evaluating the dispatcher's own bytecode.
                    let did_key_construct =
                        did_key_construct || self.try_fold_datakey_dispatcher(*target_idx, &args);

                    // Sign-check-and-panic: functions like check_nonnegative_amount
                    // that compare a parameter against 0 and panic if negative.
                    // Emit the guard directly in the caller using the caller's arg values.
                    // The checked arg is typically the hi 64 bits of an i128, passed as a
                    // LetBinding from the i128 decode. Resolve it to the original Param
                    // so the output shows `if amount < 0` rather than an unbound local.
                    let did_inline = did_key_construct
                        || if let Some(check_local) =
                            detect_sign_check_function(self.wasm_module, *target_idx)
                        {
                            if let Some(checked_arg) = args.get(check_local as usize) {
                                let checked_expr = resolve_sign_check_arg(
                                    checked_arg,
                                    &args,
                                    self.params,
                                    self.registry,
                                    &self.frame_slots.borrow(),
                                );
                                self.stmts.push(SorobanStmt::If {
                                    condition: SorobanExpr::Lt(
                                        Box::new(checked_expr),
                                        Box::new(SorobanExpr::I64Literal(0)),
                                    ),
                                    then_body: vec![SorobanStmt::Expr(SorobanExpr::Panic)],
                                    else_body: Vec::new(),
                                });
                                self.found_host_calls = true;
                            }
                            true
                        }
                        // Special case: a function whose body is just `unreachable` is a
                        // `panic!()` wrapper generated by the compiler for `panic!("msg")` calls.
                        // Do NOT set found_host_calls=true here: panic-only functions are error paths
                        // (not meaningful host operations) and should not suppress the arithmetic fallback.
                        // Push Unknown for any return values so the stack stays consistent.
                        else if is_unreachable_only_function(self.wasm_module, *target_idx)
                            && num_results == 0
                        {
                            self.stmts.push(SorobanStmt::Expr(SorobanExpr::Panic));
                            true
                        } else if let Some(wrapper_info) =
                            detect_vec_new_wrapper(self.wasm_module, *target_idx)
                        {
                            // Detected a vec_new_from_linear_memory wrapper — handle tuple
                            // construction in the parent context where memory_stores are available.
                            let count = if let Some(hc) = wrapper_info.hardcoded_count {
                                Some(hc)
                            } else {
                                // 2-param wrapper: count is the second arg (raw i32 from stack)
                                args.get(1).and_then(|a| match a {
                                    StackVal::I32(v) => Some(*v as u32),
                                    _ => None,
                                })
                            };
                            if let Some(tuple_expr) =
                                count.and_then(|c| self.try_lift_tuple_construct_with_count(c))
                            {
                                if num_results > 0 {
                                    self.stack
                                        .push(StackVal::HostCallResult(Box::new(tuple_expr)));
                                }
                                self.found_host_calls = true;
                                true
                            } else {
                                false // Fall through to normal inlining
                            }
                        } else if let Some(construct_info) = detect_struct_construct_wrapper(
                            self.wasm_module,
                            self.registry,
                            *target_idx,
                            self.return_type_udt_name().as_deref(),
                        ) {
                            // Detected a struct construct wrapper (encode + map_new_from_linear_memory).
                            // Build StructConstruct directly from the caller's args, bypassing
                            // encoder inlining which corrupts values through branch-sequential execution.
                            if args.len() >= 2 {
                                let type_name = construct_info.type_name;
                                let fields: Vec<(String, SorobanExpr)> = construct_info
                                    .field_names
                                    .iter()
                                    .enumerate()
                                    .map(|(i, name)| {
                                        let val = args.get(i + 1).unwrap_or(&StackVal::Unknown);
                                        let expr = stack_val_to_expr(
                                            val,
                                            self.params,
                                            self.registry,
                                            Some(&self.frame_slots.borrow()),
                                        );
                                        (name.clone(), expr)
                                    })
                                    .collect();
                                let struct_expr =
                                    SorobanExpr::StructConstruct { type_name, fields };

                                // Store result at the result_ptr frame slot
                                if let StackVal::FrameSlot(id, base) =
                                    args.first().unwrap_or(&StackVal::Unknown)
                                {
                                    // result_ptr + 0 = error flag (0 = success)
                                    self.frame_slots
                                        .borrow_mut()
                                        .insert((*id, base.base), StackVal::I64(0));
                                    // result_ptr + 8 = the constructed struct Val
                                    self.frame_slots.borrow_mut().insert(
                                        (*id, base.base + 8),
                                        StackVal::HostCallResult(Box::new(struct_expr)),
                                    );
                                }
                            }
                            self.found_host_calls = true;
                            true
                        } else if detect_map_new_thunk(self.wasm_module, *target_idx) {
                            // Detected a generic map_new thunk:
                            // (i32 keys_ptr, i32 count, i32 vals_ptr, i32 count) -> i64
                            // Field values are already in memory at vals_ptr (written by caller).
                            // Extract keys_ptr and count from caller args, read field names from
                            // data section, then read field values from frame_slots at vals_ptr.
                            if args.len() >= 4 {
                                let keys_ptr = extract_u32_from_stack_val(
                                    args.first().unwrap_or(&StackVal::Unknown),
                                );
                                let count = extract_u32_from_stack_val(
                                    args.get(1).unwrap_or(&StackVal::Unknown),
                                );
                                let vals_ptr_arg = args.get(2).unwrap_or(&StackVal::Unknown);

                                if let (Some(keys_ptr), Some(count)) = (keys_ptr, count)
                                    && count > 0
                                    && let Some(field_names) = self
                                        .wasm_module
                                        .data_sections
                                        .read_string_slice_array(keys_ptr, count)
                                    && let Some(type_name) = find_type_by_field_names(
                                        self.registry,
                                        &field_names,
                                        self.return_type_udt_name().as_deref(),
                                    )
                                {
                                    // Try reading field values from frame_slots
                                    if let Some(values) =
                                        self.extract_vals_from_frame_slots(vals_ptr_arg, count)
                                    {
                                        let fields: Vec<(String, SorobanExpr)> =
                                            field_names.into_iter().zip(values).collect();
                                        let struct_expr =
                                            SorobanExpr::StructConstruct { type_name, fields };
                                        self.stack
                                            .push(StackVal::HostCallResult(Box::new(struct_expr)));
                                        self.found_host_calls = true;
                                        // Already pushed result; skip normal inlining
                                        return;
                                    }
                                }
                            }
                            // Fall through to normal inlining if resolution failed
                            false
                        } else if detect_map_unpack_thunk(self.wasm_module, *target_idx) {
                            // Detected a map_unpack_to_linear_memory thunk.
                            // Args: [map_val(i64), ...i32 args...] where i32 args contain
                            // keys_ptr (data section pointer >1024), vals_ptr (FrameSlot),
                            // and count (small I32). Param order varies across SDK versions,
                            // so classify args by type rather than fixed position.
                            if args.len() >= 4 {
                                // Classify i32 args by type
                                let mut keys_ptr: Option<u32> = None;
                                let mut count: Option<u32> = None;
                                let mut vals_ptr: Option<(u32, i32)> = None; // (frame_id, base)
                                for arg in args.iter().skip(1) {
                                    match arg {
                                        StackVal::I32(v) if *v > 1024 && keys_ptr.is_none() => {
                                            keys_ptr = Some(*v as u32);
                                        }
                                        StackVal::I32(v) if count.is_none() => {
                                            count = Some(*v as u32);
                                        }
                                        StackVal::FrameSlot(id, base) if vals_ptr.is_none() => {
                                            vals_ptr = Some((*id, base.base));
                                        }
                                        _ => {}
                                    }
                                }
                                if let (Some(keys_ptr), Some(count), Some((frame_id, base))) =
                                    (keys_ptr, count, vals_ptr)
                                    && let Some(field_names) = self
                                        .wasm_module
                                        .data_sections
                                        .read_string_slice_array(keys_ptr, count)
                                    && find_type_by_field_names(self.registry, &field_names, None)
                                        .is_some()
                                {
                                    let map_expr = stack_val_to_expr(
                                        &args[0],
                                        self.params,
                                        self.registry,
                                        Some(&self.frame_slots.borrow()),
                                    );
                                    for (i, name) in field_names.iter().enumerate() {
                                        let field_expr = SorobanExpr::FieldAccess {
                                            object: Box::new(map_expr.clone()),
                                            field: name.clone(),
                                        };
                                        self.frame_slots.borrow_mut().insert(
                                            (frame_id, base + (i as i32) * 8),
                                            StackVal::HostCallResult(Box::new(field_expr)),
                                        );
                                    }
                                    cov_mark::hit!(map_unpack_thunk_field_access);
                                }
                            }
                            self.found_host_calls = true;
                            true
                        } else if let Some(enum_info) = detect_enum_dispatch_wrapper(
                            self.wasm_module,
                            self.registry,
                            *target_idx,
                        ) {
                            // Detected an enum variant construction dispatch (br_table + symbol_new +
                            // vec_new). Build EnumConstruct directly from the caller's args, bypassing
                            // branch-sequential execution which corrupts variant construction.
                            let variant_idx = args
                                .first()
                                .and_then(|a| match a {
                                    StackVal::I32(v) => Some(*v as usize),
                                    _ => None,
                                })
                                .unwrap_or(0);
                            let variant_name = enum_info
                                .variants
                                .get(variant_idx)
                                .cloned()
                                .unwrap_or_else(|| enum_info.variants[0].clone());
                            let has_data = enum_info
                                .has_data
                                .get(variant_idx)
                                .copied()
                                .unwrap_or(false);

                            let fields = if has_data && args.len() >= 2 {
                                vec![stack_val_to_expr(
                                    &args[1],
                                    self.params,
                                    self.registry,
                                    Some(&self.frame_slots.borrow()),
                                )]
                            } else {
                                vec![]
                            };

                            let enum_expr = SorobanExpr::EnumConstruct {
                                type_name: enum_info.union_name,
                                variant: variant_name,
                                fields,
                            };

                            if num_results > 0 {
                                self.stack
                                    .push(StackVal::HostCallResult(Box::new(enum_expr)));
                            } else {
                                // Void-returning wrapper: store at result_ptr frame slot
                                if let Some(StackVal::FrameSlot(id, base)) = args.first() {
                                    self.frame_slots
                                        .borrow_mut()
                                        .insert((*id, base.base), StackVal::I64(0));
                                    self.frame_slots.borrow_mut().insert(
                                        (*id, base.base + 8),
                                        StackVal::HostCallResult(Box::new(enum_expr)),
                                    );
                                }
                            }
                            self.found_host_calls = true;
                            true
                        } else if num_results == 1
                            && args.is_empty()
                            && let Some(getter) = detect_fallible_value_getter(
                                self.wasm_module,
                                self.registry,
                                *target_idx,
                            )
                        {
                            // Value-returning fallible getter (issue #34
                            // tranche 6): the helper is proven to be
                            // `get(&KEY).unwrap_or_else(|| panic_with_error!(env, E))`
                            // preceded by proven instance TTL bumps.
                            // Reconstruct at the call site: TTL statements,
                            // then push the faithful get as the call's
                            // value — it flows to consumers (exported-fn
                            // tails typed by the signature, cross-contract
                            // invoke targets) instead of dying at the
                            // helper's internal block-result joins. The
                            // AddressObject tag pins `Address` explicitly
                            // (an invoke target must type-check as
                            // `&Address`); other tags leave the value type
                            // to inference from the consuming context. The
                            // tag guard itself is the SDK's TryFromVal
                            // marshalling trap, re-inserted on recompile —
                            // dropping it loses nothing.
                            for (threshold, extend_to) in &getter.instance_ttl_bumps {
                                self.stmts.push(SorobanStmt::Expr(
                                    SorobanExpr::ExtendInstanceAndCodeTtl {
                                        threshold: Box::new(SorobanExpr::U32Literal(*threshold)),
                                        extend_to: Box::new(SorobanExpr::U32Literal(*extend_to)),
                                    },
                                ));
                            }
                            let get_expr = SorobanExpr::StorageGet {
                                storage_type: getter.storage_type,
                                key: Box::new(getter.key.clone()),
                                unwrap: false,
                                on_missing: Some(Box::new(SorobanExpr::PanicWithError(Box::new(
                                    getter.error.clone(),
                                )))),
                            };
                            let value = if getter.tag == 77 {
                                // AddressObject
                                SorobanExpr::CastAs {
                                    value: Box::new(get_expr),
                                    target_type: "Address".to_string(),
                                }
                            } else {
                                get_expr
                            };
                            // Bind ONCE and push the binding, mirroring the
                            // bytecode's single read. Pushing the bare
                            // expression instead would clone it into every
                            // consumer — and a re-read receiver silently
                            // drops mutations (`.set` on a fresh temporary
                            // compiles via auto-mut-ref). On the immutable
                            // binding a mutator is a loud E0596; single-use
                            // sites are inlined back to the direct
                            // expression by the redundant-let pass.
                            let var_idx = self.locals.len() as u32;
                            self.locals.push(StackVal::LetBinding(var_idx));
                            self.stmts.push(SorobanStmt::Let {
                                name: format!("var_{var_idx}"),
                                mutable: false,
                                value,
                            });
                            self.stack.push(StackVal::LetBinding(var_idx));
                            self.found_host_calls = true;
                            cov_mark::hit!(fallible_value_getter_recovered);
                            true
                        } else if num_results == 1
                            && args.is_empty()
                            && let Some(getter) = detect_defaulting_collection_getter(
                                self.wasm_module,
                                self.registry,
                                *target_idx,
                            )
                        {
                            // Defaulting collection getter (issue #34
                            // tranche 6 map / tranche 7 vec):
                            // `get(&KEY).unwrap_or(C::new(&env))` — the
                            // empty-collection default is the helper's own
                            // proven `select` arm, not a fabrication. Same
                            // reconstruction as the fallible sibling: TTL
                            // statements + the get as the call's value.
                            for (threshold, extend_to) in &getter.instance_ttl_bumps {
                                self.stmts.push(SorobanStmt::Expr(
                                    SorobanExpr::ExtendInstanceAndCodeTtl {
                                        threshold: Box::new(SorobanExpr::U32Literal(*threshold)),
                                        extend_to: Box::new(SorobanExpr::U32Literal(*extend_to)),
                                    },
                                ));
                            }
                            // Bind once and push the binding (see the
                            // fallible sibling above): a per-consumer
                            // re-read would silently drop collection
                            // mutations.
                            let var_idx = self.locals.len() as u32;
                            self.locals.push(StackVal::LetBinding(var_idx));
                            self.stmts.push(SorobanStmt::Let {
                                name: format!("var_{var_idx}"),
                                mutable: false,
                                value: SorobanExpr::StorageGet {
                                    storage_type: getter.storage_type,
                                    key: Box::new(getter.key.clone()),
                                    unwrap: false,
                                    on_missing: Some(Box::new(SorobanExpr::CollectionNew(
                                        getter.collection_type.to_string(),
                                    ))),
                                },
                            });
                            self.stack.push(StackVal::LetBinding(var_idx));
                            self.found_host_calls = true;
                            cov_mark::hit!(defaulting_collection_getter_recovered);
                            true
                        } else if let Some(getter) = detect_fallible_struct_getter(
                            self.wasm_module,
                            self.registry,
                            *target_idx,
                        ) && let Some(StackVal::FrameSlot(out_id, out_base)) =
                            args.first()
                            && out_base.is_static()
                        {
                            // Fallible STRUCT getter (issue #34 tranche 5): the helper
                            // is proven to be `get::<_, T>(&KEY).unwrap_or(T { zeros })`
                            // for a two-field `{u128, u64}` struct, preceded by proven
                            // constant instance TTL bumps. Reconstruct it at ONE point:
                            // emit the TTL statements and a `let` binding of the
                            // defaulting get, seed the out slots as the binding's
                            // fields, and skip inlining entirely. Inlining this shape
                            // only yields an unresolvable husk (its internal
                            // default/decode joins collapse every out slot to Unknown),
                            // and the hybrid designs that raced seeds against husk
                            // splicing were measured failures (PR #44) — with no husk,
                            // the collapse heuristics see one coherent statement
                            // stream. A non-frame out-pointer falls through to generic
                            // inlining (today's behavior).
                            let (out_id, out_base) = (*out_id, out_base.base);
                            for (threshold, extend_to) in &getter.instance_ttl_bumps {
                                self.stmts.push(SorobanStmt::Expr(
                                    SorobanExpr::ExtendInstanceAndCodeTtl {
                                        threshold: Box::new(SorobanExpr::U32Literal(*threshold)),
                                        extend_to: Box::new(SorobanExpr::U32Literal(*extend_to)),
                                    },
                                ));
                            }
                            let zeros = SorobanExpr::StructConstruct {
                                type_name: getter.type_name.clone(),
                                fields: getter
                                    .spec_fields
                                    .iter()
                                    .map(|(name, ty)| {
                                        let zero = match ty {
                                            ScSpecTypeDef::U128 => SorobanExpr::U128Literal(0),
                                            _ => SorobanExpr::U64Literal(0),
                                        };
                                        (name.clone(), zero)
                                    })
                                    .collect(),
                            };
                            let var_idx = self.locals.len() as u32;
                            self.locals.push(StackVal::LetBinding(var_idx));
                            // The CastAs wrap is the reusable `get::<_, T>`
                            // turbofish vehicle (t2's pattern): if cleanup
                            // later demotes an unconsumed binding to a bare
                            // expression, the get keeps its value type
                            // (`unwrap_or(T { .. })` needs `T`, so the
                            // `Val`-annotating fallback pass must never
                            // claim it).
                            self.stmts.push(SorobanStmt::Let {
                                name: format!("var_{var_idx}"),
                                mutable: false,
                                value: SorobanExpr::CastAs {
                                    value: Box::new(SorobanExpr::StorageGet {
                                        storage_type: getter.storage_type,
                                        key: Box::new(getter.key.clone()),
                                        unwrap: false,
                                        on_missing: Some(Box::new(zeros)),
                                    }),
                                    target_type: getter.type_name.clone(),
                                },
                            });
                            // Reference the binding as `Local(N)` — the form
                            // every counting/substitution pass understands
                            // (`NamedLocal` references are invisible to
                            // `count_local_uses`, and the dead-store pass
                            // would demote the binding while its field
                            // seeds survive — unbound `var_N`).
                            let field = |name: &str| {
                                StackVal::HostCallResult(Box::new(SorobanExpr::FieldAccess {
                                    object: Box::new(SorobanExpr::Local(var_idx)),
                                    field: name.to_string(),
                                }))
                            };
                            // The proven out layout: u128 limbs at [0, 8], u64 at 16.
                            // Both limb slots tag the SAME field expression, so the
                            // existing (lo, hi) re-pair machinery reconstructs
                            // `var_N.<u128_field>` whole at every consumer.
                            let u128_val = field(&getter.u128_field);
                            let mut slots = self.frame_slots.borrow_mut();
                            slots.insert(
                                (out_id, out_base),
                                StackVal::I128Limb {
                                    value: Box::new(u128_val.clone()),
                                    hi: false,
                                },
                            );
                            slots.insert(
                                (out_id, out_base + 8),
                                StackVal::I128Limb {
                                    value: Box::new(u128_val),
                                    hi: true,
                                },
                            );
                            slots.insert((out_id, out_base + 16), field(&getter.u64_field));
                            drop(slots);
                            self.found_host_calls = true;
                            cov_mark::hit!(fallible_struct_getter_recovered);
                            true
                        } else if let Some(unpack_info) = detect_map_unpack_decode_wrapper(
                            self.wasm_module,
                            self.registry,
                            *target_idx,
                        ) {
                            // Detected a map_unpack_to_linear_memory + decode wrapper.
                            // Synthesize FieldAccess entries at the result frame positions,
                            // bypassing the problematic decode function inlining where
                            // branch-sequential execution corrupts locals.
                            //
                            // For 2-param wrappers (i32 result_ptr, i64 map_val): args[1]
                            // is the struct being unpacked. For multi-param wrappers (e.g.,
                            // (i32, i64, i64) where extra args construct a storage key
                            // internally): the struct is obtained inside the wrapper via
                            // storage get, so use UnknownVal as the object expression.
                            if args.len() >= 2 {
                                let callee_type = self.wasm_module.get_func_type(*target_idx);
                                let callee_param_count =
                                    callee_type.map(|ft| ft.params.len()).unwrap_or(0);
                                let struct_expr = if callee_param_count == 2 {
                                    stack_val_to_expr(
                                        &args[1],
                                        self.params,
                                        self.registry,
                                        Some(&self.frame_slots.borrow()),
                                    )
                                } else {
                                    // Multi-param wrapper: struct obtained via internal storage get.
                                    // Try to construct StorageGet with key from caller's extra args.
                                    self.build_storage_get_for_multi_param_wrapper(
                                        &unpack_info,
                                        &args[1..],
                                    )
                                };
                                if let StackVal::FrameSlot(id, base) =
                                    args.first().unwrap_or(&StackVal::Unknown)
                                {
                                    // result_ptr + 0 = error flag (0 = success)
                                    self.frame_slots
                                        .borrow_mut()
                                        .insert((*id, base.base), StackVal::I64(0));
                                    // result_ptr + 8*(i+1) = decoded native field value
                                    for (i, name) in unpack_info.field_names.iter().enumerate() {
                                        let field_expr = SorobanExpr::FieldAccess {
                                            object: Box::new(struct_expr.clone()),
                                            field: name.clone(),
                                        };
                                        self.frame_slots.borrow_mut().insert(
                                            (*id, base.base + 8 * (i as i32 + 1)),
                                            StackVal::HostCallResult(Box::new(field_expr)),
                                        );
                                    }
                                }
                            }
                            self.found_host_calls = true;
                            true
                        } else if let Some(unpack_info) =
                            detect_vec_unpack_wrapper(self.wasm_module, *target_idx)
                        {
                            // Detected a vec_unpack_to_linear_memory wrapper — synthesize
                            // FrameSlot entries so subsequent reads find parameter-derived values.
                            let count = if let Some(hc) = unpack_info.hardcoded_count {
                                Some(hc)
                            } else {
                                // 3-param wrapper: count is the third arg (raw i32)
                                args.get(2).and_then(|a| match a {
                                    StackVal::I32(v) => Some(*v as u32),
                                    _ => None,
                                })
                            };
                            if let (Some(count), Some(_vec_arg)) = (count, args.first()) {
                                // The first arg is the Vec param being unpacked
                                let vec_expr = stack_val_to_expr(
                                    &args[0],
                                    self.params,
                                    self.registry,
                                    Some(&self.frame_slots.borrow()),
                                );
                                // The second arg is the frame address
                                if let StackVal::FrameSlot(id, base) =
                                    args.get(1).unwrap_or(&StackVal::Unknown)
                                {
                                    for i in 0..count {
                                        let elem_expr = SorobanExpr::MethodCall {
                                            object: Box::new(vec_expr.clone()),
                                            method: "get".to_string(),
                                            args: vec![SorobanExpr::U32Literal(i)],
                                        };
                                        self.frame_slots.borrow_mut().insert(
                                            (*id, base.base + (i as i32) * 8),
                                            StackVal::HostCallResult(Box::new(elem_expr)),
                                        );
                                    }
                                }
                            }
                            // Push Unknown for any results (vec_unpack returns Void, but wrapper
                            // may have return values for type consistency)
                            for _ in 0..num_results {
                                self.stack.push(StackVal::Unknown);
                            }
                            true
                        } else if let Some(keyed_set_info) = detect_keyed_storage_set_wrapper(
                            self.wasm_module,
                            self.registry,
                            *target_idx,
                        ) {
                            // Detected a keyed storage set wrapper.
                            //
                            // Two sub-patterns:
                            // - Direct: args = (key_index, value), variant from first arg
                            // - Fixed-key: args = (value, ...), variant from hardcoded_variant_idx
                            let (variant_idx, value_arg_idx) =
                                if let Some(fixed_idx) = keyed_set_info.hardcoded_variant_idx {
                                    (Some(fixed_idx), 0)
                                } else {
                                    let idx = args.first().and_then(|a| match a {
                                        StackVal::I64(v) => Some(*v as usize),
                                        _ => None,
                                    });
                                    (idx, 1)
                                };

                            if let Some(variant_idx) = variant_idx {
                                let variant_name = keyed_set_info
                                    .variants
                                    .get(variant_idx)
                                    .cloned()
                                    .unwrap_or_else(|| keyed_set_info.variants[0].clone());
                                let has_data = keyed_set_info
                                    .has_data
                                    .get(variant_idx)
                                    .copied()
                                    .unwrap_or(false);

                                let value_expr = stack_val_to_expr(
                                    args.get(value_arg_idx).unwrap_or(&StackVal::Unknown),
                                    self.params,
                                    self.registry,
                                    Some(&self.frame_slots.borrow()),
                                );

                                let key_fields = if has_data {
                                    vec![value_expr.clone()]
                                } else {
                                    vec![]
                                };

                                let key_expr = SorobanExpr::EnumConstruct {
                                    type_name: keyed_set_info.union_name,
                                    variant: variant_name,
                                    fields: key_fields,
                                };

                                let set_expr = SorobanExpr::StorageSet {
                                    storage_type: keyed_set_info.storage_type,
                                    key: Box::new(key_expr),
                                    value: Box::new(value_expr),
                                };

                                self.stmts.push(SorobanStmt::Expr(set_expr));
                            }
                            self.found_host_calls = true;
                            true
                        } else if let Some(keyed_get_info) = detect_keyed_storage_get_wrapper(
                            self.wasm_module,
                            self.registry,
                            *target_idx,
                        ) {
                            // Detected a keyed storage GET wrapper.
                            // Same logic as keyed SET: resolve variant from key index
                            // arg, emit StorageGet with the correct enum key.
                            let (variant_idx, _key_arg_idx) =
                                if let Some(fixed_idx) = keyed_get_info.hardcoded_variant_idx {
                                    (Some(fixed_idx), 0)
                                } else {
                                    // First i64 arg is the key index
                                    let idx = args.iter().find_map(|a| match a {
                                        StackVal::I64(v) => Some(*v as usize),
                                        _ => None,
                                    });
                                    (idx, 0)
                                };

                            if let Some(variant_idx) = variant_idx {
                                if variant_idx < keyed_get_info.variants.len() {
                                    let variant_name = &keyed_get_info.variants[variant_idx];
                                    let has_data = keyed_get_info
                                        .has_data
                                        .get(variant_idx)
                                        .copied()
                                        .unwrap_or(false);

                                    let key_expr = SorobanExpr::EnumConstruct {
                                        type_name: keyed_get_info.union_name.clone(),
                                        variant: variant_name.clone(),
                                        fields: if has_data {
                                            vec![SorobanExpr::UnknownVal]
                                        } else {
                                            vec![]
                                        },
                                    };

                                    let get_expr = SorobanExpr::StorageGet {
                                        storage_type: keyed_get_info.storage_type,
                                        key: Box::new(key_expr),
                                        unwrap: true,
                                        on_missing: None,
                                    };

                                    // Push result to stack (for return value) or emit as Let
                                    if num_results > 0 {
                                        self.stack.push(StackVal::HostCallResult(Box::new(
                                            get_expr.clone(),
                                        )));
                                    } else {
                                        // Output-pointer pattern: emit as Let binding
                                        self.stmts.push(SorobanStmt::Let {
                                            name: format!("var_{}", variant_idx),
                                            mutable: false,
                                            value: get_expr.clone(),
                                        });
                                    }

                                    // Write result to frame_slots at the output pointer
                                    // location so subsequent I64Load resolves to the
                                    // StorageGet value instead of Unknown.
                                    if let Some(StackVal::FrameSlot(frame_id, base)) = args.first()
                                    {
                                        let result_val =
                                            StackVal::HostCallResult(Box::new(get_expr));
                                        let mut fs = self.frame_slots.borrow_mut();
                                        // Status = 1 (success) at offset 0
                                        fs.insert((*frame_id, base.base), StackVal::I64(1));
                                        // Value at offsets 8, 16, 24 (covers both single
                                        // value and i128 lo/hi patterns)
                                        fs.insert((*frame_id, base.base + 8), result_val.clone());
                                        fs.insert((*frame_id, base.base + 16), result_val.clone());
                                        fs.insert((*frame_id, base.base + 24), result_val);
                                    }
                                    self.found_host_calls = true;
                                    true
                                } else {
                                    false // variant index out of range
                                }
                            } else {
                                false // no constant key index
                            }
                        } else if let Some(allowance_info) = detect_spend_allowance_wrapper(
                            self.wasm_module,
                            self.registry,
                            *target_idx,
                        ) {
                            // Detected a spend_allowance helper.
                            //
                            // Args: [from_val, spender_val, amount_lo, amount_hi]
                            // Emit:
                            //   let allowance = get(&DataKey::Allowance(AllowanceDataKey { from, spender })).unwrap();
                            //   if allowance.amount < amount { panic!() }
                            //   set(&DataKey::Allowance(...), &AllowanceValue { amount: allowance.amount - amount, ... });

                            // Build key struct: AllowanceDataKey { from, spender }
                            let key_fields: Vec<(String, SorobanExpr)> = allowance_info
                                .key_field_names
                                .iter()
                                .enumerate()
                                .map(|(i, name)| {
                                    let val = stack_val_to_expr(
                                        args.get(i).unwrap_or(&StackVal::Unknown),
                                        self.params,
                                        self.registry,
                                        Some(&self.frame_slots.borrow()),
                                    );
                                    (name.clone(), val)
                                })
                                .collect();

                            let key_struct = SorobanExpr::StructConstruct {
                                type_name: allowance_info.key_type_name.clone(),
                                fields: key_fields,
                            };

                            let key_expr = SorobanExpr::EnumConstruct {
                                type_name: allowance_info.union_name,
                                variant: allowance_info.variant_name,
                                fields: vec![key_struct],
                            };

                            // Try to find the original i128 amount parameter by type.
                            let amount_expr = self
                                .params
                                .iter()
                                .find(|p| {
                                    matches!(p.type_def, ScSpecTypeDef::I128 | ScSpecTypeDef::U128)
                                })
                                .map(|p| SorobanExpr::Param(p.name.clone()))
                                .unwrap_or_else(|| {
                                    // Fallback: use the raw lo arg (3rd arg = index 2)
                                    stack_val_to_expr(
                                        args.get(2).unwrap_or(&StackVal::Unknown),
                                        self.params,
                                        self.registry,
                                        Some(&self.frame_slots.borrow()),
                                    )
                                });

                            // Emit: let allowance = get(&key).unwrap();
                            let get_expr = SorobanExpr::StorageGet {
                                storage_type: allowance_info.storage_type,
                                key: Box::new(key_expr.clone()),
                                unwrap: true,
                                on_missing: None,
                            };
                            self.stmts.push(SorobanStmt::Let {
                                name: "allowance".to_string(),
                                mutable: false,
                                value: get_expr,
                            });

                            // Emit: if allowance.amount < amount { panic!() }
                            self.stmts.push(SorobanStmt::If {
                                condition: SorobanExpr::Lt(
                                    Box::new(SorobanExpr::FieldAccess {
                                        object: Box::new(SorobanExpr::NamedLocal(
                                            "allowance".to_string(),
                                        )),
                                        field: "amount".to_string(),
                                    }),
                                    Box::new(amount_expr.clone()),
                                ),
                                then_body: vec![SorobanStmt::Expr(SorobanExpr::Panic)],
                                else_body: vec![],
                            });

                            // Build value struct: AllowanceValue { amount: allowance.amount - amount, field2: allowance.field2, ... }
                            let value_fields: Vec<(String, SorobanExpr)> = allowance_info
                                .value_field_names
                                .iter()
                                .map(|name| {
                                    let field_val = if name == "amount" {
                                        // amount: allowance.amount - amount
                                        SorobanExpr::Sub(
                                            Box::new(SorobanExpr::FieldAccess {
                                                object: Box::new(SorobanExpr::NamedLocal(
                                                    "allowance".to_string(),
                                                )),
                                                field: "amount".to_string(),
                                            }),
                                            Box::new(amount_expr.clone()),
                                        )
                                    } else {
                                        // Other fields: allowance.<field>
                                        SorobanExpr::FieldAccess {
                                            object: Box::new(SorobanExpr::NamedLocal(
                                                "allowance".to_string(),
                                            )),
                                            field: name.clone(),
                                        }
                                    };
                                    (name.clone(), field_val)
                                })
                                .collect();

                            let set_expr = SorobanExpr::StorageSet {
                                storage_type: allowance_info.storage_type,
                                key: Box::new(key_expr),
                                value: Box::new(SorobanExpr::StructConstruct {
                                    type_name: allowance_info.value_type_name,
                                    fields: value_fields,
                                }),
                            };

                            self.stmts.push(SorobanStmt::Expr(set_expr));
                            self.found_host_calls = true;
                            true
                        } else if let Some(write_info) = detect_write_allowance_wrapper(
                            self.wasm_module,
                            self.registry,
                            *target_idx,
                        ) {
                            // Detected a write_allowance helper.
                            //
                            // Args: [from_val, spender_val, amount_lo, amount_hi, expiration_ledger]
                            // Emit:
                            //   let key = DataKey::Allowance(AllowanceDataKey { from, spender });
                            //   set(&key, &AllowanceValue { amount, expiration_ledger });
                            //   extend_ttl(&key, expiration_ledger - sequence, expiration_ledger - sequence);

                            // Build key struct
                            let key_fields: Vec<(String, SorobanExpr)> = write_info
                                .key_field_names
                                .iter()
                                .enumerate()
                                .map(|(i, name)| {
                                    let val = stack_val_to_expr(
                                        args.get(i).unwrap_or(&StackVal::Unknown),
                                        self.params,
                                        self.registry,
                                        Some(&self.frame_slots.borrow()),
                                    );
                                    (name.clone(), val)
                                })
                                .collect();

                            let key_struct = SorobanExpr::StructConstruct {
                                type_name: write_info.key_type_name,
                                fields: key_fields,
                            };

                            let key_expr = SorobanExpr::EnumConstruct {
                                type_name: write_info.union_name,
                                variant: write_info.variant_name,
                                fields: vec![key_struct],
                            };

                            // Resolve amount and expiration_ledger params
                            let amount_expr = self
                                .params
                                .iter()
                                .find(|p| {
                                    matches!(p.type_def, ScSpecTypeDef::I128 | ScSpecTypeDef::U128)
                                })
                                .map(|p| SorobanExpr::Param(p.name.clone()))
                                .unwrap_or_else(|| {
                                    stack_val_to_expr(
                                        args.get(2).unwrap_or(&StackVal::Unknown),
                                        self.params,
                                        self.registry,
                                        Some(&self.frame_slots.borrow()),
                                    )
                                });

                            let exp_ledger_expr = self
                                .params
                                .iter()
                                .find(|p| {
                                    matches!(p.type_def, ScSpecTypeDef::U32) && p.name != "amount"
                                })
                                .map(|p| SorobanExpr::Param(p.name.clone()))
                                .unwrap_or_else(|| {
                                    stack_val_to_expr(
                                        args.get(4).unwrap_or(&StackVal::Unknown),
                                        self.params,
                                        self.registry,
                                        Some(&self.frame_slots.borrow()),
                                    )
                                });

                            // Build value struct: AllowanceValue { amount, expiration_ledger }
                            let value_fields: Vec<(String, SorobanExpr)> = write_info
                                .value_field_names
                                .iter()
                                .map(|name| {
                                    let field_val = if name == "amount" {
                                        amount_expr.clone()
                                    } else if name == "expiration_ledger" {
                                        exp_ledger_expr.clone()
                                    } else {
                                        SorobanExpr::UnknownVal
                                    };
                                    (name.clone(), field_val)
                                })
                                .collect();

                            // Emit: let key = DataKey::Allowance(...)
                            self.stmts.push(SorobanStmt::Let {
                                name: "allowance".to_string(),
                                mutable: false,
                                value: key_expr.clone(),
                            });

                            // Emit: set(&key, &AllowanceValue { amount, expiration_ledger })
                            let set_expr = SorobanExpr::StorageSet {
                                storage_type: write_info.storage_type,
                                key: Box::new(SorobanExpr::NamedLocal("allowance".to_string())),
                                value: Box::new(SorobanExpr::StructConstruct {
                                    type_name: write_info.value_type_name,
                                    fields: value_fields,
                                }),
                            };
                            self.stmts.push(SorobanStmt::Expr(set_expr));

                            // Emit: extend_ttl(&key, expiration_ledger - sequence, ...)
                            let ttl_diff = SorobanExpr::Sub(
                                Box::new(exp_ledger_expr),
                                Box::new(SorobanExpr::LedgerSequence),
                            );
                            let extend_expr = SorobanExpr::StorageExtendTtl {
                                storage_type: write_info.storage_type,
                                key: Box::new(SorobanExpr::NamedLocal("allowance".to_string())),
                                threshold: Box::new(ttl_diff.clone()),
                                extend_to: Box::new(ttl_diff),
                            };
                            self.stmts.push(SorobanStmt::Expr(extend_expr));

                            self.found_host_calls = true;
                            true
                        } else if let Some(balance_info) = detect_balance_helper_wrapper(
                            self.wasm_module,
                            self.registry,
                            *target_idx,
                        ) {
                            // Detected a receive_balance or spend_balance helper.
                            //
                            // Args: [addr_val, amount_lo, amount_hi]
                            // Emit: StorageSet { key: DataKey::Balance(addr), value: get ± amount }
                            let addr_expr = stack_val_to_expr(
                                args.first().unwrap_or(&StackVal::Unknown),
                                self.params,
                                self.registry,
                                Some(&self.frame_slots.borrow()),
                            );

                            // Try to find the original i128 amount parameter by type.
                            let amount_expr = self
                                .params
                                .iter()
                                .find(|p| {
                                    matches!(p.type_def, ScSpecTypeDef::I128 | ScSpecTypeDef::U128)
                                })
                                .map(|p| SorobanExpr::Param(p.name.clone()))
                                .unwrap_or_else(|| {
                                    // Fallback: use the raw lo arg
                                    stack_val_to_expr(
                                        args.get(1).unwrap_or(&StackVal::Unknown),
                                        self.params,
                                        self.registry,
                                        Some(&self.frame_slots.borrow()),
                                    )
                                });

                            let key_expr = SorobanExpr::EnumConstruct {
                                type_name: balance_info.union_name,
                                variant: balance_info.variant_name,
                                fields: vec![addr_expr.clone()],
                            };

                            let get_expr = SorobanExpr::StorageGet {
                                storage_type: balance_info.storage_type,
                                key: Box::new(key_expr.clone()),
                                unwrap: true,
                                on_missing: None,
                            };

                            let new_balance = if balance_info.is_receive {
                                SorobanExpr::Add(Box::new(get_expr), Box::new(amount_expr))
                            } else {
                                SorobanExpr::Sub(Box::new(get_expr), Box::new(amount_expr))
                            };

                            let set_expr = SorobanExpr::StorageSet {
                                storage_type: balance_info.storage_type,
                                key: Box::new(key_expr),
                                value: Box::new(new_balance),
                            };

                            self.stmts.push(SorobanStmt::Expr(set_expr));
                            self.found_host_calls = true;
                            true
                        } else if let Some(intr) =
                            detect_i128_intrinsic(self.wasm_module, *target_idx)
                            && let Some(handled) = self.try_lower_i128_intrinsic(&intr, &args)
                        {
                            // i128/u128 soft-arith helper: lower to clean `Mul`/`Div`
                            // and write the result (as limb pair) back to the result
                            // pointer's frame slot, so chained helpers compose instead
                            // of inlining into limb-soup `todo!`s.
                            handled
                        } else if let Some(handled) =
                            self.try_lower_result_unwrap_pack(*target_idx, &args, num_results)
                        {
                            // `Result<i128,E>::unwrap`-and-pack helper consuming a
                            // frame slot that already holds a reconstructed i128
                            // (from a checked-arith composite): return that value
                            // directly instead of inlining the deep unwrap chain.
                            handled
                        } else if let Some(handled) =
                            self.try_lower_symbol_builder(*target_idx, &args)
                        {
                            // `Symbol::new(&env, "literal")` builder whose encoder sits
                            // past the inline depth limit: recover the symbol from the
                            // static `(ptr, len)` string args and write it to the result
                            // pointer, instead of degrading to `todo!`.
                            handled
                        } else if let Some(handled) =
                            self.try_lower_option_decode(*target_idx, &args)
                        {
                            // SDK `Option<u32>` decode of a `Vec::first_index_of`
                            // result: recover the `.unwrap()` value and fold the tag
                            // `br_table` to the proven-live `Some` arm, instead of
                            // degrading the tag to `UnknownVal` (which discards the
                            // match and renders `todo!("unknown value")`).
                            handled
                        } else if self.inline_depth < MAX_INLINE_CALL_DEPTH {
                            // Observe a fallible storage-get helper before inlining
                            // loses its error code + value to a husk; the recorded
                            // info rebuilds `.ok_or(..)` in `lift_function_body`.
                            self.note_fallible_storage_get(*target_idx, &args);
                            // Check if this is a load-struct wrapper BEFORE inlining.
                            // Save the output pointer info for post-inline gap filling.
                            let output_frame_slot = match args.first() {
                                Some(StackVal::FrameSlot(id, base)) => Some((*id, base.base)),
                                _ => None,
                            };
                            let load_struct_info = if output_frame_slot.is_some() {
                                detect_load_struct_wrapper(
                                    self.wasm_module,
                                    self.registry,
                                    *target_idx,
                                )
                            } else {
                                None
                            };
                            // The 2nd argument of a void out-pointer helper is
                            // the operand a pure decode helper converts —
                            // captured before `args` moves into the inline
                            // (issue #34 t2, `seed_decode_helper_result`).
                            let decode_operand = args.get(1).cloned();
                            let mut inline_result = lift_inline_call(
                                self.wasm_module,
                                self.registry,
                                *target_idx,
                                args,
                                self.inline_depth,
                                Rc::clone(&self.frame_slots),
                                Rc::clone(&self.next_frame_id),
                                Rc::clone(&self.slot_write_log),
                            );
                            // Always propagate memory stores from inlined calls — helper
                            // functions may store Val-encoded values to memory without
                            // making host calls, and these stores are consumed by later
                            // map_new_from_linear_memory struct construction calls.
                            self.memory_stores.extend(inline_result.memory_stores);
                            // After inlining a load-struct wrapper, fill in any output
                            // frame slots that remain Unknown (due to BrIf child local
                            // propagation loss per lesson #35). Slots that inlining
                            // successfully resolved are left untouched.
                            if let (Some(load_info), Some((id, base))) =
                                (&load_struct_info, output_frame_slot)
                            {
                                let storage_type =
                                    load_info.storage_type.unwrap_or(StorageType::Instance);
                                // Use the wrapper's own proven constant key when
                                // its body reads exactly one (issue #34 t3);
                                // otherwise the honest `todo!()` key as before.
                                let key = load_info
                                    .const_key
                                    .clone()
                                    .unwrap_or(SorobanExpr::UnknownVal);
                                let struct_expr = SorobanExpr::StorageGet {
                                    storage_type,
                                    key: Box::new(key),
                                    unwrap: true,
                                    on_missing: None,
                                };
                                let slots = self.frame_slots.borrow();
                                let unknown_offsets: Vec<(i32, String)> = load_info
                                    .offset_to_field
                                    .iter()
                                    .filter(|(offset, _)| {
                                        match slots.get(&(id, base + offset)) {
                                            None
                                            | Some(StackVal::Unknown)
                                            | Some(StackVal::I64(0)) => true,
                                            // Val-encoded void (TAG_VOID=2) is also Unknown
                                            Some(StackVal::I64(2)) => true,
                                            _ => false,
                                        }
                                    })
                                    .cloned()
                                    .collect();
                                drop(slots);
                                if !unknown_offsets.is_empty() {
                                    self.found_host_calls = true;
                                }
                                for (offset, name) in &unknown_offsets {
                                    let field_expr = SorobanExpr::FieldAccess {
                                        object: Box::new(struct_expr.clone()),
                                        field: name.clone(),
                                    };
                                    self.frame_slots.borrow_mut().insert(
                                        (id, base + offset),
                                        StackVal::HostCallResult(Box::new(field_expr)),
                                    );
                                }
                            }
                            // Generic sret modeling: a void helper that received a
                            // result_ptr and produced a cross-contract call result
                            // (left at result_ptr+8) but no usable discriminant at
                            // result_ptr+0. Seed +0 with the call's Result discriminant
                            // so a later `i32.load; br_table` reconstructs
                            // `match <call> { Ok(..) => .., Err(..) => .. }` and its
                            // return path instead of dropping the whole dispatch.
                            if num_results == 0
                                && let Some((id, base)) = output_frame_slot
                            {
                                // Precise marker first (br_table on Ok/Err)…
                                self.model_sret_discriminant(id, base);
                                // …then the success-status seed (br_if-guard pattern),
                                // which only fires when the slot is still unmodeled…
                                self.seed_sret_success_status(id, base, *target_idx);
                                // …then the defaulting-u128-getter seed (issue #34
                                // tranche 2): its `[lo@0, hi@8]` layout has NO
                                // discriminant, so it must be recognized BEFORE
                                // the option-decode seed would stamp `+0` with a
                                // disc marker that is really the lo limb.
                                let defaulting_seeded =
                                    detect_defaulting_u128_getter(self.wasm_module, *target_idx)
                                        && match inline_result.content.as_mut() {
                                            Some((inlined_stmts, _)) => self
                                                .seed_defaulting_u128_getter(
                                                    id,
                                                    base,
                                                    inlined_stmts,
                                                ),
                                            None => false,
                                        };
                                // …then the pure TryFromVal decode-helper seed
                                // (issue #34 t2): payload slots = decode(operand).
                                if !defaulting_seeded
                                    && let Some(class) = detect_tryfromval_decode_helper(
                                        self.wasm_module,
                                        *target_idx,
                                    )
                                    && let Some(operand) = decode_operand.as_ref()
                                {
                                    self.seed_decode_helper_result(id, base, class, operand);
                                }
                                // …then the storage-decode Option seed (issue #35),
                                // for the fallible has+get wrapper class (again only
                                // when the slot is still unmodeled).
                                let option_seeded = !defaulting_seeded
                                    && self.seed_option_decode_status(id, base, *target_idx);
                                // A freshly-recognized option-decode wrapper also
                                // left the loaded value at `+8` — link it to the
                                // inlined get's binding (issue #34 slice).
                                if option_seeded
                                    && let Some((inlined_stmts, _)) = inline_result.content.as_mut()
                                {
                                    self.link_option_decode_value(
                                        id,
                                        base,
                                        *target_idx,
                                        inlined_stmts,
                                    );
                                }
                                if *DBG_SLOTMISS {
                                    let slots = self.frame_slots.borrow();
                                    let disc = slots.get(&(id, base));
                                    if matches!(disc, None | Some(StackVal::Unknown)) {
                                        eprintln!(
                                            "[UNMODELED_OUTPTR] helper={} frame={} base={} disc={:?} val8={:?}",
                                            target_idx,
                                            id,
                                            base,
                                            disc.map(std::mem::discriminant),
                                            slots.get(&(id, base + 8)).map(std::mem::discriminant),
                                        );
                                    }
                                }
                            }
                            if let Some((inlined_stmts, return_expr)) = inline_result.content {
                                // Checked-arith composite husk drop (all-or-nothing): a void
                                // helper (e.g. Soroswap's `quote`/`get_amount_*` checked-i128
                                // math) whose only meaningful effect is the i128 result it left
                                // in the output frame slot, and whose inlined body is pure
                                // arithmetic + error-path husks (Result-discriminant guards,
                                // overflow panics — no storage/event/auth/invoke side effects),
                                // faithfully reduces to just that value. Drop the husks so the
                                // caller's pack/return reads a clean expression instead of a
                                // control-flow-soup body. Fires only when the result slot holds
                                // a fully-recovered i128 (no `UnknownVal`) AND nothing real was
                                // dropped, so it can never emit a misleading partial.
                                let result_layout = output_frame_slot
                                    .filter(|_| num_results == 0)
                                    .and_then(|(id, base)| self.clean_i128_result_layout(id, base));
                                let dropped_husks = result_layout.is_some()
                                    && stmts_are_pure_arith_husks(&inlined_stmts);
                                if dropped_husks {
                                    // For the checked `Result<i128,E>` layout, seed the
                                    // output discriminant `Ok(0)` so the consuming
                                    // `Result::unwrap` (e.g. Soroswap's `call 98`) folds
                                    // to its value-producing arm instead of emitting the
                                    // Err husk. The composite writes `0` on success, which
                                    // matches the unwrap's `if disc != 0 { Err }` guard.
                                    if let (Some((id, base)), Some((8, _))) =
                                        (output_frame_slot, result_layout)
                                    {
                                        self.frame_slots
                                            .borrow_mut()
                                            .insert((id, base), StackVal::I64(0));
                                    }
                                } else {
                                    self.stmts.extend(inlined_stmts);
                                }
                                if num_results > 0 {
                                    let rv = return_expr
                                        .map(|e| StackVal::HostCallResult(Box::new(e)))
                                        .unwrap_or(StackVal::Unknown);
                                    for _ in 0..num_results {
                                        self.stack.push(rv.clone());
                                    }
                                }
                                self.found_host_calls = true;
                                true
                            } else if let Some(stack_result) =
                                inline_result.stack_result.filter(|_| num_results > 0)
                            {
                                // No host calls — not worth inlining as statements.
                                // But the inline computed a stack result (e.g., Val-encoding
                                // wrapper with constant args). Use it instead of Unknown.
                                let mut rv = stack_result;

                                // Fix enum key constructor results: when an (i32) → i64
                                // function returns VecConstruct([SymbolLiteral]) and the
                                // caller passed a constant i32 arg, verify the symbol
                                // against the registry's variant order. Branch-sequential
                                // execution in the inlined br_table dispatch may pick the
                                // wrong variant (last arm wins instead of the indexed arm).
                                if let StackVal::HostCallResult(ref expr) = rv
                                    && let SorobanExpr::VecConstruct(elems) = expr.as_ref()
                                    && elems.len() == 1
                                    && let SorobanExpr::SymbolLiteral(sym) = &elems[0]
                                {
                                    // Find which i32 constant the caller passed
                                    if let Some(idx) = first_arg_i32 {
                                        let idx = idx as usize;
                                        // Find a union with this symbol as a variant
                                        if let Some((union_name, _)) =
                                            self.registry.find_union_variant(sym)
                                            && let Some(union_spec) =
                                                self.registry.get_union(&union_name)
                                        {
                                            // Get the variant at the caller's index
                                            let variants: Vec<String> = union_spec
                                                .cases
                                                .iter()
                                                .filter_map(|c| match c {
                                                    stellar_xdr::ScSpecUdtUnionCaseV0::VoidV0(
                                                        v,
                                                    ) => v.name.to_utf8_string().ok(),
                                                    stellar_xdr::ScSpecUdtUnionCaseV0::TupleV0(
                                                        t,
                                                    ) => t.name.to_utf8_string().ok(),
                                                })
                                                .collect();
                                            if idx < variants.len() && variants[idx] != *sym {
                                                rv = StackVal::HostCallResult(Box::new(
                                                    SorobanExpr::VecConstruct(vec![
                                                        SorobanExpr::SymbolLiteral(
                                                            variants[idx].clone(),
                                                        ),
                                                    ]),
                                                ));
                                            }
                                        }
                                    }
                                }

                                for _ in 0..num_results {
                                    self.stack.push(rv.clone());
                                }
                                true
                            } else {
                                false
                            }
                        } else {
                            false
                        };

                    if !did_inline {
                        for _ in 0..num_results {
                            self.stack.push(StackVal::Unknown);
                        }
                    }
                }
            }

            // Arithmetic
            WasmInstr::I64Add | WasmInstr::I32Add => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    // Constant fold when both operands are known
                    (StackVal::I32(x), StackVal::I32(y)) => {
                        self.stack.push(StackVal::I32(x.wrapping_add(*y)));
                    }
                    (StackVal::I64(x), StackVal::I64(y)) => {
                        self.stack.push(StackVal::I64(x.wrapping_add(*y)));
                    }
                    // FrameSlot + constant offset
                    (StackVal::FrameSlot(id, base), StackVal::I32(delta)) => {
                        self.stack
                            .push(StackVal::FrameSlot(*id, base.shift(*delta)));
                    }
                    (StackVal::I32(delta), StackVal::FrameSlot(id, base)) => {
                        self.stack
                            .push(StackVal::FrameSlot(*id, base.shift(*delta)));
                    }
                    // FrameSlot + (coeff * loop_index): a dynamic, loop-indexed
                    // address. Attach a symbolic offset term so a matching indexed
                    // load can resolve it via `dynamic_slots`.
                    (StackVal::FrameSlot(id, base), other)
                        if base.is_static() && affine_index_term(other).is_some() =>
                    {
                        let term = affine_index_term(other);
                        self.stack.push(StackVal::FrameSlot(
                            *id,
                            SlotOffset {
                                base: base.base,
                                term,
                            },
                        ));
                    }
                    (other, StackVal::FrameSlot(id, base))
                        if base.is_static() && affine_index_term(other).is_some() =>
                    {
                        let term = affine_index_term(other);
                        self.stack.push(StackVal::FrameSlot(
                            *id,
                            SlotOffset {
                                base: base.base,
                                term,
                            },
                        ));
                    }
                    _ => self
                        .stack
                        .push(StackVal::BinOp(Box::new(a), BinOper::Add, Box::new(b))),
                }
            }
            WasmInstr::I64Sub | WasmInstr::I32Sub => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    // Constant fold when both operands are known
                    (StackVal::I32(x), StackVal::I32(y)) => {
                        self.stack.push(StackVal::I32(x.wrapping_sub(*y)));
                    }
                    (StackVal::I64(x), StackVal::I64(y)) => {
                        self.stack.push(StackVal::I64(x.wrapping_sub(*y)));
                    }
                    // StackPtrRef - K = FrameBase(K): the frame allocation pattern
                    (StackVal::StackPtrRef, StackVal::I32(k)) => {
                        self.stack.push(StackVal::FrameBase(*k));
                    }
                    // FrameSlot arithmetic
                    (StackVal::FrameSlot(id, base), StackVal::I32(delta)) => {
                        self.stack
                            .push(StackVal::FrameSlot(*id, base.shift(-*delta)));
                    }
                    (StackVal::I32(delta), StackVal::FrameSlot(id, base)) => {
                        self.stack.push(StackVal::FrameSlot(
                            *id,
                            SlotOffset {
                                base: *delta - base.base,
                                term: base.term,
                            },
                        ));
                    }
                    _ => self
                        .stack
                        .push(StackVal::BinOp(Box::new(a), BinOper::Sub, Box::new(b))),
                }
            }
            WasmInstr::I64Mul | WasmInstr::I32Mul => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    (StackVal::I32(x), StackVal::I32(y)) => {
                        self.stack.push(StackVal::I32(x.wrapping_mul(*y)));
                    }
                    (StackVal::I64(x), StackVal::I64(y)) => {
                        self.stack.push(StackVal::I64(x.wrapping_mul(*y)));
                    }
                    _ => self
                        .stack
                        .push(StackVal::BinOp(Box::new(a), BinOper::Mul, Box::new(b))),
                }
            }

            // Comparison
            WasmInstr::I32Eq => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                if let (Some(av), Some(bv)) = (as_i32_const(&a), as_i32_const(&b)) {
                    self.stack.push(StackVal::I32(if av == bv { 1 } else { 0 }));
                } else {
                    self.stack
                        .push(StackVal::Compare(Box::new(a), CmpOp::Eq, Box::new(b)));
                }
            }
            WasmInstr::I64Eq => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.stack
                    .push(StackVal::Compare(Box::new(a), CmpOp::Eq, Box::new(b)));
            }
            WasmInstr::I32Ne | WasmInstr::I64Ne => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.stack
                    .push(StackVal::Compare(Box::new(a), CmpOp::Ne, Box::new(b)));
            }
            WasmInstr::I32LtS | WasmInstr::I64LtS => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.stack
                    .push(StackVal::Compare(Box::new(a), CmpOp::LtS, Box::new(b)));
            }
            WasmInstr::I32LtU | WasmInstr::I64LtU => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.stack
                    .push(StackVal::Compare(Box::new(a), CmpOp::LtU, Box::new(b)));
            }
            WasmInstr::I32GtS | WasmInstr::I64GtS => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.stack
                    .push(StackVal::Compare(Box::new(a), CmpOp::GtS, Box::new(b)));
            }
            WasmInstr::I32GtU | WasmInstr::I64GtU => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                // Constant-fold when both operands are known. This enables
                // Val-encoding wrappers (e.g., u64-to-Val with threshold check)
                // to fold their fast-path comparison to a constant, allowing the
                // br_if handler to eliminate the dead slow-path branch.
                if let (Some(av), Some(bv)) = (to_u64(&a), to_u64(&b)) {
                    self.stack.push(StackVal::I32(if av > bv { 1 } else { 0 }));
                } else {
                    self.stack
                        .push(StackVal::Compare(Box::new(a), CmpOp::GtU, Box::new(b)));
                }
            }
            WasmInstr::I32LeS | WasmInstr::I64LeS => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.stack
                    .push(StackVal::Compare(Box::new(a), CmpOp::LeS, Box::new(b)));
            }
            WasmInstr::I32LeU | WasmInstr::I64LeU => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.stack
                    .push(StackVal::Compare(Box::new(a), CmpOp::LeU, Box::new(b)));
            }
            WasmInstr::I32GeS | WasmInstr::I64GeS => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.stack
                    .push(StackVal::Compare(Box::new(a), CmpOp::GeS, Box::new(b)));
            }
            WasmInstr::I32GeU | WasmInstr::I64GeU => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.stack
                    .push(StackVal::Compare(Box::new(a), CmpOp::GeU, Box::new(b)));
            }
            WasmInstr::I32Eqz | WasmInstr::I64Eqz => {
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                if let Some(v) = to_u64(&a) {
                    self.stack.push(StackVal::I32(if v == 0 { 1 } else { 0 }));
                } else {
                    self.stack.push(StackVal::Eqz(Box::new(a)));
                }
            }

            // Bitwise - constant fold when both operands are known
            WasmInstr::I64Shl => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (to_u64(&a), to_u64(&b)) {
                    (Some(av), Some(bv)) => {
                        self.stack.push(StackVal::I64((av << (bv & 63)) as i64))
                    }
                    // Small shifts (1-3) on Params are SDK multiplication optimizations.
                    // Only apply to Params — non-Params may be Val-encode intermediates.
                    (_, Some(n)) if (1..=3).contains(&n) && matches!(a, StackVal::Param(_)) => {
                        self.stack.push(StackVal::BinOp(
                            Box::new(a),
                            BinOper::Mul,
                            Box::new(StackVal::I64(1i64 << n)),
                        ));
                    }
                    // Track as BinOp so strip_val_encode can later remove the (inner << N) part.
                    _ => self
                        .stack
                        .push(StackVal::BinOp(Box::new(a), BinOper::Shl, Box::new(b))),
                }
            }
            WasmInstr::I64ShrU => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (to_u64(&a), to_u64(&b)) {
                    (Some(av), Some(bv)) => {
                        self.stack.push(StackVal::I64((av >> (bv & 63)) as i64))
                    }
                    // Shift by exactly 32: Val-decode that strips `(inner << 32) | tag` → `inner`.
                    // For Params this just returns the Param unchanged (they are the Rust-level value).
                    (_, Some(32)) => self.stack.push(strip_val_encode(a)),
                    // Shift by exactly 31 on a Param: Val-encode of `param * 2`.
                    // U32Val = (raw << 32) | 4, so (raw << 32 | 4) >> 31 = raw << 1 = raw * 2.
                    // This is how `b *= 2` gets compiled for u32 parameters.
                    (_, Some(31)) if matches!(a, StackVal::Param(_)) => {
                        self.stack.push(StackVal::BinOp(
                            Box::new(a),
                            BinOper::Mul,
                            Box::new(StackVal::I64(2)),
                        ));
                    }
                    // Preserve Param identity through other shifts (e.g., >> 8 for U64Small).
                    _ if matches!(a, StackVal::Param(_)) => self.stack.push(a),
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I64Or => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (to_u64(&a), to_u64(&b)) {
                    (Some(av), Some(bv)) => self.stack.push(StackVal::I64((av | bv) as i64)),
                    // Track as BinOp so strip_val_encode can later remove the `| tag` part.
                    _ => self
                        .stack
                        .push(StackVal::BinOp(Box::new(a), BinOper::Or, Box::new(b))),
                }
            }
            WasmInstr::I64And => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (to_u64(&a), to_u64(&b)) {
                    (Some(av), Some(bv)) => self.stack.push(StackVal::I64((av & bv) as i64)),
                    // Param/HostCallResult & val-preserving-mask: mask clears tag bits
                    // but keeps the value field. This is inline Val arithmetic (e.g., v+1
                    // encoded as (v & ~3) + (1<<32)). Pass the value through.
                    (_, Some(mask))
                        if matches!(a, StackVal::Param(_) | StackVal::HostCallResult(_))
                            && (mask & 0xFFFFFFFF_00000000 == 0xFFFFFFFF_00000000) =>
                    {
                        self.stack.push(a);
                    }
                    (Some(mask), _)
                        if matches!(b, StackVal::Param(_) | StackVal::HostCallResult(_))
                            && (mask & 0xFFFFFFFF_00000000 == 0xFFFFFFFF_00000000) =>
                    {
                        self.stack.push(b);
                    }
                    // Val-space validation masks: mask preserves the Val tag byte and
                    // narrows the value field (e.g., 0x1F_00000004 validates decimal < 32
                    // for U32Val). Pass through the Param — the AND is range validation,
                    // not computation. Guards: mask > 0xFF (excludes dispatch preamble
                    // tag extraction & 0xFF) and low byte is a known Val tag.
                    (_, Some(mask))
                        if matches!(a, StackVal::Param(_))
                            && mask > 0xFF
                            && is_small_val_tag(mask & 0xFF) =>
                    {
                        cov_mark::hit!(i64and_val_mask_passthrough);
                        self.stack.push(a);
                    }
                    (Some(mask), _)
                        if matches!(b, StackVal::Param(_))
                            && mask > 0xFF
                            && is_small_val_tag(mask & 0xFF) =>
                    {
                        cov_mark::hit!(i64and_val_mask_passthrough);
                        self.stack.push(b);
                    }
                    // Tag extraction: `v & 0xFF` keeps only the Val tag byte. Track it as
                    // a BinOp so recognize_val_shape / stack_val_to_expr can lift it to a
                    // tag-of expression (e.g. `v.get_tag()`). Disjoint from the `mask > 0xFF`
                    // val-mask passthrough above. The non-constant guard avoids re-wrapping
                    // a value that the const-fold arm should have already handled.
                    //
                    // Only at the top level (inline_depth == 0): inside inlined SDK
                    // unpack helpers, the same `& 0xFF` checks gate a success/error
                    // status flag that the caller constant-folds to reach the happy
                    // path. Recognizing them there turns the flag into a live branch
                    // and drops the helper's result, so keep the old Unknown behavior.
                    (_, Some(0xFF))
                        if self.inline_depth == 0
                            && !matches!(a, StackVal::I32(_) | StackVal::I64(_)) =>
                    {
                        self.stack.push(StackVal::BinOp(
                            Box::new(a),
                            BinOper::And,
                            Box::new(StackVal::I64(0xFF)),
                        ));
                    }
                    (Some(0xFF), _)
                        if self.inline_depth == 0
                            && !matches!(b, StackVal::I32(_) | StackVal::I64(_)) =>
                    {
                        self.stack.push(StackVal::BinOp(
                            Box::new(b),
                            BinOper::And,
                            Box::new(StackVal::I64(0xFF)),
                        ));
                    }
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I32ShrU => {
                // Right-shift on a Param is the typical pattern for extracting an enum
                // discriminant from a Soroban Val-encoded parameter (e.g. U32Val >> 8).
                // Preserve the Param identity so match scrutinee shows the parameter name.
                let shift = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &shift) {
                    (StackVal::Param(_), _) => self.stack.push(a),
                    (StackVal::I32(x), StackVal::I32(y)) => {
                        self.stack
                            .push(StackVal::I32((*x as u32 >> (*y as u32 & 31)) as i32));
                    }
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I32And => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (to_u64(&a), to_u64(&b)) {
                    (Some(av), Some(bv)) => self
                        .stack
                        .push(StackVal::I32((av as u32 & bv as u32) as i32)),
                    // AND with 0xFFFFFFFE (-2 as i32) clears the low bit — a no-op on even values.
                    // The compiler generates this after >> 31 to clean up the multiplication-by-2
                    // pattern `(u32_val << 32 | tag) >> 31 = u32_val * 2`.
                    (_, Some(0xFFFFFFFE)) => self.stack.push(a),
                    (Some(0xFFFFFFFE), _) => self.stack.push(b),
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I32Shl => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (to_u64(&a), to_u64(&b)) {
                    (Some(av), Some(bv)) => {
                        self.stack
                            .push(StackVal::I32(((av as u32) << (bv as u32 & 31)) as i32));
                    }
                    (_, Some(n)) if n <= 3 => {
                        self.stack.push(StackVal::BinOp(
                            Box::new(a),
                            BinOper::Mul,
                            Box::new(StackVal::I32(1i32 << n)),
                        ));
                    }
                    // Sign-extend idiom `(x << k) >> k` (k ∈ {8,16,24} narrows to i8/i16/i24).
                    // Keep the inner value as a tracked Shl so the paired `I32ShrS` can
                    // round-trip it back to `x`. Without this, an `obj_cmp` result that the
                    // SDK sign-extends before a `< 0` test is lost to `Unknown`, and the
                    // whole `if a < b { panic }` guard is then dropped (the fuzz fixture).
                    // On escape (no matching `>> k`) this renders to `UnknownVal` exactly as
                    // the prior `Unknown` did — `strip_val_encode` leaves a bare Shl unknown.
                    (_, Some(n)) if matches!(n, 8 | 16 | 24) => {
                        cov_mark::hit!(i32_sign_extend_shl_tracked);
                        self.stack.push(StackVal::BinOp(
                            Box::new(a),
                            BinOper::Shl,
                            Box::new(StackVal::I32(n as i32)),
                        ));
                    }
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I32Or => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    (StackVal::I32(x), StackVal::I32(y)) => {
                        self.stack.push(StackVal::I32(x | y));
                    }
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I32Xor => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    (StackVal::I32(x), StackVal::I32(y)) => {
                        self.stack.push(StackVal::I32(x ^ y));
                    }
                    // xor 0 is identity
                    (_, StackVal::I32(0)) => self.stack.push(a),
                    (StackVal::I32(0), _) => self.stack.push(b),
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I32ShrS => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    (StackVal::I32(x), StackVal::I32(y)) => {
                        self.stack.push(StackVal::I32(x >> y));
                    }
                    // Sign-extend round-trip: `(inner << k) >> k` with matching `k` restores
                    // `inner`. Value-preserving for the subsequent `< 0` / `>= 0` sign test
                    // the SDK emits after `obj_cmp`, which is what lets `a < b` survive.
                    (StackVal::BinOp(inner, BinOper::Shl, shl_amt), StackVal::I32(y))
                        if matches!(*y, 8 | 16 | 24)
                            && matches!(**shl_amt, StackVal::I32(k) if k == *y) =>
                    {
                        cov_mark::hit!(i32_sign_extend_roundtrip);
                        let inner = (**inner).clone();
                        self.stack.push(inner);
                    }
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I64Xor => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    (StackVal::I64(x), StackVal::I64(y)) => {
                        self.stack.push(StackVal::I64(x ^ y));
                    }
                    (_, StackVal::I64(0)) => self.stack.push(a),
                    (StackVal::I64(0), _) => self.stack.push(b),
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I64ShrS => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    (StackVal::I64(x), StackVal::I64(y)) => {
                        self.stack.push(StackVal::I64(x >> y));
                    }
                    (StackVal::I64(x), StackVal::I32(y)) => {
                        self.stack.push(StackVal::I64(x >> y));
                    }
                    // Preserve Param/HostCallResult identity through shifts (e.g., >> 8 for I64Small Val-decode).
                    _ if matches!(a, StackVal::Param(_) | StackVal::HostCallResult(_)) => {
                        self.stack.push(a)
                    }
                    _ => self.stack.push(StackVal::Unknown),
                }
            }

            // Conversion
            WasmInstr::I32WrapI64 => {
                let v = self.stack.pop().unwrap_or(StackVal::Unknown);
                match v {
                    StackVal::I64(x) => self.stack.push(StackVal::I32(x as i32)),
                    other => self.stack.push(other), // Preserve identity for non-constants
                }
            }
            WasmInstr::I64ExtendI32S | WasmInstr::I64ExtendI32U => {
                let v = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.stack.push(v);
            }

            // Memory loads/stores
            WasmInstr::I32Load(off)
            | WasmInstr::I64Load(off)
            | WasmInstr::I32Load8S(off)
            | WasmInstr::I32Load8U(off)
            | WasmInstr::I32Load16S(off)
            | WasmInstr::I32Load16U(off)
            | WasmInstr::I64Load8S(off)
            | WasmInstr::I64Load8U(off)
            | WasmInstr::I64Load16S(off)
            | WasmInstr::I64Load16U(off)
            | WasmInstr::I64Load32S(off)
            | WasmInstr::I64Load32U(off) => {
                let addr = self.stack.pop().unwrap_or(StackVal::Unknown);
                let loaded = if let StackVal::FrameSlot(id, slot_off) = addr {
                    match (slot_off.term, frame_slot_key(slot_off.base, *off)) {
                        // A static slot promoted to a loop-carried scalar reads as
                        // its synthetic `var_{idx}` rather than the spilled value.
                        (None, Some(slot)) if self.promoted_slots.contains_key(&(id, slot)) => {
                            StackVal::LetBinding(self.promoted_slots[&(id, slot)])
                        }
                        (None, Some(slot)) => {
                            let mut v = self
                                .frame_slots
                                .borrow()
                                .get(&(id, slot))
                                .cloned()
                                .unwrap_or(StackVal::Unknown);
                            // Sound-join read poison (issue #34 phase 2
                            // repair): this generic load is the dataflow read
                            // of record. If the slot is tainted by a join and
                            // the observed value is STILL the then arm's
                            // value, this read consumes a phantom — the else
                            // path (`CrossArm`), the runtime-conditional
                            // fall-through (`Conditional`), or a path that
                            // provably returned (`DeadThen`) never produced
                            // it. Degrade the read to `Unknown` (today's
                            // honest `todo!()`). `Unknown` never poisons
                            // (nothing was observed), and a taint whose value
                            // another writer has since replaced never poisons
                            // (the `val` equality check) — recognizer seeds
                            // and else-arm stores keep their audited values.
                            // The census (`DBG_SLOTREAD`) measured 15 such
                            // reads corpus-wide, every one already degrading
                            // honestly downstream, so this closes the latent
                            // phantom-read hazard with no recovery cost. The
                            // `stack_val_to_expr` FrameSlot-resolution path is
                            // deliberately NOT poisoned: those resolutions
                            // happen under recognizer control, where adopted
                            // then-arm values are part of audited shapes.
                            if *DBG_LOOPRBW {
                                let wpos = self.slot_write_log.borrow().len();
                                self.slot_read_log.borrow_mut().push(((id, slot), wpos));
                            }
                            if !matches!(v, StackVal::Unknown)
                                && let Some(t) = self.slot_taints.borrow().get(&(id, slot))
                                && t.val == v
                            {
                                cov_mark::hit!(join_tainted_read_poisoned);
                                if *DBG_SLOTREAD {
                                    let tag = match t.kind {
                                        SlotTaintKind::CrossArm => "else-rbw",
                                        SlotTaintKind::Conditional => "cond-read",
                                        SlotTaintKind::DeadThen => "dead-then-read",
                                        SlotTaintKind::LoopVariant => "loop-variant-read",
                                    };
                                    let mut vdbg = format!("{v:?}");
                                    vdbg.truncate(160);
                                    eprintln!(
                                        "[SLOTREAD] {tag} frame=({id},{slot}) loop={} inline={} v={vdbg}",
                                        self.loop_depth, self.inline_depth
                                    );
                                }
                                v = StackVal::Unknown;
                            }
                            if matches!(v, StackVal::Unknown) {
                                let missing = !self.frame_slots.borrow().contains_key(&(id, slot));
                                if *DBG_SLOTMISS {
                                    let kind = if missing { "missing" } else { "stored-unknown" };
                                    let journal = self.slot_defs.borrow();
                                    let defs = journal.get(&(id, slot));
                                    eprintln!(
                                        "[SLOTMISS] frame={id} off={slot} kind={kind} defs={} unique_pure={}",
                                        defs.map_or(0, |d| d.len()),
                                        defs.is_some_and(|d| d.len() == 1
                                            && stack_val_is_loop_invariant_pure(&d[0]))
                                    );
                                }
                                // Unique-reaching-def fill (issue #34 slice): the
                                // state map lost this slot (invalidation /
                                // conservative merge), but the journal proves the
                                // function performed exactly ONE store to it, of a
                                // pure loop-invariant value. That store is the
                                // unique reaching definition, so the load reads
                                // it. Any other journal state — zero defs, several
                                // defs, an impure or loop-varying value, or a load
                                // inside a loop body — keeps today's `Unknown`.
                                if missing && self.loop_depth == 0 {
                                    let journal = self.slot_defs.borrow();
                                    if let Some(defs) = journal.get(&(id, slot))
                                        && let [only_def] = defs.as_slice()
                                        && stack_val_is_loop_invariant_pure(only_def)
                                    {
                                        cov_mark::hit!(unique_slot_def_filled);
                                        v = only_def.clone();
                                    }
                                }
                            }
                            v
                        }
                        // Dynamic (loop-indexed) offset: read the value a matching
                        // indexed store left in the side table.
                        (Some(term), Some(base)) => self
                            .dynamic_slots
                            .borrow()
                            .get(&(id, term, base))
                            .cloned()
                            .unwrap_or(StackVal::Unknown),
                        _ => StackVal::Unknown,
                    }
                } else if let Some(const_addr) = to_u64(&addr) {
                    // Try reading from WASM data segments for constant addresses.
                    // Zero-extend per WASM zero-initialized memory: a wide load of a
                    // narrow static value (e.g. `i32.load` of a 1-byte enum
                    // discriminant) reads the byte plus zero-initialized upper bytes.
                    let byte_addr = const_addr as u32 + *off;
                    let rd = |n: u32| {
                        self.wasm_module
                            .data_sections
                            .read_bytes_zero_extended(byte_addr, n)
                    };
                    match instr {
                        WasmInstr::I32Load(_) => rd(4)
                            .and_then(|b| b.as_slice().try_into().ok())
                            .map(|b| StackVal::I32(i32::from_le_bytes(b)))
                            .unwrap_or(StackVal::Unknown),
                        WasmInstr::I64Load(_) => rd(8)
                            .and_then(|b| b.as_slice().try_into().ok())
                            .map(|b| StackVal::I64(i64::from_le_bytes(b)))
                            .unwrap_or(StackVal::Unknown),
                        WasmInstr::I32Load8U(_) | WasmInstr::I64Load8U(_) => rd(1)
                            .map(|b| StackVal::I32(b[0] as i32))
                            .unwrap_or(StackVal::Unknown),
                        WasmInstr::I32Load8S(_) | WasmInstr::I64Load8S(_) => rd(1)
                            .map(|b| StackVal::I32(b[0] as i8 as i32))
                            .unwrap_or(StackVal::Unknown),
                        WasmInstr::I32Load16U(_) | WasmInstr::I64Load16U(_) => rd(2)
                            .and_then(|b| b.as_slice().try_into().ok())
                            .map(|b| StackVal::I32(u16::from_le_bytes(b) as i32))
                            .unwrap_or(StackVal::Unknown),
                        WasmInstr::I32Load16S(_) | WasmInstr::I64Load16S(_) => rd(2)
                            .and_then(|b| b.as_slice().try_into().ok())
                            .map(|b| StackVal::I32(i16::from_le_bytes(b) as i32))
                            .unwrap_or(StackVal::Unknown),
                        WasmInstr::I64Load32U(_) => rd(4)
                            .and_then(|b| b.as_slice().try_into().ok())
                            .map(|b| StackVal::I64(u32::from_le_bytes(b) as i64))
                            .unwrap_or(StackVal::Unknown),
                        WasmInstr::I64Load32S(_) => rd(4)
                            .and_then(|b| b.as_slice().try_into().ok())
                            .map(|b| StackVal::I64(i32::from_le_bytes(b) as i64))
                            .unwrap_or(StackVal::Unknown),
                        _ => StackVal::Unknown,
                    }
                } else {
                    StackVal::Unknown
                };
                self.stack.push(loaded);
            }
            WasmInstr::I64Store(offset) => {
                let value = self.stack.pop().unwrap_or(StackVal::Unknown);
                let addr = self.stack.pop().unwrap_or(StackVal::Unknown);
                self.memory_stores.push(MemoryStore {
                    offset: *offset,
                    value: value.clone(),
                });
                if let StackVal::FrameSlot(id, slot_off) = addr
                    && let Some(base) = frame_slot_key(slot_off.base, *offset)
                {
                    match slot_off.term {
                        None => self.store_frame_slot(id, base, value, 8),
                        // Dynamic (loop-indexed) write: record it in the side table
                        // keyed by the symbolic term so a matching indexed load reads
                        // it back, and invalidate any static slot the write could
                        // alias so a later static load can't read a stale value.
                        Some(term) => {
                            self.invalidate_static_aliases(id, term, base);
                            self.dynamic_slots
                                .borrow_mut()
                                .insert((id, term, base), value);
                        }
                    }
                }
            }
            WasmInstr::I32Store(offset) => {
                let value = self.stack.pop().unwrap_or(StackVal::Unknown);
                let addr = self.stack.pop().unwrap_or(StackVal::Unknown);
                // Note: I32Store is NOT recorded in memory_stores because it's typically
                // used for bookkeeping (lengths, offsets), not Val-encoded fields.
                // Val-encoded fields are stored via I64Store (Soroban Vals are 64-bit).
                if let StackVal::FrameSlot(id, slot_off) = addr
                    && let Some(base) = frame_slot_key(slot_off.base, *offset)
                {
                    match slot_off.term {
                        None => self.store_frame_slot(id, base, value, 4),
                        // Dynamic (loop-indexed) write: record it in the side table
                        // keyed by the symbolic term so a matching indexed load reads
                        // it back, and invalidate any static slot the write could
                        // alias so a later static load can't read a stale value.
                        Some(term) => {
                            self.invalidate_static_aliases(id, term, base);
                            self.dynamic_slots
                                .borrow_mut()
                                .insert((id, term, base), value);
                        }
                    }
                }
            }
            WasmInstr::I32Store8(offset)
            | WasmInstr::I32Store16(offset)
            | WasmInstr::I64Store8(offset)
            | WasmInstr::I64Store16(offset)
            | WasmInstr::I64Store32(offset) => {
                let value = self.stack.pop().unwrap_or(StackVal::Unknown);
                let addr = self.stack.pop().unwrap_or(StackVal::Unknown);
                // Track sub-word stores in frame_slots so subsequent loads
                // (e.g., I64Load8U) can resolve discriminant bytes written by
                // struct/enum decoders. Not added to memory_stores (these are
                // bookkeeping values, not Val-encoded fields).
                let sub_width = match instr {
                    WasmInstr::I32Store8(_) | WasmInstr::I64Store8(_) => 1,
                    WasmInstr::I32Store16(_) | WasmInstr::I64Store16(_) => 2,
                    _ => 4,
                };
                if let StackVal::FrameSlot(id, slot_off) = addr
                    && let Some(base) = frame_slot_key(slot_off.base, *offset)
                {
                    match slot_off.term {
                        None => self.store_frame_slot(id, base, value, sub_width),
                        // Dynamic (loop-indexed) write: record it in the side table
                        // keyed by the symbolic term so a matching indexed load reads
                        // it back, and invalidate any static slot the write could
                        // alias so a later static load can't read a stale value.
                        Some(term) => {
                            self.invalidate_static_aliases(id, term, base);
                            self.dynamic_slots
                                .borrow_mut()
                                .insert((id, term, base), value);
                        }
                    }
                }
            }

            // Control flow - consume silently, stack effects only
            WasmInstr::Block { .. } | WasmInstr::Loop { .. } => {}
            WasmInstr::If { .. } => {
                self.stack.pop(); // condition
            }
            WasmInstr::Else => {}
            WasmInstr::End => {}
            WasmInstr::Br(_) | WasmInstr::BrIf(_) => {
                if matches!(instr, WasmInstr::BrIf(_)) {
                    self.stack.pop(); // condition
                }
            }
            WasmInstr::BrTable { .. } => {
                self.stack.pop();
            }

            // Stack manipulation
            WasmInstr::Drop => {
                self.stack.pop();
            }
            WasmInstr::Select => {
                // WASM select: if cond != 0 then val1 else val2
                let cond = self.stack.pop().unwrap_or(StackVal::Unknown);
                let val2 = self.stack.pop().unwrap_or(StackVal::Unknown);
                let val1 = self.stack.pop().unwrap_or(StackVal::Unknown);
                match &cond {
                    StackVal::I32(0) | StackVal::I64(0) => self.stack.push(val2),
                    StackVal::I32(_) | StackVal::I64(_) => self.stack.push(val1),
                    _ => self.stack.push(val1), // default to val1 (common path)
                }
            }

            // Other
            WasmInstr::Return => {
                // In inlined functions, an explicit Return marks an early exit path.
                // Capture the stack-top value (if meaningful) as the return expression,
                // so lift_inline_call can extract it. Then clear the stack to prevent
                // dead-code paths from overwriting the return value.
                if self.inline_depth > 0 {
                    let ret_expr = self.stack.last().and_then(|top| {
                        let expr = stack_val_to_expr(
                            top,
                            self.params,
                            self.registry,
                            Some(&self.frame_slots.borrow()),
                        );
                        if matches!(expr, SorobanExpr::Void | SorobanExpr::UnknownVal) {
                            None
                        } else {
                            Some(expr)
                        }
                    });
                    self.stmts.push(SorobanStmt::Return(ret_expr));
                }
            }
            WasmInstr::Unreachable => {
                // Emit Panic for `unreachable` instructions that represent user-level
                // `panic!()` calls. The heuristic:
                // - At top level (inline_depth==0): only emit when stmts is empty,
                //   meaning the entire function body is just `unreachable` (a panic wrapper).
                //   Non-empty stmts means this is dead code after real host calls.
                // - Inside inlined functions (inline_depth>0): emit unless the last
                //   stmt is already Panic/PanicWithError (avoids duplicate panics).
                //   These represent actual panic paths in user logic (e.g., `if a < b { panic!() }`).
                let should_emit = if self.inline_depth > 0 {
                    !matches!(
                        self.stmts.last(),
                        Some(SorobanStmt::Expr(
                            SorobanExpr::Panic | SorobanExpr::PanicWithError(_)
                        ))
                    )
                } else {
                    self.stmts.is_empty()
                };
                if should_emit {
                    self.stmts.push(SorobanStmt::Expr(SorobanExpr::Panic));
                }
            }
            WasmInstr::Nop => {}
            WasmInstr::MemorySize => self.stack.push(StackVal::Unknown),
            WasmInstr::MemoryGrow => {
                self.stack.pop();
                self.stack.push(StackVal::Unknown);
            }
            WasmInstr::CallIndirect(type_index) => {
                // Pop the table index operand
                self.stack.pop();
                // Look up the type signature to get param/result counts
                let (num_params, num_results) = self
                    .wasm_module
                    .types
                    .get(*type_index as usize)
                    .map(|ft| (ft.params.len(), ft.results.len()))
                    .unwrap_or((0, 0));
                // Pop parameters
                for _ in 0..num_params {
                    self.stack.pop();
                }
                // Push results
                for _ in 0..num_results {
                    self.stack.push(StackVal::Unknown);
                }
                self.stmts.push(SorobanStmt::Comment(
                    "WARNING: call_indirect — not valid in Soroban".to_string(),
                ));
            }

            WasmInstr::I32DivS | WasmInstr::I32DivU => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    (StackVal::I32(x), StackVal::I32(y)) if *y != 0 => {
                        self.stack.push(StackVal::I32(x / y));
                    }
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I32RemS | WasmInstr::I32RemU => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    (StackVal::I32(x), StackVal::I32(y)) if *y != 0 => {
                        self.stack.push(StackVal::I32(x % y));
                    }
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I64DivS | WasmInstr::I64DivU => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    (StackVal::I64(x), StackVal::I64(y)) if *y != 0 => {
                        self.stack.push(StackVal::I64(x / y));
                    }
                    _ => self.stack.push(StackVal::Unknown),
                }
            }
            WasmInstr::I64RemS | WasmInstr::I64RemU => {
                let b = self.stack.pop().unwrap_or(StackVal::Unknown);
                let a = self.stack.pop().unwrap_or(StackVal::Unknown);
                match (&a, &b) {
                    (StackVal::I64(x), StackVal::I64(y)) if *y != 0 => {
                        self.stack.push(StackVal::I64(x % y));
                    }
                    _ => self.stack.push(StackVal::Unknown),
                }
            }

            WasmInstr::Unknown(_) => {}
        }
    }

    /// Lift a structured tree of WASM blocks into Soroban IR.
    fn lift_structured(&mut self, blocks: &[super::structurize::StructuredBlock]) {
        use super::structurize::StructuredBlock;
        let mut i = 0;
        while i < blocks.len() {
            match &blocks[i] {
                // Flat BrIf(0) at the instruction level: these appear when a Block
                // body has multiple BrIf(0) instructions and the Block handler only
                // captured the first one. Subsequent BrIf(0) in the body become flat
                // Instruction items in the body_ctx's processing.
                //
                // When the condition involves Unknown (dispatch preamble type check),
                // just pop the condition and continue — the check always passes for
                // valid inputs. This allows the lifter to process subsequent
                // instructions correctly instead of treating them as branch-sequential
                // code where all values accumulate and Return(None) leaks.
                //
                // For constant conditions, fold away (true → break, false → continue).
                // Non-trivial conditions fall through to the default instruction handler
                // (no-op: just pops condition) to preserve existing behavior.
                StructuredBlock::Instruction(crate::wasm::ir::WasmInstr::BrIf(0))
                    if i + 1 < blocks.len() =>
                {
                    let cond_val = self.stack.pop().unwrap_or(StackVal::Unknown);

                    // Unknown conditions (dispatch preamble type checks): always pass.
                    if stack_val_contains_unknown(&cond_val) {
                        i += 1;
                        continue;
                    }

                    // Inside a guard-error-path block, constant conditions can be
                    // safely folded: false → continue (body runs), true → continue
                    // (the "exit" is absorbed — code after this BrIf is the normal
                    // continuation, not dead code, because the outer block's error
                    // path handles the real exit).
                    if self.guard_block_depth > 0 {
                        let const_val = match &cond_val {
                            StackVal::I32(v) => Some(*v as i64),
                            StackVal::I64(v) => Some(*v),
                            _ => None,
                        };
                        if const_val.is_some() {
                            i += 1;
                            continue;
                        }
                    }

                    // Non-trivial condition → fall through to default handler (no-op).
                    // The condition was already popped above.
                }
                StructuredBlock::SafetyNetUnreachable => {
                    // CFG analysis (issue #11) proved every path reaching this
                    // `unreachable` already diverged via return/br/`-> !` call;
                    // the diverging predecessor's terminator IR has already been
                    // emitted. Skip — emitting Panic here would orphan at the
                    // caller's top level after inline-splice and trip
                    // remove_dead_code.
                }
                StructuredBlock::Instruction(instr) => {
                    self.lift_instruction(instr);
                }
                StructuredBlock::Block { body, .. } => {
                    // Try to recognize br_table match pattern first
                    if let Some(match_stmt) = self.try_recognize_match(body) {
                        self.stmts.push(match_stmt);
                        i += 1;
                        continue;
                    }

                    // Vec-front `Option` idiom: `if v.is_empty() { None } else
                    // { Some(v.first_unchecked()) }`. The value-producing `Some`
                    // branch is the following siblings, which the generic
                    // block+br_if handler would drop. Consume the rest of this
                    // block level as the else.
                    if let Some(if_stmt) =
                        self.try_recognize_option_front_if(body, &blocks[i + 1..])
                    {
                        self.stmts.push(if_stmt);
                        break;
                    }

                    // Collect all BrIf(0) positions in the body
                    let brif_positions: Vec<usize> = body
                        .iter()
                        .enumerate()
                        .filter_map(|(idx, b)| {
                            if matches!(
                                b,
                                StructuredBlock::Instruction(crate::wasm::ir::WasmInstr::BrIf(0))
                            ) {
                                Some(idx)
                            } else {
                                None
                            }
                        })
                        .collect();

                    let has_error_path = is_guard_error_path(&blocks[i + 1..]);

                    // Multi-BrIf guard chain: process iteratively to avoid
                    // branch-sequential execution corruption.
                    // Only fire when at least one inter-BrIf segment contains
                    // a Call instruction — this distinguishes real validation
                    // guards (storage reads, auth checks) from SDK dispatch
                    // preambles (pure arithmetic Val tag checks).
                    if brif_positions.len() > 1
                        && has_error_path
                        && has_call_in_brif_segments(body, &brif_positions)
                    {
                        self.process_guard_brif_chain(body, &brif_positions);
                        i += 1;
                        continue;
                    }

                    // Check for block + br_if(0) pattern -> if statement
                    if let Some(&brif_pos) = brif_positions.first() {
                        // Instructions before br_if compute the condition
                        let pre = &body[..brif_pos];
                        let post = &body[brif_pos + 1..];

                        // Lift pre-branch to get condition on stack
                        let mut pre_ctx = self.child_context();
                        pre_ctx.lift_structured(pre);

                        // Pop condition - br_if 0 means "branch OUT if true",
                        // so the remaining body runs when FALSE
                        let cond_val = pre_ctx.stack.pop().unwrap_or(StackVal::Unknown);

                        // Transfer pre_ctx state back
                        self.stack = pre_ctx.stack;
                        self.locals = pre_ctx.locals;
                        self.memory_stores = pre_ctx.memory_stores;
                        self.stmts.extend(pre_ctx.stmts);
                        self.found_host_calls |= pre_ctx.found_host_calls;

                        // GLR Phase 2: snapshot locals before body_ctx creation
                        let pre_branch_locals = self.locals.clone();

                        // Lift post-branch.
                        // If the outer block has a guard error path, increment
                        // guard_block_depth so the flat BrIf handler can treat
                        // constant-true conditions as pass-through.
                        let mut body_ctx = self.child_context();
                        if is_guard_error_path(&blocks[i + 1..]) {
                            body_ctx.guard_block_depth += 1;
                        }
                        body_ctx.lift_structured(post);
                        let then_stmts = body_ctx.stmts;
                        self.found_host_calls |= body_ctx.found_host_calls;

                        // Constant condition: fold away the branch entirely.
                        // Check both I32 and I64 — an i64.store followed by i32.load
                        // returns the stored StackVal unchanged as I64, not truncated to I32.
                        let const_val = match &cond_val {
                            StackVal::I32(v) => Some(*v as i64),
                            StackVal::I64(v) => Some(*v),
                            _ => None,
                        };
                        if let Some(v) = const_val {
                            if v == 0 {
                                // br_if never fires; body always runs -- splice body directly
                                self.stack = body_ctx.stack;
                                self.locals = body_ctx.locals;
                                self.memory_stores = body_ctx.memory_stores;
                                self.stmts.extend(then_stmts);
                            }
                            // else: br_if always fires, body never runs -- discard body stmts
                            i += 1;
                            continue;
                        }

                        // If the condition involves an Unknown value (e.g., from I64And/I64ShrU
                        // on a Soroban Val parameter), this is a dispatch preamble type-check
                        // guard that we cannot evaluate statically. Treat it as always-pass
                        // and emit the body directly without an if wrapper.
                        //
                        // A lone Val tag check (`(v & 0xFF) == TAG`) is handled the same
                        // way: wrapping a value-returning body in `if tag == X { ... }`
                        // would drop its tail/return. Multi-guard validation preambles
                        // (process_guard_brif_chain) still surface tag checks explicitly.
                        if stack_val_contains_unknown(&cond_val)
                            || is_tag_check_condition(&cond_val)
                        {
                            self.stack = body_ctx.stack;
                            self.locals = body_ctx.locals;
                            self.memory_stores = body_ctx.memory_stores;
                            // Filter Return(None)+Panic pairs when the outer
                            // block has a guard error path — these are block-exit
                            // artifacts that would become function-level terminators.
                            let then_stmts = if is_guard_error_path(&blocks[i + 1..]) {
                                strip_return_panic_pairs_in_guard(then_stmts)
                            } else {
                                then_stmts
                            };
                            self.stmts.extend(then_stmts);
                        } else if is_guard_error_path(&blocks[i + 1..]) {
                            // Guard pattern: the blocks after this one form an
                            // unconditional error path, so the body always
                            // executes on the success path.  Propagate body
                            // state back to the parent and splice statements.
                            //
                            // Filter Return(None)+Panic pairs from the body:
                            // these are block-exit artifacts from inlined functions
                            // where the WASM `return` and error-path `panic` leak
                            // into the body. In the guard-error-path context, the
                            // `return` is a block exit (not a function return) and
                            // the `panic` is from the inlined function's error path
                            // (not a real panic in the parent function).
                            let then_stmts = strip_return_panic_pairs_in_guard(then_stmts);
                            //
                            // Strategy depends on whether body has terminators:
                            // - No terminators: full splice (stack + locals +
                            //   stmts) — same as the Unknown-condition path.
                            // - Has terminators: emit If wrapper as normal, then
                            //   selectively upgrade weak parent locals to child
                            //   values for downstream resolution.
                            let has_terminator = then_stmts.iter().any(is_terminator_stmt);
                            self.memory_stores = body_ctx.memory_stores;
                            if has_terminator {
                                let condition = stack_val_to_expr(
                                    &cond_val,
                                    self.params,
                                    self.registry,
                                    Some(&self.frame_slots.borrow()),
                                );
                                let negated = SorobanExpr::Not(Box::new(condition));
                                if !then_stmts.is_empty() {
                                    self.stmts.push(SorobanStmt::If {
                                        condition: negated,
                                        then_body: then_stmts,
                                        else_body: Vec::new(),
                                    });
                                }
                                for (idx, child_val) in body_ctx.locals.iter().enumerate() {
                                    if idx < self.locals.len()
                                        && is_weak_local(&self.locals[idx])
                                        && !is_weak_local(child_val)
                                    {
                                        self.locals[idx] = child_val.clone();
                                    }
                                }
                            } else {
                                self.stack = body_ctx.stack;
                                self.locals = body_ctx.locals;
                                self.stmts.extend(then_stmts);
                            }
                        } else {
                            self.memory_stores = body_ctx.memory_stores;
                            let condition = stack_val_to_expr(
                                &cond_val,
                                self.params,
                                self.registry,
                                Some(&self.frame_slots.borrow()),
                            );
                            let negated = SorobanExpr::Not(Box::new(condition));

                            // GLR Phase 2: selectively propagate body locals.
                            // BrIf(0) means "branch OUT if true" — body runs
                            // when FALSE.  Only upgrade weak parent locals
                            // (Unknown, FrameBase, zero-init) to strong values
                            // discovered in the body.  Full phi-merge is too
                            // aggressive here because most local changes are
                            // branch-sequential execution artifacts, not real
                            // conditional assignments.
                            let body_terminates = then_stmts.iter().any(is_terminator_stmt);
                            if !body_terminates && !is_static_condition(&cond_val) {
                                for (idx, body_val) in body_ctx.locals.iter().enumerate() {
                                    if idx >= self.num_wasm_params as usize
                                        && idx < self.locals.len()
                                        && is_weak_local(&pre_branch_locals[idx])
                                        && !is_weak_local(body_val)
                                    {
                                        self.locals[idx] = body_val.clone();
                                    }
                                }
                            }
                            if !then_stmts.is_empty() {
                                self.stmts.push(SorobanStmt::If {
                                    condition: negated,
                                    then_body: then_stmts,
                                    else_body: Vec::new(),
                                });
                            }
                        }
                    } else {
                        // Regular block - transparent pass-through
                        self.lift_structured(body);
                    }
                }
                StructuredBlock::Loop { body, .. } => {
                    // Detect register-rotation copy loops BEFORE lifting.
                    // Pattern: 2-iteration loop that copies local[SOURCE] to
                    // local[TARGET] via a temporary. The lifter simulates one
                    // iteration, but TARGET only gets the correct value on the
                    // second iteration. Propagate the result explicitly.
                    let rotation = detect_register_rotation(body);

                    // Recover loop-carried locals: locals whose value flows across
                    // the back edge (an accumulator or a counter). Each becomes a
                    // `let mut var_idx = <pre-loop init>` declared before the loop;
                    // the body then mutates it via Assign (see emit_loop_carried_assign),
                    // and post-loop reads resolve to the variable instead of Unknown.
                    //
                    // Gated on a positive counted-loop match: only the bounded
                    // `i += step; i == N` shape opts into recovery. Every other loop
                    // (memory copies, host-call-driven iteration, SDK limb arithmetic
                    // whose value strips cleanly out of the stack top) stays on the
                    // single-pass path with byte-identical output.
                    //
                    // Recovery only fires for locals whose pre-loop init is a known
                    // value — otherwise the initializer would itself be `todo!()`.
                    let mut carried: Vec<u32> = Vec::new();
                    let counted = detect_counted_loop(body).is_some();

                    // Step 1 — local accumulators, only in side-effect-free counted
                    // loops. The genuine-accumulator gate (not a pure counter)
                    // excludes boilerplate index loops the baseline already collapses.
                    let local_analyzed = if counted && !loop_body_has_side_effects(body) {
                        self.analyze_loop_carried_locals(body)
                    } else {
                        Vec::new()
                    };
                    let has_local_accumulator = local_analyzed
                        .iter()
                        .any(|(idx, val)| !is_pure_counter_update(val, *idx));

                    // Step 3 — accumulators spilled to the shadow-stack frame. Allowed
                    // to contain memory stores (the spill is a store) but never calls.
                    let slot_analyzed = if counted && !loop_body_has_calls(body) {
                        self.analyze_loop_carried_slots(body)
                    } else {
                        Vec::new()
                    };
                    let has_slot_accumulator = !slot_analyzed.is_empty();

                    // Locals to recover. The slot path needs the loop's counter
                    // local(s) too (for the `while` condition), even though the loop
                    // stores — so re-derive carried locals without the side-effect gate.
                    let local_candidates: Vec<(u32, StackVal)> = if has_local_accumulator {
                        local_analyzed
                    } else if has_slot_accumulator {
                        self.analyze_loop_carried_locals(body)
                    } else {
                        Vec::new()
                    };

                    // Resolve each carried local's and slot's pre-loop init. The
                    // arithmetic conversion (like phi-merge's init) keeps a numeric
                    // `0` from being Val-decoded into `false`.
                    let local_inits: Vec<(u32, SorobanExpr)> = local_candidates
                        .iter()
                        .map(|(l, _)| {
                            let pre = self
                                .locals
                                .get(*l as usize)
                                .cloned()
                                .unwrap_or(StackVal::Unknown);
                            let slots = self.frame_slots.borrow();
                            (
                                *l,
                                stack_val_to_arith_expr(
                                    &pre,
                                    self.params,
                                    self.registry,
                                    Some(&slots),
                                ),
                            )
                        })
                        .collect();
                    let slot_inits: Vec<((u32, i32), SorobanExpr)> = slot_analyzed
                        .iter()
                        .map(|(key, pre_val)| {
                            let slots = self.frame_slots.borrow();
                            (
                                *key,
                                stack_val_to_arith_expr(
                                    pre_val,
                                    self.params,
                                    self.registry,
                                    Some(&slots),
                                ),
                            )
                        })
                        .collect();

                    // Recovery is all-or-nothing and requires every init to be an
                    // integer literal. A non-literal init (param/field) would be
                    // renamed onto its source by name propagation, turning the
                    // recovered `let mut` into a mutation of an immutable binding.
                    // Recovering only some carried values (e.g. the counter but not
                    // its accumulator) would lose the rest, so bail on the whole loop.
                    let any = !local_inits.is_empty() || !slot_inits.is_empty();
                    let all_literal = local_inits.iter().all(|(_, e)| is_int_literal_expr(e))
                        && slot_inits.iter().all(|(_, e)| is_int_literal_expr(e));

                    if any && all_literal {
                        for (l, init) in local_inits {
                            self.stmts.push(SorobanStmt::Let {
                                name: format!("var_{}", l),
                                mutable: true,
                                value: init,
                            });
                            if let Some(slot) = self.locals.get_mut(l as usize) {
                                *slot = StackVal::LetBinding(l);
                            }
                            carried.push(l);
                        }
                        // Promote each loop-carried frame slot to a fresh `let mut`
                        // variable (synthetic index allocated past the real locals).
                        for ((id, off), init) in slot_inits {
                            let var_idx = self.locals.len() as u32;
                            self.locals.push(StackVal::LetBinding(var_idx));
                            self.stmts.push(SorobanStmt::Let {
                                name: format!("var_{}", var_idx),
                                mutable: true,
                                value: init,
                            });
                            // Slot stores are emitted via store_frame_slot/promoted_slots,
                            // not LocalSet, so the synthetic index is NOT a loop_carried
                            // local — it only needs the promoted_slots mapping.
                            self.promoted_slots.insert((id, off), var_idx);
                        }
                        cov_mark::hit!(loop_carried_recovered);
                    }

                    // Write-log position before the body: everything the log
                    // gains during the body lift is a loop-body store whose
                    // post-loop map value is a ONE-ITERATION artifact (issue
                    // #38 substrate — see `taint_loop_variant_slots`).
                    let loop_pre_wpos = self.slot_write_log.borrow().len();
                    let mut loop_ctx = self.child_context();
                    loop_ctx.loop_carried_locals = carried;
                    loop_ctx.loop_depth += 1;
                    loop_ctx.lift_structured_loop(body);
                    let loop_stmts = loop_ctx.stmts;
                    self.memory_stores = loop_ctx.memory_stores;
                    self.found_host_calls |= loop_ctx.found_host_calls;

                    // Selectively propagate locals from loop context: upgrade locals
                    // to Param/HostCallResult values discovered in the loop body.
                    // Only propagate "strong" values (direct parameter references or
                    // host call results) — these are reliably correct after one
                    // simulated iteration. Constants and BinOps are ambiguous (could
                    // be mid-loop counter values) and are NOT propagated.
                    for (idx, loop_val) in loop_ctx.locals.iter().enumerate() {
                        if idx < self.locals.len()
                            && matches!(loop_val, StackVal::Param(_) | StackVal::HostCallResult(_))
                            && !matches!(
                                self.locals[idx],
                                StackVal::Param(_) | StackVal::HostCallResult(_)
                            )
                        {
                            self.locals[idx] = loop_val.clone();
                            // Inside guard blocks, protect SymbolLiteral locals from
                            // being overwritten by subsequent trivial loops. Sequential
                            // loops from br_table dispatch each construct a different
                            // variant symbol, and the first one propagated is correct
                            // (the br_table selected it). Without protection, the last
                            // loop's symbol wins (branch-sequential: last arm overwrites).
                            if self.guard_block_depth > 0
                                && let StackVal::HostCallResult(expr) = loop_val
                                && matches!(expr.as_ref(), SorobanExpr::SymbolLiteral(_))
                            {
                                self.phi_protected_locals.push(idx as u32);
                            }
                        }
                    }

                    // Issue #36: invalidate stale empty-collection defs the loop
                    // body reassigns. Soroban collections are immutable host
                    // objects — `map.set`/`vec.push_back` lower to
                    // `local = map_put(local, ..)` reassignment chains — so a
                    // parent local still holding the pre-loop `map_new`/`vec_new`
                    // result after the body wrote that local is one arm of an
                    // unmodeled phi. Post-loop reads would clone the empty
                    // constructor into every use site (silent-wrong: it
                    // compiles). Retreat to the honest hole. The scan is
                    // syntactic (`local.set`/`local.tee` anywhere in the nested
                    // body) because the write usually sits inside a guard whose
                    // child context never propagates it back up. Locals promoted
                    // to `let mut` by the carried-local recovery above are
                    // LetBinding by now and thus not touched.
                    {
                        use crate::wasm::ir::WasmInstr;
                        let mut body_instrs = Vec::new();
                        collect_instrs(body, &mut body_instrs);
                        for instr in &body_instrs {
                            if let WasmInstr::LocalSet(idx) | WasmInstr::LocalTee(idx) = instr {
                                let i = *idx as usize;
                                if i < self.locals.len() && is_empty_collection_val(&self.locals[i])
                                {
                                    cov_mark::hit!(lost_collection_loop_overwrite);
                                    self.locals[i] = StackVal::Unknown;
                                }
                            }
                        }
                    }

                    // Apply register-rotation propagation: after a 2-iteration
                    // copy loop, local[TARGET] = local[SOURCE] (pre-loop value).
                    if let Some((target, source)) = rotation
                        && (source as usize) < self.locals.len()
                        && (target as usize) < self.locals.len()
                    {
                        let source_val = self.locals[source as usize].clone();
                        self.locals[target as usize] = source_val;
                    }

                    // Detect memory copy loops and extend frame_slots for
                    // iterations the lifter didn't simulate. Pattern:
                    //   for offset in (0, STEP, ..., LIMIT-STEP):
                    //     frame[dest+offset] = frame[src+offset]
                    // The lifter simulated iteration 0; extend with 1..N.
                    let copy_info = detect_memory_copy_loop(body);
                    if let Some(copy_info) = &copy_info {
                        // Resolve frame_id: find any frame_slot entry at dest_base
                        // offset that was created by iteration 0's I64Store.
                        let frame_slots = self.frame_slots.borrow();
                        let frame_id = frame_slots
                            .keys()
                            .find(|(_, off)| *off == copy_info.dest_base)
                            .map(|(id, _)| *id);
                        if let Some(fid) = frame_id {
                            let mut new_entries = Vec::new();
                            for iter_offset in
                                (copy_info.step..copy_info.limit).step_by(copy_info.step as usize)
                            {
                                let src_key = (fid, copy_info.src_base + iter_offset as i32);
                                if let Some(val) = frame_slots.get(&src_key)
                                    && !matches!(
                                        val,
                                        StackVal::FrameSlot(..)
                                            | StackVal::FrameBase(..)
                                            | StackVal::Unknown
                                    )
                                {
                                    let dest_key = (fid, copy_info.dest_base + iter_offset as i32);
                                    new_entries.push((dest_key, val.clone()));
                                }
                            }
                            drop(frame_slots);
                            let mut frame_slots = self.frame_slots.borrow_mut();
                            for (key, val) in new_entries {
                                frame_slots.insert(key, val);
                            }
                        }
                    } else {
                        // Not a proven-exact loop model: the map's body-written
                        // slots are one-iteration artifacts — stamp them.
                        self.taint_loop_variant_slots(loop_pre_wpos);
                    }

                    if !loop_stmts.is_empty() {
                        self.stmts.push(SorobanStmt::Loop { body: loop_stmts });
                    }
                }
                StructuredBlock::IfElse {
                    then_body,
                    else_body,
                    block_type,
                } => {
                    // Pop condition from stack
                    let cond_val = self.stack.pop().unwrap_or(StackVal::Unknown);

                    // Issue #35: a fallible storage-decode discriminant guarded
                    // by a bare trap is the `.unwrap()`'s None-arm re-encoded —
                    // the same inline already rendered the load as
                    // `get(..).unwrap()`, which carries the panic-on-missing
                    // semantics. Fold the guard. ONLY this shape folds: any
                    // guard with real logic, an else arm, or a specific
                    // `panic_with_error!` falls through to the generic path,
                    // where the marker degrades to `UnknownVal` (today's
                    // honest `todo!()`), never a fabricated fold.
                    if else_body.is_empty()
                        && matches!(
                            then_body[..],
                            [StructuredBlock::Instruction(
                                crate::wasm::ir::WasmInstr::Unreachable
                            )]
                        )
                        && is_option_decode_none_check(&cond_val)
                    {
                        cov_mark::hit!(option_decode_trap_guard_folded);
                        i += 1;
                        continue;
                    }

                    // SDK multi-param marshalling guard:
                    // `if ((tag(a)!=Ta)|(tag(b)!=Tb))==0 { body; return } unreachable`.
                    // The composite condition is tautological for declared param
                    // types (see `is_param_tag_guard_composite`) and the SDK's
                    // `#[contract]` wrapper regenerates it on recompile, so splice
                    // the body inline instead of wrapping it in an `if`. Crucially,
                    // adopt the branch's value stack: the body's tail value is the
                    // function's return, which the generic path below would discard
                    // (a `Return` at depth 0 emits no statement), collapsing pure
                    // getters to an empty `if` + trap → `panic!()` (blend-backstop
                    // `user_balance`). The failure trap is marshalling too — skip it.
                    if self.inline_depth == 0
                        && else_body.is_empty()
                        && matches!(
                            then_body.last(),
                            Some(StructuredBlock::Instruction(
                                crate::wasm::ir::WasmInstr::Return
                            ))
                        )
                        && matches!(
                            &blocks[i + 1..],
                            [StructuredBlock::Instruction(
                                crate::wasm::ir::WasmInstr::Unreachable
                            )] | [StructuredBlock::SafetyNetUnreachable]
                        )
                        && is_param_tag_guard_composite(
                            &blocks[..i],
                            self.params,
                            self.num_wasm_params,
                        )
                    {
                        cov_mark::hit!(param_tag_guard_composite_spliced);
                        let mut then_ctx = self.child_context();
                        then_ctx.lift_structured(then_body);
                        self.stack = then_ctx.stack;
                        self.locals = then_ctx.locals;
                        self.memory_stores = then_ctx.memory_stores;
                        self.found_host_calls |= then_ctx.found_host_calls;
                        self.stmts.extend(then_ctx.stmts);
                        i += 2;
                        continue;
                    }

                    let condition = stack_val_to_expr(
                        &cond_val,
                        self.params,
                        self.registry,
                        Some(&self.frame_slots.borrow()),
                    );

                    let pre_locals = self.locals.clone();

                    // Measurement for the sound slot join (issue #34, next
                    // phase): both arms share ONE frame-slot map, so the
                    // else arm observes then-arm writes and the join is
                    // last-write-wins. Snapshot around the arms to quantify
                    // where that diverges from a sound per-arm join before
                    // changing the semantics.
                    let pre_slots = DBG_SLOTJOIN.then(|| self.frame_slots.borrow().clone());

                    // Write-log position before the then arm: everything the
                    // log gains between here and the post-then position is a
                    // then-arm store (issue #34 phase 2 sound-join analysis).
                    let pre_wpos = self.slot_write_log.borrow().len();

                    // Lift then branch with child context
                    let mut then_ctx = self.child_context();
                    then_ctx.lift_structured(then_body);
                    let mut then_stmts = then_ctx.stmts;

                    let then_slots = DBG_SLOTJOIN.then(|| self.frame_slots.borrow().clone());

                    // Collapse the then segment of the write log to per-key
                    // `(pre_if_value, final_then_value)`: the FIRST entry's
                    // recorded previous value is what the slot held before the
                    // `if`, the LAST entry's new value is what the then arm
                    // left behind. Keys whose final value merely restores the
                    // pre-if value are net no-ops — an else-path or downstream
                    // read observing them is sound — and are dropped here.
                    let then_writes: Vec<((u32, i32), StackVal)> = {
                        let log = self.slot_write_log.borrow();
                        let mut per_key: Vec<((u32, i32), Option<StackVal>, StackVal)> = Vec::new();
                        for w in &log[pre_wpos..] {
                            // Same-depth entries only: an inlined helper's
                            // internal stores are not this join's arm writes.
                            if w.depth != self.inline_depth {
                                continue;
                            }
                            match per_key.iter_mut().find(|(pk, _, _)| *pk == w.key) {
                                Some((_, _, last)) => *last = w.new.clone(),
                                None => per_key.push((w.key, w.prev.clone(), w.new.clone())),
                            }
                        }
                        per_key
                            .into_iter()
                            .filter(|(_, first_prev, last_new)| {
                                first_prev.as_ref() != Some(last_new)
                            })
                            .map(|(k, _, last_new)| (k, last_new))
                            .collect()
                    };

                    // Stamp the surviving then-arm values as `CrossArm`
                    // taints before the else arm lifts against the same
                    // shared map: a generic else-arm load that observes one
                    // reads a value the else path never produced, and the
                    // load path degrades it to `Unknown` (census: zero such
                    // reads corpus-wide, so this is a pure safety net).
                    {
                        let mut taints = self.slot_taints.borrow_mut();
                        for (k, val) in &then_writes {
                            taints.insert(
                                *k,
                                SlotTaint {
                                    kind: SlotTaintKind::CrossArm,
                                    val: val.clone(),
                                },
                            );
                        }
                    }

                    // Lift else branch with child context
                    let mut else_ctx = self.child_context();
                    else_ctx.lift_structured(else_body);
                    let mut else_stmts = else_ctx.stmts;

                    // Reclassify surviving `CrossArm` taints at the join. A
                    // taint an else-arm store already cleared stays cleared
                    // (the slot is self-produced on the else path).
                    {
                        let then_term = then_stmts.iter().any(is_terminator_stmt);
                        let else_term = else_stmts.iter().any(is_terminator_stmt);
                        let mut taints = self.slot_taints.borrow_mut();
                        for (k, _) in &then_writes {
                            let Some(t) = taints.get_mut(k) else { continue };
                            if t.kind != SlotTaintKind::CrossArm {
                                continue;
                            }
                            if else_term {
                                // Fall-through implies the then path ran (or
                                // nothing falls through at all): the value is
                                // unconditionally valid downstream.
                                taints.remove(k);
                            } else if then_term {
                                t.kind = SlotTaintKind::DeadThen;
                            } else {
                                t.kind = SlotTaintKind::Conditional;
                            }
                        }
                    }

                    if let (Some(pre), Some(then_s)) = (pre_slots, then_slots) {
                        let post = self.frame_slots.borrow();
                        let then_terminated = then_stmts.iter().any(is_terminator_stmt);
                        let else_terminated = else_stmts.iter().any(is_terminator_stmt);
                        for (k, tv) in &then_s {
                            let changed_in_then = pre.get(k) != Some(tv);
                            if !changed_in_then {
                                continue;
                            }
                            match post.get(k) {
                                // Both arms wrote k with different values: the
                                // survivor is the else value — last-write-wins.
                                Some(pv) if pv != tv && !else_terminated => {
                                    eprintln!(
                                        "[SLOTJOIN] divergent frame=({},{}) then!=else (else wins) then_term={then_terminated}",
                                        k.0, k.1
                                    );
                                }
                                // Then wrote and the value survives the join.
                                // Value snapshots cannot distinguish "else
                                // left it untouched" (a genuine leak: the
                                // else path never produced the value) from
                                // "else wrote the SAME value" (a benign
                                // convergent write) — this class is an UPPER
                                // BOUND on leaks, not a leak count. The
                                // read/write-journal instrumentation of the
                                // next increment measures the true
                                // population.
                                Some(pv) if pv == tv && !else_terminated && !then_terminated => {
                                    eprintln!(
                                        "[SLOTJOIN] then-survives frame=({},{}) (leak upper bound: else untouched OR wrote same)",
                                        k.0, k.1
                                    );
                                }
                                _ => {}
                            }
                        }
                        drop(post);
                    }

                    // Merge memory stores and found_host_calls from both branches
                    // Use else branch stores (it runs last) to preserve sequential order
                    self.memory_stores = else_ctx.memory_stores;
                    self.found_host_calls |= then_ctx.found_host_calls | else_ctx.found_host_calls;

                    // GLR: reconcile locals modified in either branch
                    let then_terminates = then_stmts.iter().any(is_terminator_stmt);
                    let else_terminates = else_stmts.iter().any(is_terminator_stmt);
                    if !(then_terminates && else_terminates) {
                        reconcile_branch_locals(
                            &mut self.locals,
                            &mut self.stmts,
                            &pre_locals,
                            &then_ctx.locals,
                            &else_ctx.locals,
                            then_terminates,
                            else_terminates,
                            self.num_wasm_params,
                            &mut then_stmts,
                            &mut else_stmts,
                            &mut self.phi_protected_locals,
                            self.params,
                            self.registry,
                            Some(&self.frame_slots.borrow()),
                        );
                    }

                    // Value-producing `if (result T)`: the wasm construct pushes one
                    // value from whichever arm ran, but the generic handler drops both
                    // arm stacks, so every consumer of the result reads `Unknown` —
                    // even when the arms are the SDK's small/object Val encode or
                    // decode split of the SAME source value (`(x << 8) | tag` vs
                    // `obj_from_u64(x)`), where the joined value is provably that
                    // conversion. Push the join only when equivalence is proven;
                    // any other shape leaves the stack exactly as before (the
                    // consumer keeps seeing what it saw today), so this is additive.
                    if *DBG_JOIN && matches!(block_type, crate::wasm::ir::BlockType::Value(_)) {
                        eprintln!(
                            "[DBG_JOIN] value-if: tt={} et={} parent_len={} then_len={} else_len={} tv={:?} ev={:?}",
                            then_terminates,
                            else_terminates,
                            self.stack.len(),
                            then_ctx.stack.len(),
                            else_ctx.stack.len(),
                            then_ctx.stack.last(),
                            else_ctx.stack.last(),
                        );
                    }
                    if matches!(block_type, crate::wasm::ir::BlockType::Value(_))
                        && !then_terminates
                        && !else_terminates
                        && then_ctx.stack.len() == self.stack.len() + 1
                        && else_ctx.stack.len() == self.stack.len() + 1
                        && then_ctx.stack[..self.stack.len()] == self.stack[..]
                        && else_ctx.stack[..self.stack.len()] == self.stack[..]
                        && let Some(joined) = self.join_if_result_values(
                            then_ctx.stack.last().unwrap(),
                            else_ctx.stack.last().unwrap(),
                        )
                    {
                        cov_mark::hit!(if_result_value_joined);
                        self.stack.push(joined);
                    }

                    // Only emit If when there's meaningful content
                    if !then_stmts.is_empty() || !else_stmts.is_empty() {
                        self.stmts.push(SorobanStmt::If {
                            condition,
                            then_body: then_stmts,
                            else_body: else_stmts,
                        });
                    }
                }
            }
            i += 1;
        }
    }

    /// Join the two arm values of a value-producing `if (result T)` when they are
    /// provably the same value. Two shapes qualify:
    ///
    /// 1. Structurally identical pure values (both arms computed the same thing).
    /// 2. The SDK's small/object Val split: one arm is the host-object conversion
    ///    of a source (`obj_from_u64(x)` / `obj_to_u64(x)` → `ValConvert { x }`),
    ///    the other the small-value form of the SAME source (`(x << 8) | tag`,
    ///    or `x` passed through where the shift-decode already stripped). The
    ///    join is the conversion — both arms encode/decode one value, the split
    ///    is host-representation plumbing with no Rust-level meaning.
    ///
    /// Purity is required so the joined expression can be re-read at the
    /// consumer without duplicating a side effect. Anything else → `None`, and
    /// the caller pushes nothing (byte-identical to the pre-join behavior).
    fn join_if_result_values(&self, tv: &StackVal, ev: &StackVal) -> Option<StackVal> {
        if tv == ev && stack_val_is_pure(tv) {
            return Some(tv.clone());
        }
        for (conv, small) in [(tv, ev), (ev, tv)] {
            if let StackVal::HostCallResult(expr) = conv
                && let SorobanExpr::ValConvert { value, .. } = expr.as_ref()
                && expr_is_pure_source(value)
            {
                let src = strip_val_encode(small.clone());
                if stack_val_is_pure(&src)
                    && stack_val_to_expr(
                        &src,
                        self.params,
                        self.registry,
                        Some(&self.frame_slots.borrow()),
                    ) == **value
                {
                    return Some(conv.clone());
                }
            }
        }
        None
    }

    /// Recognize the `Vec`-front `Option` idiom that an `Option<T>`-returning
    /// function lowers to:
    ///
    /// ```ignore
    /// if v.is_empty() { None } else { Some(v.first_unchecked()) }
    /// ```
    ///
    /// rustc + wasm-opt lower this to a `block { <len-check>; br_if; <None>; br_outer }`
    /// where the `Some` path is the *following siblings* of the inner block (the
    /// branch reached when `br_if` fires on the not-empty condition). The generic
    /// `block + br_if` handler keeps only the fall-through (`None`) side and drops
    /// the value-producing `Some` else, so this dedicated recognizer reconstructs
    /// the whole `if`.
    ///
    /// `inner` is the inner `Block`'s body; `tail` is the following siblings.
    /// Gated tightly (Option return + exact block shape + `vec_len` in the
    /// condition + the `Void`/`None` constant in the fall-through) so it cannot
    /// fire on unrelated `Option`-returning branches.
    fn try_recognize_option_front_if(
        &mut self,
        inner: &[super::structurize::StructuredBlock],
        tail: &[super::structurize::StructuredBlock],
    ) -> Option<SorobanStmt> {
        use super::structurize::StructuredBlock;
        use crate::wasm::ir::WasmInstr;

        // Gate: function returns `Option<T>`, and there is a value-producing else.
        if !matches!(self.return_type, Some(ScSpecTypeDef::Option(_))) || tail.is_empty() {
            return None;
        }

        // `inner` must be flat instructions shaped `[<cond..>, BrIf(0), <none..>, Br(K>=1)]`.
        let instrs: Vec<&WasmInstr> = inner
            .iter()
            .map(|b| match b {
                StructuredBlock::Instruction(i) => Some(i),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        let brif_positions: Vec<usize> = instrs
            .iter()
            .enumerate()
            .filter(|(_, i)| matches!(i, WasmInstr::BrIf(0)))
            .map(|(p, _)| p)
            .collect();
        if brif_positions.len() != 1 {
            return None;
        }
        let p = brif_positions[0];
        if !matches!(instrs.last(), Some(WasmInstr::Br(k)) if *k >= 1) {
            return None;
        }

        // The fall-through (cond false) must produce the `Void` Val (tag 2 = `None`).
        let none_path = &instrs[p + 1..instrs.len() - 1];
        if !none_path
            .iter()
            .any(|i| matches!(i, WasmInstr::I64Const(2)))
        {
            return None;
        }

        // Lift the condition and recover the vec it checks the length of.
        let mut cctx = self.child_context();
        cctx.lift_structured(&inner[..p]);
        let cond_top = cctx.stack.last().cloned()?;
        let cond_expr = {
            let slots = self.frame_slots.borrow();
            stack_val_to_expr(&cond_top, self.params, self.registry, Some(&slots))
        };
        let vec = find_vec_len_object(&cond_expr)?;

        if std::env::var("DBG_TRACE").is_ok() {
            eprintln!("[OPTFRONT] cond_expr={cond_expr:?}\n[OPTFRONT] vec={vec:?}");
        }

        let is_empty = SorobanExpr::MethodCall {
            object: Box::new(vec.clone()),
            method: "is_empty".to_string(),
            args: Vec::new(),
        };
        let first = SorobanExpr::MethodCall {
            object: Box::new(vec),
            method: "first_unchecked".to_string(),
            args: Vec::new(),
        };
        cov_mark::hit!(option_front_if_recovered);
        Some(SorobanStmt::If {
            condition: is_empty,
            then_body: vec![SorobanStmt::Return(Some(SorobanExpr::None))],
            else_body: vec![SorobanStmt::Return(Some(SorobanExpr::Some(Box::new(
                first,
            ))))],
        })
    }

    /// Try to recognize a nested block chain with br_table as a match/switch pattern.
    ///
    /// Pattern: nested Block nodes with BrTable at the innermost level.
    /// Each block's "tail" after its inner block is a case body.
    fn try_recognize_match(
        &mut self,
        body: &[super::structurize::StructuredBlock],
    ) -> Option<SorobanStmt> {
        use super::structurize::StructuredBlock;

        // Collect nested blocks and their trailing instructions
        let mut blocks: Vec<&[StructuredBlock]> = Vec::new(); // case bodies (tails)
        let mut current = body;

        // Unwrap nested Block chain.
        // Always push the tail (even if empty) to preserve index alignment with br_table targets.
        while let Some((StructuredBlock::Block { body: inner, .. }, tail)) = current.split_first() {
            blocks.push(tail);
            current = inner;
        }

        // Need at least 1 case body and the innermost should contain BrTable
        if blocks.is_empty() {
            return None;
        }

        if std::env::var("DBG_TRACE").is_ok() {
            let summ = |bs: &[StructuredBlock]| -> String {
                bs.iter()
                    .map(|b| match b {
                        StructuredBlock::Block { .. } => "Block".to_string(),
                        StructuredBlock::Loop { .. } => "Loop".to_string(),
                        StructuredBlock::IfElse { .. } => "IfElse".to_string(),
                        StructuredBlock::SafetyNetUnreachable => "SafetyNet".to_string(),
                        StructuredBlock::Instruction(i) => format!("{i:?}"),
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            eprintln!(
                "[DBG_TRACE] try_recognize_match: depth={} current=[{}]",
                blocks.len(),
                summ(current)
            );
            let has_brtable = current.iter().any(|b| {
                matches!(
                    b,
                    StructuredBlock::Instruction(crate::wasm::ir::WasmInstr::BrTable { .. })
                )
            });
            eprintln!("[DBG_TRACE]   br_table directly in current? {has_brtable}");
        }

        // Find BrTable in the innermost block
        let br_table = current.iter().find_map(|b| {
            if let StructuredBlock::Instruction(crate::wasm::ir::WasmInstr::BrTable {
                targets,
                default,
            }) = b
            {
                Some((targets.clone(), *default))
            } else {
                None
            }
        })?;

        let (targets, default_target) = br_table;

        // Lift the innermost pre-br_table instructions to get the scrutinee
        let pre_br_instrs: Vec<_> = current
            .iter()
            .take_while(|b| {
                !matches!(
                    b,
                    StructuredBlock::Instruction(crate::wasm::ir::WasmInstr::BrTable { .. })
                )
            })
            .collect();

        let mut pre_ctx = self.child_context();
        for instr in &pre_br_instrs {
            if let StructuredBlock::Instruction(i) = instr {
                pre_ctx.lift_instruction(i);
            }
        }

        // Propagate enum match recovery state from the child context.
        // `symbol_index_in_linear_memory` sets these during pre-br lifting.
        if pre_ctx.enum_cases.is_some() {
            self.enum_cases = pre_ctx.enum_cases.take();
        }
        if pre_ctx.enum_match_scrutinee.is_some() {
            self.enum_match_scrutinee = pre_ctx.enum_match_scrutinee.take();
        }

        // The scrutinee is on the stack (it's what br_table switches on)
        let scrutinee_val = pre_ctx.stack.pop().unwrap_or(StackVal::Unknown);
        let mut scrutinee = stack_val_to_expr(
            &scrutinee_val,
            self.params,
            self.registry,
            Some(&self.frame_slots.borrow()),
        );
        self.stmts.extend(pre_ctx.stmts);
        self.locals = pre_ctx.locals;
        self.found_host_calls |= pre_ctx.found_host_calls;

        // Reverse blocks since they were collected outermost-first
        blocks.reverse();

        // Try to resolve enum variant names: prefer enum_cases from
        // symbol_index_in_linear_memory, fall back to integer enum heuristic.
        let enum_info = if let Some(ref cases) = self.enum_cases {
            // Look up the union type whose variants match these names
            if let Some((type_name, has_data)) = self.registry.find_union_by_variants(cases) {
                // Replace scrutinee with the actual parameter being matched
                if let Some(ref param_expr) = self.enum_match_scrutinee {
                    scrutinee = param_expr.clone();
                    // Track this usage for the cycling counter
                    if let SorobanExpr::Param(_) = param_expr {
                        *self
                            .enum_match_counter
                            .borrow_mut()
                            .entry(type_name.clone())
                            .or_insert(0) += 1;
                    }
                }
                Some((type_name, cases.clone(), has_data))
            } else {
                // Variant names found but no matching union — try as plain enum info
                None
            }
        } else {
            None
        };
        // Fall back to integer enum resolution if no enum_cases.
        // Pass the number of distinct non-default targets so the heuristic only
        // matches enums whose variant count equals the br_table arm count.
        let num_distinct_targets = {
            let mut ts: Vec<u32> = targets
                .iter()
                .copied()
                .filter(|&t| t != default_target)
                .collect();
            ts.sort();
            ts.dedup();
            ts.len()
        };
        let int_enum_info = if enum_info.is_none() {
            self.try_resolve_enum_for_scrutinee(&scrutinee, num_distinct_targets)
        } else {
            None
        };

        // Recover scrutinee from parameter type when the heuristic found a
        // matching type but the scrutinee carries no usable discriminant — either
        // unknown, or a folded discriminant constant (udt::add; see
        // `is_recoverable_scrutinee`). Recovering to the `Param` also stops
        // `fold_constant_matches` from collapsing the match on the stale constant.
        if let Some((ref type_name, _, _)) = int_enum_info
            && is_recoverable_scrutinee(&scrutinee)
        {
            let matching_params: Vec<&str> = self
                .params
                .iter()
                .filter_map(|p| {
                    if let ScSpecTypeDef::Udt(udt) = &p.type_def
                        && udt.name.to_utf8_string().ok().as_deref() == Some(type_name.as_str())
                    {
                        return Some(p.name.as_str());
                    }
                    None
                })
                .collect();
            if !matching_params.is_empty() {
                let mut counter_map = self.enum_match_counter.borrow_mut();
                let counter = counter_map.entry(type_name.clone()).or_insert(0);
                let idx = *counter % matching_params.len();
                scrutinee = SorobanExpr::Param(matching_params[idx].to_string());
                *counter += 1;
            }
        }

        // Clear enum_cases after use
        self.enum_cases = None;
        self.enum_match_scrutinee = None;

        // Build match arms: group discriminants by target block index
        let num_blocks = blocks.len();
        let mut block_to_discriminants: std::collections::HashMap<u32, Vec<usize>> =
            std::collections::HashMap::new();
        for (discriminant, &target) in targets.iter().enumerate() {
            block_to_discriminants
                .entry(target)
                .or_default()
                .push(discriminant);
        }

        // Sort by first discriminant in each group for deterministic order
        let mut sorted_groups: Vec<(u32, Vec<usize>)> =
            block_to_discriminants.into_iter().collect();
        sorted_groups.sort_by_key(|(_, discs)| discs[0]);

        let mut arms: Vec<MatchArm> = Vec::new();

        // Compute the range of arm targets (excluding default) to identify continuation blocks.
        // Continuation blocks are those beyond the arm targets but not the default/error blocks.
        let max_arm_target = targets
            .iter()
            .copied()
            .filter(|&t| t != default_target)
            .max()
            .unwrap_or(0) as usize;
        let default_idx = default_target as usize;

        let _pre_match_locals = self.locals.clone();
        let mut _arm_locals_data: Vec<(u32, Vec<usize>, Vec<StackVal>, bool)> = Vec::new();

        for (target, discriminants) in &sorted_groups {
            let target_idx = *target as usize;
            if target_idx >= num_blocks {
                _arm_locals_data.push((*target, discriminants.clone(), self.locals.clone(), true));
                continue;
            }

            // Lift case body
            // Record parent stack depth so we can distinguish values pushed BY the case
            // body from values inherited from the parent context (the child starts with a
            // clone of self.stack, so inherited values are NOT the case's own return value).
            let parent_stack_len = self.stack.len();
            let mut case_ctx = self.child_context();
            case_ctx.lift_structured(blocks[target_idx]);

            // Continuation reattachment: find continuation blocks targeted by Br/BrIf
            // instructions within this arm and lift them as part of the arm body.
            // Only attach continuations when the arm body is otherwise empty
            // (the arm delegates entirely to the continuation).
            let continuations = Self::find_continuation_targets(
                blocks[target_idx],
                target_idx,
                max_arm_target,
                default_idx,
                num_blocks,
            );
            for cont_idx in &continuations {
                case_ctx.lift_structured(blocks[*cont_idx]);
            }
            self.found_host_calls |= case_ctx.found_host_calls;
            // Apply implicit return: if the function has a return type and the case body
            // pushed a new value onto the stack (beyond the inherited parent depth), emit
            // it as a return statement.
            // This handles WASM `Return` instructions inside br_table case bodies
            // (WasmInstr::Return does nothing in lift_instruction, leaving the value on the stack).
            if self.return_type.is_some()
                && !matches!(case_ctx.stmts.last(), Some(SorobanStmt::Return(_)))
                && case_ctx.stack.len() > parent_stack_len
            // case body pushed a new value
                && let Some(top) = case_ctx.stack.last()
            {
                let expr = stack_val_to_expr(
                    top,
                    self.params,
                    self.registry,
                    Some(&self.frame_slots.borrow()),
                );
                if !matches!(expr, SorobanExpr::Void | SorobanExpr::UnknownVal) {
                    if matches!(top, StackVal::HostCallResult(_))
                        && matches!(case_ctx.stmts.last(), Some(SorobanStmt::Expr(_)))
                    {
                        case_ctx.stmts.pop();
                    }
                    case_ctx.stmts.push(SorobanStmt::Return(Some(expr)));
                }
            }

            // Fix 3a: Recover return values stored to locals (not left on stack).
            // Pattern: I64Const(val); LocalSet(N); Br(K) — value written to a local,
            // stack doesn't grow, so the stack-based check above misses it.
            if case_ctx.stmts.is_empty()
                && self.return_type.is_some()
                && case_ctx.stack.len() <= parent_stack_len
            {
                for (idx, case_local) in case_ctx.locals.iter().enumerate() {
                    // Body-local slots are always eligible. A WASM *param* slot is
                    // eligible only when it has been repurposed to stage a constant
                    // return value: the SDK reuses the `env` slot (local 0) as scratch,
                    // writing the `Ok(..)`/`Err(..)` Val constant there before the shared
                    // tail `local.get; return` (the errors fixture's `Flag::A` arm). A
                    // param slot still carrying its parameter value is left alone.
                    if idx < self.num_wasm_params as usize
                        && !matches!(case_local, StackVal::I64(_) | StackVal::I32(_))
                    {
                        continue; // param slot still flows the parameter — skip
                    }
                    if let Some(parent_local) = self.locals.get(idx)
                        && case_local != parent_local
                    {
                        let expr = stack_val_to_expr(
                            case_local,
                            self.params,
                            self.registry,
                            Some(&self.frame_slots.borrow()),
                        );
                        if !matches!(expr, SorobanExpr::Void | SorobanExpr::UnknownVal) {
                            cov_mark::hit!(arm_return_from_reused_param_slot);
                            case_ctx.stmts.push(SorobanStmt::Return(Some(expr)));
                            break;
                        }
                    }
                }
            }

            _arm_locals_data.push((
                *target,
                discriminants.clone(),
                case_ctx.locals.clone(),
                false,
            ));
            let case_stmts = case_ctx.stmts;

            // Create pattern for each discriminant
            for &disc in discriminants {
                let pattern = if let Some((ref type_name, ref variants, ref has_data)) = enum_info {
                    if disc < variants.len() {
                        let bindings = if *has_data.get(disc).unwrap_or(&false) {
                            vec!["_".to_string()]
                        } else {
                            Vec::new()
                        };
                        MatchPattern::EnumVariant {
                            type_name: type_name.clone(),
                            variant: variants[disc].clone(),
                            bindings,
                        }
                    } else {
                        MatchPattern::Wildcard
                    }
                } else if let Some((ref type_name, ref variants, ref has_data)) = int_enum_info {
                    if disc < variants.len() {
                        let bindings = if *has_data.get(disc).unwrap_or(&false) {
                            vec!["_".to_string()]
                        } else {
                            Vec::new()
                        };
                        MatchPattern::EnumVariant {
                            type_name: type_name.clone(),
                            variant: variants[disc].clone(),
                            bindings,
                        }
                    } else {
                        MatchPattern::Wildcard
                    }
                } else {
                    MatchPattern::Literal(SorobanExpr::U32Literal(disc as u32))
                };

                arms.push(MatchArm {
                    pattern,
                    body: case_stmts.clone(),
                });
            }
        }

        // Deduplicate consecutive Wildcard arms (from out-of-range discriminants
        // targeting the same block) — keep only the first one.
        arms.dedup_by(|b, a| {
            matches!(a.pattern, MatchPattern::Wildcard)
                && matches!(b.pattern, MatchPattern::Wildcard)
        });

        // Handle the default target as a wildcard arm
        let default_idx = default_target as usize;
        #[allow(unused_variables)]
        let mut default_arm_locals: Option<Vec<StackVal>> = None;
        if default_idx < blocks.len() {
            let already_covered = sorted_groups.iter().any(|(t, _)| *t == default_target);
            if !already_covered {
                let parent_stack_len = self.stack.len();
                let mut case_ctx = self.child_context();
                case_ctx.lift_structured(blocks[default_idx]);
                self.found_host_calls |= case_ctx.found_host_calls;
                if self.return_type.is_some()
                    && !matches!(case_ctx.stmts.last(), Some(SorobanStmt::Return(_)))
                    && case_ctx.stack.len() > parent_stack_len
                    && let Some(top) = case_ctx.stack.last()
                {
                    let expr = stack_val_to_expr(
                        top,
                        self.params,
                        self.registry,
                        Some(&self.frame_slots.borrow()),
                    );
                    if !matches!(expr, SorobanExpr::Void | SorobanExpr::UnknownVal) {
                        case_ctx.stmts.push(SorobanStmt::Return(Some(expr)));
                    }
                }
                // Local-modification recovery for default arm (same as case arms)
                if case_ctx.stmts.is_empty()
                    && self.return_type.is_some()
                    && case_ctx.stack.len() <= parent_stack_len
                {
                    for (idx, case_local) in case_ctx.locals.iter().enumerate() {
                        if idx < self.num_wasm_params as usize {
                            continue;
                        }
                        if let Some(parent_local) = self.locals.get(idx)
                            && case_local != parent_local
                        {
                            let expr = stack_val_to_expr(
                                case_local,
                                self.params,
                                self.registry,
                                Some(&self.frame_slots.borrow()),
                            );
                            if !matches!(expr, SorobanExpr::Void | SorobanExpr::UnknownVal) {
                                case_ctx.stmts.push(SorobanStmt::Return(Some(expr)));
                                break;
                            }
                        }
                    }
                }
                default_arm_locals = Some(case_ctx.locals.clone());
                if !case_ctx.stmts.is_empty() {
                    arms.push(MatchArm {
                        pattern: MatchPattern::Wildcard,
                        body: case_ctx.stmts,
                    });
                }
            }
        }

        // === Phi-merge detection ===
        let num_locals = self.locals.len();
        let mut phi_local: Option<usize> = None;

        {
            let mut best_candidate: Option<(usize, usize)> = None;
            for idx in 0..num_locals {
                let parent_val = match _pre_match_locals.get(idx) {
                    Some(v) => v,
                    None => continue,
                };
                // Param slots are normally excluded from phi-merge. But the SDK
                // reuses a dead param slot as the result accumulator (udt::add:
                // `let a = match a { … }` writes its result into the slot that
                // held `b`, after `b` was already destructured). Only consider a
                // param slot when its pre-match value is a plain constant — the
                // `match`'s default-arm init (`i64.const 0; local.set 1`) staged
                // before the dispatch. A slot still flowing the parameter or any
                // derived value (e.g. constructor's `key.get(0)`) is left alone.
                // Mirrors the reused-param-slot gate in the Fix-3a recovery above.
                if idx < self.num_wasm_params as usize
                    && !matches!(parent_val, StackVal::I64(_) | StackVal::I32(_))
                {
                    continue;
                }
                let modifying: Vec<&(u32, Vec<usize>, Vec<StackVal>, bool)> = _arm_locals_data
                    .iter()
                    .filter(|(_, _, _, is_escape)| !is_escape)
                    .filter(|(_, _, locals, _)| {
                        locals.get(idx).map(|v| v != parent_val).unwrap_or(false)
                    })
                    .collect();
                let count = modifying.len();
                if count >= 2 {
                    // Only block phi-merge if the modifying arms have Returns
                    // from meaningful host calls (not spurious stack-value Returns).
                    // Check: do the modifying arms' corresponding match arms have Returns
                    // that contain host calls, storage ops, or method calls?
                    let has_substantial_return = modifying.iter().any(|(target, _, _, _)| {
                        if let Some((_, discs)) = sorted_groups.iter().find(|(t, _)| *t == *target)
                        {
                            if let Some(&first_disc) = discs.first() {
                                arms.iter().any(|arm| {
                                    let disc_matches = match &arm.pattern {
                                        MatchPattern::Literal(SorobanExpr::U32Literal(v)) => {
                                            *v == first_disc as u32
                                        }
                                        MatchPattern::EnumVariant { variant, .. } => {
                                            if let Some((_, ref variants, _)) = enum_info {
                                                variants
                                                    .get(first_disc)
                                                    .map(|v| v == variant)
                                                    .unwrap_or(false)
                                            } else if let Some((_, ref variants, _)) = int_enum_info
                                            {
                                                variants
                                                    .get(first_disc)
                                                    .map(|v| v == variant)
                                                    .unwrap_or(false)
                                            } else {
                                                false
                                            }
                                        }
                                        _ => false,
                                    };
                                    disc_matches
                                        && arm.body.iter().any(|s| match s {
                                            SorobanStmt::Return(Some(expr)) => {
                                                Self::expr_is_host_call(expr)
                                            }
                                            _ => false,
                                        })
                                })
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    });
                    if !has_substantial_return
                        && best_candidate.map(|(_, best)| count > best).unwrap_or(true)
                    {
                        best_candidate = Some((idx, count));
                    }
                }
            }
            if let Some((idx, _)) = best_candidate {
                phi_local = Some(idx);
            }
        }

        // Don't phi-merge on constant-scrutinee matches — these are optimization
        // artifacts that will be folded away by fold_constant_matches.
        let scrutinee_is_literal = matches!(
            scrutinee,
            SorobanExpr::I32Literal(_)
                | SorobanExpr::U32Literal(_)
                | SorobanExpr::I64Literal(_)
                | SorobanExpr::U64Literal(_)
                | SorobanExpr::I128Literal(_)
                | SorobanExpr::U128Literal(_)
        );
        if scrutinee_is_literal {
            phi_local = None;
        }

        if let Some(phi_idx) = phi_local {
            cov_mark::hit!(phi_merge_hit);
            // Emit `let mut var_N = <init>;` before the match
            let init_expr = stack_val_to_arith_expr(
                &_pre_match_locals[phi_idx],
                self.params,
                self.registry,
                Some(&self.frame_slots.borrow()),
            );
            self.stmts.push(SorobanStmt::Let {
                name: format!("var_{}", phi_idx),
                mutable: true,
                value: init_expr,
            });

            // Replace Fix 3a Returns with Assigns in modifying arms
            for (_target, discriminants, arm_lcls, is_escape) in &_arm_locals_data {
                if *is_escape {
                    for &disc in discriminants {
                        let pattern =
                            if let Some((ref type_name, ref variants, ref has_data)) = enum_info {
                                if disc < variants.len() {
                                    let bindings = if *has_data.get(disc).unwrap_or(&false) {
                                        vec!["_".to_string()]
                                    } else {
                                        Vec::new()
                                    };
                                    MatchPattern::EnumVariant {
                                        type_name: type_name.clone(),
                                        variant: variants[disc].clone(),
                                        bindings,
                                    }
                                } else {
                                    continue;
                                }
                            } else if let Some((ref type_name, ref variants, ref has_data)) =
                                int_enum_info
                            {
                                if disc < variants.len() {
                                    let bindings = if *has_data.get(disc).unwrap_or(&false) {
                                        vec!["_".to_string()]
                                    } else {
                                        Vec::new()
                                    };
                                    MatchPattern::EnumVariant {
                                        type_name: type_name.clone(),
                                        variant: variants[disc].clone(),
                                        bindings,
                                    }
                                } else {
                                    continue;
                                }
                            } else {
                                continue;
                            };
                        arms.push(MatchArm {
                            pattern,
                            body: Vec::new(),
                        });
                    }
                    continue;
                }
                if let Some(arm_val) = arm_lcls.get(phi_idx)
                    && arm_val != &_pre_match_locals[phi_idx]
                {
                    let val_expr = stack_val_to_expr(
                        arm_val,
                        self.params,
                        self.registry,
                        Some(&self.frame_slots.borrow()),
                    );
                    for &disc in discriminants {
                        for arm in arms.iter_mut() {
                            let matches_disc = match &arm.pattern {
                                MatchPattern::Literal(SorobanExpr::U32Literal(v)) => {
                                    *v == disc as u32
                                }
                                MatchPattern::EnumVariant { variant, .. } => {
                                    if let Some((_, ref variants, _)) = enum_info {
                                        variants.get(disc).map(|v| v == variant).unwrap_or(false)
                                    } else if let Some((_, ref variants, _)) = int_enum_info {
                                        variants.get(disc).map(|v| v == variant).unwrap_or(false)
                                    } else {
                                        false
                                    }
                                }
                                _ => false,
                            };
                            if matches_disc {
                                arm.body.retain(|s| !matches!(s, SorobanStmt::Return(_)));
                                arm.body.push(SorobanStmt::Assign {
                                    target: format!("var_{}", phi_idx),
                                    value: val_expr.clone(),
                                });
                            }
                        }
                    }
                }
            }

            // Check default arm
            if let Some(ref dlcls) = default_arm_locals
                && let Some(arm_val) = dlcls.get(phi_idx)
                && arm_val != &_pre_match_locals[phi_idx]
            {
                let val_expr = stack_val_to_expr(
                    arm_val,
                    self.params,
                    self.registry,
                    Some(&self.frame_slots.borrow()),
                );
                for arm in arms.iter_mut() {
                    if matches!(arm.pattern, MatchPattern::Wildcard) {
                        arm.body.retain(|s| !matches!(s, SorobanStmt::Return(_)));
                        arm.body.push(SorobanStmt::Assign {
                            target: format!("var_{}", phi_idx),
                            value: val_expr.clone(),
                        });
                    }
                }
            }

            // Update self.locals for post-match code
            if let Some(local) = self.locals.get_mut(phi_idx) {
                *local = StackVal::LetBinding(phi_idx as u32);
            }
            // Protect the phi-merged local from being overwritten by the
            // shared merge code that follows the br_table block chain.
            // The merge code recomputes the same per-arm values via
            // branch-sequential execution (last branch wins), producing
            // a corrupted constant. Without protection, LocalSet overwrites
            // the LetBinding, causing the return expression to reference
            // the wrong variable.
            self.phi_protected_locals.push(phi_idx as u32);
        }

        // Filter out empty-body arms (unrecoverable case bodies). An sret/Result
        // dispatch always keeps both Ok/Err arms even if one body is empty, so the
        // reconstructed dispatch (and its return path) is never dropped.
        let scrutinee_is_sret = matches!(scrutinee, SorobanExpr::SretResult(_));
        arms.retain(|arm| {
            !arm.body.is_empty()
                || (phi_local.is_some() && matches!(arm.pattern, MatchPattern::EnumVariant { .. }))
                || (scrutinee_is_sret && matches!(arm.pattern, MatchPattern::EnumVariant { .. }))
        });

        if std::env::var("DBG_TRACE").is_ok() {
            eprintln!(
                "[DBG_TRACE] MATCH RESULT: scrutinee={scrutinee:?} phi_local={phi_local:?} arms={}",
                arms.len()
            );
            for (ai, arm) in arms.iter().enumerate() {
                eprintln!(
                    "[DBG_TRACE]   arm[{ai}] pat={:?} body_len={} body={:?}",
                    arm.pattern,
                    arm.body.len(),
                    arm.body
                );
            }
        }

        if arms.is_empty() {
            if std::env::var("DBG_TRACE").is_ok() {
                eprintln!("[DBG_TRACE] MATCH DISCARDED: arms empty (scrutinee={scrutinee:?})");
            }
            return None;
        }

        Some(SorobanStmt::Match { scrutinee, arms })
    }

    /// Find continuation block indices reachable from an arm body.
    ///
    /// In the match block chain, from `blocks[arm_idx]`, a `Br(N)` instruction
    /// at nesting depth D within the arm body targets `blocks[arm_idx + (N - D) + 1]`.
    /// Continuation blocks are those beyond the br_table target range
    /// (i.e., index > max_br_table_target) — they contain code that logically
    /// belongs to this arm but was placed outside by the LLVM backend for code sharing.
    /// Check if an expression is a "substantial" host call / storage / method call
    /// (as opposed to a simple literal or local reference).
    fn expr_is_host_call(expr: &SorobanExpr) -> bool {
        matches!(
            expr,
            SorobanExpr::StorageGet { .. }
                | SorobanExpr::StorageSet { .. }
                | SorobanExpr::StorageHas { .. }
                | SorobanExpr::StorageRemove { .. }
                | SorobanExpr::InvokeContract { .. }
                | SorobanExpr::TryInvokeContract { .. }
                | SorobanExpr::MethodCall { .. }
                | SorobanExpr::RawHostCall { .. }
        )
    }

    fn find_continuation_targets(
        arm_body: &[super::structurize::StructuredBlock],
        arm_index: usize,
        max_arm_target: usize,
        default_idx: usize,
        num_blocks: usize,
    ) -> Vec<usize> {
        let mut targets = Vec::new();
        Self::scan_br_targets(
            arm_body,
            arm_index,
            0,
            max_arm_target,
            default_idx,
            num_blocks,
            &mut targets,
        );
        targets.sort();
        targets.dedup();
        targets
    }

    fn scan_br_targets(
        body: &[super::structurize::StructuredBlock],
        arm_index: usize,
        nesting_depth: usize,
        max_arm_target: usize,
        default_idx: usize,
        num_blocks: usize,
        targets: &mut Vec<usize>,
    ) {
        use super::structurize::StructuredBlock;
        use crate::wasm::ir::WasmInstr;

        for block in body {
            match block {
                StructuredBlock::Instruction(WasmInstr::Br(n))
                | StructuredBlock::Instruction(WasmInstr::BrIf(n)) => {
                    let is_unconditional =
                        matches!(block, StructuredBlock::Instruction(WasmInstr::Br(_)));
                    let n = *n as usize;
                    if n > nesting_depth {
                        let match_target = arm_index + (n - nesting_depth) + 1;
                        // Continuation blocks are beyond the arm targets but
                        // within the match scope. When default_idx <= max_arm_target
                        // (e.g., default targets the same block as arm 0), use
                        // num_blocks as the upper bound but only for unconditional
                        // branches (conditional branches in this case target error
                        // handlers, not continuations).
                        let upper = if default_idx > max_arm_target {
                            default_idx
                        } else if is_unconditional {
                            num_blocks
                        } else {
                            // BrIf with relaxed bounds: skip (would hit error block)
                            continue;
                        };
                        if match_target > max_arm_target
                            && match_target < upper
                            && match_target < num_blocks
                        {
                            targets.push(match_target);
                        }
                    }
                }
                StructuredBlock::Block { body: inner, .. }
                | StructuredBlock::Loop { body: inner, .. } => {
                    Self::scan_br_targets(
                        inner,
                        arm_index,
                        nesting_depth + 1,
                        max_arm_target,
                        default_idx,
                        num_blocks,
                        targets,
                    );
                }
                StructuredBlock::IfElse {
                    then_body,
                    else_body,
                    ..
                } => {
                    Self::scan_br_targets(
                        then_body,
                        arm_index,
                        nesting_depth + 1,
                        max_arm_target,
                        default_idx,
                        num_blocks,
                        targets,
                    );
                    Self::scan_br_targets(
                        else_body,
                        arm_index,
                        nesting_depth + 1,
                        max_arm_target,
                        default_idx,
                        num_blocks,
                        targets,
                    );
                }
                _ => {}
            }
        }
    }

    /// Try to resolve enum variant names for a match scrutinee.
    /// Returns (type_name, variant_names, has_data_per_variant) if the scrutinee
    /// can be mapped to a known enum or union.
    fn try_resolve_enum_for_scrutinee(
        &self,
        scrutinee: &SorobanExpr,
        num_targets: usize,
    ) -> Option<(String, Vec<String>, Vec<bool>)> {
        // An sret/Result discriminant: a 2-way dispatch on a call's `Result<T, E>`
        // written into a frame slot. Reconstruct as `Ok`/`Err` (both data-carrying)
        // so the success *and* error paths — and the post-dispatch return — survive
        // instead of being dropped as an unresolved (`UnknownVal`) scrutinee. Checked
        // before the integer-enum loop so a same-arity UDT enum can't shadow it.
        if matches!(scrutinee, SorobanExpr::SretResult(_)) {
            return Some((
                "Result".to_string(),
                vec!["Ok".to_string(), "Err".to_string()],
                vec![true, true],
            ));
        }

        // A clean `i32` literal scrutinee is a *known* br_table selector — a folded
        // discriminant or a seeded `Option`-decode tag — so it must fold to its
        // single live arm (`fold_constant_matches`), not resolve to an enum. The
        // integer-enum loop below would otherwise grab the first registry enum with
        // enough variants and mislabel it (e.g. `1 == LiquidityPoolType::ConstantProduct`),
        // which also blocks the constant fold. Mirrors the literal-scrutinee guard
        // the union path already applies.
        if matches!(scrutinee, SorobanExpr::I32Literal(_)) {
            return None;
        }

        // Prefer an enum/union that matches one of THIS function's parameters: a
        // br_table is almost always dispatching on a parameter, and the param's
        // declared type disambiguates same-arity candidates. Without this, the
        // first registry integer enum with enough variants wins and mislabels the
        // variants — e.g. the `recursive_enum` match on `RecursiveEnum` was resolved
        // to the unrelated 2-variant integer enum `UdtEnum2`, leaking a
        // `todo!("unknown value")`. Unions are only considered for an unknown
        // scrutinee, mirroring the fallback union path below (a known literal
        // scrutinee means a result-selecting br_table, not a discriminant match).
        for p in self.params {
            let ScSpecTypeDef::Udt(udt) = &p.type_def else {
                continue;
            };
            let Ok(tname) = udt.name.to_utf8_string() else {
                continue;
            };
            if let Some(spec) = self.registry.enums.get(&tname) {
                let mut variants: Vec<(u32, String)> = spec
                    .cases
                    .iter()
                    .filter_map(|c| c.name.to_utf8_string().ok().map(|n| (c.value, n)))
                    .collect();
                if !variants.is_empty() && variants.len() >= num_targets {
                    variants.sort_by_key(|(v, _)| *v);
                    let has_data = vec![false; variants.len()];
                    let ordered = variants.into_iter().map(|(_, n)| n).collect();
                    cov_mark::hit!(enum_resolved_by_param_type);
                    return Some((tname, ordered, has_data));
                }
            }
            if is_recoverable_scrutinee(scrutinee)
                && let Some(spec) = self.registry.unions.get(&tname)
            {
                let mut variants: Vec<String> = Vec::new();
                let mut has_data: Vec<bool> = Vec::new();
                for case in spec.cases.iter() {
                    match case {
                        stellar_xdr::ScSpecUdtUnionCaseV0::VoidV0(v) => {
                            if let Ok(n) = v.name.to_utf8_string() {
                                variants.push(n);
                                has_data.push(false);
                            }
                        }
                        stellar_xdr::ScSpecUdtUnionCaseV0::TupleV0(t) => {
                            if let Ok(n) = t.name.to_utf8_string() {
                                variants.push(n);
                                has_data.push(true);
                            }
                        }
                    }
                }
                if !variants.is_empty() && variants.len() >= num_targets {
                    cov_mark::hit!(union_resolved_by_param_type);
                    return Some((tname, variants, has_data));
                }
            }
        }

        // Check all integer enums in the registry.
        // Only match when the variant count >= the br_table target count
        // (some variants may share arms). This prevents misidentifying union
        // br_tables (many targets) as small integer enum matches.
        for (name, spec) in &self.registry.enums {
            let mut variants: Vec<(u32, String)> = Vec::new();
            for case in spec.cases.iter() {
                if let Ok(vname) = case.name.to_utf8_string() {
                    variants.push((case.value, vname));
                }
            }
            if !variants.is_empty() && variants.len() >= num_targets {
                variants.sort_by_key(|(v, _)| *v);
                let has_data = vec![false; variants.len()];
                let ordered: Vec<String> = variants.into_iter().map(|(_, n)| n).collect();
                return Some((name.clone(), ordered, has_data));
            }
        }

        // Also check unions (data-carrying enums like UdtEnum), but only when
        // the scrutinee is unknown — a known literal scrutinee (e.g., `match 2`)
        // indicates a result-selecting br_table, not a discriminant match.
        if !matches!(scrutinee, SorobanExpr::UnknownVal) {
            return None;
        }
        use stellar_xdr::ScSpecUdtUnionCaseV0;
        for (name, spec) in &self.registry.unions {
            let mut variants: Vec<String> = Vec::new();
            let mut has_data: Vec<bool> = Vec::new();
            for case in spec.cases.iter() {
                match case {
                    ScSpecUdtUnionCaseV0::VoidV0(v) => {
                        if let Ok(vname) = v.name.to_utf8_string() {
                            variants.push(vname);
                            has_data.push(false);
                        }
                    }
                    ScSpecUdtUnionCaseV0::TupleV0(t) => {
                        if let Ok(vname) = t.name.to_utf8_string() {
                            variants.push(vname);
                            has_data.push(true);
                        }
                    }
                }
            }
            if !variants.is_empty() && variants.len() >= num_targets {
                return Some((name.clone(), variants, has_data));
            }
        }

        None
    }

    /// Process a Block body containing multiple BrIf(0) guards iteratively.
    ///
    /// Instead of finding the FIRST BrIf(0) and lifting everything after it as
    /// a single body (which causes branch-sequential execution corruption when
    /// subsequent BrIf(0)s are inside that body), this processes each segment
    /// between BrIf(0)s independently:
    ///
    /// 1. For each BrIf(0), lift the preceding segment to compute the condition
    /// 2. Classify the condition: constant (fold), unknown (skip), or real guard
    /// 3. Real guards emit `if cond { panic!() }`
    /// 4. The tail after all guards is the actual function body
    fn process_guard_brif_chain(
        &mut self,
        body: &[super::structurize::StructuredBlock],
        brif_positions: &[usize],
    ) {
        let mut cursor = 0;

        for &brif_pos in brif_positions {
            // Process segment between cursor and this BrIf
            let segment = &body[cursor..brif_pos];
            cursor = brif_pos + 1;

            // Lift segment in child context to compute condition
            let mut seg_ctx = self.child_context();
            seg_ctx.lift_structured(segment);
            let cond_val = seg_ctx.stack.pop().unwrap_or(StackVal::Unknown);

            // Splice segment state back (condition computation side effects)
            self.stack = seg_ctx.stack;
            self.locals = seg_ctx.locals;
            self.memory_stores = seg_ctx.memory_stores;
            let seg_stmts = strip_return_panic_pairs_in_guard(seg_ctx.stmts);
            let seg_stmts = strip_nonfinal_void_returns(seg_stmts);
            self.stmts.extend(seg_stmts);
            self.found_host_calls |= seg_ctx.found_host_calls;

            // Classify condition
            let const_val = match &cond_val {
                StackVal::I32(v) => Some(*v as i64),
                StackVal::I64(v) => Some(*v),
                _ => None,
            };

            if const_val.is_some() {
                // Constant conditions in guard chains are type-check preamble
                // artifacts: the lifter's static evaluation can resolve tag
                // comparisons to constants, but the runtime behavior depends
                // on actual parameter values.  Treat both true and false as
                // pass-through (same as guard_block_depth > 0 behavior in
                // the flat BrIf handler).
                continue;
            }

            if stack_val_contains_unknown(&cond_val) {
                continue; // Dispatch preamble — always passes
            }

            // Skip Val-level preamble checks: comparisons involving constants
            // that are multiples of 2^32 (Soroban Val encoding artifacts).
            // These are SDK-generated checks on raw Val-encoded values (type
            // tags, field lengths, etc.) before Val conversion.
            if stack_val_has_val_constant(&cond_val) {
                continue;
            }

            // Real guard: emit if cond { panic!() }
            let condition = stack_val_to_expr(
                &cond_val,
                self.params,
                self.registry,
                Some(&self.frame_slots.borrow()),
            );
            self.stmts.push(SorobanStmt::If {
                condition,
                then_body: vec![SorobanStmt::Expr(SorobanExpr::Panic)],
                else_body: Vec::new(),
            });
        }

        // Process tail (function body after all guards)
        let tail = &body[cursor..];
        if !tail.is_empty() {
            let mut tail_ctx = self.child_context();
            tail_ctx.guard_block_depth += 1;
            tail_ctx.lift_structured(tail);
            let tail_stmts = strip_return_panic_pairs_in_guard(tail_ctx.stmts);
            let tail_stmts = strip_nonfinal_void_returns(tail_stmts);
            self.stack = tail_ctx.stack;
            self.locals = tail_ctx.locals;
            self.memory_stores = tail_ctx.memory_stores;
            self.stmts.extend(tail_stmts);
            self.found_host_calls |= tail_ctx.found_host_calls;
        }
    }

    /// Lift structured blocks inside a loop, converting branch instructions
    /// to break/continue statements.
    fn lift_structured_loop(&mut self, blocks: &[super::structurize::StructuredBlock]) {
        use super::structurize::StructuredBlock;

        for block in blocks {
            match block {
                StructuredBlock::Instruction(instr) => {
                    use crate::wasm::ir::WasmInstr;
                    match instr {
                        WasmInstr::Br(0) => {
                            // br 0 in loop = continue (jump to loop header)
                            self.stmts.push(SorobanStmt::Continue);
                        }
                        WasmInstr::Br(_) => {
                            // br N>0 = break out of enclosing scope
                            self.stmts.push(SorobanStmt::Break);
                        }
                        WasmInstr::BrIf(0) => {
                            // br_if 0 = conditional continue
                            let cond_val = self.stack.pop().unwrap_or(StackVal::Unknown);
                            let condition = stack_val_to_expr(
                                &cond_val,
                                self.params,
                                self.registry,
                                Some(&self.frame_slots.borrow()),
                            );
                            self.stmts.push(SorobanStmt::If {
                                condition,
                                then_body: vec![SorobanStmt::Continue],
                                else_body: Vec::new(),
                            });
                        }
                        WasmInstr::BrIf(_) => {
                            // br_if N>0 = conditional break
                            let cond_val = self.stack.pop().unwrap_or(StackVal::Unknown);
                            let condition = stack_val_to_expr(
                                &cond_val,
                                self.params,
                                self.registry,
                                Some(&self.frame_slots.borrow()),
                            );
                            self.stmts.push(SorobanStmt::If {
                                condition,
                                then_body: vec![SorobanStmt::Break],
                                else_body: Vec::new(),
                            });
                        }
                        _ => self.lift_instruction(instr),
                    }
                }
                StructuredBlock::Block { body, .. } => {
                    // Same three-part logic as lift_structured's Block handler:
                    // BrIf(0) inside a block exits the block (forward jump), NOT the loop.

                    // 1. Try match recognition (blocks inside loops can contain br_table)
                    if let Some(match_stmt) = self.try_recognize_match(body) {
                        self.stmts.push(match_stmt);
                        continue;
                    }

                    // 2. Check for block + br_if(0) -> if statement
                    if let Some(brif_pos) = body.iter().position(|b| {
                        matches!(
                            b,
                            StructuredBlock::Instruction(crate::wasm::ir::WasmInstr::BrIf(0))
                        )
                    }) {
                        let pre = &body[..brif_pos];
                        let post = &body[brif_pos + 1..];

                        // Lift pre-branch to get condition on stack
                        let mut pre_ctx = self.child_context();
                        pre_ctx.lift_structured(pre);

                        // Pop condition - br_if 0 means "branch OUT of block if true",
                        // so the remaining body runs when FALSE
                        let cond_val = pre_ctx.stack.pop().unwrap_or(StackVal::Unknown);

                        // Transfer pre_ctx state back
                        self.stack = pre_ctx.stack;
                        self.locals = pre_ctx.locals;
                        self.memory_stores = pre_ctx.memory_stores;
                        self.stmts.extend(pre_ctx.stmts);
                        self.found_host_calls |= pre_ctx.found_host_calls;

                        // Lift post-branch (block scope, not loop scope)
                        let mut body_ctx = self.child_context();
                        body_ctx.lift_structured(post);
                        let then_stmts = body_ctx.stmts;
                        self.found_host_calls |= body_ctx.found_host_calls;

                        // Inside a loop, block-exit conditions often involve loop
                        // variables with stale initial values. Treat these as
                        // always-pass to preserve the block body.
                        //
                        // - I32(0): always-pass (br_if never fires)
                        // - I32(nonzero): always-pass (stale loop variable)
                        // - Compare of two concrete constants: stale loop condition
                        // - Unknown-containing: dispatch preamble type-check
                        //
                        // Only emit an if-statement when the condition involves
                        // parameters or host call results (non-stale values).
                        let is_stale_loop_cond = matches!(&cond_val, StackVal::I32(_))
                            || stack_val_contains_unknown(&cond_val)
                            || stack_val_is_concrete_compare(&cond_val);

                        if is_stale_loop_cond {
                            self.stack = body_ctx.stack.clone();
                            self.locals = body_ctx.locals;
                            self.memory_stores = body_ctx.memory_stores;
                            self.stmts.extend(then_stmts);
                            // If body_ctx left a VecConstruct/StructConstruct on the
                            // stack (from a WASM Return at inline_depth=0) and the
                            // stmts only have trivial loop/continue/break patterns,
                            // emit the stack value as a Return. This recovers the
                            // init+work loop pattern where the real return value is
                            // constructed inside the loop's deferred code path.
                            if let Some(top) = body_ctx.stack.last()
                                && matches!(top, StackVal::HostCallResult(_))
                            {
                                let all_trivial = self.stmts.iter().all(|s| {
                                    matches!(
                                        s,
                                        SorobanStmt::Loop { .. }
                                            | SorobanStmt::Continue
                                            | SorobanStmt::Break
                                    )
                                });
                                if all_trivial {
                                    let expr = stack_val_to_expr(
                                        top,
                                        self.params,
                                        self.registry,
                                        Some(&self.frame_slots.borrow()),
                                    );
                                    self.stmts.push(SorobanStmt::Return(Some(expr)));
                                }
                            }
                        } else {
                            self.memory_stores = body_ctx.memory_stores;
                            let condition = stack_val_to_expr(
                                &cond_val,
                                self.params,
                                self.registry,
                                Some(&self.frame_slots.borrow()),
                            );
                            let negated = SorobanExpr::Not(Box::new(condition));
                            if !then_stmts.is_empty() {
                                self.stmts.push(SorobanStmt::If {
                                    condition: negated,
                                    then_body: then_stmts,
                                    else_body: Vec::new(),
                                });
                            }
                        }
                    } else {
                        // Regular block - transparent pass-through
                        self.lift_structured(body);
                    }
                }
                StructuredBlock::Loop { body, .. } => {
                    // Nested loop — same one-iteration-artifact discipline as
                    // the top-level loop site (no copy-loop model runs here,
                    // so body-written slots always stamp).
                    let loop_pre_wpos = self.slot_write_log.borrow().len();
                    let mut inner_ctx = self.child_context();
                    inner_ctx.loop_depth += 1;
                    inner_ctx.lift_structured_loop(body);
                    let inner_stmts = inner_ctx.stmts;
                    self.found_host_calls |= inner_ctx.found_host_calls;
                    self.taint_loop_variant_slots(loop_pre_wpos);
                    if !inner_stmts.is_empty() {
                        self.stmts.push(SorobanStmt::Loop { body: inner_stmts });
                    }
                }
                StructuredBlock::IfElse {
                    then_body,
                    else_body,
                    ..
                } => {
                    let cond_val = self.stack.pop().unwrap_or(StackVal::Unknown);
                    let condition = stack_val_to_expr(
                        &cond_val,
                        self.params,
                        self.registry,
                        Some(&self.frame_slots.borrow()),
                    );

                    let mut then_ctx = self.child_context();
                    then_ctx.lift_structured_loop(then_body);
                    let then_stmts = then_ctx.stmts;

                    let mut else_ctx = self.child_context();
                    else_ctx.lift_structured_loop(else_body);
                    let else_stmts = else_ctx.stmts;

                    self.found_host_calls |= then_ctx.found_host_calls | else_ctx.found_host_calls;

                    if !then_stmts.is_empty() || !else_stmts.is_empty() {
                        self.stmts.push(SorobanStmt::If {
                            condition,
                            then_body: then_stmts,
                            else_body: else_stmts,
                        });
                    }
                }
                StructuredBlock::SafetyNetUnreachable => {
                    // CFG analysis already proved this `unreachable` is dead;
                    // emit nothing (see lift_structured for the explainer).
                }
            }
        }
    }

    /// Try to lift a linear memory host call into a struct/tuple construction.
    fn try_lift_linear_memory_call(
        &mut self,
        host_fn: &HostFunction,
        args: &[SorobanExpr],
    ) -> Option<SorobanExpr> {
        match (&host_fn.module, host_fn.name.as_str()) {
            (HostModule::Map, "map_new_from_linear_memory") => self.try_lift_struct_construct(args),
            (HostModule::Vec, "vec_new_from_linear_memory") => self.try_lift_tuple_construct(args),
            (HostModule::Buf, "symbol_new_from_linear_memory") => {
                // symbol_new_from_linear_memory(lm_pos, len) — reads a symbol name
                // from the WASM data section as a UTF-8 string.
                if args.len() < 2 {
                    return None;
                }
                let ptr = extract_u32_from_expr(&args[0])?;
                let len = extract_u32_from_expr(&args[1])?;
                let name = self.wasm_module.data_sections.read_string(ptr, len)?;
                Some(SorobanExpr::SymbolLiteral(name))
            }
            (HostModule::Buf, "string_new_from_linear_memory") => {
                // string_new_from_linear_memory(lm_pos, len) — reads a string
                // from the WASM data section as a UTF-8 string.
                if args.len() < 2 {
                    return None;
                }
                let ptr = extract_u32_from_expr(&args[0])?;
                let len = extract_u32_from_expr(&args[1])?;
                let s = self.wasm_module.data_sections.read_string(ptr, len)?;
                Some(SorobanExpr::StringLiteral(s))
            }
            (HostModule::Buf, "symbol_index_in_linear_memory") => {
                // symbol_index_in_linear_memory(discriminant, cases_ptr, count)
                // Returns the index of `discriminant` in the CASES array.
                // Used by SDK for matching on `#[contracttype]` enums.
                if args.len() < 3 {
                    return None;
                }
                let cases_ptr = extract_u32_from_expr(&args[1])?;
                let count = extract_u32_from_expr(&args[2])?;
                let variant_names = self
                    .wasm_module
                    .data_sections
                    .read_string_slice_array(cases_ptr, count)?;

                // Try to identify the scrutinee: the first argument is the discriminant
                // symbol, which was extracted from the enum parameter. Track back to
                // find the original parameter.
                let scrutinee = self.find_enum_scrutinee(&args[0]);
                self.enum_match_scrutinee = scrutinee;
                self.enum_cases = Some(variant_names);

                // Return a dummy value — the actual branch index is consumed by br_table
                // and replaced by enum variant patterns in try_recognize_match().
                Some(SorobanExpr::UnknownVal)
            }
            _ => None,
        }
    }

    /// Try to lift a linear memory host call using raw StackVal args (before SorobanExpr conversion).
    /// This preserves Val-encoded BinOp patterns that `stack_val_to_expr` would destroy.
    fn try_lift_linear_memory_call_raw(
        &mut self,
        host_fn: &HostFunction,
        raw_args: &[StackVal],
    ) -> Option<SorobanExpr> {
        match (&host_fn.module, host_fn.name.as_str()) {
            (HostModule::Map, "map_new_from_linear_memory") => {
                self.try_lift_struct_construct_raw(raw_args)
            }
            // vec_new_from_linear_memory: primary path is SorobanExpr-based
            // (try_lift_tuple_construct via extract_recent_stores). When that fails,
            // try frame_slots-based recovery as a fallback — this handles cases where
            // values were populated by a copy loop (detect_memory_copy_loop).
            (HostModule::Vec, "vec_new_from_linear_memory") => {
                if raw_args.len() < 2 {
                    return None;
                }
                let count = extract_u32_from_stack_val(&raw_args[1])?;
                let values = self.extract_vals_from_frame_slots(&raw_args[0], count)?;
                // Apply same stale-init replacement as try_lift_tuple_construct_with_count
                let values: Vec<SorobanExpr> = values
                    .into_iter()
                    .map(|v| match &v {
                        SorobanExpr::BoolLiteral(false) | SorobanExpr::Void => {
                            SorobanExpr::UnknownVal
                        }
                        _ => v,
                    })
                    .collect();
                Some(SorobanExpr::VecConstruct(values))
            }
            // vec_unpack_to_linear_memory(vec, vals_pos, len): unpacks Vec elements
            // into frame memory. Synthesize FrameSlot entries so subsequent loads
            // resolve to parameter-derived indexing (e.g., arg.get(0), arg.get(1)).
            (HostModule::Vec, "vec_unpack_to_linear_memory") => {
                self.handle_vec_unpack_raw(raw_args);
                // Return None so it falls through to RawHostCall (will be cleaned up
                // by orphan host call removal). The real effect is the FrameSlot entries.
                None
            }
            // map_unpack_to_linear_memory(map, keys_pos, vals_pos, count): unpacks Map
            // (struct) fields into frame memory. Synthesize FrameSlot entries so subsequent
            // loads resolve to field access expressions (e.g., v.a, v.b) instead of stale
            // Void sentinels from frame initialization.
            (HostModule::Map, "map_unpack_to_linear_memory") => {
                self.handle_map_unpack_raw(raw_args);
                None
            }
            (HostModule::Buf, "symbol_new_from_linear_memory") => {
                if raw_args.len() < 2 {
                    return None;
                }
                let ptr = extract_u32_from_stack_val(&raw_args[0])?;
                let len = extract_u32_from_stack_val(&raw_args[1])?;
                let name = self.wasm_module.data_sections.read_string(ptr, len)?;
                Some(SorobanExpr::SymbolLiteral(name))
            }
            (HostModule::Buf, "string_new_from_linear_memory") => {
                if raw_args.len() < 2 {
                    return None;
                }
                let ptr = extract_u32_from_stack_val(&raw_args[0])?;
                let len = extract_u32_from_stack_val(&raw_args[1])?;
                let s = self.wasm_module.data_sections.read_string(ptr, len)?;
                Some(SorobanExpr::StringLiteral(s))
            }
            (HostModule::Buf, "symbol_index_in_linear_memory") => {
                if raw_args.len() < 3 {
                    return None;
                }
                let cases_ptr = extract_u32_from_stack_val(&raw_args[1])?;
                let count = extract_u32_from_stack_val(&raw_args[2])?;
                let variant_names = self
                    .wasm_module
                    .data_sections
                    .read_string_slice_array(cases_ptr, count)?;

                let discriminant_expr = stack_val_to_expr(
                    &raw_args[0],
                    self.params,
                    self.registry,
                    Some(&self.frame_slots.borrow()),
                );
                let scrutinee = self.find_enum_scrutinee(&discriminant_expr);
                self.enum_match_scrutinee = scrutinee;
                self.enum_cases = Some(variant_names);

                Some(SorobanExpr::UnknownVal)
            }
            _ => None,
        }
    }

    /// Try to lift `map_new_from_linear_memory` using raw StackVal args.
    fn try_lift_struct_construct_raw(&mut self, raw_args: &[StackVal]) -> Option<SorobanExpr> {
        if raw_args.len() < 3 {
            return None;
        }

        let keys_ptr = extract_u32_from_stack_val(&raw_args[0])?;
        let count = extract_u32_from_stack_val(&raw_args[2])?;

        if count == 0 {
            return None;
        }

        let field_names = self
            .wasm_module
            .data_sections
            .read_string_slice_array(keys_ptr, count)?;

        if field_names.len() != count as usize {
            return None;
        }

        // Check for union variant construction (single-field map with variant name)
        if count == 1 {
            use stellar_xdr::ScSpecUdtUnionCaseV0;
            for (union_name, spec) in &self.registry.unions {
                for case in spec.cases.iter() {
                    let vname = match case {
                        ScSpecUdtUnionCaseV0::VoidV0(v) => v.name.to_utf8_string().ok(),
                        ScSpecUdtUnionCaseV0::TupleV0(t) => t.name.to_utf8_string().ok(),
                    };
                    if vname.as_deref() == Some(&field_names[0]) {
                        let values = self
                            .extract_recent_stores(count)
                            .or_else(|| self.extract_vals_from_frame_slots(&raw_args[1], count))?;
                        return Some(SorobanExpr::EnumConstruct {
                            type_name: union_name.clone(),
                            variant: field_names[0].clone(),
                            fields: values,
                        });
                    }
                }
            }
        }

        // Find matching struct or event type
        let type_name = self.find_type_by_fields(&field_names)?;

        // Try memory_stores first, fall back to frame_slots (for generic wrappers
        // where the caller stored values to frame memory but memory_stores are in
        // the parent context, not the inlined wrapper's context).
        // Reject all-UnknownVal results from extract_recent_stores — those are stale
        // initialization values; the real values may be in frame_slots.
        let values = self
            .extract_recent_stores(count)
            .filter(|v| !v.iter().all(|e| matches!(e, SorobanExpr::UnknownVal)))
            .or_else(|| self.extract_vals_from_frame_slots(&raw_args[1], count))?;
        let fields: Vec<(String, SorobanExpr)> = field_names.into_iter().zip(values).collect();

        Some(SorobanExpr::StructConstruct { type_name, fields })
    }

    /// Extract field values from shared frame_slots using the vals_ptr argument.
    ///
    /// When `map_new_from_linear_memory` is called through a generic wrapper (where
    /// keys_ptr is a parameter, not hardcoded), the caller stores field values to
    /// frame memory before the call. These stores are in the parent's memory_stores
    /// (not accessible from the inlined wrapper context), but the values ARE in the
    /// shared frame_slots. This method reads them directly.
    fn extract_vals_from_frame_slots(
        &self,
        vals_ptr_raw: &StackVal,
        count: u32,
    ) -> Option<Vec<SorobanExpr>> {
        // Unwrap Val-encoding: vals_ptr may be (FrameSlot << 32) | 4
        let (frame_id, base_offset) = extract_frame_slot_from_stack_val(vals_ptr_raw)?;

        let frame_slots = self.frame_slots.borrow();
        let mut values = Vec::new();
        for i in 0..count {
            let offset = base_offset + (i as i32) * 8;
            let val = frame_slots.get(&(frame_id, offset))?;
            // Guard against circular FrameSlot references
            if matches!(
                val,
                StackVal::FrameSlot(_, _) | StackVal::FrameBase(_) | StackVal::Unknown
            ) {
                return None;
            }
            let expr = stack_val_to_expr(val, self.params, self.registry, Some(&frame_slots));
            values.push(expr);
        }
        Some(values)
    }

    /// Try to lift `map_new_from_linear_memory(keys_ptr, vals_ptr, count)` into a StructConstruct.
    ///
    /// The KEYS array format is `(u32 ptr, u32 len)` slice descriptors (8 bytes each),
    /// where each pair points to a UTF-8 field name string in the data section.
    fn try_lift_struct_construct(&mut self, args: &[SorobanExpr]) -> Option<SorobanExpr> {
        if args.len() < 3 {
            return None;
        }

        let keys_ptr = extract_u32_from_expr(&args[0])?;
        let count = extract_u32_from_expr(&args[2])?;

        if count == 0 {
            return None;
        }

        // Read field names from the data section.
        // Keys are stored as (ptr, len) slice descriptors pointing to UTF-8 strings.
        let field_names = self
            .wasm_module
            .data_sections
            .read_string_slice_array(keys_ptr, count)?;

        if field_names.len() != count as usize {
            return None;
        }

        // Find matching struct type
        let type_name = self.find_struct_by_fields(&field_names)?;

        // Extract recent memory stores as field values.
        // Reject if all values are UnknownVal — this indicates stale initialization
        // values (from frame setup loops) that were replaced by the stale-init filter.
        // In this case, the real values may be in frame_slots (from a prior inlined call).
        let values = self.extract_recent_stores(count)?;
        if values.iter().all(|v| matches!(v, SorobanExpr::UnknownVal)) {
            return None;
        }

        // Build field list
        let fields: Vec<(String, SorobanExpr)> = field_names.into_iter().zip(values).collect();

        Some(SorobanExpr::StructConstruct { type_name, fields })
    }

    /// Handle `vec_unpack_to_linear_memory(vec, vals_pos, len)` by synthesizing
    /// FrameSlot entries. This makes the unpacked tuple elements available for
    /// subsequent `vec_new_from_linear_memory` calls that read from the same frame
    /// positions, replacing stale Void placeholders with parameter-derived values.
    fn handle_vec_unpack_raw(&mut self, raw_args: &[StackVal]) {
        if raw_args.len() < 3 {
            return;
        }

        // Extract the vec source (the parameter being unpacked)
        let vec_expr = stack_val_to_expr(
            &raw_args[0],
            self.params,
            self.registry,
            Some(&self.frame_slots.borrow()),
        );

        // Extract the frame address where elements will be written
        // The vals_pos arg is Val-encoded: (frame_addr << 32) | 4 (U32 tag).
        // We need the raw StackVal to get the FrameSlot.
        let addr_val = strip_val_encode(raw_args[1].clone());

        // Extract count from Val-encoded u32: (count << 32) | 4
        let count_val = strip_val_encode(raw_args[2].clone());
        let count = match &count_val {
            StackVal::I64(v) => Some(*v as u32),
            StackVal::I32(v) => Some(*v as u32),
            _ => None,
        };

        if let (StackVal::FrameSlot(id, base), Some(count)) = (&addr_val, count) {
            for i in 0..count {
                let elem_expr = SorobanExpr::MethodCall {
                    object: Box::new(vec_expr.clone()),
                    method: "get".to_string(),
                    args: vec![SorobanExpr::U32Literal(i)],
                };
                self.frame_slots.borrow_mut().insert(
                    (*id, base.base + (i as i32) * 8),
                    StackVal::HostCallResult(Box::new(elem_expr)),
                );
            }
            cov_mark::hit!(vec_unpack_raw_frame_slot);
        }
    }

    /// Build a `StorageGet` expression for a multi-param map_unpack_decode wrapper.
    /// The wrapper internally constructs a storage key from its extra args and reads a struct
    /// from storage. We try to reconstruct the full `StorageGet` expression with the correct
    /// storage type, DataKey variant, and key struct from the caller's args + registry.
    fn build_storage_get_for_multi_param_wrapper(
        &self,
        unpack_info: &MapUnpackDecodeInfo,
        extra_args: &[StackVal],
    ) -> SorobanExpr {
        let storage_type = unpack_info.storage_type.unwrap_or(StorageType::Temporary);

        // Try to construct the storage key from the extra args + registry heuristics.
        // Strategy: find a union variant whose data struct fields match the extra args.
        let key_expr =
            self.try_build_data_key_from_args(unpack_info.type_name.as_deref(), extra_args);

        SorobanExpr::StorageGet {
            storage_type,
            key: Box::new(key_expr.unwrap_or(SorobanExpr::UnknownVal)),
            unwrap: true,
            on_missing: None,
        }
    }

    /// Try to construct a DataKey enum variant from the caller's extra args.
    /// Matches union variants whose data struct field count equals extra arg count.
    fn try_build_data_key_from_args(
        &self,
        value_type_name: Option<&str>,
        extra_args: &[StackVal],
    ) -> Option<SorobanExpr> {
        if extra_args.is_empty() {
            return None;
        }

        // Convert extra args to expressions
        let arg_exprs: Vec<SorobanExpr> = extra_args
            .iter()
            .map(|a| {
                stack_val_to_expr(
                    a,
                    self.params,
                    self.registry,
                    Some(&self.frame_slots.borrow()),
                )
            })
            .collect();

        // Search all unions for a variant whose data type has fields matching arg count
        for (union_name, union_spec) in &self.registry.unions {
            for case in union_spec.cases.iter() {
                if let stellar_xdr::ScSpecUdtUnionCaseV0::TupleV0(tuple_case) = case {
                    // Variant has exactly one data type → look up the struct
                    if tuple_case.type_.len() != 1 {
                        continue;
                    }
                    let variant_name = tuple_case.name.to_utf8_string().ok()?;

                    // Heuristic: if we know the value type name (e.g., "AllowanceValue"),
                    // check if the variant name is a prefix (e.g., "Allowance")
                    if let Some(vtn) = value_type_name
                        && !vtn.starts_with(&variant_name)
                    {
                        continue;
                    }

                    // Find the struct type for this variant's data
                    if let stellar_xdr::ScSpecTypeDef::Udt(udt) = &tuple_case.type_[0] {
                        let data_type_name = udt.name.to_utf8_string().ok()?;
                        if let Some(data_struct) = self.registry.structs.get(&data_type_name) {
                            // Check field count matches extra arg count
                            if data_struct.fields.len() != extra_args.len() {
                                continue;
                            }

                            // Build the key struct from extra args
                            let fields: Vec<(String, SorobanExpr)> = data_struct
                                .fields
                                .iter()
                                .zip(arg_exprs.iter())
                                .filter_map(|(field, expr)| {
                                    let fname = field.name.to_utf8_string().ok()?;
                                    Some((fname, expr.clone()))
                                })
                                .collect();

                            if fields.len() != data_struct.fields.len() {
                                continue;
                            }

                            let key_struct = SorobanExpr::StructConstruct {
                                type_name: data_type_name,
                                fields,
                            };

                            return Some(SorobanExpr::EnumConstruct {
                                type_name: union_name.clone(),
                                variant: variant_name,
                                fields: vec![key_struct],
                            });
                        }
                    }
                }
            }
        }

        None
    }

    /// Handle `map_unpack_to_linear_memory(map, keys_pos, vals_pos, count)` by synthesizing
    /// FrameSlot entries with field access expressions. This makes the unpacked struct fields
    /// available for subsequent loads, replacing stale Void placeholders with `v.field_name`
    /// expressions that propagate through the decode→compute→encode→construct chain.
    fn handle_map_unpack_raw(&mut self, raw_args: &[StackVal]) {
        // map_unpack_to_linear_memory(map, keys_pos, vals_pos, count)
        if raw_args.len() < 4 {
            return;
        }

        // Extract the map source (the struct being unpacked)
        let map_expr = stack_val_to_expr(
            &raw_args[0],
            self.params,
            self.registry,
            Some(&self.frame_slots.borrow()),
        );

        // Extract keys_pos to read field names from the WASM data section.
        // The keys_pos arg is Val-encoded: (ptr << 32) | 4 (U32 tag).
        // Uses extract_u32_from_stack_val which handles both pre-folded I64
        // constants and symbolic BinOp((x << 32) | 4) patterns.
        let keys_ptr = extract_u32_from_stack_val(&raw_args[1]);

        // Extract count from Val-encoded u32: (count << 32) | 4
        let count = extract_u32_from_stack_val(&raw_args[3]);

        // Extract vals_pos frame address (Val-encoded FrameSlot)
        let vals_addr = strip_val_encode(raw_args[2].clone());

        if let (Some(keys_ptr), Some(count), StackVal::FrameSlot(id, base)) =
            (keys_ptr, count, &vals_addr)
        {
            // Read field names from the data section (same KEYS array format as struct construct)
            if let Some(field_names) = self
                .wasm_module
                .data_sections
                .read_string_slice_array(keys_ptr, count)
            {
                // Synthesize FrameSlot entries: vals_pos + i*8 → FieldAccess(map, field_name)
                for (i, name) in field_names.iter().enumerate() {
                    let field_expr = SorobanExpr::FieldAccess {
                        object: Box::new(map_expr.clone()),
                        field: name.clone(),
                    };
                    self.frame_slots.borrow_mut().insert(
                        (*id, base.base + (i as i32) * 8),
                        StackVal::HostCallResult(Box::new(field_expr)),
                    );
                }
                cov_mark::hit!(map_unpack_raw_field_access);
            }
        }
    }

    /// Try to lift `vec_new_from_linear_memory(vals_ptr, count)` into a tuple/struct construct.
    fn try_lift_tuple_construct(&mut self, args: &[SorobanExpr]) -> Option<SorobanExpr> {
        if args.len() < 2 {
            return None;
        }
        let count = extract_u32_from_expr(&args[1])?;
        self.try_lift_tuple_construct_with_count(count)
    }

    /// Lift tuple/struct construction from memory stores given a known element count.
    /// Shared by both the host-call path and the wrapper-interception path.
    fn try_lift_tuple_construct_with_count(&mut self, count: u32) -> Option<SorobanExpr> {
        if count == 0 {
            return None;
        }

        // Extract recent memory stores as values
        let values = self.extract_recent_stores(count)?;

        // Replace stale init placeholders with UnknownVal. The SDK initializes
        // tuple memory with Void (tag 0x02) before calling vec_unpack, but the
        // host function writes are invisible to our stack simulation. Masking a
        // stale Void value produces BoolLiteral(false) (tag 0x00). These are
        // almost never real tuple elements.
        let values: Vec<SorobanExpr> = values
            .into_iter()
            .map(|v| match &v {
                SorobanExpr::BoolLiteral(false) | SorobanExpr::Void => SorobanExpr::UnknownVal,
                _ => v,
            })
            .collect();

        // Check for enum variant construction: Vec[SymbolLiteral(variant_name), inner_value]
        // The SDK constructs tagged union variants as 2-element Vecs.
        if count == 2
            && let SorobanExpr::SymbolLiteral(ref variant_name) = values[0]
        {
            use stellar_xdr::ScSpecUdtUnionCaseV0;
            for (union_name, spec) in &self.registry.unions {
                for case in spec.cases.iter() {
                    let vname = match case {
                        ScSpecUdtUnionCaseV0::VoidV0(v) => v.name.to_utf8_string().ok(),
                        ScSpecUdtUnionCaseV0::TupleV0(t) => t.name.to_utf8_string().ok(),
                    };
                    if vname.as_deref() == Some(variant_name) {
                        return Some(SorobanExpr::EnumConstruct {
                            type_name: union_name.clone(),
                            variant: variant_name.clone(),
                            fields: vec![values[1].clone()],
                        });
                    }
                }
            }
        }

        // Check registry for a tuple struct with matching arity
        if let Some(type_name) = self.find_tuple_struct_by_arity(count) {
            let fields: Vec<(String, SorobanExpr)> = values
                .into_iter()
                .enumerate()
                .map(|(i, v)| (i.to_string(), v))
                .collect();
            Some(SorobanExpr::StructConstruct { type_name, fields })
        } else {
            Some(SorobanExpr::VecConstruct(values))
        }
    }

    /// The UDT type name of this function's return value, unwrapping `Option<T>` /
    /// `Result<T, E>` to the inner `T`. Used to disambiguate field-name-identical
    /// structs (e.g. `UdtRecursive` vs `RecursiveToEnum`, both `{a, b}`).
    fn return_type_udt_name(&self) -> Option<String> {
        let mut ty = self.return_type.as_ref()?;
        loop {
            match ty {
                ScSpecTypeDef::Option(o) => ty = o.value_type.as_ref(),
                ScSpecTypeDef::Result(r) => ty = r.ok_type.as_ref(),
                _ => break,
            }
        }
        self.registry.resolve_type_name(ty)
    }

    /// Find a struct type whose field names match exactly. When several structs share
    /// the same field-name set, prefer the one whose name matches this function's
    /// return/param UDT type (`return_type_udt_name`); otherwise fall back to the first
    /// match in declared (BTreeMap) order, preserving prior behavior.
    fn find_struct_by_fields(&self, field_names: &[String]) -> Option<String> {
        let mut matches: Vec<&String> = Vec::new();
        for (name, spec) in &self.registry.structs {
            let spec_fields: Vec<String> = spec
                .fields
                .iter()
                .filter_map(|f| f.name.to_utf8_string().ok())
                .collect();
            if spec_fields == field_names {
                matches.push(name);
            }
        }
        if matches.len() > 1
            && let Some(hint) = self.return_type_udt_name()
            && let Some(m) = matches.iter().find(|n| ***n == hint)
        {
            cov_mark::hit!(struct_disambiguated_by_return_type);
            return Some((*m).clone());
        }
        matches.first().map(|n| (*n).clone())
    }

    /// Find any type (struct, event, or union variant) whose field/param names match.
    /// Searches structs first, then events (all params), then union variants.
    fn find_type_by_fields(&self, field_names: &[String]) -> Option<String> {
        // 1. Structs
        if let Some(name) = self.find_struct_by_fields(field_names) {
            return Some(name);
        }
        // 2. Events — match all params or data-only suffix
        // (topic fields come first, data fields follow; the map only contains data fields)
        for (name, spec) in &self.registry.events {
            let param_names: Vec<String> = spec
                .params
                .iter()
                .filter_map(|p| p.name.to_utf8_string().ok())
                .collect();
            // Exact match (all params)
            if param_names == field_names {
                return Some(name.clone());
            }
            // Suffix match (data fields after topic fields)
            if param_names.len() > field_names.len() {
                let suffix = &param_names[param_names.len() - field_names.len()..];
                if suffix == field_names {
                    return Some(name.clone());
                }
            }
        }
        None
    }

    /// Find a tuple struct with all-numeric field names and matching arity.
    fn find_tuple_struct_by_arity(&self, count: u32) -> Option<String> {
        for (name, spec) in &self.registry.structs {
            if spec.fields.len() != count as usize {
                continue;
            }
            let all_numeric = spec.fields.iter().all(|f| {
                f.name
                    .to_utf8_string()
                    .map(|n| n.parse::<usize>().is_ok())
                    .unwrap_or(false)
            });
            if all_numeric {
                return Some(name.clone());
            }
        }
        None
    }

    /// Try to identify the enum parameter being matched on.
    /// The discriminant arg to `symbol_index_in_linear_memory` is derived from
    /// the enum parameter. We trace it back to find the original `Param(name)`.
    fn find_enum_scrutinee(&self, discriminant_arg: &SorobanExpr) -> Option<SorobanExpr> {
        // Direct param reference
        if matches!(discriminant_arg, SorobanExpr::Param(_)) {
            return Some(discriminant_arg.clone());
        }
        // Method call on a param (e.g. key.get_discriminant())
        if let SorobanExpr::MethodCall { object, .. } = discriminant_arg
            && matches!(object.as_ref(), SorobanExpr::Param(_))
        {
            return Some(*object.clone());
        }
        // HostCallResult wrapping a param access
        if let SorobanExpr::RawHostCall { args, .. } = discriminant_arg {
            for arg in args {
                if matches!(arg, SorobanExpr::Param(_)) {
                    return Some(arg.clone());
                }
            }
        }
        // Heuristic: find a function parameter whose type is a known union
        for param in self.params {
            if let ScSpecTypeDef::Udt(udt) = &param.type_def
                && let Ok(type_name) = udt.name.to_utf8_string()
                && self.registry.unions.contains_key(&type_name)
            {
                return Some(SorobanExpr::Param(param.name.clone()));
            }
        }
        None
    }

    /// Take the last `count` memory stores with distinct offsets, sort by offset,
    /// and convert to expressions. Returns None if there are fewer than `count`
    /// distinct offsets available.
    ///
    /// The distinct-offset deduplication handles SDK copy-loop artifacts: the SDK
    /// stores tuple elements to one memory region, then copies them to another via
    /// a loop. The copy loop produces I64Store instructions at the same static
    /// offset (0), duplicating earlier stores. Walking backwards and skipping
    /// duplicate offsets recovers the original distinct elements.
    fn extract_recent_stores(&mut self, count: u32) -> Option<Vec<SorobanExpr>> {
        let count = count as usize;
        if self.memory_stores.len() < count {
            return None;
        }

        // Walk backwards to find `count` stores with distinct static offsets.
        let mut seen_offsets = std::collections::HashSet::new();
        let mut indices = Vec::new();

        for i in (0..self.memory_stores.len()).rev() {
            let offset = self.memory_stores[i].offset;
            if seen_offsets.insert(offset) {
                indices.push(i);
                if indices.len() == count {
                    break;
                }
            }
        }

        if indices.len() < count {
            return None;
        }

        // Remove selected stores from memory_stores (in reverse index order
        // so that earlier indices remain valid after each removal).
        indices.sort();
        let mut stores: Vec<MemoryStore> = Vec::new();
        for &i in indices.iter().rev() {
            stores.push(self.memory_stores.remove(i));
        }
        stores.sort_by_key(|s| s.offset);

        let exprs: Vec<SorobanExpr> = stores
            .iter()
            .map(|s| {
                stack_val_to_expr(
                    &s.value,
                    self.params,
                    self.registry,
                    Some(&self.frame_slots.borrow()),
                )
            })
            .collect();

        Some(exprs)
    }
}

/// Lift a single function body from WASM instructions to Soroban IR.
///
/// Uses stack simulation to track values through WASM instructions and extract
/// meaningful arguments passed to host function calls.
/// Result of lifting a function body.
struct LiftBodyResult {
    stmts: Vec<SorobanStmt>,
    /// Whether host calls were detected during lifting (even if the body
    /// ended up empty after optimization removes orphan statements).
    found_host_calls: bool,
}

fn lift_function_body(
    wasm_module: &WasmModule,
    registry: &TypeRegistry,
    func_index: u32,
    params: &[FnParam],
    return_type: &Option<ScSpecTypeDef>,
) -> LiftBodyResult {
    let func = match wasm_module.get_function(func_index) {
        Some(f) => f,
        None => {
            return LiftBodyResult {
                stmts: Vec::new(),
                found_host_calls: false,
            };
        }
    };

    // Get function type to know how many WASM-level params exist
    let func_type = wasm_module.get_func_type(func_index);
    let num_wasm_params = func_type.map(|ft| ft.params.len()).unwrap_or(0) as u32;

    // Initialize locals: WASM params first, then declared locals
    let mut locals: Vec<StackVal> = Vec::new();
    for i in 0..num_wasm_params {
        if (i as usize) < params.len() {
            locals.push(StackVal::Param(params[i as usize].name.clone()));
        } else {
            locals.push(StackVal::WasmParam(i));
        }
    }
    for _ in &func.locals {
        locals.push(StackVal::Unknown);
    }

    let mut ctx = LiftContext::new(
        wasm_module,
        registry,
        params,
        return_type,
        locals,
        num_wasm_params,
    );

    // Structurize flat WASM instructions into a tree, then lift. Reclassify
    // compiler-emitted safety-net `unreachable` traps before lifting so the
    // Unreachable handler only emits Panic for genuine user panics (issue #11).
    let mut structured = super::structurize::structurize(&func.body);
    super::cfg_analysis::classify_safety_net_unreachables(&mut structured, wasm_module);
    // Layer B (issue #12): rewrite multi-level `br_if` to a `fail_with_error`
    // tail into a nested `if cond { panic_with_error!(…) }` (see
    // `recover_fail_with_error_branches`).
    recover_fail_with_error_branches(&mut structured, wasm_module);
    if let Ok(want) = std::env::var("DBG_STRUCT")
        && (want.is_empty() || want == func_index.to_string())
    {
        eprintln!("[DBG_STRUCT] func {func_index} structured:\n{structured:#?}");
    }
    ctx.lift_structured(&structured);

    // Re-attribute enum-payload loads hoisted before a `match` dispatch into the
    // arms (udt::add). Runs over the whole body now that every load is resolved.
    rebind_hoisted_enum_payload_body(&mut ctx.stmts);

    // Recover the SDK `Vec<i64>` fold idiom in a tuple-payload `match` arm
    // (udt::add UdtD) BEFORE the optimizer deletes the constant-folded loop.
    recover_vec_iter_fold(&mut ctx.stmts, registry);

    // Recover a fallible storage getter whose value + missing-key `Err` branch
    // were lost to a `has`/`extend_ttl` + `todo!()` husk. Phase 1 handles only the
    // DIRECT-return form (the getter returns the stored value as-is); a "computed"
    // getter that transforms the value through now-lost arithmetic keeps its husk
    // (recovering its early-return faithfully is the follow-up). The recovered get
    // is emitted as a bare tail `Expr` (NOT `Return(Some(..))`, which codegen would
    // double-wrap to `Ok(get(..).ok_or(..))`).
    let multiple_gets = *ctx.fallible_get_count.borrow() > 1;
    let fallible_rec = ctx.fallible_get_recovery.borrow_mut().take();
    if let Some(rec) = fallible_rec
        && let Some(ScSpecTypeDef::Result(r)) = return_type
    {
        // A "computed" getter feeds the storage value through now-lost arithmetic,
        // so only its leading missing-key `Err` path is faithfully recoverable: emit
        // `get::<_, Val>(&key).ok_or(Error::V)?;` then keep the honest `todo!()`
        // tail. A "direct" getter returns the stored value as-is: the recovered
        // `get(..).ok_or(..)` IS the tail. The turbofish pins the value type the
        // `.ok_or` can't infer — the declared ok-type for direct, `Val` for computed
        // (the value is discarded by the `?`).
        //
        // A getter that reads more than one key (`multiple_gets`) is treated as
        // computed even without arithmetic: the value-returning tail would return
        // the FIRST key's value/error and drop the later reads, so emit only the
        // always-faithful leading early-return guard.
        let computed = multiple_gets || function_calls_math_helper(wasm_module, func_index, 3);
        let value_ty = if computed {
            Some("soroban_sdk::Val".to_string())
        } else {
            crate::pipeline::spec_type_to_string(&r.ok_type)
        };
        if let Some(value_ty) = value_ty {
            let err = checked_error_expr(registry, &rec.err_type, rec.error_code);
            let get = SorobanExpr::StorageGet {
                storage_type: rec.storage_type,
                key: Box::new(rec.key),
                unwrap: false,
                on_missing: Some(Box::new(err)),
            };
            // `CastAs` is the turbofish vehicle (codegen renders
            // `get::<_, T>(&key).ok_or(err)`); `on_missing` carries the error.
            let get = SorobanExpr::CastAs {
                value: Box::new(get),
                target_type: value_ty,
            };
            cov_mark::hit!(fallible_get_recovered);
            // Computed: a lone `get(..).ok_or(err)?;` statement; codegen's
            // `needs_todo_value_tail` appends the honest `todo!()` value tail
            // (`Try` in tail position counts as the `()`-typed `?;` statement).
            // Direct: the `get(..).ok_or(err)` IS the value tail.
            let stmts = vec![SorobanStmt::Expr(if computed {
                SorobanExpr::Try(Box::new(get))
            } else {
                get
            })];
            return LiftBodyResult {
                stmts,
                found_host_calls: true,
            };
        }
    }

    // Remove Return(None) immediately before Panic: the Return is from an inlined
    // body's WASM return instruction, not a meaningful Rust return statement. Without
    // this, remove_dead_code truncates the Panic as unreachable code after return.
    // This pattern occurs when the SDK compiles `panic!()` as a call to a bare
    // `unreachable` trap function in the dispatch wrapper, placed after the body call.
    // If we found no meaningful host calls, try pattern detection
    if !ctx.found_host_calls
        && return_type.is_some()
        && has_arithmetic_pattern(&func.body)
        // The arithmetic shortcut reduces a function to a single `return <expr>`
        // built from the stack top, discarding any emitted statements. That is
        // correct for straight-line arithmetic (the loop, if any, is SDK
        // boilerplate and the real value strips out of the stack top), but wrong
        // when the stack top is a recovered loop-carried variable whose `let mut`
        // declaration lives in the discarded statements. Skip it in that case.
        && !ctx
            .stack
            .last()
            .map(stackval_references_let_or_phi)
            .unwrap_or(false)
    {
        // Try to extract the clean Rust expression by stripping Val encode/decode boilerplate.
        // This handles arithmetic like `a + b` where the stack holds `(a+b << N) | tag`.
        // We only use the stripped result when it contains no Unknown sub-values; if the inner
        // arithmetic used untracked ops (e.g., i32.and for b *= 2), fall through to the fallback.
        if let Some(top) = ctx.stack.last() {
            let stripped = strip_val_encode(top.clone());
            if !stack_val_contains_unknown(&stripped) {
                let expr =
                    stack_val_to_expr(&stripped, params, registry, Some(&ctx.frame_slots.borrow()));
                if !matches!(expr, SorobanExpr::Void | SorobanExpr::UnknownVal) {
                    let expr = narrow_to_bool(expr, return_type);
                    return LiftBodyResult {
                        stmts: vec![SorobanStmt::Return(Some(expr))],
                        found_host_calls: false,
                    };
                }
            }
        }
        // A subtraction collapses to this fallback (the U64Small/Object encode
        // branch defeats the strip path), where `generate_arithmetic_body` would
        // hard-code `Add`. Restore `a.checked_sub(b).ok_or(..)` from the bytecode
        // first.
        if let Some(tail) =
            recover_checked_arith_from_body(&func.body, params, return_type, registry)
        {
            return LiftBodyResult {
                stmts: vec![tail],
                found_host_calls: false,
            };
        }
        // Fallback for simple a + b (when stack is just a Param, strip_val_encode fails, or
        // the stripped expression contains Unknown from untracked i32 operations)
        return LiftBodyResult {
            stmts: generate_arithmetic_body(params, return_type),
            found_host_calls: false,
        };
    }

    let found_host_calls = ctx.found_host_calls;

    // Check for implicit return: if the function has a return type and there's
    // a meaningful value left on the stack, emit it as a return statement.
    if return_type.is_some()
        && let Some(top) = ctx.stack.last()
    {
        let expr = stack_val_to_expr(top, params, registry, Some(&ctx.frame_slots.borrow()));
        let expr = narrow_to_bool(expr, return_type);
        match &expr {
            SorobanExpr::Void | SorobanExpr::UnknownVal => {}
            _ => {
                // If the return value is a HostCallResult whose Expr statement was already
                // speculatively emitted, remove the Expr so the call appears only in the Return.
                // Only pop when the Expr matches the return expression — a different trailing
                // Expr (e.g., require_auth before a constant return) must be preserved.
                if matches!(top, StackVal::HostCallResult(_))
                    && let Some(SorobanStmt::Expr(last_expr)) = ctx.stmts.last()
                    && *last_expr == expr
                {
                    ctx.stmts.pop();
                }
                ctx.stmts.push(SorobanStmt::Return(Some(expr)));
            }
        }
    }

    // All-or-nothing for value-returning reconstructions: when no return value was
    // recovered anywhere — no `Return(Some)` and no value-producing tail — the body
    // is an incomplete reconstruction (a validation-guard / husk shell whose real
    // result was lost, e.g. a checked-i128 library fn whose arithmetic didn't fully
    // compose). Such a body can't type-check as the value-returning function it
    // belongs to, and the reference-free metric would score it as clean. Emit an
    // honest stub (empty body → `todo!`) instead of the misleading partial.
    LiftBodyResult {
        stmts: ctx.stmts,
        found_host_calls,
    }
}

/// True if the whole body is validation-guard panics with no value-producing
/// statement — every statement is either a bare `panic!()`/`panic_with_error!()`
/// or an `if cond { <panic-guard> }` with an empty `else` — **and at least one is
/// an `if` guard**. A value-returning function with such a body has no return
/// path; it is the misleading shell a checked-i128 library function collapses to
/// when its arithmetic didn't compose (`if amount_in != 0 { panic!() }`). The
/// `if`-guard requirement excludes a lone `{ panic!() }` body, which compiles
/// (a diverging getter), so this only touches the partials we introduce, not
/// pre-existing bare-panic reconstructions.
pub(crate) fn is_panic_guard_shell(stmts: &[SorobanStmt]) -> bool {
    !stmts.is_empty()
        && stmts.iter().all(stmt_is_panic_guard)
        && stmts.iter().any(|s| matches!(s, SorobanStmt::If { .. }))
}

fn stmt_is_panic_guard(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_)) => true,
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            else_body.is_empty()
                && !then_body.is_empty()
                && then_body.iter().all(stmt_is_panic_guard)
        }
        _ => false,
    }
}

/// True if any statement (transitively) contains an unrecovered marker —
/// `UnknownVal` / `CyclicSlot` / `RawHostCall`, each of which renders as a
/// `todo!`. Used to keep the all-or-nothing stub from touching honest partials.
pub(crate) fn stmts_contain_unknown(stmts: &[SorobanStmt]) -> bool {
    stmts.iter().any(stmt_contains_unknown)
}

fn stmt_contains_unknown(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => expr_contains_unknown(e),
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            expr_contains_unknown(value)
        }
        SorobanStmt::Return(None)
        | SorobanStmt::Break
        | SorobanStmt::Continue
        | SorobanStmt::Comment(_) => false,
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            expr_contains_unknown(condition)
                || stmts_contain_unknown(then_body)
                || stmts_contain_unknown(else_body)
        }
        SorobanStmt::Match { scrutinee, arms } => {
            expr_contains_unknown(scrutinee) || arms.iter().any(|a| stmts_contain_unknown(&a.body))
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => stmts_contain_unknown(body),
        SorobanStmt::For {
            start, end, body, ..
        } => {
            expr_contains_unknown(start)
                || expr_contains_unknown(end)
                || stmts_contain_unknown(body)
        }
    }
}

/// True if `expr` (transitively) contains an unrecovered marker. Exhaustive on
/// purpose so a new `SorobanExpr` variant forces a decision here rather than
/// silently reading as "clean".
fn expr_contains_unknown(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::UnknownVal
        | SorobanExpr::CyclicSlot { .. }
        | SorobanExpr::RawHostCall { .. } => true,
        // Leaves with no expression children.
        SorobanExpr::U32Literal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::I64Literal(_)
        | SorobanExpr::U128Literal(_)
        | SorobanExpr::I128Literal(_)
        | SorobanExpr::BoolLiteral(_)
        | SorobanExpr::SymbolLiteral(_)
        | SorobanExpr::StringLiteral(_)
        | SorobanExpr::BytesLiteral(_)
        | SorobanExpr::Void
        | SorobanExpr::None
        | SorobanExpr::Param(_)
        | SorobanExpr::Local(_)
        | SorobanExpr::NamedLocal(_)
        | SorobanExpr::Env
        | SorobanExpr::ContractError { .. }
        | SorobanExpr::Panic
        | SorobanExpr::LedgerSequence
        | SorobanExpr::LedgerTimestamp
        | SorobanExpr::LedgerNetworkId
        | SorobanExpr::CurrentContractAddress
        | SorobanExpr::MaxLiveUntilLedger
        | SorobanExpr::CollectionNew(_)
        | SorobanExpr::ValTagName(_) => false,
        // Single child.
        SorobanExpr::Some(b)
        | SorobanExpr::Not(b)
        | SorobanExpr::RequireAuth(b)
        | SorobanExpr::AuthorizeAsCurrContract(b)
        | SorobanExpr::ErrorFromCode(b)
        | SorobanExpr::PanicWithError(b)
        | SorobanExpr::CryptoSha256(b)
        | SorobanExpr::CryptoKeccak256(b)
        | SorobanExpr::PrngReseed(b)
        | SorobanExpr::PrngBytesNew(b)
        | SorobanExpr::PrngVecShuffle(b)
        | SorobanExpr::StrkeyToAddress(b)
        | SorobanExpr::AddressToStrkey(b)
        | SorobanExpr::SretResult(b)
        | SorobanExpr::ValTag(b)
        | SorobanExpr::ValConvert { value: b, .. }
        | SorobanExpr::CastAs { value: b, .. }
        | SorobanExpr::Try(b) => expr_contains_unknown(b),
        // Two children.
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Rem(a, b)
        | SorobanExpr::Eq(a, b)
        | SorobanExpr::Ne(a, b)
        | SorobanExpr::Lt(a, b)
        | SorobanExpr::Le(a, b)
        | SorobanExpr::Gt(a, b)
        | SorobanExpr::Ge(a, b)
        | SorobanExpr::And(a, b)
        | SorobanExpr::Or(a, b)
        | SorobanExpr::RequireAuthForArgs {
            address: a,
            args: b,
        }
        | SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold: a,
            extend_to: b,
        }
        | SorobanExpr::VecTryIterFold { vec: a, init: b } => {
            expr_contains_unknown(a) || expr_contains_unknown(b)
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => expr_contains_unknown(key),
        SorobanExpr::StorageSet { key, value, .. } => {
            expr_contains_unknown(key) || expr_contains_unknown(value)
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            expr_contains_unknown(key)
                || expr_contains_unknown(threshold)
                || expr_contains_unknown(extend_to)
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            topics.iter().any(expr_contains_unknown) || expr_contains_unknown(data)
        }
        SorobanExpr::InvokeContract {
            address,
            function,
            args,
            ..
        }
        | SorobanExpr::TryInvokeContract {
            address,
            function,
            args,
            ..
        } => {
            expr_contains_unknown(address)
                || expr_contains_unknown(function)
                || args.iter().any(expr_contains_unknown)
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            fields.iter().any(|(_, v)| expr_contains_unknown(v))
        }
        SorobanExpr::EnumConstruct { fields, .. } => fields.iter().any(expr_contains_unknown),
        SorobanExpr::TupleConstruct(items)
        | SorobanExpr::VecConstruct(items)
        | SorobanExpr::Log(items) => items.iter().any(expr_contains_unknown),
        SorobanExpr::MapConstruct(pairs) => pairs
            .iter()
            .any(|(k, v)| expr_contains_unknown(k) || expr_contains_unknown(v)),
        SorobanExpr::FieldAccess { object, .. } => expr_contains_unknown(object),
        SorobanExpr::MethodCall { object, args, .. } => {
            expr_contains_unknown(object) || args.iter().any(expr_contains_unknown)
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            expr_contains_unknown(public_key)
                || expr_contains_unknown(message)
                || expr_contains_unknown(signature)
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            expr_contains_unknown(msg_digest)
                || expr_contains_unknown(signature)
                || expr_contains_unknown(recovery_id)
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            expr_contains_unknown(low) || expr_contains_unknown(high)
        }
    }
}

/// Inline a single internal function call into the calling context.
///
/// Result of inlining a function call.
/// Detect identity-passthrough functions: functions that just validate and return
/// a parameter (e.g., `test_i64(env, v: i64) -> i64 { v }`). The WASM compiles
/// these as Val-decode/encode wrappers with no meaningful host calls. Returns the
/// matching parameter name if found.
pub fn find_identity_passthrough_param(
    params: &[FnParam],
    return_type: &ScSpecTypeDef,
) -> Option<String> {
    // Find the first non-env parameter whose type matches the return type
    for param in params {
        if param.type_def == *return_type {
            return Some(param.name.clone());
        }
    }
    None
}

struct InlineResult {
    /// Inlined statements and return expression, or None if the function had no
    /// host-call side effects (not worth inlining as statements).
    content: Option<(Vec<SorobanStmt>, Option<SorobanExpr>)>,
    /// Memory stores (I64Store) collected during execution. Always populated,
    /// even when `content` is None — helper functions that only do Val-encoding
    /// and memory stores (no host calls) still produce stores consumed by
    /// subsequent `map_new_from_linear_memory` calls.
    memory_stores: Vec<MemoryStore>,
    /// Stack-top value from no-host-call helpers (e.g., Val-encoding wrappers
    /// called with constant arguments). The parent can use this computed result
    /// instead of pushing Unknown when content is None.
    stack_result: Option<StackVal>,
}

/// Attempt to inline an internal (non-host) function call.
///
/// Returns `InlineResult` with the inlined content (if worth inlining) and
/// any memory stores produced. Memory stores are always returned because helper
/// functions may store Val-encoded values without making host calls, and these
/// stores are consumed by subsequent `map_new_from_linear_memory` struct construction.
#[allow(clippy::too_many_arguments)]
fn lift_inline_call(
    wasm_module: &WasmModule,
    registry: &TypeRegistry,
    target_idx: u32,
    arg_vals: Vec<StackVal>,
    inline_depth: u32,
    frame_slots: Rc<RefCell<HashMap<(u32, i32), StackVal>>>,
    next_frame_id: Rc<RefCell<u32>>,
    slot_write_log: Rc<RefCell<SlotWriteLog>>,
) -> InlineResult {
    let func = match wasm_module.get_function(target_idx) {
        Some(f) => f,
        None => {
            return InlineResult {
                content: None,
                memory_stores: Vec::new(),
                stack_result: None,
            };
        }
    };
    let func_type = match wasm_module.get_func_type(target_idx) {
        Some(ft) => ft,
        None => {
            return InlineResult {
                content: None,
                memory_stores: Vec::new(),
                stack_result: None,
            };
        }
    };
    let num_wasm_params = func_type.params.len() as u32;

    // Callee locals: params from arg_vals, then Unknown for body locals
    let mut locals: Vec<StackVal> = arg_vals;
    while locals.len() < num_wasm_params as usize {
        locals.push(StackVal::Unknown);
    }
    for _ in &func.locals {
        locals.push(StackVal::Unknown);
    }

    let params: &[FnParam] = &[];
    let return_type: Option<ScSpecTypeDef> = None;

    let mut ctx = LiftContext::new(
        wasm_module,
        registry,
        params,
        &return_type,
        locals,
        num_wasm_params,
    );
    // Defence in depth: the only current call-site already gates on the
    // depth, but a future caller could forget. Bail out cleanly rather than
    // recursing past the bound.
    if inline_depth >= MAX_INLINE_CALL_DEPTH {
        return InlineResult {
            content: None,
            memory_stores: Vec::new(),
            stack_result: None,
        };
    }
    ctx.inline_depth = inline_depth + 1;
    ctx.frame_slots = frame_slots;
    ctx.next_frame_id = next_frame_id;
    // Shared like `frame_slots`: the log records GLOBAL simulation order, so
    // a descriptor built by the caller stays justified when a callee that
    // received its pointer re-derives the key (the frame-descriptor fold).
    ctx.slot_write_log = slot_write_log;

    // Reclassify safety-net `unreachable` traps before lifting (issue #11) —
    // critical at inline_depth > 0, where trailing safety-net Panics would
    // otherwise splice into the caller's top level and trip remove_dead_code.
    let mut structured = super::structurize::structurize(&func.body);
    super::cfg_analysis::classify_safety_net_unreachables(&mut structured, wasm_module);
    // Layer B (issue #12): nest multi-level `br_if` to a `fail_with_error` tail
    // as `if cond { panic_with_error!(…) }` so the contract error survives
    // inlining instead of leaking as a stray (see
    // `recover_fail_with_error_branches`).
    recover_fail_with_error_branches(&mut structured, wasm_module);
    // Debug affordance: dump the structured body of an *inlined* (non-exported)
    // function by index. `DBG_STRUCT` only reaches lifted entrypoints; the big
    // contracts degrade values inside 3-4 levels of inlined helpers, so tracing
    // an `UnknownVal` back to its source needs the inlined bodies too. Pair with
    // `DBG_NAMEIDX` to resolve the entrypoint index, then walk the call graph.
    if let Ok(want) = std::env::var("DBG_INLINE_STRUCT")
        && want == target_idx.to_string()
    {
        eprintln!(
            "[DBG_INLINE_STRUCT] inlined func {target_idx} ({num_wasm_params} params):\n{structured:#?}"
        );
    }
    ctx.lift_structured(&structured);

    if !ctx.found_host_calls {
        // No host calls — not worth inlining as statements, but return
        // memory stores so parent contexts can use them for struct construction.
        // Also return the computed result: Val-encoding wrappers with constant args
        // produce a known Return value that the parent should use instead of Unknown.
        // Check Return stmts first (captures fast-path results that precede unreachable
        // slow-path code which may push different values onto the stack).
        let stack_result = if let Some(ret_pos) = ctx
            .stmts
            .iter()
            .rposition(|s| matches!(s, SorobanStmt::Return(Some(_))))
        {
            if let SorobanStmt::Return(Some(expr)) = ctx.stmts.remove(ret_pos) {
                Some(StackVal::HostCallResult(Box::new(expr)))
            } else {
                ctx.stack.last().cloned()
            }
        } else {
            ctx.stack.last().cloned()
        };
        cov_mark::hit!(inline_content_none);
        return InlineResult {
            content: None,
            memory_stores: ctx.memory_stores,
            stack_result,
        };
    }

    // Extract return value from final Return statement, or from stack top
    let mut return_expr = match ctx.stmts.last() {
        Some(SorobanStmt::Return(Some(_))) => {
            if let Some(SorobanStmt::Return(Some(expr))) = ctx.stmts.pop() {
                Some(expr)
            } else {
                None
            }
        }
        _ => {
            let result = ctx.stack.last().and_then(|top| {
                let expr =
                    stack_val_to_expr(top, params, registry, Some(&ctx.frame_slots.borrow()));
                match expr {
                    SorobanExpr::Void | SorobanExpr::UnknownVal => None,
                    e => Some(e),
                }
            });
            // When the return value is captured from the stack, any trailing
            // Return(None) is redundant (the WASM return instruction merely
            // marks the end of execution; the value is already on the stack).
            if result.is_some() && matches!(ctx.stmts.last(), Some(SorobanStmt::Return(None))) {
                ctx.stmts.pop();
            }
            result
        }
    };

    // Fallback: extract return value from inside a Loop body.
    // Inlined symbol-construction functions use a loop to build a value
    // and Return from inside the loop. The standard extraction above misses
    // this because it only checks the last top-level statement.
    // Resolve Local(N) through the loop body's Let bindings (not ctx.locals,
    // which has the pre-loop initial value). Scan backwards from the Return
    // to find the last Let for that local.
    if return_expr.is_none()
        && let Some(SorobanStmt::Loop { body }) = ctx.stmts.last()
    {
        // Find the Return expression
        let mut ret_expr: Option<&SorobanExpr> = None;
        for s in body.iter().rev() {
            if let SorobanStmt::Return(Some(expr)) = s {
                ret_expr = Some(expr);
                break;
            }
        }
        if let Some(SorobanExpr::Local(ret_idx)) = ret_expr {
            // Find the last Let binding for var_{ret_idx} before the Return,
            // then recursively resolve any Local(N) references in the value
            // by looking up earlier Let bindings in the same loop body.
            let target_name = format!("var_{}", ret_idx);
            for s in body.iter().rev() {
                if let SorobanStmt::Let { name, value, .. } = s
                    && *name == target_name
                {
                    return_expr = Some(resolve_locals_in_expr(value.clone(), body));
                    break;
                }
            }
        } else if let Some(expr) = ret_expr {
            return_expr = Some(expr.clone());
        }
    }

    // Unwrap single-element VecConstruct: SDK enum key encoding wraps the
    // variant symbol in a Vec for host function calls, but at the user API level
    // you pass &DataKey::Variant directly. Strip the wrapper.
    if let Some(SorobanExpr::VecConstruct(ref elems)) = return_expr
        && elems.len() == 1
    {
        return_expr = Some(elems[0].clone());
    }

    // Issue #36: an extracted empty-collection value (`Map::new`/`Vec::new`/
    // `Bytes::new`) that is one arm of an unmodeled phi — canonically
    // `get(&key).unwrap_or_else(|| vec![...])`, where the default arm wins the
    // single-value extraction while the loaded value escapes another way.
    // Cloning the empty constructor into every caller use site is silent-wrong
    // (it compiles, so the soundness ratchet can't see it); retreat to the
    // honest hole. Two proofs of divergence:
    //   1. Another return path carries a different value (a nested
    //      `Return(Some(≠))`, or a `Return(None)` — an exit whose value could
    //      not be captured).
    //   2. The helper reaches `get_contract_data`: the collection may be the
    //      storage-loaded one via a local-phi + br join, which leaves no
    //      nested Return behind (branch-sequential lift makes the fall-through
    //      default constructor the local's last write).
    // All-paths-agree empty constructions in storage-free helpers are
    // untouched.
    // The empty constructor may hide behind a `let var_N = Map::new(&env)`
    // materialisation (the returned expr is then `Local(N)`); resolve one
    // level through the inlined Lets for gate evaluation. A local that is
    // later re-assigned (`Assign var_N = …`) was properly phi-materialised
    // and is NOT stale — skip those.
    let gate_value = match &return_expr {
        Some(SorobanExpr::Local(idx)) => {
            let name = format!("var_{}", idx);
            let reassigned = ctx
                .stmts
                .iter()
                .any(|s| matches!(s, SorobanStmt::Assign { target, .. } if *target == name));
            if reassigned {
                None
            } else {
                Some(resolve_locals_in_expr(SorobanExpr::Local(*idx), &ctx.stmts))
            }
        }
        Some(other) => Some(other.clone()),
        None => None,
    };
    if let Some(ret) = &gate_value
        && matches!(ret, SorobanExpr::CollectionNew(_))
        && (has_divergent_nested_return(&ctx.stmts, ret)
            || func_reaches_host(
                wasm_module,
                target_idx,
                HostModule::Ledger,
                "get_contract_data",
                0,
            ))
    {
        cov_mark::hit!(lost_collection_multipath_return);
        return_expr = None;
    }

    // Convert Return→Break inside Loop bodies of inlined content. Returns in
    // loop bodies cause the optimizer's dead-code removal to treat the Loop as
    // a terminator, stripping subsequent statements from the parent function.
    convert_loop_returns_to_breaks(&mut ctx.stmts);

    cov_mark::hit!(inline_content_some);
    InlineResult {
        content: Some((ctx.stmts, return_expr)),
        memory_stores: ctx.memory_stores,
        stack_result: None,
    }
}

/// Recursively scan inlined statements for a return path whose value differs
/// from `expected`: a `Return(Some(expr))` with a different expression, or a
/// `Return(None)` (an exit whose value could not be captured). Used by
/// [`lift_inline_call`] to detect multi-path helper returns that its
/// single-value extraction cannot faithfully represent (issue #36).
fn has_divergent_nested_return(stmts: &[SorobanStmt], expected: &SorobanExpr) -> bool {
    stmts.iter().any(|stmt| match stmt {
        SorobanStmt::Return(Some(expr)) => expr != expected,
        SorobanStmt::Return(None) => true,
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            has_divergent_nested_return(then_body, expected)
                || has_divergent_nested_return(else_body, expected)
        }
        SorobanStmt::Match { arms, .. } => arms
            .iter()
            .any(|arm| has_divergent_nested_return(&arm.body, expected)),
        SorobanStmt::Loop { body } | SorobanStmt::For { body, .. } | SorobanStmt::Block(body) => {
            has_divergent_nested_return(body, expected)
        }
        _ => false,
    })
}

/// Resolve `Local(N)` references in an expression by looking up the corresponding
/// `Let var_N = value` in the given statement list. Used to resolve locals in
/// inlined loop body return values where the locals don't exist in the parent context.
fn resolve_locals_in_expr(expr: SorobanExpr, stmts: &[SorobanStmt]) -> SorobanExpr {
    match expr {
        SorobanExpr::Local(idx) => {
            let target_name = format!("var_{}", idx);
            // Scan backwards for the FIRST meaningful Let for this local
            // (first = the original value, before overwrites)
            let mut first_value: Option<SorobanExpr> = None;
            for s in stmts.iter() {
                if let SorobanStmt::Let { name, value, .. } = s
                    && *name == target_name
                {
                    first_value = Some(value.clone());
                    break; // Take the first (most meaningful) assignment
                }
            }
            first_value.unwrap_or(expr)
        }
        SorobanExpr::VecConstruct(elements) => SorobanExpr::VecConstruct(
            elements
                .into_iter()
                .map(|e| resolve_locals_in_expr(e, stmts))
                .collect(),
        ),
        other => other,
    }
}

/// Convert `Return(Some(expr))` → `Break` inside Loop bodies of inlined content.
///
/// Returns inside Loop bodies of inlined functions cause the optimizer's
/// dead-code removal to treat the Loop as a terminator, stripping subsequent
/// statements that belong to the parent function. Converting them to `Break`
/// makes the loop exit after one iteration without acting as a function
/// terminator.
///
/// Returns inside If/Match bodies are kept — they represent legitimate
/// conditional exits that map to early returns in the parent function.
fn convert_loop_returns_to_breaks(stmts: &mut [SorobanStmt]) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Loop { body } => {
                // Convert Returns inside loop bodies to Break
                for s in body.iter_mut() {
                    if matches!(s, SorobanStmt::Return(_)) {
                        *s = SorobanStmt::Break;
                    }
                }
                // Recurse into nested structures within the loop
                convert_loop_returns_to_breaks(body);
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                convert_loop_returns_to_breaks(then_body);
                convert_loop_returns_to_breaks(else_body);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    convert_loop_returns_to_breaks(&mut arm.body);
                }
            }
            SorobanStmt::Block(body) => {
                convert_loop_returns_to_breaks(body);
            }
            _ => {}
        }
    }
}

/// Resolve a sign-check function's checked argument to a meaningful expression.
///
/// The checked arg is typically the hi 64 bits of an i128 parameter, stored as a
/// `LetBinding` from an inlined i128 decode whose stmts were discarded. Converting
/// it directly produces an unbound `Local(N)`. Instead, scan all args and frame slot
/// values for a `Param` reference. Since both hi and lo parts originate from the same
/// i128 parameter decode, finding a Param in any related value is sufficient.
fn resolve_sign_check_arg(
    checked_arg: &StackVal,
    all_args: &[StackVal],
    params: &[FnParam],
    registry: &TypeRegistry,
    frame_slots: &HashMap<(u32, i32), StackVal>,
) -> SorobanExpr {
    // Try direct conversion first
    let direct = stack_val_to_expr(checked_arg, params, registry, Some(frame_slots));
    if !matches!(&direct, SorobanExpr::Local(_)) {
        return direct;
    }
    // Direct conversion produced an unbound Local. Try resolving through all args
    // and frame_slot values to find a Param reference.
    for arg in all_args {
        if let Some(param_expr) = try_extract_param_from_stack_val(arg) {
            return param_expr;
        }
    }
    // Also scan frame_slot values for Param references
    for val in frame_slots.values() {
        if let Some(param_expr) = try_extract_param_from_stack_val(val) {
            return param_expr;
        }
    }
    direct
}

/// Try to extract a Param expression from a StackVal, traversing through
/// HostCallResult and ValConvert wrappers.
fn try_extract_param_from_stack_val(val: &StackVal) -> Option<SorobanExpr> {
    match val {
        StackVal::Param(name) => Some(SorobanExpr::Param(name.clone())),
        StackVal::HostCallResult(expr) => match &**expr {
            SorobanExpr::Param(name) => Some(SorobanExpr::Param(name.clone())),
            SorobanExpr::ValConvert { value, .. } => match &**value {
                SorobanExpr::Param(name) => Some(SorobanExpr::Param(name.clone())),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// The i128/u128 arithmetic operation a soft-arith helper implements. Soroban
/// has no native 128-bit type, so the SDK lowers `i128`/`u128` `*` and `/` onto
/// `(result_ptr, a_lo, a_hi, b_lo, b_hi[, …])` helper functions that do the math
/// on two-i64 limbs. We classify those helpers and lower them back to clean
/// `Mul`/`Div` rather than letting them inline into limb-soup `todo!`s.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum I128Op {
    Mul,
    Div,
    /// Truncating divide that adds 1 to the quotient when the remainder is
    /// nonzero — `a / b + (a % b != 0) as i128`. Soroswap's fee `div_ceil`.
    DivCeil,
}

/// A classified i128 soft-arith helper: the operation plus the arg indices of
/// the operand limb pairs. The result is written back through whichever leading
/// `i32` arg(s) point at a frame slot (see `try_lower_i128_intrinsic`).
#[derive(Debug, Clone, Copy)]
struct I128Intrinsic {
    op: I128Op,
    a_lo: usize,
    a_hi: usize,
    b_lo: usize,
    b_hi: usize,
    /// Result-limb byte offsets from the output pointer. Unchecked helpers write
    /// the value directly (`lo@0, hi@8`); checked (`Result<i128,E>`-returning)
    /// helpers reserve `+0` for the status discriminant (`lo@8, hi@16`).
    res_lo_off: i32,
    res_hi_off: i32,
}

/// Count occurrences of selected opcodes in a function body (a coarse fingerprint).
fn opcode_counts(func: &crate::wasm::ir::WasmFunction) -> I128Fingerprint {
    use crate::wasm::ir::WasmInstr;
    let mut fp = I128Fingerprint::default();
    for ins in &func.body {
        match ins {
            WasmInstr::I64Mul => fp.mul += 1,
            WasmInstr::I64DivU | WasmInstr::I64DivS => fp.div += 1,
            WasmInstr::I64Store(_) => fp.store += 1,
            WasmInstr::Select => fp.select += 1,
            WasmInstr::I64Xor => fp.xor += 1,
            WasmInstr::Call(t) => fp.calls.push(*t),
            _ => {}
        }
    }
    fp
}

#[derive(Default)]
struct I128Fingerprint {
    mul: usize,
    div: usize,
    store: usize,
    select: usize,
    xor: usize,
    calls: Vec<u32>,
}

/// True when `func_idx` has the soft-arith helper signature `(i32 ptr, i64 a_lo,
/// i64 a_hi, i64 b_lo, i64 b_hi [, i32])` returning nothing — two 128-bit operands
/// passed as limb pairs, result written through the leading pointer.
fn is_two_i128_operand_helper(module: &WasmModule, func_idx: u32) -> bool {
    use crate::wasm::ir::WasmType;
    let Some(ft) = module.get_func_type(func_idx) else {
        return false;
    };
    if !ft.results.is_empty() {
        return false;
    }
    // 5-param (ptr,a_lo,a_hi,b_lo,b_hi) or 6-param (…,ptr2) forms.
    matches!(
        ft.params.as_slice(),
        [
            WasmType::I32,
            WasmType::I64,
            WasmType::I64,
            WasmType::I64,
            WasmType::I64
        ] | [
            WasmType::I32,
            WasmType::I64,
            WasmType::I64,
            WasmType::I64,
            WasmType::I64,
            WasmType::I32
        ]
    )
}

/// Classify `func_idx` as an i128 multiply/divide soft-arith helper, recursing one
/// level into a signed wrapper that delegates to an unsigned core. Returns the
/// operation and the operand/result arg layout, or `None` if it is not one.
/// True if `func` is the Soroban small-symbol encoder: its body compares input
/// bytes against the `_` / `0` / `A` / `a` boundaries (95 / 48 / 65 / 97) of the
/// 6-bit symbol character packing. The four constants together are a near-unique
/// signature — no unrelated code compares bytes against exactly that set.
fn is_small_symbol_encoder(func: &crate::wasm::ir::WasmFunction) -> bool {
    use crate::wasm::ir::WasmInstr;
    let (mut underscore, mut digit0, mut upper_a, mut lower_a) = (false, false, false, false);
    for ins in &func.body {
        if let WasmInstr::I32Const(c) = ins {
            match *c {
                95 => underscore = true,
                48 => digit0 = true,
                65 => upper_a = true,
                97 => lower_a = true,
                _ => {}
            }
        }
    }
    underscore && digit0 && upper_a && lower_a
}

/// True if `func_idx` builds a `Symbol` from a static `(str_ptr, str_len)` slice —
/// signature `(i32 result_ptr, i32 str_ptr, i32 str_len) -> ()` whose body
/// transitively (≤2 call levels) reaches the small-symbol encoder.
///
/// The SDK's `Symbol::new(&env, "literal")` lowers to such a wrapper; with the
/// `DataKey::into_val` dispatch deeply inlined, the encoder itself sits past
/// `MAX_INLINE_CALL_DEPTH`, so the wrapper's result degrades to `UnknownVal`. The
/// decompiled effect is `Symbol::new(read_string(str_ptr, str_len))` written via
/// `result_ptr` — recovered directly in `try_lower_symbol_builder`.
/// Evaluate a constant *descriptor-pointer* DataKey constructor call
/// (`(i32) -> i64`, `call <ctor>(<static ptr>)`): the pointer addresses a
/// 1-byte enum discriminant in static data; the constructor br_tables over it
/// and builds `Vec[Symbol(<variant>)]` from linear-memory strings. Returns
/// the proven key expression, or `None` on any deviation (non-static pointer,
/// wrong shape, unresolvable variant name). Extracted from
/// [`LiftContext::try_push_descriptor_key`] so load-struct-wrapper detection
/// can recover the same key from a helper's own body (issue #34 tranche 3).
fn descriptor_key_from_ptr(module: &WasmModule, target_idx: u32, ptr: i32) -> Option<SorobanExpr> {
    use crate::wasm::ir::WasmType;
    if ptr <= 1024 {
        return None; // not a data-section pointer
    }
    let ft = module.get_func_type(target_idx)?;
    if ft.params.as_slice() != [WasmType::I32] || ft.results.as_slice() != [WasmType::I64] {
        return None;
    }
    if !func_reaches_symbol_encoder(module, target_idx, 0) {
        return None;
    }
    // The descriptor pointer addresses a 1-byte enum discriminant (win #4's
    // zero-extend reads the byte-or-0 of the covering segment); require the
    // address to lie in real static data so we never resolve runtime memory.
    // The descriptor pointer addresses a 1-byte enum discriminant; require
    // the address to lie in REAL initialized static data. A constant pointer
    // in a segment gap was probed as "zero-initialized BSS → variant 0" and
    // REJECTED by corpus audit: such gaps can hold mutable statics written at
    // runtime, and resolving them fabricated keys that surfaced as wrong
    // substitutions (soroswap events with DataKeys in Address/value fields).
    // (The PROVEN gap case — a linker-elided all-zero descriptor row — is
    // handled by executing the ctor's real bytecode instead:
    // [`gap_row_proven_zero`] + `DkEval.gap_zero`.)
    let disc = module
        .data_sections
        .read_bytes_zero_extended(ptr as u32, 1)
        .map(|b| b[0] as usize)?;
    let strings = extract_data_strings(module, target_idx);
    let name = strings.get(disc)?;
    if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return None;
    }
    Some(SorobanExpr::VecConstruct(vec![SorobanExpr::SymbolLiteral(
        name.clone(),
    )]))
}

/// Prove that the data-segment GAP `[x, end)` holds WASM's zero-initialized
/// memory at EVERY point of every execution — i.e. it is a constant
/// descriptor row whose all-zero data segment the linker elided (aqua's
/// `PoolRewardConfig` row sits between its `\x01` and `\x06` neighbors
/// exactly 16 bytes apart), not a runtime-written mutable static (the
/// blindly-probed zero-fill PR #44 rejected as fabrication).
///
/// The proof is module-wide materialization discipline: a WASM store needs
/// a pointer, and every pointer a rustc/LLVM module can aim at a static
/// row originates from an `i32.const` relocation of that object's base (a
/// non-stack-pointer global would be the only other channel — refused
/// outright below). So the range stays zero if:
/// - the module has no bulk-memory or atomic-store instruction anywhere
///   (those write through addresses this scan cannot see; the parser
///   preserves them as [`WasmInstr::Unknown`]);
/// - the module never reads a global other than the shadow stack pointer
///   (`global.get 0`) — a pointer-holding global could smuggle the row
///   address past the constant scan;
/// - every module-wide `I32Const(c)` with `c` in `[x - 15, end)` — the
///   row itself plus the widest store-immediate slop that could still land
///   in it from below — is EXACTLY `x` and immediately followed by
///   `Call(ctor)`: the address is only ever materialized as this one
///   ctor's argument, never as a store base, an arithmetic seed, or
///   another function's argument;
/// - no `I32Const(c)` within ±4096 of the row feeds an `i32.add`/`i32.sub`
///   within its next two instructions — the derived-pointer shape
///   (`i32.const base; … ; i32.add` reaching the row from a farther
///   constant, in either direction) is refused wholesale (greptile P1 on
///   PR #45). Longer derivation chains through locals are out of model:
///   LLVM materializes each static object's address directly and never
///   assembles it from another object's relocation.
///
/// What the ctor itself does with the pointer is NOT assumed: the caller
/// evaluates the ctor's real bytecode under [`DkEval`], whose stores
/// REQUIRE shadow-stack addresses — an absolute store anywhere in the
/// trace bails the whole eval. A completed eval therefore proves the ctor
/// never writes the row, and (its trace being input-determined) that no
/// call of it ever will.
fn gap_row_proven_zero(module: &WasmModule, ctor: u32, x: u32, end: u32) -> bool {
    use crate::wasm::ir::WasmInstr as WI;
    let lo = x.saturating_sub(15);
    let band_lo = x.saturating_sub(4096);
    let band_hi = end.saturating_add(4096);
    for func in &module.functions {
        for (i, instr) in func.body.iter().enumerate() {
            match instr {
                WI::Unknown(s) if s.contains("Memory") || s.contains("Store") => {
                    return false;
                }
                WI::GlobalGet(g) if *g != 0 => {
                    return false;
                }
                WI::I32Const(c)
                    if (lo..end).contains(&(*c as u32))
                        && (*c as u32 != x
                            || !matches!(func.body.get(i + 1), Some(WI::Call(t)) if *t == ctor)) =>
                {
                    return false;
                }
                // Only plausible static-base constants (> 1024, the same
                // data-pointer threshold used module-wide) participate in
                // the derived-pointer refusal — small constants are
                // offsets/immediates, not object bases.
                WI::I32Const(c)
                    if *c > 1024
                        && (band_lo..band_hi).contains(&(*c as u32))
                        && func.body[i + 1..]
                            .iter()
                            .take(2)
                            .any(|n| matches!(n, WI::I32Add | WI::I32Sub)) =>
                {
                    return false;
                }
                _ => {}
            }
        }
    }
    cov_mark::hit!(gap_row_proven_zero);
    true
}

fn is_symbol_from_lm_builder(module: &WasmModule, func_idx: u32) -> bool {
    use crate::wasm::ir::WasmType;
    let Some(ft) = module.get_func_type(func_idx) else {
        return false;
    };
    if ft.params.as_slice() != [WasmType::I32, WasmType::I32, WasmType::I32]
        || !ft.results.is_empty()
    {
        return false;
    }
    func_reaches_symbol_encoder(module, func_idx, 0)
}

/// True if `idx` transitively (≤3 call levels) reaches the Soroban symbol encoder:
/// either the host `symbol_new_from_linear_memory` import (the long-symbol path,
/// more than 9 chars) or the inline small-symbol encoder (the short path). A
/// near-unique signature of code that builds a `Symbol` from a static `(ptr, len)`.
fn func_reaches_symbol_encoder(module: &WasmModule, idx: u32, depth: u32) -> bool {
    use crate::wasm::ir::WasmInstr;
    if depth > 3 {
        return false;
    }
    if let Some(hf) = module.imports.get_by_index(idx) {
        return hf.module == HostModule::Buf && hf.name == "symbol_new_from_linear_memory";
    }
    let Some(func) = module.get_function(idx) else {
        return false;
    };
    if is_small_symbol_encoder(func) {
        return true;
    }
    func.body
        .iter()
        .any(|ins| matches!(ins, WasmInstr::Call(t) if func_reaches_symbol_encoder(module, *t, depth + 1)))
}

/// True if `idx` transitively (≤2 call levels) reaches the host function
/// `host_module::name`. The generic sibling of `func_reaches_symbol_encoder`.
fn func_reaches_host(
    module: &WasmModule,
    idx: u32,
    host_module: HostModule,
    name: &str,
    depth: u32,
) -> bool {
    use crate::wasm::ir::WasmInstr;
    if depth > 2 {
        return false;
    }
    if let Some(hf) = module.imports.get_by_index(idx) {
        return hf.module == host_module && hf.name == name;
    }
    let Some(func) = module.get_function(idx) else {
        return false;
    };
    func.body
        .iter()
        .any(|ins| matches!(ins, WasmInstr::Call(t) if func_reaches_host(module, *t, host_module, name, depth + 1)))
}

/// Output-struct offsets of the SDK `Option<u32>` decode helper.
struct OptionDecodeLayout {
    /// Offset of the discriminant byte (`0 = None`, `1 = Some(small)`, `2 = Some(obj)`).
    tag_off: i32,
    /// Offset of the unwrapped `u32` payload.
    val_off: i32,
}

/// Recognize the SDK-generated `Option<u32>` decoder `(i32 ptr, i64 opt) -> ()`.
///
/// `Vec::first_index_of` returns `Option<u32>` as a host `Val`; the SDK decodes it
/// with a tiny pure helper that writes a `{tag, value}` struct to `ptr`:
/// `if opt == 2 /*Void*/ { tag = 0 } else { value = (opt >> 32) as u32;
///  tag = if (opt & 0xff) == 4 /*U32Val*/ { 1 } else { 2 } };
///  *(ptr + val_off) = value; *(ptr + tag_off) = tag`.
/// Returns the two store offsets. Matches only the exact shape (the `Void(2)`
/// check, the `>> 32` payload extract, the `U32Val(4)` tag `select`, two `i32`
/// stores, no calls) so it can never misfire on a generic scratch writer.
fn detect_option_decode_helper(module: &WasmModule, idx: u32) -> Option<OptionDecodeLayout> {
    use crate::wasm::ir::{WasmInstr, WasmType};
    // Local function only — never an import.
    if module.imports.get_by_index(idx).is_some() {
        return None;
    }
    let ft = module.get_func_type(idx)?;
    if ft.params.as_slice() != [WasmType::I32, WasmType::I64] || !ft.results.is_empty() {
        return None;
    }
    let body = &module.get_function(idx)?.body;
    if body
        .iter()
        .any(|i| matches!(i, WasmInstr::Call(_) | WasmInstr::CallIndirect(_)))
    {
        return None;
    }
    let has_void_check = body
        .windows(2)
        .any(|w| matches!(w, [WasmInstr::I64Const(2), WasmInstr::I64Eq]));
    let has_shift = body
        .windows(2)
        .any(|w| matches!(w, [WasmInstr::I64Const(32), WasmInstr::I64ShrU]));
    let has_tag4 = body
        .windows(2)
        .any(|w| matches!(w, [WasmInstr::I64Const(4), WasmInstr::I64Eq]));
    if !(has_void_check
        && has_shift
        && has_tag4
        && body.iter().any(|i| matches!(i, WasmInstr::Select)))
    {
        return None;
    }
    // The payload local is set right after the `>> 32; wrap` extract; the tag
    // local is the first `local.set` after the discriminant `if`'s closing `end`.
    let value_local = body.windows(2).find_map(|w| match w {
        [WasmInstr::I32WrapI64, WasmInstr::LocalSet(v)] => Some(*v),
        _ => None,
    })?;
    let select_pos = body.iter().position(|i| matches!(i, WasmInstr::Select))?;
    let end_pos = select_pos
        + body[select_pos..]
            .iter()
            .position(|i| matches!(i, WasmInstr::End))?;
    let tag_local = body[end_pos..].iter().find_map(|i| match i {
        WasmInstr::LocalSet(t) => Some(*t),
        _ => None,
    })?;
    // Each store is `local.get ptr; local.get <local>; i32.store off`.
    let mut val_off = None;
    let mut tag_off = None;
    for w in body.windows(2) {
        if let [WasmInstr::LocalGet(x), WasmInstr::I32Store(off)] = w {
            if *x == value_local {
                val_off = Some(*off as i32);
            } else if *x == tag_local {
                tag_off = Some(*off as i32);
            }
        }
    }
    Some(OptionDecodeLayout {
        tag_off: tag_off?,
        val_off: val_off?,
    })
}

/// True for a `Vec::first_index_of` method call (the only `Option` decode we
/// collapse to `.unwrap()`; its `None`/element-absent path is the
/// compiler-proven-dead arm here).
fn expr_is_first_index_of(e: &SorobanExpr) -> bool {
    matches!(e, SorobanExpr::MethodCall { method, .. } if method == "first_index_of")
}

// ---------------------------------------------------------------------------
// DataKey dispatcher folding (constant-selector micro-evaluation)
// ---------------------------------------------------------------------------
//
// The SDK lowers `DataKey::into_val` for a multi-variant storage-key enum to a
// *dispatcher*: `(i64 selector, i64 payload…) -> i64 Val` whose body
// `br_table`s over the selector, each arm building its variant's key —
// `Vec[Symbol]` for unit variants (the SDK vec-wraps those too),
// `Vec[Symbol, payload]` for data variants — from linear-memory strings.
// Inlining can't fold it (branch-sequential execution picks the wrong arm and
// the key degrades to `UnknownVal`), and structural per-arm string extraction
// is UNSAFE: arms permute through the `br_table`, and pointer locals are
// preloaded/overridden across arms (Band's "Relayer" is preloaded before the
// `br_table`, "RefData" overrides it in an arm), so body-order pairing
// mis-assigns names to selectors.
//
// `DkEval` instead *executes* the dispatcher's real bytecode for the concrete
// selector: symbol bytes come from the data section, the key shape from the
// actual `vec_new_from_linear_memory` window. Payload args flow through
// abstractly (`DkVal::Arg`) — pure moves only; any computation on them, any
// unmodeled instruction, any runtime-dependent branch, or a non-key result
// bails the whole fold so the call falls back to normal inlining (an honest
// `todo!`, never a fabricated key).

/// Hard step budget for one dispatcher evaluation (all interpreted calls included).
const DK_MAX_STEPS: u32 = 4096;
/// Max interpreted call depth below the dispatcher itself.
const DK_MAX_CALL_DEPTH: u32 = 4;
/// Max instructions in any single interpreted body.
const DK_MAX_BODY: usize = 400;
/// Max elements read out of a `vec_new_from_linear_memory` window.
const DK_MAX_VEC: i32 = 8;

/// Abstract value for the DataKey-dispatcher micro-evaluator.
#[derive(Clone, Debug, PartialEq)]
enum DkVal {
    I32(i32),
    I64(i64),
    /// A shadow-stack address, relative to the stack pointer at dispatcher entry.
    StackPtr(i32),
    /// The dispatcher's `i`-th argument, passed through abstractly (payloads).
    Arg(usize),
    /// A long (>9 char) `Symbol` built via host `symbol_new_from_linear_memory`.
    SymObj(String),
    /// A `Vec` built via host `vec_new_from_linear_memory` from tracked slots.
    VecVal(Vec<DkVal>),
}

/// One entered block during evaluation.
#[derive(Clone)]
struct DkFrame {
    /// Index of the matching `End`.
    end: usize,
    /// Result arity of the block (0 or 1).
    arity: usize,
    /// Value-stack height at block entry.
    height: usize,
}

/// Forward small-symbol codec — the exact inverse of
/// `DataSection::decode_symbol_val`. Chars pack MSB-first as 6-bit codes
/// (`_`=1, '0'..'9'=2..11, 'A'..'Z'=12..37, 'a'..'z'=38..63); the packed body
/// shifts left 8 and tags `0x0e` (SymbolSmall).
fn encode_symbol_small(name: &str) -> Option<i64> {
    if name.is_empty() || name.len() > 9 {
        return None;
    }
    let mut body: u64 = 0;
    for c in name.chars() {
        let code = match c {
            '_' => 1u64,
            '0'..='9' => 2 + (c as u64 - '0' as u64),
            'A'..='Z' => 12 + (c as u64 - 'A' as u64),
            'a'..='z' => 38 + (c as u64 - 'a' as u64),
            _ => return None,
        };
        body = (body << 6) | code;
    }
    Some(((body << 8) | TAG_SYMBOL_SMALL) as i64)
}

/// Cheap shape gate for `try_fold_datakey_dispatcher`: an internal function
/// whose body `br_table`s and transitively builds `Symbol`s from linear
/// memory. Loops and indirect calls are out of model (the symbol encoder's
/// own loop is handled by classification, never interpreted).
fn is_datakey_dispatcher(module: &WasmModule, func_idx: u32) -> bool {
    use crate::wasm::ir::WasmInstr;
    if module.imports.get_by_index(func_idx).is_some() {
        return false;
    }
    let Some(func) = module.get_function(func_idx) else {
        return false;
    };
    if func.body.len() > DK_MAX_BODY {
        return false;
    }
    let mut has_br_table = false;
    for ins in &func.body {
        match ins {
            WasmInstr::BrTable { .. } => has_br_table = true,
            WasmInstr::Loop { .. } | WasmInstr::CallIndirect(_) => return false,
            _ => {}
        }
    }
    has_br_table && func_reaches_symbol_encoder(module, func_idx, 0)
}

/// For each `Block`/`If` in a flat body: instr index → (matching `End`, `Else`).
/// An unmatched trailing `End` is the function terminator. Returns `None` on a
/// malformed nesting (the fold then bails).
fn dk_scan_blocks(
    body: &[crate::wasm::ir::WasmInstr],
) -> Option<HashMap<usize, (usize, Option<usize>)>> {
    use crate::wasm::ir::WasmInstr;
    let mut map = HashMap::new();
    let mut open: Vec<(usize, Option<usize>)> = Vec::new();
    for (i, ins) in body.iter().enumerate() {
        match ins {
            WasmInstr::Block { .. } | WasmInstr::Loop { .. } | WasmInstr::If { .. } => {
                open.push((i, None));
            }
            WasmInstr::Else => open.last_mut()?.1 = Some(i),
            WasmInstr::End => {
                if let Some((start, els)) = open.pop() {
                    map.insert(start, (i, els));
                }
            }
            _ => {}
        }
    }
    Some(map)
}

fn dk_block_arity(bt: &crate::wasm::ir::BlockType) -> Option<usize> {
    use crate::wasm::ir::BlockType;
    match bt {
        BlockType::Empty => Some(0),
        BlockType::Value(_) => Some(1),
        BlockType::FuncType(_) => None,
    }
}

fn dk_i32(v: &DkVal) -> Option<i32> {
    match v {
        DkVal::I32(x) => Some(*x),
        _ => None,
    }
}

fn dk_i64(v: &DkVal) -> Option<i64> {
    match v {
        DkVal::I64(x) => Some(*x),
        _ => None,
    }
}

/// Exit a block normally (its `End` reached): keep the block's results, drop
/// anything between them and the entry height.
fn dk_exit_block(stack: &mut Vec<DkVal>, fr: &DkFrame) -> Option<()> {
    if stack.len() < fr.height + fr.arity {
        return None;
    }
    let results = stack.split_off(stack.len() - fr.arity);
    stack.truncate(fr.height);
    stack.extend(results);
    Some(())
}

/// Take a branch to label `depth`: unwind to that frame carrying its results,
/// and resume after its `End`. (Loop frames cannot occur — bodies containing
/// `Loop` are rejected before interpretation.)
fn dk_branch(frames: &mut Vec<DkFrame>, stack: &mut Vec<DkVal>, depth: u32) -> Option<usize> {
    let idx = frames.len().checked_sub(1 + depth as usize)?;
    let fr = frames[idx].clone();
    if stack.len() < fr.arity || stack.len() - fr.arity < fr.height {
        return None;
    }
    let results = stack.split_off(stack.len() - fr.arity);
    stack.truncate(fr.height);
    stack.extend(results);
    frames.truncate(idx);
    Some(fr.end + 1)
}

/// Micro-evaluator state shared across the dispatcher and the small helpers it
/// calls (validators, thin wrappers). The shadow stack pointer (global 0) and
/// the shadow-stack memory persist across interpreted calls, exactly as at
/// runtime.
struct DkEval<'m> {
    module: &'m WasmModule,
    /// Shadow-stack cells: entry-SP-relative address → (value, store width).
    /// Loads must match the stored width exactly — no partial aliasing.
    mem: HashMap<i32, (DkVal, u32)>,
    /// Global 0 (the shadow stack pointer).
    sp: DkVal,
    steps: u32,
    /// A data-segment gap `[start, end)` PROVEN to hold zero-initialized
    /// memory at every execution point ([`gap_row_proven_zero`]) — a
    /// linker-elided all-zero descriptor row. Static loads inside it read
    /// `0`; everything else about gap memory stays out of model.
    gap_zero: Option<(u32, u32)>,
}

impl DkEval<'_> {
    fn store(&mut self, addr: i32, val: DkVal, width: u32) {
        // Invalidate any overlapping cell so stale halves can never be re-read.
        self.mem
            .retain(|&a, &mut (_, w)| a + w as i32 <= addr || a >= addr + width as i32);
        self.mem.insert(addr, (val, width));
    }

    fn load(&self, addr: &DkVal, offset: u32, width: u32) -> Option<DkVal> {
        match addr {
            DkVal::StackPtr(o) => {
                let a = o.checked_add(offset as i32)?;
                if let Some((v, w)) = self.mem.get(&a)
                    && *w == width
                {
                    return Some(v.clone());
                }
                // Narrower read fully inside a wider CONSTANT cell: pure
                // little-endian byte extraction (an `i64.store`d enum
                // discriminant read back with `i32.load` — blend-backstop's
                // descriptor shape). Cells never overlap (`store`
                // invalidates), so at most one covers the range; a covering
                // SYMBOLIC cell cannot be sliced — the load stays out of
                // model.
                for (a0, (v, w0)) in &self.mem {
                    if *a0 <= a && a + width as i32 <= a0 + *w0 as i32 {
                        let c: u64 = match v {
                            DkVal::I32(x) => *x as u32 as u64,
                            DkVal::I64(x) => *x as u64,
                            _ => return None,
                        };
                        let shifted = c >> (8 * (a - a0) as u32);
                        let masked = if width == 8 {
                            shifted
                        } else {
                            shifted & ((1u64 << (8 * width)) - 1)
                        };
                        return Some(match width {
                            8 => DkVal::I64(masked as i64),
                            _ => DkVal::I32(masked as u32 as i32),
                        });
                    }
                }
                None
            }
            // Static data reads (e.g. variant-name tables); never shadow-stack.
            DkVal::I32(a) if *a > 1024 => {
                let start = (*a as u32).checked_add(offset)?;
                let bytes = match self
                    .module
                    .data_sections
                    .read_bytes_zero_extended(start, width)
                {
                    Some(b) => b,
                    // A read entirely inside the PROVEN-zero gap row (a
                    // linker-elided all-zero descriptor) observes WASM's
                    // zero-initialized memory. Unproven gaps stay out of
                    // model, exactly as before.
                    None if self.gap_zero.is_some_and(|(lo, hi)| {
                        start >= lo && start.checked_add(width).is_some_and(|e| e <= hi)
                    }) =>
                    {
                        cov_mark::hit!(dk_gap_zero_read);
                        vec![0u8; width as usize]
                    }
                    None => return None,
                };
                let mut v: u64 = 0;
                for (i, b) in bytes.iter().enumerate() {
                    v |= (*b as u64) << (8 * i);
                }
                Some(match width {
                    8 => DkVal::I64(v as i64),
                    _ => DkVal::I32(v as u32 as i32),
                })
            }
            _ => None,
        }
    }

    /// Handle a `call` inside an interpreted body: classify `(ptr, len) -> Val`
    /// symbol/vec builders (computed from static data, never interpreted —
    /// the symbol encoder contains a loop), otherwise recursively interpret.
    /// Any direct host-import call is out of model.
    fn handle_call(&mut self, target: u32, stack: &mut Vec<DkVal>, depth: u32) -> Option<()> {
        use crate::wasm::ir::WasmType;
        if self.module.imports.get_by_index(target).is_some() {
            return None;
        }
        let ft = self.module.get_func_type(target)?;
        let n = ft.params.len();
        if stack.len() < n {
            return None;
        }
        let args = stack.split_off(stack.len() - n);

        if ft.params.as_slice() == [WasmType::I32, WasmType::I32]
            && ft.results.as_slice() == [WasmType::I64]
        {
            let reaches_sym = func_reaches_symbol_encoder(self.module, target, 0);
            let reaches_vec = func_reaches_host(
                self.module,
                target,
                HostModule::Vec,
                "vec_new_from_linear_memory",
                0,
            );
            match (reaches_sym, reaches_vec) {
                (true, false) => {
                    // Symbol builder: read the real name from static data.
                    let (DkVal::I32(ptr), DkVal::I32(len)) = (&args[0], &args[1]) else {
                        return None;
                    };
                    if *ptr <= 1024 || *len <= 0 || *len > 32 {
                        return None;
                    }
                    let name = self
                        .module
                        .data_sections
                        .read_string(*ptr as u32, *len as u32)?;
                    if name.is_empty()
                        || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                    {
                        return None;
                    }
                    stack.push(if name.len() <= 9 {
                        DkVal::I64(encode_symbol_small(&name)?)
                    } else {
                        DkVal::SymObj(name)
                    });
                    return Some(());
                }
                (false, true) => {
                    // Vec builder: collect the elements from the tracked window.
                    let (DkVal::StackPtr(o), DkVal::I32(count)) = (&args[0], &args[1]) else {
                        return None;
                    };
                    if *count <= 0 || *count > DK_MAX_VEC {
                        return None;
                    }
                    let mut elems = Vec::new();
                    for i in 0..*count {
                        let (v, w) = self.mem.get(&(o.checked_add(8 * i)?))?;
                        if *w != 8 {
                            return None;
                        }
                        elems.push(v.clone());
                    }
                    stack.push(DkVal::VecVal(elems));
                    return Some(());
                }
                (true, true) => return None,
                (false, false) => {}
            }
        }

        // The 3-param VOID symbol builder `(i32 out, i32 str_ptr, i32
        // str_len)` — the SDK's long-symbol out-pointer protocol. Same
        // modeling as `try_lower_symbol_builder`: the `0` success
        // discriminant at `out+0`, the symbol Val at `out+8`; the symbol
        // name comes from real static data under the same alnum gates.
        if ft.params.as_slice() == [WasmType::I32, WasmType::I32, WasmType::I32]
            && ft.results.is_empty()
            && is_symbol_from_lm_builder(self.module, target)
        {
            let (DkVal::StackPtr(o), DkVal::I32(ptr), DkVal::I32(len)) =
                (&args[0], &args[1], &args[2])
            else {
                return None;
            };
            if *ptr <= 1024 || *len <= 0 || *len > 32 {
                return None;
            }
            let name = self
                .module
                .data_sections
                .read_string(*ptr as u32, *len as u32)?;
            if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                return None;
            }
            let sym = if name.len() <= 9 {
                DkVal::I64(encode_symbol_small(&name)?)
            } else {
                DkVal::SymObj(name)
            };
            let o = *o;
            self.store(o, DkVal::I32(0), 4);
            self.store(o.checked_add(8)?, sym, 8);
            return Some(());
        }

        if let Some(v) = self.eval_call(target, args, depth + 1)? {
            stack.push(v);
        }
        Some(())
    }

    /// Interpret one function body. Outer `None` = anything out of model
    /// (bail the fold); inner value = the function's result (None for void).
    fn eval_call(&mut self, func_idx: u32, args: Vec<DkVal>, depth: u32) -> Option<Option<DkVal>> {
        use crate::wasm::ir::{WasmInstr as WI, WasmType};
        if depth > DK_MAX_CALL_DEPTH {
            return None;
        }
        let func = self.module.get_function(func_idx)?;
        if func.body.len() > DK_MAX_BODY
            || func
                .body
                .iter()
                .any(|i| matches!(i, WI::Loop { .. } | WI::CallIndirect(_)))
        {
            return None;
        }
        let ft = self.module.get_func_type(func_idx)?;
        if ft.results.len() > 1 || args.len() != ft.params.len() {
            return None;
        }
        let result_arity = ft.results.len();

        let mut locals = args;
        for ty in &func.locals {
            locals.push(match ty {
                WasmType::I32 => DkVal::I32(0),
                WasmType::I64 => DkVal::I64(0),
                _ => return None,
            });
        }

        let ends = dk_scan_blocks(&func.body)?;
        let mut stack: Vec<DkVal> = Vec::new();
        let mut frames: Vec<DkFrame> = Vec::new();
        let mut ip = 0usize;

        macro_rules! bin_i32 {
            ($f:expr) => {{
                let b = dk_i32(&stack.pop()?)?;
                let a = dk_i32(&stack.pop()?)?;
                stack.push(DkVal::I32($f(a, b)));
            }};
        }
        macro_rules! bin_i64 {
            ($f:expr) => {{
                let b = dk_i64(&stack.pop()?)?;
                let a = dk_i64(&stack.pop()?)?;
                stack.push(DkVal::I64($f(a, b)));
            }};
        }
        macro_rules! cmp_i32 {
            ($f:expr) => {{
                let b = dk_i32(&stack.pop()?)?;
                let a = dk_i32(&stack.pop()?)?;
                stack.push(DkVal::I32($f(a, b) as i32));
            }};
        }
        macro_rules! cmp_i64 {
            ($f:expr) => {{
                let b = dk_i64(&stack.pop()?)?;
                let a = dk_i64(&stack.pop()?)?;
                stack.push(DkVal::I32($f(a, b) as i32));
            }};
        }

        loop {
            self.steps += 1;
            if self.steps > DK_MAX_STEPS {
                return None;
            }
            let Some(ins) = func.body.get(ip) else {
                break; // fell off the end = function return
            };
            if *DBG_DKTRACE {
                eprintln!("[DKTRACE] f={func_idx} ip={ip} {ins:?} stack={stack:?}");
            }
            match ins {
                WI::I32Const(v) => stack.push(DkVal::I32(*v)),
                WI::I64Const(v) => stack.push(DkVal::I64(*v)),
                WI::LocalGet(n) => stack.push(locals.get(*n as usize)?.clone()),
                WI::LocalSet(n) => *locals.get_mut(*n as usize)? = stack.pop()?,
                WI::LocalTee(n) => {
                    let v = stack.last()?.clone();
                    *locals.get_mut(*n as usize)? = v;
                }
                WI::GlobalGet(0) => stack.push(self.sp.clone()),
                WI::GlobalSet(0) => self.sp = stack.pop()?,
                WI::Drop => {
                    stack.pop()?;
                }
                WI::Select => {
                    let c = dk_i32(&stack.pop()?)?;
                    let b = stack.pop()?;
                    let a = stack.pop()?;
                    stack.push(if c != 0 { a } else { b });
                }
                WI::Nop => {}

                // Pointer-aware i32 add/sub (shadow-stack frame arithmetic);
                // everything else concrete-only.
                WI::I32Add => {
                    let b = stack.pop()?;
                    let a = stack.pop()?;
                    stack.push(match (a, b) {
                        (DkVal::I32(x), DkVal::I32(y)) => DkVal::I32(x.wrapping_add(y)),
                        (DkVal::StackPtr(o), DkVal::I32(k))
                        | (DkVal::I32(k), DkVal::StackPtr(o)) => DkVal::StackPtr(o.checked_add(k)?),
                        _ => return None,
                    });
                }
                WI::I32Sub => {
                    let b = stack.pop()?;
                    let a = stack.pop()?;
                    stack.push(match (a, b) {
                        (DkVal::I32(x), DkVal::I32(y)) => DkVal::I32(x.wrapping_sub(y)),
                        (DkVal::StackPtr(o), DkVal::I32(k)) => DkVal::StackPtr(o.checked_sub(k)?),
                        _ => return None,
                    });
                }
                WI::I32Mul => bin_i32!(|a: i32, b: i32| a.wrapping_mul(b)),
                WI::I32And => bin_i32!(|a, b| a & b),
                WI::I32Or => bin_i32!(|a, b| a | b),
                WI::I32Xor => bin_i32!(|a, b| a ^ b),
                WI::I32Shl => bin_i32!(|a: i32, b: i32| a.wrapping_shl(b as u32)),
                WI::I32ShrU => bin_i32!(|a: i32, b: i32| ((a as u32) >> (b as u32 & 31)) as i32),
                WI::I32ShrS => bin_i32!(|a: i32, b: i32| a.wrapping_shr(b as u32)),
                WI::I64Add => bin_i64!(|a: i64, b: i64| a.wrapping_add(b)),
                WI::I64Sub => bin_i64!(|a: i64, b: i64| a.wrapping_sub(b)),
                WI::I64Mul => bin_i64!(|a: i64, b: i64| a.wrapping_mul(b)),
                WI::I64And => bin_i64!(|a, b| a & b),
                WI::I64Or => bin_i64!(|a, b| a | b),
                WI::I64Xor => bin_i64!(|a, b| a ^ b),
                WI::I64Shl => bin_i64!(|a: i64, b: i64| a.wrapping_shl(b as u32)),
                WI::I64ShrU => bin_i64!(|a: i64, b: i64| ((a as u64) >> (b as u64 & 63)) as i64),
                WI::I64ShrS => bin_i64!(|a: i64, b: i64| a.wrapping_shr(b as u32)),

                WI::I32Eqz => {
                    let a = dk_i32(&stack.pop()?)?;
                    stack.push(DkVal::I32((a == 0) as i32));
                }
                WI::I64Eqz => {
                    let a = dk_i64(&stack.pop()?)?;
                    stack.push(DkVal::I32((a == 0) as i32));
                }
                WI::I32Eq => cmp_i32!(|a, b| a == b),
                WI::I32Ne => cmp_i32!(|a, b| a != b),
                WI::I32LtS => cmp_i32!(|a, b| a < b),
                WI::I32LtU => cmp_i32!(|a: i32, b: i32| (a as u32) < (b as u32)),
                WI::I32GtS => cmp_i32!(|a, b| a > b),
                WI::I32GtU => cmp_i32!(|a: i32, b: i32| (a as u32) > (b as u32)),
                WI::I32LeS => cmp_i32!(|a, b| a <= b),
                WI::I32LeU => cmp_i32!(|a: i32, b: i32| (a as u32) <= (b as u32)),
                WI::I32GeS => cmp_i32!(|a, b| a >= b),
                WI::I32GeU => cmp_i32!(|a: i32, b: i32| (a as u32) >= (b as u32)),
                WI::I64Eq => cmp_i64!(|a, b| a == b),
                WI::I64Ne => cmp_i64!(|a, b| a != b),
                WI::I64LtS => cmp_i64!(|a, b| a < b),
                WI::I64LtU => cmp_i64!(|a: i64, b: i64| (a as u64) < (b as u64)),
                WI::I64GtS => cmp_i64!(|a, b| a > b),
                WI::I64GtU => cmp_i64!(|a: i64, b: i64| (a as u64) > (b as u64)),
                WI::I64LeS => cmp_i64!(|a, b| a <= b),
                WI::I64LeU => cmp_i64!(|a: i64, b: i64| (a as u64) <= (b as u64)),
                WI::I64GeS => cmp_i64!(|a, b| a >= b),
                WI::I64GeU => cmp_i64!(|a: i64, b: i64| (a as u64) >= (b as u64)),

                WI::I32WrapI64 => {
                    let a = dk_i64(&stack.pop()?)?;
                    stack.push(DkVal::I32(a as i32));
                }
                WI::I64ExtendI32U => {
                    let a = dk_i32(&stack.pop()?)?;
                    stack.push(DkVal::I64(a as u32 as i64));
                }
                WI::I64ExtendI32S => {
                    let a = dk_i32(&stack.pop()?)?;
                    stack.push(DkVal::I64(a as i64));
                }

                WI::I32Load(off) => {
                    let addr = stack.pop()?;
                    stack.push(self.load(&addr, *off, 4)?);
                }
                WI::I64Load(off) => {
                    let addr = stack.pop()?;
                    stack.push(self.load(&addr, *off, 8)?);
                }
                WI::I32Load8U(off) => {
                    let addr = stack.pop()?;
                    stack.push(self.load(&addr, *off, 1)?);
                }
                WI::I64Load32U(off) => {
                    // A 4-byte zero-extending load: constants extend
                    // concretely. A symbolic cell REFUSES: the 4-wide store
                    // that seeded it may have been an `i32.wrap_i64` whose
                    // identity-preserving lift kept the full 64-bit value in
                    // the abstract cell, so passing the token through would
                    // embed the untruncated expression where the runtime
                    // holds only the low 32 bits (greptile P1). A symbolic
                    // pass-through needs a proof the source is genuinely
                    // 32-bit — the tag/type-hinted payloads planned for the
                    // packing-chain tranche.
                    let addr = stack.pop()?;
                    stack.push(match self.load(&addr, *off, 4)? {
                        DkVal::I32(x) => DkVal::I64(x as u32 as i64),
                        _ => return None,
                    });
                }
                WI::I32Store(off) => {
                    let val = stack.pop()?;
                    let DkVal::StackPtr(o) = stack.pop()? else {
                        return None;
                    };
                    self.store(o.checked_add(*off as i32)?, val, 4);
                }
                WI::I64Store(off) => {
                    let val = stack.pop()?;
                    let DkVal::StackPtr(o) = stack.pop()? else {
                        return None;
                    };
                    self.store(o.checked_add(*off as i32)?, val, 8);
                }

                WI::Block { block_type } => {
                    let (end, _) = *ends.get(&ip)?;
                    frames.push(DkFrame {
                        end,
                        arity: dk_block_arity(block_type)?,
                        height: stack.len(),
                    });
                }
                WI::If { block_type } => {
                    let cond = dk_i32(&stack.pop()?)?;
                    let (end, els) = *ends.get(&ip)?;
                    let fr = DkFrame {
                        end,
                        arity: dk_block_arity(block_type)?,
                        height: stack.len(),
                    };
                    if cond != 0 {
                        frames.push(fr);
                    } else if let Some(e) = els {
                        frames.push(fr);
                        ip = e + 1;
                        continue;
                    } else {
                        ip = end + 1;
                        continue;
                    }
                }
                WI::Else => {
                    // End of the taken then-branch: exit past the matching End.
                    let fr = frames.pop()?;
                    dk_exit_block(&mut stack, &fr)?;
                    ip = fr.end + 1;
                    continue;
                }
                WI::End => {
                    if let Some(fr) = frames.pop() {
                        dk_exit_block(&mut stack, &fr)?;
                    } else {
                        break; // function end
                    }
                }
                WI::Br(d) => {
                    ip = dk_branch(&mut frames, &mut stack, *d)?;
                    continue;
                }
                WI::BrIf(d) => {
                    let cond = dk_i32(&stack.pop()?)?;
                    if cond != 0 {
                        ip = dk_branch(&mut frames, &mut stack, *d)?;
                        continue;
                    }
                }
                WI::BrTable { targets, default } => {
                    let idx = dk_i32(&stack.pop()?)? as u32 as usize;
                    let d = targets.get(idx).copied().unwrap_or(*default);
                    ip = dk_branch(&mut frames, &mut stack, d)?;
                    continue;
                }
                WI::Return => break,
                // A trapping path means the selector is invalid at runtime —
                // nothing to recover.
                WI::Unreachable => return None,
                WI::Call(t) => self.handle_call(*t, &mut stack, depth)?,
                _ => return None,
            }
            ip += 1;
        }

        if result_arity == 1 {
            Some(Some(stack.pop()?))
        } else {
            Some(None)
        }
    }
}

/// True when the body contains the verbatim limb-forwarding call window
/// `[local.get L, local.get 1, local.get 2, local.get 3, local.get 4,
/// call target]` — the delegation wrapper passing its own four i64 limb
/// params unchanged to the core (with a fresh scratch out-pointer `L`).
/// Anything else (reordered, transformed, or partial forwarding) fails, so
/// the wrapper provably computes exactly what the core computes.
fn forwards_limb_params_verbatim(func: &crate::wasm::ir::WasmFunction, target: u32) -> bool {
    use crate::wasm::ir::WasmInstr;
    func.body.windows(6).any(|w| {
        matches!(
            w,
            [
                WasmInstr::LocalGet(_),
                WasmInstr::LocalGet(1),
                WasmInstr::LocalGet(2),
                WasmInstr::LocalGet(3),
                WasmInstr::LocalGet(4),
                WasmInstr::Call(t)
            ] if *t == target
        )
    })
}

/// Where an i128 soft-arith helper writes its result limbs relative to the output
/// pointer (param 0). Unchecked helpers (the SDK's inline soft-arith) write the
/// value directly as `{lo@0, hi@8}`; checked (`Result<i128,E>`-returning) helpers
/// — used by SDK consumers like Soroswap that call `checked_mul`/`checked_div` —
/// reserve `+0` for the status discriminant and write `{lo@8, hi@16}`. Detected by
/// whether the body computes the `param0 + 16` store address
/// (`local.get 0; i32.const 16; i32.add`): only the 24-byte checked layout
/// addresses `+16`; the 16-byte unchecked layout never does, and a multiply leaf
/// that surfaces overflow through a separate `i32` flag pointer writes its hi limb
/// at `+8`, so it stays unchecked.
fn i128_result_offsets(func: &crate::wasm::ir::WasmFunction) -> (i32, i32) {
    use crate::wasm::ir::WasmInstr;
    let checked = func.body.windows(3).any(|w| {
        matches!(
            w,
            [
                WasmInstr::LocalGet(0),
                WasmInstr::I32Const(16),
                WasmInstr::I32Add
            ]
        )
    });
    if checked { (8, 16) } else { (0, 8) }
}

fn detect_i128_intrinsic(module: &WasmModule, func_idx: u32) -> Option<I128Intrinsic> {
    detect_i128_intrinsic_inner(module, func_idx, 0)
}

fn detect_i128_intrinsic_inner(
    module: &WasmModule,
    func_idx: u32,
    depth: u32,
) -> Option<I128Intrinsic> {
    if depth > 2 || !is_two_i128_operand_helper(module, func_idx) {
        return None;
    }
    let func = module.get_function(func_idx)?;
    let fp = opcode_counts(func);
    let (res_lo_off, res_hi_off) = i128_result_offsets(func);
    let layout = |op: I128Op| I128Intrinsic {
        op,
        a_lo: 1,
        a_hi: 2,
        b_lo: 3,
        b_hi: 4,
        res_lo_off,
        res_hi_off,
    };

    // Leaf unsigned multiply: schoolbook 32-bit limb products, two stores, no calls.
    if fp.calls.is_empty() && fp.mul >= 5 && fp.store >= 2 && fp.div == 0 {
        return Some(layout(I128Op::Mul));
    }
    // Leaf / near-leaf unsigned divide: any inline `I64DivU`/`I64DivS` marks a
    // division core. A 128-bit multiply never divides (branches 1 and 3 require
    // `div == 0`), so a 64-bit division op uniquely identifies a divide — including
    // a Knuth long-division core whose quotient estimation legitimately contains
    // several `i64.mul` (the real mainnet core has mul == 7, which the old
    // `mul <= 6` cap wrongly rejected).
    if fp.div >= 1 {
        return Some(layout(I128Op::Div));
    }
    // Widening / fixed-point multiply (6-param, delegates the limb products to a
    // multiply leaf several times): the low-128 result is `a * b`.
    if fp.div == 0
        && fp.calls.len() >= 2
        && fp.calls.iter().all(|&t| {
            matches!(
                detect_i128_intrinsic_inner(module, t, depth + 1).map(|i| i.op),
                Some(I128Op::Mul)
            )
        })
    {
        return Some(layout(I128Op::Mul));
    }
    // Signed wrapper: `abs(a)`/`abs(b)` (the Select + I64Xor sign-fixup idiom) then
    // a single delegated call to an unsigned core; the sign-corrected result keeps
    // the core's operation.
    if fp.select >= 2 && fp.xor >= 1 && fp.calls.len() == 1 {
        let core = detect_i128_intrinsic_inner(module, fp.calls[0], depth + 1)?;
        return Some(layout(core.op));
    }
    // Round-up-on-inexact divide wrapper (e.g. Soroswap's fee `div_ceil`): no
    // direct mul/div of its own, delegates the truncating division to a Div core,
    // then adds 1 to the quotient whenever the remainder is nonzero. Empirically
    // (executed under wasmi) it computes `a / b + (a % b != 0) as i128` over the
    // full signed domain — NOT a sign-aware ceiling. Distinguished from a plain
    // signed-div wrapper by the post-division `+1` increment idiom.
    if fp.div == 0
        && fp.mul == 0
        && fp.calls.iter().any(|&t| {
            matches!(
                detect_i128_intrinsic_inner(module, t, depth + 1).map(|i| i.op),
                Some(I128Op::Div)
            )
        })
        && has_inexact_increment(func)
    {
        return Some(layout(I128Op::DivCeil));
    }
    // Plain delegation wrapper: NO arithmetic of its own (blend's `232`-shape —
    // scratch-buffer adapter around a divmod core that keeps only the
    // quotient). Verified by execution against the mainnet blend pools: the
    // core (`227`) is compiler-rt-style unsigned 128÷128 divmod writing
    // `[q_lo@0, q_hi@8, r@16..]`; the wrapper forwards its four limb params
    // verbatim and copies back only `[0, 8]` — so it IS the core's operation
    // at the standard unchecked layout. Airtight: requires zero own
    // mul/div/select/xor, exactly one classifiable callee, the literal
    // `[local.get L, local.get 1..4, call]` verbatim-forwarding window, and
    // no post-division rounding fixup (the DivCeil branch above claims that
    // shape — this one must never shadow it).
    if fp.mul == 0
        && fp.div == 0
        && fp.select == 0
        && fp.xor == 0
        && fp.calls.len() == 1
        && forwards_limb_params_verbatim(func, fp.calls[0])
        && !has_inexact_increment(func)
        && delegation_copies_core_result(func, fp.calls[0])
    {
        let core = detect_i128_intrinsic_inner(module, fp.calls[0], depth + 1)?;
        cov_mark::hit!(i128_delegation_wrapper_classified);
        return Some(layout(core.op));
    }
    None
}

/// Abstract values for the delegation-wrapper copy-back verifier.
#[derive(Clone, PartialEq, Debug)]
enum DelegVal {
    /// The wrapper's own out-pointer (param 0).
    OutPtr,
    /// The scratch buffer forwarded to the core as ITS out-pointer.
    Scratch,
    /// `Scratch + 8` (the computed-address form of the hi-limb slot).
    ScratchOff8,
    /// The core's result limbs, loaded from the scratch after the call.
    CoreLo,
    CoreHi,
    /// A small i32 constant (address arithmetic operand).
    ConstI32(i32),
    Other,
}

/// Prove — by linear abstract interpretation over the whole (straight-line)
/// body — that a delegation wrapper RETURNS the core's result: after the
/// forwarded call, the only stores through the out-pointer are
/// `out[0] = scratch[0]` (the core's lo limb) and `out[8] = scratch[8]`
/// (hi), possibly via single i64 temp locals; and if the wrapper forwards
/// its own out-pointer directly, that it never overwrites the result. Any
/// control flow, unrecognized instruction, store of a non-core value
/// through out, swapped limbs, or read of the core's other output slots
/// (a divmod remainder) fails the proof (greptile P1 on PR #43).
fn delegation_copies_core_result(func: &crate::wasm::ir::WasmFunction, core: u32) -> bool {
    use crate::wasm::ir::WasmInstr as WI;
    let n_params = 5; // gated upstream: (i32, i64, i64, i64, i64)
    let mut locals: Vec<DelegVal> = vec![DelegVal::Other; n_params + func.locals.len()];
    locals[0] = DelegVal::OutPtr;
    let mut stack: Vec<DelegVal> = Vec::new();
    let mut call_seen = false;
    // Which abstract pointer the core received as its out: Scratch (fresh
    // buffer, results must be copied out) or OutPtr (direct — results are
    // already in place and must not be overwritten).
    let mut core_out: Option<DelegVal> = None;
    let mut stored_lo = false;
    let mut stored_hi = false;
    for ins in &func.body {
        match ins {
            // Frame prologue/epilogue and address arithmetic.
            WI::GlobalGet(_) => stack.push(DelegVal::Other),
            WI::GlobalSet(_) => {
                stack.pop();
            }
            WI::I32Const(c) => stack.push(DelegVal::ConstI32(*c)),
            WI::I32Sub => {
                stack.pop();
                stack.pop();
                // `global.get 0; i32.const N; i32.sub` — the scratch allocation.
                stack.push(DelegVal::Scratch);
            }
            WI::I32Add => {
                let b = stack.pop();
                let a = stack.pop();
                stack.push(match (a, b) {
                    (Some(DelegVal::Scratch), Some(DelegVal::ConstI32(8)))
                    | (Some(DelegVal::ConstI32(8)), Some(DelegVal::Scratch)) => {
                        DelegVal::ScratchOff8
                    }
                    _ => DelegVal::Other,
                });
            }
            WI::LocalGet(i) => {
                stack.push(locals.get(*i as usize).cloned().unwrap_or(DelegVal::Other))
            }
            WI::LocalSet(i) => {
                let v = stack.pop().unwrap_or(DelegVal::Other);
                if let Some(slot) = locals.get_mut(*i as usize) {
                    *slot = v;
                }
            }
            WI::LocalTee(i) => {
                let v = stack.last().cloned().unwrap_or(DelegVal::Other);
                if let Some(slot) = locals.get_mut(*i as usize) {
                    *slot = v;
                }
            }
            WI::Call(t) if *t == core && !call_seen => {
                if stack.len() < n_params {
                    return false;
                }
                let args = stack.split_off(stack.len() - n_params);
                match args.first() {
                    Some(DelegVal::Scratch) => core_out = Some(DelegVal::Scratch),
                    Some(DelegVal::OutPtr) => core_out = Some(DelegVal::OutPtr),
                    _ => return false,
                }
                call_seen = true;
            }
            WI::I64Load(off) => {
                let addr = stack.pop().unwrap_or(DelegVal::Other);
                if !call_seen || core_out != Some(DelegVal::Scratch) {
                    return false; // no reads before the call / in direct mode
                }
                stack.push(match (addr, off) {
                    (DelegVal::Scratch, 0) => DelegVal::CoreLo,
                    (DelegVal::Scratch, 8) | (DelegVal::ScratchOff8, 0) => DelegVal::CoreHi,
                    _ => return false, // remainder slots / unknown source
                });
            }
            WI::I64Store(off) => {
                let value = stack.pop().unwrap_or(DelegVal::Other);
                let addr = stack.pop().unwrap_or(DelegVal::Other);
                if addr != DelegVal::OutPtr {
                    return false; // stores anywhere else are unmodeled
                }
                match (off, value) {
                    (0, DelegVal::CoreLo) => stored_lo = true,
                    (8, DelegVal::CoreHi) => stored_hi = true,
                    _ => return false, // swapped limbs / non-core value
                }
            }
            // The function-level terminator. A NESTED block's End is
            // unreachable here — Block/Loop/If all fail the whitelist below.
            WI::End => {}
            // Anything else — control flow, arithmetic, other calls,
            // constants stored as i64 — is outside the proven shape.
            _ => return false,
        }
    }
    match core_out {
        // Scratch mode: both limbs must have been copied out.
        Some(DelegVal::Scratch) => stored_lo && stored_hi,
        // Direct mode: the core wrote out[0,8] itself; the body proved it
        // never loaded or stored anything after (those arms return false
        // unless in scratch mode).
        Some(DelegVal::OutPtr) => !stored_lo && !stored_hi,
        _ => false,
    }
}

/// True if the body contains the "+1 when the division was inexact" idiom that
/// marks a round-up divide wrapper: a remainder-zero test (`i64.or; i64.eqz`,
/// combining the two remainder limbs) AND a literal-`1` increment of the
/// quotient (`i64.const 1; i64.add`). A plain truncating-div wrapper has neither.
fn has_inexact_increment(func: &crate::wasm::ir::WasmFunction) -> bool {
    use crate::wasm::ir::WasmInstr;
    let body = &func.body;
    let has_increment = body
        .windows(2)
        .any(|w| matches!(w, [WasmInstr::I64Const(1), WasmInstr::I64Add]));
    let has_remainder_test = body
        .windows(2)
        .any(|w| matches!(w, [WasmInstr::I64Or, WasmInstr::I64Eqz]));
    has_increment && has_remainder_test
}

/// Rebuild a whole 128-bit operand from its two i64 limb args. Returns the value
/// and whether it came from a genuinely limb-tracked source (`true`) versus a
/// best-effort recovery (`false`). Returns `None` for degraded limb-soup.
///
/// The cleanliness flag gates the best-effort cases at the call site: lowering a
/// helper only fires when at least one operand is genuinely limb-tracked, so a
/// real i128 multiply whose operands are *both* mere constants/handles (as in
/// non-share-math contexts) is left to inline rather than fabricated.
fn reconstruct_i128_operand(lo: &StackVal, hi: &StackVal) -> Option<(StackVal, bool)> {
    match (lo, hi) {
        // The canonical clean case: both limbs tag the SAME source 128-bit value.
        (
            StackVal::I128Limb {
                value: lv,
                hi: false,
            },
            StackVal::I128Limb {
                value: hv,
                hi: true,
            },
        ) if lv == hv => Some(((**lv).clone(), true)),
        // Best-effort but faithful: a clean low limb whose high limb degraded (e.g.
        // a spilled hi word reloaded as an opaque local). A lone limb already lowers
        // to its source value, so recover the source rather than dropping to soup.
        // This is still genuinely limb-tracked, so it counts as clean.
        (StackVal::I128Limb { value, hi: false }, h) if !is_clean_hi_limb(h) => {
            Some(((**value).clone(), true))
        }
        // A small i128 constant carried as two i64 constant limbs (e.g. fee
        // factors `(997, 0)` / `(1000, 0)`). Not limb-tracked → best-effort.
        (StackVal::I64(l), StackVal::I64(h)) => {
            let v = ((*h as i128) << 64) | (*l as u64 as i128);
            Some((
                StackVal::HostCallResult(Box::new(SorobanExpr::I128Literal(v))),
                false,
            ))
        }
        // A 128-bit value spilled WHOLE to one slot and reloaded as the low limb
        // (storage/cross-contract i128s the SDK keeps as a single Object handle):
        // the operand is that whole value; the degraded high arg is the junk hi word.
        // Best-effort — only trustworthy when paired with a limb-tracked operand.
        (lo, h) if is_whole_i128_value(lo) && !is_clean_hi_limb(h) => Some((lo.clone(), false)),
        // Open-coded i128 add/sub (carry/borrow limb chains the SDK emits inline
        // rather than via a helper call).
        _ => reconstruct_i128_addsub(lo, hi),
    }
}

/// Recognize the open-coded i128 add/sub limb idiom — the two's-complement
/// carry/borrow chains the SDK emits inline (no helper call) — and rebuild the
/// whole 128-bit value as `Add`/`Sub` of its recursively-reconstructed operands.
///
/// Borrow-subtract `A - B`:
///   lo = A_lo - B_lo
///   hi = (A_hi - B_hi) - (A_lo <u B_lo)            // the borrow
/// Carry-add `A + B`:
///   lo = A_lo + B_lo
///   hi = (lo <u addend_lo) + (B_hi + A_hi)         // the carry; operand order varies
///
/// Strictly structural: the borrow/carry comparison must reference the SAME limb
/// sub-expressions as the `lo` computation, and BOTH operands must reconstruct
/// cleanly. So it can only fire on a genuine 128-bit add/sub — never on the
/// `0 - x` negations the signed mul/div wrappers emit (whose hi limb is
/// `0 - (x_hi + (x_lo != 0))`, matching neither shape).
fn reconstruct_i128_addsub(lo: &StackVal, hi: &StackVal) -> Option<(StackVal, bool)> {
    // --- Borrow-subtract: lo = A_lo - B_lo, hi = (A_hi - B_hi) - (A_lo <u B_lo) ---
    if let StackVal::BinOp(a_lo, BinOper::Sub, b_lo) = lo
        && let StackVal::BinOp(hi_diff, BinOper::Sub, borrow) = hi
        && let StackVal::BinOp(a_hi, BinOper::Sub, b_hi) = &**hi_diff
        && is_unsigned_lt(borrow, a_lo, b_lo)
    {
        let (a, a_clean) = reconstruct_i128_operand(a_lo, a_hi)?;
        let (b, b_clean) = reconstruct_i128_operand(b_lo, b_hi)?;
        return (a_clean && b_clean).then(|| {
            (
                StackVal::BinOp(Box::new(a), BinOper::Sub, Box::new(b)),
                true,
            )
        });
    }
    // --- Add of a clean value and a small positive constant K (K fits the low
    //     limb, K_hi = 0): lo = A_lo + K ; hi = A_hi + carry, where the carry is
    //     `(A_lo + K) <u K` — which the compiler folds to `Eqz(lo)` when K == 1.
    //     Soroswap's `get_amount_in` applies this `+ 1` to its rounded quotient. ---
    if let StackVal::BinOp(a_lo, BinOper::Add, k) = lo
        && let StackVal::I64(kv) = &**k
        && *kv > 0
        && let StackVal::BinOp(s1, BinOper::Add, s2) = hi
    {
        let is_const_carry = |c: &StackVal| match c {
            StackVal::Eqz(inner) => *kv == 1 && **inner == *lo,
            _ => is_unsigned_lt(c, lo, k),
        };
        let a_hi = if is_const_carry(s2) {
            Some(&**s1)
        } else if is_const_carry(s1) {
            Some(&**s2)
        } else {
            None
        };
        if let Some(a_hi) = a_hi {
            let (a, a_clean) = reconstruct_i128_operand(a_lo, a_hi)?;
            return a_clean.then(|| {
                (
                    StackVal::BinOp(
                        Box::new(a),
                        BinOper::Add,
                        Box::new(StackVal::HostCallResult(Box::new(
                            SorobanExpr::I128Literal(*kv as i128),
                        ))),
                    ),
                    true,
                )
            });
        }
        return None;
    }
    // --- Carry-add: lo = A_lo + B_lo, hi = (lo <u addend_lo) + (B_hi + A_hi) ---
    if let StackVal::BinOp(x_lo, BinOper::Add, y_lo) = lo
        && let StackVal::BinOp(s1, BinOper::Add, s2) = hi
    {
        // One summand of `hi` is the carry `(lo <u addend_lo)`, the other is the
        // hi-limb sum `Add(_, _)`.
        let (carry, hi_sum) = match (is_carry(s1, lo, x_lo, y_lo), is_carry(s2, lo, x_lo, y_lo)) {
            (true, false) => (true, s2),
            (false, true) => (true, s1),
            _ => return None,
        };
        if !carry {
            return None;
        }
        let StackVal::BinOp(p_hi, BinOper::Add, q_hi) = &**hi_sum else {
            return None;
        };
        // Pair each low limb with its matching high limb (addition is commutative,
        // so try both pairings and accept the one where both operands reconstruct).
        for (xh, yh) in [(p_hi, q_hi), (q_hi, p_hi)] {
            if let (Some((a, a_clean)), Some((b, b_clean))) = (
                reconstruct_i128_operand(x_lo, xh),
                reconstruct_i128_operand(y_lo, yh),
            ) && a_clean
                && b_clean
            {
                return Some((
                    StackVal::BinOp(Box::new(a), BinOper::Add, Box::new(b)),
                    true,
                ));
            }
        }
        return None;
    }
    None
}

/// True if `e` computes the unsigned comparison `x <u y`. The compiler emits this
/// borrow/carry bit either way around — `x <u y` directly or its mirror `y >u x` —
/// so accept both spellings.
fn is_unsigned_lt(e: &StackVal, x: &StackVal, y: &StackVal) -> bool {
    match e {
        StackVal::Compare(l, CmpOp::LtU, r) => **l == *x && **r == *y,
        StackVal::Compare(l, CmpOp::GtU, r) => **l == *y && **r == *x,
        _ => false,
    }
}

/// True if `e` is the add carry bit `sum_lo <u addend_lo` — the comparison of the
/// freshly-computed low sum against one of the two addends' low limbs.
fn is_carry(e: &StackVal, sum_lo: &StackVal, x_lo: &StackVal, y_lo: &StackVal) -> bool {
    is_unsigned_lt(e, sum_lo, x_lo) || is_unsigned_lt(e, sum_lo, y_lo)
}

/// True for a `StackVal` that already represents a complete 128-bit value (not a
/// single limb): a host-call result, a parameter, or a named let binding. Used to
/// recover operands the SDK passed whole rather than as a fresh `(lo, hi)` split.
fn is_whole_i128_value(sv: &StackVal) -> bool {
    matches!(
        sv,
        StackVal::HostCallResult(_) | StackVal::Param(_) | StackVal::LetBinding(_)
    )
}

/// True when `sv` is a clean high limb `I128Limb { hi: true, .. }` — the only shape
/// that should pair with a clean low limb. Anything else is a degraded high word.
fn is_clean_hi_limb(sv: &StackVal) -> bool {
    matches!(sv, StackVal::I128Limb { hi: true, .. })
}

/// Type a cross-contract-call operand of i128 arithmetic as `i128`. Cross-contract
/// calls default to `soroban_sdk::Val` when their return type is unknown; when the
/// result feeds an i128 multiply/divide it must be `i128` so the arithmetic type-
/// checks (`balance.into_val()` / `balance * shares`). Other operand shapes
/// (storage gets, params) infer `i128` from the surrounding arithmetic.
fn force_i128_type(expr: SorobanExpr) -> SorobanExpr {
    match expr {
        SorobanExpr::InvokeContract {
            address,
            function,
            args,
            return_type: None,
        } => SorobanExpr::InvokeContract {
            address,
            function,
            args,
            return_type: Some("i128".to_string()),
        },
        SorobanExpr::TryInvokeContract {
            address,
            function,
            args,
            return_type: None,
        } => SorobanExpr::TryInvokeContract {
            address,
            function,
            args,
            return_type: Some("i128".to_string()),
        },
        other => other,
    }
}

/// Detect a sign-check-and-panic function like `check_nonnegative_amount`.
/// Pattern: `block { local.get N; i64.const 0; i64.lt_s; br_if 0; return; end }; call <panic>; unreachable`.
/// Returns the local index that is compared (typically the hi word of an i128).
fn detect_sign_check_function(module: &WasmModule, func_idx: u32) -> Option<u32> {
    use crate::wasm::ir::WasmInstr;
    let func = module.get_function(func_idx)?;
    let instrs: Vec<_> = func
        .body
        .iter()
        .filter(|i| !matches!(i, WasmInstr::End))
        .collect();
    // Expected: Block, LocalGet(N), I64Const(0), I64LtS, BrIf(0), Return, Call(panic), Unreachable
    if instrs.len() != 8 {
        return None;
    }
    if !matches!(instrs[0], WasmInstr::Block { .. }) {
        return None;
    }
    let local_idx = match instrs[1] {
        WasmInstr::LocalGet(idx) => *idx,
        _ => return None,
    };
    if !matches!(instrs[2], WasmInstr::I64Const(0)) {
        return None;
    }
    if !matches!(instrs[3], WasmInstr::I64LtS) {
        return None;
    }
    if !matches!(instrs[4], WasmInstr::BrIf(0)) {
        return None;
    }
    if !matches!(instrs[5], WasmInstr::Return) {
        return None;
    }
    if let WasmInstr::Call(target) = instrs[6] {
        if !is_unreachable_only_function(module, *target) {
            return None;
        }
    } else {
        return None;
    }
    if !matches!(instrs[7], WasmInstr::Unreachable) {
        return None;
    }
    Some(local_idx)
}

/// Returns true if the function at `func_idx` consists solely of an `unreachable` instruction
/// (with an optional trailing `End` that the parser includes for function bodies).
/// These are generated by the compiler for `panic!()` wrappers in `no_std` Soroban contracts.
pub(crate) fn is_unreachable_only_function(module: &WasmModule, func_idx: u32) -> bool {
    use crate::wasm::ir::WasmInstr;
    if let Some(func) = module.get_function(func_idx) {
        // WASM function bodies include a trailing End instruction, so we filter it out.
        let real_instrs: Vec<_> = func
            .body
            .iter()
            .filter(|i| !matches!(i, WasmInstr::End))
            .collect();
        real_instrs.len() == 1 && matches!(real_instrs[0], WasmInstr::Unreachable)
    } else {
        false
    }
}

/// Returns true if the wrapper function at `func_idx` has a call to a bare
/// `unreachable` trap function at nesting depth 1 (inside the outermost SDK
/// dispatch block). This indicates the SDK compiled a `panic!()` at the end of
/// the original source — the body call completes, then the wrapper calls the trap.
///
/// Trap calls deeper than depth 1 are inside the function body (e.g., `panic!()`
/// inside an if-branch compiled via br_table) and should not trigger this flag.
fn wrapper_has_panic_call(module: &WasmModule, func_idx: u32) -> bool {
    use crate::wasm::ir::WasmInstr;
    if let Some(func) = module.get_function(func_idx) {
        let mut depth: usize = 0;
        let mut found_depth1_trap = false;
        for instr in &func.body {
            match instr {
                WasmInstr::Block { .. } | WasmInstr::Loop { .. } | WasmInstr::If { .. } => {
                    depth += 1;
                }
                WasmInstr::End => {
                    depth = depth.saturating_sub(1);
                }
                WasmInstr::Call(target)
                    if depth == 1 && is_unreachable_only_function(module, *target) =>
                {
                    found_depth1_trap = true;
                }
                _ => {}
            }
        }
        found_depth1_trap
    } else {
        false
    }
}

/// Information about a detected `vec_new_from_linear_memory` wrapper function.
struct VecNewWrapperInfo {
    /// For 1-param wrappers, the hardcoded count extracted from the body.
    /// For 2-param wrappers, this is None (count comes from caller args).
    hardcoded_count: Option<u32>,
}

/// Detect if a function is a thin wrapper around `vec_new_from_linear_memory`.
///
/// The SDK compiles tuple/vec construction through a small helper that only
/// Val-encodes its i32 parameters (shift+or) then calls the import. Two variants:
/// - 2-param `wrapper(vals_ptr, count)` — count from caller
/// - 1-param `wrapper(vals_ptr)` — count hardcoded inside as a Val-encoded U32
fn detect_vec_new_wrapper(module: &WasmModule, func_idx: u32) -> Option<VecNewWrapperInfo> {
    use crate::wasm::imports::HostModule;
    use crate::wasm::ir::WasmInstr;

    let func = module.get_function(func_idx)?;
    let func_type = module.get_func_type(func_idx)?;

    // Find the single Call instruction and verify it targets vec_new_from_linear_memory
    let mut call_target = None;
    for instr in &func.body {
        if let WasmInstr::Call(target) = instr {
            if call_target.is_some() {
                return None; // More than one call — not a simple wrapper
            }
            call_target = Some(*target);
        }
    }
    let call_target = call_target?;

    let host_fn = module.imports.get_by_index(call_target)?;
    if host_fn.module != HostModule::Vec || host_fn.name != "vec_new_from_linear_memory" {
        return None;
    }

    // Verify all instructions are benign Val-encoding ops
    for instr in &func.body {
        match instr {
            WasmInstr::Call(_)
            | WasmInstr::End
            | WasmInstr::LocalGet(_)
            | WasmInstr::I64ExtendI32U
            | WasmInstr::I64Const(_)
            | WasmInstr::I64Shl
            | WasmInstr::I64Or => {}
            _ => return None,
        }
    }

    // For 1-param wrappers, extract the hardcoded count from the Val-encoded constant
    let hardcoded_count = if func_type.params.len() == 1 {
        func.body.iter().find_map(|instr| {
            if let WasmInstr::I64Const(v) = instr {
                let val = *v as u64;
                // Val-encoded U32: low byte is TAG_U32 (0x04), value in upper 32 bits.
                // Skip the encoding constants 4 and 32 used for shift+or.
                if val != 4 && val != 32 && (val & 0xff) == TAG_U32 {
                    Some((val >> 32) as u32)
                } else {
                    None
                }
            } else {
                None
            }
        })
    } else {
        None
    };

    cov_mark::hit!(detect_vec_new_wrapper_hit);
    Some(VecNewWrapperInfo { hardcoded_count })
}

/// Detect if a function is a thin wrapper around `vec_unpack_to_linear_memory`.
///
/// Same structure as `detect_vec_new_wrapper`: Val-encodes i32 parameters then calls
/// the import, drops the result. Returns the hardcoded count for 2-param wrappers,
/// or None for 3-param wrappers (count comes from caller).
fn detect_vec_unpack_wrapper(module: &WasmModule, func_idx: u32) -> Option<VecNewWrapperInfo> {
    use crate::wasm::imports::HostModule;
    use crate::wasm::ir::WasmInstr;

    let func = module.get_function(func_idx)?;
    let func_type = module.get_func_type(func_idx)?;

    // Find the single Call instruction and verify it targets vec_unpack_to_linear_memory
    let mut call_target = None;
    for instr in &func.body {
        if let WasmInstr::Call(target) = instr {
            if call_target.is_some() {
                return None;
            }
            call_target = Some(*target);
        }
    }
    let call_target = call_target?;

    let host_fn = module.imports.get_by_index(call_target)?;
    if host_fn.module != HostModule::Vec || host_fn.name != "vec_unpack_to_linear_memory" {
        return None;
    }

    // Verify all instructions are benign Val-encoding ops + drop (result is Void)
    for instr in &func.body {
        match instr {
            WasmInstr::Call(_)
            | WasmInstr::End
            | WasmInstr::LocalGet(_)
            | WasmInstr::I64ExtendI32U
            | WasmInstr::I64Const(_)
            | WasmInstr::I64Shl
            | WasmInstr::I64Or
            | WasmInstr::Drop => {}
            _ => return None,
        }
    }

    // For 2-param wrappers (vec, addr), the count is hardcoded as a Val-encoded U32
    let hardcoded_count = if func_type.params.len() <= 2 {
        func.body.iter().find_map(|instr| {
            if let WasmInstr::I64Const(v) = instr {
                let val = *v as u64;
                if val != 4 && val != 32 && (val & 0xff) == TAG_U32 {
                    Some((val >> 32) as u32)
                } else {
                    None
                }
            } else {
                None
            }
        })
    } else {
        None
    };

    cov_mark::hit!(detect_vec_unpack_wrapper_hit);
    Some(VecNewWrapperInfo { hardcoded_count })
}

/// Info returned by `detect_load_struct_wrapper`.
struct LoadStructWrapperInfo {
    /// Maps output_ptr offset (in bytes) to field name.
    /// Extracted by tracing stores in the function body back to map_unpack field order.
    offset_to_field: Vec<(i32, String)>,
    #[allow(dead_code)]
    type_name: Option<String>,
    storage_type: Option<StorageType>,
    /// The storage key the wrapper reads, when its body proves exactly ONE
    /// constant key (a descriptor-pointer DataKey constructor call or an
    /// immediate `I64Const` key Val). `None` when zero or several candidates —
    /// the synthesized field accesses then keep the honest `todo!()` key.
    const_key: Option<SorobanExpr>,
}

/// True when `f` is a storage-read probe a key Val can flow into as
/// `(key, storage_type)`: the `has_contract_data` / `get_contract_data`
/// import itself, or a thin internal wrapper with the `(i64, i64)` key +
/// storage-type signature (≤1 result — `has` wrappers return an i32 bool,
/// `get` wrappers the i64 Val) that reaches one of them within 2 calls.
fn is_storage_probe(module: &WasmModule, f: u32) -> bool {
    use crate::wasm::ir::WasmType;
    if let Some(hf) = module.imports.get_by_index(f) {
        return hf.module == HostModule::Ledger
            && matches!(hf.name.as_str(), "get_contract_data" | "has_contract_data");
    }
    let Some(ft) = module.get_func_type(f) else {
        return false;
    };
    if ft.params.as_slice() != [WasmType::I64, WasmType::I64] || ft.results.len() > 1 {
        return false;
    }
    func_reaches_host(module, f, HostModule::Ledger, "get_contract_data", 0)
        || func_reaches_host(module, f, HostModule::Ledger, "has_contract_data", 0)
}

/// Convert a [`DkEval`] result into a fully-CONSTANT storage-key expression:
/// a `Symbol` Val, or a `Vec` of symbols headed by one (the SDK's unit-variant
/// `Vec[Symbol]` wrapping). Unlike `dk_result_to_key_expr` there are no caller
/// payloads to embed — any non-symbol element means the key has a runtime
/// component and is NOT a constant key.
fn dk_result_to_const_key(result: &DkVal) -> Option<SorobanExpr> {
    let sym_of = |v: &DkVal| -> Option<String> {
        match v {
            DkVal::I64(raw) => crate::wasm::data::DataSection::decode_symbol_val(*raw as u64),
            DkVal::SymObj(name) => Some(name.clone()),
            _ => None,
        }
    };
    match result {
        DkVal::I64(_) | DkVal::SymObj(_) => Some(SorobanExpr::SymbolLiteral(sym_of(result)?)),
        DkVal::VecVal(elems) => {
            let mut out = Vec::with_capacity(elems.len());
            for e in elems {
                out.push(SorobanExpr::SymbolLiteral(sym_of(e)?));
            }
            if out.is_empty() {
                return None;
            }
            Some(SorobanExpr::VecConstruct(out))
        }
        _ => None,
    }
}

/// Recover the single constant storage key a load-struct wrapper's body reads,
/// if provable (issue #34 tranche 3). Two bytecode idioms:
///
/// 1. `[I32Const(x), Call(ctor)]` where `ctor: (i32) -> i64` reaches the
///    symbol encoder — a DataKey constructor taking either an immediate
///    variant selector or a static descriptor pointer. Resolved by
///    micro-executing the constructor's real bytecode ([`DkEval`]) with the
///    constant argument; static-data loads read the real data section.
/// 2. `I64Const` key Val two instructions before a `get_contract_data` /
///    `has_contract_data` import call (the `key; storage_type; call` window,
///    same as [`fallible_get_const_key`]).
///
/// All candidates across the body must agree on ONE key (structurally equal);
/// zero or conflicting candidates → `None` → today's `todo!()` key.
fn load_struct_const_key(
    module: &WasmModule,
    registry: &TypeRegistry,
    func: &crate::wasm::ir::WasmFunction,
) -> Option<SorobanExpr> {
    use crate::wasm::ir::{WasmInstr, WasmType};
    let mut found: Option<SorobanExpr> = None;
    let mut put = |k: SorobanExpr| -> bool {
        match &found {
            Some(prev) if *prev != k => false, // conflict → ambiguous
            _ => {
                found = Some(k);
                true
            }
        }
    };
    // The ctor's RESULT must provably be a storage key: the instructions
    // right after the ctor call must consume it as `(key, storage_type)` of
    // a has/get — `(local.tee k)? ; i64.const <st> ; call <storage-probe>`.
    // A constant symbol built for anything else (an event topic, an error
    // string) never matches this window and produces no candidate
    // (greptile P1 on PR #43).
    let ctor_result_feeds_storage = |call_pos: usize| -> bool {
        let mut j = call_pos + 1;
        if matches!(func.body.get(j), Some(WasmInstr::LocalTee(_))) {
            j += 1;
        }
        matches!(func.body.get(j), Some(WasmInstr::I64Const(_)))
            && matches!(func.body.get(j + 1), Some(WasmInstr::Call(f)) if is_storage_probe(module, *f))
    };
    for (i, w) in func.body.windows(2).enumerate() {
        let key = match w {
            [WasmInstr::I32Const(x), WasmInstr::Call(t)]
                if module.imports.get_by_index(*t).is_none()
                    && module.get_func_type(*t).is_some_and(|ft| {
                        ft.params.as_slice() == [WasmType::I32]
                            && ft.results.as_slice() == [WasmType::I64]
                    })
                    && func_reaches_symbol_encoder(module, *t, 0)
                    && ctor_result_feeds_storage(i + 1) =>
            {
                // When the ctor's argument is a pointer into a data-segment
                // GAP, the eval can only proceed if the gap is the PROVEN
                // linker-elided all-zero descriptor row: bounded by the next
                // real segment, materialized module-wide only as this ctor's
                // argument ([`gap_row_proven_zero`]). The eval then runs the
                // ctor's REAL bytecode over zero bytes — no descriptor-shape
                // assumption — and DkEval's stores refusing absolute
                // addresses proves the row is never written.
                let gap_zero = (*x > 1024
                    && module
                        .data_sections
                        .read_bytes_zero_extended(*x as u32, 1)
                        .is_none())
                .then(|| {
                    let next_seg = module
                        .data_sections
                        .segments
                        .iter()
                        .map(|s| s.offset)
                        .filter(|o| *o > *x as u32)
                        .min()
                        .unwrap_or(u32::MAX);
                    let end = next_seg.min((*x as u32).saturating_add(32));
                    (end > *x as u32 && gap_row_proven_zero(module, *t, *x as u32, end))
                        .then_some((*x as u32, end))
                })
                .flatten();
                let mut ev = DkEval {
                    module,
                    mem: HashMap::new(),
                    sp: DkVal::StackPtr(0),
                    steps: 0,
                    gap_zero,
                };
                match ev.eval_call(*t, vec![DkVal::I32(*x)], 0) {
                    Some(Some(result)) => dk_result_to_const_key(&result),
                    // The static descriptor-pointer fallback applies ONLY
                    // when the evaluator refused because the dispatcher is
                    // too large (aqua's 13-arm ctor is ~6k instructions) —
                    // for THAT shape, `x` is by construction a descriptor
                    // pointer. Any other eval failure (unsupported
                    // instruction, depth, control flow) proves nothing about
                    // `x`, and reading a byte through it could fabricate a
                    // variant from unrelated data (greptile P1 on PR #44).
                    _ if module
                        .get_function(*t)
                        .is_some_and(|f| f.body.len() > DK_MAX_BODY) =>
                    {
                        descriptor_key_from_ptr(module, *t, *x)
                    }
                    _ => None,
                }
            }
            [_, WasmInstr::Call(t)] => module
                .imports
                .get_by_index(*t)
                .filter(|hf| {
                    hf.module == HostModule::Ledger
                        && matches!(hf.name.as_str(), "get_contract_data" | "has_contract_data")
                })
                .and_then(|_| match func.body.get(i.checked_sub(1)?) {
                    Some(WasmInstr::I64Const(raw)) => {
                        let k = try_decode_val(*raw, registry);
                        (!matches!(k, SorobanExpr::UnknownVal | SorobanExpr::Void)).then_some(k)
                    }
                    _ => None,
                }),
            _ => None,
        };
        if let Some(k) = key
            && !put(k)
        {
            return None;
        }
    }
    found
}

/// Detect if a function is a "load struct" wrapper that reads a struct from
/// contract storage and unpacks its fields to linear memory.
///
/// This pattern (e.g., `load_offer` in single_offer) takes a single i32
/// output pointer, internally calls `get_contract_data` +
/// `map_unpack_to_linear_memory`, and writes the unpacked field values to
/// the output pointer. Inlining this function fails because BrIf child
/// context locals are discarded (lesson #35), losing the field values.
/// Instead, we detect the wrapper and synthesize FrameSlot entries directly.
///
/// The function body's output layout is compiler-dependent (Rust struct layout
/// reorders fields for alignment and uses native sizes). We trace the actual
/// I64Store/I64Store32 instructions to map output offsets to field names.
///
/// Expected signature: `(i32 output_ptr) -> void`
fn detect_load_struct_wrapper(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<LoadStructWrapperInfo> {
    use crate::wasm::imports::HostModule;
    use crate::wasm::ir::{WasmInstr, WasmType};

    let func = module.get_function(func_idx)?;
    let func_type = module.get_func_type(func_idx)?;

    // Must have exactly 1 param of type I32 and no results (void return).
    if func_type.params.len() != 1 || func_type.params[0] != WasmType::I32 {
        return None;
    }
    if !func_type.results.is_empty() {
        return None;
    }

    // Body must be reasonably sized (not a giant function).
    if func.body.len() > 200 {
        return None;
    }

    // Scan for required host calls: get_contract_data + map_unpack_to_linear_memory.
    // The has_contract_data check is often done through an internal helper, so we
    // don't require it directly.
    let mut has_get_contract_data = false;
    let mut has_map_unpack = false;

    for instr in &func.body {
        if let WasmInstr::Call(target) = instr {
            if let Some(host_fn) = module.imports.get_by_index(*target) {
                match (host_fn.module, host_fn.name.as_str()) {
                    (HostModule::Ledger, "get_contract_data") => {
                        has_get_contract_data = true;
                    }
                    (HostModule::Map, "map_unpack_to_linear_memory") => {
                        has_map_unpack = true;
                    }
                    _ => {}
                }
            } else if detect_map_unpack_thunk(module, *target) {
                has_map_unpack = true;
            }
        }
    }

    if !has_get_contract_data || !has_map_unpack {
        return None;
    }

    // Extract field names from the data section.
    let mut data_section_ptrs: Vec<u32> = Vec::new();
    let mut val_encoded_u32s: Vec<u32> = Vec::new();

    for instr in &func.body {
        match instr {
            WasmInstr::I32Const(v) if *v > 1024 => {
                data_section_ptrs.push(*v as u32);
            }
            WasmInstr::I64Const(v) => {
                let val = *v as u64;
                if (val & 0xff) == TAG_U32 && val > 0xff {
                    val_encoded_u32s.push((val >> 32) as u32);
                }
            }
            _ => {}
        }
    }

    let mut map_unpack_count: Option<u32> = None;
    if let Some(&last) = val_encoded_u32s.last() {
        map_unpack_count = Some(last);
    }

    let all_candidate_ptrs: Vec<u32> = data_section_ptrs
        .iter()
        .chain(
            val_encoded_u32s
                .iter()
                .take(val_encoded_u32s.len().saturating_sub(1)),
        )
        .copied()
        .collect();

    let mut found_keys_ptr: Option<u32> = None;
    let mut found_count: Option<u32> = None;

    for &ptr in &all_candidate_ptrs {
        let try_counts: Vec<u32> = if let Some(c) = map_unpack_count {
            vec![c]
        } else {
            (1..=16).collect()
        };
        for count in try_counts {
            if let Some(names) = module.data_sections.read_string_slice_array(ptr, count) {
                if names.len() == count as usize
                    && find_type_by_field_names(registry, &names, None).is_some()
                {
                    found_keys_ptr = Some(ptr);
                    found_count = Some(count);
                    break;
                }
            } else {
                break;
            }
        }
        if found_keys_ptr.is_some() {
            break;
        }
    }

    let keys_ptr = found_keys_ptr?;
    let count = found_count?;

    let field_names = module
        .data_sections
        .read_string_slice_array(keys_ptr, count)?;
    if field_names.len() != count as usize {
        return None;
    }

    let type_name = find_type_by_field_names(registry, &field_names, None);
    type_name.as_ref()?;

    // Trace the output layout by analyzing stores to the output pointer (local 0).
    //
    // The function unpacks map fields into temporary frame memory, validates each,
    // then stores the decoded values to the output pointer. The output layout is
    // determined by the Rust struct layout, NOT by the map key order.
    //
    // Strategy:
    // 1. Find which locals loaded from which unpack buffer offsets (I64Load from
    //    the frame base + offset → local via LocalTee/LocalSet)
    // 2. Find which offsets in the output pointer each local is stored to (I64Store
    //    or I64Store32 preceded by LocalGet(0))
    // 3. Map output offset → unpack offset → field name
    let offset_to_field = trace_output_field_mapping(func, &field_names, count);

    // Require at least one successfully mapped field.
    if offset_to_field.is_empty() {
        return None;
    }

    let storage_type = detect_storage_type_in_body(module, &func.body);
    let const_key = load_struct_const_key(module, registry, func);

    cov_mark::hit!(detect_load_struct_wrapper_hit);
    Some(LoadStructWrapperInfo {
        offset_to_field,
        type_name,
        storage_type,
        const_key,
    })
}

/// Trace the output offset → field name mapping for a load-struct wrapper.
///
/// After `map_unpack_to_linear_memory`, the function loads each Val-encoded field
/// from the unpack buffer (frame base + 8, +16, +24, ...) into locals, validates
/// their type tags, then stores decoded values to the output pointer at
/// compiler-determined offsets.
///
/// Returns a vec of (output_offset, field_name) pairs.
fn trace_output_field_mapping(
    func: &crate::wasm::ir::WasmFunction,
    field_names: &[String],
    count: u32,
) -> Vec<(i32, String)> {
    use crate::wasm::ir::WasmInstr;

    // Step 1: Find the frame base local. Pattern: GlobalGet(0) - I32Const(N) → LocalTee(base)
    // The frame base is typically local 1.
    let mut frame_base_local: Option<u32> = None;
    for window in func.body.windows(4) {
        if let [
            WasmInstr::GlobalGet(0),
            WasmInstr::I32Const(_),
            WasmInstr::I32Sub,
            WasmInstr::LocalTee(local),
        ] = window
        {
            frame_base_local = Some(*local);
            break;
        }
    }
    let frame_base_local = match frame_base_local {
        Some(l) => l,
        None => return Vec::new(),
    };

    // Step 2: Track which locals get which unpack buffer values.
    // Pattern: LocalGet(frame_base) / I64Load(offset) / LocalTee(target_local)
    // The unpack buffer starts at frame_base + 8 (first 8 bytes may be used for
    // the map Val itself). Fields at offsets 8, 16, 24, ...
    // Field index = (load_offset - 8) / 8
    let mut local_to_field_idx: HashMap<u32, usize> = HashMap::new();

    for window in func.body.windows(3) {
        if let [
            WasmInstr::LocalGet(base),
            WasmInstr::I64Load(load_offset),
            WasmInstr::LocalTee(target),
        ] = window
            && *base == frame_base_local
            && *load_offset >= 8
        {
            let field_idx = ((*load_offset - 8) / 8) as usize;
            if field_idx < count as usize {
                local_to_field_idx.insert(*target, field_idx);
            }
        }
    }

    // Step 3: Track stores to the output pointer (local 0).
    // Patterns:
    //   LocalGet(0) / LocalGet(src) / I64Store(offset) → i64 field at offset
    //   LocalGet(0) / LocalGet(src) / I64Const(32) / I64ShrU / I64Store32(offset)
    //       → u32 field (Val-encoded u32 shifted right by 32) at offset
    let mut result: Vec<(i32, String)> = Vec::new();

    for window in func.body.windows(3) {
        if let [
            WasmInstr::LocalGet(0),
            WasmInstr::LocalGet(src),
            WasmInstr::I64Store(store_offset),
        ] = window
            && let Some(&field_idx) = local_to_field_idx.get(src)
            && let Some(name) = field_names.get(field_idx)
        {
            result.push((*store_offset as i32, name.clone()));
        }
    }

    // Also check for u32 fields stored via I64ShrU + I64Store32.
    for window in func.body.windows(5) {
        if let [
            WasmInstr::LocalGet(0),
            WasmInstr::LocalGet(src),
            WasmInstr::I64Const(32),
            WasmInstr::I64ShrU,
            WasmInstr::I64Store32(store_offset),
        ] = window
            && let Some(&field_idx) = local_to_field_idx.get(src)
            && let Some(name) = field_names.get(field_idx)
        {
            result.push((*store_offset as i32, name.clone()));
        }
    }

    result
}

/// Info returned by `detect_map_unpack_decode_wrapper`.
struct MapUnpackDecodeInfo {
    field_names: Vec<String>,
    /// Struct type name from registry (e.g., "AllowanceValue")
    type_name: Option<String>,
    /// Storage type detected from wrapper body (for multi-param wrappers)
    storage_type: Option<StorageType>,
}

/// Detect if a function is a "struct unpack + decode" wrapper that contains a call
/// to `map_unpack_to_linear_memory` plus Val-decode calls for each field.
///
/// This pattern (e.g., func 27 in contracttrait_impl_partial) unpacks a struct's
/// Val-encoded fields into frame memory, decodes each field from Val to native type,
/// and stores the decoded values to a result pointer. Inlining this function fails
/// because the decode step has branches that corrupt locals through sequential execution.
/// Instead, we detect it as a unit and synthesize FieldAccess expressions at the result positions.
///
/// Expected signature: `(i32 result_ptr, i64 map_val) -> void`
fn detect_map_unpack_decode_wrapper(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<MapUnpackDecodeInfo> {
    use crate::wasm::imports::HostModule;
    use crate::wasm::ir::WasmInstr;

    let func = module.get_function(func_idx)?;
    let func_type = module.get_func_type(func_idx)?;

    // Must have at least 2 params. The classic pattern is (i32 result_ptr, i64 map_val).
    // Multi-param variants like (i32, i64, i64) also exist when the wrapper internally
    // constructs the storage key from extra args. 1-param functions should fall through
    // to normal inlining where handle_map_unpack_raw can resolve fields correctly.
    if func_type.params.len() < 2 {
        return None;
    }

    // A helper that checks `has_contract_data` is a *fallible* storage getter
    // (`if has { get + unpack + extend_ttl } else { default }`), not a decode
    // wrapper: claiming it here replaces the whole protocol with bare field
    // accesses, silently dropping the missing-key default branch and the TTL
    // bump (blend-backstop `user_balance`). Let it inline generically so that
    // control flow survives.
    if func
        .body
        .iter()
        .any(|ins| matches!(ins, WasmInstr::Call(t) if func_reaches_host(module, *t, HostModule::Ledger, "has_contract_data", 0)))
    {
        cov_mark::hit!(map_unpack_decode_skips_fallible_getter);
        return None;
    }

    // Find a Call to map_unpack_to_linear_memory — either directly (host import) or
    // indirectly through a thunk (detected by detect_map_unpack_thunk).
    let mut has_map_unpack = false;
    let mut map_unpack_keys_ptr: Option<u32> = None;
    let mut map_unpack_count: Option<u32> = None;

    // Scan for Call to map_unpack_to_linear_memory (direct or via thunk)
    for instr in &func.body {
        if let WasmInstr::Call(target) = instr {
            if let Some(host_fn) = module.imports.get_by_index(*target) {
                if host_fn.module == HostModule::Map
                    && host_fn.name == "map_unpack_to_linear_memory"
                {
                    has_map_unpack = true;
                }
            } else {
                // Check for indirect call through a map_unpack thunk
                if detect_map_unpack_thunk(module, *target) {
                    has_map_unpack = true;
                }
            }
        }
    }

    if !has_map_unpack {
        return None;
    }

    // Extract keys_ptr and count for the map_unpack_to_linear_memory call.
    // keys_ptr can be:
    //   - An I32Const (pointing to data section) that gets Val-encoded at runtime via
    //     i64.extend_i32_u + i64.shl 32 + i64.or 4
    //   - A pre-folded I64Const with tag 0x04 (TAG_U32)
    // count is typically a pre-folded I64Const with tag 0x04 (TAG_U32).
    //
    // Strategy: collect I32Const values > 1024 (data section pointers) and
    // Val-encoded I64Const values. The I32Const is keys_ptr, the I64Const count is count.
    let mut data_section_ptrs: Vec<u32> = Vec::new();
    let mut val_encoded_u32s: Vec<u32> = Vec::new();

    for instr in &func.body {
        match instr {
            WasmInstr::I32Const(v)
                // Data section pointers are typically > 1024
                if *v > 1024 => {
                    data_section_ptrs.push(*v as u32);
                }
            WasmInstr::I64Const(v) => {
                let val = *v as u64;
                // Val-encoded u32: (value << 32) | 4, skip bare tag (4) and small values
                if (val & 0xff) == TAG_U32 && val > 0xff {
                    val_encoded_u32s.push((val >> 32) as u32);
                }
            }
            _ => {}
        }
    }

    // count: last Val-encoded u32 (count comes after keys_ptr and vals_ptr in call args)
    if let Some(&last) = val_encoded_u32s.last() {
        map_unpack_count = Some(last);
    }

    // Try each candidate pointer and validate field names against the registry.
    // The function body may contain multiple I32Const > 1024 (e.g., event field names
    // AND struct field names). We need the one whose fields match a known struct type.
    // Also try Val-encoded I64 pointers as fallback.
    let all_candidate_ptrs: Vec<u32> = data_section_ptrs
        .iter()
        .chain(
            val_encoded_u32s
                .iter()
                .take(val_encoded_u32s.len().saturating_sub(1)),
        )
        .copied()
        .collect();

    for &ptr in &all_candidate_ptrs {
        let try_counts: Vec<u32> = if let Some(c) = map_unpack_count {
            vec![c]
        } else {
            (1..=16).collect()
        };
        for count in try_counts {
            if let Some(names) = module.data_sections.read_string_slice_array(ptr, count) {
                if names.len() == count as usize
                    && find_type_by_field_names(registry, &names, None).is_some()
                {
                    map_unpack_keys_ptr = Some(ptr);
                    map_unpack_count = Some(count);
                    break;
                }
            } else {
                break; // Read failed for this ptr — no point trying larger counts
            }
        }
        if map_unpack_keys_ptr.is_some() {
            break;
        }
    }

    let keys_ptr = map_unpack_keys_ptr?;
    let count = map_unpack_count?;

    // Read field names from the data section
    let field_names = module
        .data_sections
        .read_string_slice_array(keys_ptr, count)?;
    if field_names.len() != count as usize {
        return None;
    }

    // Only match struct types, NOT union types (which also use map_unpack
    // but for enum variant discrimination, handled by the normal match recovery path).
    let type_name = find_type_by_field_names(registry, &field_names, None);
    type_name.as_ref()?;

    // For multi-param wrappers, detect the storage type by scanning for
    // direct calls to storage host imports (get_contract_data, has_contract_data).
    // The storage type is the last i64 argument before the call (0=Temp, 1=Persist, 2=Instance).
    let storage_type = if func_type.params.len() > 2 {
        detect_storage_type_in_body(module, &func.body)
    } else {
        None
    };

    cov_mark::hit!(detect_map_unpack_decode_wrapper_hit);
    Some(MapUnpackDecodeInfo {
        field_names,
        type_name,
        storage_type,
    })
}

/// Info returned by `detect_struct_construct_wrapper`.
struct StructConstructWrapperInfo {
    field_names: Vec<String>,
    type_name: String,
}

/// Detect if a function is a "struct construct" wrapper that encodes native values
/// and calls `map_new_from_linear_memory` to construct a struct/map.
///
/// This pattern (e.g., func 29 in contracttrait_impl_partial) takes a result_ptr
/// plus native field values (i64), encodes each to a Val, then calls
/// `map_new_from_linear_memory`. Inlining fails because the encoder has branches
/// that corrupt values through sequential execution. Instead, we detect the wrapper
/// and directly build a StructConstruct from the caller's args.
///
/// Expected signature: `(i32 result_ptr, i64 val1, i64 val2, ...) -> void`
fn detect_struct_construct_wrapper(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
    prefer: Option<&str>,
) -> Option<StructConstructWrapperInfo> {
    use crate::wasm::imports::HostModule;
    use crate::wasm::ir::{WasmInstr, WasmType};

    let func = module.get_function(func_idx)?;
    let func_type = module.get_func_type(func_idx)?;

    // Must take at least 2 params: (i32 result_ptr, i64 val1, ...)
    if func_type.params.len() < 2 {
        return None;
    }

    // First param must be i32 (result pointer)
    if func_type.params[0] != WasmType::I32 {
        return None;
    }

    // Find a Call to map_new_from_linear_memory
    let mut has_map_new = false;
    for instr in &func.body {
        if let WasmInstr::Call(target) = instr
            && let Some(host_fn) = module.imports.get_by_index(*target)
            && host_fn.module == HostModule::Map
            && host_fn.name == "map_new_from_linear_memory"
        {
            has_map_new = true;
        }
    }

    if !has_map_new {
        return None;
    }

    // Extract keys_ptr and count (same approach as detect_map_unpack_decode_wrapper)
    let mut keys_ptr_val: Option<u32> = None;
    let mut count_val: Option<u32> = None;

    let mut data_section_ptrs: Vec<u32> = Vec::new();
    let mut val_encoded_u32s: Vec<u32> = Vec::new();

    for instr in &func.body {
        match instr {
            WasmInstr::I32Const(v) if *v > 1024 => {
                data_section_ptrs.push(*v as u32);
            }
            WasmInstr::I64Const(v) => {
                let val = *v as u64;
                if (val & 0xff) == TAG_U32 && val > 0xff {
                    val_encoded_u32s.push((val >> 32) as u32);
                }
            }
            _ => {}
        }
    }

    if !data_section_ptrs.is_empty() {
        keys_ptr_val = Some(data_section_ptrs[0]);
    } else if val_encoded_u32s.len() >= 2 {
        keys_ptr_val = Some(val_encoded_u32s[0]);
    }

    if let Some(&last) = val_encoded_u32s.last() {
        count_val = Some(last);
    }

    let keys_ptr = keys_ptr_val?;
    let count = count_val?;

    // Verify count matches the number of i64 params (excluding the i32 result_ptr)
    let num_val_params = func_type.params.len() - 1;
    if count as usize != num_val_params {
        return None;
    }

    let field_names = module
        .data_sections
        .read_string_slice_array(keys_ptr, count)?;
    if field_names.len() != count as usize {
        return None;
    }

    // Must match a known struct type — skip for unions (enum variant construction
    // uses the same map_new_from_linear_memory but should go through the normal path).
    let type_name = find_type_by_field_names(registry, &field_names, prefer)?;

    cov_mark::hit!(detect_struct_construct_wrapper_hit);
    Some(StructConstructWrapperInfo {
        field_names,
        type_name,
    })
}

/// Detect a "generic map_new thunk" pattern:
/// `(i32 keys_ptr, i32 count, i32 vals_ptr, i32 count) -> i64`
///
/// This pattern (SDK v25+) is a thin wrapper that validates arg equality,
/// Val-encodes the three i32 args, and calls `map_new_from_linear_memory`.
/// Unlike `detect_struct_construct_wrapper` which takes typed i64 field values,
/// this wrapper takes raw i32 pointers — the field values are already stored
/// in memory at vals_ptr by the caller.
fn detect_map_new_thunk(module: &WasmModule, func_idx: u32) -> bool {
    use crate::wasm::imports::HostModule;
    use crate::wasm::ir::{WasmInstr, WasmType};

    let Some(func) = module.get_function(func_idx) else {
        return false;
    };
    let Some(func_type) = module.get_func_type(func_idx) else {
        return false;
    };

    // Must be (i32, i32, i32, i32) -> i64
    if func_type.params.len() != 4
        || !func_type.params.iter().all(|p| *p == WasmType::I32)
        || func_type.results.len() != 1
        || func_type.results[0] != WasmType::I64
    {
        return false;
    }

    // Must contain a Call to map_new_from_linear_memory and be short (< 40 instrs)
    if func.body.len() > 40 {
        return false;
    }

    let result = func.body.iter().any(|instr| {
        if let WasmInstr::Call(target) = instr
            && let Some(host_fn) = module.imports.get_by_index(*target)
        {
            return host_fn.module == HostModule::Map
                && host_fn.name == "map_new_from_linear_memory";
        }
        false
    });
    if result {
        cov_mark::hit!(detect_map_new_thunk_hit);
    }
    result
}

/// Detect if a function is a "map_unpack thunk" — a thin validation wrapper
/// around `map_unpack_to_linear_memory`.
///
/// SDK v25+ generates a thunk with signature `(i64 map, i32 keys_ptr, i32 vals_ptr,
/// i32 count, i32 count2) -> void` that validates `count == count2`, Val-encodes
/// the i32 args, and calls the host function. Intercepting this thunk at the call
/// site (before Val-encoding) lets us synthesize FieldAccess entries using the raw
/// i32 args, bypassing the problematic double-inlining path where Val-encoding of
/// FrameSlot addresses produces unresolvable BinOp expressions.
fn detect_map_unpack_thunk(module: &WasmModule, func_idx: u32) -> bool {
    use crate::wasm::imports::HostModule;
    use crate::wasm::ir::{WasmInstr, WasmType};

    let Some(func) = module.get_function(func_idx) else {
        return false;
    };
    let Some(func_type) = module.get_func_type(func_idx) else {
        return false;
    };

    // Signature: first param is i64 (map Val), rest are i32, no results (void)
    // Typical: (i64, i32, i32, i32, i32) -> void
    if func_type.params.len() < 4 || !func_type.results.is_empty() {
        return false;
    }
    if func_type.params[0] != WasmType::I64 {
        return false;
    }
    if !func_type.params[1..].iter().all(|p| *p == WasmType::I32) {
        return false;
    }

    // Short body (validation + Val-encoding + call)
    if func.body.len() > 60 {
        return false;
    }

    // Must contain a direct Call to map_unpack_to_linear_memory
    let result = func.body.iter().any(|instr| {
        if let WasmInstr::Call(target) = instr
            && let Some(host_fn) = module.imports.get_by_index(*target)
        {
            return host_fn.module == HostModule::Map
                && host_fn.name == "map_unpack_to_linear_memory";
        }
        false
    });
    if result {
        cov_mark::hit!(detect_map_unpack_thunk_hit);
    }
    result
}

/// Detect the storage type used by a function by scanning for direct calls
/// to storage host imports (get_contract_data, has_contract_data) and
/// extracting the storage type constant from the preceding I64Const.
fn detect_storage_type_in_body(
    module: &WasmModule,
    body: &[crate::wasm::ir::WasmInstr],
) -> Option<StorageType> {
    use crate::wasm::imports::HostModule;
    use crate::wasm::ir::WasmInstr;

    for (i, instr) in body.iter().enumerate() {
        if let WasmInstr::Call(target) = instr
            && let Some(host_fn) = module.imports.get_by_index(*target)
            && host_fn.module == HostModule::Ledger
            && (host_fn.name == "get_contract_data" || host_fn.name == "has_contract_data")
        {
            // Look backwards for the storage type I64Const (0/1/2)
            for j in (0..i).rev().take(10) {
                if let WasmInstr::I64Const(v) = &body[j] {
                    return match *v {
                        0 => Some(StorageType::Temporary),
                        1 => Some(StorageType::Persistent),
                        2 => Some(StorageType::Instance),
                        _ => continue,
                    };
                }
            }
        }
    }
    None
}

/// Find a struct/event type name by its field names.
fn find_type_by_field_names(
    registry: &TypeRegistry,
    field_names: &[String],
    prefer: Option<&str>,
) -> Option<String> {
    // Collect every struct whose field-name set matches.
    let mut matches: Vec<&String> = Vec::new();
    for (name, spec) in &registry.structs {
        let spec_fields: Vec<String> = spec
            .fields
            .iter()
            .filter_map(|f| f.name.to_utf8_string().ok())
            .collect();
        if spec_fields == *field_names {
            matches.push(name);
        }
    }
    // When the field-name set is ambiguous (e.g. `UdtRecursive` vs `RecursiveToEnum`,
    // both `{a, b}`), prefer the struct named like the caller's return/param UDT;
    // otherwise keep first-in-declared-order (prior behavior).
    if matches.len() > 1
        && let Some(p) = prefer
        && let Some(m) = matches.iter().find(|n| **n == p)
    {
        cov_mark::hit!(struct_disambiguated_by_return_type);
        return Some((*m).clone());
    }
    matches.first().map(|n| (*n).clone())
}

/// Info returned by `detect_balance_helper_wrapper`.
struct BalanceHelperInfo {
    /// `true` = receive_balance (add), `false` = spend_balance (subtract).
    is_receive: bool,
    /// Storage type (normally Persistent for balance storage).
    storage_type: StorageType,
    /// Union type name (e.g., "DataKey").
    union_name: String,
    /// Variant name (e.g., "Balance").
    variant_name: String,
}

/// Detect a `receive_balance` or `spend_balance` helper function.
///
/// These are the Soroban token SDK's balance update helpers that:
/// 1. Read the current balance from persistent storage (via sub-function)
/// 2. Add (receive) or subtract (spend) the amount
/// 3. Write the updated balance back (via sub-function)
///
/// Pattern: `(i64, i64, i64) -> void` where param 0 = address,
/// params 1-2 = amount (i128 split into lo/hi i64).
///
/// Detection criteria:
/// - 3 i64 params, void return
/// - Body < 100 instructions
/// - Call chain reaches both read (has/get_contract_data) and write (put_contract_data)
/// - Body contains i64.add (receive) or i64.sub (spend) instructions
/// - Registry contains a union with a "Balance" variant
fn detect_balance_helper_wrapper(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<BalanceHelperInfo> {
    use crate::wasm::ir::{WasmInstr, WasmType};

    let func = module.get_function(func_idx)?;
    let func_type = module.get_func_type(func_idx)?;

    // Must be (i64, i64, i64) -> void
    if func_type.params.len() != 3
        || !func_type.params.iter().all(|p| *p == WasmType::I64)
        || !func_type.results.is_empty()
    {
        return None;
    }

    // Body must be moderate size
    if func.body.len() > 100 {
        return None;
    }

    // Check for i64.add and/or i64.sub instructions in the body
    let mut has_add = false;
    let mut has_sub = false;
    let mut internal_calls: Vec<u32> = Vec::new();

    for instr in &func.body {
        match instr {
            WasmInstr::I64Add => has_add = true,
            WasmInstr::I64Sub => has_sub = true,
            WasmInstr::Call(target) if module.imports.get_by_index(*target).is_none() => {
                internal_calls.push(*target);
            }
            _ => {}
        }
    }

    // Must have arithmetic (at least one of add or sub)
    if !has_add && !has_sub {
        return None;
    }

    // The call chain must reach both read and write storage operations.
    // Check up to 2 levels deep (balance_helper -> read_balance -> host calls).
    let mut found_read = false;
    let mut found_write = false;

    for &callee in &internal_calls {
        if function_calls_host_in_chain(module, callee, HostModule::Ledger, "has_contract_data", 2)
            || function_calls_host_in_chain(
                module,
                callee,
                HostModule::Ledger,
                "get_contract_data",
                2,
            )
        {
            found_read = true;
        }
        if function_calls_host_in_chain(module, callee, HostModule::Ledger, "put_contract_data", 2)
        {
            found_write = true;
        }
    }

    if !found_read || !found_write {
        return None;
    }

    // Registry must have a union with a "Balance" variant
    let (union_name, has_data) = registry.find_union_variant("Balance")?;
    if !has_data {
        // Balance variant must carry data (the address)
        return None;
    }

    // Detect storage type from the call chain
    let storage_type = internal_calls
        .iter()
        .find_map(|&callee| detect_storage_type_in_chain(module, callee, 2))
        .unwrap_or(StorageType::Persistent);

    // Distinguish receive (add only or add dominant) vs spend (sub only or sub dominant)
    let is_receive = has_add && !has_sub;

    cov_mark::hit!(detect_balance_helper_wrapper_hit);
    Some(BalanceHelperInfo {
        is_receive,
        storage_type,
        union_name,
        variant_name: "Balance".to_string(),
    })
}

/// Info returned by `detect_spend_allowance_wrapper`.
struct SpendAllowanceInfo {
    /// Storage type (normally Temporary for allowance storage).
    storage_type: StorageType,
    /// Union type name (e.g., "DataKey").
    union_name: String,
    /// Variant name (e.g., "Allowance").
    variant_name: String,
    /// Key struct type name (e.g., "AllowanceDataKey").
    key_type_name: String,
    /// Key struct field names (e.g., ["from", "spender"]).
    key_field_names: Vec<String>,
    /// Value struct type name (e.g., "AllowanceValue").
    value_type_name: String,
    /// Value struct field names (e.g., ["amount", "expiration_ledger"]).
    value_field_names: Vec<String>,
}

/// Detect a `spend_allowance` helper function.
///
/// These are the Soroban token SDK's allowance spending helpers that:
/// 1. Read the current allowance from temporary storage (via sub-function)
/// 2. Check if allowance.amount >= amount (panic if insufficient)
/// 3. Write back the allowance with decremented amount (via sub-function)
///
/// Pattern: `(i64, i64, i64, i64) -> void` where params 0-1 = from/spender addresses,
/// params 2-3 = amount (i128 split into lo/hi i64).
///
/// Detection criteria:
/// - 4 i64 params, void return
/// - Body < 150 instructions
/// - Call chain reaches both read (has/get_contract_data) and write (put_contract_data)
/// - Body contains i64.sub AND comparison (I64LtS, I64GtS, etc.)
/// - Registry contains a union with an "Allowance" variant
/// - Value struct found by name heuristic (variant_name + "Value")
fn detect_spend_allowance_wrapper(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<SpendAllowanceInfo> {
    use crate::wasm::ir::{WasmInstr, WasmType};

    let func = module.get_function(func_idx)?;
    let func_type = module.get_func_type(func_idx)?;

    // Must be (i64, i64, i64, i64) -> void
    if func_type.params.len() != 4
        || !func_type.params.iter().all(|p| *p == WasmType::I64)
        || !func_type.results.is_empty()
    {
        return None;
    }

    // Body must be moderate size
    if func.body.len() > 150 {
        return None;
    }

    // Check for i64.sub AND comparison instructions in the body
    let mut has_sub = false;
    let mut has_compare = false;
    let mut internal_calls: Vec<u32> = Vec::new();

    for instr in &func.body {
        match instr {
            WasmInstr::I64Sub => has_sub = true,
            WasmInstr::I64LtS | WasmInstr::I64LtU | WasmInstr::I64GtS => {
                has_compare = true;
            }
            WasmInstr::Call(target) if module.imports.get_by_index(*target).is_none() => {
                internal_calls.push(*target);
            }
            _ => {}
        }
    }

    // Must have BOTH subtraction AND comparison (distinguishes from balance helper)
    if !has_sub || !has_compare {
        return None;
    }

    // The call chain must reach both read and write storage operations.
    // Check up to 3 levels deep (spend_allowance -> read_allowance -> host calls).
    let mut found_read = false;
    let mut found_write = false;

    for &callee in &internal_calls {
        if function_calls_host_in_chain(module, callee, HostModule::Ledger, "has_contract_data", 3)
            || function_calls_host_in_chain(
                module,
                callee,
                HostModule::Ledger,
                "get_contract_data",
                3,
            )
        {
            found_read = true;
        }
        if function_calls_host_in_chain(module, callee, HostModule::Ledger, "put_contract_data", 3)
        {
            found_write = true;
        }
    }

    if !found_read || !found_write {
        return None;
    }

    // Registry must have a union with an "Allowance" variant
    let (union_name, has_data) = registry.find_union_variant("Allowance")?;
    if !has_data {
        // Allowance variant must carry data (the AllowanceDataKey)
        return None;
    }

    // Get the key struct type from the variant's data type
    let key_type_def = registry.find_variant_data_type(&union_name, "Allowance")?;
    let key_type_name = registry.resolve_type_name(&key_type_def)?;
    let key_struct = registry.get_struct(&key_type_name)?;
    let key_field_names: Vec<String> = key_struct
        .fields
        .iter()
        .filter_map(|f| f.name.to_utf8_string().ok())
        .collect();
    if key_field_names.len() < 2 {
        return None; // Key struct must have at least 2 fields (from, spender)
    }

    // Find the value struct by name heuristic: variant_name + "Value"
    let value_type_name = format!("{}Value", "Allowance");
    let value_struct = registry.get_struct(&value_type_name)?;
    let value_field_names: Vec<String> = value_struct
        .fields
        .iter()
        .filter_map(|f| f.name.to_utf8_string().ok())
        .collect();
    if !value_field_names.contains(&"amount".to_string()) {
        return None; // Value struct must have an "amount" field
    }

    // Detect storage type from the call chain
    let storage_type = internal_calls
        .iter()
        .find_map(|&callee| detect_storage_type_in_chain(module, callee, 3))
        .unwrap_or(StorageType::Temporary);

    cov_mark::hit!(detect_spend_allowance_wrapper_hit);
    Some(SpendAllowanceInfo {
        storage_type,
        union_name,
        variant_name: "Allowance".to_string(),
        key_type_name,
        key_field_names,
        value_type_name,
        value_field_names,
    })
}

/// Detect a `write_allowance` helper function.
///
/// These are the Soroban token SDK's allowance write helpers that:
/// 1. Optionally validate expiration_ledger >= ledger.sequence() (if amount > 0)
/// 2. Write AllowanceValue { amount, expiration_ledger } to temporary storage
/// 3. Optionally extend TTL (if amount > 0)
///
/// Pattern: `(i64, i64, i64, i64, i32) -> void` where params 0-1 = from/spender,
/// params 2-3 = amount (i128 lo/hi), param 4 = expiration_ledger (u32 as i32).
///
/// Key distinction from spend_allowance (4 params):
/// - 5 params (extra expiration_ledger)
/// - Does NOT read from storage (no get_contract_data) — write only
/// - Has extend_ttl in call chain
/// - No i64.sub instruction
fn detect_write_allowance_wrapper(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<SpendAllowanceInfo> {
    use crate::wasm::imports::HostModule;
    use crate::wasm::ir::{WasmInstr, WasmType};

    let func = module.get_function(func_idx)?;
    let func_type = module.get_func_type(func_idx)?;

    // Must be 5 params (4 i64 + 1 i32) with void return.
    // The 5th param (expiration_ledger) is u32, compiled as i32.
    if func_type.params.len() != 5 || !func_type.results.is_empty() {
        return None;
    }
    // First 4 params must be i64 (from, spender, amount_lo, amount_hi)
    if !func_type.params[..4].iter().all(|p| *p == WasmType::I64) {
        return None;
    }
    // 5th param must be i32 (expiration_ledger as u32)
    if func_type.params[4] != WasmType::I32 {
        return None;
    }

    // Body must be moderate size
    if func.body.len() > 200 {
        return None;
    }

    // Check for key instructions.
    // write_allowance must NOT have i64.sub (that's spend_allowance).
    let mut has_sub = false;
    let mut internal_calls: Vec<u32> = Vec::new();
    // Also check for DIRECT host calls (write_allowance may call put_contract_data directly)
    let mut found_write = false;
    let mut found_extend_ttl = false;

    for instr in &func.body {
        match instr {
            WasmInstr::I64Sub => has_sub = true,
            WasmInstr::Call(target) => {
                if let Some(host_fn) = module.imports.get_by_index(*target) {
                    // Direct host call — check for storage operations
                    if host_fn.module == HostModule::Ledger {
                        if host_fn.name == "put_contract_data" {
                            found_write = true;
                        }
                        if host_fn.name == "extend_contract_data_ttl" {
                            found_extend_ttl = true;
                        }
                    }
                } else {
                    internal_calls.push(*target);
                }
            }
            _ => {}
        }
    }

    // Must NOT have subtraction (distinguishes from spend_allowance)
    if has_sub {
        return None;
    }

    // Call chain must reach write (put_contract_data) AND extend_ttl.
    // Check both direct host calls (found above) and call chain through internal functions.
    for &callee in &internal_calls {
        if !found_write
            && function_calls_host_in_chain(
                module,
                callee,
                HostModule::Ledger,
                "put_contract_data",
                2,
            )
        {
            found_write = true;
        }
        if !found_extend_ttl
            && function_calls_host_in_chain(
                module,
                callee,
                HostModule::Ledger,
                "extend_contract_data_ttl",
                2,
            )
        {
            found_extend_ttl = true;
        }
    }

    if !found_write || !found_extend_ttl {
        return None;
    }

    // Registry must have a union with an "Allowance" variant
    let (union_name, has_data) = registry.find_union_variant("Allowance")?;
    if !has_data {
        return None;
    }

    // Get key struct type from the variant
    let key_type_def = registry.find_variant_data_type(&union_name, "Allowance")?;
    let key_type_name = registry.resolve_type_name(&key_type_def)?;
    let key_struct = registry.get_struct(&key_type_name)?;
    let key_field_names: Vec<String> = key_struct
        .fields
        .iter()
        .filter_map(|f| f.name.to_utf8_string().ok())
        .collect();
    if key_field_names.len() < 2 {
        return None;
    }

    // Find the value struct (AllowanceValue)
    let value_type_name = format!("{}Value", "Allowance");
    let value_struct = registry.get_struct(&value_type_name)?;
    let value_field_names: Vec<String> = value_struct
        .fields
        .iter()
        .filter_map(|f| f.name.to_utf8_string().ok())
        .collect();

    // Detect storage type
    let storage_type = internal_calls
        .iter()
        .find_map(|&callee| detect_storage_type_in_chain(module, callee, 2))
        .unwrap_or(StorageType::Temporary);

    cov_mark::hit!(detect_write_allowance_wrapper_hit);
    Some(SpendAllowanceInfo {
        storage_type,
        union_name,
        variant_name: "Allowance".to_string(),
        key_type_name,
        key_field_names,
        value_type_name,
        value_field_names,
    })
}

/// Check if a function's call chain (up to `depth` levels) reaches a specific
/// host function. Generalizes `function_calls_host` with depth recursion.
/// True if `func_idx` (transitively, depth-capped) calls ANY import from the
/// given host module. Used as an exclusion gate: e.g. a storage getter that
/// touches the Int module decodes its loaded `Val` into scalar limbs, so its
/// out-slot layout is NOT the raw `[disc@0, val@8]` shape.
fn function_calls_module_in_chain(
    module: &WasmModule,
    func_idx: u32,
    host_module: HostModule,
    depth: u32,
) -> bool {
    if depth == 0 {
        return false;
    }
    let Some(func) = module.get_function(func_idx) else {
        return false;
    };
    for instr in &func.body {
        if let crate::wasm::ir::WasmInstr::Call(target) = instr {
            if let Some(host_fn) = module.imports.get_by_index(*target) {
                if host_fn.module == host_module {
                    return true;
                }
            } else if depth > 1
                && function_calls_module_in_chain(module, *target, host_module, depth - 1)
            {
                return true;
            }
        }
    }
    false
}

fn function_calls_host_in_chain(
    module: &WasmModule,
    func_idx: u32,
    host_module: HostModule,
    host_name: &str,
    depth: u32,
) -> bool {
    if depth == 0 {
        return false;
    }

    let func = match module.get_function(func_idx) {
        Some(f) => f,
        None => return false,
    };

    for instr in &func.body {
        if let crate::wasm::ir::WasmInstr::Call(target) = instr {
            if let Some(host_fn) = module.imports.get_by_index(*target) {
                if host_fn.module == host_module && host_fn.name == host_name {
                    return true;
                }
            } else if depth > 1
                && function_calls_host_in_chain(module, *target, host_module, host_name, depth - 1)
            {
                return true;
            }
        }
    }
    false
}

/// Info returned by `detect_keyed_storage_set_wrapper`.
struct KeyedStorageSetWrapperInfo {
    /// Union type name (e.g., "DataKey").
    union_name: String,
    /// Variant names in br_table index order.
    variants: Vec<String>,
    /// Whether each variant carries data (TupleV0 vs VoidV0).
    has_data: Vec<bool>,
    /// Storage type (Instance, Persistent, Temporary).
    storage_type: StorageType,
    /// If `Some(idx)`, the key variant index is hardcoded inside the function
    /// and the caller args are `(value, ...)` instead of `(key_index, value)`.
    hardcoded_variant_idx: Option<usize>,
}

/// Detect a "keyed storage set" wrapper function.
///
/// Two sub-patterns are recognized:
///
/// **Direct** (e.g., func 23 in liquidity_pool): first param is the key index,
/// the function directly calls `put_contract_data` and an internal key constructor
/// with a `br_table`.
///
/// ```text
/// (func (param i64 i64)          ;; (key_index, value)
///   local.get 0                   ;; key_index
///   local.get 1                   ;; value
///   call <key_constructor>        ;; br_table-based enum key construction
///   local.get 1                   ;; value again
///   i64.const <storage_type>      ;; 0=Temp, 1=Persistent, 2=Instance
///   call <put_contract_data>      ;; host import
///   drop
/// )
/// ```
///
/// **Indirect / fixed-key** (e.g., func 41 in liquidity_pool): the key index is
/// a hardcoded `I64Const` inside the function body, and the function delegates
/// to an intermediate wrapper chain that eventually reaches `put_contract_data`
/// and a `br_table` key constructor.
///
/// ```text
/// (func (param i64 i64)          ;; (value_lo, value_hi) or (value, ...)
///   i64.const <key_index>         ;; hardcoded variant index
///   local.get 0
///   local.get 1
///   call <intermediate>           ;; chain reaching put_contract_data + br_table
/// )
/// ```
fn detect_keyed_storage_set_wrapper(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<KeyedStorageSetWrapperInfo> {
    use crate::wasm::ir::WasmInstr;

    let func = module.get_function(func_idx)?;
    let func_type = module.get_func_type(func_idx)?;

    // Must return void
    if !func_type.results.is_empty() {
        return None;
    }

    // Must have i64 params only
    if func_type
        .params
        .iter()
        .any(|p| *p != crate::wasm::ir::WasmType::I64)
    {
        return None;
    }

    // Body must be short (thin wrapper)
    if func.body.len() > 20 {
        return None;
    }

    // Collect call targets and I64Const values from the body
    let mut internal_calls: Vec<u32> = Vec::new();
    let mut has_put_contract_data = false;
    let mut storage_type = StorageType::Instance;
    let mut i64_consts: Vec<i64> = Vec::new();

    for (i, instr) in func.body.iter().enumerate() {
        match instr {
            WasmInstr::Call(target) => {
                if let Some(host_fn) = module.imports.get_by_index(*target) {
                    if host_fn.module == HostModule::Ledger && host_fn.name == "put_contract_data" {
                        has_put_contract_data = true;
                        // Look backwards for the storage type I64Const
                        for j in (0..i).rev().take(5) {
                            if let WasmInstr::I64Const(v) = &func.body[j] {
                                storage_type = match *v {
                                    0 => StorageType::Temporary,
                                    1 => StorageType::Persistent,
                                    2 => StorageType::Instance,
                                    _ => continue,
                                };
                                break;
                            }
                        }
                    }
                } else {
                    internal_calls.push(*target);
                }
            }
            WasmInstr::I64Const(v) => {
                i64_consts.push(*v);
            }
            _ => {}
        }
    }

    // --- Pattern 1: Direct (calls put_contract_data + key constructor) ---
    if has_put_contract_data {
        if let Some(&key_constructor_idx) = internal_calls.first()
            && func_type.params.len() == 2
            && has_br_table_in_body(module, key_constructor_idx)
            && let Some(enum_info) =
                detect_enum_dispatch_wrapper(module, registry, key_constructor_idx)
        {
            return Some(KeyedStorageSetWrapperInfo {
                union_name: enum_info.union_name,
                variants: enum_info.variants,
                has_data: enum_info.has_data,
                storage_type,
                hardcoded_variant_idx: None,
            });
        }
        return None;
    }

    // --- Pattern 2: Indirect / fixed-key ---
    // Must have exactly 2 i64 params (the thin wrapper signature), call exactly
    // one internal function, and have a hardcoded I64Const that is the key variant
    // index. The 2-param restriction prevents matching intermediate functions like
    // func 22 (3 params) where the I64Const is a storage type, not a key index.
    if func_type.params.len() != 2 || internal_calls.len() != 1 || i64_consts.is_empty() {
        return None;
    }

    let delegate_idx = internal_calls[0];
    // The hardcoded I64Const must be a small non-negative number (variant index).
    // Filter out large values (storage type constants that could also be small)
    // by requiring the delegate chain to contain both br_table and put_contract_data.
    let key_index_candidate = i64_consts[0];
    if !(0..=255).contains(&key_index_candidate) {
        return None;
    }

    // Check that the delegate chain (up to 3 levels deep) reaches put_contract_data
    // and has a br_table. Depth 3 is needed because the chain can be:
    // thin_wrapper -> intermediate -> storage_func -> key_constructor (with br_table)
    if !delegate_chain_has_storage_and_dispatch(module, delegate_idx, 3) {
        return None;
    }

    // Find the enum dispatch info by scanning the delegate chain for a function
    // with br_table and variant string references
    let enum_info = find_enum_dispatch_in_chain(module, registry, delegate_idx, 3)?;

    // Detect storage type from the delegate chain
    let chain_storage_type =
        detect_storage_type_in_chain(module, delegate_idx, 3).unwrap_or(StorageType::Instance);

    let variant_idx = key_index_candidate as usize;
    if variant_idx >= enum_info.variants.len() {
        return None;
    }

    Some(KeyedStorageSetWrapperInfo {
        union_name: enum_info.union_name,
        variants: enum_info.variants,
        has_data: enum_info.has_data,
        storage_type: chain_storage_type,
        hardcoded_variant_idx: Some(variant_idx),
    })
}

/// Detect a "keyed storage get" wrapper function — the GET equivalent of
/// `detect_keyed_storage_set_wrapper`.
///
/// Two sub-patterns:
/// - **Direct**: function calls `get_contract_data` (or `has_contract_data` +
///   `get_contract_data`) and a key constructor with br_table.
/// - **Indirect/fixed-key**: function has a hardcoded I64Const key index and
///   delegates to a chain reaching get_contract_data + br_table.
///
/// The caller passes the key variant index as an I64Const argument. The wrapper
/// resolves the variant and emits `StorageGet { key: DataKey::Variant }`.
fn detect_keyed_storage_get_wrapper(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<KeyedStorageSetWrapperInfo> {
    use crate::wasm::ir::WasmInstr;

    let func = module.get_function(func_idx)?;
    let func_type = module.get_func_type(func_idx)?;

    // Body must be short-to-moderate. i128-returning get wrappers (like func 20
    // in liquidity_pool) include block/end markers + i128 decoding logic, reaching
    // ~45 instructions in the WasmModule's flat instruction count.
    if func.body.len() > 60 {
        return None;
    }

    // Collect call targets and I64Const values
    let mut internal_calls: Vec<u32> = Vec::new();
    let mut has_get_contract_data = false;
    let mut has_has_contract_data = false;
    let mut storage_type = StorageType::Instance;
    let mut i64_consts: Vec<i64> = Vec::new();

    for (i, instr) in func.body.iter().enumerate() {
        match instr {
            WasmInstr::Call(target) => {
                if let Some(host_fn) = module.imports.get_by_index(*target) {
                    if host_fn.module == HostModule::Ledger {
                        if host_fn.name == "get_contract_data" {
                            has_get_contract_data = true;
                            // Look backwards for storage type
                            for j in (0..i).rev().take(5) {
                                if let WasmInstr::I64Const(v) = &func.body[j] {
                                    storage_type = match *v {
                                        0 => StorageType::Temporary,
                                        1 => StorageType::Persistent,
                                        2 => StorageType::Instance,
                                        _ => continue,
                                    };
                                    break;
                                }
                            }
                        }
                        if host_fn.name == "has_contract_data" {
                            has_has_contract_data = true;
                        }
                    }
                } else {
                    internal_calls.push(*target);
                }
            }
            WasmInstr::I64Const(v) => {
                i64_consts.push(*v);
            }
            _ => {}
        }
    }

    // --- Pattern 1: Direct (calls get_contract_data + key constructor) ---
    if has_get_contract_data || has_has_contract_data {
        // Find a key constructor with br_table in the internal calls
        for &callee in &internal_calls {
            if has_br_table_in_body(module, callee)
                && let Some(enum_info) = detect_enum_dispatch_wrapper(module, registry, callee)
            {
                return Some(KeyedStorageSetWrapperInfo {
                    union_name: enum_info.union_name,
                    variants: enum_info.variants,
                    has_data: enum_info.has_data,
                    storage_type,
                    hardcoded_variant_idx: None,
                });
            }
        }
        // No br_table key constructor found — check one level deeper
        for &callee in &internal_calls {
            if let Some(enum_info) = find_enum_dispatch_in_chain(module, registry, callee, 2) {
                let chain_storage =
                    detect_storage_type_in_chain(module, callee, 2).unwrap_or(storage_type);
                return Some(KeyedStorageSetWrapperInfo {
                    union_name: enum_info.union_name,
                    variants: enum_info.variants,
                    has_data: enum_info.has_data,
                    storage_type: chain_storage,
                    hardcoded_variant_idx: None,
                });
            }
        }
        return None;
    }

    // --- Pattern 2: Indirect / fixed-key ---
    // Must have 1-2 params, call one internal function, and have a hardcoded I64Const.
    if func_type.params.len() > 2 || internal_calls.len() != 1 || i64_consts.is_empty() {
        return None;
    }

    let delegate_idx = internal_calls[0];
    let key_index_candidate = i64_consts[0];
    if !(0..=255).contains(&key_index_candidate) {
        return None;
    }

    // Check that the delegate chain reaches get/has_contract_data and br_table
    let reaches_get = function_calls_host_in_chain(
        module,
        delegate_idx,
        HostModule::Ledger,
        "get_contract_data",
        3,
    ) || function_calls_host_in_chain(
        module,
        delegate_idx,
        HostModule::Ledger,
        "has_contract_data",
        3,
    );
    if !reaches_get {
        return None;
    }

    // Find enum dispatch info
    let enum_info = find_enum_dispatch_in_chain(module, registry, delegate_idx, 3)?;

    let chain_storage_type =
        detect_storage_type_in_chain(module, delegate_idx, 3).unwrap_or(StorageType::Instance);

    let variant_idx = key_index_candidate as usize;
    if variant_idx >= enum_info.variants.len() {
        return None;
    }

    Some(KeyedStorageSetWrapperInfo {
        union_name: enum_info.union_name,
        variants: enum_info.variants,
        has_data: enum_info.has_data,
        storage_type: chain_storage_type,
        hardcoded_variant_idx: Some(variant_idx),
    })
}

/// Check if a function's body contains a `BrTable` instruction.
fn has_br_table_in_body(module: &WasmModule, func_idx: u32) -> bool {
    module
        .get_function(func_idx)
        .map(|f| {
            f.body
                .iter()
                .any(|instr| matches!(instr, crate::wasm::ir::WasmInstr::BrTable { .. }))
        })
        .unwrap_or(false)
}

/// Check if a function's delegate chain (up to `depth` levels) reaches both
/// `put_contract_data` and a `br_table`.
fn delegate_chain_has_storage_and_dispatch(module: &WasmModule, func_idx: u32, depth: u32) -> bool {
    if depth == 0 {
        return false;
    }

    let func = match module.get_function(func_idx) {
        Some(f) => f,
        None => return false,
    };

    let mut found_put = false;
    let mut found_br_table = false;

    if func
        .body
        .iter()
        .any(|instr| matches!(instr, crate::wasm::ir::WasmInstr::BrTable { .. }))
    {
        found_br_table = true;
    }

    for instr in &func.body {
        if let crate::wasm::ir::WasmInstr::Call(target) = instr {
            if let Some(host_fn) = module.imports.get_by_index(*target) {
                if host_fn.module == HostModule::Ledger && host_fn.name == "put_contract_data" {
                    found_put = true;
                }
            } else if depth > 1 {
                // Recurse into internal calls
                if delegate_chain_has_storage_and_dispatch(module, *target, depth - 1) {
                    return true;
                }
                // Also check if the callee has br_table or put_contract_data
                if has_br_table_in_body(module, *target) {
                    found_br_table = true;
                }
                if function_calls_host(module, *target, HostModule::Ledger, "put_contract_data") {
                    found_put = true;
                }
            }
        }
    }

    found_put && found_br_table
}

/// Check if a function directly calls a specific host function.
fn function_calls_host(
    module: &WasmModule,
    func_idx: u32,
    host_module: HostModule,
    host_name: &str,
) -> bool {
    let func = match module.get_function(func_idx) {
        Some(f) => f,
        None => return false,
    };
    for instr in &func.body {
        if let crate::wasm::ir::WasmInstr::Call(target) = instr
            && let Some(host_fn) = module.imports.get_by_index(*target)
            && host_fn.module == host_module
            && host_fn.name == host_name
        {
            return true;
        }
    }
    false
}

/// Find enum dispatch info by scanning a function's call chain (up to `depth`
/// levels) for a function whose body matches `detect_enum_dispatch_wrapper`.
fn find_enum_dispatch_in_chain(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
    depth: u32,
) -> Option<EnumDispatchWrapperInfo> {
    if depth == 0 {
        return None;
    }

    // Try the function itself first
    if let Some(info) = detect_enum_dispatch_wrapper(module, registry, func_idx) {
        return Some(info);
    }

    // Try internal call targets
    let func = module.get_function(func_idx)?;
    for instr in &func.body {
        if let crate::wasm::ir::WasmInstr::Call(target) = instr
            && module.imports.get_by_index(*target).is_none()
        {
            // Internal call — recurse
            if let Some(info) = find_enum_dispatch_in_chain(module, registry, *target, depth - 1) {
                return Some(info);
            }
        }
    }
    None
}

/// Detect storage type from a function's call chain (up to `depth` levels).
/// Info recovered from a fallible storage-get helper. See
/// [`detect_fallible_storage_get_helper`].
struct FallibleStorageGetInfo {
    storage_type: StorageType,
    error_code: u32,
    /// `Some` when the storage key is a constant inside the helper (a 1-param
    /// helper like `get_admin`'s `Admin` symbol); `None` when the key is the
    /// caller's 2nd argument (a parameter-keyed getter).
    const_key: Option<SorobanExpr>,
}

/// Recognize a "fallible storage-get" helper: a void function taking an I32
/// out-pointer that reads `get_contract_data` and writes a discriminated
/// `Result`-shaped struct `{ tag@0, error_code@4, value@8.. }`, storing a single
/// literal contract error code on the missing-key path. The SDK compiles
/// `env.storage().<dur>().get(&key).ok_or(Error::V)` into exactly this shape, but
/// inlining + structurization collapse it to a `has`/`extend_ttl` + `todo!()`
/// husk, dropping the value and the `Err`. This recovers `(storage_type,
/// error_code, const_key?)` so the caller can rebuild the faithful `.ok_or(..)`.
///
/// Airtight: requires void return + I32 first param (1 or 2 params), reachability
/// to `get_contract_data` but NOT `put_contract_data` (excludes setters /
/// read-modify-write), a discriminant store at offset 0, and EXACTLY ONE distinct
/// non-zero `[I32Const(code), I32Store(4)]` (the error-field write). Any deviation
/// → `None` → the existing husk is emitted unchanged.
fn detect_fallible_storage_get_helper(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<FallibleStorageGetInfo> {
    use crate::wasm::ir::WasmInstr;
    let func_type = module.get_func_type(func_idx)?;
    // Void helper whose first param is the I32 out-pointer (sret); 1 or 2 params.
    if !func_type.results.is_empty() || func_type.params.len() > 2 {
        return None;
    }
    if !matches!(
        func_type.params.first(),
        Some(crate::wasm::ir::WasmType::I32)
    ) {
        return None;
    }
    // Reads storage, never writes it.
    if !function_calls_host_in_chain(module, func_idx, HostModule::Ledger, "get_contract_data", 3) {
        return None;
    }
    if function_calls_host_in_chain(module, func_idx, HostModule::Ledger, "put_contract_data", 3) {
        return None;
    }
    let func = module.get_function(func_idx)?;
    // The missing-key path writes a single literal contract error code into the
    // result's error field: `I32Const(code); I32Store(offset 4)`, code != 0.
    let mut error_code: Option<u32> = None;
    for w in func.body.windows(2) {
        if let [WasmInstr::I32Const(c), WasmInstr::I32Store(4)] = w {
            let c = *c as u32;
            if c == 0 {
                continue;
            }
            match error_code {
                Some(prev) if prev != c => return None, // ambiguous → bail
                _ => error_code = Some(c),
            }
        }
    }
    let error_code = error_code?;
    // A discriminated Result writer tags the ok/err discriminant at offset 0.
    if !func
        .body
        .iter()
        .any(|i| matches!(i, WasmInstr::I32Store(0)))
    {
        return None;
    }
    let storage_type = detect_storage_type_in_chain(module, func_idx, 3)?;
    // A 1-param helper keys storage by a constant inside the helper (e.g. `Admin`):
    // recover it from the Val const feeding get_contract_data.
    let const_key = if func_type.params.len() == 1 {
        fallible_get_const_key(module, registry, func_idx)
    } else {
        None
    };
    Some(FallibleStorageGetInfo {
        storage_type,
        error_code,
        const_key,
    })
}

/// Recover the constant storage key a 1-param fallible-get helper passes to
/// `get_contract_data`. The host call is `get_contract_data(key_val,
/// storage_type_val)`, so the key is the `I64Const` two positions before the
/// `Call` (`key; storage_type; call`).
fn fallible_get_const_key(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<SorobanExpr> {
    use crate::wasm::ir::WasmInstr;
    let func = module.get_function(func_idx)?;
    for (i, instr) in func.body.iter().enumerate() {
        if let WasmInstr::Call(target) = instr
            && let Some(hf) = module.imports.get_by_index(*target)
            && hf.module == HostModule::Ledger
            && hf.name == "get_contract_data"
            && i >= 2
            && let WasmInstr::I64Const(key_val) = func.body[i - 2]
        {
            let key = try_decode_val(key_val, registry);
            // Only accept a clean, fabrication-free key (a symbol/scalar literal).
            if !matches!(key, SorobanExpr::UnknownVal | SorobanExpr::Void) {
                return Some(key);
            }
        }
    }
    None
}

/// The dissected body of a recognized getter-protocol husk: the single
/// storage get, the local key bindings that feed it, and the real TTL side
/// effects to preserve. See [`collect_getter_protocol`].
struct GetterProtocol {
    get: (StorageType, SorobanExpr),
    bindings: Vec<(String, SorobanExpr)>,
}

/// Dissect an inlined helper body that is EXACTLY a storage-getter protocol:
/// TTL extensions, pure key-construction bindings, `has` guards, decode
/// tag-guards (bare `Panic`), and ONE storage get — nothing else. Any other
/// statement or expression (a set, an event, an auth, an invoke, a second
/// get, a get hiding inside a condition) makes the whole dissection fail, so
/// the caller can only replace husks whose every statement is accounted for.
fn collect_getter_protocol(stmts: &[SorobanStmt]) -> Option<GetterProtocol> {
    let mut gets: Vec<(StorageType, SorobanExpr)> = Vec::new();
    let mut bindings: Vec<(String, SorobanExpr)> = Vec::new();
    if !walk_getter_protocol(stmts, &mut gets, &mut bindings) {
        return None;
    }
    let [(storage_type, key)] = gets.as_slice() else {
        return None; // zero or several gets → not this protocol
    };
    Some(GetterProtocol {
        get: (*storage_type, key.clone()),
        bindings,
    })
}

fn walk_getter_protocol(
    stmts: &[SorobanStmt],
    gets: &mut Vec<(StorageType, SorobanExpr)>,
    bindings: &mut Vec<(String, SorobanExpr)>,
) -> bool {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Expr(e) => match e {
                SorobanExpr::ExtendInstanceAndCodeTtl { .. }
                | SorobanExpr::StorageExtendTtl { .. } => {}
                SorobanExpr::StorageGet {
                    storage_type, key, ..
                } => gets.push((*storage_type, (**key).clone())),
                SorobanExpr::StorageHas { .. }
                | SorobanExpr::Panic
                | SorobanExpr::UnknownVal
                | SorobanExpr::Void => {}
                _ => return false,
            },
            SorobanStmt::Let { name, value, .. } => match value {
                SorobanExpr::StorageGet {
                    storage_type, key, ..
                } => gets.push((*storage_type, (**key).clone())),
                v if protocol_key_value(v) => bindings.push((name.clone(), v.clone())),
                _ => return false,
            },
            SorobanStmt::Assign { value, .. } => {
                if !protocol_key_value(value) {
                    return false;
                }
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                if !protocol_guard_cond(condition)
                    || !walk_getter_protocol(then_body, gets, bindings)
                    || !walk_getter_protocol(else_body, gets, bindings)
                {
                    return false;
                }
            }
            SorobanStmt::Block(body) => {
                if !walk_getter_protocol(body, gets, bindings) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

/// A value a getter protocol may bind to a local: key material (symbols,
/// literals, vec/enum construction over key material) or the simulation's own
/// placeholders. NEVER a storage/host operation — those must surface at
/// statement level where the walker accounts for them.
fn protocol_key_value(e: &SorobanExpr) -> bool {
    match e {
        SorobanExpr::SymbolLiteral(_)
        | SorobanExpr::StringLiteral(_)
        | SorobanExpr::U32Literal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::I64Literal(_)
        | SorobanExpr::U128Literal(_)
        | SorobanExpr::I128Literal(_)
        | SorobanExpr::BoolLiteral(_)
        | SorobanExpr::Param(_)
        | SorobanExpr::Local(_)
        | SorobanExpr::NamedLocal(_)
        | SorobanExpr::UnknownVal
        | SorobanExpr::Void => true,
        SorobanExpr::VecConstruct(items) => items.iter().all(protocol_key_value),
        SorobanExpr::EnumConstruct { fields, .. } => fields.iter().all(protocol_key_value),
        _ => false,
    }
}

/// A condition a getter protocol's guard may test: `has` checks, tag reads,
/// and boolean/comparison structure over those and key material. A
/// `StorageGet` anywhere in a condition fails the walk — the value read there
/// would be lost by the husk replacement.
fn protocol_guard_cond(e: &SorobanExpr) -> bool {
    match e {
        SorobanExpr::StorageHas { .. } => true,
        SorobanExpr::ValTag(inner) => protocol_guard_cond(inner),
        SorobanExpr::Not(a) => protocol_guard_cond(a),
        SorobanExpr::Eq(a, b)
        | SorobanExpr::Ne(a, b)
        | SorobanExpr::Lt(a, b)
        | SorobanExpr::Le(a, b)
        | SorobanExpr::Gt(a, b)
        | SorobanExpr::Ge(a, b)
        | SorobanExpr::And(a, b)
        | SorobanExpr::Or(a, b) => protocol_guard_cond(a) && protocol_guard_cond(b),
        other => protocol_key_value(other),
    }
}

/// The unique meaningful value bound to `name` in a protocol husk, skipping
/// the simulation's `UnknownVal` placeholder inits and bare local echoes.
/// Duplicated identical bindings collapse; two DIFFERENT meaningful values →
/// `None` (ambiguous — stay honest).
fn unique_binding_value(bindings: &[(String, SorobanExpr)], name: &str) -> Option<SorobanExpr> {
    let mut found: Option<SorobanExpr> = None;
    for (n, v) in bindings {
        if n != name
            || matches!(
                v,
                SorobanExpr::UnknownVal
                    | SorobanExpr::Void
                    | SorobanExpr::Local(_)
                    | SorobanExpr::NamedLocal(_)
            )
        {
            continue;
        }
        match &found {
            Some(prev) if prev != v => return None,
            _ => found = Some(v.clone()),
        }
    }
    found
}

/// The scalar type a pure `TryFromVal` decode helper produces. See
/// [`detect_tryfromval_decode_helper`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DecodeHelperClass {
    U64,
    U128,
    I128,
}

/// The set of distinct `i64.store` offsets in a function body, or `None` if
/// the body also contains an `i32.store` (a bookkeeping/struct writer — not
/// one of the fixed scalar out-slot layouts these detectors prove).
fn i64_store_offsets(func: &crate::wasm::ir::WasmFunction) -> Option<Vec<u32>> {
    use crate::wasm::ir::WasmInstr;
    let mut offs: Vec<u32> = Vec::new();
    for i in &func.body {
        match i {
            WasmInstr::I64Store(o) => {
                if !offs.contains(o) {
                    offs.push(*o);
                }
            }
            WasmInstr::I32Store(_) | WasmInstr::I32Store8(_) | WasmInstr::I32Store16(_) => {
                return None;
            }
            _ => {}
        }
    }
    offs.sort_unstable();
    Some(offs)
}

/// True when the body decodes ITS OWN `val` parameter with the named
/// Int-module import: an adjacent `[local.get 1, call <import>]` window that
/// occurs BEFORE any reassignment of local 1 (`local.set/tee 1`). This is a
/// dataflow proof, not a reachability co-occurrence — the decode's operand is
/// provably the parameter (greptile P1 on PR #42). Position-aware rather than
/// body-wide: real SDK decoders commonly REUSE local 1 for the decoded result
/// after the last decode window (aqua's u64/u128 decoders), which must not
/// disqualify the pre-reassignment windows.
fn decodes_own_param(
    module: &WasmModule,
    func: &crate::wasm::ir::WasmFunction,
    name: &str,
) -> bool {
    use crate::wasm::ir::WasmInstr;
    let first_reassign = func
        .body
        .iter()
        .position(|i| matches!(i, WasmInstr::LocalSet(1) | WasmInstr::LocalTee(1)))
        .unwrap_or(usize::MAX);
    // Flat position proves execution order only without back-edges: a loop
    // that decodes local 1 and reassigns it later in the body would decode
    // the REPLACEMENT on iterations 2+, so any `loop` + reassignment voids
    // the position proof (greptile P1 on PR #44). Loop-free bodies (all the
    // real SDK decoders) keep the position-aware acceptance.
    if first_reassign != usize::MAX
        && func
            .body
            .iter()
            .any(|i| matches!(i, WasmInstr::Loop { .. }))
    {
        return false;
    }
    func.body.windows(2).enumerate().any(|(i, w)| {
        i < first_reassign
            && matches!(w, [WasmInstr::LocalGet(1), WasmInstr::Call(t)]
                if module.imports.get_by_index(*t).is_some_and(|hf| hf.module == HostModule::Int && hf.name == name))
    })
}

/// Recognize a pure `TryFromVal` scalar-decode helper (issue #34 tranche 2):
/// a void `(out_ptr: i32, val: i64)` function that converts its Val operand
/// into a scalar and writes a `Result`-shaped struct — `[disc@0, val@8]`
/// (u64) or `[disc@0, err@8, lo@16, hi@24]` (u128/i128) — with NO other
/// effects (no storage access, no cross-contract call, no struct unpack).
/// The small/object tag split inside collapses the payload stores at the
/// lifter's joins, but the semantic is total on the payload slots: they hold
/// exactly the decoded operand. The discriminant is path-dependent and is
/// NOT covered — it stays whatever the lift left (honest).
///
/// Dataflow-proven, not co-occurrence (greptile P1s on PR #42): the decode
/// calls must consume the `val` PARAMETER directly (`[local.get 1, call]`
/// windows, local 1 never reassigned), and the body's `i64.store` offsets
/// must be a subset of the claimed layout (any extra store, or any
/// `i32.store`, disqualifies).
fn detect_tryfromval_decode_helper(
    module: &WasmModule,
    func_idx: u32,
) -> Option<DecodeHelperClass> {
    use crate::wasm::ir::WasmType;
    let func_type = module.get_func_type(func_idx)?;
    if !func_type.results.is_empty()
        || func_type.params.as_slice() != [WasmType::I32, WasmType::I64]
    {
        return None;
    }
    if function_calls_module_in_chain(module, func_idx, HostModule::Ledger, 3)
        || function_calls_module_in_chain(module, func_idx, HostModule::Call, 3)
        || function_calls_host_in_chain(
            module,
            func_idx,
            HostModule::Map,
            "map_unpack_to_linear_memory",
            3,
        )
        || function_calls_host_in_chain(
            module,
            func_idx,
            HostModule::Vec,
            "vec_unpack_to_linear_memory",
            3,
        )
    {
        return None;
    }
    let func = module.get_function(func_idx)?;
    let store_offs = i64_store_offsets(func)?;
    let subset_of = |allowed: &[u32]| store_offs.iter().all(|o| allowed.contains(o));
    // Exclusions stay chain-wide (broader is safer); the POSITIVE decode
    // evidence must be the body's own `[local.get 1, call]` windows.
    let chain =
        |name: &str| function_calls_host_in_chain(module, func_idx, HostModule::Int, name, 3);
    let own = |name: &str| decodes_own_param(module, func, name);
    let u64_decode = own("obj_to_u64");
    let u128_decode = own("obj_to_u128_hi64") && own("obj_to_u128_lo64");
    let i128_decode = own("obj_to_i128_hi64") && own("obj_to_i128_lo64");
    let wide = [
        "obj_to_u128_hi64",
        "obj_to_u128_lo64",
        "obj_to_i128_hi64",
        "obj_to_i128_lo64",
    ];
    match (u64_decode, u128_decode, i128_decode) {
        (false, true, false)
            if !chain("obj_to_u64")
                && !chain("obj_to_i64")
                && !chain("obj_to_i128_hi64")
                && !chain("obj_to_i128_lo64")
                && store_offs.contains(&16)
                && store_offs.contains(&24)
                && subset_of(&[0, 8, 16, 24]) =>
        {
            Some(DecodeHelperClass::U128)
        }
        (false, false, true)
            if !chain("obj_to_u64")
                && !chain("obj_to_i64")
                && !chain("obj_to_u128_hi64")
                && !chain("obj_to_u128_lo64")
                && store_offs.contains(&16)
                && store_offs.contains(&24)
                && subset_of(&[0, 8, 16, 24]) =>
        {
            Some(DecodeHelperClass::I128)
        }
        (true, false, false)
            if !chain("obj_to_i64")
                && wide.iter().all(|n| !chain(n))
                && store_offs.contains(&0)
                && store_offs.contains(&8)
                && subset_of(&[0, 8]) =>
        {
            Some(DecodeHelperClass::U64)
        }
        _ => None,
    }
}

/// Info for a recognized VALUE-RETURNING fallible getter (issue #34
/// tranche 6). See [`detect_fallible_value_getter`].
struct FallibleValueGetterInfo {
    storage_type: StorageType,
    key: SorobanExpr,
    /// The Val object tag the success path asserts (`64..=77`, e.g.
    /// 77 = `AddressObject`, 76 = `MapObject`) — the SDK's `TryFromVal`
    /// marshalling check, whose constant NAMES the loaded type.
    tag: u8,
    /// The missing-path error (`fail_with_error`'s constant Error Val),
    /// decoded against the registry's error enums.
    error: SorobanExpr,
    /// Proven instance TTL bumps, as in [`FallibleStructGetterInfo`].
    instance_ttl_bumps: Vec<(u32, u32)>,
}

/// Recognize a "value-returning fallible getter" (issue #34 tranche 6): a
/// zero-parameter `() -> i64` helper implementing
/// `env.storage().<dur>().get::<_, T>(&KEY).unwrap_or_else(|| panic_with_error!(env, E))`
/// — the aqua class rooting the reward chains (`TokenShare` share-token
/// Address, `RewardGaugesMap` gauge map). The SDK shape:
/// `[bump]; if has(KEY) { v = get(KEY); if tag(v) != T { trap } return v }
/// fail_with_error(E)`.
///
/// The helper RETURNS its value (no out-pointer), so today its result dies
/// at the lifter's block-result joins and every consumer — including
/// cross-contract invoke TARGETS (`env.invoke_contract(&todo!(), ..)`) and
/// exported-fn tails — degrades to `todo!("unknown value")`. Recognition
/// pushes the faithful get expression as the call's stack value instead of
/// inlining.
///
/// Every element is bytecode-proven; any deviation → `None`:
/// - internal, zero params, one i64 result, NO `Loop` (the position proofs
///   below rely on flat order);
/// - chains `has_contract_data` AND `get_contract_data`, never
///   `put_contract_data`, and no cross-contract call;
/// - the storage key is a proven constant ([`load_struct_const_key`]:
///   ctor-window micro-execution, incl. the proven-zero gap path);
/// - exactly one TryFromVal tag guard `[i64.const 255, i64.and,
///   i64.const T, i64.ne, br_if]` with an unambiguous object tag
///   (`64..=77`) — the guard both pins the class and names the type;
/// - exactly one missing-path window `[i64.const E, call fail]` where `E`
///   is a constant Error Val (tag 3) and `fail` reaches the
///   `fail_with_error` host import;
/// - the RETURNED value is provably the get's result: exactly one
///   `[call get, local.tee k]` window (get = import or ≤2-deep chain),
///   exactly one `[local.get k, return]` window and no other `Return`,
///   the tee precedes the return, and `k` is not reassigned between them
///   (sound under the no-`Loop` gate);
/// - every TTL-extension reachability is a proven constant instance bump
///   ([`collect_proven_instance_ttl_bumps`]).
fn detect_fallible_value_getter(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<FallibleValueGetterInfo> {
    use crate::wasm::ir::{WasmInstr as WI, WasmType};
    let ft = module.get_func_type(func_idx)?;
    if !ft.params.is_empty() || ft.results.as_slice() != [WasmType::I64] {
        return None;
    }
    let func = module.get_function(func_idx)?;
    if func.body.iter().any(|i| matches!(i, WI::Loop { .. })) {
        return None;
    }
    let ledger =
        |name: &str| function_calls_host_in_chain(module, func_idx, HostModule::Ledger, name, 3);
    if !ledger("has_contract_data") || !ledger("get_contract_data") || ledger("put_contract_data") {
        return None;
    }
    if function_calls_module_in_chain(module, func_idx, HostModule::Call, 3) {
        return None;
    }
    let instance_ttl_bumps = collect_proven_instance_ttl_bumps(module, func)?;
    let storage_type = detect_storage_type_in_chain(module, func_idx, 3)?;
    let key = load_struct_const_key(module, registry, func)?;
    // Unique get-tee: the get's result captured in local `k` AND left on
    // the operand stack (tee) for the guard that must follow.
    let mut get_tee: Option<(usize, u32)> = None;
    for (i, w) in func.body.windows(2).enumerate() {
        if let [WI::Call(g), WI::LocalTee(k)] = w
            && func_reaches_host(module, *g, HostModule::Ledger, "get_contract_data", 0)
            && get_tee.replace((i + 1, *k)).is_some()
        {
            return None;
        }
    }
    let (tee_pos, k) = get_tee?;
    // The get is has-GUARDED: a unique window where a conditional consumes
    // the has result — directly (`[call has, if/br_if]`, the i32-wrapper
    // shape) or through the Bool-Val compare (`[call has, i64.const 1,
    // i64.eq, if/br_if]`, the direct-import shape) — positioned before the
    // get, so the missing-key path provably branches around it (flat order
    // is execution order under the no-Loop gate). Without this, a helper
    // getting unconditionally would trap on a missing key where the
    // reconstruction panics with E (greptile P1 on PR #46).
    let is_branch = |i: &crate::wasm::ir::WasmInstr| matches!(i, WI::If { .. } | WI::BrIf(_));
    let mut has_guard: Option<usize> = None;
    for (i, w) in func.body.windows(4).enumerate() {
        let guarded = match w {
            [WI::Call(h), g, _, _] if is_branch(g) => Some(h),
            [WI::Call(h), WI::I64Const(1), WI::I64Eq, g] if is_branch(g) => Some(h),
            _ => None,
        };
        if let Some(h) = guarded
            && func_reaches_host(module, *h, HostModule::Ledger, "has_contract_data", 0)
            && has_guard.replace(i).is_some()
        {
            return None;
        }
    }
    if !has_guard.is_some_and(|h| h < tee_pos) {
        return None;
    }
    // Exactly one TryFromVal tag guard, and it must IMMEDIATELY follow the
    // get-tee: the tee leaves the loaded value on the stack, so adjacency
    // IS the value linkage — the guard provably inspects the get's result,
    // not some unrelated Val (greptile P1 on PR #46).
    let mut tag_guard: Option<(usize, u8)> = None;
    for (i, w) in func.body.windows(5).enumerate() {
        if let [
            WI::I64Const(255),
            WI::I64And,
            WI::I64Const(t),
            WI::I64Ne,
            WI::BrIf(_),
        ] = w
            && (!(64..=77).contains(t) || tag_guard.replace((i, *t as u8)).is_some())
        {
            return None;
        }
    }
    let (guard_pos, tag) = tag_guard?;
    if guard_pos != tee_pos + 1 {
        return None;
    }
    // Unique tee'd-local return, after the tee, with no reassignment
    // between — the returned value IS the get's result.
    let mut ret_pos: Option<usize> = None;
    for (i, w) in func.body.windows(2).enumerate() {
        match w {
            [WI::LocalGet(l), WI::Return] if *l == k => {
                if ret_pos.replace(i + 1).is_some() {
                    return None;
                }
            }
            [_, WI::Return] => return None, // a Return of anything else
            _ => {}
        }
    }
    let ret_pos = ret_pos?;
    if tee_pos >= ret_pos
        || func.body[tee_pos + 1..ret_pos]
            .iter()
            .any(|i| matches!(i, WI::LocalSet(l) | WI::LocalTee(l) if *l == k))
    {
        return None;
    }
    // Exactly one constant-Error fail window, and it must sit AFTER the
    // success return in flat order: under the no-Loop gate, everything
    // past the `return` executes only on paths that did not return — the
    // refusal continuation — so the fail is path-linked to the
    // missing-key/wrong-tag branches, not some unrelated prior path
    // (greptile P1 on PR #46).
    let mut fail: Option<(usize, i64)> = None;
    for (i, w) in func.body.windows(2).enumerate() {
        if let [WI::I64Const(e), WI::Call(f)] = w
            && (*e as u64) & 0xff == TAG_ERROR
            && func_reaches_host(module, *f, HostModule::Context, "fail_with_error", 0)
            && fail.replace((i, *e)).is_some()
        {
            return None;
        }
    }
    let (fail_pos, error_val) = fail?;
    if fail_pos <= ret_pos {
        return None;
    }
    let error = try_decode_val(error_val, registry);
    cov_mark::hit!(fallible_value_getter_detected);
    Some(FallibleValueGetterInfo {
        storage_type,
        key,
        tag,
        error,
        instance_ttl_bumps,
    })
}

/// The empty-collection kind a defaulting collection getter defaults to:
/// its VecObject/MapObject tag, `<mod>.<host>` constructor, and the
/// `CollectionNew` type name codegen renders (issue #34 tranche 7).
#[derive(Clone, Copy)]
struct CollectionKind {
    tag: i64,
    ctor_module: HostModule,
    ctor_name: &'static str,
    type_name: &'static str,
}

const COLLECTION_KINDS: [CollectionKind; 2] = [
    CollectionKind {
        tag: 76, // MapObject
        ctor_module: HostModule::Map,
        ctor_name: "map_new",
        type_name: "Map",
    },
    CollectionKind {
        tag: 75, // VecObject
        ctor_module: HostModule::Vec,
        ctor_name: "vec_new",
        type_name: "Vec",
    },
];

/// Info for a recognized DEFAULTING collection getter (issue #34 tranche 6
/// map / tranche 7 vec, the sibling of [`detect_fallible_value_getter`]).
/// See [`detect_defaulting_collection_getter`].
struct DefaultingCollectionGetterInfo {
    storage_type: StorageType,
    key: SorobanExpr,
    /// The empty-collection type name codegen emits as the `unwrap_or`
    /// default (`"Map"` or `"Vec"`) — proven from the tag guard + ctor.
    collection_type: &'static str,
    instance_ttl_bumps: Vec<(u32, u32)>,
}

/// Recognize a "defaulting collection getter" (issue #34 tranche 6 map /
/// tranche 7 vec): a zero-parameter `() -> i64` helper implementing
/// `env.storage().<dur>().get::<_, C<..>>(&KEY).unwrap_or(C::new(&env))`
/// for a collection `C` ∈ {Map, Vec} — aqua's `RewardGaugesMap` (map) and
/// the DataKey-5 vec reader. The SDK shape:
/// `[bump]; block { flag = has(KEY); if !flag br; v = get(KEY);
/// if tag(v) == C br; unreachable }; select(v, C_new(), flag)`.
/// The empty-collection default is PROVEN, not fabricated: the bytecode
/// unconditionally constructs it as the select's missing arm (`unwrap_or`
/// renders the same eager evaluation; an unobserved `map_new`/`vec_new`
/// has no effect). Every element is bytecode-proven; any deviation → `None`:
/// - internal, zero params, one i64 result, no `Loop`;
/// - chains has + get, never put, no cross-contract call;
/// - proven constant key + storage type + instance TTL bumps (as in the
///   fallible-value sibling);
/// - exactly one tag guard, the INVERTED `[i64.const 255, i64.and,
///   i64.const TAG, i64.eq, br_if]` (success exits; fall-through traps),
///   where TAG is the Map/Vec object tag — the SAME tag whose constructor
///   the select's default arm calls (a MapObject guard with a `vec_new`
///   default, or vice versa, is not this shape);
/// - the body TAIL is exactly `[local.get v, call C_new, local.get c,
///   select]` where `v` is the unique get-tee'd local and `c` the unique
///   has-tee'd local, neither reassigned after its tee, and `C_new` is the
///   host constructor import or a thin wrapper reaching it;
/// - the has flag guards the get, and the tag guard is adjacent to the
///   get-tee (the value-linkage / path-linkage proofs from PR #46).
fn detect_defaulting_collection_getter(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<DefaultingCollectionGetterInfo> {
    use crate::wasm::ir::{WasmInstr as WI, WasmType};
    let ft = module.get_func_type(func_idx)?;
    if !ft.params.is_empty() || ft.results.as_slice() != [WasmType::I64] {
        return None;
    }
    let func = module.get_function(func_idx)?;
    if func.body.iter().any(|i| matches!(i, WI::Loop { .. })) {
        return None;
    }
    let ledger =
        |name: &str| function_calls_host_in_chain(module, func_idx, HostModule::Ledger, name, 3);
    if !ledger("has_contract_data") || !ledger("get_contract_data") || ledger("put_contract_data") {
        return None;
    }
    if function_calls_module_in_chain(module, func_idx, HostModule::Call, 3) {
        return None;
    }
    let instance_ttl_bumps = collect_proven_instance_ttl_bumps(module, func)?;
    let storage_type = detect_storage_type_in_chain(module, func_idx, 3)?;
    let key = load_struct_const_key(module, registry, func)?;
    // Exactly one INVERTED collection-tag guard (success-exit polarity); its
    // tag selects which collection kind (Map/Vec) this getter defaults to.
    let mut guard_tag: Option<i64> = None;
    for w in func.body.windows(5) {
        if let [
            WI::I64Const(255),
            WI::I64And,
            WI::I64Const(t),
            _,
            WI::BrIf(_),
        ] = w
        {
            if !matches!(w[3], WI::I64Eq) || !COLLECTION_KINDS.iter().any(|k| k.tag == *t) {
                return None; // any other guard shape → not this class
            }
            if guard_tag.replace(*t).is_some() {
                return None;
            }
        }
    }
    let guard_tag = guard_tag?;
    let kind = COLLECTION_KINDS.iter().find(|k| k.tag == guard_tag)?;
    // Unique get-tee and has-tee locals.
    let mut get_tee: Option<(usize, u32)> = None;
    let mut has_tee: Option<(usize, u32)> = None;
    for (i, w) in func.body.windows(2).enumerate() {
        if let [WI::Call(g), WI::LocalTee(k)] = w {
            if func_reaches_host(module, *g, HostModule::Ledger, "get_contract_data", 0) {
                if get_tee.replace((i + 1, *k)).is_some() {
                    return None;
                }
            } else if func_reaches_host(module, *g, HostModule::Ledger, "has_contract_data", 0)
                && has_tee.replace((i + 1, *k)).is_some()
            {
                return None;
            }
        }
    }
    let (get_pos, v) = get_tee?;
    let (has_pos, c) = has_tee?;
    if v == c {
        return None;
    }
    // The has flag GUARDS the get: the has-tee must feed `[i32.eqz,
    // br_if]` directly (the tee leaves the flag on the stack), and the get
    // must come after — so the missing-key path provably branches around
    // the get before it could trap (greptile P1 on PR #46).
    if !matches!(
        (func.body.get(has_pos + 1), func.body.get(has_pos + 2)),
        (Some(WI::I32Eqz), Some(WI::BrIf(_)))
    ) || has_pos >= get_pos
    {
        return None;
    }
    // The tag guard inspects the GET's value: it must immediately follow
    // the get-tee, consuming the teed value left on the stack (greptile
    // P1 on PR #46 — adjacency IS the value linkage). Its tag is the
    // collection kind's.
    if !matches!(
        func.body.get(get_pos + 1..get_pos + 6),
        Some([
            WI::I64Const(255),
            WI::I64And,
            WI::I64Const(t),
            WI::I64Eq,
            WI::BrIf(_)
        ]) if *t == kind.tag
    ) {
        return None;
    }
    // The tail select consumes exactly (v, C_new(), c) — and `C_new` must
    // be the constructor for the SAME kind the tag guard proved.
    let is_kind_ctor = |t: u32| {
        module.imports.get_by_index(t).map_or_else(
            || {
                module.get_function(t).is_some_and(|f| {
                    f.body.len() <= 4
                        && f.body.iter().any(|i| {
                            matches!(i, WI::Call(m)
                            if module.imports.get_by_index(*m).is_some_and(|hf|
                                hf.module == kind.ctor_module && hf.name == kind.ctor_name))
                        })
                })
            },
            |hf| hf.module == kind.ctor_module && hf.name == kind.ctor_name,
        )
    };
    let tail_ok = matches!(func.body.as_slice(),
        [.., WI::LocalGet(a), WI::Call(mn), WI::LocalGet(b), WI::Select]
        | [.., WI::LocalGet(a), WI::Call(mn), WI::LocalGet(b), WI::Select, WI::End]
            if *a == v && *b == c && is_kind_ctor(*mn));
    if !tail_ok {
        return None;
    }
    // Neither local is reassigned after its tee (flat order = execution
    // order under the no-Loop gate).
    let reassigned = |k: u32, after: usize| {
        func.body[after + 1..]
            .iter()
            .any(|i| matches!(i, WI::LocalSet(l) | WI::LocalTee(l) if *l == k))
    };
    if reassigned(v, get_pos) || reassigned(c, has_pos) {
        return None;
    }
    cov_mark::hit!(defaulting_collection_getter_detected);
    Some(DefaultingCollectionGetterInfo {
        storage_type,
        key,
        collection_type: kind.type_name,
        instance_ttl_bumps,
    })
}

/// Info for a recognized fallible STRUCT getter (issue #34 tranche 4). See
/// [`detect_fallible_struct_getter`].
///
/// Consumed by the early-recognizer arm in the `Call` handler (issue #34
/// tranche 5): the arm reconstructs the getter at its call site — proven
/// TTL bumps, then a `let` binding of the defaulting get, then out-slot
/// seeds referencing the binding's fields — and skips inlining entirely,
/// so the collapse heuristics see one coherent statement stream and no
/// husk ever exists to race the seeds (the two hybrid designs measured
/// and rejected in PR #44).
struct FallibleStructGetterInfo {
    storage_type: StorageType,
    key: SorobanExpr,
    type_name: String,
    /// The struct's u128 field (decoded to out slots `[0, 8]`) and u64 field
    /// (out slot `16`) — the rustc layout for a `{u128, u64}` struct.
    u128_field: String,
    u64_field: String,
    /// Spec-declared field order, for rendering the zero-default construct.
    spec_fields: Vec<(String, ScSpecTypeDef)>,
    /// Proven instance TTL bumps `(threshold, extend_to)`, in body order —
    /// the SDK's `bump_instance`-style prologue. Every TTL-family
    /// reachability in the helper is either proven into this list or the
    /// whole recognition is refused ([`collect_proven_instance_ttl_bumps`]),
    /// so reconstructing exactly these statements never drops a bump.
    instance_ttl_bumps: Vec<(u32, u32)>,
}

/// Recognize a "fallible struct getter" (issue #34 tranche 4): a void
/// `(i32 out)` helper implementing
/// `env.storage().<dur>().get::<_, T>(&KEY).unwrap_or(T { .. zeros })` for a
/// TWO-field struct `T { u128, u64 }` — the aqua `PoolRewardConfig` /
/// `PoolRewardData` class rooting the reward-math chains. The SDK shape:
/// `if !has(KEY) { out = zeros } else { get(KEY) → MapObject tag check →
/// map_unpack(LM field names) → per-field TryFromVal decodes → out }`.
///
/// Every element is bytecode-proven; any deviation → `None` → today's
/// output byte-identical:
/// - void, exactly one I32 param (the out-pointer);
/// - chains `has_contract_data` AND `get_contract_data`, never
///   `put_contract_data`, and no cross-contract call — so the appended
///   re-get at the call site observes the same storage state;
/// - unpacks via `map_unpack_to_linear_memory` (import or thunk) with an LM
///   field-name descriptor matching a registry struct of EXACTLY two fields,
///   one `u128` + one `u64` (the only layout this recovers: rustc places the
///   u128 at `[0, 8]` and the u64 at `16`, confirmed by the out stores);
/// - calls EXACTLY one `U128`-class and one `U64`-class TryFromVal decode
///   helper ([`detect_tryfromval_decode_helper`]), each once — the
///   class↔field linking is therefore unique, no instruction tracing needed;
/// - the zero-default window `[i64.const 0, local.set, i64.const 0, br]`
///   (the missing-key path zeroing both u128 limbs; the u64 default is the
///   zero-initialized local);
/// - out stores at offsets 0, 8 AND 16 present;
/// - the storage key is a proven constant ([`load_struct_const_key`]);
/// - every TTL-extension reachability is a proven constant instance bump
///   ([`collect_proven_instance_ttl_bumps`]).
fn detect_fallible_struct_getter(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<FallibleStructGetterInfo> {
    use crate::wasm::ir::{WasmInstr, WasmType};
    let func_type = module.get_func_type(func_idx)?;
    if !func_type.results.is_empty() || func_type.params.as_slice() != [WasmType::I32] {
        return None;
    }
    let ledger =
        |name: &str| function_calls_host_in_chain(module, func_idx, HostModule::Ledger, name, 3);
    if !ledger("has_contract_data") || !ledger("get_contract_data") || ledger("put_contract_data") {
        return None;
    }
    if function_calls_module_in_chain(module, func_idx, HostModule::Call, 3) {
        return None;
    }
    let func = module.get_function(func_idx)?;
    // Unpacks the loaded map (directly or through the SDK's marshalling thunk).
    let has_map_unpack = func.body.iter().any(|i| {
        matches!(i, WasmInstr::Call(t)
            if module.imports.get_by_index(*t).map_or_else(
                || detect_map_unpack_thunk(module, *t),
                |hf| hf.module == HostModule::Map && hf.name == "map_unpack_to_linear_memory"))
    });
    if !has_map_unpack {
        return None;
    }
    // The LM field-name descriptor: an I32Const pointer whose string-slice
    // array of length 2 names a registry struct.
    let mut found: Option<(String, Vec<String>)> = None;
    for instr in &func.body {
        let WasmInstr::I32Const(ptr) = instr else {
            continue;
        };
        if *ptr <= 1024 {
            continue;
        }
        if let Some(names) = module.data_sections.read_string_slice_array(*ptr as u32, 2)
            && names.len() == 2
            && let Some(tn) = find_type_by_field_names(registry, &names, None)
        {
            if found.as_ref().is_some_and(|(t, _)| *t != tn) {
                return None; // two different struct descriptors → ambiguous
            }
            found = Some((tn, names));
        }
    }
    let (type_name, _names) = found?;
    let spec = registry.structs.get(&type_name)?;
    let spec_fields: Vec<(String, ScSpecTypeDef)> = spec
        .fields
        .iter()
        .filter_map(|f| Some((f.name.to_utf8_string().ok()?, f.type_.clone())))
        .collect();
    if spec_fields.len() != 2 {
        return None;
    }
    let u128_field = spec_fields
        .iter()
        .find(|(_, t)| matches!(t, ScSpecTypeDef::U128))?
        .0
        .clone();
    let u64_field = spec_fields
        .iter()
        .find(|(_, t)| matches!(t, ScSpecTypeDef::U64))?
        .0
        .clone();
    // Exactly one decode helper per width class, each called exactly once —
    // the class↔field link is unique.
    let mut u128_calls = 0usize;
    let mut u64_calls = 0usize;
    for instr in &func.body {
        if let WasmInstr::Call(t) = instr
            && module.imports.get_by_index(*t).is_none()
        {
            match detect_tryfromval_decode_helper(module, *t) {
                Some(DecodeHelperClass::U128) => u128_calls += 1,
                Some(DecodeHelperClass::U64) => u64_calls += 1,
                Some(DecodeHelperClass::I128) => return None,
                None => {}
            }
        }
    }
    if u128_calls != 1 || u64_calls != 1 {
        return None;
    }
    // The missing-key path zeroes both u128 limbs and exits.
    let has_zero_default = func.body.windows(4).any(|w| {
        matches!(
            w,
            [
                WasmInstr::I64Const(0),
                WasmInstr::LocalSet(_),
                WasmInstr::I64Const(0),
                WasmInstr::Br(_)
            ]
        )
    });
    if !has_zero_default {
        return None;
    }
    // All three out slots are written.
    let has_store = |off: u32| {
        func.body
            .iter()
            .any(|i| matches!(i, WasmInstr::I64Store(o) if *o == off))
    };
    if !has_store(0) || !has_store(8) || !has_store(16) {
        return None;
    }
    let storage_type = detect_storage_type_in_chain(module, func_idx, 3)?;
    let key = load_struct_const_key(module, registry, func)?;
    let instance_ttl_bumps = collect_proven_instance_ttl_bumps(module, func)?;
    cov_mark::hit!(fallible_struct_getter_detected);
    Some(FallibleStructGetterInfo {
        storage_type,
        key,
        type_name,
        u128_field,
        u64_field,
        spec_fields,
        instance_ttl_bumps,
    })
}

/// The ledger TTL-extension host family. Reconstructing a getter without its
/// TTL bumps would silently change ledger rent behavior (the issue-#33
/// lesson: never drop a side effect the bytecode proves), so any
/// reachability of these that [`collect_proven_instance_ttl_bumps`] cannot
/// prove as a constant instance bump refuses the whole recognition.
const TTL_EXTEND_FAMILY: [&str; 5] = [
    "extend_contract_data_ttl",
    "extend_current_contract_instance_and_code_ttl",
    "extend_contract_instance_and_code_ttl",
    "extend_contract_instance_ttl",
    "extend_contract_code_ttl",
];

/// Prove every TTL-extension side effect of `func` as a constant *instance*
/// bump, returning the `(threshold, extend_to)` pairs in body order — or
/// `None` if any TTL-family call cannot be proven (a keyed
/// `extend_contract_data_ttl`, non-constant thresholds, a bump buried in an
/// unproven callee).
///
/// Two proven shapes, both requiring TAG_U32-encoded `i64.const` operands
/// (decoded as `value >> 32`):
/// - a direct `[i64.const T, i64.const E, call $l8]` window on
///   `extend_current_contract_instance_and_code_ttl`;
/// - a call to a thin constant wrapper: a `() -> ()` function whose whole
///   body is that window plus `drop` (the SDK's `bump_instance` shape —
///   aqua's func 77).
///
/// Any OTHER route to the family — a different family import called directly, or
/// an internal callee whose depth-3 chain reaches any family name without
/// being the thin wrapper — returns `None`.
///
/// POSITION is proven, not just operands: a proven bump must sit in the
/// body's straight-line PREFIX (before the first control-flow instruction),
/// which dominates every path — so hoisting it to an unconditional
/// statement preserves semantics exactly. A bump inside or after any
/// branch (e.g. only on the key-present arm) refuses the whole recognition:
/// reconstructing it unconditionally would bump the TTL on paths that never
/// did (greptile P1 on PR #45).
fn collect_proven_instance_ttl_bumps(
    module: &WasmModule,
    func: &crate::wasm::ir::WasmFunction,
) -> Option<Vec<(u32, u32)>> {
    use crate::wasm::ir::WasmInstr as WI;
    // Index of the first control-flow instruction: calls at or past it are
    // no longer dominated by function entry as straight-line code.
    let first_control_flow = func
        .body
        .iter()
        .position(|i| {
            matches!(
                i,
                WI::Block { .. }
                    | WI::Loop { .. }
                    | WI::If { .. }
                    | WI::Else
                    | WI::Br(_)
                    | WI::BrIf(_)
                    | WI::BrTable { .. }
                    | WI::Return
                    | WI::Unreachable
                    | WI::CallIndirect(_)
            )
        })
        .unwrap_or(func.body.len());
    let decode_u32_val = |v: i64| {
        let v = v as u64;
        ((v & 0xff) == TAG_U32).then_some((v >> 32) as u32)
    };
    let is_instance_bump = |hf: &crate::wasm::imports::HostFunction| {
        hf.module == HostModule::Ledger
            && hf.name == "extend_current_contract_instance_and_code_ttl"
    };
    // A thin constant wrapper: `() -> ()`, body exactly the const window +
    // the dropped result (function bodies end with the bare `End`).
    let as_thin_const_wrapper = |t: u32| -> Option<(u32, u32)> {
        let ft = module.get_func_type(t)?;
        if !ft.params.is_empty() || !ft.results.is_empty() {
            return None;
        }
        match module.get_function(t)?.body.as_slice() {
            [WI::I64Const(a), WI::I64Const(b), WI::Call(imp), WI::Drop]
            | [
                WI::I64Const(a),
                WI::I64Const(b),
                WI::Call(imp),
                WI::Drop,
                WI::End,
            ] if module
                .imports
                .get_by_index(*imp)
                .is_some_and(is_instance_bump) =>
            {
                Some((decode_u32_val(*a)?, decode_u32_val(*b)?))
            }
            _ => None,
        }
    };
    let mut bumps = Vec::new();
    for (i, instr) in func.body.iter().enumerate() {
        let WI::Call(t) = instr else { continue };
        if let Some(hf) = module.imports.get_by_index(*t) {
            if is_instance_bump(hf) {
                // Direct call: both operands must be constant TAG_U32 Vals,
                // and the call must dominate (straight-line prefix).
                if i >= first_control_flow {
                    return None;
                }
                let window = (i >= 2).then(|| (&func.body[i - 2], &func.body[i - 1]));
                let Some((WI::I64Const(a), WI::I64Const(b))) = window else {
                    return None;
                };
                bumps.push((decode_u32_val(*a)?, decode_u32_val(*b)?));
            } else if hf.module == HostModule::Ledger
                && TTL_EXTEND_FAMILY.contains(&hf.name.as_str())
            {
                return None;
            }
        } else if let Some(bump) = as_thin_const_wrapper(*t) {
            if i >= first_control_flow {
                return None;
            }
            bumps.push(bump);
        } else if TTL_EXTEND_FAMILY
            .iter()
            .any(|n| function_calls_host_in_chain(module, *t, HostModule::Ledger, n, 3))
        {
            return None;
        }
    }
    Some(bumps)
}

/// Recognize a "defaulting u128 storage getter" (issue #34 tranche 2): a void
/// helper taking only an I32 out-pointer that reads storage fallibly and
/// writes the decoded u128 as `[lo@0, hi@8]`, yielding 0 for BOTH limbs when
/// the key is missing — the SDK lowering of
/// `env.storage().<dur>().get::<_, u128>(&key).unwrap_or(0)` (an accumulator
/// read: aqua's `TotalAccumulatedReward` et al.). Proven from bytecode:
/// - void, exactly one I32 param (the out-pointer);
/// - chains BOTH `has_contract_data` and `get_contract_data`, never
///   `put_contract_data`, and makes no cross-contract call;
/// - decodes u128 and ONLY u128, IN ITS OWN BODY (direct `obj_to_u128_hi64`
///   and `obj_to_u128_lo64` calls; no u64/i64/i128 decode anywhere in the
///   chain) — the decode belongs to this function's flow, not a nested
///   callee's (greptile P1 on PR #42);
/// - pushes the literal-0 default as the first value of an I64-valued block
///   (the `[Block(result i64), I64Const(0)]` window) — the missing-key lo
///   limb (the hi limb's default is the zero-initialized local);
/// - writes EXACTLY the two out slots and nothing else: the body's
///   `i64.store` offsets are exactly `{0, 8}` and it has no `i32.store`
///   (an extra store would mean a layout this detector does not prove).
///
/// Any deviation → `false` → the caller leaves today's output byte-identical.
fn detect_defaulting_u128_getter(module: &WasmModule, func_idx: u32) -> bool {
    use crate::wasm::ir::{BlockType, WasmInstr, WasmType};
    let Some(func_type) = module.get_func_type(func_idx) else {
        return false;
    };
    if !func_type.results.is_empty() || func_type.params.as_slice() != [WasmType::I32] {
        return false;
    }
    let ledger =
        |name: &str| function_calls_host_in_chain(module, func_idx, HostModule::Ledger, name, 3);
    if !ledger("get_contract_data") || !ledger("has_contract_data") || ledger("put_contract_data") {
        return false;
    }
    if function_calls_module_in_chain(module, func_idx, HostModule::Call, 3) {
        return false;
    }
    let Some(func) = module.get_function(func_idx) else {
        return false;
    };
    // The u128 decode must be in THIS function's own flow (direct import
    // calls), and its exclusions chain-wide (broader is safer).
    let direct_int = |name: &str| {
        func.body.iter().any(|i| {
            matches!(i, WasmInstr::Call(t)
                if module.imports.get_by_index(*t).is_some_and(
                    |hf| hf.module == HostModule::Int && hf.name == name))
        })
    };
    if !direct_int("obj_to_u128_hi64") || !direct_or_chain_excludes(module, func_idx, direct_int) {
        return false;
    }
    let has_default_block = func.body.windows(2).any(|w| {
        matches!(
            w,
            [
                WasmInstr::Block {
                    block_type: BlockType::Value(WasmType::I64)
                },
                WasmInstr::I64Const(0)
            ]
        )
    });
    // The body writes EXACTLY the `[lo@0, hi@8]` layout and nothing else.
    let stores_exact = i64_store_offsets(func).is_some_and(|offs| offs == [0, 8]);
    has_default_block && stores_exact
}

/// Second half of the defaulting-getter decode gate, split for readability:
/// the lo-limb decode is also direct, and no other-width decode exists
/// anywhere in the chain.
fn direct_or_chain_excludes(
    module: &WasmModule,
    func_idx: u32,
    direct_int: impl Fn(&str) -> bool,
) -> bool {
    let chain =
        |name: &str| function_calls_host_in_chain(module, func_idx, HostModule::Int, name, 3);
    direct_int("obj_to_u128_lo64")
        && !chain("obj_to_u64")
        && !chain("obj_to_i64")
        && !chain("obj_to_i128_hi64")
        && !chain("obj_to_i128_lo64")
}

/// True if `func_idx` (transitively, depth ≤ 3) reaches a helper that performs
/// real integer arithmetic — `mul`+`div`, or repeated `mul` — i.e. the gas math
/// of a "computed" getter, as opposed to a plain `get → re-encode` direct getter.
/// `shl` (Val tagging) does not count.
fn function_calls_math_helper(module: &WasmModule, func_idx: u32, depth: u32) -> bool {
    use crate::wasm::ir::WasmInstr;
    if depth == 0 {
        return false;
    }
    let Some(func) = module.get_function(func_idx) else {
        return false;
    };
    let muls = func
        .body
        .iter()
        .filter(|i| matches!(i, WasmInstr::I64Mul))
        .count();
    let divs = func
        .body
        .iter()
        .filter(|i| matches!(i, WasmInstr::I64DivU | WasmInstr::I64DivS))
        .count();
    if (divs >= 1 && muls >= 1) || muls >= 2 {
        return true;
    }
    for instr in &func.body {
        if let WasmInstr::Call(target) = instr
            && module.imports.get_by_index(*target).is_none()
            && function_calls_math_helper(module, *target, depth - 1)
        {
            return true;
        }
    }
    false
}

fn detect_storage_type_in_chain(
    module: &WasmModule,
    func_idx: u32,
    depth: u32,
) -> Option<StorageType> {
    if depth == 0 {
        return None;
    }

    let func = module.get_function(func_idx)?;

    // Check direct host calls in this function
    if let Some(st) = detect_storage_type_in_body(module, &func.body) {
        return Some(st);
    }

    // Also check put_contract_data (not just get/has)
    for (i, instr) in func.body.iter().enumerate() {
        if let crate::wasm::ir::WasmInstr::Call(target) = instr {
            if let Some(host_fn) = module.imports.get_by_index(*target) {
                if host_fn.module == HostModule::Ledger && host_fn.name == "put_contract_data" {
                    for j in (0..i).rev().take(10) {
                        if let crate::wasm::ir::WasmInstr::I64Const(v) = &func.body[j] {
                            return match *v {
                                0 => Some(StorageType::Temporary),
                                1 => Some(StorageType::Persistent),
                                2 => Some(StorageType::Instance),
                                _ => continue,
                            };
                        }
                    }
                }
            } else if depth > 1 {
                // Recurse into internal calls
                if let Some(st) = detect_storage_type_in_chain(module, *target, depth - 1) {
                    return Some(st);
                }
            }
        }
    }
    None
}

/// Info returned by `detect_enum_dispatch_wrapper`.
struct EnumDispatchWrapperInfo {
    union_name: String,
    /// Variant names in br_table index order.
    variants: Vec<String>,
    /// Whether each variant carries data (TupleV0 vs VoidV0).
    has_data: Vec<bool>,
}

/// Detect if a function is an enum variant construction dispatch that uses
/// `br_table` to select a variant by index, creates a symbol for the variant
/// name, and builds a 2-element vec [symbol, data] via `vec_new_from_linear_memory`.
///
/// Pattern (e.g., func 13 in constructor): `(i32 variant_index, i32 data) -> i64`
/// - `br_table` dispatches on first param
/// - Each branch loads a data-section string pointer + length (variant name)
/// - Calls symbol_new and vec_new to build the variant representation
///
/// Returns variant info so the caller can build `EnumConstruct` directly.
fn detect_enum_dispatch_wrapper(
    module: &WasmModule,
    registry: &TypeRegistry,
    func_idx: u32,
) -> Option<EnumDispatchWrapperInfo> {
    use crate::wasm::ir::WasmInstr;

    let func = module.get_function(func_idx)?;

    // Must have a br_table
    let mut has_br_table = false;
    for instr in &func.body {
        if matches!(instr, WasmInstr::BrTable { .. }) {
            has_br_table = true;
            break;
        }
    }
    if !has_br_table {
        return None;
    }

    // Collect (ptr, len) pairs: consecutive I32Const where ptr > 1024 and len < 256.
    // These are the variant name string pointers passed to symbol_new_from_linear_memory.
    let mut string_refs: Vec<(u32, u32)> = Vec::new();
    let i32_consts: Vec<i32> = func
        .body
        .iter()
        .filter_map(|instr| match instr {
            WasmInstr::I32Const(v) => Some(*v),
            _ => None,
        })
        .collect();

    // Walk consecutive I32Const pairs looking for (ptr > 1024, len < 256) patterns.
    let mut i = 0;
    while i + 1 < i32_consts.len() {
        let ptr = i32_consts[i] as u32;
        let len = i32_consts[i + 1] as u32;
        if ptr > 1024 && len > 0 && len < 256 {
            // Verify we can actually read a string at this location
            if module.data_sections.read_string(ptr, len).is_some() {
                string_refs.push((ptr, len));
                i += 2;
                continue;
            }
        }
        i += 1;
    }

    if string_refs.is_empty() {
        return None;
    }

    // Read variant names from data section
    let variant_names: Vec<String> = string_refs
        .iter()
        .filter_map(|(ptr, len)| module.data_sections.read_string(*ptr, *len))
        .collect();

    if variant_names.len() != string_refs.len() {
        return None;
    }

    // Deduplicate (default br_table target may repeat a variant)
    let mut unique_names: Vec<String> = Vec::new();
    for name in &variant_names {
        if !unique_names.contains(name) {
            unique_names.push(name.clone());
        }
    }

    // Match against union variants in registry
    if let Some((union_name, has_data)) = registry.find_union_by_variants(&unique_names) {
        cov_mark::hit!(detect_enum_dispatch_wrapper_hit);
        Some(EnumDispatchWrapperInfo {
            union_name,
            variants: unique_names,
            has_data,
        })
    } else {
        None
    }
}

/// Detect a register-rotation copy loop pattern in a structured loop body.
///
/// The SDK generates 2-iteration copy loops to move a value from one WASM local
/// to another via a temporary. Pattern:
/// ```text
/// loop:
///   local.get CURRENT → local.set TARGET    ; rotate: target = old current
///   ... counter decrement logic ...
///   local.get SOURCE  → local.set CURRENT   ; current = source value
///   ... condition check ...
///   br_if 0                                  ; loop back (only first iteration)
/// ```
/// After the loop exits (second iteration), TARGET contains SOURCE's pre-loop value.
/// Returns `Some((target_idx, source_idx))` if the pattern matches.
fn detect_register_rotation(body: &[super::structurize::StructuredBlock]) -> Option<(u32, u32)> {
    use super::structurize::StructuredBlock;
    use crate::wasm::ir::WasmInstr;

    // Flatten the loop body instructions
    let instrs: Vec<&WasmInstr> = body
        .iter()
        .filter_map(|b| match b {
            StructuredBlock::Instruction(i) => Some(i),
            _ => None,
        })
        .collect();

    // Need at least: LocalGet, LocalSet, ..., LocalGet, LocalSet, ..., BrIf
    if instrs.len() < 5 {
        return None;
    }

    // Must end with BrIf(0) (loop back)
    if !matches!(instrs.last(), Some(WasmInstr::BrIf(0))) {
        return None;
    }

    // First two instructions must be LocalGet(CURRENT), LocalSet(TARGET)
    let current = match instrs[0] {
        WasmInstr::LocalGet(idx) => *idx,
        _ => return None,
    };
    let target = match instrs[1] {
        WasmInstr::LocalSet(idx) if *idx != current => *idx,
        _ => return None,
    };

    // Find the last LocalGet → LocalSet pair before BrIf that writes to CURRENT.
    // Scan backwards from the BrIf (skip last = BrIf, second-to-last = LocalGet for condition).
    let mut source = None;
    for i in (0..instrs.len().saturating_sub(2)).rev() {
        if let WasmInstr::LocalSet(set_idx) = instrs[i]
            && *set_idx == current
        {
            // The instruction before this LocalSet should be LocalGet(SOURCE)
            if i > 0
                && let WasmInstr::LocalGet(get_idx) = instrs[i - 1]
            {
                source = Some(*get_idx);
            }
            break;
        }
    }

    let source = source?;

    // Guard: source must be different from target and current
    if source == target || source == current {
        return None;
    }

    cov_mark::hit!(detect_register_rotation_hit);
    Some((target, source))
}

/// Recursively flatten a structured block tree into a flat list of the
/// instructions it contains, in execution order. Shared by the loop
/// recognizers (`detect_memory_copy_loop`, `detect_counted_loop`) and the
/// loop-carried dataflow analysis.
fn collect_instrs<'a>(
    blocks: &'a [super::structurize::StructuredBlock],
    out: &mut Vec<&'a crate::wasm::ir::WasmInstr>,
) {
    use super::structurize::StructuredBlock;
    for b in blocks {
        match b {
            StructuredBlock::Instruction(i) => out.push(i),
            StructuredBlock::Block { body, .. } => collect_instrs(body, out),
            StructuredBlock::Loop { body, .. } => collect_instrs(body, out),
            StructuredBlock::IfElse {
                then_body,
                else_body,
                ..
            } => {
                collect_instrs(then_body, out);
                collect_instrs(else_body, out);
            }
            // Safety-net `unreachable` is dead by construction; nothing for
            // the loop / memory-copy / counted-loop recognizers to consume.
            StructuredBlock::SafetyNetUnreachable => {}
        }
    }
}

/// Information about a detected memory copy loop.
struct MemoryCopyLoopInfo {
    src_base: i32,
    dest_base: i32,
    limit: u32,
    step: u32,
}

/// Detect a memory copy loop pattern in a structured loop body.
///
/// Pattern:
/// ```text
/// loop:
///   local.get COUNTER; i32.const LIMIT; i32.eq; br_if N  ; break if done
///   <load from FrameSlot(id, src_base + counter)>
///   <store to FrameSlot(id, dest_base + counter)>
///   local.get COUNTER; i32.const STEP; i32.add; local.set COUNTER
///   br 0
/// ```
///
/// The lifter simulates iteration 0 (counter=0). This function extracts the
/// loop parameters so the caller can extend frame_slots for remaining iterations.
///
/// Requires the loop to have already been lifted (so frame_slots from iteration 0
/// are populated). Uses those to determine frame_id, src_base, and dest_base.
fn detect_memory_copy_loop(
    body: &[super::structurize::StructuredBlock],
) -> Option<MemoryCopyLoopInfo> {
    use crate::wasm::ir::WasmInstr;

    // The loop body should be a Block (break target) containing either
    // a sequence of instructions or nested blocks. Flatten to find key instructions.
    let mut all_instrs = Vec::new();
    collect_instrs(body, &mut all_instrs);

    // Need: I64Load + I64Store pair, counter increment pattern
    if all_instrs.len() < 8 {
        return None;
    }

    // Find the limit: look for `local.get COUNTER; i32.const LIMIT; i32.eq`.
    // The consumer iterates `(step..limit).step_by(step)` over the recovered
    // limit; an unbounded limit from crafted WASM (up to u32::MAX) would let
    // an attacker drive the lifter into a multi-million-iteration HashMap
    // loop. Real Rust struct copies don't exceed a few hundred bytes, so cap
    // at 1024 — anything larger is either pathological or out of scope for
    // this recognizer.
    const MAX_MEMORY_COPY_BYTES: u32 = 1024;
    let mut counter_local = None;
    let mut limit = None;
    for w in all_instrs.windows(3) {
        if let (WasmInstr::LocalGet(cnt), WasmInstr::I32Const(lim), WasmInstr::I32Eq) =
            (w[0], w[1], w[2])
        {
            counter_local = Some(*cnt);
            limit = Some((*lim as u32).min(MAX_MEMORY_COPY_BYTES));
            break;
        }
    }
    let counter_local = counter_local?;
    let limit = limit?;

    // Find the step: `local.get COUNTER; i32.const STEP; i32.add; local.set COUNTER`
    let mut step = None;
    for w in all_instrs.windows(4) {
        if let (
            WasmInstr::LocalGet(cnt),
            WasmInstr::I32Const(s),
            WasmInstr::I32Add,
            WasmInstr::LocalSet(cnt2),
        ) = (w[0], w[1], w[2], w[3])
            && *cnt == counter_local
            && *cnt2 == counter_local
            && *s > 0
        {
            step = Some(*s as u32);
            break;
        }
    }
    let step = step?;

    // Verify there's an I64Load and I64Store pair (the actual copy)
    let has_load = all_instrs
        .iter()
        .any(|i| matches!(i, WasmInstr::I64Load(_)));
    let has_store = all_instrs
        .iter()
        .any(|i| matches!(i, WasmInstr::I64Store(_)));
    if !has_load || !has_store {
        return None;
    }

    // Determine frame_id, src_base, dest_base from the I64Store's frame_slot
    // entries that iteration 0 already created. The loop copied from
    // FrameSlot(id, src_base + 0) to FrameSlot(id, dest_base + 0).
    // We detect this by finding `local.get BASE; i32.const OFFSET; i32.add`
    // patterns before the I64Load and I64Store.
    //
    // Simpler approach: look for two distinct I32Const values used with the
    // base local in I32Add — the smaller one is src_base_add, larger is dest_base_add.
    // The actual base offsets include the base local's FrameSlot offset.
    let mut base_local = None;
    let mut add_constants: Vec<i32> = Vec::new();

    // Find the local used as the frame base (it should be used with I32Add + I32Const)
    for w in all_instrs.windows(3) {
        if let (WasmInstr::LocalGet(loc), WasmInstr::I32Const(c), WasmInstr::I32Add) =
            (w[0], w[1], w[2])
            && *loc != counter_local
        {
            base_local = Some(*loc);
            if !add_constants.contains(c) {
                add_constants.push(*c);
            }
        }
    }

    // Also check for bare `local.get BASE; local.get COUNTER; i32.add`
    // (src with no additional offset → src_base_add = 0)
    for w in all_instrs.windows(3) {
        if let (WasmInstr::LocalGet(loc), WasmInstr::LocalGet(cnt), WasmInstr::I32Add) =
            (w[0], w[1], w[2])
            && *cnt == counter_local
            && Some(*loc) == base_local
            && !add_constants.contains(&0)
        {
            add_constants.push(0);
        }
    }

    let _base_local = base_local?;
    if add_constants.len() < 2 {
        return None;
    }

    add_constants.sort();
    let src_add = add_constants[0];
    let dest_add = add_constants[1];

    // We don't know the frame_id or the base local's FrameSlot offset here
    // (that's runtime state). But we know the RELATIVE offsets: dest is at
    // base+dest_add and src is at base+src_add. The absolute offsets are
    // base_slot_offset + add_constant.
    //
    // Since we need the frame_id, we'll use a sentinel approach: return
    // frame_id=u32::MAX and let the caller resolve it from frame_slots
    // by looking for an entry that was created during iteration 0.
    // The caller knows that iteration 0 copied src_base+0 → dest_base+0.
    //
    // Actually, simpler: return the relative difference and let the caller
    // search frame_slots for any entry at offset dest_add that was recently
    // created (from iteration 0's I64Store).

    Some(MemoryCopyLoopInfo {
        src_base: src_add,
        dest_base: dest_add,
        limit,
        step,
    })
}

/// A loop recognized as counted: a single induction variable stepped by a
/// constant and compared against a constant bound to decide the exit.
struct CountedLoopInfo {
    #[allow(dead_code)]
    counter_local: u32,
    #[allow(dead_code)]
    step: i64,
    #[allow(dead_code)]
    bound: i64,
}

/// Recognize a counted loop: a body containing both a counter step
/// `local.get C; (i32|i64).const S; (i32|i64).add; local.set C` (S != 0) and an
/// exit test against a constant `local.get C; (i32|i64).const N; (i32|i64).(eq|ne)`
/// on the same counter `C`. This is the gate for loop-carried value recovery —
/// it positively identifies the bounded-iteration shape (`for i in ..` /
/// `while i != N`) and leaves every other loop (memory copies, host-call-driven
/// iteration, SDK limb arithmetic) on the existing single-pass path untouched.
fn detect_counted_loop(body: &[super::structurize::StructuredBlock]) -> Option<CountedLoopInfo> {
    use crate::wasm::ir::WasmInstr;

    let mut all_instrs = Vec::new();
    collect_instrs(body, &mut all_instrs);

    // Step: `local.get C; const S; (add|sub); local.set C` (same C, S != 0).
    // A `sub` is a descending counter, recorded as a negative step.
    let mut counter_step: Option<(u32, i64)> = None;
    for w in all_instrs.windows(4) {
        let (cnt, s) = match (w[0], w[1], w[2], w[3]) {
            (
                WasmInstr::LocalGet(c),
                WasmInstr::I32Const(s),
                WasmInstr::I32Add,
                WasmInstr::LocalSet(c2),
            ) if c == c2 => (*c, *s as i64),
            (
                WasmInstr::LocalGet(c),
                WasmInstr::I64Const(s),
                WasmInstr::I64Add,
                WasmInstr::LocalSet(c2),
            ) if c == c2 => (*c, *s),
            (
                WasmInstr::LocalGet(c),
                WasmInstr::I32Const(s),
                WasmInstr::I32Sub,
                WasmInstr::LocalSet(c2),
            ) if c == c2 => (*c, -(*s as i64)),
            (
                WasmInstr::LocalGet(c),
                WasmInstr::I64Const(s),
                WasmInstr::I64Sub,
                WasmInstr::LocalSet(c2),
                // `-i64::MIN` overflows; such a pathological step isn't a real
                // counter, so skip it rather than panic.
            ) if c == c2 => match s.checked_neg() {
                Some(neg) => (*c, neg),
                None => continue,
            },
            _ => continue,
        };
        if s != 0 {
            counter_step = Some((cnt, s));
            break;
        }
    }
    let (counter_local, step) = counter_step?;

    // Exit test: `local.get C; const N; (eq|ne)` on the same counter.
    let mut bound: Option<i64> = None;
    for w in all_instrs.windows(3) {
        let (c, n) = match (w[0], w[1], w[2]) {
            (
                WasmInstr::LocalGet(c),
                WasmInstr::I32Const(n),
                WasmInstr::I32Eq | WasmInstr::I32Ne,
            ) => (*c, *n as i64),
            (
                WasmInstr::LocalGet(c),
                WasmInstr::I64Const(n),
                WasmInstr::I64Eq | WasmInstr::I64Ne,
            ) => (*c, *n),
            _ => continue,
        };
        if c == counter_local {
            bound = Some(n);
            break;
        }
    }
    let bound = bound?;

    Some(CountedLoopInfo {
        counter_local,
        step,
        bound,
    })
}

/// True if the loop body performs observable side effects — a call (host or
/// internal) or a memory store. Loop-carried recovery is restricted to
/// side-effect-free bodies: loops that publish events, copy memory, or invoke
/// contracts are handled by the existing idiom recognizers and must not be
/// rewritten into a `let mut` + mutation loop.
fn loop_body_has_side_effects(body: &[super::structurize::StructuredBlock]) -> bool {
    use crate::wasm::ir::WasmInstr;
    let mut instrs = Vec::new();
    collect_instrs(body, &mut instrs);
    instrs.iter().any(|i| {
        matches!(
            i,
            WasmInstr::Call(_)
                | WasmInstr::CallIndirect(_)
                | WasmInstr::I32Store(_)
                | WasmInstr::I64Store(_)
                | WasmInstr::I32Store8(_)
                | WasmInstr::I32Store16(_)
                | WasmInstr::I64Store8(_)
                | WasmInstr::I64Store16(_)
                | WasmInstr::I64Store32(_)
        )
    })
}

/// True if the loop body contains a call (host or internal). Frame-slot
/// promotion tolerates memory stores (the spill is itself a store) but never
/// calls — a loop that invokes a contract, requires auth, or publishes an event
/// is handled by the existing recognizers and left untouched.
fn loop_body_has_calls(body: &[super::structurize::StructuredBlock]) -> bool {
    use crate::wasm::ir::WasmInstr;
    let mut instrs = Vec::new();
    collect_instrs(body, &mut instrs);
    instrs
        .iter()
        .any(|i| matches!(i, WasmInstr::Call(_) | WasmInstr::CallIndirect(_)))
}

/// Extract an i32-compatible constant from a StackVal (for cross-type constant folding).
fn as_i32_const(sv: &StackVal) -> Option<i32> {
    match sv {
        StackVal::I32(v) => Some(*v),
        StackVal::I64(v) => Some(*v as i32),
        _ => None,
    }
}

/// Extract a u64 value from a StackVal if it's a known constant.
fn to_u64(val: &StackVal) -> Option<u64> {
    match val {
        StackVal::I32(v) => Some(*v as u32 as u64),
        StackVal::I64(v) => Some(*v as u64),
        _ => None,
    }
}

/// Returns true if `tag` (low byte of an i64 Val) is a known Soroban small-value tag.
/// These tags appear in the `(inner << N) | tag` Val-encode pattern.
fn is_small_val_tag(tag: u64) -> bool {
    matches!(
        tag & 0xFF,
        TAG_FALSE
            | TAG_TRUE
            | TAG_VOID
            | TAG_ERROR
            | TAG_U32
            | TAG_I32
            | TAG_U64_SMALL
            | TAG_I64_SMALL
            | TAG_TIMEPOINT_SMALL
            | TAG_DURATION_SMALL
            | TAG_U128_SMALL
            | TAG_I128_SMALL
            | TAG_U256_SMALL
            | TAG_I256_SMALL
            | TAG_SYMBOL_SMALL
    )
}

/// Returns true if `tag` is an object tag (low byte in `0x40..=0x7f`): the Val
/// carries a 32-bit object handle in its major field rather than an inline payload.
fn is_object_tag(tag: u64) -> bool {
    (0x40..=0x7f).contains(&(tag & 0xFF))
}

/// Map a Val tag byte to its canonical upstream `Tag` variant name.
///
/// Returns `None` for bytes that are not a recognized tag (reserved codes,
/// bound markers, the invalid `Bad` code). Single source of truth for both the
/// `Tag::<name>` rendering of recovered tag checks and any tag-name diagnostics.
fn val_tag_name(tag: u64) -> Option<&'static str> {
    Some(match tag & 0xFF {
        TAG_FALSE => "False",
        TAG_TRUE => "True",
        TAG_VOID => "Void",
        TAG_ERROR => "Error",
        TAG_U32 => "U32Val",
        TAG_I32 => "I32Val",
        TAG_U64_SMALL => "U64Small",
        TAG_I64_SMALL => "I64Small",
        TAG_TIMEPOINT_SMALL => "TimepointSmall",
        TAG_DURATION_SMALL => "DurationSmall",
        TAG_U128_SMALL => "U128Small",
        TAG_I128_SMALL => "I128Small",
        TAG_U256_SMALL => "U256Small",
        TAG_I256_SMALL => "I256Small",
        TAG_SYMBOL_SMALL => "SymbolSmall",
        TAG_U64_OBJECT => "U64Object",
        TAG_I64_OBJECT => "I64Object",
        TAG_TIMEPOINT_OBJECT => "TimepointObject",
        TAG_DURATION_OBJECT => "DurationObject",
        TAG_U128_OBJECT => "U128Object",
        TAG_I128_OBJECT => "I128Object",
        TAG_U256_OBJECT => "U256Object",
        TAG_I256_OBJECT => "I256Object",
        TAG_BYTES_OBJECT => "BytesObject",
        TAG_STRING_OBJECT => "StringObject",
        TAG_SYMBOL_OBJECT => "SymbolObject",
        TAG_VEC_OBJECT => "VecObject",
        TAG_MAP_OBJECT => "MapObject",
        TAG_ADDRESS_OBJECT => "AddressObject",
        TAG_MUXED_ADDRESS_OBJECT => "MuxedAddressObject",
        _ => return None,
    })
}

/// Build the right-hand side of a recovered tag comparison from a tag byte:
/// a named `Tag::<name>` constant when the byte is a known tag, otherwise the
/// raw numeric value.
fn val_tag_const_expr(tag: u64) -> SorobanExpr {
    match val_tag_name(tag) {
        Some(name) => SorobanExpr::ValTagName(name.to_string()),
        None => SorobanExpr::U32Literal(tag as u32),
    }
}

/// Lower a Val tag comparison `(v & 0xFF) <cmp> TAG` to its `(get_tag, Tag::Name)`
/// operand pair, in original operand order. Returns `None` if neither side is a
/// tag-of against a constant tag byte.
fn lower_tag_comparison(
    a: &StackVal,
    b: &StackVal,
    params: &[FnParam],
    registry: &TypeRegistry,
    frame_slots: Option<&FrameSlotMap>,
    visiting: &mut Vec<(u32, i32)>,
) -> Option<(SorobanExpr, SorobanExpr)> {
    if let Some(ValShape::TagOf(inner)) = recognize_val_shape(a)
        && let Some(tag) = to_u64(b)
    {
        let lhs = SorobanExpr::ValTag(Box::new(stack_val_to_expr_inner(
            &inner,
            params,
            registry,
            frame_slots,
            visiting,
        )));
        return Some((lhs, val_tag_const_expr(tag)));
    }
    if let Some(ValShape::TagOf(inner)) = recognize_val_shape(b)
        && let Some(tag) = to_u64(a)
    {
        let rhs = SorobanExpr::ValTag(Box::new(stack_val_to_expr_inner(
            &inner,
            params,
            registry,
            frame_slots,
            visiting,
        )));
        return Some((val_tag_const_expr(tag), rhs));
    }
    None
}

/// A recognized Soroban Val encode/decode shape lifted from a `StackVal` subtree.
///
/// Pure structural classification of the bit patterns the SDK emits when packing
/// or unpacking a Val. Centralizes recognition so every operand position (load,
/// store, arithmetic, compare, branch, return) shares one source of truth; each
/// consumer decides which tags/shifts it cares about.
#[derive(Debug, Clone, PartialEq)]
enum ValShape {
    /// `v & 0xFF` — extract the 8-bit tag of `v`.
    TagOf(StackVal),
    /// `(payload << shift) | tag` — construct a Val from `payload` carrying `tag`.
    Construct {
        payload: StackVal,
        shift: u32,
        tag: u64,
    },
}

/// Classify a `StackVal` as a Soroban Val encode/decode shape, if it matches one.
///
/// Purely structural: matches the immediate `BinOp` shape and does not recurse
/// into the operands' own shapes.
fn recognize_val_shape(val: &StackVal) -> Option<ValShape> {
    let StackVal::BinOp(lhs, op, rhs) = val else {
        return None;
    };
    match op {
        // Tag extraction: `v & 0xFF`.
        BinOper::And if to_u64(rhs) == Some(0xFF) => Some(ValShape::TagOf((**lhs).clone())),
        // Construction: `(payload << shift) | tag` where `tag` is a known Val tag.
        BinOper::Or => {
            let tag = to_u64(rhs)?;
            if tag > 0xFF || val_tag_name(tag).is_none() {
                return None;
            }
            let StackVal::BinOp(payload, BinOper::Shl, shift_val) = &**lhs else {
                return None;
            };
            let shift = to_u64(shift_val)? as u32;
            Some(ValShape::Construct {
                payload: (**payload).clone(),
                shift,
                tag,
            })
        }
        _ => None,
    }
}

/// Strip a Soroban Val-encode pattern: `(inner << N) | small_tag` → `inner`.
///
/// Used in the `>> 32` handler to decode a previously-encoded Val back to its
/// Rust-level arithmetic value. Also used in the arithmetic fallback to extract
/// the clean expression from the Val-encoded stack top. Only small-value tags
/// are stripped: an object construction `(handle << 32) | object_tag` carries an
/// opaque handle, not a Rust-level value, so it is left as `Unknown`.
/// A stack value whose expression form can be re-evaluated at any consumer
/// without duplicating a side effect: constants, parameters, let-bound locals,
/// and arithmetic/conversion trees over those. Host-call results are impure
/// except the `ValConvert` conversion wrapper over a pure source (a pure
/// re-tagging of a value, not an effect).
fn stack_val_is_pure(v: &StackVal) -> bool {
    match v {
        StackVal::I32(_)
        | StackVal::I64(_)
        | StackVal::Param(_)
        | StackVal::WasmParam(_)
        | StackVal::LetBinding(_) => true,
        StackVal::BinOp(a, _, b) | StackVal::Compare(a, _, b) => {
            stack_val_is_pure(a) && stack_val_is_pure(b)
        }
        StackVal::Eqz(a) => stack_val_is_pure(a),
        StackVal::I128Limb { value, .. } => stack_val_is_pure(value),
        StackVal::HostCallResult(e) => match e.as_ref() {
            SorobanExpr::ValConvert { value, .. } => expr_is_pure_source(value),
            // A bare reference the value-link seeds wrap (`var_N` from
            // `link_option_decode_value`) — re-reading a binding is free.
            SorobanExpr::NamedLocal(_) | SorobanExpr::Local(_) | SorobanExpr::Param(_) => true,
            _ => false,
        },
        _ => false,
    }
}

/// Stricter than [`stack_val_is_pure`]: also LOOP-INVARIANT. Used by the
/// unique-reaching-def journal fill, where the single recorded store may sit
/// inside a loop the load is not part of — a value derived from a let-bound
/// local could then be a loop counter, varying per iteration. Constants,
/// parameters, and arithmetic over those cannot vary; `LetBinding` /
/// `HostCallResult` are excluded.
fn stack_val_is_loop_invariant_pure(v: &StackVal) -> bool {
    match v {
        StackVal::I32(_) | StackVal::I64(_) | StackVal::Param(_) | StackVal::WasmParam(_) => true,
        StackVal::BinOp(a, _, b) | StackVal::Compare(a, _, b) => {
            stack_val_is_loop_invariant_pure(a) && stack_val_is_loop_invariant_pure(b)
        }
        StackVal::Eqz(a) => stack_val_is_loop_invariant_pure(a),
        StackVal::I128Limb { value, .. } => stack_val_is_loop_invariant_pure(value),
        _ => false,
    }
}

/// Expression-level purity for a `ValConvert` source: a parameter, literal, or
/// local binding — never a call, storage read, or collection build.
fn expr_is_pure_source(e: &SorobanExpr) -> bool {
    matches!(
        e,
        SorobanExpr::Param(_)
            | SorobanExpr::Local(_)
            | SorobanExpr::NamedLocal(_)
            | SorobanExpr::U32Literal(_)
            | SorobanExpr::I32Literal(_)
            | SorobanExpr::U64Literal(_)
            | SorobanExpr::I64Literal(_)
            | SorobanExpr::U128Literal(_)
            | SorobanExpr::I128Literal(_)
            | SorobanExpr::BoolLiteral(_)
    )
}

fn strip_val_encode(val: StackVal) -> StackVal {
    // Construction `(inner << N) | small_tag` → inner (centralized recognition).
    if let Some(ValShape::Construct { payload, tag, .. }) = recognize_val_shape(&val)
        && is_small_val_tag(tag)
    {
        return payload;
    }
    match val {
        // A `| tag` shape that wasn't a strippable small-value construction
        // (object tag, non-Shl inner, …) decodes to nothing recoverable here.
        StackVal::BinOp(_, BinOper::Or, _) => StackVal::Unknown,
        // Param + (N << 32): inline Val arithmetic. The SDK adds N directly
        // in Val encoding space. Low 32 bits == 0 confirms this is a shifted
        // constant, not a raw value. Decode to Param + N.
        StackVal::BinOp(param, BinOper::Add, delta) => {
            if let StackVal::I64(d) = *delta {
                let raw = d as u64;
                if raw & 0xFFFFFFFF == 0 && matches!(*param, StackVal::Param(_)) {
                    let constant = (raw >> 32) as i64;
                    return StackVal::BinOp(param, BinOper::Add, Box::new(StackVal::I64(constant)));
                }
            }
            StackVal::Unknown
        }
        // Params pass through unchanged (they ARE the Rust-level values in a Val wrapper)
        p @ StackVal::Param(_) => p,
        // HostCallResult wrapping FieldAccess: represents a struct field value from
        // map_unpack_to_linear_memory. The Val encode/decode is transparent — the field
        // access IS the Rust-level value. Only FieldAccess is safe; other HostCallResult
        // types (Add, StorageGet) are actual Val-encoded results.
        StackVal::HostCallResult(ref inner)
            if matches!(**inner, SorobanExpr::FieldAccess { .. }) =>
        {
            cov_mark::hit!(strip_val_encode_field_access_passthrough);
            val
        }
        _ => StackVal::Unknown,
    }
}

/// A symbolic affine term on a frame-slot offset: `coeff * <index_local>`,
/// where `index_local` is the WASM local holding a loop induction variable.
/// Lets `frame[base + i*stride]` accesses (which otherwise fall through to
/// `BinOp`) be addressed. A slot carrying a term is routed to the separate
/// `dynamic_slots` table; only the static `SlotOffset::base` keys `frame_slots`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct SymTerm {
    /// WASM local index of the induction variable.
    index_local: u32,
    /// Byte-stride multiplier (always > 0).
    coeff: u32,
}

/// A frame-relative byte offset carried by `StackVal::FrameSlot`. `term == None`
/// is the purely-static case and behaves exactly like the legacy `i32` offset
/// that keys the `frame_slots` map. A `Some` term marks a dynamic (loop-indexed)
/// address resolved via `dynamic_slots`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct SlotOffset {
    /// Static byte offset from the frame base (the legacy slot key).
    base: i32,
    /// Optional affine term `coeff * index_local`. `None` == purely static.
    term: Option<SymTerm>,
}

impl SlotOffset {
    /// A purely-static offset — the only kind that keys `frame_slots`.
    fn at(base: i32) -> Self {
        SlotOffset { base, term: None }
    }
    /// True when this offset has no symbolic term.
    fn is_static(&self) -> bool {
        self.term.is_none()
    }
    /// Shift the static base by `delta`, preserving any symbolic term.
    fn shift(&self, delta: i32) -> Self {
        SlotOffset {
            base: self.base + delta,
            term: self.term,
        }
    }
}

/// Abstract value tracked on the WASM stack during simulation.
#[derive(Debug, Clone, PartialEq)]
enum StackVal {
    /// A known integer constant
    I32(i32),
    I64(i64),
    /// A reference to a spec-level function parameter
    Param(String),
    /// A raw WASM parameter (when no spec mapping exists)
    WasmParam(u32),
    /// Result of a host call
    HostCallResult(Box<SorobanExpr>),
    /// Result of a binary operation
    BinOp(Box<StackVal>, BinOper, Box<StackVal>),
    /// Result of a comparison operation
    Compare(Box<StackVal>, CmpOp, Box<StackVal>),
    /// Result of eqz (test for zero)
    Eqz(Box<StackVal>),
    /// Bound to a Let statement; references the Let by WASM local index.
    /// Converted to SorobanExpr::Local(idx) which codegen renders as `var_{idx}`.
    LetBinding(u32),
    /// The loop-head merge value of a loop-carried local (by WASM local index).
    /// An opaque height-1 leaf used to seed the loop dataflow analysis: a local
    /// whose post-body value transitively references its own `LoopPhi` is
    /// loop-carried and becomes a `let mut var_{idx}` the body mutates.
    /// Like `LetBinding`, it converts to `SorobanExpr::Local(idx)` (`var_{idx}`).
    LoopPhi(u32),
    /// The loop-head merge value of a loop-carried frame slot (by frame_id and
    /// byte offset). The slot analogue of `LoopPhi`: a slot whose post-body
    /// stored value references its own `FrameSlotPhi` is loop-carried (an
    /// accumulator spilled to the shadow stack) and is promoted to a synthetic
    /// `let mut` variable. Only ever lives in the throwaway analysis context's
    /// `frame_slots`; if it reaches codegen it degrades to `UnknownVal`.
    FrameSlotPhi(u32, i32),
    /// The Some/None discriminant of a fallible storage-decode helper's output
    /// (`[disc@0, value@8]`, `0 = missing/None, 1 = present/Some`), seeded by
    /// `seed_option_decode_status` (issue #35). Consumed by the IfElse
    /// handler: an `if disc == 0 { <bare trap> }` guard is the `.unwrap()`'s
    /// None-arm re-encoded and folds away (the rendered `get(..).unwrap()`
    /// carries the panic-on-missing semantics). Every OTHER consumer degrades
    /// to `UnknownVal` — a non-trap branch on the discriminant (an
    /// `unwrap_or` default arm, a kill-switch check) is REAL control flow
    /// that must stay, and a `panic_with_error!` guard carries an error code
    /// the fold would lose.
    OptionDecodeDisc,
    /// Transitional: `global_get 0` (the WASM stack pointer)
    StackPtrRef,
    /// Transitional: `StackPtrRef - frame_size` before local_tee assigns it.
    /// The frame size value is not read; only the variant tag matters.
    FrameBase(#[allow(dead_code)] i32),
    /// A frame-relative address: (globally unique frame ID, offset from frame base).
    /// Arithmetic on a FrameSlot produces another FrameSlot with updated offset;
    /// the offset may be static or carry a symbolic loop-index term (`SlotOffset`).
    FrameSlot(u32, SlotOffset),
    /// One 64-bit limb (low or high) of a 128-bit value. Soroban lowers i128/u128
    /// arithmetic onto two-i64-limb soft-arithmetic helpers; this keeps the limb
    /// tied to its source 128-bit value so a matching `(lo, hi)` pair can be
    /// re-paired back into the whole value (`obj_from_i128_pieces`, a soft-arith
    /// helper operand). A lone limb that reaches expr conversion lowers to the
    /// source value's expression (the common case is a sign/zero check on the hi
    /// limb, which is semantically a check on the whole value).
    I128Limb {
        value: Box<StackVal>,
        hi: bool,
    },
    /// Unknown/untracked value
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum BinOper {
    Add,
    Sub,
    Mul,
    /// i64 left shift — Val-encode step, tracked so strip_val_encode can remove it.
    Shl,
    /// Bitwise or — Val-encode step, tracked so strip_val_encode can remove it.
    Or,
    /// Bitwise and — used for Val tag extraction (`v & 0xFF`), tracked so
    /// recognize_val_shape can lift it to a tag-of expression.
    And,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum CmpOp {
    Eq,
    Ne,
    LtS,
    LtU,
    GtS,
    GtU,
    LeS,
    LeU,
    GeS,
    GeU,
}

/// Returns true if the StackVal is a comparison where both operands are concrete
/// constants (I32/I64), with no parameters or Unknown values. Inside a loop,
/// such comparisons likely use stale initial values of loop variables.
fn stack_val_is_concrete_compare(val: &StackVal) -> bool {
    fn is_concrete_const(v: &StackVal) -> bool {
        matches!(v, StackVal::I32(_) | StackVal::I64(_))
    }
    match val {
        StackVal::Compare(a, _, b) => is_concrete_const(a) && is_concrete_const(b),
        StackVal::Eqz(a) => is_concrete_const(a),
        _ => false,
    }
}

/// Returns true when a statement is an unconditional terminator (Panic,
/// PanicWithError, or Return) that would prevent subsequent code from
/// executing if spliced into a parent scope.
fn is_terminator_stmt(s: &SorobanStmt) -> bool {
    matches!(
        s,
        SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_))
            | SorobanStmt::Return(_)
    )
}

/// Pre-optimization recovery of the SDK `Vec<i64>` fold idiom inside a
/// tuple-payload `match` arm (udt::add UdtD).
///
/// The arm lifts as `[Expr(<recv>.len()), Loop { … <recv>.get(0) … }]` where
/// `<recv>` is the `Vec` field of the variant's tuple payload. The loop's guards
/// constant-fold, so the optimizer (`remove_spurious_len` + `collapse_trivial_loops`)
/// would delete the whole skeleton and lose the fold. Replace the arm body with a
/// single `Assign{ <phi var>, tup.<scalar> + VecTryIterFold{ tup.<vec>, 0 } }`,
/// which survives the optimizer and collapses to `let x = match …` in codegen
/// (`try_combine_let_match`).
///
/// Narrowly gated (see [`try_rewrite_vec_fold_arm`]) so it cannot touch other
/// fixtures: constructor's storage-dispatch `match` has no loop, and the
/// memory-copy / counted loops match raw load/store offsets, never `len`/`get`
/// on an identical `FieldAccess` receiver inside an `EnumVariant` arm.
fn recover_vec_iter_fold(stmts: &mut [SorobanStmt], registry: &TypeRegistry) {
    for s in stmts.iter_mut() {
        match s {
            SorobanStmt::Match { arms, .. } => {
                // The phi accumulator target is shared by the data-carrying arms
                // (e.g. `var_1`); read it from any sibling arm's `Assign`.
                let phi_target = arms.iter().find_map(|a| {
                    a.body.iter().find_map(|st| match st {
                        SorobanStmt::Assign { target, .. } => Some(target.clone()),
                        _ => None,
                    })
                });
                for arm in arms.iter_mut() {
                    if let Some(ref phi) = phi_target {
                        try_rewrite_vec_fold_arm(arm, phi, registry);
                    }
                    recover_vec_iter_fold(&mut arm.body, registry);
                }
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                recover_vec_iter_fold(then_body, registry);
                recover_vec_iter_fold(else_body, registry);
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                recover_vec_iter_fold(body, registry);
            }
            _ => {}
        }
    }
}

/// If `arm` is the `Vec`-fold skeleton (see [`recover_vec_iter_fold`]), replace
/// its body with `Assign{ phi, tup.<scalar> + VecTryIterFold{ tup.<vec>, 0 } }`
/// and rename its payload binding to `tup`. Returns whether it rewrote the arm.
fn try_rewrite_vec_fold_arm(arm: &mut MatchArm, phi: &str, registry: &TypeRegistry) -> bool {
    // Inspect immutably first, collect the tuple indices, then mutate.
    let (scalar_idx, vec_idx) = {
        let (type_name, variant, binding) = match &arm.pattern {
            MatchPattern::EnumVariant {
                type_name,
                variant,
                bindings,
            } if bindings.len() == 1 => (type_name, variant, &bindings[0]),
            _ => return false,
        };
        if arm.body.len() != 2 {
            return false;
        }
        // body[0] = `Expr(<recv>.len())`
        let recv = match &arm.body[0] {
            SorobanStmt::Expr(SorobanExpr::MethodCall {
                object,
                method,
                args,
            }) if method == "len" && args.is_empty() => object.as_ref(),
            _ => return false,
        };
        // recv must be `<binding>.<field>` (the Vec field of the tuple payload).
        match recv {
            SorobanExpr::FieldAccess { object, .. } => match object.as_ref() {
                SorobanExpr::NamedLocal(n) if n == binding => {}
                _ => return false,
            },
            _ => return false,
        }
        // body[1] = `Loop` whose body iterates `<recv>.get(..)` on the same receiver.
        let loop_body = match &arm.body[1] {
            SorobanStmt::Loop { body } => body,
            _ => return false,
        };
        let has_get = loop_body.iter().any(|st| {
            matches!(
                st,
                SorobanStmt::Expr(SorobanExpr::MethodCall { object, method, .. })
                    if method == "get" && object.as_ref() == recv
            )
        });
        if !has_get {
            return false;
        }
        match tuple_fold_indices(registry, type_name, variant) {
            Some(idxs) => idxs,
            None => return false,
        }
    };

    // Mutate: rename the binding to `tup`, replace the body with the recovered fold.
    if let MatchPattern::EnumVariant { bindings, .. } = &mut arm.pattern {
        bindings[0] = "tup".to_string();
    }
    let tup_field = |i: usize| SorobanExpr::FieldAccess {
        object: Box::new(SorobanExpr::NamedLocal("tup".to_string())),
        field: i.to_string(),
    };
    let value = SorobanExpr::Add(
        Box::new(tup_field(scalar_idx)),
        Box::new(SorobanExpr::VecTryIterFold {
            vec: Box::new(tup_field(vec_idx)),
            init: Box::new(SorobanExpr::I64Literal(0)),
        }),
    );
    arm.body = vec![SorobanStmt::Assign {
        target: phi.to_string(),
        value,
    }];
    cov_mark::hit!(vec_iter_fold_recovered);
    true
}

/// For a union `variant` whose payload is a 2-field tuple struct `(i64, Vec<_>)`,
/// return `(scalar_index, vec_index)`. `None` if the payload is not that shape.
fn tuple_fold_indices(
    registry: &TypeRegistry,
    union_name: &str,
    variant: &str,
) -> Option<(usize, usize)> {
    let payload = registry.find_variant_data_type(union_name, variant)?;
    let udt_name = registry.resolve_type_name(&payload)?;
    let spec = registry.get_struct(&udt_name)?;
    if spec.fields.len() != 2 {
        return None;
    }
    let mut scalar_idx = None;
    let mut vec_idx = None;
    for (i, f) in spec.fields.iter().enumerate() {
        // Tuple struct: field names are numeric ("0", "1", …).
        if f.name.to_utf8_string().ok()?.parse::<usize>().is_err() {
            return None;
        }
        match &f.type_ {
            ScSpecTypeDef::Vec(_) => vec_idx = Some(i),
            ScSpecTypeDef::I64 => scalar_idx = Some(i),
            _ => return None,
        }
    }
    Some((scalar_idx?, vec_idx?))
}

/// Body-level re-attribution of an enum scrutinee's hoisted payload field-loads.
///
/// Runs after lifting (so every `<enum_param>.<field>` load is resolved — unlike
/// the per-match recognition, where the scrutinee's loads may still be unresolved)
/// and before optimization. For each `Match` over a `Param` enum scrutinee, binds
/// each data-carrying arm's payload to `v0` and rewrites the arm's reads of the
/// hoisted `let var_N = <param>.<field>` (which surface as `Local(N)`) into
/// `v0.<field>`. The now-dead hoisted `let`s are left for the optimizer's
/// unused-let removal.
fn rebind_hoisted_enum_payload_body(stmts: &mut [SorobanStmt]) {
    // Collect hoisted payload loads: WASM local index N -> (enum param, field).
    let mut load_of: std::collections::HashMap<u32, (String, String)> =
        std::collections::HashMap::new();
    for s in stmts.iter() {
        if let SorobanStmt::Let {
            name,
            value: SorobanExpr::FieldAccess { object, field },
            ..
        } = s
            && let SorobanExpr::Param(p) = object.as_ref()
            && let Some(idx) = name
                .strip_prefix("var_")
                .and_then(|n| n.parse::<u32>().ok())
        {
            load_of.insert(idx, (p.clone(), field.clone()));
        }
    }
    if load_of.is_empty() {
        return;
    }
    for s in stmts.iter_mut() {
        rebind_enum_payload_in_stmt(s, &load_of);
    }
}

fn rebind_enum_payload_in_stmt(
    s: &mut SorobanStmt,
    load_of: &std::collections::HashMap<u32, (String, String)>,
) {
    match s {
        SorobanStmt::Match { scrutinee, arms } => {
            let scrut_param = match scrutinee {
                SorobanExpr::Param(p) => Some(p.clone()),
                _ => None,
            };
            let field_of: std::collections::HashMap<u32, String> = scrut_param
                .as_ref()
                .map(|p| {
                    load_of
                        .iter()
                        .filter(|(_, (pp, _))| pp == p)
                        .map(|(n, (_, f))| (*n, f.clone()))
                        .collect()
                })
                .unwrap_or_default();
            for arm in arms.iter_mut() {
                // Recurse into nested matches first.
                for st in arm.body.iter_mut() {
                    rebind_enum_payload_in_stmt(st, load_of);
                }
                if !field_of.is_empty()
                    && let MatchPattern::EnumVariant { bindings, .. } = &mut arm.pattern
                    && bindings.len() == 1
                    && bindings[0] == "_"
                {
                    let mut consumed = std::collections::HashSet::new();
                    let mut bound = false;
                    for st in arm.body.iter_mut() {
                        rewrite_local_payload_in_stmt(
                            st,
                            &field_of,
                            "v0",
                            &mut consumed,
                            &mut bound,
                        );
                    }
                    if bound {
                        bindings[0] = "v0".to_string();
                    }
                }
            }
        }
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            for st in then_body.iter_mut().chain(else_body.iter_mut()) {
                rebind_enum_payload_in_stmt(st, load_of);
            }
        }
        SorobanStmt::For { body, .. } | SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            for st in body.iter_mut() {
                rebind_enum_payload_in_stmt(st, load_of);
            }
        }
        _ => {}
    }
}

/// Rewrite `Local(n)` reads of a hoisted enum-payload load (`field_of[n]`) into
/// `<binding>.<field>` within a statement tree. Used by `rebind_hoisted_enum_payload_body`.
fn rewrite_local_payload_in_stmt(
    st: &mut SorobanStmt,
    field_of: &std::collections::HashMap<u32, String>,
    binding: &str,
    consumed: &mut std::collections::HashSet<u32>,
    bound: &mut bool,
) {
    match st {
        SorobanStmt::Expr(e)
        | SorobanStmt::Let { value: e, .. }
        | SorobanStmt::Assign { value: e, .. }
        | SorobanStmt::Return(Some(e)) => {
            rewrite_local_payload_in_expr(e, field_of, binding, consumed, bound)
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            rewrite_local_payload_in_expr(condition, field_of, binding, consumed, bound);
            for s in then_body.iter_mut().chain(else_body.iter_mut()) {
                rewrite_local_payload_in_stmt(s, field_of, binding, consumed, bound);
            }
        }
        SorobanStmt::Match { arms, .. } => {
            for arm in arms.iter_mut() {
                for s in arm.body.iter_mut() {
                    rewrite_local_payload_in_stmt(s, field_of, binding, consumed, bound);
                }
            }
        }
        SorobanStmt::For {
            start, end, body, ..
        } => {
            rewrite_local_payload_in_expr(start, field_of, binding, consumed, bound);
            rewrite_local_payload_in_expr(end, field_of, binding, consumed, bound);
            for s in body.iter_mut() {
                rewrite_local_payload_in_stmt(s, field_of, binding, consumed, bound);
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            for s in body.iter_mut() {
                rewrite_local_payload_in_stmt(s, field_of, binding, consumed, bound);
            }
        }
        _ => {}
    }
}

fn rewrite_local_payload_in_expr(
    e: &mut SorobanExpr,
    field_of: &std::collections::HashMap<u32, String>,
    binding: &str,
    consumed: &mut std::collections::HashSet<u32>,
    bound: &mut bool,
) {
    if let SorobanExpr::Local(n) = e {
        if let Some(field) = field_of.get(n) {
            consumed.insert(*n);
            *bound = true;
            *e = SorobanExpr::FieldAccess {
                object: Box::new(SorobanExpr::NamedLocal(binding.to_string())),
                field: field.clone(),
            };
        }
        return;
    }
    let mut rec =
        |x: &mut SorobanExpr| rewrite_local_payload_in_expr(x, field_of, binding, consumed, bound);
    match e {
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Rem(a, b)
        | SorobanExpr::Eq(a, b)
        | SorobanExpr::Ne(a, b)
        | SorobanExpr::Lt(a, b)
        | SorobanExpr::Le(a, b)
        | SorobanExpr::Gt(a, b)
        | SorobanExpr::Ge(a, b)
        | SorobanExpr::And(a, b)
        | SorobanExpr::Or(a, b) => {
            rec(a);
            rec(b);
        }
        SorobanExpr::Not(x)
        | SorobanExpr::SretResult(x)
        | SorobanExpr::ValTag(x)
        | SorobanExpr::Some(x)
        | SorobanExpr::ErrorFromCode(x)
        | SorobanExpr::PanicWithError(x) => rec(x),
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => rec(value),
        SorobanExpr::FieldAccess { object, .. } => rec(object),
        SorobanExpr::MethodCall { object, args, .. } => {
            rec(object);
            for a in args.iter_mut() {
                rec(a);
            }
        }
        SorobanExpr::TupleConstruct(xs) | SorobanExpr::VecConstruct(xs) => {
            for x in xs.iter_mut() {
                rec(x);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for x in fields.iter_mut() {
                rec(x);
            }
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, x) in fields.iter_mut() {
                rec(x);
            }
        }
        _ => {}
    }
}

/// Whether a `StackVal` references a phi-merged `LetBinding` anywhere in its tree.
/// Lets udt::add's post-match composition (`var_a + var_b`) write through the
/// phi-protection guard (which otherwise drops the final `a + b`). NOTE: this is
/// the partial composition recovery — it also captures UdtD's arm-local tail
/// (`tup.0 + sum`) that the structurizer leaves in a shared merge block, so the
/// final sum still carries a spurious term until that block is attributed to the
/// arm (the same shared-block work the fold reconstruction needs).
fn stack_val_references_letbinding(v: &StackVal) -> bool {
    match v {
        StackVal::LetBinding(_) => true,
        StackVal::BinOp(a, _, b) | StackVal::Compare(a, _, b) => {
            stack_val_references_letbinding(a) || stack_val_references_letbinding(b)
        }
        StackVal::Eqz(a) => stack_val_references_letbinding(a),
        _ => false,
    }
}

/// Find the receiver object of a `.len()` `MethodCall` anywhere within `expr`.
/// Used by `try_recognize_option_front_if` to recover the `Vec` whose length the
/// not-empty condition checks.
fn find_vec_len_object(expr: &SorobanExpr) -> Option<SorobanExpr> {
    match expr {
        SorobanExpr::MethodCall { object, method, .. } if method == "len" => {
            Some((**object).clone())
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            find_vec_len_object(object).or_else(|| args.iter().find_map(find_vec_len_object))
        }
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Rem(a, b)
        | SorobanExpr::Eq(a, b)
        | SorobanExpr::Ne(a, b)
        | SorobanExpr::Lt(a, b)
        | SorobanExpr::Le(a, b)
        | SorobanExpr::Gt(a, b)
        | SorobanExpr::Ge(a, b)
        | SorobanExpr::And(a, b)
        | SorobanExpr::Or(a, b) => find_vec_len_object(a).or_else(|| find_vec_len_object(b)),
        SorobanExpr::Not(e)
        | SorobanExpr::ValConvert { value: e, .. }
        | SorobanExpr::CastAs { value: e, .. }
        | SorobanExpr::ValTag(e)
        | SorobanExpr::Some(e)
        | SorobanExpr::SretResult(e) => find_vec_len_object(e),
        SorobanExpr::FieldAccess { object, .. } => find_vec_len_object(object),
        _ => None,
    }
}

/// A "weak" local is one that carries no meaningful semantic content — it is
/// either uninitialised (Unknown), a zero-initialisation constant, or a raw
/// frame pointer.  Guard-pattern propagation may safely overwrite these with
/// values discovered inside a guard body, but must never overwrite strong
/// values like LetBinding or Param references.
fn is_weak_local(val: &StackVal) -> bool {
    matches!(
        val,
        StackVal::Unknown
            | StackVal::FrameBase(_)
            | StackVal::FrameSlot(_, _)
            | StackVal::StackPtrRef
            | StackVal::I32(0)
            | StackVal::I64(0)
    )
}

/// Snapshot of all WASM locals at a point in time, used to detect which locals
/// changed across a branch.
#[allow(dead_code)]
type LocalSnapshot = Vec<StackVal>;

/// Returns true when a condition value tests a fallible storage-decode
/// discriminant for the None arm (`disc == 0` / `eqz disc`). Used by the
/// IfElse handler's trap-guard fold (issue #35); see
/// [`StackVal::OptionDecodeDisc`].
fn is_option_decode_none_check(cond: &StackVal) -> bool {
    match cond {
        StackVal::Eqz(x) => matches!(x.as_ref(), StackVal::OptionDecodeDisc),
        StackVal::Compare(a, CmpOp::Eq, b) => {
            matches!(
                (a.as_ref(), b.as_ref()),
                (
                    StackVal::OptionDecodeDisc,
                    StackVal::I32(0) | StackVal::I64(0)
                ) | (
                    StackVal::I32(0) | StackVal::I64(0),
                    StackVal::OptionDecodeDisc
                )
            )
        }
        _ => false,
    }
}

/// Returns true when a tracked value is the raw result of an empty-collection
/// constructor host call (`map_new`/`vec_new`/`bytes_new`). Used by the loop
/// handler to invalidate such defs when a loop body overwrites the local
/// (issue #36): keeping the pre-loop empty constructor across a mutation chain
/// fabricates an empty `Map`/`Vec` at every post-loop use site.
fn is_empty_collection_val(val: &StackVal) -> bool {
    matches!(
        val,
        StackVal::HostCallResult(expr) if matches!(expr.as_ref(), SorobanExpr::CollectionNew(_))
    )
}

/// Returns true for StackVal variants that carry meaningful semantic content
/// worth preserving across branches via phi-merge. Raw constants (I32, I64)
/// are excluded because they are often intermediate computation values from
/// branch-sequential execution rather than intentional results.
fn is_meaningful_for_phi(val: &StackVal) -> bool {
    matches!(
        val,
        StackVal::Param(_)
            | StackVal::HostCallResult(_)
            | StackVal::LetBinding(_)
            | StackVal::Compare(_, _, _)
    ) || matches!(
        val,
        StackVal::BinOp(_, BinOper::Add | BinOper::Sub | BinOper::Mul, _)
    )
}

/// Checks whether a `let mut var_N` binding already exists in the statement list.
fn is_already_phi_declared(stmts: &[SorobanStmt], local_idx: u32) -> bool {
    let name = format!("var_{}", local_idx);
    stmts
        .iter()
        .any(|s| matches!(s, SorobanStmt::Let { name: n, mutable: true, .. } if n == &name))
}

/// Reconciles divergent local values after an if/else branch by emitting
/// `let mut` declarations and `Assign` statements to capture phi-merge values.
///
/// For each WASM local that differs between the two branches:
/// - If one branch terminates (return/panic), only the other's value matters.
/// - If both agree, the shared value is propagated.
/// - If values diverge and at least one is meaningful, a phi variable is emitted.
#[allow(clippy::too_many_arguments)]
fn reconcile_branch_locals(
    parent_locals: &mut [StackVal],
    parent_stmts: &mut Vec<SorobanStmt>,
    pre_branch: &[StackVal],
    branch_a_locals: &[StackVal],
    branch_b_locals: &[StackVal],
    a_terminates: bool,
    b_terminates: bool,
    num_wasm_params: u32,
    branch_a_stmts: &mut Vec<SorobanStmt>,
    branch_b_stmts: &mut Vec<SorobanStmt>,
    phi_protected: &mut Vec<u32>,
    params: &[FnParam],
    registry: &TypeRegistry,
    frame_slots: Option<&FrameSlotMap>,
) {
    let limit = pre_branch
        .len()
        .min(branch_a_locals.len())
        .min(branch_b_locals.len())
        .min(parent_locals.len());

    for idx in (num_wasm_params as usize)..limit {
        let pre = &pre_branch[idx];
        let a = &branch_a_locals[idx];
        let b = &branch_b_locals[idx];

        // Both unchanged — nothing to do
        if a == pre && b == pre {
            continue;
        }

        // Both branches terminate — neither flows out
        if a_terminates && b_terminates {
            continue;
        }

        // One branch terminates — only the other's value matters
        if a_terminates {
            parent_locals[idx] = b.clone();
            continue;
        }
        if b_terminates {
            parent_locals[idx] = a.clone();
            continue;
        }

        // Both agree on value
        if a == b {
            parent_locals[idx] = a.clone();
            continue;
        }

        // Divergent — need phi, but only for meaningful values
        if !is_meaningful_for_phi(a) && !is_meaningful_for_phi(b) {
            continue;
        }

        // Emit let mut if not already declared
        if !is_already_phi_declared(parent_stmts, idx as u32) {
            let init_expr = stack_val_to_arith_expr(pre, params, registry, frame_slots);
            parent_stmts.push(SorobanStmt::Let {
                name: format!("var_{}", idx),
                mutable: true,
                value: init_expr,
            });
        }

        // Add assignments to branches for changed values
        if a != pre {
            let a_expr = stack_val_to_arith_expr(a, params, registry, frame_slots);
            branch_a_stmts.push(SorobanStmt::Assign {
                target: format!("var_{}", idx),
                value: a_expr,
            });
        }
        if b != pre {
            let b_expr = stack_val_to_arith_expr(b, params, registry, frame_slots);
            branch_b_stmts.push(SorobanStmt::Assign {
                target: format!("var_{}", idx),
                value: b_expr,
            });
        }

        parent_locals[idx] = StackVal::LetBinding(idx as u32);
        phi_protected.push(idx as u32);
    }
}

/// Check whether the remaining blocks in a parent scope form an unconditional
/// error path (panic / unreachable).  When a BrIf(0) guard check is followed
/// only by such an error path, the if-body always executes on the success path,
/// so locals set inside the body are safe to propagate to the parent context.
///
/// Recognised patterns (all after the current Block):
///   - `[Instruction(Unreachable)]`
///   - `[Instruction(Call(_)), Instruction(Unreachable)]`
///   - `[Block { body: <error_path> }]`  (one wrapper block around the above)
///
/// Strip `Return(None)` + `Expr(Panic)` consecutive pairs from a guard-error-path
/// body. These pairs are block-exit artifacts from inlined function bodies where
/// the WASM `return` instruction and error-path `panic` appear at the top level.
///
/// In the guard-error-path context, `Return(None)` is a block-level exit (not a
/// function return) because the outer block's error path handles the real exit.
/// Removing these pairs prevents `remove_dead_code` from treating the `Return(None)`
/// as a function-level terminator.
///
/// Only strips pairs that are NOT the last two items (the final pair might be the
/// function's legitimate return + wrapper panic).
fn strip_return_panic_pairs_in_guard(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    if stmts.len() < 4 {
        // Too short to have a non-final pair — leave unchanged
        return stmts;
    }

    let mut result = Vec::with_capacity(stmts.len());
    let mut i = 0;
    while i < stmts.len() {
        // Pattern 1: Return(None) + Expr(Panic) consecutive pair.
        // Block-exit artifacts from inlined functions. Strip non-final pairs.
        if i + 1 < stmts.len()
            && matches!(&stmts[i], SorobanStmt::Return(None))
            && matches!(
                &stmts[i + 1],
                SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_))
            )
            && i + 2 < stmts.len()
        {
            i += 2;
            continue;
        }

        // Pattern 2: Expr(Panic) immediately after a side-effectful operation.
        // These are error-path artifacts from inlined functions where the
        // operation's error path (e.g., unwrap failure, key not found,
        // contract call failure) produces a standalone panic. The actual
        // error handling is in the outer block's Unreachable.
        // Only strip non-final panics to preserve the wrapper panic at the end.
        if matches!(
            &stmts[i],
            SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_))
        ) && i + 1 < stmts.len()
            && is_post_operation_panic_context(result.last())
        {
            i += 1;
            continue;
        }

        result.push(stmts[i].clone());
        i += 1;
    }
    result
}

/// Strip non-final inlined-function artifacts at all nesting levels:
/// - `Return(None)` — block-exit artifacts from WASM `return` in inlined bodies
/// - `Expr(Panic)` after side-effectful host calls — error-path artifacts from
///   inlined function error paths (unwrap failure, contract call failure, etc.)
///
/// ONLY called from `process_guard_brif_chain` — in the guard chain
/// context, these are always artifacts, never legitimate user code.
/// The function's actual return is handled by the stack-based implicit
/// return in `lift_function_body`.
fn strip_nonfinal_void_returns(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let len = stmts.len();
    let mut result = Vec::with_capacity(len);
    for (i, stmt) in stmts.into_iter().enumerate() {
        let is_final = i + 1 >= len;
        // Strip non-final Return(None)
        if !is_final && matches!(&stmt, SorobanStmt::Return(None)) {
            continue;
        }
        // Strip non-final standalone Panic/PanicWithError ONLY when preceded
        // by a side-effectful host call (InvokeContract, StorageSet, StorageGet
        // with unwrap, RequireAuth, etc.). This distinguishes inlined error-path
        // artifacts from legitimate user panics (e.g., `if a < b { panic!() }`).
        if !is_final
            && matches!(
                &stmt,
                SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_))
            )
            && is_post_host_call_panic(result.last())
        {
            continue;
        }
        // Recurse into nested bodies
        result.push(strip_nonfinal_void_returns_stmt(stmt));
    }
    result
}

/// Check if the preceding statement is a side-effectful host call whose
/// error path produces a standalone Panic artifact. More permissive than
/// `is_post_operation_panic_context` — matches any side-effectful expression
/// or let binding from a host call.
fn is_post_host_call_panic(prev: Option<&SorobanStmt>) -> bool {
    match prev {
        Some(SorobanStmt::Expr(e)) | Some(SorobanStmt::Let { value: e, .. }) => matches!(
            e,
            SorobanExpr::InvokeContract { .. }
                | SorobanExpr::TryInvokeContract { .. }
                | SorobanExpr::StorageGet { .. }
                | SorobanExpr::StorageSet { .. }
                | SorobanExpr::StorageHas { .. }
                | SorobanExpr::StorageRemove { .. }
                | SorobanExpr::RequireAuth(_)
                | SorobanExpr::RequireAuthForArgs { .. }
                | SorobanExpr::PublishEvent { .. }
                | SorobanExpr::MethodCall { .. }
                | SorobanExpr::ValConvert { .. }
                | SorobanExpr::StorageExtendTtl { .. }
                | SorobanExpr::ExtendInstanceAndCodeTtl { .. }
                | SorobanExpr::CurrentContractAddress
        ),
        _ => false,
    }
}

fn strip_nonfinal_void_returns_stmt(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: strip_nonfinal_void_returns(then_body),
            else_body: strip_nonfinal_void_returns(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| crate::ir::soroban_ir::MatchArm {
                    body: strip_nonfinal_void_returns(arm.body),
                    ..arm
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: strip_nonfinal_void_returns(body),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(strip_nonfinal_void_returns(body)),
        other => other,
    }
}

/// Check if the preceding statement is a side-effectful operation whose
/// error path produces a standalone panic artifact.
///
/// Conservative: only matches specific patterns known to produce safe
/// post-panic continuation. Adding too many patterns exposes downstream
/// `var_N` artifacts from unresolved variable names.
fn is_post_operation_panic_context(prev: Option<&SorobanStmt>) -> bool {
    match prev {
        // After Let { StorageGet { unwrap: true } } — unwrap failure path
        Some(SorobanStmt::Let {
            value: SorobanExpr::StorageGet { unwrap: true, .. },
            ..
        }) => true,
        // After Let { ValConvert { StorageGet } } — typed storage read error path
        Some(SorobanStmt::Let {
            value: SorobanExpr::ValConvert { value, .. },
            ..
        }) => matches!(value.as_ref(), SorobanExpr::StorageGet { unwrap: true, .. }),
        _ => false,
    }
}

/// Extract string literals referenced by a function's body from the WASM data section.
/// Finds consecutive (I32Const ptr, I32Const len) pairs and reads the strings.
fn extract_data_strings(module: &WasmModule, func_idx: u32) -> Vec<String> {
    use crate::wasm::ir::WasmInstr;
    let mut strings = Vec::new();

    let func = match module.get_function(func_idx) {
        Some(f) => f,
        None => return strings,
    };

    // Scan for consecutive I32Const pairs that look like (ptr, len)
    for window in func.body.windows(2) {
        if let [WasmInstr::I32Const(ptr), WasmInstr::I32Const(len)] = window {
            let ptr = *ptr as u32;
            let len = *len as u32;
            // Reasonable string: ptr > 1024 (data section), len 1-64
            if ptr > 1024
                && len > 0
                && len <= 64
                && let Some(s) = module.data_sections.read_string(ptr, len)
            {
                // Only keep strings that look like identifiers
                if s.chars().all(|c| c.is_alphanumeric() || c == '_') {
                    strings.push(s);
                }
            }
        }
    }

    // Also check internal call targets (one level deep)
    for instr in &func.body {
        if let WasmInstr::Call(target) = instr
            && module.imports.get_by_index(*target).is_none()
        {
            // Don't recurse too deep
            if let Some(callee) = module.get_function(*target) {
                for window in callee.body.windows(2) {
                    if let [WasmInstr::I32Const(ptr), WasmInstr::I32Const(len)] = window {
                        let ptr = *ptr as u32;
                        let len = *len as u32;
                        if ptr > 1024
                            && len > 0
                            && len <= 64
                            && let Some(s) = module.data_sections.read_string(ptr, len)
                            && s.chars().all(|c| c.is_alphanumeric() || c == '_')
                        {
                            strings.push(s);
                        }
                    }
                }
            }
        }
    }

    strings
}

/// Branch-exit target for [`recover_fail_with_error_branches`], indexed by WASM
/// branch depth: the innermost enclosing control structure is the last element
/// of the `enclosing` stack (depth 0), the next out is depth 1, and so on.
enum BranchExitTarget {
    /// `br`/`br_if` to this depth is a loop back-edge (continue) — never an
    /// error exit, so never recovered.
    LoopContinue,
    /// `br`/`br_if` to this depth exits to a short, flat, diverging tail that
    /// calls `fail_with_error` (a contract-error panic). Holds the cloned tail
    /// instructions, inlined at the branch site.
    FailWithError(Vec<super::structurize::StructuredBlock>),
    /// Any other exit (normal continuation, bare trap, nested control flow):
    /// left to the existing break/continue lifting.
    Plain,
}

/// Is `tail` a short, flat, diverging error path that reports a contract error
/// via `fail_with_error`? This is the body of a validation guard's panic
/// branch — `i64.const <error>; call $fail_with_error; unreachable` — and
/// branching to it is semantically `if cond { panic_with_error!(…) }`.
///
/// Gated tightly: no nested control flow, ends in `unreachable` (raw or the
/// issue-#11 safety-net reclassification), short (a real tail is 1–4 nodes),
/// and contains a direct `fail_with_error` wrapper call. The `fail_with_error`
/// requirement is the load-bearing gate — it fires only on genuine contract
/// error reporting, never on SDK dispatch preambles or compiler safety nets.
fn is_fail_with_error_tail(
    tail: &[super::structurize::StructuredBlock],
    module: &WasmModule,
) -> bool {
    use super::structurize::StructuredBlock;
    use crate::wasm::ir::WasmInstr;

    const MAX_TAIL_LEN: usize = 6;
    if tail.is_empty() || tail.len() > MAX_TAIL_LEN {
        return false;
    }
    // The tail must end in a divergence (raw `unreachable` or its safety-net form).
    if !matches!(
        tail.last(),
        Some(StructuredBlock::Instruction(WasmInstr::Unreachable))
            | Some(StructuredBlock::SafetyNetUnreachable)
    ) {
        return false;
    }
    // Every node must be a plain instruction (or the safety-net marker): nested
    // control flow would risk inlining real continuation code, not just a trap.
    let mut has_fail_with_error = false;
    for sb in tail {
        match sb {
            StructuredBlock::SafetyNetUnreachable => {}
            StructuredBlock::Instruction(WasmInstr::Call(idx))
                if function_calls_host(module, *idx, HostModule::Context, "fail_with_error") =>
            {
                has_fail_with_error = true;
            }
            StructuredBlock::Instruction(_) => {}
            _ => return false,
        }
    }
    has_fail_with_error
}

/// Layer B (issue #12): recover validation panics dropped by multi-level
/// branches. A `br_if k` whose depth-`k` target is a `fail_with_error` tail
/// (see [`is_fail_with_error_tail`]) is the WASM lowering of
/// `if cond { panic_with_error!(…) }`, but the flat lifter loses the
/// association — the condition surfaces as `if cond { break }` inside a loop
/// while the panic leaks out as a sibling stray (later dropped by the
/// optimizer), so the specific contract error is lost.
///
/// This pure pre-pass over the structured tree rewrites each such `br_if k`
/// into an inline `IfElse { then: <tail> }`. The condition is already on the
/// stack and `br_if`/`if` both pop one i32 with the same true-polarity, so the
/// existing `IfElse` lifting reproduces the nested `panic_with_error!`. The
/// now-unreachable original tail is left in place and dropped downstream by the
/// optimizer's stray-panic pass, exactly as before.
///
/// Scope is deliberately narrow: only `BrIf` (not unconditional `Br`), only
/// `fail_with_error` tails. Every other branch keeps its current break/continue
/// lifting byte-for-byte.
fn recover_fail_with_error_branches(
    blocks: &mut [super::structurize::StructuredBlock],
    module: &WasmModule,
) {
    rewrite_branch_seq(blocks, &mut Vec::new(), module);
}

fn rewrite_branch_seq(
    blocks: &mut [super::structurize::StructuredBlock],
    enclosing: &mut Vec<BranchExitTarget>,
    module: &WasmModule,
) {
    use super::structurize::StructuredBlock;
    use crate::wasm::ir::{BlockType, WasmInstr};

    let n = blocks.len();

    // Phase 1 — classify each child's branch-exit target from its following
    // siblings. Done up front (read-only) so the Phase 2 rewrites below cannot
    // perturb the classification.
    let mut child_targets: Vec<Option<BranchExitTarget>> = Vec::with_capacity(n);
    for (i, child) in blocks.iter().enumerate() {
        let t = match child {
            StructuredBlock::Loop { .. } => Some(BranchExitTarget::LoopContinue),
            StructuredBlock::Block { .. } | StructuredBlock::IfElse { .. } => {
                if is_fail_with_error_tail(&blocks[i + 1..], module) {
                    Some(BranchExitTarget::FailWithError(blocks[i + 1..].to_vec()))
                } else {
                    Some(BranchExitTarget::Plain)
                }
            }
            _ => None,
        };
        child_targets.push(t);
    }

    // Phase 2 — rewrite branch instructions at THIS level. Each rewrite is 1:1
    // (one `BrIf` node becomes one `IfElse` node), preserving indices so
    // `child_targets` stays aligned for Phase 3.
    for block in blocks.iter_mut() {
        if let StructuredBlock::Instruction(WasmInstr::BrIf(k)) = block {
            let depth = *k as usize;
            if depth < enclosing.len()
                && let BranchExitTarget::FailWithError(tail) =
                    &enclosing[enclosing.len() - 1 - depth]
            {
                cov_mark::hit!(layer_b_brif_to_fail_with_error);
                *block = StructuredBlock::IfElse {
                    block_type: BlockType::Empty,
                    then_body: tail.clone(),
                    else_body: Vec::new(),
                };
            }
        }
    }

    // Phase 3 — recurse into children, extending the enclosing stack by one
    // entry per nested control structure (matching WASM branch-depth counting).
    for i in 0..n {
        let Some(target) = child_targets[i].take() else {
            continue;
        };
        match &mut blocks[i] {
            StructuredBlock::Block { body, .. } | StructuredBlock::Loop { body, .. } => {
                enclosing.push(target);
                rewrite_branch_seq(body, enclosing, module);
                enclosing.pop();
            }
            StructuredBlock::IfElse {
                then_body,
                else_body,
                ..
            } => {
                enclosing.push(target);
                rewrite_branch_seq(then_body, enclosing, module);
                rewrite_branch_seq(else_body, enclosing, module);
                enclosing.pop();
            }
            _ => {}
        }
    }
}

fn is_guard_error_path(remaining: &[super::structurize::StructuredBlock]) -> bool {
    use super::structurize::StructuredBlock;
    use crate::wasm::ir::WasmInstr;

    // After issue #11's CFG reclassification, the trailing `unreachable` of a
    // guard error path may have become `SafetyNetUnreachable`. Both shapes are
    // semantic dead-ends — recognise either.
    let is_dead_end = |sb: &StructuredBlock| {
        matches!(
            sb,
            StructuredBlock::Instruction(WasmInstr::Unreachable)
                | StructuredBlock::SafetyNetUnreachable
        )
    };

    match remaining {
        // Direct Unreachable (or its safety-net reclassification)
        [sb] if is_dead_end(sb) => true,
        // Call to panic wrapper followed by Unreachable (or safety-net)
        [StructuredBlock::Instruction(WasmInstr::Call(_)), sb] if is_dead_end(sb) => true,
        // Single wrapper Block around an error path
        [StructuredBlock::Block { body, .. }] => is_guard_error_path(body),
        _ => false,
    }
}

/// Check whether any segment between BrIf(0) positions contains a Call
/// instruction (recursively scanning nested blocks).  This distinguishes
/// real validation guard blocks (which call host functions for storage reads,
/// auth checks, etc.) from SDK dispatch preambles (which only do arithmetic
/// on Soroban Val parameter tags).
fn has_call_in_brif_segments(
    body: &[super::structurize::StructuredBlock],
    brif_positions: &[usize],
) -> bool {
    use super::structurize::StructuredBlock;
    use crate::wasm::ir::WasmInstr;

    fn segment_has_call(blocks: &[StructuredBlock]) -> bool {
        for b in blocks {
            match b {
                StructuredBlock::Instruction(WasmInstr::Call(_)) => return true,
                StructuredBlock::Block { body, .. } | StructuredBlock::Loop { body, .. }
                    if segment_has_call(body) =>
                {
                    return true;
                }
                StructuredBlock::IfElse {
                    then_body,
                    else_body,
                    ..
                } if (segment_has_call(then_body) || segment_has_call(else_body)) => {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    let mut cursor = 0;
    for &brif_pos in brif_positions {
        let segment = &body[cursor..brif_pos];
        if segment_has_call(segment) {
            return true;
        }
        cursor = brif_pos + 1;
    }
    false
}

/// Returns true if the StackVal is a constant expression that could be
/// evaluated statically.  Used to guard BrIf(0) local propagation: when the
/// condition is statically known the branch is deterministic and propagating
/// body locals would corrupt match/phi-merge recovery.
fn is_static_condition(val: &StackVal) -> bool {
    match val {
        StackVal::I32(_) | StackVal::I64(_) => true,
        StackVal::Compare(a, _, b) => is_static_condition(a) && is_static_condition(b),
        StackVal::Eqz(inner) => is_static_condition(inner),
        StackVal::BinOp(a, _, b) => is_static_condition(a) && is_static_condition(b),
        _ => false,
    }
}

/// Returns true if the StackVal condition tree contains an I64 constant that
/// looks like a Soroban Val-encoded value (nonzero multiple of 2^32).  These
/// appear in SDK-generated dispatch preambles that compare raw Val-encoded
/// values (type tags, field lengths) before Val conversion.
fn stack_val_has_val_constant(val: &StackVal) -> bool {
    match val {
        StackVal::I64(v) => {
            let u = *v as u64;
            u > 0 && u.is_multiple_of(1u64 << 32)
        }
        StackVal::Compare(a, _, b) | StackVal::BinOp(a, _, b) => {
            stack_val_has_val_constant(a) || stack_val_has_val_constant(b)
        }
        StackVal::Eqz(inner) => stack_val_has_val_constant(inner),
        _ => false,
    }
}

/// Returns true if the StackVal involves an Unknown value anywhere in its tree.
///
/// Used to detect dispatch preamble type-check conditions that cannot be evaluated
/// statically (e.g., I64And(param, 0xFF) != expected_tag).
/// True if `val` transitively references `LoopPhi(idx)` — the test that decides
/// whether a body-written local is genuinely loop-carried (its new value depends
/// on its own loop-head value) versus freshly recomputed each iteration.
fn stackval_references_loop_phi(val: &StackVal, idx: u32) -> bool {
    match val {
        StackVal::LoopPhi(i) => *i == idx,
        StackVal::BinOp(a, _, b) | StackVal::Compare(a, _, b) => {
            stackval_references_loop_phi(a, idx) || stackval_references_loop_phi(b, idx)
        }
        StackVal::Eqz(a) => stackval_references_loop_phi(a, idx),
        _ => false,
    }
}

/// True if `val` transitively references `FrameSlotPhi(id, off)` — the slot
/// analogue of [`stackval_references_loop_phi`]. Decides whether a frame slot is
/// genuinely loop-carried (its new value depends on its own loop-head value).
fn stackval_references_frame_slot_phi(val: &StackVal, id: u32, off: i32) -> bool {
    match val {
        StackVal::FrameSlotPhi(i, o) => *i == id && *o == off,
        StackVal::BinOp(a, _, b) | StackVal::Compare(a, _, b) => {
            stackval_references_frame_slot_phi(a, id, off)
                || stackval_references_frame_slot_phi(b, id, off)
        }
        StackVal::Eqz(a) => stackval_references_frame_slot_phi(a, id, off),
        _ => false,
    }
}

/// True if `val` is a pure induction-counter update for the frame slot
/// `(id, off)`: exactly `slot ± constant`. A slot stepped like a counter is not
/// an accumulator worth promoting (and is almost never a real spill).
fn is_pure_counter_slot_update(val: &StackVal, id: u32, off: i32) -> bool {
    let StackVal::BinOp(a, BinOper::Add | BinOper::Sub, b) = val else {
        return false;
    };
    let is_self = |v: &StackVal| matches!(v, StackVal::FrameSlotPhi(i, o) if *i == id && *o == off);
    let is_const = |v: &StackVal| matches!(v, StackVal::I32(_) | StackVal::I64(_));
    (is_self(a) && is_const(b)) || (is_const(a) && is_self(b))
}

/// True if `val` is a pure induction-counter update for local `idx`: exactly
/// `idx ± constant` (`LoopPhi(idx) + C` / `C + LoopPhi(idx)` / `LoopPhi(idx) - C`).
/// A counted loop whose *only* loop-carried locals are pure counters does no
/// real work (it just steps an index that is dead after the loop) and is SDK
/// boilerplate the baseline already drops — so recovery skips it. A loop with a
/// genuine accumulator (`acc + i`, `acc + load`, ...) is not pure and is recovered.
fn is_pure_counter_update(val: &StackVal, idx: u32) -> bool {
    let StackVal::BinOp(a, BinOper::Add | BinOper::Sub, b) = val else {
        return false;
    };
    let is_self = |v: &StackVal| matches!(v, StackVal::LoopPhi(i) if *i == idx);
    let is_const = |v: &StackVal| matches!(v, StackVal::I32(_) | StackVal::I64(_));
    (is_self(a) && is_const(b)) || (is_const(a) && is_self(b))
}

/// True if `expr` is a plain integer literal. Loop-carried recovery only fires
/// when the pre-loop init is a literal: a named init (param, field access, ...)
/// would be renamed onto its source by variable-name propagation, turning the
/// recovered `let mut` into a mutation of an immutable binding (e.g. a function
/// parameter) that does not compile. A literal has no derivable name, so the
/// recovered variable keeps its `let mut var_N` declaration.
fn is_int_literal_expr(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::I32Literal(_)
            | SorobanExpr::I64Literal(_)
            | SorobanExpr::U32Literal(_)
            | SorobanExpr::U64Literal(_)
    )
}

/// True if `val` transitively references a `LetBinding` or `LoopPhi` — i.e. a
/// named variable (e.g. a recovered loop-carried local). Used to decide whether
/// the arithmetic shortcut may reduce a function to its stack top: a top that
/// names such a variable depends on emitted `let`/`let mut` statements and must
/// not be lifted out of them.
fn stackval_references_let_or_phi(val: &StackVal) -> bool {
    match val {
        StackVal::LetBinding(_) | StackVal::LoopPhi(_) => true,
        StackVal::BinOp(a, _, b) | StackVal::Compare(a, _, b) => {
            stackval_references_let_or_phi(a) || stackval_references_let_or_phi(b)
        }
        StackVal::Eqz(a) => stackval_references_let_or_phi(a),
        _ => false,
    }
}

fn stack_val_contains_unknown(val: &StackVal) -> bool {
    match val {
        StackVal::Unknown => true,
        StackVal::Compare(a, _, b) => {
            stack_val_contains_unknown(a) || stack_val_contains_unknown(b)
        }
        StackVal::BinOp(a, _, b) => stack_val_contains_unknown(a) || stack_val_contains_unknown(b),
        StackVal::Eqz(a) => stack_val_contains_unknown(a),
        StackVal::FrameSlot(_, _) => false,
        _ => false,
    }
}

fn expr_is_clean_arith(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Rem(a, b)
        // Comparisons appear in the round-up divide's `(a % b != 0)` inexact term;
        // they are pure and operate over clean-arith operands.
        | SorobanExpr::Eq(a, b)
        | SorobanExpr::Ne(a, b) => expr_is_clean_arith(a) && expr_is_clean_arith(b),
        SorobanExpr::CastAs { value, .. } | SorobanExpr::ValConvert { value, .. } => {
            expr_is_clean_arith(value)
        }
        SorobanExpr::Param(_)
        | SorobanExpr::Local(_)
        | SorobanExpr::NamedLocal(_)
        | SorobanExpr::I128Literal(_)
        | SorobanExpr::U128Literal(_)
        | SorobanExpr::I64Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U32Literal(_) => true,
        _ => false,
    }
}

/// True if every statement is a pure-arithmetic "husk" — none performs a real
/// side effect (storage write, event, auth, cross-contract invoke, prng, log).
/// Error-path panics, arithmetic, and control flow are allowed: they are the
/// Result-discriminant guards a checked-arith composite collapses to once its
/// happy-path value is recovered into the frame slot. Conservative — an
/// unrecognized effect keeps the statements (no drop).
fn stmts_are_pure_arith_husks(stmts: &[SorobanStmt]) -> bool {
    stmts.iter().all(stmt_is_pure_arith_husk)
}

fn stmt_is_pure_arith_husk(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => !expr_has_effect(e),
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            !expr_has_effect(value)
        }
        SorobanStmt::Return(None)
        | SorobanStmt::Break
        | SorobanStmt::Continue
        | SorobanStmt::Comment(_) => true,
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            !expr_has_effect(condition)
                && stmts_are_pure_arith_husks(then_body)
                && stmts_are_pure_arith_husks(else_body)
        }
        SorobanStmt::Match { scrutinee, arms } => {
            !expr_has_effect(scrutinee) && arms.iter().all(|a| stmts_are_pure_arith_husks(&a.body))
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => stmts_are_pure_arith_husks(body),
        SorobanStmt::For {
            start, end, body, ..
        } => !expr_has_effect(start) && !expr_has_effect(end) && stmts_are_pure_arith_husks(body),
    }
}

/// True if `expr` (transitively) performs a state-changing side effect that must
/// not be silently dropped. Storage *reads* and arithmetic are effect-free.
fn expr_has_effect(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::StorageSet { .. }
        | SorobanExpr::StorageRemove { .. }
        | SorobanExpr::StorageExtendTtl { .. }
        | SorobanExpr::ExtendInstanceAndCodeTtl { .. }
        | SorobanExpr::PublishEvent { .. }
        | SorobanExpr::RequireAuth(_)
        | SorobanExpr::RequireAuthForArgs { .. }
        | SorobanExpr::AuthorizeAsCurrContract(_)
        | SorobanExpr::InvokeContract { .. }
        | SorobanExpr::TryInvokeContract { .. }
        | SorobanExpr::Log(_)
        | SorobanExpr::PrngReseed(_)
        | SorobanExpr::PrngBytesNew(_)
        | SorobanExpr::PrngVecShuffle(_)
        | SorobanExpr::PrngU64InRange { .. } => true,
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Rem(a, b)
        | SorobanExpr::Eq(a, b)
        | SorobanExpr::Ne(a, b)
        | SorobanExpr::Lt(a, b)
        | SorobanExpr::Le(a, b)
        | SorobanExpr::Gt(a, b)
        | SorobanExpr::Ge(a, b)
        | SorobanExpr::And(a, b)
        | SorobanExpr::Or(a, b) => expr_has_effect(a) || expr_has_effect(b),
        SorobanExpr::Not(a)
        | SorobanExpr::Some(a)
        | SorobanExpr::PanicWithError(a)
        | SorobanExpr::ErrorFromCode(a)
        | SorobanExpr::CastAs { value: a, .. }
        | SorobanExpr::ValConvert { value: a, .. } => expr_has_effect(a),
        SorobanExpr::MethodCall { object, args, .. } => {
            expr_has_effect(object) || args.iter().any(expr_has_effect)
        }
        SorobanExpr::FieldAccess { object, .. } => expr_has_effect(object),
        SorobanExpr::TupleConstruct(items) | SorobanExpr::VecConstruct(items) => {
            items.iter().any(expr_has_effect)
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            fields.iter().any(|(_, v)| expr_has_effect(v))
        }
        SorobanExpr::EnumConstruct { fields, .. } => fields.iter().any(expr_has_effect),
        // Storage reads (`StorageGet`/`StorageHas`) are idempotent; all remaining
        // variants are leaves or pure projections.
        _ => false,
    }
}

/// True if `val` is a Soroban Val tag comparison: `(v & 0xFF) <cmp> TAG`.
///
/// These are the SDK's argument type-validation checks. A multi-guard validation
/// preamble keeps them as explicit `if ... { panic!() }` guards, but a lone
/// `block { tag-check; br_if; <value-returning body> }` would otherwise wrap the
/// body's tail in `if tag == X { ... }` and drop the return value. Treating a lone
/// tag check as a pass-through (like an unknown condition) keeps such bodies intact.
fn is_tag_check_condition(val: &StackVal) -> bool {
    let StackVal::Compare(a, _, b) = val else {
        return false;
    };
    (matches!(recognize_val_shape(a), Some(ValShape::TagOf(_))) && to_u64(b).is_some())
        || (matches!(recognize_val_shape(b), Some(ValShape::TagOf(_))) && to_u64(a).is_some())
}

/// Numeric Val tag uniquely determined by a declared spec param type — the
/// lifter-level sibling of the optimizer's `unique_val_tag` (which maps to tag
/// *names* for already-lifted `get_tag` comparisons). Only types whose Val
/// encoding admits exactly one tag qualify; small/object-ambiguous types
/// (u64, i128, Symbol, bool, …) return `None`.
fn unique_numeric_val_tag(td: &ScSpecTypeDef) -> Option<u64> {
    Some(match td {
        ScSpecTypeDef::Address => TAG_ADDRESS_OBJECT,
        ScSpecTypeDef::Vec(_) => TAG_VEC_OBJECT,
        ScSpecTypeDef::Map(_) => TAG_MAP_OBJECT,
        ScSpecTypeDef::Bytes | ScSpecTypeDef::BytesN(_) => TAG_BYTES_OBJECT,
        ScSpecTypeDef::String => TAG_STRING_OBJECT,
        ScSpecTypeDef::U32 => TAG_U32,
        ScSpecTypeDef::I32 => TAG_I32,
        _ => return None,
    })
}

/// Recognize the multi-param SDK marshalling guard computation preceding an
/// entrypoint `if`: `((p_a & 255) != T_a) | ((p_b & 255) != T_b) | …; i32.eqz`,
/// i.e. "all params carry their declared Val tag". The `i32.or` collapses the
/// composite to `Unknown` on the value stack (its leaves are unrecoverable
/// there), so this matches the *raw instruction* window instead. True only when
/// EVERY or-ed leaf is `local.get <param>; i64.const 255; i64.and; i64.const
/// <tag>; i64.ne` with `<tag>` the tag uniquely determined by that param's
/// declared spec type ([`unique_numeric_val_tag`]) — the whole composite is then
/// tautological for host-validated arguments, the same rationale as the
/// optimizer's `fold_tautological_tag_guards`. Requires ≥ 2 leaves: the
/// single-check form lifts cleanly as `ValTag(Param)` and stays on the existing
/// paths.
fn is_param_tag_guard_composite(
    preceding: &[super::structurize::StructuredBlock],
    params: &[FnParam],
    num_wasm_params: u32,
) -> bool {
    use crate::wasm::ir::WasmInstr;
    // Reversed instruction window ending at the `if`'s condition; stops at the
    // first non-instruction sibling (frame-setup noise before the guard is
    // simply never reached by the backward match).
    let instrs: Vec<&WasmInstr> = preceding
        .iter()
        .rev()
        .map_while(|b| match b {
            super::structurize::StructuredBlock::Instruction(i) => Some(i),
            _ => None,
        })
        .collect();

    let mut pos = 0;
    if !matches!(instrs.first(), Some(WasmInstr::I32Eqz)) {
        return false;
    }
    pos += 1;

    // Backward shape: Eqz, Or, G_k, Or, G_{k-1}, …, Or, G_2, G_1 where each
    // reversed group G is [I64Ne, I64Const(tag), I64And, I64Const(255), LocalGet(p)].
    let mut groups = 0usize;
    loop {
        let saw_or = matches!(instrs.get(pos), Some(WasmInstr::I32Or));
        if saw_or {
            pos += 1;
        }
        match (
            instrs.get(pos),
            instrs.get(pos + 1),
            instrs.get(pos + 2),
            instrs.get(pos + 3),
            instrs.get(pos + 4),
        ) {
            (
                Some(WasmInstr::I64Ne),
                Some(WasmInstr::I64Const(tag)),
                Some(WasmInstr::I64And),
                Some(WasmInstr::I64Const(255)),
                Some(WasmInstr::LocalGet(p)),
            ) => {
                if *p >= num_wasm_params {
                    return false;
                }
                let Some(param) = params.get(*p as usize) else {
                    return false;
                };
                if unique_numeric_val_tag(&param.type_def) != Some(*tag as u64) {
                    return false;
                }
                pos += 5;
                groups += 1;
            }
            _ => return false,
        }
        if !saw_or {
            break;
        }
    }
    groups >= 2
}

/// Narrow I32Literal(0/1) to BoolLiteral when the function's return type is bool.
fn narrow_to_bool(expr: SorobanExpr, return_type: &Option<ScSpecTypeDef>) -> SorobanExpr {
    if matches!(return_type, Some(ScSpecTypeDef::Bool)) {
        match &expr {
            SorobanExpr::I32Literal(0) => return SorobanExpr::BoolLiteral(false),
            SorobanExpr::I32Literal(1) => return SorobanExpr::BoolLiteral(true),
            _ => {}
        }
    }
    expr
}

/// Type alias for frame slot storage: maps (frame_id, byte_offset) to stored StackVal.
type FrameSlotMap = HashMap<(u32, i32), StackVal>;

/// Type alias for the dynamic (loop-indexed) frame slot side table: maps
/// `(frame_id, symbolic_term, static_base)` to the stored `StackVal`.
type DynamicSlotMap = HashMap<(u32, SymTerm, i32), StackVal>;

/// Type alias for the append-only store journal: every REAL store to a static
/// `(frame_id, offset)` slot, in program order (see `LiftContext::slot_defs`).
type SlotDefJournal = HashMap<(u32, i32), Vec<StackVal>>;

/// One entry of the ordered static-slot write log (see
/// `LiftContext::slot_write_log`), in simulation order.
#[derive(Clone, Debug)]
struct SlotWrite {
    key: (u32, i32),
    /// What the slot held before this store (the join's net-no-op check).
    prev: Option<StackVal>,
    new: StackVal,
    /// The REAL store instruction's width (`i32.store` = 4, `i64.store` = 8,
    /// sub-word = 1/2) — the frame-descriptor key fold seeds its evaluator's
    /// exact-width memory from it.
    width: u32,
    /// `inline_depth` of the storing context. The IfElse join poison
    /// segments arms over SAME-DEPTH entries only, so a caller's join never
    /// treats an inlined helper's internal stores as its own then-arm writes
    /// (poisoning them degraded working getter recoveries when the log
    /// became shared across `lift_inline_call`); the frame-descriptor key
    /// fold reads all depths (a callee legitimately re-derives its caller's
    /// descriptor through a passed pointer).
    depth: u32,
}

/// Type alias for the ordered static-slot write log.
type SlotWriteLog = Vec<SlotWrite>;

/// Convert a stack value to a SorobanExpr, decoding packed Soroban Val constants.
///
/// When `frame_slots` is provided, FrameSlot values are resolved by looking up
/// the stored value in the frame slot map (populated by I64Store/I32Store handlers).
fn stack_val_to_expr(
    val: &StackVal,
    params: &[FnParam],
    registry: &TypeRegistry,
    frame_slots: Option<&FrameSlotMap>,
) -> SorobanExpr {
    // `visiting` records the frame slots on the active resolution path so a
    // self-referential slot is detected with path-local state instead of a
    // thread-local set.
    let mut visiting: Vec<(u32, i32)> = Vec::new();
    stack_val_to_expr_inner(val, params, registry, frame_slots, &mut visiting)
}

#[allow(clippy::only_used_in_recursion)]
fn stack_val_to_expr_inner(
    val: &StackVal,
    params: &[FnParam],
    registry: &TypeRegistry,
    frame_slots: Option<&FrameSlotMap>,
    visiting: &mut Vec<(u32, i32)>,
) -> SorobanExpr {
    match val {
        StackVal::I32(v) => SorobanExpr::I32Literal(*v),
        StackVal::I64(v) => try_decode_val(*v, registry),
        StackVal::Param(name) => SorobanExpr::Param(name.clone()),
        StackVal::WasmParam(idx) => SorobanExpr::Local(*idx),
        StackVal::HostCallResult(expr) => (**expr).clone(),
        // A lone 128-bit limb that survives to expr conversion (i.e. it was not
        // re-paired into the whole value): lower to the source value's expression.
        // The common surviving case is a sign/zero check on the hi limb, which is
        // semantically a check on the whole 128-bit value.
        StackVal::I128Limb { value, .. } => {
            stack_val_to_expr_inner(value, params, registry, frame_slots, visiting)
        }
        StackVal::BinOp(a, op, b) => {
            match op {
                BinOper::Add | BinOper::Sub | BinOper::Mul => {
                    // Use raw-int conversion for children: constants inside stripped arithmetic
                    // are raw integers, not Val-encoded (e.g., the `2` in `b * 2`).
                    let a_expr =
                        stack_val_to_arith_expr_inner(a, params, registry, frame_slots, visiting);
                    let b_expr =
                        stack_val_to_arith_expr_inner(b, params, registry, frame_slots, visiting);
                    match op {
                        BinOper::Add => SorobanExpr::Add(Box::new(a_expr), Box::new(b_expr)),
                        BinOper::Sub => SorobanExpr::Sub(Box::new(a_expr), Box::new(b_expr)),
                        BinOper::Mul => SorobanExpr::Mul(Box::new(a_expr), Box::new(b_expr)),
                        _ => unreachable!(),
                    }
                }
                // Val-encode artifacts — try strip_val_encode to recover the inner value.
                // If that fails (Unknown), fall back to arithmetic for Shl or UnknownVal for Or.
                BinOper::Shl | BinOper::Or => {
                    let reconstructed =
                        StackVal::BinOp(Box::new((**a).clone()), *op, Box::new((**b).clone()));
                    match strip_val_encode(reconstructed) {
                        StackVal::Unknown => {
                            // Shl with small shift amounts (1-3) is likely real arithmetic (multiply
                            // by power of 2), not Val encoding (which uses shift 8 or 32).
                            if *op == BinOper::Shl
                                && let StackVal::I64(shift) = **b
                                && (1..=3).contains(&shift)
                            {
                                let a_expr = stack_val_to_arith_expr_inner(
                                    a,
                                    params,
                                    registry,
                                    frame_slots,
                                    visiting,
                                );
                                let multiplier = 1i64 << shift;
                                return SorobanExpr::Mul(
                                    Box::new(a_expr),
                                    Box::new(SorobanExpr::I64Literal(multiplier)),
                                );
                            }
                            SorobanExpr::UnknownVal
                        }
                        ref other => {
                            stack_val_to_expr_inner(other, params, registry, frame_slots, visiting)
                        }
                    }
                }
                // Tag extraction `v & 0xFF` → `v.get_tag()`. Anything else AND-shaped
                // wasn't a recognized Val pattern, so it stays unknown.
                BinOper::And => {
                    if to_u64(b) == Some(0xFF) {
                        SorobanExpr::ValTag(Box::new(stack_val_to_expr_inner(
                            a,
                            params,
                            registry,
                            frame_slots,
                            visiting,
                        )))
                    } else {
                        SorobanExpr::UnknownVal
                    }
                }
            }
        }
        StackVal::Compare(a, op, b) => {
            // Use arithmetic conversion for comparison operands: I64 constants
            // like 0 should stay as I64Literal(0), not decode to BoolLiteral(false)
            // via try_decode_val. The host-call result on one side still goes through
            // stack_val_to_expr correctly (HostCallResult delegates to expr.clone()).
            //
            // Val threshold decoding: when comparing Val-encoded values with i64.gt_u,
            // the SDK uses (n << 32) | 0xFFFFFFFF as a threshold constant. This means
            // "is the Val's upper 32 bits > n", which for U32 Vals equals "decoded > n".
            // Decode these threshold constants to produce readable comparisons.
            // Tag check: `(v & 0xFF) <cmp> TAG` → `v.get_tag() <cmp> Tag::Name`.
            let (a_expr, b_expr) = if let Some(pair) =
                lower_tag_comparison(a, b, params, registry, frame_slots, visiting)
            {
                pair
            } else {
                match (a.as_ref(), b.as_ref()) {
                    (_, StackVal::I64(v)) if is_val_threshold_constant(*v as u64) => {
                        let decoded = (*v as u64) >> 32;
                        let a_e =
                            stack_val_to_expr_inner(a, params, registry, frame_slots, visiting);
                        (a_e, SorobanExpr::I64Literal(decoded as i64))
                    }
                    (StackVal::I64(v), _) if is_val_threshold_constant(*v as u64) => {
                        let decoded = (*v as u64) >> 32;
                        let b_e =
                            stack_val_to_expr_inner(b, params, registry, frame_slots, visiting);
                        (SorobanExpr::I64Literal(decoded as i64), b_e)
                    }
                    _ => {
                        let a_e = stack_val_to_arith_expr_inner(
                            a,
                            params,
                            registry,
                            frame_slots,
                            visiting,
                        );
                        let b_e = stack_val_to_arith_expr_inner(
                            b,
                            params,
                            registry,
                            frame_slots,
                            visiting,
                        );
                        (a_e, b_e)
                    }
                }
            };
            match op {
                CmpOp::Eq => SorobanExpr::Eq(Box::new(a_expr), Box::new(b_expr)),
                CmpOp::Ne => SorobanExpr::Ne(Box::new(a_expr), Box::new(b_expr)),
                CmpOp::LtS | CmpOp::LtU => SorobanExpr::Lt(Box::new(a_expr), Box::new(b_expr)),
                CmpOp::GtS | CmpOp::GtU => SorobanExpr::Gt(Box::new(a_expr), Box::new(b_expr)),
                CmpOp::LeS | CmpOp::LeU => SorobanExpr::Le(Box::new(a_expr), Box::new(b_expr)),
                CmpOp::GeS | CmpOp::GeU => SorobanExpr::Ge(Box::new(a_expr), Box::new(b_expr)),
            }
        }
        StackVal::Eqz(a) => {
            let a_expr = stack_val_to_expr_inner(a, params, registry, frame_slots, visiting);
            // If the inner expression is already a comparison, use Not to avoid
            // chained comparison operators (which Rust rejects)
            match &a_expr {
                SorobanExpr::Eq(_, _)
                | SorobanExpr::Ne(_, _)
                | SorobanExpr::Lt(_, _)
                | SorobanExpr::Le(_, _)
                | SorobanExpr::Gt(_, _)
                | SorobanExpr::Ge(_, _) => SorobanExpr::Not(Box::new(a_expr)),
                _ => SorobanExpr::Eq(Box::new(a_expr), Box::new(SorobanExpr::I32Literal(0))),
            }
        }
        StackVal::LetBinding(idx) => SorobanExpr::Local(*idx),
        StackVal::LoopPhi(idx) => SorobanExpr::Local(*idx),
        // Analysis-only marker; should never reach codegen. Degrade safely.
        StackVal::FrameSlotPhi(_, _) => SorobanExpr::UnknownVal,
        StackVal::OptionDecodeDisc => SorobanExpr::UnknownVal,
        StackVal::FrameSlot(id, offset) => {
            // Try to resolve FrameSlot by looking up what was stored at this location.
            // Only static offsets key `frame_slots`; a dynamic (loop-indexed) address
            // has no single stored expression and degrades to UnknownVal.
            if offset.is_static()
                && let Some(slots) = frame_slots
                && let Some(stored) = slots.get(&(*id, offset.base))
            {
                // Avoid infinite recursion: don't recurse into FrameSlots or Unknown
                if !matches!(
                    stored,
                    StackVal::FrameSlot(_, _) | StackVal::FrameBase(_) | StackVal::Unknown
                ) {
                    // The stored value may transitively reference this same slot
                    // (e.g. a Val-encoded BinOp embedding it), which the matches!
                    // check above cannot see. `visiting` records the slots on the
                    // current resolution path; a revisit means a cycle, so degrade
                    // to UnknownVal instead of recursing forever.
                    let key = (*id, offset.base);
                    if visiting.contains(&key) {
                        // Genuine self-referential slot: report it precisely
                        // (which slot closed the cycle) rather than as an
                        // anonymous unknown.
                        return SorobanExpr::CyclicSlot {
                            frame_id: *id,
                            offset: offset.base,
                        };
                    }
                    visiting.push(key);
                    let resolved =
                        stack_val_to_expr_inner(stored, params, registry, frame_slots, visiting);
                    visiting.pop();
                    return resolved;
                }
            }
            SorobanExpr::UnknownVal
        }
        StackVal::FrameBase(_) | StackVal::StackPtrRef => SorobanExpr::UnknownVal,
        StackVal::Unknown => SorobanExpr::UnknownVal,
    }
}

/// Convert a StackVal to a SorobanExpr in an arithmetic BinOp context.
///
/// For I32/I64 constants used as direct children of arithmetic BinOps, return them as
/// raw integer literals rather than going through `try_decode_val`. Constants like `2`
/// (a multiplication factor) or `32` (a shift amount) appear as `StackVal::I64(2)` and
/// would otherwise decode to Void/U32(0) via `try_decode_val`.
fn stack_val_to_arith_expr(
    val: &StackVal,
    params: &[FnParam],
    registry: &TypeRegistry,
    frame_slots: Option<&FrameSlotMap>,
) -> SorobanExpr {
    let mut visiting: Vec<(u32, i32)> = Vec::new();
    stack_val_to_arith_expr_inner(val, params, registry, frame_slots, &mut visiting)
}

#[allow(clippy::only_used_in_recursion)]
fn stack_val_to_arith_expr_inner(
    val: &StackVal,
    params: &[FnParam],
    registry: &TypeRegistry,
    frame_slots: Option<&FrameSlotMap>,
    visiting: &mut Vec<(u32, i32)>,
) -> SorobanExpr {
    match val {
        StackVal::I32(v) => SorobanExpr::I32Literal(*v),
        StackVal::I64(v) => SorobanExpr::I64Literal(*v),
        // Void-returning host calls should not participate in arithmetic.
        // Branch-sequential execution can leak extend_ttl / StorageExtendTtl
        // return values (Void tag = 2) into arithmetic operand positions.
        // Replace with 0 so constant folding eliminates the no-op (x - 0 → x).
        StackVal::HostCallResult(expr) if is_void_returning_expr(expr) => {
            cov_mark::hit!(void_return_guard_in_arith);
            SorobanExpr::I64Literal(0)
        }
        _ => stack_val_to_expr_inner(val, params, registry, frame_slots, visiting),
    }
}

/// Check if a u64 constant is a "Val threshold" used in SDK comparisons.
///
/// The SDK compares Val-encoded values using `i64.gt_u` with threshold constants
/// of the form `(n << 32) | 0xFFFFFFFF`. This constant sits between U32(n) and
/// U32(n+1) in unsigned ordering, so `val > threshold` iff `decoded_val > n`.
///
/// Example: `vec_len(v) > 0x0AFFFFFFFF` checks if length > 10.
fn is_val_threshold_constant(v: u64) -> bool {
    // Low 32 bits must be all 1s, and upper 32 bits must be a small number
    (v & 0xFFFFFFFF) == 0xFFFFFFFF && (v >> 32) <= 1000
}

/// Check if an expression is a void-returning host call (extend_ttl variants).
/// These always return the Void Val (0x02), not a meaningful value.
fn is_void_returning_expr(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::ExtendInstanceAndCodeTtl { .. } | SorobanExpr::StorageExtendTtl { .. }
    )
}

/// True if `expr` is — or transitively wraps — a cross-contract invoke
/// (`InvokeContract` / `TryInvokeContract`). Helper sret callees often store
/// the invoke result wrapped in `ValConvert` / `MethodCall` / `FieldAccess`, so
/// the discriminant-modeling gate has to look past those layers.
fn expr_contains_invoke_contract(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::InvokeContract { .. } | SorobanExpr::TryInvokeContract { .. } => true,
        SorobanExpr::ValConvert { value: inner, .. }
        | SorobanExpr::CastAs { value: inner, .. }
        | SorobanExpr::FieldAccess { object: inner, .. }
        | SorobanExpr::ValTag(inner)
        | SorobanExpr::SretResult(inner)
        | SorobanExpr::Not(inner)
        | SorobanExpr::ErrorFromCode(inner) => expr_contains_invoke_contract(inner),
        SorobanExpr::MethodCall { object, args, .. } => {
            expr_contains_invoke_contract(object) || args.iter().any(expr_contains_invoke_contract)
        }
        _ => false,
    }
}

/// Try to decode a 64-bit value as a packed Soroban Val.
///
/// Soroban uses 64-bit "Val" values with a tag in the low byte:
/// - 0x00 = False, 0x01 = True, 0x02 = Void
/// - 0x03 = Error
/// - 0x04 = U32 (value << 32), 0x05 = I32 (value << 32)
/// - 0x06 = U64Small (value << 8), 0x07 = I64Small (value << 8)
/// - 0x0e = SymbolSmall (6-bit chars packed in upper bits)
/// - 0x40..=0x7f = Object types (need host call to extract)
fn try_decode_val(v: i64, registry: &TypeRegistry) -> SorobanExpr {
    let val = v as u64;
    let tag = val & 0xff;

    match tag {
        TAG_FALSE => SorobanExpr::BoolLiteral(false),
        TAG_TRUE => SorobanExpr::BoolLiteral(true),
        TAG_VOID => SorobanExpr::Void,
        TAG_ERROR => {
            // Error Val: bits 32-63 = contract error code, bits 8-15 = error type (0=Contract)
            let error_code = (val >> 32) as u32;
            let (error_type, variant_name) = registry
                .lookup_error_variant(error_code)
                .map(|(en, vn)| (Some(en), Some(vn)))
                .unwrap_or((None, None));
            SorobanExpr::ContractError {
                error_code,
                error_type,
                variant_name,
            }
        }
        TAG_U32 => {
            // U32 - value in upper 32 bits (major field)
            let value = (val >> 32) as u32;
            SorobanExpr::U32Literal(value)
        }
        TAG_I32 => {
            // I32 - value in upper 32 bits (major field)
            let value = (val >> 32) as i32;
            SorobanExpr::I32Literal(value)
        }
        TAG_U64_SMALL => {
            // U64Small
            let value = val >> 8;
            SorobanExpr::U64Literal(value)
        }
        TAG_I64_SMALL => {
            // I64Small
            let value = (val >> 8) as i64;
            SorobanExpr::I64Literal(value)
        }
        TAG_SYMBOL_SMALL => {
            // SymbolSmall
            if let Some(sym) = crate::wasm::data::DataSection::decode_symbol_val(val) {
                SorobanExpr::SymbolLiteral(sym)
            } else {
                SorobanExpr::I64Literal(v)
            }
        }
        // Object tags (0x40..=0x7f) carry a 32-bit handle, not an inline value, so
        // a constant Val with an object tag cannot be decoded without the host.
        // Storage type discriminants and other raw small ints also land here.
        _ if is_object_tag(tag) => SorobanExpr::I64Literal(v),
        _ => {
            // If it looks like a raw small value with no special tag, return as-is
            SorobanExpr::I64Literal(v)
        }
    }
}

/// Extract a U32 value from a raw StackVal before SorobanExpr conversion.
/// Handles: `I32(v)`, `I64(Val-encoded)`, `BinOp((x << 32) | TAG_U32)` patterns.
/// This is needed because `stack_val_to_expr` converts Val-encode BinOps to UnknownVal,
/// losing the encoded value.
fn extract_u32_from_stack_val(val: &StackVal) -> Option<u32> {
    match val {
        StackVal::I32(v) => Some(*v as u32),
        StackVal::I64(v) => {
            let val = *v as u64;
            if (val & 0xff) == TAG_U32 {
                Some((val >> 32) as u32)
            } else {
                None
            }
        }
        // Pattern: (x << 32) | 4  — Val-encoding of u32 (centralized recognition).
        StackVal::BinOp(..) => match recognize_val_shape(val) {
            Some(ValShape::Construct {
                payload,
                shift: 32,
                tag: TAG_U32,
            }) => match payload {
                StackVal::I32(v) => Some(v as u32),
                StackVal::I64(v) => Some(v as u32),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// Extract a FrameSlot (frame_id, base_offset) from a StackVal, unwrapping
/// Val-encoding if present.
///
/// Handles:
/// - Direct `FrameSlot(id, offset)`
/// - Val-encoded: `(FrameSlot << 32) | 4` (the BinOp tree from u32 Val encoding)
fn extract_frame_slot_from_stack_val(val: &StackVal) -> Option<(u32, i32)> {
    match val {
        StackVal::FrameSlot(id, offset) => Some((*id, offset.base)),
        // Val-encoded: (FrameSlot << 32) | 4 (centralized recognition).
        StackVal::BinOp(..) => match recognize_val_shape(val) {
            Some(ValShape::Construct {
                payload: StackVal::FrameSlot(id, offset),
                shift: 32,
                tag: TAG_U32,
            }) => Some((id, offset.base)),
            _ => None,
        },
        _ => None,
    }
}

/// Extract a U32 value from a SorobanExpr.
/// Handles U32Literal directly, and I64Literal via Val decoding (tag 0x04 = U32).
/// U32Val layout: bits 63-32 = value (major), bits 31-8 = 0 (minor), bits 7-0 = tag (0x04).
pub(crate) fn extract_u32_from_expr(expr: &SorobanExpr) -> Option<u32> {
    match expr {
        SorobanExpr::U32Literal(v) => Some(*v),
        SorobanExpr::I32Literal(v) => Some(*v as u32),
        SorobanExpr::I64Literal(v) => {
            // Try to decode as a Soroban Val U32
            let val = *v as u64;
            let tag = val & 0xff;
            if tag == TAG_U32 {
                Some((val >> 32) as u32)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Check if a function body contains a simple arithmetic pattern (add, sub, etc.)
fn has_arithmetic_pattern(body: &[crate::wasm::ir::WasmInstr]) -> bool {
    use crate::wasm::ir::WasmInstr;
    body.iter().any(|instr| {
        matches!(
            instr,
            WasmInstr::I64Add
                | WasmInstr::I64Sub
                | WasmInstr::I64Mul
                | WasmInstr::I32Add
                | WasmInstr::I32Sub
                | WasmInstr::I32Mul
        )
    })
}

/// Generate a simple arithmetic function body.
fn generate_arithmetic_body(
    params: &[FnParam],
    _return_type: &Option<ScSpecTypeDef>,
) -> Vec<SorobanStmt> {
    if params.len() == 2 {
        let a = SorobanExpr::Param(params[0].name.clone());
        let b = SorobanExpr::Param(params[1].name.clone());
        vec![SorobanStmt::Return(Some(SorobanExpr::Add(
            Box::new(a),
            Box::new(b),
        )))]
    } else {
        Vec::new()
    }
}

// --- Checked-arithmetic recovery (`a.checked_add/sub(b).ok_or(<err>)`) ---------
//
// The SDK compiles `a.checked_add(b).ok_or(E)` to: a wrapping `i{64,32}.add`,
// an unsigned carry test `(a+b) <u a`, and a branch that returns the preloaded
// `Err` Val on overflow. The arithmetic shortcut in `lift_function_body`
// collapses all of that to the bare sum, so the function decompiles to the
// overflow-UNSAFE `Ok(a + b)` (which traps under `overflow-checks`). These
// helpers restore the checked form, reading the real error code from the
// bytecode (no fabrication). Gating is deliberately rigid; any mismatch returns
// `None`, leaving the shortcut's existing output untouched.

/// Width (bits) of a `Result<int, E>` ok-type the recovery handles (`u32`/`i32`
/// → 32, `u64`/`i64` → 64), paired with the declared error type. `None` for any
/// other return shape.
fn checked_result_shape(return_type: &Option<ScSpecTypeDef>) -> Option<(u32, ScSpecTypeDef)> {
    let Some(ScSpecTypeDef::Result(r)) = return_type else {
        return None;
    };
    let width = match &*r.ok_type {
        ScSpecTypeDef::U64 | ScSpecTypeDef::I64 => 64,
        ScSpecTypeDef::U32 | ScSpecTypeDef::I32 => 32,
        _ => return None,
    };
    Some((width, (*r.error_type).clone()))
}

/// The single contract-error `Val` constant the SDK preloads on the error path,
/// returned as its contract error code. `None` if there is no Error-tagged
/// constant, or more than one distinct one (ambiguous → bail).
///
/// An Error `Val` carries the error *type* in bits 8–15 (0 = Contract) and the
/// code in bits 32–63. Only `ScErrorType::Contract` constants are real
/// `#[contracterror]` codes; a non-Contract error (host/WasmVm/etc.) must NOT be
/// mistaken for a contract code, so it is skipped (and if it were the only
/// Error-tagged const, recovery bails — `None`).
fn find_checked_error_code(body: &[crate::wasm::ir::WasmInstr]) -> Option<u32> {
    use crate::wasm::ir::WasmInstr;
    let mut found: Option<u32> = None;
    for instr in body {
        if let WasmInstr::I64Const(c) = instr {
            let v = *c as u64;
            if v & 0xff == TAG_ERROR && (v >> 8) & 0xff == 0 {
                let code = (v >> 32) as u32;
                match found {
                    Some(prev) if prev != code => return None,
                    _ => found = Some(code),
                }
            }
        }
    }
    found
}

/// True if the body contains the width-appropriate unsigned-`<` the SDK emits for
/// an overflow/underflow guard.
fn has_unsigned_lt(body: &[crate::wasm::ir::WasmInstr], width: u32) -> bool {
    use crate::wasm::ir::WasmInstr;
    body.iter().any(|i| {
        if width == 64 {
            matches!(i, WasmInstr::I64LtU)
        } else {
            matches!(i, WasmInstr::I32LtU)
        }
    })
}

/// Contract-error expression for a recovered `.ok_or(..)`, rendered to match the
/// function's declared `Result<_, E>` error type so the result type-checks —
/// mirrors the return-type rendering in `codegen::module`. Reads the real code
/// from the WASM; never fabricates an enum/variant the spec doesn't carry.
fn checked_error_expr(registry: &TypeRegistry, err_type: &ScSpecTypeDef, code: u32) -> SorobanExpr {
    let enum_name = match err_type {
        ScSpecTypeDef::Udt(u) => u.name.to_utf8_string().ok(),
        // Raw `soroban_sdk::Error`: codegen substitutes the sole error enum when
        // there is exactly one, else leaves it as `soroban_sdk::Error`. With two
        // or more enums we deliberately do NOT guess a variant via
        // `lookup_error_variant` (first-match across all enums): two enums can
        // share a code (e.g. both `=1`), so a guess would fabricate the wrong
        // `E::Variant`. The declared type is the opaque `Error`, so the honest,
        // type-correct rendering is `Error::from_contract_error(code)` below.
        ScSpecTypeDef::Error if registry.error_enums.len() == 1 => {
            registry.error_enums.keys().next().cloned()
        }
        _ => None,
    };
    match enum_name {
        Some(name) => {
            let variant_name = registry.get_error_enum(&name).and_then(|e| {
                e.cases
                    .iter()
                    .find(|c| c.value == code)
                    .and_then(|c| c.name.to_utf8_string().ok())
            });
            SorobanExpr::ContractError {
                error_code: code,
                error_type: Some(name),
                variant_name,
            }
        }
        None => SorobanExpr::ContractError {
            error_code: code,
            error_type: None,
            variant_name: None,
        },
    }
}

/// Build the recovered tail expression `a.checked_<op>(b).ok_or(<err>)`.
fn checked_arith_tail(method: &str, a: String, b: String, err: SorobanExpr) -> SorobanStmt {
    SorobanStmt::Expr(SorobanExpr::MethodCall {
        object: Box::new(SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::Param(a)),
            method: method.to_string(),
            args: vec![SorobanExpr::Param(b)],
        }),
        method: "ok_or".to_string(),
        args: vec![err],
    })
}

/// Recover `a.checked_add(b)`/`a.checked_sub(b)` `.ok_or(<err>)` from the WASM
/// body at the arithmetic-shortcut fallback (where `generate_arithmetic_body`
/// would otherwise hard-code an overflow-unsafe `Ok(a + b)`, even for a
/// subtraction). Gated on a `Result<int, E>` return over two params, the SDK
/// overflow guard (unsigned-`<`), and a single Error-tagged constant.
///
/// - **sub**: read both op and operand order from the bytecode — the unique
///   width-appropriate `LocalGet(i); LocalGet(j); Sub` over two distinct param
///   slots (decoded in place), confirmed by a borrow guard
///   `LocalGet(i); LocalGet(j); LtU` with the same operands/order (`a < b`). So
///   `b.checked_sub(a)` is recovered correctly too.
/// - **add**: commutative, so operands are `params[0], params[1]` — the same
///   operand assumption `generate_arithmetic_body` already makes for `Ok(a + b)`,
///   now made overflow-safe.
fn recover_checked_arith_from_body(
    body: &[crate::wasm::ir::WasmInstr],
    params: &[FnParam],
    return_type: &Option<ScSpecTypeDef>,
    registry: &TypeRegistry,
) -> Option<SorobanStmt> {
    use crate::wasm::ir::WasmInstr;
    if params.len() != 2 {
        return None;
    }
    let (width, err_type) = checked_result_shape(return_type)?;
    // Both forms require the SDK overflow/underflow guard and a real error const.
    if !has_unsigned_lt(body, width) {
        return None;
    }
    let code = find_checked_error_code(body)?;
    let nparams = params.len() as u32;
    let is_sub = |o: &WasmInstr| {
        if width == 64 {
            matches!(o, WasmInstr::I64Sub)
        } else {
            matches!(o, WasmInstr::I32Sub)
        }
    };
    let is_add = |o: &WasmInstr| {
        if width == 64 {
            matches!(o, WasmInstr::I64Add)
        } else {
            matches!(o, WasmInstr::I32Add)
        }
    };
    let is_lt = |o: &WasmInstr| {
        if width == 64 {
            matches!(o, WasmInstr::I64LtU)
        } else {
            matches!(o, WasmInstr::I32LtU)
        }
    };

    // Subtraction: read operands + order from the bytecode (non-commutative).
    if let Some((i, j)) = body.windows(3).find_map(|w| match w {
        [WasmInstr::LocalGet(i), WasmInstr::LocalGet(j), o]
            if is_sub(o) && *i < nparams && *j < nparams && i != j =>
        {
            Some((*i, *j))
        }
        _ => None,
    }) {
        // Borrow guard with the same operands in the same order (`a < b`).
        let has_borrow = body.windows(3).any(|w| {
            matches!(w, [WasmInstr::LocalGet(a), WasmInstr::LocalGet(b), o] if *a == i && *b == j && is_lt(o))
        });
        if has_borrow {
            cov_mark::hit!(checked_arith_recovered);
            return Some(checked_arith_tail(
                "checked_sub",
                params[i as usize].name.clone(),
                params[j as usize].name.clone(),
                checked_error_expr(registry, &err_type, code),
            ));
        }
    }

    // Addition: commutative — operands are the two params (the same assumption
    // the plain-`Ok(a + b)` fallback already makes), now overflow-safe.
    if body.iter().any(is_add) {
        cov_mark::hit!(checked_arith_recovered);
        return Some(checked_arith_tail(
            "checked_add",
            params[0].name.clone(),
            params[1].name.clone(),
            checked_error_expr(registry, &err_type, code),
        ));
    }

    None
}

#[cfg(test)]
mod tests {
    //! Scaffold-level tests for lifter helpers. The full lifter is exercised
    //! end-to-end by the integration suite; this module establishes a place
    //! for narrow unit tests of attacker-surface helpers so future regressions
    //! land here first.
    use super::*;

    // ----- frame_slot_key (Phase 4.1) ----------------------------------

    #[test]
    fn frame_slot_key_handles_zero_offset() {
        assert_eq!(frame_slot_key(100, 0), Some(100));
        assert_eq!(frame_slot_key(0, 0), Some(0));
    }

    #[test]
    fn frame_slot_key_handles_small_positive_offset() {
        assert_eq!(frame_slot_key(0, 16), Some(16));
        assert_eq!(frame_slot_key(-16, 16), Some(0));
        assert_eq!(frame_slot_key(100, 200), Some(300));
    }

    #[test]
    fn frame_slot_key_returns_none_for_max_u32_offset() {
        // u32::MAX is a valid WASM memory offset but cannot fit in i32 alongside
        // any non-negative base — the slot tracker must return None instead of
        // panicking or wrapping.
        assert_eq!(frame_slot_key(0, u32::MAX), None);
        assert_eq!(frame_slot_key(1, u32::MAX), None);
        assert_eq!(frame_slot_key(i32::MAX, 1), None);
    }

    #[test]
    fn frame_slot_key_returns_none_for_high_bit_offset() {
        // Offsets ≥ 0x8000_0000 previously cast to negative i32 and wrapped;
        // verify the widened arithmetic refuses them cleanly.
        assert_eq!(frame_slot_key(0, 0x8000_0000), None);
        assert_eq!(frame_slot_key(0, 0x8000_0001), None);
    }

    #[test]
    fn frame_slot_key_with_negative_base_can_recover_in_range() {
        // A negative base plus a large positive offset can land back in range —
        // verify the helper accepts it. i32::MIN + u32::MAX = 0x7FFF_FFFF (i32::MAX).
        assert_eq!(frame_slot_key(-1, 1), Some(0));
        assert_eq!(frame_slot_key(i32::MIN, u32::MAX), Some(i32::MAX));
    }

    // ----- MAX_INLINE_CALL_DEPTH constant (Phase 4.3) ------------------

    #[test]
    fn inline_call_depth_const_is_within_safe_bounds() {
        // Sanity check on the depth bound: not 0 (which would disable inlining),
        // not absurdly large (which would risk recursion blowup).
        const _: () = assert!(MAX_INLINE_CALL_DEPTH >= 1);
        const _: () = assert!(MAX_INLINE_CALL_DEPTH <= 32);
    }

    #[test]
    fn lift_inline_call_short_circuits_at_max_depth() {
        // Defence-in-depth: even if the caller forgets to check, the callee
        // bails out cleanly rather than recursing past the limit. Verify by
        // calling with target_idx=0 on an empty-WASM module — content is None,
        // no memory stores, no stack result.
        use crate::wasm::WasmModule;
        // Minimal valid WASM: 4-byte magic + 4-byte version, no sections.
        let empty_wasm = WasmModule::parse(b"\0asm\x01\x00\x00\x00").expect("empty WASM parses");
        let registry = crate::spec::registry::TypeRegistry {
            functions: std::collections::BTreeMap::new(),
            structs: std::collections::BTreeMap::new(),
            unions: std::collections::BTreeMap::new(),
            enums: std::collections::BTreeMap::new(),
            error_enums: std::collections::BTreeMap::new(),
            events: std::collections::BTreeMap::new(),
            meta: Vec::new(),
            spec_entries: Vec::new(),
        };
        let result = lift_inline_call(
            &empty_wasm,
            &registry,
            0,
            Vec::new(),
            MAX_INLINE_CALL_DEPTH,
            Rc::new(RefCell::new(HashMap::new())),
            Rc::new(RefCell::new(0)),
            Rc::new(RefCell::new(Vec::new())),
        );
        assert!(result.content.is_none());
        assert!(result.memory_stores.is_empty());
        assert!(result.stack_result.is_none());
    }

    // ----- stack_val_to_expr frame-slot cycle guard --------------------

    fn empty_registry() -> crate::spec::registry::TypeRegistry {
        crate::spec::registry::TypeRegistry {
            functions: std::collections::BTreeMap::new(),
            structs: std::collections::BTreeMap::new(),
            unions: std::collections::BTreeMap::new(),
            enums: std::collections::BTreeMap::new(),
            error_enums: std::collections::BTreeMap::new(),
            events: std::collections::BTreeMap::new(),
            meta: Vec::new(),
            spec_entries: Vec::new(),
        }
    }

    // ----- checked-arithmetic recovery --------------------------------

    /// `0x1_0000_0003`: a contract-error `Val` constant — tag `0x03` (Error),
    /// code `1` (`val >> 32`). The Err the SDK preloads for an overflow path.
    const ERR_VAL: i64 = 4_294_967_299;

    fn u64_param(name: &str) -> FnParam {
        FnParam {
            name: name.to_string(),
            type_def: ScSpecTypeDef::U64,
        }
    }

    fn result_u64_error() -> Option<ScSpecTypeDef> {
        Some(ScSpecTypeDef::Result(Box::new(
            stellar_xdr::ScSpecTypeResult {
                ok_type: Box::new(ScSpecTypeDef::U64),
                error_type: Box::new(ScSpecTypeDef::Error),
            },
        )))
    }

    /// Unwrap the recovered `a.checked_<op>(b).ok_or(_)` tail into
    /// `(method, minuend, subtrahend)` for assertions.
    fn checked_parts(stmt: Option<SorobanStmt>) -> (String, String, String) {
        let Some(SorobanStmt::Expr(SorobanExpr::MethodCall { object, method, .. })) = stmt else {
            panic!("not a recovered tail expr: {stmt:?}");
        };
        assert_eq!(method, "ok_or");
        let SorobanExpr::MethodCall {
            method: op,
            object: inner,
            args,
        } = *object
        else {
            panic!("inner is not a method call");
        };
        let SorobanExpr::Param(a) = *inner else {
            panic!("receiver is not a param");
        };
        let [SorobanExpr::Param(b)] = args.as_slice() else {
            panic!("arg is not a single param");
        };
        (op, a, b.clone())
    }

    #[test]
    fn recover_checked_add_emits_checked_add_ok_or() {
        use crate::wasm::ir::WasmInstr::*;
        cov_mark::check!(checked_arith_recovered);
        // add is commutative → operands are params[0], params[1].
        let body = vec![I64Add, I64LtU, I64Const(ERR_VAL)];
        let params = [u64_param("a"), u64_param("b")];
        let got =
            recover_checked_arith_from_body(&body, &params, &result_u64_error(), &empty_registry());
        assert_eq!(
            checked_parts(got),
            ("checked_add".into(), "a".into(), "b".into())
        );
    }

    #[test]
    fn recover_checked_sub_reads_operand_order_from_bytecode() {
        use crate::wasm::ir::WasmInstr::*;
        cov_mark::check!(checked_arith_recovered);
        // Bytecode computes `b - a` (operands LocalGet(1), LocalGet(0)) with a
        // matching `b < a` borrow guard — must recover `b.checked_sub(a)`, NOT
        // declaration order.
        let body = vec![
            LocalGet(1),
            LocalGet(0),
            I64LtU,
            LocalGet(1),
            LocalGet(0),
            I64Sub,
            I64Const(ERR_VAL),
        ];
        let params = [u64_param("a"), u64_param("b")];
        let got =
            recover_checked_arith_from_body(&body, &params, &result_u64_error(), &empty_registry());
        assert_eq!(
            checked_parts(got),
            ("checked_sub".into(), "b".into(), "a".into())
        );
    }

    #[test]
    fn recover_checked_error_is_raw_error_when_no_enum() {
        use crate::wasm::ir::WasmInstr::*;
        // No error enums in the registry → `soroban_sdk::Error::from_contract_error(1)`
        // (ContractError with no type/variant).
        let body = vec![I64Add, I64LtU, I64Const(ERR_VAL)];
        let params = [u64_param("a"), u64_param("b")];
        let Some(SorobanStmt::Expr(SorobanExpr::MethodCall { args, .. })) =
            recover_checked_arith_from_body(&body, &params, &result_u64_error(), &empty_registry())
        else {
            panic!("not recovered");
        };
        assert!(matches!(
            args.as_slice(),
            [SorobanExpr::ContractError {
                error_code: 1,
                error_type: None,
                variant_name: None,
            }]
        ));
    }

    #[test]
    fn checked_arith_skips_non_result_or_non_scalar_return() {
        use crate::wasm::ir::WasmInstr::*;
        let body = vec![I64Add, I64LtU, I64Const(ERR_VAL)];
        let params = [u64_param("a"), u64_param("b")];
        let reg = empty_registry();
        // Bare scalar return (the plain `add` fn) and no return type → untouched.
        assert!(
            recover_checked_arith_from_body(&body, &params, &Some(ScSpecTypeDef::U64), &reg)
                .is_none()
        );
        assert!(recover_checked_arith_from_body(&body, &params, &None, &reg).is_none());
    }

    #[test]
    fn checked_arith_skips_without_overflow_guard_or_error_const() {
        use crate::wasm::ir::WasmInstr::*;
        let params = [u64_param("a"), u64_param("b")];
        let reg = empty_registry();
        // No unsigned-`<` guard → a plain wrapping `Ok(a + b)`, not checked.
        assert!(
            recover_checked_arith_from_body(
                &[I64Add, I64Const(ERR_VAL)],
                &params,
                &result_u64_error(),
                &reg
            )
            .is_none()
        );
        // `I64Const(7)` has tag 7, not Error(3) → no contract-error const to put
        // in `.ok_or(..)` → bail (no fabricated error smuggled in).
        assert!(
            recover_checked_arith_from_body(
                &[I64Add, I64LtU, I64Const(7)],
                &params,
                &result_u64_error(),
                &reg
            )
            .is_none()
        );
    }

    #[test]
    fn checked_arith_skips_non_binary_arity() {
        use crate::wasm::ir::WasmInstr::*;
        let body = vec![I64Add, I64LtU, I64Const(ERR_VAL)];
        let three = [u64_param("a"), u64_param("b"), u64_param("c")];
        assert!(
            recover_checked_arith_from_body(&body, &three, &result_u64_error(), &empty_registry())
                .is_none()
        );
    }

    #[test]
    fn checked_arith_skips_non_contract_error_const() {
        use crate::wasm::ir::WasmInstr::*;
        // Error-tagged Val whose error-TYPE sub-field (bits 8-15) is non-zero
        // (`0x01` = a non-Contract error, e.g. WasmVm). `find_checked_error_code`
        // must skip it — its `val >> 32` is NOT a contract error code — so with no
        // genuine contract-error const present, recovery bails (no wrong code
        // smuggled into `.ok_or(..)`).
        const NON_CONTRACT_ERR: i64 = 0x1_0000_0103; // tag 0x03, type 0x01, code 1
        assert_eq!(0x103u64 & 0xff, TAG_ERROR);
        assert_ne!((0x103u64 >> 8) & 0xff, 0);
        let params = [u64_param("a"), u64_param("b")];
        assert!(
            recover_checked_arith_from_body(
                &[I64Add, I64LtU, I64Const(NON_CONTRACT_ERR)],
                &params,
                &result_u64_error(),
                &empty_registry()
            )
            .is_none()
        );
    }

    /// Registry holding the named `#[contracterror]` enums, each `(variant, code)`.
    fn registry_with_error_enums(
        enums: &[(&str, &[(&str, u32)])],
    ) -> crate::spec::registry::TypeRegistry {
        let mut reg = empty_registry();
        for (name, cases) in enums {
            let cases: Vec<_> = cases
                .iter()
                .map(|(vname, value)| stellar_xdr::ScSpecUdtErrorEnumCaseV0 {
                    doc: Default::default(),
                    name: (*vname).try_into().unwrap(),
                    value: *value,
                })
                .collect();
            reg.error_enums.insert(
                (*name).to_string(),
                stellar_xdr::ScSpecUdtErrorEnumV0 {
                    doc: Default::default(),
                    lib: Default::default(),
                    name: (*name).try_into().unwrap(),
                    cases: cases.try_into().unwrap(),
                },
            );
        }
        reg
    }

    fn recovered_ok_or_arg(stmt: Option<SorobanStmt>) -> SorobanExpr {
        let Some(SorobanStmt::Expr(SorobanExpr::MethodCall { args, .. })) = stmt else {
            panic!("not a recovered tail expr: {stmt:?}");
        };
        let [arg] = args.as_slice() else {
            panic!("ok_or takes exactly one arg");
        };
        arg.clone()
    }

    #[test]
    fn checked_error_raw_error_resolves_sole_enum_variant() {
        use crate::wasm::ir::WasmInstr::*;
        // Declared error type is the raw `soroban_sdk::Error`, but there is exactly
        // ONE error enum → codegen substitutes it, so the `.ok_or(..)` arg names
        // that enum's variant for the recovered code (mirrors return-type rendering).
        let body = vec![I64Add, I64LtU, I64Const(ERR_VAL)];
        let params = [u64_param("a"), u64_param("b")];
        let reg = registry_with_error_enums(&[("Error", &[("Overflow", 1)])]);
        assert!(matches!(
            recovered_ok_or_arg(recover_checked_arith_from_body(
                &body,
                &params,
                &result_u64_error(),
                &reg
            )),
            SorobanExpr::ContractError {
                error_code: 1,
                error_type: Some(t),
                variant_name: Some(v),
            } if t == "Error" && v == "Overflow"
        ));
    }

    #[test]
    fn checked_error_raw_error_with_multiple_enums_is_unguessed() {
        use crate::wasm::ir::WasmInstr::*;
        // Declared error type is the raw `soroban_sdk::Error` and TWO enums share
        // code 1. We deliberately do NOT guess a variant (that would fabricate the
        // wrong `E::Variant`); the honest rendering is `Error::from_contract_error(1)`
        // — i.e. ContractError with no type/variant. Locks in this choice against a
        // regression toward the ambiguous `lookup_error_variant` path.
        let body = vec![I64Add, I64LtU, I64Const(ERR_VAL)];
        let params = [u64_param("a"), u64_param("b")];
        let reg = registry_with_error_enums(&[
            ("Error", &[("Overflow", 1)]),
            ("MyError", &[("Boom", 1)]),
        ]);
        assert!(matches!(
            recovered_ok_or_arg(recover_checked_arith_from_body(
                &body,
                &params,
                &result_u64_error(),
                &reg
            )),
            SorobanExpr::ContractError {
                error_code: 1,
                error_type: None,
                variant_name: None,
            }
        ));
    }

    #[test]
    fn stack_val_to_expr_breaks_self_referential_frame_slot() {
        // Regression for the aquarius.wasm stack overflow: a frame slot whose
        // stored value is a Val-encoded `(inner << 32) | tag` that embeds the
        // *same* slot. `strip_val_encode` peels the encoding back to the slot,
        // and resolving it re-enters the slot lookup forever. The one-level
        // `matches!` guard can't see the embedded slot (the stored value is a
        // BinOp, not a bare FrameSlot), so the path tracker must break the cycle.
        let slot = StackVal::FrameSlot(0, SlotOffset::at(0));
        let encoded = StackVal::BinOp(
            Box::new(StackVal::BinOp(
                Box::new(slot.clone()),
                BinOper::Shl,
                Box::new(StackVal::I64(32)),
            )),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_U32 as i64)),
        );
        let mut slots: FrameSlotMap = HashMap::new();
        slots.insert((0, 0), encoded);

        let registry = empty_registry();
        // Terminates (no overflow) and reports the cycle precisely, naming the
        // slot that closed it, instead of an anonymous UnknownVal.
        let expr = stack_val_to_expr(&slot, &[], &registry, Some(&slots));
        assert_eq!(
            expr,
            SorobanExpr::CyclicSlot {
                frame_id: 0,
                offset: 0
            }
        );
    }

    #[test]
    fn stack_val_to_expr_breaks_indirect_frame_slot_cycle() {
        // Two slots that reference each other through a non-FrameSlot wrapper
        // (Eqz), so the one-level guard passes at each hop. The path tracker
        // must still terminate the mutual recursion.
        let mut slots: FrameSlotMap = HashMap::new();
        slots.insert(
            (0, 0),
            StackVal::Eqz(Box::new(StackVal::FrameSlot(0, SlotOffset::at(8)))),
        );
        slots.insert(
            (0, 8),
            StackVal::Eqz(Box::new(StackVal::FrameSlot(0, SlotOffset::at(0)))),
        );

        let registry = empty_registry();
        // Terminates, and the recovered expression names the cyclic slot
        // precisely somewhere inside (wrapped by the Eqz comparisons).
        let expr = stack_val_to_expr(
            &StackVal::FrameSlot(0, SlotOffset::at(0)),
            &[],
            &registry,
            Some(&slots),
        );
        assert!(
            format!("{expr:?}").contains("CyclicSlot"),
            "expected a precise CyclicSlot marker, got {expr:?}"
        );
    }

    #[test]
    fn stack_val_to_expr_still_resolves_acyclic_frame_slot() {
        // The guard must not break legitimate (acyclic) slot resolution: a slot
        // holding a plain parameter should resolve to that parameter.
        let mut slots: FrameSlotMap = HashMap::new();
        slots.insert((0, 0), StackVal::Param("amount".to_string()));

        let registry = empty_registry();
        let expr = stack_val_to_expr(
            &StackVal::FrameSlot(0, SlotOffset::at(0)),
            &[],
            &registry,
            Some(&slots),
        );
        assert_eq!(expr, SorobanExpr::Param("amount".to_string()));
    }

    // ----- symbolic dynamic offsets (issue #7) --------------------------

    #[test]
    fn affine_index_term_recognizes_index_shapes() {
        let idx = StackVal::WasmParam(2);
        // Bare index → stride 1.
        assert_eq!(
            affine_index_term(&idx),
            Some(SymTerm {
                index_local: 2,
                coeff: 1
            })
        );
        // index * const and const * index (either operand order).
        let mul =
            |a: StackVal, b: StackVal| StackVal::BinOp(Box::new(a), BinOper::Mul, Box::new(b));
        assert_eq!(
            affine_index_term(&mul(idx.clone(), StackVal::I32(8))),
            Some(SymTerm {
                index_local: 2,
                coeff: 8
            })
        );
        assert_eq!(
            affine_index_term(&mul(StackVal::I64(8), idx.clone())),
            Some(SymTerm {
                index_local: 2,
                coeff: 8
            })
        );
        // index << shift → coeff = 1 << shift.
        let shl = StackVal::BinOp(
            Box::new(idx.clone()),
            BinOper::Shl,
            Box::new(StackVal::I32(3)),
        );
        assert_eq!(
            affine_index_term(&shl),
            Some(SymTerm {
                index_local: 2,
                coeff: 8
            })
        );
        // Loop-carried phi and promoted let-binding are also valid indices.
        assert!(affine_index_term(&StackVal::LoopPhi(5)).is_some());
        assert!(affine_index_term(&StackVal::LetBinding(5)).is_some());
        // Non-index shapes are rejected (fall through to plain BinOp).
        assert_eq!(affine_index_term(&StackVal::I32(8)), None);
        assert_eq!(
            affine_index_term(&mul(StackVal::I32(3), StackVal::I32(8))),
            None
        );
        // Stride 0 / out-of-range is rejected.
        assert_eq!(affine_index_term(&mul(idx.clone(), StackVal::I32(0))), None);
    }

    #[test]
    fn dynamic_offset_arithmetic_and_readback() {
        use crate::wasm::ir::WasmInstr;
        // `frame_ptr + i*8` forms a dynamic FrameSlot; a store then a load with
        // the same symbolic offset round-trips the value through dynamic_slots,
        // while a load at a different index misses (→ Unknown).
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 1);

        // Build the dynamic address `FrameSlot(0, base 0) + WasmParam(0)*8`.
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.stack.push(StackVal::WasmParam(0));
        ctx.lift_instruction(&WasmInstr::I32Const(8));
        ctx.lift_instruction(&WasmInstr::I32Mul);
        ctx.lift_instruction(&WasmInstr::I32Add);
        let dyn_addr = ctx.stack.last().cloned().unwrap();
        assert!(
            matches!(&dyn_addr, StackVal::FrameSlot(0, off) if off.term == Some(SymTerm { index_local: 0, coeff: 8 })),
            "expected dynamic FrameSlot, got {dyn_addr:?}"
        );

        // Store a value through the dynamic address: [addr, value] then i64.store.
        ctx.stack.push(dyn_addr.clone());
        ctx.stack.push(StackVal::Param("spilled".to_string()));
        ctx.lift_instruction(&WasmInstr::I64Store(0));

        // Load it back at the same index → recovers the stored value.
        ctx.stack.push(dyn_addr);
        ctx.lift_instruction(&WasmInstr::I64Load(0));
        assert_eq!(
            ctx.stack.pop(),
            Some(StackVal::Param("spilled".to_string()))
        );

        // A load at a different index (WasmParam(1)) misses → Unknown.
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.stack.push(StackVal::WasmParam(1));
        ctx.lift_instruction(&WasmInstr::I32Const(8));
        ctx.lift_instruction(&WasmInstr::I32Mul);
        ctx.lift_instruction(&WasmInstr::I32Add);
        ctx.lift_instruction(&WasmInstr::I64Load(0));
        assert_eq!(ctx.stack.pop(), Some(StackVal::Unknown));
    }

    #[test]
    fn i32_sign_extend_idiom_round_trips_inner_value() {
        use crate::wasm::ir::WasmInstr;
        // `(x << k) >> k` for k ∈ {8,16,24} sign-extends a narrow value; for the
        // `< 0` sign test the SDK emits after `obj_cmp` it is value-preserving, so
        // the lifter must round-trip the inner value rather than dropping it to
        // `Unknown` (regression guard for the fuzz fixture: `if a < b { panic }`).
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 1);

        let inner = StackVal::HostCallResult(Box::new(SorobanExpr::Param("a".to_string())));
        for k in [8i32, 16, 24] {
            ctx.stack.clear();
            ctx.stack.push(inner.clone());
            ctx.lift_instruction(&WasmInstr::I32Const(k));
            ctx.lift_instruction(&WasmInstr::I32Shl);
            // After the shl alone the value is tracked as a Shl marker, not lost.
            assert!(
                matches!(ctx.stack.last(), Some(StackVal::BinOp(_, BinOper::Shl, _))),
                "shl {k} should track the inner value, got {:?}",
                ctx.stack.last()
            );
            ctx.lift_instruction(&WasmInstr::I32Const(k));
            ctx.lift_instruction(&WasmInstr::I32ShrS);
            assert_eq!(ctx.stack.pop(), Some(inner.clone()), "round-trip k={k}");
        }

        // A mismatched width does NOT round-trip (it is not a sign-extend) → Unknown.
        ctx.stack.clear();
        ctx.stack.push(inner.clone());
        ctx.lift_instruction(&WasmInstr::I32Const(24));
        ctx.lift_instruction(&WasmInstr::I32Shl);
        ctx.lift_instruction(&WasmInstr::I32Const(16));
        ctx.lift_instruction(&WasmInstr::I32ShrS);
        assert_eq!(
            ctx.stack.pop(),
            Some(StackVal::Unknown),
            "mismatched widths"
        );

        // A non-sign-extend shift width still degrades to Unknown (unchanged behavior).
        ctx.stack.clear();
        ctx.stack.push(inner);
        ctx.lift_instruction(&WasmInstr::I32Const(5));
        ctx.lift_instruction(&WasmInstr::I32Shl);
        assert_eq!(
            ctx.stack.pop(),
            Some(StackVal::Unknown),
            "non-extend width 5"
        );
    }

    #[test]
    fn dynamic_store_invalidates_aliased_static_slots() {
        use crate::wasm::ir::WasmInstr;
        // A dynamic write `frame[0 + i*8]` may alias the static slot at offset 8
        // (congruent to 0 mod 8) but not the one at offset 12, so only the former
        // is dropped — a later static load of it can't return a stale value.
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 1);
        ctx.frame_slots
            .borrow_mut()
            .insert((0, 8), StackVal::Param("a".to_string()));
        ctx.frame_slots
            .borrow_mut()
            .insert((0, 12), StackVal::Param("b".to_string()));

        // Build and store through the dynamic address `frame_ptr + i*8`.
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.stack.push(StackVal::WasmParam(0));
        ctx.lift_instruction(&WasmInstr::I32Const(8));
        ctx.lift_instruction(&WasmInstr::I32Mul);
        ctx.lift_instruction(&WasmInstr::I32Add);
        ctx.stack.push(StackVal::Param("c".to_string()));
        ctx.lift_instruction(&WasmInstr::I64Store(0));

        assert!(!ctx.frame_slots.borrow().contains_key(&(0, 8)));
        assert_eq!(
            ctx.frame_slots.borrow().get(&(0, 12)),
            Some(&StackVal::Param("b".to_string()))
        );
    }

    #[test]
    fn sret_result_scrutinee_resolves_to_ok_err() {
        // A br_table whose scrutinee is an sret/Result discriminant resolves to a
        // two-arm Ok/Err dispatch (both data-carrying), regardless of registry
        // contents — checked before the integer-enum heuristic.
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);

        let scrut = SorobanExpr::SretResult(Box::new(SorobanExpr::UnknownVal));
        assert_eq!(
            ctx.try_resolve_enum_for_scrutinee(&scrut, 2),
            Some((
                "Result".to_string(),
                vec!["Ok".to_string(), "Err".to_string()],
                vec![true, true]
            ))
        );
        // A plain unknown scrutinee with no registry types still resolves to None.
        assert_eq!(
            ctx.try_resolve_enum_for_scrutinee(&SorobanExpr::UnknownVal, 2),
            None
        );
    }

    #[test]
    fn model_sret_discriminant_seeds_marker_from_invoke_payload() {
        // A void helper left a cross-contract invoke result at result_ptr+8 but no
        // discriminant at result_ptr+0. Modeling seeds +0 with SretResult(<invoke>)
        // so a later load+br_table reconstructs the Ok/Err dispatch.
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 1);

        let invoke = SorobanExpr::TryInvokeContract {
            address: Box::new(SorobanExpr::Param("calc".to_string())),
            function: Box::new(SorobanExpr::SymbolLiteral("estimate_swap".to_string())),
            args: vec![],
            return_type: None,
        };
        ctx.frame_slots
            .borrow_mut()
            .insert((0, 8), StackVal::HostCallResult(Box::new(invoke.clone())));

        ctx.model_sret_discriminant(0, 0);

        // +0 now resolves to SretResult(<invoke>), which the dispatch recognizer
        // turns into a `match .. { Ok(..) => .., Err(..) => .. }`.
        match ctx.frame_slots.borrow().get(&(0, 0)) {
            Some(StackVal::HostCallResult(e)) => {
                assert_eq!(**e, SorobanExpr::SretResult(Box::new(invoke)));
            }
            other => panic!("expected SretResult marker at result_ptr+0, got {other:?}"),
        }
    }

    #[test]
    fn option_decode_none_check_matches_disc_zero_tests() {
        // `eqz disc` and `disc == 0` (either operand order) are the None-arm
        // tests the trap-guard fold recognizes.
        let disc = || Box::new(StackVal::OptionDecodeDisc);
        assert!(is_option_decode_none_check(&StackVal::Eqz(disc())));
        assert!(is_option_decode_none_check(&StackVal::Compare(
            disc(),
            CmpOp::Eq,
            Box::new(StackVal::I64(0)),
        )));
        assert!(is_option_decode_none_check(&StackVal::Compare(
            Box::new(StackVal::I32(0)),
            CmpOp::Eq,
            disc(),
        )));
        // The success-arm polarity (`disc != 0`) and non-marker scrutinees are
        // REAL control flow — never folded.
        assert!(!is_option_decode_none_check(&StackVal::Compare(
            disc(),
            CmpOp::Ne,
            Box::new(StackVal::I64(0)),
        )));
        assert!(!is_option_decode_none_check(&StackVal::Eqz(Box::new(
            StackVal::Unknown
        ))));
        assert!(!is_option_decode_none_check(&StackVal::Compare(
            disc(),
            CmpOp::Eq,
            Box::new(StackVal::I64(1)),
        )));
    }

    #[test]
    fn if_result_join_encode_split_joins_to_conversion() {
        // The SDK's small/object Val encode split of ONE source: then-arm
        // `(p << 8) | U64Small`, else-arm `obj_from_u64(p)` → the join is the
        // conversion (both arms encode the same value; the split is host
        // plumbing).
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);

        let p = || StackVal::Param("amount".to_string());
        let small = StackVal::BinOp(
            Box::new(StackVal::BinOp(
                Box::new(p()),
                BinOper::Shl,
                Box::new(StackVal::I64(8)),
            )),
            BinOper::Or,
            Box::new(StackVal::I64(6)),
        );
        let conv = StackVal::HostCallResult(Box::new(SorobanExpr::ValConvert {
            value: Box::new(SorobanExpr::Param("amount".to_string())),
            target_type: "u64".to_string(),
        }));
        // Both arm orders join to the conversion.
        assert_eq!(ctx.join_if_result_values(&small, &conv), Some(conv.clone()));
        assert_eq!(ctx.join_if_result_values(&conv, &small), Some(conv.clone()));
        // Identical pure arms join to themselves.
        assert_eq!(ctx.join_if_result_values(&p(), &p()), Some(p()));
    }

    #[test]
    fn if_result_join_refuses_unproven_arms() {
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);

        // An Unknown source can't be proven equal to anything.
        let small_unknown = StackVal::BinOp(
            Box::new(StackVal::BinOp(
                Box::new(StackVal::Unknown),
                BinOper::Shl,
                Box::new(StackVal::I64(8)),
            )),
            BinOper::Or,
            Box::new(StackVal::I64(6)),
        );
        let conv_unknown = StackVal::HostCallResult(Box::new(SorobanExpr::ValConvert {
            value: Box::new(SorobanExpr::UnknownVal),
            target_type: "u64".to_string(),
        }));
        assert_eq!(
            ctx.join_if_result_values(&small_unknown, &conv_unknown),
            None
        );
        // Different sources never join.
        let conv_other = StackVal::HostCallResult(Box::new(SorobanExpr::ValConvert {
            value: Box::new(SorobanExpr::Param("other".to_string())),
            target_type: "u64".to_string(),
        }));
        let small_amount = StackVal::BinOp(
            Box::new(StackVal::BinOp(
                Box::new(StackVal::Param("amount".to_string())),
                BinOper::Shl,
                Box::new(StackVal::I64(8)),
            )),
            BinOper::Or,
            Box::new(StackVal::I64(6)),
        );
        assert_eq!(ctx.join_if_result_values(&small_amount, &conv_other), None);
        // Identical IMPURE arms (a storage get) never join: re-reading the
        // expression at the consumer would duplicate a host call.
        let get = StackVal::HostCallResult(Box::new(SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key: Box::new(SorobanExpr::SymbolLiteral("K".to_string())),
            unwrap: true,
            on_missing: None,
        }));
        assert_eq!(ctx.join_if_result_values(&get, &get), None);
        // Path-dependent constants (a Result discriminant) never join.
        assert_eq!(
            ctx.join_if_result_values(&StackVal::I64(0), &StackVal::I64(1)),
            None
        );
    }

    #[test]
    fn unique_slot_def_fill_recovers_invalidated_slot() {
        use crate::wasm::ir::WasmInstr;
        // A store journals its def; when invalidation later drops the slot from
        // the state map, a load still recovers the value through the journal —
        // it is the function's unique reaching definition.
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);

        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.stack.push(StackVal::Param("key".to_string()));
        ctx.lift_instruction(&WasmInstr::I64Store(16));
        // Simulate invalidation (the state map loses the slot; the journal keeps it).
        ctx.frame_slots.borrow_mut().remove(&(0, 16));

        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.lift_instruction(&WasmInstr::I64Load(16));
        assert_eq!(ctx.stack.pop(), Some(StackVal::Param("key".to_string())));
    }

    #[test]
    fn unique_slot_def_fill_stays_honest_otherwise() {
        use crate::wasm::ir::WasmInstr;
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;

        // Two defs → ambiguous → Unknown.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        for p in ["a", "b"] {
            ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
            ctx.stack.push(StackVal::Param(p.to_string()));
            ctx.lift_instruction(&WasmInstr::I64Store(16));
        }
        ctx.frame_slots.borrow_mut().remove(&(0, 16));
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.lift_instruction(&WasmInstr::I64Load(16));
        assert_eq!(ctx.stack.pop(), Some(StackVal::Unknown));

        // Inside a loop body → the load may observe a later iteration's store
        // → Unknown.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.stack.push(StackVal::Param("a".to_string()));
        ctx.lift_instruction(&WasmInstr::I64Store(16));
        ctx.frame_slots.borrow_mut().remove(&(0, 16));
        ctx.loop_depth = 1;
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.lift_instruction(&WasmInstr::I64Load(16));
        assert_eq!(ctx.stack.pop(), Some(StackVal::Unknown));

        // A loop-varying def (`LetBinding` — possibly a loop counter) → Unknown.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.stack.push(StackVal::LetBinding(3));
        ctx.lift_instruction(&WasmInstr::I64Store(16));
        ctx.frame_slots.borrow_mut().remove(&(0, 16));
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.lift_instruction(&WasmInstr::I64Load(16));
        assert_eq!(ctx.stack.pop(), Some(StackVal::Unknown));

        // A slot that holds a stored `Unknown` (the last store was genuinely
        // unknown-valued) is NOT filled from an earlier journal entry.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.stack.push(StackVal::Param("a".to_string()));
        ctx.lift_instruction(&WasmInstr::I64Store(16));
        ctx.frame_slots
            .borrow_mut()
            .insert((0, 16), StackVal::Unknown);
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.lift_instruction(&WasmInstr::I64Load(16));
        assert_eq!(ctx.stack.pop(), Some(StackVal::Unknown));

        // A dynamic (loop-indexed) aliasing write both evicts the slot AND
        // poisons its journal: the dynamic store may have overwritten the
        // value at runtime, so the fill must NOT resurrect the stale static
        // store (greptile P1).
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.stack.push(StackVal::Param("a".to_string()));
        ctx.lift_instruction(&WasmInstr::I64Store(16));
        // Dynamic store through `frame + i*8` — aliases offset 16.
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.stack.push(StackVal::WasmParam(0));
        ctx.lift_instruction(&WasmInstr::I32Const(8));
        ctx.lift_instruction(&WasmInstr::I32Mul);
        ctx.lift_instruction(&WasmInstr::I32Add);
        ctx.stack.push(StackVal::Param("b".to_string()));
        ctx.lift_instruction(&WasmInstr::I64Store(0));
        assert!(
            !ctx.frame_slots.borrow().contains_key(&(0, 16)),
            "aliasing write evicts the static slot"
        );
        ctx.stack.push(StackVal::FrameSlot(0, SlotOffset::at(0)));
        ctx.lift_instruction(&WasmInstr::I64Load(16));
        assert_eq!(ctx.stack.pop(), Some(StackVal::Unknown));
    }

    #[test]
    fn link_option_decode_value_promotes_orphan_get() {
        // The unique inlined orphan `Expr(get)` becomes a `let var_N` binding
        // and the value slot reads that binding — never a re-issued get.
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);

        let get = SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key: Box::new(SorobanExpr::SymbolLiteral("Admin".to_string())),
            unwrap: true,
            on_missing: None,
        };
        let mut stmts = vec![SorobanStmt::Expr(get.clone())];
        ctx.link_option_decode_value(0, 0, 999, &mut stmts);

        let SorobanStmt::Let { name, value, .. } = &stmts[0] else {
            panic!("orphan get should be promoted to a Let, got {:?}", stmts[0]);
        };
        assert_eq!(*value, get);
        let idx: u32 = name
            .strip_prefix("var_")
            .and_then(|s| s.parse().ok())
            .expect("synthetic var_N name");
        assert_eq!(
            ctx.frame_slots.borrow().get(&(0, 8)),
            Some(&StackVal::LetBinding(idx))
        );
    }

    #[test]
    fn link_option_decode_value_stays_honest_otherwise() {
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;

        let get = |key: &str| SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key: Box::new(SorobanExpr::SymbolLiteral(key.to_string())),
            unwrap: true,
            on_missing: None,
        };
        // Two gets → ambiguous → no seed, statements untouched.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        let mut stmts = vec![SorobanStmt::Expr(get("A")), SorobanStmt::Expr(get("B"))];
        ctx.link_option_decode_value(0, 0, 999, &mut stmts);
        assert!(matches!(stmts[0], SorobanStmt::Expr(_)));
        assert!(ctx.frame_slots.borrow().get(&(0, 8)).is_none());

        // A hole-keyed get → no seed.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        let mut stmts = vec![SorobanStmt::Expr(SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key: Box::new(SorobanExpr::UnknownVal),
            unwrap: true,
            on_missing: None,
        })];
        ctx.link_option_decode_value(0, 0, 999, &mut stmts);
        assert!(matches!(stmts[0], SorobanStmt::Expr(_)));
        assert!(ctx.frame_slots.borrow().get(&(0, 8)).is_none());

        // An already-bound get reuses ITS name (no rewrite, no fresh local).
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        let mut stmts = vec![SorobanStmt::Let {
            name: "admin".to_string(),
            mutable: false,
            value: get("Admin"),
        }];
        ctx.link_option_decode_value(0, 0, 999, &mut stmts);
        match ctx.frame_slots.borrow().get(&(0, 8)) {
            Some(StackVal::HostCallResult(e)) => {
                assert_eq!(**e, SorobanExpr::NamedLocal("admin".to_string()));
            }
            other => panic!("expected NamedLocal seed, got {other:?}"),
        }
    }

    #[test]
    fn loop_invariant_purity_excludes_bindings_and_calls() {
        // `LetBinding` may name a loop counter; host-call results are effects.
        // Constants, params, and arithmetic over them are invariant.
        assert!(stack_val_is_loop_invariant_pure(&StackVal::I64(7)));
        assert!(stack_val_is_loop_invariant_pure(&StackVal::Param(
            "p".to_string()
        )));
        assert!(stack_val_is_loop_invariant_pure(&StackVal::BinOp(
            Box::new(StackVal::Param("p".to_string())),
            BinOper::Add,
            Box::new(StackVal::I64(1)),
        )));
        assert!(!stack_val_is_loop_invariant_pure(&StackVal::LetBinding(2)));
        assert!(!stack_val_is_loop_invariant_pure(
            &StackVal::HostCallResult(Box::new(SorobanExpr::LedgerTimestamp))
        ));
        assert!(!stack_val_is_loop_invariant_pure(&StackVal::Unknown));
    }

    #[test]
    fn option_decode_disc_degrades_to_unknown() {
        // Any consumer other than the trap-guard fold must see the marker as a
        // lost value (today's honest `todo!()`), never a fabricated constant.
        let reg = empty_registry();
        let expr = stack_val_to_expr(&StackVal::OptionDecodeDisc, &[], &reg, None);
        assert_eq!(expr, SorobanExpr::UnknownVal);
    }

    #[test]
    fn expr_contains_invoke_contract_looks_past_wrappers() {
        // The helper's invoke result is typically wrapped in ValConvert / MethodCall /
        // FieldAccess before being stored — the recognizer must see past those.
        let invoke = SorobanExpr::TryInvokeContract {
            address: Box::new(SorobanExpr::UnknownVal),
            function: Box::new(SorobanExpr::SymbolLiteral("foo".to_string())),
            args: vec![],
            return_type: None,
        };
        assert!(expr_contains_invoke_contract(&invoke));
        let wrapped = SorobanExpr::ValConvert {
            value: Box::new(SorobanExpr::MethodCall {
                object: Box::new(invoke.clone()),
                method: "unwrap".to_string(),
                args: vec![],
            }),
            target_type: "u128".to_string(),
        };
        assert!(expr_contains_invoke_contract(&wrapped));
        // Pure non-invoke expressions are rejected.
        assert!(!expr_contains_invoke_contract(&SorobanExpr::U64Literal(7)));
    }

    #[test]
    fn model_sret_discriminant_ignores_non_invoke_payload() {
        // No false positive: a plain (non-cross-contract) payload at +8 must not
        // synthesize an sret discriminant.
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 1);
        ctx.frame_slots.borrow_mut().insert(
            (0, 8),
            StackVal::HostCallResult(Box::new(SorobanExpr::U64Literal(7))),
        );
        ctx.model_sret_discriminant(0, 0);
        assert!(ctx.frame_slots.borrow().get(&(0, 0)).is_none());
    }

    // ----- detect_memory_copy_loop bound -------------------
    //
    // The internal `MAX_MEMORY_COPY_BYTES` constant is exercised indirectly
    // by the integration suite (no fixture currently triggers the loop
    // detector). A future regression that removed the cap would still be
    // surfaced by build-time inspection of the source; the bound is small
    // (1024) and obvious. Direct testing requires constructing a synthetic
    // WASM function body, which is heavy enough to belong in its own
    // follow-up rather than this PR.

    // ----- Val tag table + naming (issue #4) ---------------------------

    #[test]
    fn object_tags_and_names_match_canonical_layout() {
        assert!(is_object_tag(TAG_VEC_OBJECT)); // 75
        assert!(is_object_tag(64));
        assert!(is_object_tag(127));
        assert!(!is_object_tag(TAG_U32)); // small value
        assert!(!is_object_tag(7));

        assert_eq!(val_tag_name(TAG_VEC_OBJECT), Some("VecObject"));
        assert_eq!(val_tag_name(TAG_ADDRESS_OBJECT), Some("AddressObject"));
        assert_eq!(val_tag_name(TAG_U32), Some("U32Val"));
        assert_eq!(val_tag_name(TAG_SYMBOL_SMALL), Some("SymbolSmall"));
        // Bound markers / reserved bytes are not tags.
        assert_eq!(val_tag_name(63), None);
        assert_eq!(val_tag_name(200), None);
    }

    // ----- recognize_val_shape (issue #4) ------------------------------

    fn shl(inner: StackVal, by: i64) -> StackVal {
        StackVal::BinOp(Box::new(inner), BinOper::Shl, Box::new(StackVal::I64(by)))
    }

    #[test]
    fn recognize_val_shape_tag_extraction() {
        let v = StackVal::BinOp(
            Box::new(StackVal::Param("v".to_string())),
            BinOper::And,
            Box::new(StackVal::I64(0xFF)),
        );
        assert_eq!(
            recognize_val_shape(&v),
            Some(ValShape::TagOf(StackVal::Param("v".to_string())))
        );
    }

    #[test]
    fn recognize_val_shape_constructions() {
        // (payload << 32) | U32 tag
        let c32 = StackVal::BinOp(
            Box::new(shl(StackVal::Param("p".to_string()), 32)),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_U32 as i64)),
        );
        assert_eq!(
            recognize_val_shape(&c32),
            Some(ValShape::Construct {
                payload: StackVal::Param("p".to_string()),
                shift: 32,
                tag: TAG_U32,
            })
        );

        // (payload << 8) | U64Small tag
        let c8 = StackVal::BinOp(
            Box::new(shl(StackVal::I64(5), 8)),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_U64_SMALL as i64)),
        );
        assert_eq!(
            recognize_val_shape(&c8),
            Some(ValShape::Construct {
                payload: StackVal::I64(5),
                shift: 8,
                tag: TAG_U64_SMALL,
            })
        );
    }

    #[test]
    fn recognize_val_shape_rejects_unknown_tag() {
        // `(x << 32) | 0x99` is not a known tag → not a construction.
        let bogus = StackVal::BinOp(
            Box::new(shl(StackVal::Param("p".to_string()), 32)),
            BinOper::Or,
            Box::new(StackVal::I64(0x99)),
        );
        assert_eq!(recognize_val_shape(&bogus), None);
    }

    // ----- tag-equality lowering (issue #4, DoD item 5) ---------------

    fn tag_of(param: &str) -> StackVal {
        StackVal::BinOp(
            Box::new(StackVal::Param(param.to_string())),
            BinOper::And,
            Box::new(StackVal::I64(0xFF)),
        )
    }

    #[test]
    fn tag_check_in_kept_branch_lifts_to_named_guard() {
        // `(arg & 0xFF) != 75` → `arg.get_tag() != Tag::VecObject`.
        let cmp = StackVal::Compare(
            Box::new(tag_of("arg")),
            CmpOp::Ne,
            Box::new(StackVal::I64(TAG_VEC_OBJECT as i64)),
        );
        let expr = stack_val_to_expr(&cmp, &[], &empty_registry(), None);
        assert_eq!(
            expr,
            SorobanExpr::Ne(
                Box::new(SorobanExpr::ValTag(Box::new(SorobanExpr::Param(
                    "arg".to_string()
                )))),
                Box::new(SorobanExpr::ValTagName("VecObject".to_string())),
            )
        );
        // Crucially, the recovered condition has no Unknown placeholder.
        assert!(!matches!(expr, SorobanExpr::UnknownVal));
    }

    #[test]
    fn tag_check_equality_with_constant_on_left() {
        // `75 == (arg & 0xFF)` → `Tag::VecObject == arg.get_tag()`.
        let cmp = StackVal::Compare(
            Box::new(StackVal::I64(TAG_VEC_OBJECT as i64)),
            CmpOp::Eq,
            Box::new(tag_of("arg")),
        );
        let expr = stack_val_to_expr(&cmp, &[], &empty_registry(), None);
        assert_eq!(
            expr,
            SorobanExpr::Eq(
                Box::new(SorobanExpr::ValTagName("VecObject".to_string())),
                Box::new(SorobanExpr::ValTag(Box::new(SorobanExpr::Param(
                    "arg".to_string()
                )))),
            )
        );
    }

    #[test]
    fn standalone_tag_extraction_lifts_to_get_tag() {
        // A bare `v & 0xFF` (not in a comparison) becomes `v.get_tag()`.
        let expr = stack_val_to_expr(&tag_of("v"), &[], &empty_registry(), None);
        assert_eq!(
            expr,
            SorobanExpr::ValTag(Box::new(SorobanExpr::Param("v".to_string())))
        );
    }

    // ----- non-regression: centralized routing preserves behavior -----

    #[test]
    fn strip_val_encode_still_strips_small_construction() {
        // `(param << 32) | U32` strips back to the param.
        let encoded = StackVal::BinOp(
            Box::new(shl(StackVal::Param("p".to_string()), 32)),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_U32 as i64)),
        );
        assert_eq!(strip_val_encode(encoded), StackVal::Param("p".to_string()));
    }

    #[test]
    fn strip_val_encode_leaves_object_construction_unknown() {
        // Object constructions carry an opaque handle, not a Rust value.
        let encoded = StackVal::BinOp(
            Box::new(shl(StackVal::I64(7), 32)),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_VEC_OBJECT as i64)),
        );
        assert_eq!(strip_val_encode(encoded), StackVal::Unknown);
    }

    #[test]
    fn extract_u32_from_stack_val_still_decodes_construction() {
        let encoded = StackVal::BinOp(
            Box::new(shl(StackVal::I64(7), 32)),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_U32 as i64)),
        );
        assert_eq!(extract_u32_from_stack_val(&encoded), Some(7));
    }

    // ----- coverage: tag table, helpers, edge shapes (issue #4) -------

    #[test]
    fn val_tag_name_covers_every_known_tag() {
        let expected: &[(u64, &str)] = &[
            (TAG_FALSE, "False"),
            (TAG_TRUE, "True"),
            (TAG_VOID, "Void"),
            (TAG_ERROR, "Error"),
            (TAG_U32, "U32Val"),
            (TAG_I32, "I32Val"),
            (TAG_U64_SMALL, "U64Small"),
            (TAG_I64_SMALL, "I64Small"),
            (TAG_TIMEPOINT_SMALL, "TimepointSmall"),
            (TAG_DURATION_SMALL, "DurationSmall"),
            (TAG_U128_SMALL, "U128Small"),
            (TAG_I128_SMALL, "I128Small"),
            (TAG_U256_SMALL, "U256Small"),
            (TAG_I256_SMALL, "I256Small"),
            (TAG_SYMBOL_SMALL, "SymbolSmall"),
            (TAG_U64_OBJECT, "U64Object"),
            (TAG_I64_OBJECT, "I64Object"),
            (TAG_TIMEPOINT_OBJECT, "TimepointObject"),
            (TAG_DURATION_OBJECT, "DurationObject"),
            (TAG_U128_OBJECT, "U128Object"),
            (TAG_I128_OBJECT, "I128Object"),
            (TAG_U256_OBJECT, "U256Object"),
            (TAG_I256_OBJECT, "I256Object"),
            (TAG_BYTES_OBJECT, "BytesObject"),
            (TAG_STRING_OBJECT, "StringObject"),
            (TAG_SYMBOL_OBJECT, "SymbolObject"),
            (TAG_VEC_OBJECT, "VecObject"),
            (TAG_MAP_OBJECT, "MapObject"),
            (TAG_ADDRESS_OBJECT, "AddressObject"),
            (TAG_MUXED_ADDRESS_OBJECT, "MuxedAddressObject"),
        ];
        for (tag, name) in expected {
            assert_eq!(val_tag_name(*tag), Some(*name), "tag {tag}");
        }
        // Reserved codes, bound markers, and the invalid `Bad` byte are not tags.
        for non_tag in [15u64, 63, 0x80, 0xFF] {
            assert_eq!(val_tag_name(non_tag), None, "byte {non_tag}");
        }
    }

    #[test]
    fn val_tag_const_expr_named_and_numeric_fallback() {
        assert_eq!(
            val_tag_const_expr(TAG_VEC_OBJECT),
            SorobanExpr::ValTagName("VecObject".to_string())
        );
        // Unknown tag byte falls back to a raw numeric literal.
        assert_eq!(val_tag_const_expr(0x99), SorobanExpr::U32Literal(0x99));
    }

    #[test]
    fn recognize_val_shape_rejects_or_without_shl_inner() {
        // `param | TAG` (no inner shift) is not a Val construction.
        let v = StackVal::BinOp(
            Box::new(StackVal::Param("p".to_string())),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_U32 as i64)),
        );
        assert_eq!(recognize_val_shape(&v), None);
    }

    #[test]
    fn stack_val_to_expr_non_tag_and_mask_is_unknown() {
        // `v & 0xF0` is not a tag extraction, so it stays unrecovered.
        let v = StackVal::BinOp(
            Box::new(StackVal::Param("p".to_string())),
            BinOper::And,
            Box::new(StackVal::I64(0xF0)),
        );
        assert_eq!(
            stack_val_to_expr(&v, &[], &empty_registry(), None),
            SorobanExpr::UnknownVal
        );
    }

    #[test]
    fn extract_u32_from_stack_val_payload_variants() {
        // i32 payload.
        let i32_payload = StackVal::BinOp(
            Box::new(shl(StackVal::I32(9), 32)),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_U32 as i64)),
        );
        assert_eq!(extract_u32_from_stack_val(&i32_payload), Some(9));
        // Non-integer payload: no value.
        let param_payload = StackVal::BinOp(
            Box::new(shl(StackVal::Param("p".to_string()), 32)),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_U32 as i64)),
        );
        assert_eq!(extract_u32_from_stack_val(&param_payload), None);
        // A BinOp that isn't a U32 construction: no value.
        let not_construct = StackVal::BinOp(
            Box::new(StackVal::Param("p".to_string())),
            BinOper::And,
            Box::new(StackVal::I64(0xFF)),
        );
        assert_eq!(extract_u32_from_stack_val(&not_construct), None);
    }

    #[test]
    fn extract_frame_slot_from_stack_val_decodes_and_rejects() {
        let encoded = StackVal::BinOp(
            Box::new(shl(StackVal::FrameSlot(3, SlotOffset::at(16)), 32)),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_U32 as i64)),
        );
        assert_eq!(extract_frame_slot_from_stack_val(&encoded), Some((3, 16)));
        // Direct frame slot passes through.
        assert_eq!(
            extract_frame_slot_from_stack_val(&StackVal::FrameSlot(1, SlotOffset::at(8))),
            Some((1, 8))
        );
        // A U32 construction over a non-frame-slot payload is rejected.
        let not_slot = StackVal::BinOp(
            Box::new(shl(StackVal::I64(5), 32)),
            BinOper::Or,
            Box::new(StackVal::I64(TAG_U32 as i64)),
        );
        assert_eq!(extract_frame_slot_from_stack_val(&not_slot), None);
    }

    #[test]
    fn lower_tag_comparison_handles_both_orders_and_misses() {
        let reg = empty_registry();
        // tag-of on the left.
        let (l, r) = lower_tag_comparison(
            &tag_of("v"),
            &StackVal::I64(75),
            &[],
            &reg,
            None,
            &mut Vec::new(),
        )
        .unwrap();
        assert_eq!(
            l,
            SorobanExpr::ValTag(Box::new(SorobanExpr::Param("v".to_string())))
        );
        assert_eq!(r, SorobanExpr::ValTagName("VecObject".to_string()));
        // tag-of on the right.
        let (l, r) = lower_tag_comparison(
            &StackVal::I64(75),
            &tag_of("v"),
            &[],
            &reg,
            None,
            &mut Vec::new(),
        )
        .unwrap();
        assert_eq!(l, SorobanExpr::ValTagName("VecObject".to_string()));
        assert_eq!(
            r,
            SorobanExpr::ValTag(Box::new(SorobanExpr::Param("v".to_string())))
        );
        // Neither side is a tag check.
        assert!(
            lower_tag_comparison(
                &StackVal::Param("x".to_string()),
                &StackVal::I64(1),
                &[],
                &reg,
                None,
                &mut Vec::new()
            )
            .is_none()
        );
    }

    #[test]
    fn is_tag_check_condition_detects_tag_compares() {
        // `(v & 0xFF) != TAG`, both operand orders.
        assert!(is_tag_check_condition(&StackVal::Compare(
            Box::new(tag_of("v")),
            CmpOp::Ne,
            Box::new(StackVal::I64(TAG_VEC_OBJECT as i64)),
        )));
        assert!(is_tag_check_condition(&StackVal::Compare(
            Box::new(StackVal::I64(TAG_VEC_OBJECT as i64)),
            CmpOp::Eq,
            Box::new(tag_of("v")),
        )));
        // Not a tag comparison.
        assert!(!is_tag_check_condition(&StackVal::Compare(
            Box::new(StackVal::Param("a".to_string())),
            CmpOp::Eq,
            Box::new(StackVal::Param("b".to_string())),
        )));
        // Not a comparison at all.
        assert!(!is_tag_check_condition(&StackVal::Param("a".to_string())));
    }

    fn empty_lift_module() -> WasmModule {
        WasmModule::parse(b"\0asm\x01\x00\x00\x00").expect("empty WASM parses")
    }

    /// Fixture for the issue-#34 tranche-2 detectors. Imports: 0=has, 1=get
    /// (ledger), 2=obj_to_u128_hi64, 3=obj_to_u128_lo64, 4=obj_to_u64,
    /// 5=put. Functions: 6 = defaulting u128 getter `[lo@0, hi@8]`;
    /// 7 = pure u128 TryFromVal decode `[disc@0, err@8, lo@16, hi@24]`;
    /// 8 = pure u64 TryFromVal decode `[disc@0, val@8]`; 9 = a getter that
    /// ALSO puts (negative); 10 = a decode of BOTH widths (negative);
    /// 13 = u64 decode that REUSES the val local for its result after the
    /// decode window (aqua's real decoder shape — must still classify).
    fn tranche2_module() -> WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (import "l" "0" (func (param i64 i64) (result i64)))
                (import "l" "1" (func (param i64 i64) (result i64)))
                (import "i" "5" (func (param i64) (result i64)))
                (import "i" "4" (func (param i64) (result i64)))
                (import "i" "0" (func (param i64) (result i64)))
                (import "l" "_" (func (param i64 i64 i64) (result i64)))
                (func (param i32)                                   ;; 6
                    (local i64 i64)
                    local.get 0
                    block (result i64)
                        i64.const 0
                        i64.const 100 i64.const 2 call 0
                        i32.wrap_i64 i32.eqz br_if 0
                        drop
                        i64.const 100 i64.const 2 call 1
                        local.tee 1
                        call 2 local.set 2
                        local.get 1 call 3
                    end
                    i64.store
                    local.get 0 local.get 2 i64.store offset=8)
                (func (param i32 i64)                               ;; 7
                    local.get 0 i64.const 0 i64.store
                    local.get 0 local.get 1 call 2 i64.store offset=24
                    local.get 0 local.get 1 call 3 i64.store offset=16)
                (func (param i32 i64)                               ;; 8
                    local.get 0 i64.const 0 i64.store
                    local.get 0 local.get 1 call 4 i64.store offset=8)
                (func (param i32)                                   ;; 9
                    (local i64 i64)
                    local.get 0
                    block (result i64)
                        i64.const 0
                        i64.const 100 i64.const 2 call 0
                        i32.wrap_i64 i32.eqz br_if 0
                        drop
                        i64.const 100 i64.const 2 call 1
                        local.tee 1
                        call 2 local.set 2
                        local.get 1 call 3
                    end
                    i64.store
                    local.get 0 local.get 2 i64.store offset=8
                    i64.const 100 i64.const 0 i64.const 2 call 5 drop)
                (func (param i32 i64)                               ;; 10
                    local.get 0 i64.const 0 i64.store
                    local.get 0 local.get 1 call 2 i64.store offset=24
                    local.get 0 local.get 1 call 3 i64.store offset=16
                    local.get 0 local.get 1 call 4 i64.store offset=8)
                (func (param i32 i64)                               ;; 11
                    local.get 1 i64.const 8 i64.shr_u local.set 1
                    local.get 0 i64.const 0 i64.store
                    local.get 0 local.get 1 call 4 i64.store offset=8)
                (func (param i32 i64)                               ;; 12
                    local.get 0 i64.const 0 i64.store
                    local.get 0 local.get 1 call 4 i64.store offset=8
                    local.get 0 i64.const 7 i64.store offset=32)
                (func (param i32 i64)                               ;; 13
                    local.get 0 i64.const 0 i64.store
                    local.get 1 call 4 local.set 1
                    local.get 0 local.get 1 i64.store offset=8)
                (func (param i32 i64)                               ;; 14
                    loop
                        local.get 1 call 4 local.set 1
                        local.get 1 i64.const 0 i64.ne br_if 0
                    end
                    local.get 0 i64.const 0 i64.store
                    local.get 0 local.get 1 i64.store offset=8)
            )"#,
        )
        .expect("wat parses");
        WasmModule::parse(&wasm).expect("module parses")
    }

    /// Fixture for the issue-#34 tranche-3 recognizers. Imports: 0=has, 1=get
    /// (ledger). Functions: 2 = `(i32,i32)->i64` small-symbol builder (reads
    /// name bytes from LM); 3 = `(i32)->i64` immediate-selector DataKey ctor
    /// (br_table over the selector → symbol via 2); 4 = load-struct wrapper
    /// whose key is `ctor(0)`; 5 = wrapper reading TWO different keys
    /// (`ctor(0)` and `ctor(1)`) → ambiguous; 6 = divmod-style core (5-param,
    /// div_u); 7 = plain delegation wrapper forwarding limbs verbatim to 6;
    /// 8 = transforming wrapper (doubles a limb before calling 6);
    /// 9 = wrapper storing a PARAM (not the core's result) to out;
    /// 10 = wrapper copying the core's REMAINDER slots `[16, 24]`.
    /// Data: "AdmCfg" at 2000, "UsrCfg" at 2006.
    fn tranche3_module() -> WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (import "l" "0" (func (param i64 i64) (result i64)))
                (import "l" "1" (func (param i64 i64) (result i64)))
                (memory 1)
                (data (i32.const 2000) "AdmCfgUsrCfg")
                (func (;2;) (param i32 i32) (result i64)
                    (local i64 i32)
                    ;; the char-class constants the small-symbol shape gate
                    ;; keys on (is_small_symbol_encoder): '_', '0', 'A', 'a'
                    i32.const 95 drop
                    i32.const 48 drop
                    i32.const 65 drop
                    i32.const 97 drop
                    loop
                        local.get 3 local.get 1 i32.lt_u
                        if
                            local.get 2 i64.const 6 i64.shl
                            local.get 0 local.get 3 i32.add i32.load8_u
                            i64.extend_i32_u i64.const 32 i64.sub i64.or
                            local.set 2
                            local.get 3 i32.const 1 i32.add local.set 3
                            br 1
                        end
                    end
                    local.get 2 i64.const 8 i64.shl i64.const 14 i64.or)
                (func (;3;) (param i32) (result i64)
                    block
                        block
                            local.get 0 br_table 0 1 0
                        end
                        i32.const 2000 i32.const 6 call 2
                        return
                    end
                    i32.const 2006 i32.const 6 call 2)
                (func (;4;) (param i32)
                    (local i64)
                    i32.const 0 call 3 local.tee 1
                    i64.const 2 call 0 drop
                    local.get 1 i64.const 2 call 1
                    local.set 1
                    local.get 0 local.get 1 i64.store)
                (func (;5;) (param i32)
                    (local i64)
                    i32.const 0 call 3
                    i64.const 2 call 0 drop
                    i32.const 1 call 3
                    i64.const 2 call 1 local.set 1
                    local.get 0 local.get 1 i64.store)
                (func (;6;) (param i32 i64 i64 i64 i64)
                    local.get 0
                    local.get 1 local.get 3 i64.div_u
                    i64.store
                    local.get 0 i64.const 0 i64.store offset=8)
                (func (;7;) (param i32 i64 i64 i64 i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 5 global.set 0
                    local.get 5
                    local.get 1 local.get 2 local.get 3 local.get 4
                    call 6
                    local.get 0 local.get 5 i64.load i64.store
                    local.get 0 local.get 5 i64.load offset=8 i64.store offset=8
                    local.get 5 i32.const 16 i32.add global.set 0)
                (func (;8;) (param i32 i64 i64 i64 i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 5 global.set 0
                    local.get 5
                    local.get 1 i64.const 1 i64.shl
                    local.get 2 local.get 3 local.get 4
                    call 6
                    local.get 0 local.get 5 i64.load i64.store
                    local.get 5 i32.const 16 i32.add global.set 0)
                (func (;9;) (param i32 i64 i64 i64 i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 5 global.set 0
                    local.get 5
                    local.get 1 local.get 2 local.get 3 local.get 4
                    call 6
                    local.get 0 local.get 1 i64.store
                    local.get 0 local.get 5 i64.load offset=8 i64.store offset=8
                    local.get 5 i32.const 16 i32.add global.set 0)
                (func (;10;) (param i32 i64 i64 i64 i64)
                    (local i32)
                    global.get 0 i32.const 32 i32.sub local.tee 5 global.set 0
                    local.get 5
                    local.get 1 local.get 2 local.get 3 local.get 4
                    call 6
                    local.get 0 local.get 5 i64.load offset=16 i64.store
                    local.get 0 local.get 5 i64.load offset=24 i64.store offset=8
                    local.get 5 i32.const 32 i32.add global.set 0)
                (func (;11;) (param i32)
                    i32.const 0 call 3 drop
                    local.get 0 i64.const 0 i64.store)
                (func (;12;) (param i64 i64) (result i32)
                    local.get 0 local.get 1 call 0 i64.const 1 i64.eq)
                (func (;13;) (param i32)
                    (local i64)
                    i32.const 0 call 3 local.tee 1
                    i64.const 2 call 12 drop
                    local.get 1 i64.const 2 call 1 local.set 1
                    local.get 0 local.get 1 i64.store)
                (func (;14;) (param i32) (result i64)
                    (local i32)
                    loop
                        local.get 1 i32.const 1 i32.add local.tee 1
                        i32.const 3 i32.lt_u br_if 0
                    end
                    i32.const 2000 i32.const 6 call 2)
                (func (;15;) (param i32)
                    (local i64)
                    i32.const 2000 call 14 local.tee 1
                    i64.const 2 call 0 drop
                    local.get 1 i64.const 2 call 1 local.set 1
                    local.get 0 local.get 1 i64.store)
                (global (mut i32) (i32.const 8192))
            )"#,
        )
        .expect("wat parses");
        WasmModule::parse(&wasm).expect("module parses")
    }

    fn struct_getter_registry() -> crate::spec::registry::TypeRegistry {
        let mut reg = empty_registry();
        let field = |name: &str, t: ScSpecTypeDef| stellar_xdr::ScSpecUdtStructFieldV0 {
            doc: "".try_into().unwrap(),
            name: name.try_into().unwrap(),
            type_: t,
        };
        reg.structs.insert(
            "RewardCfg".to_string(),
            stellar_xdr::ScSpecUdtStructV0 {
                doc: "".try_into().unwrap(),
                lib: "".try_into().unwrap(),
                name: "RewardCfg".try_into().unwrap(),
                fields: vec![
                    field("expired", ScSpecTypeDef::U64),
                    field("tps", ScSpecTypeDef::U128),
                ]
                .try_into()
                .unwrap(),
            },
        );
        reg
    }

    /// Self-contained fixture for [`detect_fallible_struct_getter`] and its
    /// call-site recovery arm (issue #34 t4/t5): imports 0=has, 1=get,
    /// 2=map_unpack, 3=obj_to_u64, 4=obj_to_u128_hi64, 5=obj_to_u128_lo64,
    /// 6=extend_current_contract_instance_and_code_ttl,
    /// 7=extend_contract_data_ttl; func 8 = small-symbol encoder, 9 =
    /// DataKey ctor (selector → "CfgKey"), 10 = u64 decoder, 11 = u128
    /// decoder, 12 = thin constant instance-TTL wrapper (threshold 100,
    /// extend_to 200), 13 = THE fallible struct getter (bumps the instance
    /// TTL via 12, then has/get/unpack/decode), 14 = a getter variant with
    /// an UNPROVEN keyed TTL extension (must refuse), 15 = a caller that
    /// frames an out pointer, calls 13, and returns the u64 field slot, 16 =
    /// a non-constant direct instance bump (must refuse). Data: field names
    /// "expired"/"tps" + their `(ptr, len)` descriptor array + "CfgKey".
    fn struct_getter_module() -> WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (import "l" "0" (func (param i64 i64) (result i64)))
                (import "l" "1" (func (param i64 i64) (result i64)))
                (import "m" "a" (func (param i64 i32 i32 i32 i32) (result i64)))
                (import "i" "0" (func (param i64) (result i64)))
                (import "i" "5" (func (param i64) (result i64)))
                (import "i" "4" (func (param i64) (result i64)))
                (import "l" "8" (func (param i64 i64) (result i64)))
                (import "l" "7" (func (param i64 i64 i64 i64) (result i64)))
                (memory 1)
                (global (mut i32) (i32.const 8192))
                (data (i32.const 2000) "expiredtpsCfgKey")
                (data (i32.const 2016) "\d0\07\00\00\07\00\00\00\d7\07\00\00\03\00\00\00")
                (func (;8;) (param i32 i32) (result i64)
                    (local i64 i32)
                    i32.const 95 drop
                    i32.const 48 drop
                    i32.const 65 drop
                    i32.const 97 drop
                    loop
                        local.get 3 local.get 1 i32.lt_u
                        if
                            local.get 2 i64.const 6 i64.shl
                            local.get 0 local.get 3 i32.add i32.load8_u
                            i64.extend_i32_u i64.const 32 i64.sub i64.or
                            local.set 2
                            local.get 3 i32.const 1 i32.add local.set 3
                            br 1
                        end
                    end
                    local.get 2 i64.const 8 i64.shl i64.const 14 i64.or)
                (func (;9;) (param i32) (result i64)
                    block
                        block
                            local.get 0 br_table 0 1 0
                        end
                        i32.const 2010 i32.const 6 call 8
                        return
                    end
                    i32.const 2010 i32.const 6 call 8)
                (func (;10;) (param i32 i64)
                    local.get 0 i64.const 0 i64.store
                    local.get 0 local.get 1 call 3 i64.store offset=8)
                (func (;11;) (param i32 i64)
                    local.get 0 i64.const 0 i64.store
                    local.get 0 local.get 1 call 4 i64.store offset=24
                    local.get 0 local.get 1 call 5 i64.store offset=16)
                (func (;12;)
                    i64.const 429496729604
                    i64.const 858993459204
                    call 6
                    drop)
                (func (;13;) (param i32)
                    (local i64 i64)
                    call 12
                    block (result i64)
                        i32.const 0 call 9 local.tee 1
                        i64.const 2 call 0
                        i32.wrap_i64 i32.eqz
                        if
                            i64.const 0 local.set 2
                            i64.const 0
                            br 1
                        end
                        local.get 1 i64.const 2 call 1 local.set 1
                        local.get 1 i32.const 2016 i32.const 2 local.get 0 i32.const 2 call 2 drop
                        i32.const 4096 local.get 1 call 10
                        i32.const 4096 local.get 1 call 11
                        i64.const 5
                    end
                    drop
                    local.get 0 i64.const 0 i64.store
                    local.get 0 i64.const 0 i64.store offset=8
                    local.get 0 i64.const 0 i64.store offset=16)
                (func (;14;) (param i32)
                    (local i64 i64)
                    i64.const 2 i64.const 2 i64.const 429496729604 i64.const 858993459204
                    call 7
                    drop
                    block (result i64)
                        i32.const 0 call 9 local.tee 1
                        i64.const 2 call 0
                        i32.wrap_i64 i32.eqz
                        if
                            i64.const 0 local.set 2
                            i64.const 0
                            br 1
                        end
                        local.get 1 i64.const 2 call 1 local.set 1
                        local.get 1 i32.const 2016 i32.const 2 local.get 0 i32.const 2 call 2 drop
                        i32.const 4096 local.get 1 call 10
                        i32.const 4096 local.get 1 call 11
                        i64.const 5
                    end
                    drop
                    local.get 0 i64.const 0 i64.store
                    local.get 0 i64.const 0 i64.store offset=8
                    local.get 0 i64.const 0 i64.store offset=16)
                (func (;15;) (result i64)
                    (local i32)
                    global.get 0 i32.const 32 i32.sub local.tee 0 global.set 0
                    local.get 0 call 13
                    local.get 0 i64.load offset=16
                    local.get 0 i32.const 32 i32.add global.set 0)
                (func (;16;)
                    (local i64)
                    local.get 0 local.get 0 call 6 drop)
            )"#,
        )
        .expect("wat parses");
        WasmModule::parse(&wasm).expect("module parses")
    }

    #[test]
    fn detect_fallible_struct_getter_classifies_and_resolves() {
        let m = struct_getter_module();
        let reg = struct_getter_registry();
        let info = detect_fallible_struct_getter(&m, &reg, 13)
            .expect("the fallible struct getter classifies");
        assert_eq!(info.type_name, "RewardCfg");
        assert_eq!(info.u128_field, "tps");
        assert_eq!(info.u64_field, "expired");
        assert_eq!(info.storage_type, StorageType::Instance);
        assert_eq!(
            info.key,
            SorobanExpr::SymbolLiteral("CfgKey".to_string()),
            "the ctor call micro-executes to the storage key"
        );
        assert_eq!(
            info.instance_ttl_bumps,
            vec![(100, 200)],
            "the thin-wrapper instance bump is proven with decoded constants"
        );
        // Wrong shapes never classify: a bare decoder, and the ctor itself.
        assert!(detect_fallible_struct_getter(&m, &reg, 10).is_none());
        assert!(detect_fallible_struct_getter(&m, &reg, 9).is_none());
        // An unproven TTL-family call (keyed extend_contract_data_ttl)
        // refuses the whole recognition — reconstructing without it would
        // silently drop a ledger side effect.
        assert!(detect_fallible_struct_getter(&m, &reg, 14).is_none());
    }

    /// Fixture for the VALUE-RETURNING getter classes (issue #34 t6,
    /// [`detect_fallible_value_getter`] / [`detect_defaulting_map_getter`]):
    /// imports 0=has, 1=get, 2=fail_with_error, 3=instance-TTL bump,
    /// 4=map_new; func 5 = small-symbol encoder, 6 = DataKey ctor
    /// (selector → "TokenAddr"/"Other"), 7 = thin TTL wrapper (100, 200),
    /// 8 = fail wrapper, 9 = has wrapper (`(i64,i64) -> i32`), 10 = THE
    /// fallible value getter (Bool-Val-compare has shape), 11 = its
    /// caller, 12 = NEGATIVE: returns a constant instead of the get
    /// result, 13 = THE defaulting map getter (has-wrapper shape, select
    /// tail), 14 = its caller, 15 = NEGATIVE: the has flag does not guard
    /// the get (`i32.eqz` fed to `drop`, not `br_if`), 16 = NEGATIVE: the
    /// tag guard is not adjacent to the get-tee.
    fn value_getter_module() -> WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (import "l" "0" (func (param i64 i64) (result i64)))
                (import "l" "1" (func (param i64 i64) (result i64)))
                (import "x" "5" (func (param i64) (result i64)))
                (import "l" "8" (func (param i64 i64) (result i64)))
                (import "m" "_" (func (result i64)))
                (memory 1)
                (data (i32.const 2000) "TokenAddrOther")
                (func (;5;) (param i32 i32) (result i64)
                    (local i64 i32)
                    i32.const 95 drop
                    i32.const 48 drop
                    i32.const 65 drop
                    i32.const 97 drop
                    loop
                        local.get 3 local.get 1 i32.lt_u
                        if
                            local.get 2 i64.const 6 i64.shl
                            local.get 0 local.get 3 i32.add i32.load8_u
                            i64.extend_i32_u i64.const 32 i64.sub i64.or
                            local.set 2
                            local.get 3 i32.const 1 i32.add local.set 3
                            br 1
                        end
                    end
                    local.get 2 i64.const 8 i64.shl i64.const 14 i64.or)
                (func (;6;) (param i32) (result i64)
                    block
                        block
                            local.get 0 br_table 0 1 0
                        end
                        i32.const 2000 i32.const 9 call 5
                        return
                    end
                    i32.const 2009 i32.const 5 call 5)
                (func (;7;)
                    i64.const 429496729604
                    i64.const 858993459204
                    call 3
                    drop)
                (func (;8;) (param i64)
                    local.get 0 call 2 drop)
                (func (;9;) (param i64 i64) (result i32)
                    local.get 0 local.get 1 call 0 i64.const 1 i64.eq)
                (func (;10;) (result i64)
                    (local i64)
                    call 7
                    block
                        i32.const 0 call 6 local.tee 0
                        i64.const 2 call 0
                        i64.const 1 i64.eq
                        if
                            local.get 0 i64.const 2 call 1 local.tee 0
                            i64.const 255 i64.and i64.const 77 i64.ne br_if 1
                            local.get 0
                            return
                        end
                    end
                    i64.const 2151778615299
                    call 8
                    unreachable)
                (func (;11;) (result i64)
                    call 10)
                (func (;12;) (result i64)
                    (local i64)
                    call 7
                    block
                        i32.const 0 call 6 local.tee 0
                        i64.const 2 call 0
                        i64.const 1 i64.eq
                        if
                            local.get 0 i64.const 2 call 1 local.tee 0
                            i64.const 255 i64.and i64.const 77 i64.ne br_if 1
                            i64.const 2
                            return
                        end
                    end
                    i64.const 2151778615299
                    call 8
                    unreachable)
                (func (;13;) (result i64)
                    (local i64 i64 i32)
                    call 7
                    block
                        i32.const 0 call 6 local.tee 0
                        i64.const 2 call 9 local.tee 2
                        i32.eqz br_if 0
                        local.get 0 i64.const 2 call 1 local.tee 1
                        i64.const 255 i64.and i64.const 76 i64.eq br_if 0
                        unreachable
                    end
                    local.get 1
                    call 4
                    local.get 2
                    select)
                (func (;14;) (result i64)
                    call 13)
                (func (;15;) (result i64)
                    (local i64 i64 i32)
                    call 7
                    block
                        i32.const 0 call 6 local.tee 0
                        i64.const 2 call 9 local.tee 2
                        i32.eqz drop
                        local.get 0 i64.const 2 call 1 local.tee 1
                        i64.const 255 i64.and i64.const 76 i64.eq br_if 0
                        unreachable
                    end
                    local.get 1
                    call 4
                    local.get 2
                    select)
                (func (;16;) (result i64)
                    (local i64)
                    call 7
                    block
                        i32.const 0 call 6 local.tee 0
                        i64.const 2 call 0
                        i64.const 1 i64.eq
                        if
                            local.get 0 i64.const 2 call 1 local.tee 0
                            drop
                            local.get 0
                            i64.const 255 i64.and i64.const 77 i64.ne br_if 1
                            local.get 0
                            return
                        end
                    end
                    i64.const 2151778615299
                    call 8
                    unreachable)
            )"#,
        )
        .expect("wat parses");
        WasmModule::parse(&wasm).expect("module parses")
    }

    #[test]
    fn detect_fallible_value_getter_classifies_and_refuses() {
        let m = value_getter_module();
        let reg = empty_registry();
        let info = detect_fallible_value_getter(&m, &reg, 10).expect("the value getter classifies");
        assert_eq!(info.storage_type, StorageType::Instance);
        assert_eq!(
            info.key,
            SorobanExpr::SymbolLiteral("TokenAddr".to_string())
        );
        assert_eq!(info.tag, 77, "the guard names AddressObject");
        assert_eq!(info.instance_ttl_bumps, vec![(100, 200)]);
        let SorobanExpr::ContractError { error_code, .. } = info.error else {
            panic!("expected the decoded contract error, got {:?}", info.error);
        };
        assert_eq!(error_code, 501);
        // The value linkage is proven, not assumed: a variant returning a
        // CONSTANT instead of the get result refuses.
        assert!(detect_fallible_value_getter(&m, &reg, 12).is_none());
        // The tag guard must be ADJACENT to the get-tee (value linkage).
        assert!(detect_fallible_value_getter(&m, &reg, 16).is_none());
        // Wrong shapes never classify: the ctor and the encoder.
        assert!(detect_fallible_value_getter(&m, &reg, 6).is_none());
        assert!(detect_fallible_value_getter(&m, &reg, 5).is_none());
    }

    #[test]
    fn defaulting_map_getter_classifies_and_refuses() {
        let m = value_getter_module();
        let reg = empty_registry();
        let info =
            detect_defaulting_collection_getter(&m, &reg, 13).expect("the map getter classifies");
        assert_eq!(info.storage_type, StorageType::Instance);
        assert_eq!(info.collection_type, "Map");
        assert_eq!(
            info.key,
            SorobanExpr::SymbolLiteral("TokenAddr".to_string())
        );
        assert_eq!(info.instance_ttl_bumps, vec![(100, 200)]);
        // The has flag must GUARD the get: the eqz-fed-to-drop variant
        // (an unconditional get that would trap on a missing key) refuses.
        assert!(detect_defaulting_collection_getter(&m, &reg, 15).is_none());
        // The fallible sibling never cross-classifies (ne-guard, no select
        // tail) — and vice versa.
        assert!(detect_defaulting_collection_getter(&m, &reg, 10).is_none());
        assert!(detect_fallible_value_getter(&m, &reg, 13).is_none());
    }

    #[test]
    fn defaulting_map_getter_recovers_at_call_site() {
        // End-to-end: lifting the caller (func 14) binds the defaulting
        // map get once and returns the binding.
        cov_mark::check!(defaulting_collection_getter_recovered);
        let m = value_getter_module();
        let reg = empty_registry();
        let result = lift_inline_call(
            &m,
            &reg,
            14,
            Vec::new(),
            0,
            Rc::new(RefCell::new(HashMap::new())),
            Rc::new(RefCell::new(0)),
            Rc::new(RefCell::new(Vec::new())),
        );
        let (stmts, return_expr) = result.content.expect("the recovery is effectful");
        let binding_idx = stmts
            .iter()
            .find_map(|s| match s {
                SorobanStmt::Let {
                    name,
                    value:
                        SorobanExpr::StorageGet {
                            storage_type: StorageType::Instance,
                            key,
                            unwrap: false,
                            on_missing: Some(miss),
                        },
                    ..
                } => {
                    assert_eq!(**key, SorobanExpr::SymbolLiteral("TokenAddr".to_string()));
                    assert_eq!(
                        miss.as_ref(),
                        &SorobanExpr::CollectionNew("Map".to_string()),
                        "the missing path is the proven empty-map default"
                    );
                    name.strip_prefix("var_")
                        .and_then(|n| n.parse::<u32>().ok())
                }
                _ => None,
            })
            .expect("the map get is bound: {stmts:?}");
        assert_eq!(
            return_expr,
            Some(SorobanExpr::Local(binding_idx)),
            "the caller returns the binding"
        );
    }

    /// Compact fixture for the VEC-defaulting getter (issue #34 t7): the
    /// tag-75 / vec_new sibling of the map getter. Imports 0=has, 1=get,
    /// 2=vec_new; func 3 = the getter (`if has(K) { v=get(K);
    /// tag(v)==75 br }; select(v, vec_new(), c)`), 4 = its caller. Key is
    /// a bare Val-encoded symbol two before the get import (the
    /// `fallible_get_const_key` window), so no ctor is needed.
    fn vec_getter_module() -> WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (import "l" "0" (func (param i64 i64) (result i64)))
                (import "l" "1" (func (param i64 i64) (result i64)))
                (import "v" "_" (func (result i64)))
                (memory 1)
                (func (;3;) (result i64)
                    (local i64 i64 i32)
                    block
                        i64.const 275146723598473 i64.const 2 call 0 local.tee 2
                        i32.eqz br_if 0
                        i64.const 275146723598473 i64.const 2 call 1 local.tee 1
                        i64.const 255 i64.and i64.const 75 i64.eq br_if 0
                        unreachable
                    end
                    local.get 1
                    call 2
                    local.get 2
                    select)
                (func (;4;) (result i64)
                    call 3)
            )"#,
        )
        .expect("wat parses");
        WasmModule::parse(&wasm).expect("module parses")
    }

    #[test]
    fn defaulting_vec_getter_classifies_and_recovers() {
        cov_mark::check!(defaulting_collection_getter_recovered);
        let m = vec_getter_module();
        let reg = empty_registry();
        let info =
            detect_defaulting_collection_getter(&m, &reg, 3).expect("the vec getter classifies");
        assert_eq!(info.collection_type, "Vec", "tag 75 + vec_new → Vec");
        // A MapObject-kind cross-check would need tag 76 + map_new; the
        // detector pins the kind to the tag guard's constant.
        let result = lift_inline_call(
            &m,
            &reg,
            4,
            Vec::new(),
            0,
            Rc::new(RefCell::new(HashMap::new())),
            Rc::new(RefCell::new(0)),
            Rc::new(RefCell::new(Vec::new())),
        );
        let (stmts, _) = result.content.expect("the recovery is effectful");
        assert!(
            stmts.iter().any(|s| matches!(
                s,
                SorobanStmt::Let {
                    value: SorobanExpr::StorageGet { on_missing: Some(miss), .. },
                    ..
                } if matches!(miss.as_ref(), SorobanExpr::CollectionNew(c) if c == "Vec")
            )),
            "the missing path is the proven empty-vec default: {stmts:?}"
        );
    }

    #[test]
    fn fallible_value_getter_recovers_at_call_site() {
        // End-to-end: lifting the caller (func 11) reconstructs the TTL
        // bump and returns the faithful Address-pinned defaulting get.
        cov_mark::check!(fallible_value_getter_recovered);
        let m = value_getter_module();
        let reg = empty_registry();
        let result = lift_inline_call(
            &m,
            &reg,
            11,
            Vec::new(),
            0,
            Rc::new(RefCell::new(HashMap::new())),
            Rc::new(RefCell::new(0)),
            Rc::new(RefCell::new(Vec::new())),
        );
        let (stmts, return_expr) = result.content.expect("the recovery is effectful");
        assert!(
            stmts.iter().any(|s| matches!(
                s,
                SorobanStmt::Expr(SorobanExpr::ExtendInstanceAndCodeTtl { .. })
            )),
            "the proven TTL bump is reconstructed: {stmts:?}"
        );
        // The value is bound ONCE (a per-consumer re-read would silently
        // drop mutations); the caller returns the binding.
        let binding_idx = stmts
            .iter()
            .find_map(|s| match s {
                SorobanStmt::Let {
                    name,
                    value: SorobanExpr::CastAs { value, target_type },
                    ..
                } => {
                    assert_eq!(target_type, "Address");
                    let SorobanExpr::StorageGet {
                        storage_type: StorageType::Instance,
                        key,
                        unwrap: false,
                        on_missing: Some(miss),
                    } = value.as_ref()
                    else {
                        panic!("expected the fallible get, got {value:?}");
                    };
                    assert_eq!(**key, SorobanExpr::SymbolLiteral("TokenAddr".to_string()));
                    assert!(
                        matches!(miss.as_ref(), SorobanExpr::PanicWithError(_)),
                        "the missing path panics with the proven error: {miss:?}"
                    );
                    name.strip_prefix("var_")
                        .and_then(|n| n.parse::<u32>().ok())
                }
                _ => None,
            })
            .expect("the get is bound: {stmts:?}");
        assert_eq!(
            return_expr,
            Some(SorobanExpr::Local(binding_idx)),
            "the caller returns the binding"
        );
    }

    /// Fixture for the proven-zero gap lever ([`gap_row_proven_zero`] +
    /// `DkEval.gap_zero`): func 0 = small-symbol encoder, 1 = descriptor
    /// ctor (`disc = *(ptr)` → br_table → "GapKey"/"AltKey"), 2 = the only
    /// materialization of gap constant 3016 (a clean `[i32.const, call 1]`
    /// window), 3 = a bad use of gap constant 4016 (followed by a load, not
    /// a call), 4 = a bad below-slop neighbor of gap 5016 (5010 followed by
    /// drop), 5 = a ctor that STORES through its pointer (must bail eval).
    /// Data ends at 3004; addresses 3016/4016/5016 are all gaps.
    fn gap_ctor_module() -> WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (memory 1)
                (data (i32.const 2000) "GapKeyAltKey")
                (data (i32.const 3000) "\01")
                (func (;0;) (param i32 i32) (result i64)
                    (local i64 i32)
                    i32.const 95 drop
                    i32.const 48 drop
                    i32.const 65 drop
                    i32.const 97 drop
                    loop
                        local.get 3 local.get 1 i32.lt_u
                        if
                            local.get 2 i64.const 6 i64.shl
                            local.get 0 local.get 3 i32.add i32.load8_u
                            i64.extend_i32_u i64.const 32 i64.sub i64.or
                            local.set 2
                            local.get 3 i32.const 1 i32.add local.set 3
                            br 1
                        end
                    end
                    local.get 2 i64.const 8 i64.shl i64.const 14 i64.or)
                (func (;1;) (param i32) (result i64)
                    block
                        block
                            local.get 0 i32.load br_table 0 1 0
                        end
                        i32.const 2000 i32.const 6 call 0
                        return
                    end
                    i32.const 2006 i32.const 6 call 0)
                (func (;2;) (result i64)
                    i32.const 3016 call 1)
                (func (;3;) (result i32)
                    i32.const 4016 i32.load)
                (func (;4;)
                    i32.const 5010 drop
                    i32.const 5016 call 1 drop)
                (func (;5;) (param i32) (result i64)
                    local.get 0 i32.const 7 i32.store
                    i32.const 2000 i32.const 6 call 0)
                (func (;6;) (result i32)
                    i32.const 16000 i32.const 16 i32.add)
            )"#,
        )
        .expect("wat parses");
        WasmModule::parse(&wasm).expect("module parses")
    }

    #[test]
    fn gap_row_proven_zero_gates() {
        let m = gap_ctor_module();
        // 3016: only materialized as ctor 1's argument → proven.
        assert!(gap_row_proven_zero(&m, 1, 3016, 3032));
        // The proof is ctor-specific: the same row claimed for a different
        // callee is refused (the pointer demonstrably feeds func 1).
        assert!(!gap_row_proven_zero(&m, 0, 3016, 3032));
        // 4016: the constant is followed by a load, not a call → refused.
        assert!(!gap_row_proven_zero(&m, 1, 4016, 4032));
        // 5016: a below-slop neighbor constant (5010) escapes the call
        // window → refused (it could be a store base reaching the row).
        assert!(!gap_row_proven_zero(&m, 1, 5016, 5032));
        // 16016: a band constant feeding i32.add — the derived-pointer
        // shape that could reach the row from a farther base → refused.
        assert!(!gap_row_proven_zero(&m, 1, 16016, 16032));
        // A module reading any non-stack-pointer global refuses every gap
        // proof — a pointer-holding global could smuggle the row address
        // past the constant scan.
        let glob = wat::parse_str(
            r#"(module
                (memory 1)
                (global (mut i32) (i32.const 8192))
                (global (mut i32) (i32.const 0))
                (func (;0;) (result i32) global.get 1)
                (func (;1;) (param i32) (result i64) i64.const 0)
            )"#,
        )
        .expect("wat parses");
        let glob = WasmModule::parse(&glob).expect("module parses");
        assert!(!gap_row_proven_zero(&glob, 1, 3016, 3032));
        // A module containing bulk-memory ops refuses every gap proof.
        let bulk = wat::parse_str(
            r#"(module
                (memory 1)
                (func (;0;) (result i64) i32.const 3016 call 1)
                (func (;1;) (param i32) (result i64) i64.const 0)
                (func (;2;) (param i32 i32 i32)
                    local.get 0 local.get 1 local.get 2 memory.copy)
            )"#,
        )
        .expect("wat parses");
        let bulk = WasmModule::parse(&bulk).expect("module parses");
        assert!(!gap_row_proven_zero(&bulk, 1, 3016, 3032));
    }

    #[test]
    fn dk_eval_reads_proven_zero_gap_and_bails_on_absolute_store() {
        let m = gap_ctor_module();
        let eval = |target: u32, arg: i32, gap_zero: Option<(u32, u32)>| {
            let mut ev = DkEval {
                module: &m,
                mem: HashMap::new(),
                sp: DkVal::StackPtr(0),
                steps: 0,
                gap_zero,
            };
            ev.eval_call(target, vec![DkVal::I32(arg)], 0)
        };
        // The proven gap reads zero → disc 0 → the ctor's real bytecode
        // selects the variant-0 arm and builds "GapKey".
        cov_mark::check!(dk_gap_zero_read);
        let result = eval(1, 3016, Some((3016, 3032))).expect("eval completes");
        assert_eq!(
            dk_result_to_const_key(&result.expect("ctor returns a value")),
            Some(SorobanExpr::SymbolLiteral("GapKey".to_string()))
        );
        // Without the proof the gap load stays out of model → eval bails.
        assert_eq!(eval(1, 3016, None), None);
        // A read outside the proven range bails too.
        assert_eq!(eval(1, 4016, Some((3016, 3032))), None);
        // The store-through-pointer ctor bails EVEN with the proof — DkEval
        // stores require shadow-stack addresses, which is what makes a
        // completed eval a proof that the row is never written.
        assert_eq!(eval(5, 3016, Some((3016, 3032))), None);
    }

    #[test]
    fn gap_lever_never_bypasses_storage_consumption_gate() {
        // A getter-shaped body whose proven-gap ctor result does NOT feed a
        // storage probe (func 0 is the symbol encoder) must produce no key
        // candidate — the gap lever only changes how the eval reads the
        // descriptor, never which ctor results qualify as storage keys.
        let m = gap_ctor_module();
        let reg = empty_registry();
        use crate::wasm::ir::WasmInstr as WI;
        let getter = crate::wasm::ir::WasmFunction {
            index: 99,
            type_index: 0,
            locals: vec![],
            body: vec![
                WI::I32Const(3016),
                WI::Call(1),
                WI::LocalTee(1),
                WI::I64Const(2),
                WI::Call(0),
                WI::End,
            ],
        };
        assert_eq!(load_struct_const_key(&m, &reg, &getter), None);
    }

    #[test]
    fn collect_instance_ttl_bumps_proves_windows_and_refuses_nonconst() {
        let m = struct_getter_module();
        // The thin wrapper's own body is the direct-import const window.
        let bumps = collect_proven_instance_ttl_bumps(&m, m.get_function(12).unwrap());
        assert_eq!(bumps, Some(vec![(100, 200)]));
        // A direct instance bump with NON-constant operands proves nothing.
        assert_eq!(
            collect_proven_instance_ttl_bumps(&m, m.get_function(16).unwrap()),
            None
        );
        // No TTL calls at all → empty proof, not a refusal.
        assert_eq!(
            collect_proven_instance_ttl_bumps(&m, m.get_function(10).unwrap()),
            Some(vec![])
        );
        // POSITION is proven: the same wrapper call placed INSIDE a block
        // (after control flow — e.g. only on the key-present arm) is no
        // longer dominated by entry, so hoisting it unconditionally would
        // change ledger-rent behavior → the whole proof refuses.
        use crate::wasm::ir::{BlockType, WasmInstr as WI};
        let conditional_bump = crate::wasm::ir::WasmFunction {
            index: 99,
            type_index: 0,
            locals: vec![],
            body: vec![
                WI::Block {
                    block_type: BlockType::Empty,
                },
                WI::Call(12),
                WI::End,
                WI::End,
            ],
        };
        assert_eq!(
            collect_proven_instance_ttl_bumps(&m, &conditional_bump),
            None
        );
    }

    #[test]
    fn fallible_struct_getter_recovers_at_call_site() {
        // End-to-end through the Call handler: lifting the caller (func 15)
        // must reconstruct the getter at ONE point — the proven TTL bump,
        // the defaulting-get binding, and the u64 field slot flowing into
        // the caller's return — with the getter never inlined.
        cov_mark::check!(fallible_struct_getter_recovered);
        let m = struct_getter_module();
        let reg = struct_getter_registry();
        let result = lift_inline_call(
            &m,
            &reg,
            15,
            Vec::new(),
            0,
            Rc::new(RefCell::new(HashMap::new())),
            Rc::new(RefCell::new(0)),
            Rc::new(RefCell::new(Vec::new())),
        );
        let (stmts, return_expr) = result.content.expect("the recovery is effectful");
        assert!(
            stmts.iter().any(|s| matches!(
                s,
                SorobanStmt::Expr(SorobanExpr::ExtendInstanceAndCodeTtl { threshold, extend_to })
                    if **threshold == SorobanExpr::U32Literal(100)
                        && **extend_to == SorobanExpr::U32Literal(200)
            )),
            "the proven instance TTL bump is reconstructed: {stmts:?}"
        );
        let binding_name = stmts
            .iter()
            .find_map(|s| match s {
                SorobanStmt::Let {
                    name,
                    value:
                        SorobanExpr::CastAs {
                            value: get,
                            target_type,
                        },
                    ..
                } => {
                    let SorobanExpr::StorageGet {
                        storage_type: StorageType::Instance,
                        key,
                        unwrap: false,
                        on_missing: Some(default),
                    } = get.as_ref()
                    else {
                        return None;
                    };
                    assert_eq!(
                        target_type, "RewardCfg",
                        "the turbofish pins the value type"
                    );
                    assert_eq!(**key, SorobanExpr::SymbolLiteral("CfgKey".to_string()));
                    let SorobanExpr::StructConstruct { type_name, fields } = default.as_ref()
                    else {
                        panic!("expected the zero-default construct, got {default:?}");
                    };
                    assert_eq!(type_name, "RewardCfg");
                    assert_eq!(
                        fields,
                        &vec![
                            ("expired".to_string(), SorobanExpr::U64Literal(0)),
                            ("tps".to_string(), SorobanExpr::U128Literal(0)),
                        ],
                        "the missing-key default zeroes every spec field"
                    );
                    Some(name.clone())
                }
                _ => None,
            })
            .expect("the defaulting get is bound: {stmts:?}");
        let binding_idx: u32 = binding_name
            .strip_prefix("var_")
            .and_then(|n| n.parse().ok())
            .expect("binding is a var_N local");
        assert_eq!(
            return_expr,
            Some(SorobanExpr::FieldAccess {
                object: Box::new(SorobanExpr::Local(binding_idx)),
                field: "expired".to_string(),
            }),
            "the caller's u64 slot read resolves to the binding's field"
        );
    }

    #[test]
    fn dk_result_to_const_key_accepts_only_constant_symbols() {
        // A raw small-symbol Val / SymObj / vec of symbols → key; any
        // non-symbol element → not a constant key.
        let adm = encode_symbol_small("AdmCfg").expect("encodes");
        assert_eq!(
            dk_result_to_const_key(&DkVal::I64(adm)),
            Some(SorobanExpr::SymbolLiteral("AdmCfg".to_string()))
        );
        assert_eq!(
            dk_result_to_const_key(&DkVal::SymObj("LongSymbolName".to_string())),
            Some(SorobanExpr::SymbolLiteral("LongSymbolName".to_string()))
        );
        assert_eq!(
            dk_result_to_const_key(&DkVal::VecVal(vec![DkVal::I64(adm)])),
            Some(SorobanExpr::VecConstruct(vec![SorobanExpr::SymbolLiteral(
                "AdmCfg".to_string()
            )]))
        );
        assert_eq!(
            dk_result_to_const_key(&DkVal::VecVal(vec![DkVal::I64(adm), DkVal::Arg(1)])),
            None,
            "a runtime payload element means the key is not constant"
        );
        assert_eq!(dk_result_to_const_key(&DkVal::VecVal(vec![])), None);
    }

    #[test]
    fn load_struct_const_key_executes_ctor_and_rejects_ambiguity() {
        let m = tranche3_module();
        let reg = empty_registry();
        // Wrapper 4: key = ctor(0), micro-executed → Symbol("AdmCfg").
        let f4 = m.get_function(4).expect("func 4");
        assert_eq!(
            load_struct_const_key(&m, &reg, f4),
            Some(SorobanExpr::SymbolLiteral("AdmCfg".to_string()))
        );
        // Wrapper 5 reads two DIFFERENT keys → ambiguous → None.
        let f5 = m.get_function(5).expect("func 5");
        assert_eq!(load_struct_const_key(&m, &reg, f5), None);
        // greptile P1 shape: a ctor whose result does NOT feed a storage
        // probe (dropped here) is no key candidate → None.
        let f11 = m.get_function(11).expect("func 11");
        assert_eq!(load_struct_const_key(&m, &reg, f11), None);
        // The probe may be a thin INTERNAL `(i64, i64)` has/get wrapper
        // (the corpus routes has/get through such thunks) — func 13 feeds
        // the ctor result into wrapper 12.
        let f13 = m.get_function(13).expect("func 13");
        assert_eq!(
            load_struct_const_key(&m, &reg, f13),
            Some(SorobanExpr::SymbolLiteral("AdmCfg".to_string()))
        );
        // greptile P1 shape: a SMALL ctor whose eval fails structurally (a
        // loop) with an in-segment argument must NOT fall back to the
        // descriptor-pointer read — that byte is unrelated data, and
        // interpreting it would fabricate a variant. The fallback is gated
        // to the oversize-dispatcher condition only.
        let f15 = m.get_function(15).expect("func 15");
        assert_eq!(load_struct_const_key(&m, &reg, f15), None);
    }

    #[test]
    fn i128_delegation_wrapper_inherits_core_op() {
        let m = tranche3_module();
        // The core itself: div_u present → Div.
        assert_eq!(
            detect_i128_intrinsic(&m, 6).map(|i| i.op),
            Some(I128Op::Div)
        );
        // Verbatim-forwarding wrapper inherits Div (blend `232` shape).
        assert_eq!(
            detect_i128_intrinsic(&m, 7).map(|i| i.op),
            Some(I128Op::Div)
        );
        // A wrapper that TRANSFORMS a limb before delegating must NOT classify
        // — it computes something other than the core's operation.
        assert!(detect_i128_intrinsic(&m, 8).is_none());
        // greptile P1 shapes: the wrapper must provably RETURN the core's
        // result. Storing a param instead of the loaded core limb, or copying
        // the core's REMAINDER slots (a Rem, not the core's op), never
        // classifies.
        assert!(detect_i128_intrinsic(&m, 9).is_none());
        assert!(detect_i128_intrinsic(&m, 10).is_none());
    }

    #[test]
    fn detect_defaulting_u128_getter_classifies() {
        let m = tranche2_module();
        assert!(detect_defaulting_u128_getter(&m, 6), "the getter matches");
        assert!(
            !detect_defaulting_u128_getter(&m, 9),
            "a getter that also puts is excluded"
        );
        assert!(
            !detect_defaulting_u128_getter(&m, 7),
            "a pure decode (2 params, no storage) is not a getter"
        );
    }

    #[test]
    fn detect_tryfromval_decode_helper_classifies() {
        let m = tranche2_module();
        assert_eq!(
            detect_tryfromval_decode_helper(&m, 7),
            Some(DecodeHelperClass::U128)
        );
        assert_eq!(
            detect_tryfromval_decode_helper(&m, 8),
            Some(DecodeHelperClass::U64)
        );
        assert_eq!(
            detect_tryfromval_decode_helper(&m, 6),
            None,
            "storage access excludes the defaulting getter"
        );
        assert_eq!(
            detect_tryfromval_decode_helper(&m, 10),
            None,
            "mixed-width decode is ambiguous"
        );
        // greptile P1 shapes: the decode must consume the UNMODIFIED `val`
        // parameter, and the stores must be exactly the claimed layout.
        assert_eq!(
            detect_tryfromval_decode_helper(&m, 11),
            None,
            "a reassigned val param breaks the operand proof"
        );
        assert_eq!(
            detect_tryfromval_decode_helper(&m, 12),
            None,
            "an extra store is a layout this detector does not prove"
        );
        // Position-aware operand proof: reusing the val local for the RESULT
        // after the decode window (aqua's real u64/u128 decoders) is fine —
        // only a reassignment BEFORE the window breaks the proof.
        assert_eq!(
            detect_tryfromval_decode_helper(&m, 13),
            Some(DecodeHelperClass::U64)
        );
        // …and a LOOP with a reassignment voids the flat-position proof
        // entirely (iterations 2+ decode the replacement value).
        assert_eq!(detect_tryfromval_decode_helper(&m, 14), None);
    }

    #[test]
    fn getter_protocol_walk_accepts_husk_and_rejects_writes() {
        let key_vec =
            SorobanExpr::VecConstruct(vec![SorobanExpr::SymbolLiteral("TokenShare".to_string())]);
        let get = SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key: Box::new(SorobanExpr::Local(6)),
            unwrap: true,
            on_missing: None,
        };
        let husk = |tail: Vec<SorobanStmt>| {
            let mut v = vec![
                SorobanStmt::Expr(SorobanExpr::ExtendInstanceAndCodeTtl {
                    threshold: Box::new(SorobanExpr::U32Literal(1)),
                    extend_to: Box::new(SorobanExpr::U32Literal(2)),
                }),
                SorobanStmt::Let {
                    name: "var_6".to_string(),
                    mutable: true,
                    value: SorobanExpr::UnknownVal,
                },
                SorobanStmt::Let {
                    name: "var_6".to_string(),
                    mutable: false,
                    value: key_vec.clone(),
                },
                SorobanStmt::Expr(SorobanExpr::StorageHas {
                    storage_type: StorageType::Instance,
                    key: Box::new(SorobanExpr::Local(6)),
                }),
                SorobanStmt::If {
                    condition: SorobanExpr::Eq(
                        Box::new(SorobanExpr::StorageHas {
                            storage_type: StorageType::Instance,
                            key: Box::new(SorobanExpr::Local(6)),
                        }),
                        Box::new(SorobanExpr::I64Literal(1)),
                    ),
                    then_body: vec![
                        SorobanStmt::Expr(get.clone()),
                        SorobanStmt::If {
                            condition: SorobanExpr::Ne(
                                Box::new(SorobanExpr::UnknownVal),
                                Box::new(SorobanExpr::I32Literal(68)),
                            ),
                            then_body: vec![SorobanStmt::Expr(SorobanExpr::Panic)],
                            else_body: vec![],
                        },
                    ],
                    else_body: vec![],
                },
            ];
            v.extend(tail);
            v
        };

        let protocol = collect_getter_protocol(&husk(vec![])).expect("husk is the protocol");
        assert_eq!(protocol.get.0, StorageType::Instance);
        assert_eq!(
            unique_binding_value(&protocol.bindings, "var_6"),
            Some(key_vec.clone()),
            "the key binding resolves through the UnknownVal init"
        );

        // A write anywhere fails the whole dissection.
        let with_set = husk(vec![SorobanStmt::Expr(SorobanExpr::StorageSet {
            storage_type: StorageType::Instance,
            key: Box::new(key_vec.clone()),
            value: Box::new(SorobanExpr::U32Literal(1)),
        })]);
        assert!(collect_getter_protocol(&with_set).is_none());

        // A second get is ambiguous.
        let with_second_get = husk(vec![SorobanStmt::Expr(get.clone())]);
        assert!(collect_getter_protocol(&with_second_get).is_none());
    }

    #[test]
    fn seed_defaulting_getter_appends_binding_and_seeds_limbs() {
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);

        let key_vec =
            SorobanExpr::VecConstruct(vec![SorobanExpr::SymbolLiteral("TokenShare".to_string())]);
        let mut stmts = vec![
            SorobanStmt::Let {
                name: "var_6".to_string(),
                mutable: false,
                value: key_vec.clone(),
            },
            SorobanStmt::Expr(SorobanExpr::StorageGet {
                storage_type: StorageType::Instance,
                key: Box::new(SorobanExpr::Local(6)),
                unwrap: true,
                on_missing: None,
            }),
        ];
        let n_before = stmts.len();
        assert!(ctx.seed_defaulting_u128_getter(0, 16, &mut stmts));
        // The husk is untouched; the defaulting binding is APPENDED.
        assert_eq!(stmts.len(), n_before + 1);
        let SorobanStmt::Let { value, .. } = stmts.last().unwrap() else {
            panic!("appended stmt should be a Let, got {:?}", stmts.last());
        };
        let SorobanExpr::CastAs { value: get, .. } = value else {
            panic!("binding should be the u128-annotated get, got {value:?}");
        };
        let SorobanExpr::StorageGet {
            key, on_missing, ..
        } = get.as_ref()
        else {
            panic!("expected StorageGet, got {get:?}");
        };
        assert_eq!(**key, key_vec, "the Local(6) key resolved to its binding");
        assert_eq!(
            on_missing.as_deref(),
            Some(&SorobanExpr::U128Literal(0)),
            "the missing path defaults to 0"
        );
        // Both limb slots read the binding.
        let slots = ctx.frame_slots.borrow();
        assert!(matches!(
            slots.get(&(0, 16)),
            Some(StackVal::I128Limb { hi: false, .. })
        ));
        assert!(matches!(
            slots.get(&(0, 24)),
            Some(StackVal::I128Limb { hi: true, .. })
        ));
    }

    #[test]
    fn seed_decode_helper_respects_purity_and_layout() {
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;

        // Pure operand (a binding reference) → u128 limbs seeded at +16/+24.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        ctx.seed_decode_helper_result(0, 0, DecodeHelperClass::U128, &StackVal::LetBinding(3));
        {
            let slots = ctx.frame_slots.borrow();
            assert!(matches!(
                slots.get(&(0, 16)),
                Some(StackVal::I128Limb { hi: false, .. })
            ));
            assert!(matches!(
                slots.get(&(0, 24)),
                Some(StackVal::I128Limb { hi: true, .. })
            ));
            assert!(slots.get(&(0, 0)).is_none(), "the disc stays honest");
        }

        // U64 layout seeds only +8.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        ctx.seed_decode_helper_result(
            0,
            0,
            DecodeHelperClass::U64,
            &StackVal::Param("v".to_string()),
        );
        {
            let slots = ctx.frame_slots.borrow();
            assert!(matches!(
                slots.get(&(0, 8)),
                Some(StackVal::HostCallResult(_))
            ));
            assert!(slots.get(&(0, 16)).is_none());
        }

        // An impure operand (a raw storage-get result) seeds nothing —
        // re-reading it at a consumer would duplicate the host call.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        let impure = StackVal::HostCallResult(Box::new(SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key: Box::new(SorobanExpr::SymbolLiteral("K".to_string())),
            unwrap: true,
            on_missing: None,
        }));
        ctx.seed_decode_helper_result(0, 0, DecodeHelperClass::U128, &impure);
        assert!(ctx.frame_slots.borrow().is_empty());
    }

    #[test]
    fn purity_accepts_reference_wrapping_host_results() {
        // The value-link seeds wrap plain references (`var_N`); re-reading a
        // binding is free, so joins/seeds may use them.
        assert!(stack_val_is_pure(&StackVal::HostCallResult(Box::new(
            SorobanExpr::NamedLocal("var_3_2".to_string())
        ))));
        assert!(!stack_val_is_pure(&StackVal::HostCallResult(Box::new(
            SorobanExpr::LedgerTimestamp
        ))));
    }

    #[test]
    fn i64and_tag_extraction_constant_on_either_side() {
        use crate::wasm::ir::WasmInstr;
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        let expected = StackVal::BinOp(
            Box::new(StackVal::Param("v".to_string())),
            BinOper::And,
            Box::new(StackVal::I64(0xFF)),
        );

        // Value on the left, 0xFF mask on the right: `v & 0xFF`.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        ctx.stack.push(StackVal::Param("v".to_string()));
        ctx.stack.push(StackVal::I64(0xFF));
        ctx.lift_instruction(&WasmInstr::I64And);
        assert_eq!(ctx.stack.pop(), Some(expected.clone()));

        // 0xFF mask on the left, value on the right: `0xFF & v`.
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        ctx.stack.push(StackVal::I64(0xFF));
        ctx.stack.push(StackVal::Param("v".to_string()));
        ctx.lift_instruction(&WasmInstr::I64And);
        assert_eq!(ctx.stack.pop(), Some(expected));
    }

    #[test]
    fn i64and_tag_extraction_suppressed_inside_inlined_helper() {
        use crate::wasm::ir::WasmInstr;
        let wasm = empty_lift_module();
        let reg = empty_registry();
        let rt = None;
        // inline_depth > 0: the tag check must NOT be recovered (stays Unknown so
        // the inlined helper's success-status propagation is preserved).
        let mut ctx = LiftContext::new(&wasm, &reg, &[], &rt, vec![], 0);
        ctx.inline_depth = 1;
        ctx.stack.push(StackVal::Param("v".to_string()));
        ctx.stack.push(StackVal::I64(0xFF));
        ctx.lift_instruction(&WasmInstr::I64And);
        assert_eq!(ctx.stack.pop(), Some(StackVal::Unknown));
    }

    #[test]
    fn stack_val_to_expr_decodes_val_threshold_constants() {
        let reg = empty_registry();
        // (10 << 32) | 0xFFFFFFFF sits between U32(10) and U32(11) in unsigned
        // order, so `len > threshold` decodes to `len > 10`.
        let threshold = StackVal::I64(((10u64 << 32) | 0xFFFFFFFF) as i64);

        let right = StackVal::Compare(
            Box::new(StackVal::Param("len".to_string())),
            CmpOp::GtU,
            Box::new(threshold.clone()),
        );
        assert_eq!(
            stack_val_to_expr(&right, &[], &reg, None),
            SorobanExpr::Gt(
                Box::new(SorobanExpr::Param("len".to_string())),
                Box::new(SorobanExpr::I64Literal(10)),
            )
        );

        let left = StackVal::Compare(
            Box::new(threshold),
            CmpOp::LtU,
            Box::new(StackVal::Param("len".to_string())),
        );
        assert_eq!(
            stack_val_to_expr(&left, &[], &reg, None),
            SorobanExpr::Lt(
                Box::new(SorobanExpr::I64Literal(10)),
                Box::new(SorobanExpr::Param("len".to_string())),
            )
        );
    }

    // ---------------------------------------------------------------------
    // i128/u128 soft-arith: a lone 128-bit limb that reaches expr conversion
    // (not re-paired) lowers to its source value's expression.
    // ---------------------------------------------------------------------
    #[test]
    fn lone_i128_limb_lowers_to_source_value() {
        let reg = empty_registry();
        for hi in [false, true] {
            let limb = StackVal::I128Limb {
                value: Box::new(StackVal::Param("amount".to_string())),
                hi,
            };
            assert_eq!(
                stack_val_to_expr(&limb, &[], &reg, None),
                SorobanExpr::Param("amount".to_string()),
                "lone limb (hi={hi}) should lower to the source value"
            );
        }
    }

    // ---------------------------------------------------------------------
    // Phase 2 (Stage 2): i128/u128 soft-arith helper detection + operand
    // reconstruction. The lifter classifies the `(result_ptr, a_lo, a_hi,
    // b_lo, b_hi)` multiply/divide helpers and lowers them to clean
    // `Mul`/`Div`, rebuilding each operand from its limb pair.
    // ---------------------------------------------------------------------

    #[test]
    fn reconstruct_i128_operand_pairs_clean_limbs() {
        let src = StackVal::Param("amount".to_string());
        let lo = StackVal::I128Limb {
            value: Box::new(src.clone()),
            hi: false,
        };
        let hi = StackVal::I128Limb {
            value: Box::new(src.clone()),
            hi: true,
        };
        assert_eq!(
            reconstruct_i128_operand(&lo, &hi),
            Some((src, true)),
            "a matching (lo, hi) limb pair recovers the whole value (clean)"
        );
    }

    #[test]
    fn reconstruct_i128_operand_folds_constant_limbs() {
        // Fee factors like `(997, 0)` arrive as two i64 constant limbs — best-effort.
        assert_eq!(
            reconstruct_i128_operand(&StackVal::I64(997), &StackVal::I64(0)),
            Some((
                StackVal::HostCallResult(Box::new(SorobanExpr::I128Literal(997))),
                false
            ))
        );
    }

    #[test]
    fn reconstruct_i128_operand_rejects_mismatched_and_soup() {
        let lo = StackVal::I128Limb {
            value: Box::new(StackVal::Param("x".to_string())),
            hi: false,
        };
        let hi_other = StackVal::I128Limb {
            value: Box::new(StackVal::Param("y".to_string())),
            hi: true,
        };
        // Two clean limbs of DIFFERENT sources is a genuine mismatch — reject it
        // rather than fabricate, since neither lone limb is obviously the operand.
        assert_eq!(
            reconstruct_i128_operand(&lo, &hi_other),
            None,
            "clean limbs of different sources must not pair"
        );
        // A clean low limb with a DEGRADED high limb recovers its source (the lone
        // limb already lowers to that value), and counts as clean.
        let degraded_hi = StackVal::LetBinding(2);
        assert_eq!(
            reconstruct_i128_operand(&lo, &degraded_hi),
            Some((StackVal::Param("x".to_string()), true)),
            "a clean low limb recovers its source when the high limb degraded"
        );
        let soup = StackVal::BinOp(
            Box::new(StackVal::Unknown),
            BinOper::Mul,
            Box::new(StackVal::Unknown),
        );
        assert_eq!(
            reconstruct_i128_operand(&soup, &hi_other),
            None,
            "a degraded limb-soup operand is not reconstructable"
        );
    }

    /// Three functions with the soft-arith helper signature: a schoolbook
    /// multiply leaf (≥5 `i64.mul`, two stores, no calls), a divide core
    /// (`i64.div_u`), and a benign non-helper with the same signature.
    #[cfg(test)]
    fn i128_helper_module() -> crate::wasm::WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (func $mul (param i32 i64 i64 i64 i64)
                    local.get 0
                    local.get 1 local.get 3 i64.mul
                    local.get 1 local.get 4 i64.mul i64.add
                    local.get 2 local.get 3 i64.mul i64.add
                    local.get 2 local.get 4 i64.mul i64.add
                    local.get 1 local.get 3 i64.mul i64.add
                    i64.store
                    local.get 0
                    local.get 2 local.get 4 i64.mul
                    i64.store offset=8)
                (func $div (param i32 i64 i64 i64 i64)
                    local.get 0
                    local.get 1 local.get 3 i64.div_u
                    i64.store)
                (func $noop (param i32 i64 i64 i64 i64)
                    local.get 0 local.get 1 i64.store))
            "#,
        )
        .expect("wat parses");
        crate::wasm::WasmModule::parse(&wasm).expect("module parses")
    }

    #[test]
    fn detect_i128_intrinsic_classifies_helpers() {
        let m = i128_helper_module();
        assert_eq!(
            detect_i128_intrinsic(&m, 0).map(|i| i.op),
            Some(I128Op::Mul),
            "schoolbook multiply leaf"
        );
        assert_eq!(
            detect_i128_intrinsic(&m, 1).map(|i| i.op),
            Some(I128Op::Div),
            "div_u core"
        );
        assert!(
            detect_i128_intrinsic(&m, 2).is_none(),
            "a same-signature non-arithmetic function is not a helper"
        );
    }

    #[test]
    fn div_core_with_many_muls_still_classifies() {
        // The real mainnet 128-bit division core uses several `i64.mul` for quotient
        // estimation (Knuth long division). The old `mul <= 6` cap rejected it; an
        // inline division op alone must mark a divide.
        let wasm = wat::parse_str(
            r#"(module
                (func $div_heavy (param i32 i64 i64 i64 i64)
                    local.get 0
                    local.get 1 local.get 3 i64.mul
                    local.get 1 local.get 4 i64.mul i64.add
                    local.get 2 local.get 3 i64.mul i64.add
                    local.get 2 local.get 4 i64.mul i64.add
                    local.get 1 local.get 3 i64.mul i64.add
                    local.get 2 local.get 4 i64.mul i64.add
                    local.get 1 local.get 4 i64.mul i64.add
                    local.get 3 i64.div_u
                    i64.store))
            "#,
        )
        .expect("wat parses");
        let m = crate::wasm::WasmModule::parse(&wasm).expect("module parses");
        assert_eq!(
            detect_i128_intrinsic(&m, 0).map(|i| i.op),
            Some(I128Op::Div),
            "div core with 7 muls classifies as divide"
        );
    }

    #[test]
    fn i128_result_offsets_detects_checked_layout() {
        // Unchecked helpers write the value as `{lo@0, hi@8}`; checked
        // `Result<i128,E>` helpers reserve `+0` for the discriminant and address
        // `param0 + 16` for the hi limb.
        let wasm = wat::parse_str(
            r#"(module
                (func $unchecked (param i32 i64 i64)
                    local.get 0 local.get 1 i64.store
                    local.get 0 local.get 2 i64.store offset=8)
                (func $checked (param i32 i64 i64)
                    local.get 0 i64.const 0 i64.store
                    local.get 0 local.get 1 i64.store offset=8
                    local.get 0 i32.const 16 i32.add local.get 2 i64.store))
            "#,
        )
        .expect("wat parses");
        let m = crate::wasm::WasmModule::parse(&wasm).expect("module parses");
        assert_eq!(
            i128_result_offsets(m.get_function(0).unwrap()),
            (0, 8),
            "unchecked layout"
        );
        assert_eq!(
            i128_result_offsets(m.get_function(1).unwrap()),
            (8, 16),
            "checked Result layout"
        );
    }

    /// A module exercising the fallible-storage-get recognizer: imports
    /// `get_contract_data` (l.1) + `put_contract_data` (l._), then helpers at
    /// global indices 2..=8 (imports occupy 0,1).
    fn fallible_get_module() -> crate::wasm::WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (import "l" "1" (func (param i64 i64) (result i64)))
                (import "l" "_" (func (param i64 i64 i64)))
                (func (param i32 i32)                                  ;; 2: keyed get, Temporary, 400
                    local.get 1 i64.extend_i32_u i64.const 0 call 0 drop
                    local.get 0 i32.const 0 i32.store
                    local.get 0 i32.const 400 i32.store offset=4
                    local.get 0 i32.const 1 i32.store)
                (func (param i32 i32)                                  ;; 3: get + put (setter) → excluded
                    local.get 1 i64.extend_i32_u i64.const 0 call 0 drop
                    local.get 1 i64.extend_i32_u i64.const 0 local.get 1 i64.extend_i32_u call 1
                    local.get 0 i32.const 400 i32.store offset=4
                    local.get 0 i32.const 1 i32.store)
                (func (param i32 i32)                                  ;; 4: no get_contract_data
                    local.get 0 i32.const 400 i32.store offset=4
                    local.get 0 i32.const 1 i32.store)
                (func (param i32 i32)                                  ;; 5: two distinct codes → ambiguous
                    local.get 1 i64.extend_i32_u i64.const 0 call 0 drop
                    local.get 0 i32.const 400 i32.store offset=4
                    local.get 0 i32.const 401 i32.store offset=4
                    local.get 0 i32.const 1 i32.store)
                (func (param i32)                                      ;; 6: 1-param const "Admin" key, Instance, 2
                    i64.const 54344266510 i64.const 2 call 0 drop
                    local.get 0 i32.const 0 i32.store
                    local.get 0 i32.const 2 i32.store offset=4
                    local.get 0 i32.const 1 i32.store)
                (func (param i64 i64) (result i64)                     ;; 7: math helper (mul + div)
                    local.get 0 local.get 1 i64.mul
                    local.get 0 local.get 1 i64.div_u i64.add)
                (func (param i32 i32)                                  ;; 8: direct getter — calls helper 2
                    local.get 0 local.get 1 call 2))
            "#,
        )
        .expect("wat parses");
        crate::wasm::WasmModule::parse(&wasm).expect("module parses")
    }

    #[test]
    fn detect_fallible_storage_get_helper_classifies() {
        let m = fallible_get_module();
        let reg = empty_registry();
        // 2: keyed get → Temporary, code 400, no const key (key is the caller arg).
        let got = detect_fallible_storage_get_helper(&m, &reg, 2).expect("helper 2 matches");
        assert_eq!(got.storage_type, StorageType::Temporary);
        assert_eq!(got.error_code, 400);
        assert!(got.const_key.is_none());
        // 6: 1-param const-key get → Instance, code 2, key = symbol "Admin".
        let got6 = detect_fallible_storage_get_helper(&m, &reg, 6).expect("helper 6 matches");
        assert_eq!(got6.storage_type, StorageType::Instance);
        assert_eq!(got6.error_code, 2);
        assert!(
            matches!(got6.const_key, Some(SorobanExpr::SymbolLiteral(ref s)) if s == "Admin"),
            "const key should decode to the Admin symbol, got {:?}",
            got6.const_key
        );
        // Negatives → None (today's husk is emitted unchanged).
        assert!(
            detect_fallible_storage_get_helper(&m, &reg, 3).is_none(),
            "a setter (calls put_contract_data) is excluded"
        );
        assert!(
            detect_fallible_storage_get_helper(&m, &reg, 4).is_none(),
            "no get_contract_data"
        );
        assert!(
            detect_fallible_storage_get_helper(&m, &reg, 5).is_none(),
            "two distinct error codes is ambiguous"
        );
        assert!(
            detect_fallible_storage_get_helper(&m, &reg, 7).is_none(),
            "a value-returning math helper is not a fallible get"
        );
    }

    #[test]
    fn function_calls_math_helper_separates_computed_from_direct() {
        let m = fallible_get_module();
        assert!(function_calls_math_helper(&m, 7, 3), "7 is the math helper");
        assert!(
            !function_calls_math_helper(&m, 8, 3),
            "8 calls only the fallible get → direct getter"
        );
        assert!(
            !function_calls_math_helper(&m, 2, 3),
            "the get helper itself has no arithmetic"
        );
    }

    #[test]
    fn note_fallible_get_counts_all_but_records_first() {
        // A getter that reads more than one key must NOT be rebuilt as a single
        // value-returning `get(..).ok_or(..)` tail — that would return the FIRST
        // key's value/error and silently drop the rest. The observer therefore
        // counts EVERY fallible-get (so `lift_function_body` can force the faithful
        // early-return guard when count > 1) while keeping only the FIRST record.
        // Guards greptile P1 "First Helper Replaces Body".
        let m = fallible_get_module();
        let reg = empty_registry();
        let params: Vec<FnParam> = Vec::new();
        let ret = result_u64_error();
        let mut ctx = LiftContext::new(&m, &reg, &params, &ret, Vec::new(), 0);

        // First read: helper 2, keyed by the caller's 2nd arg (Temporary, code 400).
        ctx.note_fallible_storage_get(
            2,
            &[StackVal::Unknown, StackVal::Param("chain_id".to_string())],
        );
        assert_eq!(*ctx.fallible_get_count.borrow(), 1, "first get counted");
        // Second read: helper 6, const "Admin" key — counted but NOT recorded.
        ctx.note_fallible_storage_get(6, &[]);
        assert_eq!(
            *ctx.fallible_get_count.borrow(),
            2,
            "second get also counted"
        );

        let rec = ctx.fallible_get_recovery.borrow();
        let rec = rec.as_ref().expect("first get recorded");
        assert_eq!(
            rec.key,
            SorobanExpr::Param("chain_id".to_string()),
            "the FIRST read's key is kept, not overwritten by the later const-key read"
        );
        assert_eq!(rec.error_code, 400, "first read's error code is kept");
        assert_eq!(rec.storage_type, StorageType::Temporary);
    }

    #[test]
    fn panic_guard_shell_and_unknown_detection() {
        use crate::ir::{SorobanExpr, SorobanStmt};
        let guard = SorobanStmt::If {
            condition: SorobanExpr::Ne(
                Box::new(SorobanExpr::Param("amount_in".into())),
                Box::new(SorobanExpr::I128Literal(0)),
            ),
            then_body: vec![SorobanStmt::Expr(SorobanExpr::Panic)],
            else_body: vec![],
        };
        // `if cond { panic!() }` with no value path is the misleading shell.
        assert!(is_panic_guard_shell(std::slice::from_ref(&guard)));
        // A bare `panic!()` (no `if`) is NOT a shell — it compiles as a diverging
        // getter and must be preserved.
        assert!(!is_panic_guard_shell(&[SorobanStmt::Expr(
            SorobanExpr::Panic
        )]));
        // A value-producing tail is not a shell.
        assert!(!is_panic_guard_shell(&[SorobanStmt::Return(Some(
            SorobanExpr::Param("x".into())
        ))]));
        // The clean guard carries no `todo!`; an `UnknownVal` condition is an honest
        // partial that must not be stubbed.
        assert!(!stmts_contain_unknown(std::slice::from_ref(&guard)));
        let dirty = SorobanStmt::If {
            condition: SorobanExpr::UnknownVal,
            then_body: vec![SorobanStmt::Expr(SorobanExpr::Panic)],
            else_body: vec![],
        };
        assert!(stmts_contain_unknown(std::slice::from_ref(&dirty)));
    }

    #[test]
    fn divceil_classifies_round_up_wrapper() {
        // $core has an inline divide → classifies as Div. $ceil delegates to $core
        // and carries the inexact-increment idiom (`i64.or; i64.eqz` remainder test
        // + `i64.const 1; i64.add` quotient bump) → DivCeil. $plain forwards to the
        // div core but has no increment → not classified (the increment is required).
        let wasm = wat::parse_str(
            r#"(module
                (func $core (param i32 i64 i64 i64 i64)
                    local.get 0 local.get 1 local.get 3 i64.div_u i64.store)
                (func $ceil (param i32 i64 i64 i64 i64)
                    local.get 0 local.get 1 local.get 2 local.get 3 local.get 4 call $core
                    local.get 1 local.get 2 i64.or i64.eqz drop
                    local.get 1 i64.const 1 i64.add drop)
                (func $plain (param i32 i64 i64 i64 i64)
                    local.get 0 local.get 1 local.get 2 local.get 3 local.get 4 call $core))
            "#,
        )
        .expect("wat parses");
        let m = crate::wasm::WasmModule::parse(&wasm).expect("module parses");
        assert_eq!(
            detect_i128_intrinsic(&m, 0).map(|i| i.op),
            Some(I128Op::Div)
        );
        assert_eq!(
            detect_i128_intrinsic(&m, 1).map(|i| i.op),
            Some(I128Op::DivCeil),
            "div core + inexact increment classifies as DivCeil"
        );
        assert_eq!(
            detect_i128_intrinsic(&m, 2).map(|i| i.op),
            Some(I128Op::Div),
            "a verbatim forwarder without the increment inherits the core's \
             op (issue #34 t3 delegation rule, execution-verified against the \
             blend divmod core) — crucially NOT DivCeil"
        );
    }

    #[test]
    fn reconstruct_i128_inline_borrow_sub_and_carry_add() {
        // Clean limb pairs for two whole 128-bit operands x and y.
        let lo = |n: &str| StackVal::I128Limb {
            value: Box::new(StackVal::Param(n.into())),
            hi: false,
        };
        let hi = |n: &str| StackVal::I128Limb {
            value: Box::new(StackVal::Param(n.into())),
            hi: true,
        };
        let cmp =
            |a: StackVal, op: CmpOp, b: StackVal| StackVal::Compare(Box::new(a), op, Box::new(b));
        let bin =
            |a: StackVal, op: BinOper, b: StackVal| StackVal::BinOp(Box::new(a), op, Box::new(b));

        // x - y:  lo = x.lo - y.lo ; hi = (x.hi - y.hi) - (x.lo <u y.lo)
        let sub_lo = bin(lo("x"), BinOper::Sub, lo("y"));
        let sub_hi = bin(
            bin(hi("x"), BinOper::Sub, hi("y")),
            BinOper::Sub,
            cmp(lo("x"), CmpOp::LtU, lo("y")),
        );
        assert_eq!(
            reconstruct_i128_operand(&sub_lo, &sub_hi),
            Some((
                bin(
                    StackVal::Param("x".into()),
                    BinOper::Sub,
                    StackVal::Param("y".into())
                ),
                true
            )),
            "borrow-subtract limb pair rebuilds as x - y"
        );

        // x + y:  lo = x.lo + y.lo ; hi = (lo <u y.lo) + (y.hi + x.hi)
        let add_lo = bin(lo("x"), BinOper::Add, lo("y"));
        let add_hi = bin(
            cmp(add_lo.clone(), CmpOp::LtU, lo("y")),
            BinOper::Add,
            bin(hi("y"), BinOper::Add, hi("x")),
        );
        assert_eq!(
            reconstruct_i128_operand(&add_lo, &add_hi),
            Some((
                bin(
                    StackVal::Param("x".into()),
                    BinOper::Add,
                    StackVal::Param("y".into())
                ),
                true
            )),
            "carry-add limb pair rebuilds as x + y"
        );

        // A two's-complement negation `0 - y` (the signed-wrapper abs idiom) must NOT
        // be mistaken for a 128-bit subtract: its hi limb is `0 - (y.hi + (y.lo != 0))`,
        // whose left operand is `0`, not a `Sub`.
        let neg_lo = bin(StackVal::I64(0), BinOper::Sub, lo("y"));
        let neg_hi = bin(
            StackVal::I64(0),
            BinOper::Sub,
            bin(
                hi("y"),
                BinOper::Add,
                cmp(lo("y"), CmpOp::Ne, StackVal::I64(0)),
            ),
        );
        assert_eq!(
            reconstruct_i128_operand(&neg_lo, &neg_hi),
            None,
            "a 0 - y negation is not a 128-bit subtract"
        );
    }

    #[test]
    fn reconstruct_i128_gtu_borrow_and_const_increment() {
        use crate::ir::SorobanExpr;
        let lo = |n: &str| StackVal::I128Limb {
            value: Box::new(StackVal::Param(n.into())),
            hi: false,
        };
        let hi = |n: &str| StackVal::I128Limb {
            value: Box::new(StackVal::Param(n.into())),
            hi: true,
        };
        let cmp =
            |a: StackVal, op: CmpOp, b: StackVal| StackVal::Compare(Box::new(a), op, Box::new(b));
        let bin =
            |a: StackVal, op: BinOper, b: StackVal| StackVal::BinOp(Box::new(a), op, Box::new(b));

        // x - y with the borrow written as the mirror `y.lo >u x.lo` (GtU form) —
        // equivalent to `x.lo <u y.lo`. Soroswap's get_amount_in emits this spelling.
        let sub_lo = bin(lo("x"), BinOper::Sub, lo("y"));
        let sub_hi = bin(
            bin(hi("x"), BinOper::Sub, hi("y")),
            BinOper::Sub,
            cmp(lo("y"), CmpOp::GtU, lo("x")),
        );
        assert_eq!(
            reconstruct_i128_operand(&sub_lo, &sub_hi),
            Some((
                bin(
                    StackVal::Param("x".into()),
                    BinOper::Sub,
                    StackVal::Param("y".into())
                ),
                true
            )),
            "GtU-form borrow still rebuilds x - y"
        );

        // q + 1: lo = q.lo + 1 ; hi = q.hi + (q.lo + 1 == 0)  [Eqz carry for +1].
        let inc_lo = bin(lo("q"), BinOper::Add, StackVal::I64(1));
        let inc_hi = bin(
            hi("q"),
            BinOper::Add,
            StackVal::Eqz(Box::new(inc_lo.clone())),
        );
        assert_eq!(
            reconstruct_i128_operand(&inc_lo, &inc_hi),
            Some((
                bin(
                    StackVal::Param("q".into()),
                    BinOper::Add,
                    StackVal::HostCallResult(Box::new(SorobanExpr::I128Literal(1)))
                ),
                true
            )),
            "constant +1 with Eqz carry rebuilds q + 1"
        );
    }

    #[test]
    fn is_symbol_from_lm_builder_classifies_wrappers() {
        // $enc = the small-symbol encoder (carries the _/0/A/a byte boundaries).
        // $wrap = the (result_ptr, str_ptr, str_len) builder that calls it.
        // $other = a same-shape function that does NOT reach an encoder.
        let wasm = wat::parse_str(
            r#"(module
                (func $enc (param i32 i32 i32)
                    i32.const 95 drop
                    i32.const 48 drop
                    i32.const 65 drop
                    i32.const 97 drop)
                (func $wrap (param i32 i32 i32)
                    local.get 0 local.get 1 local.get 2 call $enc)
                (func $other (param i32 i32 i32)
                    local.get 0 i32.const 1 i32.store)
                (func $wrong_sig (param i32 i64)
                    local.get 0 call $enc))
            "#,
        )
        .expect("wat parses");
        let m = crate::wasm::WasmModule::parse(&wasm).expect("module parses");
        // $enc itself is the encoder, but its signature gates it out as a *builder*.
        assert!(is_small_symbol_encoder(m.get_function(0).unwrap()));
        assert!(
            is_symbol_from_lm_builder(&m, 1),
            "the 3-i32 wrapper that reaches the encoder is a builder"
        );
        assert!(
            !is_symbol_from_lm_builder(&m, 2),
            "a 3-i32 function that never reaches an encoder is not a builder"
        );
        assert!(
            !is_symbol_from_lm_builder(&m, 3),
            "wrong signature is not a builder even if it reaches the encoder"
        );
    }

    #[test]
    fn detect_option_decode_helper_classifies_decoder() {
        // $decode mirrors the SDK `Option<u32>` decoder: Void(2) -> tag 0; else
        // value = opt>>32, tag = select(1, 2, (opt&0xff)==4); stores value@+4, tag@+0.
        // $wrong_sig has the right body shape but the wrong signature; $no_select
        // has the right signature but no tag `select`.
        let wasm = wat::parse_str(
            r#"(module
                (func $decode (param i32 i64) (local i32 i32)
                    local.get 1 i64.const 2 i64.eq
                    if (result i32)
                        i32.const 0
                    else
                        local.get 1 i64.const 32 i64.shr_u i32.wrap_i64 local.set 2
                        i32.const 1 i32.const 2
                        local.get 1 i64.const 255 i64.and i64.const 4 i64.eq
                        select
                    end
                    local.set 3
                    local.get 0 local.get 2 i32.store offset=4
                    local.get 0 local.get 3 i32.store)
                (func $wrong_sig (param i32 i32) (local i32 i32)
                    local.get 1 i32.const 2 i32.eq drop
                    i32.const 0 local.set 2)
                (func $no_select (param i32 i64) (local i32)
                    local.get 1 i64.const 32 i64.shr_u i32.wrap_i64 local.set 2
                    local.get 0 local.get 2 i32.store offset=4))
            "#,
        )
        .expect("wat parses");
        let m = crate::wasm::WasmModule::parse(&wasm).expect("module parses");
        let layout = detect_option_decode_helper(&m, 0).expect("$decode is recognized");
        assert_eq!(layout.tag_off, 0, "tag is stored at +0");
        assert_eq!(layout.val_off, 4, "value is stored at +4");
        assert!(
            detect_option_decode_helper(&m, 1).is_none(),
            "wrong signature is not an option decoder"
        );
        assert!(
            detect_option_decode_helper(&m, 2).is_none(),
            "a decoder without the tag select is not recognized"
        );
    }

    #[test]
    fn encode_symbol_small_round_trips() {
        // The forward codec must be the exact inverse of decode_symbol_val.
        for name in ["Admin", "TTLConfig", "Relayer", "RefData", "_x0Zz9", "a"] {
            let v = encode_symbol_small(name).unwrap_or_else(|| panic!("{name} encodes"));
            assert_eq!(
                crate::wasm::data::DataSection::decode_symbol_val(v as u64).as_deref(),
                Some(name),
                "decode(encode({name})) round-trips"
            );
        }
        assert_eq!(encode_symbol_small(""), None, "empty never encodes");
        assert_eq!(
            encode_symbol_small("TenCharsXX"),
            None,
            ">9 chars is not a small symbol"
        );
        assert_eq!(encode_symbol_small("a-b"), None, "invalid char rejected");
    }

    /// A module mirroring Band's `DataKey::into_val` dispatcher (func 27),
    /// including everything that defeats structural per-arm string pairing:
    /// the `br_table` permutes selectors to arms, the "Relayer" pointer is
    /// preloaded BEFORE the `br_table`, "RefData" overrides it inside an arm,
    /// and the two data variants share one vec-packing tail.
    /// Layout (same as Band): Admin@+0(5) TTLConfig@+5(9) Relayer@+14(7) RefData@+21(7).
    fn datakey_dispatcher_module() -> crate::wasm::WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (import "v" "g" (func $hostvec (param i64 i64) (result i64)))
                (memory 1)
                (global $sp (mut i32) (i32.const 1048576))
                (data (i32.const 1048768) "AdminTTLConfigRelayerRefData")
                ;; small-symbol encoder stub: carries the 95/48/65/97 fingerprint.
                ;; Classified by the string args, never interpreted.
                (func $enc (param i32 i32) (result i64)
                    i32.const 95 drop i32.const 48 drop
                    i32.const 65 drop i32.const 97 drop
                    i64.const 0)
                ;; vec_new_from_linear_memory wrapper (classified, not interpreted)
                (func $vecbuild (param i32 i32) (result i64)
                    i64.const 0 i64.const 0 call $hostvec)
                ;; validator: outptr[0] = 0, outptr[8] = Vec[val]  (Band func 31)
                (func $validate (param i32 i64)
                    (local i32)
                    global.get $sp i32.const 16 i32.sub local.tee 2 global.set $sp
                    local.get 2 local.get 1 i64.store offset=8
                    local.get 0
                    local.get 2 i32.const 8 i32.add i32.const 1 call $vecbuild
                    i64.store offset=8
                    local.get 0 i64.const 0 i64.store
                    local.get 2 i32.const 16 i32.add global.set $sp)
                ;; the dispatcher (Band func 27)
                (func $disp (param i64 i64) (result i64)
                    (local i32 i32 i32)
                    global.get $sp i32.const 48 i32.sub local.tee 2 global.set $sp
                    i32.const 1048782 local.set 3      ;; preload "Relayer"
                    block (result i64)
                      block
                        block
                          block
                            block
                              block
                                local.get 0
                                i32.wrap_i64
                                i32.const 1
                                i32.sub
                                br_table 0 4 3 1
                              end
                              ;; sel==1 -> unit "TTLConfig"
                              local.get 2 i32.const 16 i32.add
                              i32.const 1048773 i32.const 9 call $enc
                              call $validate
                              local.get 2 i64.load offset=16 i32.wrap_i64 br_if 1
                              local.get 2 i64.load offset=24
                              br 4
                            end
                            ;; default (sel==0 or >=4) -> unit "Admin"
                            local.get 2
                            i32.const 1048768 i32.const 5 call $enc
                            call $validate
                            local.get 2 i64.load i32.wrap_i64 br_if 0
                            local.get 2 i64.load offset=8
                            br 3
                          end
                          unreachable
                        end
                        ;; sel==3 -> override pointer to "RefData"
                        i32.const 1048789 local.set 3
                      end
                      ;; shared data-variant tail: Vec[Symbol(ptr,7), payload]
                      local.get 3 i32.const 7 call $enc
                      local.set 0
                      global.get $sp i32.const 16 i32.sub local.tee 3 global.set $sp
                      local.get 3 local.get 1 i64.store offset=8
                      local.get 3 local.get 0 i64.store
                      local.get 2 i32.const 32 i32.add local.tee 4
                      local.get 3 i32.const 2 call $vecbuild
                      i64.store offset=8
                      local.get 4 i64.const 0 i64.store
                      local.get 3 i32.const 16 i32.add global.set $sp
                      local.get 2 i64.load offset=40
                    end
                    local.get 2 i32.const 48 i32.add global.set $sp)
                ;; same-signature decoy with a br_table but no symbol encoder
                (func $decoy (param i64 i64) (result i64)
                    block
                      block
                        local.get 0 i32.wrap_i64 br_table 0 1
                      end
                    end
                    i64.const 14)
                ;; loop-carrying variant: out of model even though it reaches $enc
                (func $loopy (param i64 i64) (result i64)
                    loop
                      nop
                    end
                    block
                      block
                        local.get 0 i32.wrap_i64 br_table 0 1
                      end
                    end
                    i32.const 1048768 i32.const 5 call $enc))
            "#,
        )
        .expect("wat parses");
        crate::wasm::WasmModule::parse(&wasm).expect("module parses")
    }

    #[test]
    fn datakey_dispatcher_folds_by_execution() {
        let m = datakey_dispatcher_module();
        let (disp, decoy, loopy) = (4u32, 5u32, 6u32);

        assert!(
            is_datakey_dispatcher(&m, disp),
            "the Band-shaped dispatcher classifies"
        );
        assert!(
            !is_datakey_dispatcher(&m, decoy),
            "a br_table func that never builds symbols is not a dispatcher"
        );
        assert!(
            !is_datakey_dispatcher(&m, loopy),
            "a loop-carrying body is out of model"
        );

        let eval = |sel: DkVal, payload: DkVal| {
            let mut ev = DkEval {
                module: &m,
                mem: HashMap::new(),
                sp: DkVal::StackPtr(0),
                steps: 0,
                gap_zero: None,
            };
            ev.eval_call(disp, vec![sel, payload], 0)
        };
        let sym = |v: &DkVal| match v {
            DkVal::I64(raw) => crate::wasm::data::DataSection::decode_symbol_val(*raw as u64),
            _ => None,
        };

        // The EXECUTED selector→variant mapping. Body order is
        // TTLConfig→Admin→RefData→Relayer-tail; naive body-order pairing
        // would mis-assign every one of these.
        let unit = |sel: i64, want: &str| {
            let r = eval(DkVal::I64(sel), DkVal::I64(0));
            let Some(Some(DkVal::VecVal(elems))) = r else {
                panic!("selector {sel} should evaluate to a vec key; got {r:?}");
            };
            assert_eq!(elems.len(), 1, "unit variant is a 1-element vec");
            assert_eq!(sym(&elems[0]).as_deref(), Some(want), "selector {sel}");
        };
        unit(0, "Admin");
        unit(1, "TTLConfig");
        // Out-of-range selectors take the br_table default — the bytecode's
        // own semantics.
        unit(9, "Admin");

        let data = |sel: i64, want: &str| {
            let r = eval(DkVal::I64(sel), DkVal::Arg(1));
            let Some(Some(DkVal::VecVal(elems))) = r else {
                panic!("selector {sel} should evaluate to a vec key; got {r:?}");
            };
            assert_eq!(elems.len(), 2, "data variant is [Symbol, payload]");
            assert_eq!(sym(&elems[0]).as_deref(), Some(want), "selector {sel}");
            assert_eq!(
                elems[1],
                DkVal::Arg(1),
                "the abstract payload passes through untouched"
            );
        };
        data(2, "Relayer");
        data(3, "RefData");

        // A non-constant selector cannot pick a br_table arm — bail, never guess.
        assert_eq!(
            eval(DkVal::Arg(0), DkVal::Arg(1)),
            None,
            "runtime selector is honestly unrecoverable"
        );
    }

    // ---------------------------------------------------------------------
    // Layer B (issue #12): multi-level `br_if` to a `fail_with_error` tail
    // recovers as a nested `if cond { panic_with_error!(…) }`.
    // ---------------------------------------------------------------------

    /// Build a module with a `fail_with_error` import (`x.5`), a thin wrapper
    /// that calls it (mirroring aquarius `call 80`), and a validation function
    /// whose inner block reaches the wrapper tail via a `br_if 0`, while a
    /// sibling `br_if 1` exits to a non-error (empty) tail.
    #[cfg(test)]
    fn fail_with_error_validate_module() -> crate::wasm::WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (import "x" "5" (func $fail (param i64) (result i64)))
                (func $wrap (param i64)
                    local.get 0
                    call $fail
                    drop)
                (func $validate (param i64)
                    block            ;; @1
                        block        ;; @2
                            local.get 0
                            i64.const 100
                            i64.gt_s
                            br_if 1   ;; depth 1 -> exits @1 -> empty tail (plain)
                            local.get 0
                            i64.eqz
                            br_if 0   ;; depth 0 -> exits @2 -> wrapper tail (fail_with_error)
                        end
                        i64.const 999
                        call $wrap
                        unreachable  ;; @2 exit tail: contract-error panic
                    end))
            "#,
        )
        .expect("wat parses");
        crate::wasm::WasmModule::parse(&wasm).expect("module parses")
    }

    #[test]
    fn layer_b_rewrites_brif_to_fail_with_error_tail() {
        use super::super::structurize::StructuredBlock;
        use crate::wasm::ir::WasmInstr;

        let module = fail_with_error_validate_module();
        // $validate is the second defined function (index 2: import 0, wrap 1).
        let validate = module.get_function(2).expect("validate present");
        let mut tree = super::super::structurize::structurize(&validate.body);

        // Sanity: before the pass, the depth-1 branch is a raw `BrIf(1)`.
        fn count_brif(blocks: &[StructuredBlock], depth: u32) -> usize {
            blocks
                .iter()
                .map(|b| match b {
                    StructuredBlock::Instruction(WasmInstr::BrIf(k)) if *k == depth => 1,
                    StructuredBlock::Block { body, .. } | StructuredBlock::Loop { body, .. } => {
                        count_brif(body, depth)
                    }
                    StructuredBlock::IfElse {
                        then_body,
                        else_body,
                        ..
                    } => count_brif(then_body, depth) + count_brif(else_body, depth),
                    _ => 0,
                })
                .sum()
        }
        // Count IfElse nodes whose then-body is a fail_with_error tail.
        fn count_recovered(blocks: &[StructuredBlock]) -> usize {
            blocks
                .iter()
                .map(|b| match b {
                    StructuredBlock::IfElse {
                        then_body,
                        else_body,
                        ..
                    } => {
                        let here = matches!(
                            then_body.last(),
                            Some(StructuredBlock::Instruction(WasmInstr::Unreachable))
                        ) && then_body
                            .iter()
                            .any(|n| matches!(n, StructuredBlock::Instruction(WasmInstr::Call(_))));
                        here as usize + count_recovered(then_body) + count_recovered(else_body)
                    }
                    StructuredBlock::Block { body, .. } | StructuredBlock::Loop { body, .. } => {
                        count_recovered(body)
                    }
                    _ => 0,
                })
                .sum()
        }

        assert_eq!(
            count_brif(&tree, 0),
            1,
            "expected one depth-0 br_if pre-pass"
        );
        recover_fail_with_error_branches(&mut tree, &module);
        assert_eq!(
            count_brif(&tree, 0),
            0,
            "the depth-0 br_if to the fail_with_error tail should be rewritten away"
        );
        assert_eq!(
            count_recovered(&tree),
            1,
            "exactly one IfElse wrapping the fail_with_error tail should be synthesized"
        );
        // The depth-1 br_if to the plain (empty) `@1` exit must be left untouched.
        assert_eq!(
            count_brif(&tree, 1),
            1,
            "the depth-1 br_if to a non-error exit must be preserved as-is"
        );
    }

    #[test]
    fn layer_b_ignores_non_fail_with_error_tails() {
        use super::super::structurize::StructuredBlock;
        use crate::wasm::ir::WasmInstr;

        // A function whose only block exit is a bare `unreachable` (no
        // fail_with_error): the pass must NOT rewrite the br_if (we deliberately
        // scope out bare traps to avoid panic-ifying compiler safety nets).
        let wasm = wat::parse_str(
            r#"(module
                (func $f (param i64)
                    block
                        local.get 0
                        i64.const 1
                        i64.eq
                        br_if 0
                        local.get 0
                        drop
                    end
                    unreachable))
            "#,
        )
        .expect("wat parses");
        let module = crate::wasm::WasmModule::parse(&wasm).expect("module parses");
        let validate = module.get_function(0).expect("present");
        let mut tree = super::super::structurize::structurize(&validate.body);
        let before = format!("{tree:?}");
        recover_fail_with_error_branches(&mut tree, &module);
        assert_eq!(
            before,
            format!("{tree:?}"),
            "bare-trap exits must be left byte-identical"
        );
        assert!(
            tree.iter().any(|b| matches!(
                b,
                StructuredBlock::Block { body, .. } if body.iter().any(|n| matches!(
                    n,
                    StructuredBlock::Instruction(WasmInstr::BrIf(0))
                ))
            )),
            "the br_if should still be present and unrewritten"
        );
    }

    /// Fixture for the IfElse sound-join read poison (issue #34 phase 2).
    /// Every function allocates a shadow-stack frame (`global.get 0` −16 →
    /// `local.tee 1`), conditionally writes slot +8 inside an `if`, then
    /// loads the slot after the join and returns it. No host calls, so
    /// `lift_inline_call` surfaces the raw post-join `StackVal` as
    /// `stack_result`. Functions: 0 = conditional then-write (if without
    /// else); 1 = dead-then (the then arm stores and RETURNS); 2 = both arms
    /// write (else overwrite — last-write-wins is today's semantics, sound
    /// on the fall-through the abstract state tracks); 3 = net no-op (the
    /// then arm re-stores the pre-if value); 4 = else arm traps (fall-through
    /// implies the then path ran).
    fn join_poison_module() -> WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (global (mut i32) (i32.const 1048576))
                (memory 1)
                (func (;0;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 0 i32.wrap_i64
                    if
                        local.get 1 i64.const 42 i64.store offset=8
                    end
                    local.get 1 i64.load offset=8)
                (func (;1;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 0 i32.wrap_i64
                    if
                        local.get 1 i64.const 42 i64.store offset=8
                        i64.const 7
                        return
                    end
                    local.get 1 i64.load offset=8)
                (func (;2;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 0 i32.wrap_i64
                    if
                        local.get 1 i64.const 42 i64.store offset=8
                    else
                        local.get 1 i64.const 99 i64.store offset=8
                    end
                    local.get 1 i64.load offset=8)
                (func (;3;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 1 i64.const 7 i64.store offset=8
                    local.get 0 i32.wrap_i64
                    if
                        local.get 1 i64.const 7 i64.store offset=8
                    end
                    local.get 1 i64.load offset=8)
                (func (;4;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 0 i32.wrap_i64
                    if
                        local.get 1 i64.const 42 i64.store offset=8
                    else
                        unreachable
                    end
                    local.get 1 i64.load offset=8)
            )"#,
        )
        .expect("wat parses");
        WasmModule::parse(&wasm).expect("module parses")
    }

    /// Lift one `join_poison_module` function and return the raw post-join
    /// tail value.
    fn join_poison_result(idx: u32) -> StackVal {
        let m = join_poison_module();
        let reg = empty_registry();
        let result = lift_inline_call(
            &m,
            &reg,
            idx,
            vec![StackVal::Unknown],
            0,
            Rc::new(RefCell::new(HashMap::new())),
            Rc::new(RefCell::new(0)),
            Rc::new(RefCell::new(Vec::new())),
        );
        result.stack_result.expect("the tail load leaves a value")
    }

    /// Fixture for the loop-variant slot poison (issue #38 substrate).
    /// Functions: 0 = a loop body writes slot +8 (one-iteration artifact —
    /// the post-loop read must degrade); 1 = the body re-stores the exact
    /// pre-loop value (net no-op — the post-loop read stays sound).
    fn loop_poison_module() -> WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (global (mut i32) (i32.const 1048576))
                (memory 1)
                (func (;0;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    loop
                        local.get 1 i64.const 42 i64.store offset=8
                        local.get 0 i32.wrap_i64
                        br_if 0
                    end
                    local.get 1 i64.load offset=8)
                (func (;1;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 1 i64.const 7 i64.store offset=8
                    loop
                        local.get 1 i64.const 7 i64.store offset=8
                        local.get 0 i32.wrap_i64
                        br_if 0
                    end
                    local.get 1 i64.load offset=8)
            )"#,
        )
        .expect("wat parses");
        WasmModule::parse(&wasm).expect("module parses")
    }

    fn loop_poison_result(idx: u32) -> StackVal {
        let m = loop_poison_module();
        let reg = empty_registry();
        let result = lift_inline_call(
            &m,
            &reg,
            idx,
            vec![StackVal::Unknown],
            0,
            Rc::new(RefCell::new(HashMap::new())),
            Rc::new(RefCell::new(0)),
            Rc::new(RefCell::new(Vec::new())),
        );
        result.stack_result.expect("the tail load leaves a value")
    }

    #[test]
    fn loop_written_slot_post_loop_read_poisoned() {
        // `loop { slot = 42; br_if } ; read slot` — the map holds the
        // one-iteration value, but at runtime the loop may have written it
        // any number of times (or the surrounding control flow zero times).
        // The post-loop read must degrade to Unknown, not adopt 42.
        cov_mark::check!(join_tainted_read_poisoned);
        assert!(matches!(loop_poison_result(0), StackVal::Unknown));
    }

    #[test]
    fn loop_net_noop_slot_read_stays_sound() {
        // The body re-stores the exact pre-loop value: every iteration count
        // (including the abstract one) leaves the same state — no poison.
        let v = loop_poison_result(1);
        assert!(
            matches!(v, StackVal::I64(7)),
            "save/restore slot must keep its value, got {v:?}"
        );
    }

    #[test]
    fn join_conditional_then_write_read_poisoned() {
        // `if c { slot = 42 }; read slot` — the abstract state holds 42
        // unconditionally, the runtime only on then executions. The post-join
        // read must degrade to Unknown, not fabricate 42.
        cov_mark::check!(join_tainted_read_poisoned);
        assert!(matches!(join_poison_result(0), StackVal::Unknown));
    }

    #[test]
    fn join_dead_then_write_read_poisoned() {
        // `if c { slot = 42; return 7 }; read slot` — every execution that
        // reaches the read took the else path, where the slot was never
        // written. Reading 42 would fabricate a value from a returned path.
        cov_mark::check!(join_tainted_read_poisoned);
        assert!(matches!(join_poison_result(1), StackVal::Unknown));
    }

    #[test]
    fn join_sound_reads_not_poisoned() {
        // Else overwrite: the else arm's store lifts the taint; the read
        // observes the else value exactly as today (last-write-wins).
        assert!(matches!(join_poison_result(2), StackVal::I64(99)));
        // Net no-op: the then arm re-stores the pre-if value, so observing
        // it is indistinguishable from the pre-state — never tainted.
        assert!(matches!(join_poison_result(3), StackVal::I64(7)));
        // Else terminates: fall-through implies the then path ran, so the
        // then value is unconditionally valid downstream.
        assert!(matches!(join_poison_result(4), StackVal::I64(42)));
    }

    /// Fixture for the frame-descriptor DataKey fold (issue #34 t10): the
    /// `(i32) -> i64` descriptor-pointer ctor form where the row is built at
    /// runtime in the caller's frame. Import 0 = `vec_new_from_linear_memory`;
    /// func 1 = the small-symbol encoder (marker constants + char loop);
    /// func 2 = the `(ptr, count)` vec builder reaching import 0; func 3 =
    /// THE CTOR — `br_table` on `descriptor[0]`, selector 0 → keyed arm
    /// `vec![Symbol("UserData"), descriptor[8]]`, selector 1 → unit arm
    /// `vec![Symbol("AdminKey")]`. Callers: 4 = genuine keyed build
    /// (selector + payload stored right before the call); 5 = selector-only
    /// build (payload slot never stored); 6 = unit-variant build; 7 = build
    /// whose selector is stored with `i64.store` (a CONSTANT the ctor's
    /// `i32.load` slices soundly — little-endian byte extraction);
    /// 8 = build whose payload bytes a later `i64.store` at `+4` partially
    /// clobbers (the overlap refusal); 9 = build whose RUNTIME payload is
    /// stored 4-wide but read 8-wide (symbolic cells cannot be sliced).
    fn frame_descriptor_module() -> WasmModule {
        let wasm = wat::parse_str(
            r#"(module
                (import "v" "g" (func (param i64 i64) (result i64)))
                (memory 1)
                (data (i32.const 2000) "UserDataAdminKey")
                (global (mut i32) (i32.const 1048576))
                (func (;1;) (param i32 i32) (result i64)
                    (local i64 i32)
                    i32.const 95 drop
                    i32.const 48 drop
                    i32.const 65 drop
                    i32.const 97 drop
                    loop
                        local.get 3 local.get 1 i32.lt_u
                        if
                            local.get 2 i64.const 6 i64.shl
                            local.get 0 local.get 3 i32.add i32.load8_u
                            i64.extend_i32_u i64.const 32 i64.sub i64.or
                            local.set 2
                            local.get 3 i32.const 1 i32.add local.set 3
                            br 1
                        end
                    end
                    local.get 2 i64.const 8 i64.shl i64.const 14 i64.or)
                (func (;2;) (param i32 i32) (result i64)
                    local.get 0 i64.extend_i32_u
                    local.get 1 i64.extend_i32_u
                    call 0)
                (func (;3;) (param i32) (result i64)
                    (local i32)
                    global.get 0 i32.const 32 i32.sub local.tee 1 drop
                    block
                        block
                            local.get 0 i32.load br_table 0 1 0
                        end
                        local.get 1 i32.const 2000 i32.const 8 call 1 i64.store
                        local.get 1 local.get 0 i64.load offset=8 i64.store offset=8
                        local.get 1 i32.const 2 call 2
                        return
                    end
                    local.get 1 i32.const 2008 i32.const 8 call 1 i64.store
                    local.get 1 i32.const 1 call 2)
                (func (;4;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 1 i32.const 0 i32.store
                    local.get 1 local.get 0 i64.store offset=8
                    local.get 1 call 3)
                (func (;5;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 1 i32.const 0 i32.store
                    local.get 1 call 3)
                (func (;6;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 1 i32.const 1 i32.store
                    local.get 1 call 3)
                (func (;7;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 1 i64.const 0 i64.store
                    local.get 1 local.get 0 i64.store offset=8
                    local.get 1 call 3)
                (func (;8;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 32 i32.sub local.tee 1 drop
                    local.get 1 i32.const 0 i32.store
                    local.get 1 local.get 0 i64.store offset=8
                    local.get 1 i64.const 7 i64.store offset=4
                    local.get 1 call 3)
                (func (;9;) (param i64) (result i64)
                    (local i32)
                    global.get 0 i32.const 16 i32.sub local.tee 1 drop
                    local.get 1 i32.const 0 i32.store
                    local.get 1 local.get 0 i32.wrap_i64 i32.store offset=8
                    local.get 1 call 3)
            )"#,
        )
        .expect("wat parses");
        WasmModule::parse(&wasm).expect("module parses")
    }

    /// Lift one `frame_descriptor_module` caller with an optional
    /// pre-planted frame slot (the stale-state negative), returning the raw
    /// tail value.
    fn frame_descriptor_result(
        idx: u32,
        plant: Option<((u32, i32), StackVal)>,
    ) -> Option<StackVal> {
        let m = frame_descriptor_module();
        let reg = empty_registry();
        let slots = Rc::new(RefCell::new(HashMap::new()));
        if let Some((key, val)) = plant {
            slots.borrow_mut().insert(key, val);
        }
        let result = lift_inline_call(
            &m,
            &reg,
            idx,
            vec![StackVal::Param("user".to_string())],
            0,
            slots,
            Rc::new(RefCell::new(0)),
            Rc::new(RefCell::new(Vec::new())),
        );
        result.stack_result
    }

    fn as_key_vec(v: &StackVal) -> Option<&Vec<SorobanExpr>> {
        match v {
            StackVal::HostCallResult(e) => match e.as_ref() {
                SorobanExpr::VecConstruct(elems) => Some(elems),
                _ => None,
            },
            _ => None,
        }
    }

    #[test]
    fn dk_eval_slices_constant_cells_only() {
        let m = frame_descriptor_module();
        let mut ev = DkEval {
            module: &m,
            mem: HashMap::new(),
            sp: DkVal::StackPtr(0),
            steps: 0,
            gap_zero: None,
        };
        ev.store(0, DkVal::I64(0x1122334455667788), 8);
        ev.store(16, DkVal::Arg(0), 8);
        let sp = DkVal::StackPtr(0);
        // Exact-width read returns the cell as-is.
        assert_eq!(ev.load(&sp, 0, 8), Some(DkVal::I64(0x1122334455667788)));
        // Narrow reads inside the constant cell extract little-endian bytes.
        assert_eq!(ev.load(&sp, 0, 4), Some(DkVal::I32(0x55667788)));
        assert_eq!(ev.load(&sp, 4, 4), Some(DkVal::I32(0x11223344)));
        assert_eq!(ev.load(&sp, 6, 1), Some(DkVal::I32(0x22)));
        // A read crossing the cell's end stays out of model.
        assert_eq!(ev.load(&sp, 4, 8), None);
        // Symbolic cells cannot be sliced.
        assert_eq!(ev.load(&sp, 16, 4), None);
        assert_eq!(ev.load(&sp, 16, 8), Some(DkVal::Arg(0)));
    }

    #[test]
    fn frame_descriptor_keyed_ctor_folds_at_call_site() {
        // Keyed variant: the descriptor row {0, user} built right before the
        // call executes the ctor's real bytecode — the br_table picks arm 0,
        // the symbol comes from the data section, and the runtime payload
        // flows through untouched as the second vec element.
        cov_mark::check!(frame_descriptor_key_folded);
        let keyed = frame_descriptor_result(4, None).expect("keyed build leaves a value");
        let elems = as_key_vec(&keyed).expect("keyed build folds to a vec key");
        assert_eq!(elems.len(), 2);
        assert_eq!(elems[0], SorobanExpr::SymbolLiteral("UserData".to_string()));
        assert!(
            !matches!(elems[1], SorobanExpr::UnknownVal),
            "the payload embeds the caller's runtime value: {:?}",
            elems[1]
        );
        // Unit variant: selector 1 picks the payload-less arm by execution.
        let unit = frame_descriptor_result(6, None).expect("unit build leaves a value");
        let elems = as_key_vec(&unit).expect("unit build folds");
        assert_eq!(
            elems.as_slice(),
            [SorobanExpr::SymbolLiteral("AdminKey".to_string())]
        );
        // A CONSTANT selector stored 8-wide reads back through the ctor's
        // `i32.load` by little-endian byte extraction (blend-backstop's
        // descriptor shape) — the keyed arm still folds.
        let wide = frame_descriptor_result(7, None).expect("wide-selector build leaves a value");
        let elems = as_key_vec(&wide).expect("wide-selector build folds");
        assert_eq!(elems[0], SorobanExpr::SymbolLiteral("UserData".to_string()));
    }

    #[test]
    fn frame_descriptor_fold_refuses_unproven_slots() {
        cov_mark::check_count!(frame_descriptor_key_folded, 0);
        // Payload slot never stored: the keyed arm's load misses → refuse.
        assert!(
            frame_descriptor_result(5, None)
                .as_ref()
                .and_then(as_key_vec)
                .is_none()
        );
        // Stale state: the payload slot value exists in the abstract map but
        // NOT in the write log (a recognizer-seed-style direct insert whose
        // runtime overwrite the lifter may have missed) → unjustified →
        // refuse. This is the gate the blend-fixed-pool `ResData(SCALAR_12)`
        // fabrication audit forced.
        assert!(
            frame_descriptor_result(5, Some(((0, 8), StackVal::I64(1000000000000))))
                .as_ref()
                .and_then(as_key_vec)
                .is_none()
        );
        // A RUNTIME payload stored 4-wide but read 8-wide: symbolic cells
        // cannot be sliced, so the mismatched read refuses.
        assert!(
            frame_descriptor_result(9, None)
                .as_ref()
                .and_then(as_key_vec)
                .is_none()
        );
        // A later `i64.store` at +4 clobbers bytes of the payload stored at
        // +8 without touching its exact `(frame, offset)` log/map entries —
        // the overlap test refuses the payload, the ctor's load misses, and
        // the fold refuses (greptile P1 on PR #50).
        assert!(
            frame_descriptor_result(8, None)
                .as_ref()
                .and_then(as_key_vec)
                .is_none()
        );
    }
}
