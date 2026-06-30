/// Pipeline orchestration.
///
/// Runs the 5-stage decompilation pipeline:
/// 1. WASM Parser -> WasmModule
///    1b. Soroban Compliance Validation
/// 2. Spec Extractor -> TypeRegistry
/// 3. Pattern Matcher -> Soroban-Aware IR
/// 4. IR Optimizer -> High-Level IR
/// 5. Rust Emitter -> Formatted source code
use std::collections::HashMap;

use crate::codegen::module::{assemble_generic_module, assemble_module, format_source};
use crate::ir::correctness::{
    annotate_uninferable_collections, annotate_uninferable_gets, clone_reused_move_params,
    husk_type_mismatched_ok_literal,
};
use crate::ir::optimizer::{
    drop_void_unknown_value_return_guards, fold_tautological_tag_guards, optimize_stmts,
    optimize_stmts_preserve_host_calls, propagate_variable_names, recover_match_arm_storage_keys,
    recover_tokens_sorted_validation, remove_self_assignments,
    replace_void_with_none_in_option_fields,
};
use crate::ir::soroban_ir::{MatchArm, MatchPattern, SorobanExpr, SorobanStmt, StorageType};
use crate::pattern::lift_functions;
use crate::pattern::lifter::{
    find_identity_passthrough_param, is_panic_guard_shell, stmts_contain_unknown,
};
use crate::spec::registry::TypeRegistry;
use crate::wasm::WasmModule;
use crate::wasm::imports::HostModule;
use crate::wasm::validate::validate_soroban;
use crate::{
    DecompileError, DecompileHints, DecompileIR, DecompileMode, DecompileOptions, DecompileResult,
    FunctionHints, HintValue, ValidationReport,
};
use stellar_xdr::curr::ScSpecTypeDef;

/// Run the full decompilation pipeline.
pub fn run(wasm: &[u8], options: &DecompileOptions) -> Result<DecompileResult, DecompileError> {
    let ir = run_to_ir(wasm, options)?;
    Ok(DecompileResult {
        source: ir.source,
        sdk_version: ir.sdk_version,
        standard_interfaces: ir.standard_interfaces,
        validation: ir.validation,
    })
}

/// Run the full decompilation pipeline and return all intermediate representations.
pub fn run_to_ir(wasm: &[u8], options: &DecompileOptions) -> Result<DecompileIR, DecompileError> {
    // Stage 0 (optional): Pre-optimize WASM with wasm-opt
    let optimized;
    let wasm = if options.pre_optimize {
        log::info!("Stage 0: Pre-optimizing WASM with wasm-opt");
        optimized = run_wasm_opt(wasm)?;
        log::info!(
            "  Optimized: {} -> {} bytes ({:.1}% reduction)",
            wasm.len(),
            optimized.len(),
            (1.0 - optimized.len() as f64 / wasm.len() as f64) * 100.0,
        );
        &optimized
    } else {
        wasm
    };

    // Stage 1: Parse WASM
    log::info!("Stage 1: Parsing WASM binary ({} bytes)", wasm.len());
    let mut wasm_module = WasmModule::parse(wasm).map_err(DecompileError::WasmParse)?;

    log::info!(
        "  Imports: {}, Exports: {}, Functions: {}, Data segments: {}",
        wasm_module.imports.len(),
        wasm_module.exports.functions.len(),
        wasm_module.functions.len(),
        wasm_module.data_sections.segments.len(),
    );

    // Detect Soroban vs generic WASM
    let is_soroban = match options.mode {
        DecompileMode::Soroban => true,
        DecompileMode::Generic => false,
        DecompileMode::Auto => {
            wasm_module.custom_sections.contains_key("contractspecv0")
                || wasm_module.custom_sections.contains_key("contractmetav0")
                || wasm_module
                    .imports
                    .functions
                    .iter()
                    .any(|f| !matches!(f.module, HostModule::Unknown))
        }
    };

    if !is_soroban {
        log::info!("  Detected generic (non-Soroban) WASM binary");
    }

    // Stage 1b: Soroban compliance validation
    let mut validation = if is_soroban {
        log::info!("Stage 1b: Validating Soroban compliance");
        validate_soroban(&wasm_module)
    } else {
        ValidationReport::default()
    };

    // Merge parser-collected diagnostics
    let mut parse_report = ValidationReport::default();
    for diag in std::mem::take(&mut wasm_module.parse_diagnostics) {
        parse_report.add(diag);
    }
    validation.merge(parse_report);

    if is_soroban {
        if validation.has_warnings() {
            for diag in &validation.diagnostics {
                log::warn!("  {}", diag);
            }
        } else {
            log::info!("  Module is Soroban-compliant");
        }
    }

    // Add non-Soroban warning diagnostic
    if !is_soroban {
        validation.add(crate::wasm::validate::SorobanDiagnostic {
            severity: crate::wasm::validate::DiagnosticSeverity::Warning,
            category: crate::wasm::validate::DiagnosticCategory::NonRustSdk,
            message: "This WASM binary is not a Soroban smart contract. \
                      Output is a best-effort reconstruction from raw WASM bytecode."
                .to_string(),
            function_index: None,
        });
    }

    // Stage 2: Extract spec and build type registry
    log::info!("Stage 2: Extracting contract spec");
    let registry = TypeRegistry::from_wasm(wasm)?;

    let sdk_version = registry.sdk_version();

    // Detect non-Rust SDK contracts: contractspecv0 present but no rssdkver metadata
    if is_soroban && sdk_version.is_none() && !registry.functions.is_empty() {
        validation.add(crate::wasm::validate::SorobanDiagnostic {
            severity: crate::wasm::validate::DiagnosticSeverity::Warning,
            category: crate::wasm::validate::DiagnosticCategory::NonRustSdk,
            message: "No Rust SDK version detected (rssdkver metadata absent). \
                      Contract may be from a non-Rust SDK; function body recovery may be limited."
                .to_string(),
            function_index: None,
        });
    }

    log::info!(
        "  Functions: {}, Structs: {}, Enums: {}, Events: {}, SDK: {}",
        registry.functions.len(),
        registry.structs.len(),
        registry.enums.len() + registry.unions.len(),
        registry.events.len(),
        sdk_version.as_deref().unwrap_or("unknown"),
    );

    // Stage 3: Pattern matching - lift WASM to Soroban IR
    log::info!("Stage 3: Pattern matching and function lifting");
    let mut contract_module =
        lift_functions(&wasm_module, &registry, options.spec_only, is_soroban);

    log::info!(
        "  Lifted {} functions, {} types, {} error enums, {} events",
        contract_module.functions.len(),
        contract_module.types.len(),
        contract_module.error_enums.len(),
        contract_module.events.len(),
    );

    // Stage 4: Optimize IR
    log::info!("Stage 4: Optimizing IR");
    for func in &mut contract_module.functions {
        let pre_opt_body = if func.had_host_calls {
            Some(func.body.clone())
        } else {
            None
        };
        if std::env::var("DBG_PREOPT")
            .map(|v| v.is_empty() || v == func.name)
            .unwrap_or(false)
        {
            eprintln!(
                "[DBG_PREOPT] {} pre-opt ({} stmts):\n{:#?}",
                func.name,
                func.body.len(),
                func.body
            );
        }
        // Data-carrying-enum identity round-trip (`fn f(v: E) -> E { v }`): the SDK's
        // decode→match→re-encode lifts to a `Match` over `v` with degenerate per-variant
        // arms that the optimizer would strip to an empty body → `todo!`. Recognize it
        // here (pre-optimization, while the match is intact) and collapse to the faithful
        // `v` so the identity survives. See `is_enum_identity_roundtrip` for the gating.
        if let Some(ret_ty) = &func.return_type
            && let Some(param_name) = find_identity_passthrough_param(&func.params, ret_ty)
            && is_enum_identity_roundtrip(&func.body, &param_name)
        {
            cov_mark::hit!(enum_identity_roundtrip);
            func.body = vec![SorobanStmt::Return(Some(SorobanExpr::Param(param_name)))];
        }

        // Router token-list validation: recognize the SDK's sorted+unique token
        // check (inlined into ~27 accessors) — whose loop lifts mangled (lost
        // induction/bound, unconditional mid-loop break) — by its unique
        // `TokensNotSorted` + `DuplicatesNotAllowed` error-code pair, and lift it
        // to the faithful `for i in 1..tokens.len() { … }`. Run pre-optimization
        // while the mangled loop and the recovered error codes are both intact.
        func.body = recover_tokens_sorted_validation(std::mem::take(&mut func.body));

        // Tautological SDK type-tag guards: `<param>.get_tag() == Tag::<T>` where
        // the param's type uniquely fixes the tag (Address→AddressObject, …) is
        // always true. Fold to a constant `bool` (using the param types) so the
        // optimizer's constant-`if` folding drops the guard, clearing the
        // non-compiling `get_tag()`/`Tag` references. Run pre-optimization while
        // the operand is still the lifter's `ValTag(Param(_))` (before naming).
        func.body = fold_tautological_tag_guards(std::mem::take(&mut func.body), &func.params);

        let optimized = optimize_stmts(std::mem::take(&mut func.body));
        func.body = optimized;

        // Void functions: drop SDK Val-decode dispatch husks (`if <lost-tag> {
        // return <int> }`) that inlining a non-void decoder leaves behind. The
        // value-return is invalid in a void context (codegen drops it → a stray
        // `if todo!() == 1114112 {}`); when the condition is itself `UnknownVal`
        // the guard is a pure artifact. Gated on void return type here so the
        // pass never touches a real value-returning decoder.
        if func.return_type.is_none() {
            func.body = drop_void_unknown_value_return_guards(std::mem::take(&mut func.body));
        }

        // When optimization empties a function body that had host calls,
        // re-optimize preserving orphan host calls so users see
        // env.module().function() calls instead of todo!().
        if func.body.is_empty()
            && func.had_host_calls
            && let Some(stmts) = pre_opt_body
        {
            func.body = optimize_stmts_preserve_host_calls(stmts);
        }

        // Identity-passthrough detection: after optimization removes orphan host calls,
        // if the body is empty and a parameter's type matches the return type, this is
        // a validate-and-return function (e.g., test_i64(v: i64) -> i64 { v }).
        // Guard: skip when the lifter detected host calls — those functions had real
        // logic that was lost during lifting, not genuine identity passthroughs.
        if func.body.is_empty()
            && !func.had_host_calls
            && let Some(ret_ty) = &func.return_type
            && let Some(param_name) = find_identity_passthrough_param(&func.params, ret_ty)
        {
            cov_mark::hit!(identity_passthrough_applied);
            func.body
                .push(SorobanStmt::Return(Some(SorobanExpr::Param(param_name))));
        }

        // Extended identity-passthrough: body is a single `param.get(0)` return/expr
        // or `StructConstruct { field: param.field, ... }` where param type matches
        // return type — union/struct validate-and-return.
        // No had_host_calls guard here — these ARE genuine passthroughs even when
        // host calls (like vec_unpack) were used for parameter destructuring.
        if func.body.len() == 1
            && let Some(ret_ty) = &func.return_type
            && let Some(param_name) = find_identity_passthrough_param(&func.params, ret_ty)
        {
            let get_expr = match &func.body[0] {
                SorobanStmt::Expr(e) => Some(e),
                SorobanStmt::Return(Some(e)) => Some(e),
                _ => None,
            };
            let is_passthrough = get_expr.is_some_and(|e| {
                is_identity_get_pattern(e, &param_name)
                    || is_identity_struct_reconstruct(e, &param_name)
                    || is_identity_bool_literal(e, ret_ty)
            });
            if is_passthrough {
                func.body = vec![SorobanStmt::Return(Some(SorobanExpr::Param(param_name)))];
            }
        }

        // Artifact loop unwrap: `loop { expr }` as the sole body statement of a
        // function with a return type → inline `expr`. SDK copy-loop patterns
        // produce WASM loops whose break/return paths are lost during lifting,
        // leaving an exitless loop wrapping the real return expression.
        if func.return_type.is_some() {
            let should_unwrap = matches!(
                func.body.as_slice(),
                [SorobanStmt::Loop { body }] if matches!(body.as_slice(), [SorobanStmt::Expr(_)])
            );
            if should_unwrap {
                let old_body = std::mem::take(&mut func.body);
                if let Some(SorobanStmt::Loop { body }) = old_body.into_iter().next() {
                    func.body = body;
                }
            }
        }

        // Trailing panic removal: when a function with a return type ends with
        // a bare `panic!()` at the top level, it's a WASM trap artifact from the
        // structurizer losing the return path. Remove it so the preceding
        // expression becomes the tail return value.
        if func.return_type.is_some()
            && func.body.len() >= 2
            && matches!(
                func.body.last(),
                Some(SorobanStmt::Expr(SorobanExpr::Panic))
            )
        {
            func.body.pop();
        }

        // Void function panic removal: for void/unit-returning functions,
        // a sole panic!() in the body is an SDK parameter validation trap artifact.
        if matches!(
            func.body.as_slice(),
            [SorobanStmt::Expr(SorobanExpr::Panic)]
        ) && matches!(
            &func.return_type,
            None | Some(stellar_xdr::curr::ScSpecTypeDef::Void)
        ) {
            func.body.clear();
        }

        // Append panic!() for functions whose wrapper calls a bare trap function.
        // This must happen AFTER optimization because the optimizer's remove_dead_code
        // would kill the Panic (the inlined body's loop contains Return(None) which
        // makes the loop appear infinite, causing everything after it to be dead code).
        if func.wrapper_panics {
            // Skip panic append for void functions with empty bodies —
            // the trap comes from SDK parameter validation, not real logic.
            let is_void_empty = func.body.is_empty()
                && matches!(
                    &func.return_type,
                    None | Some(stellar_xdr::curr::ScSpecTypeDef::Void)
                );
            if !is_void_empty {
                let already_has_panic = func.body.iter().any(|s| {
                    matches!(
                        s,
                        SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_))
                    )
                });
                if !already_has_panic {
                    cov_mark::hit!(wrapper_panic_appended);
                    func.body.push(SorobanStmt::Expr(SorobanExpr::Panic));
                }
            }
        }

        // All-or-nothing for value-returning reconstructions: a body that — after
        // optimization and trailing-panic handling — is *entirely* validation-guard
        // panics (`if cond { panic!() }` with no value path) is the misleading shell
        // a checked-i128 library fn collapses to when its arithmetic didn't compose.
        // It cannot type-check as the value it returns, and the reference-free metric
        // would score it as clean — emit an honest stub instead. Gated on a
        // deceptively-clean body (no `todo!`) and an actual `if` guard, so it never
        // touches an honest partial or a bare diverging `panic!()` getter.
        if func
            .return_type
            .as_ref()
            .is_some_and(|t| !matches!(t, ScSpecTypeDef::Void))
            && is_panic_guard_shell(&func.body)
            && !stmts_contain_unknown(&func.body)
        {
            func.body.clear();
        }
    }

    // Soroban-specific post-optimization passes (4b–4e).
    // These operate on Soroban IR patterns (storage, events, enums, etc.)
    // that don't exist in generic WASM output.
    if is_soroban {
        // Stage 4b: Infer return types for cross-contract calls in tail position.
        for func in &mut contract_module.functions {
            if let Some(ret_ty) = &func.return_type {
                cov_mark::hit!(stage_4b_return_type_inferred);
                // `type_str` drives the non-Result `InvokeContract` case; the
                // `TryInvokeContract` case derives its own ok type from `ret_ty`,
                // so run the pass even for `Result<..>` returns (where
                // `spec_type_to_string` yields `None` and the old gate skipped it,
                // leaving `try_invoke_contract::<Val>` un-inferred).
                let type_str = spec_type_to_string(ret_ty).unwrap_or_default();
                set_invoke_return_type_in_tail(&mut func.body, &type_str, ret_ty);
            }
        }
        log::trace!("Pipeline pass: stage_4b return_type_inference");

        // Stage 4b3: a tail `Vec`/`Map` `.get(i)` returns `Option<T>`; when the
        // enclosing function returns the element type `T` (not `Option`/`Result`/
        // void), the source wrote `.get(i).unwrap()` and the lifter dropped the
        // unwrap. Re-attach it so the body type-checks (issues #19/#20: bls/bn254
        // `fr_vec_get`).
        for func in &mut contract_module.functions {
            if let Some(rt) = &func.return_type
                && !matches!(
                    rt,
                    stellar_xdr::curr::ScSpecTypeDef::Option(_)
                        | stellar_xdr::curr::ScSpecTypeDef::Result(_)
                        | stellar_xdr::curr::ScSpecTypeDef::Void
                )
            {
                wrap_tail_vec_get_unwrap(&mut func.body);
            }
        }
        log::trace!("Pipeline pass: stage_4b3 vec_get_unwrap");

        // Stage 4b3b: strip a leaked tuple-scalar term from a fold-bearing match
        // composition (udt::add). `recover_vec_iter_fold` moves UdtD's `tup.0`
        // into the arm, but wasm-opt's hoisted copy of that scalar still lands in
        // the post-match return as `Add(Add(<scrutinee>.field, a), b)` (rendered
        // `a.a + a + b`). Drop the leaked `<scrutinee param>.field` term so the
        // return is the faithful `a + b` (issue #14, udt).
        for func in &mut contract_module.functions {
            strip_leaked_fold_scalar(&mut func.body);
        }
        log::trace!("Pipeline pass: stage_4b3b strip_leaked_fold_scalar");

        // Stage 4b4: recover misrouted crypto struct-field arguments (issue #19,
        // bls `dummy_verify`). A reused WASM local can alias both a struct field
        // (`proof.fp2`) and an unrelated scratch value — the BLS scalar-field
        // modulus, materialized as `u256_val_from_be_bytes(bytes_new_from_linear_
        // memory(addr, 32))`. The lifter names both bindings `var_N`, so the
        // optimizer's dead-store + single-use inlining can substitute the modulus
        // into `map_fp2_to_g2(..)`, emitting the non-existent `env.buf()` and
        // failing to compile. Rewrite such a misrouted argument back to the
        // matching struct-param field. See `recover_crypto_field_args`.
        for func in &mut contract_module.functions {
            recover_crypto_field_args(&mut func.body, &func.params, &registry);
        }
        log::trace!("Pipeline pass: stage_4b4 recover_crypto_field_args");

        // Stage 4b5: bind data-carrying match-arm payloads (Fix D1, issue #14, udt). A
        // Soroban enum with data is a 2-element Vec `[discriminant, payload]`, so an arm
        // reads the variant's data via `<scrutinee>.get(1)`. The lifter leaves such arms
        // with a `_` binding and the body referencing the raw `scrutinee.get(1)` (a type
        // error — the scrutinee is the enum, not its payload). Post-optimization (so
        // transient payload reads that the optimizer strips, e.g. constructor's
        // `key.get(1)`, are already gone), give the arm a real binding and rewrite its
        // surviving payload reads to it: `Variant(v0) => ... v0 ...`.
        for func in &mut contract_module.functions {
            recover_enum_payload_bindings(&mut func.body);
        }
        log::trace!("Pipeline pass: stage_4b5 recover_enum_payload_bindings");

        // Stage 4b6: recover a `Result<Option<T>, E>`-returning enum dispatch (Fix D,
        // issue #14, udt `recursive_enum`). The lifter recovers the match and (via 4b5)
        // the payload binding, but drops the data-less arm(s) (non-exhaustive match),
        // leaves the surviving arm's tail as a bare `Expr` (so codegen's `Ok(..)` wrap
        // never fires), and lowers `Map::get` to a `contains_key` probe. Restore the
        // missing data-less variants as `Ok(None)`, rewrite the tail `contains_key`→`get`,
        // and mark each arm's tail for `Ok(..)` wrapping.
        for func in &mut contract_module.functions {
            recover_result_option_enum_match(&mut func.body, &func.return_type, &registry);
        }
        log::trace!("Pipeline pass: stage_4b6 recover_result_option_enum_match");

        // Stage 4b2: Replace Void/UnknownVal with None in Option-typed struct/event fields.
        for func in &mut contract_module.functions {
            func.body =
                replace_void_with_none_in_option_fields(std::mem::take(&mut func.body), &registry);
        }
        log::trace!("Pipeline pass: stage_4b2 void_to_none_in_option_fields");

        // Stage 4c: Recover storage keys from match scrutinees.
        for func in &mut contract_module.functions {
            cov_mark::hit!(stage_4c_storage_key_recovered);
            func.body = recover_match_arm_storage_keys(std::mem::take(&mut func.body));
        }
        log::trace!("Pipeline pass: stage_4c recover_match_arm_storage_keys");

        // Stage 4c2: Recover storage keys for extend_ttl inside if-has guards.
        for func in &mut contract_module.functions {
            recover_extend_ttl_keys(&mut func.body);
        }
        log::trace!("Pipeline pass: stage_4c2 recover_extend_ttl_keys");

        // Stage 4c3: Merge orphan LedgerSequence into adjacent extend_ttl args.
        for func in &mut contract_module.functions {
            merge_orphan_ledger_sequence(&mut func.body);
        }
        log::trace!("Pipeline pass: stage_4c3 merge_orphan_ledger_sequence");

        // Stages 4c4-4c7: Repair weak operands from optional function-scoped
        // hints. The index is built once and shared across all four passes so
        // each function lookup is O(1) instead of the previous O(F_hints)
        // linear scan per pass per function.
        if let Some(hints) = &options.hints {
            let hints_index = build_hints_index(hints);
            for func in &mut contract_module.functions {
                let empty: Vec<&FunctionHints> = Vec::new();
                let func_hints = hints_index
                    .get(func.name.as_str())
                    .unwrap_or(&empty)
                    .as_slice();
                if func_hints.is_empty() {
                    continue;
                }
                if let Some(key) = unique_storage_hint_key_for_function(func_hints) {
                    repair_unknown_storage_keys_from_hint(&mut func.body, &key);
                }
                if let Some(event_hint) = unique_event_hint_for_function(func_hints) {
                    repair_unknown_event_values_from_hint(&mut func.body, &event_hint);
                }
                if let Some(function) = unique_invoke_hint_function_for_function(func_hints) {
                    repair_unknown_invoke_functions_from_hint(&mut func.body, &function);
                }
                if let Some(auth_hint) = unique_auth_hint_for_function(func_hints) {
                    repair_weak_auth_from_hint(&mut func.body, &auth_hint);
                }
            }
        }
        log::trace!("Pipeline pass: stage_4c4_4c7 hint-driven repairs");

        // Stage 4d: Remove trailing orphan .len() from Result<(), E> functions.
        for func in &mut contract_module.functions {
            if let Some(stellar_xdr::curr::ScSpecTypeDef::Result(r)) = &func.return_type
                && matches!(*r.ok_type, stellar_xdr::curr::ScSpecTypeDef::Void)
                && let Some(SorobanStmt::Expr(SorobanExpr::MethodCall { method, args, .. })) =
                    func.body.last()
                && method == "len"
                && args.is_empty()
            {
                func.body.pop();
            }
        }
        log::trace!("Pipeline pass: stage_4d remove_trailing_len");

        // Stage 4e: Remove .unwrap() from StorageGet in Option-returning functions.
        for func in &mut contract_module.functions {
            if matches!(
                &func.return_type,
                Some(stellar_xdr::curr::ScSpecTypeDef::Option(_))
            ) {
                remove_storage_unwrap(&mut func.body);
            }
        }
        log::trace!("Pipeline pass: stage_4e remove_storage_unwrap");
    }

    // Stage 4f: Resolve Local(N) to Param(name) when N corresponds to a
    // function parameter slot and the local is never re-bound in the body.
    for func in &mut contract_module.functions {
        cov_mark::hit!(stage_4f_local_resolved_to_param);
        let param_local_base = infer_param_local_base(
            &func.body,
            &func.params,
            func.wasm_param_base,
            func.takes_env,
        );
        resolve_param_locals(&mut func.body, &func.params, param_local_base);
    }
    log::trace!("Pipeline pass: stage_4f resolve_param_locals");

    // Stage 4g: Strip unused env parameter.
    // If the function body never references `env`, remove `takes_env` so the
    // generated signature matches the original source more closely.
    for func in &mut contract_module.functions {
        if func.takes_env && !stmts_use_env(&func.body) {
            cov_mark::hit!(stage_4g_env_removed);
            func.takes_env = false;
        }
    }
    log::trace!("Pipeline pass: stage_4g strip_unused_env");

    // Soroban-specific post-optimization passes (4h–4y + final cleanup).
    if is_soroban {
        // Stage 4h: Resolve unused params in cross-contract call args.
        for func in &mut contract_module.functions {
            cov_mark::hit!(stage_4h_artifact_replaced_with_param);
            resolve_unused_invoke_params(&mut func.body, &func.params);
        }
        log::trace!("Pipeline pass: stage_4h resolve_unused_invoke_params");

        // Stage 4h2: Resolve unbound Local(N) in InvokeContract/ValConvert args.
        for func in &mut contract_module.functions {
            resolve_unbound_invoke_locals(&mut func.body);
        }
        log::trace!("Pipeline pass: stage_4h2 resolve_unbound_invoke_locals");

        // Stage 4i: Promote match arm expressions to tail position.
        for func in &mut contract_module.functions {
            if func.return_type.is_some() {
                promote_match_arm_exprs(&mut func.body);
            }
        }
        log::trace!("Pipeline pass: stage_4i promote_match_arm_exprs");

        // Stage 4j: Recover integer enum cast arms.
        for func in &mut contract_module.functions {
            recover_enum_cast_arms(&mut func.body, &registry);
        }
        log::trace!("Pipeline pass: stage_4j recover_enum_cast_arms");

        // Stage 4k: Replace artifact let bindings used in match arms.
        for func in &mut contract_module.functions {
            replace_match_arm_artifact_refs(&mut func.body, &registry);
        }
        log::trace!("Pipeline pass: stage_4k replace_match_arm_artifact_refs");

        // Stage 4p: Recover struct field operations in match arms.
        for func in &mut contract_module.functions {
            if let Some(ref ret_ty) = func.return_type {
                recover_struct_field_arms(&mut func.body, &registry, ret_ty);
            }
        }
        log::trace!("Pipeline pass: stage_4p recover_struct_field_arms");

        // Stage 4l: Recover high-level event publish pattern.
        for func in &mut contract_module.functions {
            recover_event_publish(&mut func.body, &registry, &func.params);
        }
        log::trace!("Pipeline pass: stage_4l recover_event_publish");

        // Stage 4m: Recover enum key construction from tuple patterns.
        for func in &mut contract_module.functions {
            cov_mark::hit!(stage_4m_enum_key_constructed);
            recover_enum_key_construction(&mut func.body, &registry);
        }
        log::trace!("Pipeline pass: stage_4m recover_enum_key_construction");

        // Stage 4m2: Fix misidentified enum variant keys.
        for func in &mut contract_module.functions {
            fix_misidentified_instance_keys(&mut func.body, &registry);
        }
        log::trace!("Pipeline pass: stage_4m2 fix_misidentified_instance_keys");

        // Re-run variable name propagation + self-assignment removal.
        for func in &mut contract_module.functions {
            let param_names: Vec<String> = func.params.iter().map(|p| p.name.clone()).collect();
            func.body = propagate_variable_names(std::mem::take(&mut func.body), &param_names);
            func.body = remove_self_assignments(std::mem::take(&mut func.body));
        }
        log::trace!("Pipeline pass: re-run propagate_variable_names + remove_self_assignments");

        // Stage 4n: Fix BoolLiteral in numeric-returning functions.
        for func in &mut contract_module.functions {
            if let Some(ref ret_ty) = func.return_type
                && is_numeric_type(ret_ty)
            {
                cov_mark::hit!(stage_4n_bool_literal_fixed);
                fix_bool_literal_returns(&mut func.body);
            }
        }
        log::trace!("Pipeline pass: stage_4n fix_bool_literal_returns");

        // Stage 4n2: Fix BoolLiteral in StorageSet values.
        for func in &mut contract_module.functions {
            fix_bool_in_storage_set(&mut func.body);
        }
        log::trace!("Pipeline pass: stage_4n2 fix_bool_in_storage_set");

        // Stage 4o: Strip return values from void functions.
        for func in &mut contract_module.functions {
            let is_void =
                func.return_type.is_none() || matches!(func.return_type, Some(ScSpecTypeDef::Void));
            if is_void {
                cov_mark::hit!(stage_4o_void_return_stripped);
                strip_returns_in_void_fn(&mut func.body);
                drop_dead_lets(&mut func.body);
            }
        }
        log::trace!("Pipeline pass: stage_4o strip_void_returns");

        // Stage 4p2: Convert VecConstruct → TupleConstruct in tuple-returning functions.
        for func in &mut contract_module.functions {
            if let Some(ScSpecTypeDef::Tuple(t)) = &func.return_type {
                let expected_len = t.value_types.len();
                convert_vec_to_tuple_return(&mut func.body, expected_len);
            }
        }
        log::trace!("Pipeline pass: stage_4p2 convert_vec_to_tuple_return");

        // Stage 4p3: Type the operands of recovered i128 share-math. Cross-contract
        // calls (`balance(...)`) and storage gets otherwise default to
        // `soroban_sdk::Val`, which doesn't type-check in `balance - amount`. Pass 1
        // retypes invokes and inline gets per function while collecting the storage
        // keys read as i128; pass 2 types every get of those keys across all
        // functions (so a tuple-returning `get_rsrvs` or a dead `let reserve_a` whose
        // slot is i128 elsewhere is typed too).
        let mut i128_keys: Vec<SorobanExpr> = Vec::new();
        for func in &mut contract_module.functions {
            let used = coerce_i128_invoke_types(&mut func.body, &func.params);
            for key in used.keys {
                if !i128_keys.contains(&key) {
                    i128_keys.push(key);
                }
            }
        }
        for func in &mut contract_module.functions {
            type_i128_key_gets(&mut func.body, &i128_keys);
        }
        log::trace!("Pipeline pass: stage_4p3 coerce_i128_invoke_types");

        // Stage 4q: Replace incomplete struct reconstructions with parameter references.
        for func in &mut contract_module.functions {
            replace_incomplete_struct_with_param(&mut func.body, &func.params, &registry);
        }
        log::trace!("Pipeline pass: stage_4q replace_incomplete_struct_with_param");

        // Stage 4r: Strip trailing panic from non-wrapper functions.
        for func in &mut contract_module.functions {
            if !func.wrapper_panics
                && func.body.len() >= 2
                && matches!(
                    func.body.last(),
                    Some(SorobanStmt::Expr(SorobanExpr::Panic))
                )
            {
                cov_mark::hit!(stage_4r_trailing_panic_stripped);
                func.body.pop();
            }
        }
        log::trace!("Pipeline pass: stage_4r strip_non_wrapper_trailing_panic");

        // Stage 4s: Recover map_unpack getter pattern.
        for func in &mut contract_module.functions {
            recover_map_unpack_getter(func, &registry);
        }
        log::trace!("Pipeline pass: stage_4s recover_map_unpack_getter");

        // Stage 4t: Recover broken struct getter bodies.
        for func in &mut contract_module.functions {
            recover_broken_struct_getter(func, &registry);
        }
        log::trace!("Pipeline pass: stage_4t recover_broken_struct_getter");

        // Stage 4t2: Bind orphan StorageGet to a named variable.
        for func in &mut contract_module.functions {
            bind_orphan_struct_get(func, &registry);
        }
        log::trace!("Pipeline pass: stage_4t2 bind_orphan_struct_get");

        // Stage 4w: Replace StorageGet(UnknownVal).field with local_var.field.
        for func in &mut contract_module.functions {
            resolve_unknown_key_field_access(&mut func.body);
        }
        log::trace!("Pipeline pass: stage_4w resolve_unknown_key_field_access [1]");

        // Stage 4u: Remove SymbolLiteral Let bindings that shadow function parameters.
        for func in &mut contract_module.functions {
            let param_names: Vec<String> = func.params.iter().map(|p| p.name.clone()).collect();
            remove_symbol_param_shadows(&mut func.body, &param_names);
        }
        log::trace!("Pipeline pass: stage_4u remove_symbol_param_shadows");

        // Stage 4v: Recover has-guarded StorageGet return values.
        for func in &mut contract_module.functions {
            recover_has_get_return_value(func, &registry);
        }
        log::trace!("Pipeline pass: stage_4v recover_has_get_return_value");

        // Final cleanup: re-run dead-let elimination.
        for func in &mut contract_module.functions {
            use crate::ir::optimizer::remove_redundant_lets_public;
            func.body = remove_redundant_lets_public(std::mem::take(&mut func.body));
        }
        log::trace!("Pipeline pass: final_cleanup remove_redundant_lets");

        // Re-run Stage 4w after final cleanup.
        for func in &mut contract_module.functions {
            resolve_unknown_key_field_access(&mut func.body);
        }
        log::trace!("Pipeline pass: stage_4w resolve_unknown_key_field_access [2]");

        // Stage 4x: Fix RequireAuth referencing an EnumConstruct variable.
        for func in &mut contract_module.functions {
            fix_require_auth_on_enum_key(&mut func.body);
        }
        log::trace!("Pipeline pass: stage_4x fix_require_auth_on_enum_key");

        // Stage 4y: Resolve unbound var_N in event publish data.
        for func in &mut contract_module.functions {
            let param_local_base = infer_param_local_base(
                &func.body,
                &func.params,
                func.wasm_param_base,
                func.takes_env,
            );
            resolve_event_data_params(&mut func.body, &func.params, param_local_base);
        }
        log::trace!("Pipeline pass: stage_4y resolve_event_data_params");
    }

    // Final compile-correctness pass: annotate un-inferable storage gets with an
    // explicit `Val` type so they type-check (E0277/E0282/E0284), then the same
    // for empty `Map::new`/`Vec::new` collections whose value type was lost
    // (E0283 → `Map::<_, Val>`). Runs last, on the fully-shaped body after every
    // other stage, and applies to all output (not just SDK contracts). See
    // `ir::correctness::{annotate_uninferable_gets, annotate_uninferable_collections}`.
    for func in &mut contract_module.functions {
        let returns_value = !matches!(&func.return_type, None | Some(ScSpecTypeDef::Void));
        let body = std::mem::take(&mut func.body);
        // A get in tail position is the inferable return value ONLY if the body
        // actually supplies the tail. When codegen synthesizes the tail (`Ok(())`
        // for `Result<(), E>`, or a `todo!()` value tail for a lost-value fn), the
        // trailing statement is discarded — its un-inferable `V` must be annotated.
        // Without this, a `Result<(), E>` fn's trailing discarded `.get()` was
        // mistaken for the return value and left to fail inference (E0284).
        let body_supplies_tail = returns_value
            && !crate::codegen::module::codegen_synthesizes_tail(&func.return_type, &body);
        let body = annotate_uninferable_gets(body, body_supplies_tail);
        let body = annotate_uninferable_collections(body);
        // Lever 2: a fabricated literal in the success tail whose type contradicts a
        // scalar `Result<T, E>` ok-type (e.g. `Ok(false)` in `-> Result<u128, E>`) →
        // honest `todo!()`. Guaranteed-mismatch only; never touches a coercing value.
        let body = husk_type_mismatched_ok_literal(body, func.return_type.as_ref());
        func.body = clone_reused_move_params(body, &func.params);
    }

    // Stage 5: Generate Rust source
    log::info!("Stage 5: Generating Rust source");
    let tokens = if is_soroban {
        assemble_module(&contract_module, &registry)
    } else {
        assemble_generic_module(&contract_module)
    };
    let mut source = format_source(&tokens).map_err(|e| DecompileError::Format(e.to_string()))?;

    // Prepend warning headers
    let has_non_rust_sdk = validation.diagnostics.iter().any(|d| {
        matches!(
            d.category,
            crate::wasm::validate::DiagnosticCategory::NonRustSdk,
        )
    });
    if !is_soroban {
        let header = "// NOTE: This WASM binary is not a Soroban smart contract.\n\
                       // No contractspecv0 metadata was found. The output below is a best-effort\n\
                       // reconstruction of the exported functions from raw WASM bytecode.\n\n";
        source = format!("{}{}", header, source);
    } else if has_non_rust_sdk {
        // Soroban metadata is present but no rssdkver was found. The Rust-SDK
        // wrapper detectors do not apply, so function bodies are heuristic only.
        // Make this prominent so reviewers do not mistake the output for an
        // accurate reconstruction of the original source.
        let header = "// ============================================================\n\
                      // WARNING: non-Rust SDK contract.\n\
                      // \n\
                      // This binary has a Soroban contract spec but no Rust SDK\n\
                      // version (`rssdkver`) marker. SDK-specific wrapper detectors\n\
                      // do not apply, and decompiled function bodies are a heuristic\n\
                      // best-effort reconstruction. Treat all output below as\n\
                      // approximate; do not rely on it for security-sensitive review\n\
                      // without independent verification against the binary.\n\
                      // ============================================================\n\n";
        source = format!("{}{}", header, source);
    } else if validation.has_warnings() {
        let mut header = String::from("// SOROBAN COMPLIANCE WARNINGS:\n");
        for diag in &validation.diagnostics {
            header.push_str(&format!("// - {}\n", diag));
        }
        header.push_str("//\n\n");
        header.push_str(&source);
        source = header;
    }

    log::info!(
        "Decompilation complete ({} bytes of Rust source)",
        source.len()
    );

    let standard_interfaces = contract_module.standard_interfaces.clone();

    Ok(DecompileIR {
        contract_module,
        registry,
        validation,
        source,
        sdk_version,
        standard_interfaces,
    })
}

/// Build a lookup index keyed by `function_name` so the four hint passes can
/// share an O(1) per-function lookup instead of doing four linear scans.
fn build_hints_index(hints: &DecompileHints) -> HashMap<&str, Vec<&FunctionHints>> {
    let mut idx: HashMap<&str, Vec<&FunctionHints>> = HashMap::new();
    for fh in &hints.functions {
        idx.entry(fh.function_name.as_str()).or_default().push(fh);
    }
    idx
}

fn unique_storage_hint_key_for_function(function_hints: &[&FunctionHints]) -> Option<SorobanExpr> {
    let mut unique_key = None;

    for function_hints in function_hints {
        for storage_hint in &function_hints.storage {
            let key = hint_value_to_soroban_expr(&storage_hint.key)?;

            match &unique_key {
                None => unique_key = Some(key),
                Some(existing) if existing == &key => {}
                Some(_) => return None,
            }
        }
    }

    unique_key
}

#[derive(Debug, Clone, PartialEq)]
struct EventRepairHint {
    topics: Vec<SorobanExpr>,
    data: Vec<SorobanExpr>,
}

fn unique_event_hint_for_function(function_hints: &[&FunctionHints]) -> Option<EventRepairHint> {
    let mut unique_event = None;

    for function_hints in function_hints {
        for event_hint in &function_hints.events {
            let event = EventRepairHint {
                topics: event_hint
                    .topics
                    .iter()
                    .map(hint_value_to_soroban_expr)
                    .collect::<Option<Vec<_>>>()?,
                data: event_hint
                    .data
                    .iter()
                    .map(hint_value_to_soroban_expr)
                    .collect::<Option<Vec<_>>>()?,
            };

            match &unique_event {
                None => unique_event = Some(event),
                Some(existing) if existing == &event => {}
                Some(_) => return None,
            }
        }
    }

    unique_event
}

fn unique_invoke_hint_function_for_function(
    function_hints: &[&FunctionHints],
) -> Option<SorobanExpr> {
    let mut unique_function = None;

    for function_hints in function_hints {
        for invoke_hint in &function_hints.invokes {
            let Some(function) = &invoke_hint.function else {
                continue;
            };
            let function = invoke_function_hint_to_soroban_expr(function)?;

            match &unique_function {
                None => unique_function = Some(function),
                Some(existing) if existing == &function => {}
                Some(_) => return None,
            }
        }
    }

    unique_function
}

fn invoke_function_hint_to_soroban_expr(value: &HintValue) -> Option<SorobanExpr> {
    match value {
        HintValue::Symbol(value) => Some(SorobanExpr::SymbolLiteral(value.clone())),
        HintValue::String(value) => Some(SorobanExpr::StringLiteral(value.clone())),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq)]
struct AuthRepairHint {
    address: Option<SorobanExpr>,
    args: SorobanExpr,
}

fn unique_auth_hint_for_function(function_hints: &[&FunctionHints]) -> Option<AuthRepairHint> {
    let mut unique_auth = None;

    for function_hints in function_hints {
        for auth_hint in &function_hints.auth {
            let address = match &auth_hint.address {
                Some(address) => Some(hint_value_to_soroban_expr(address)?),
                None => None,
            };
            let args = auth_hint
                .args
                .iter()
                .map(hint_value_to_soroban_expr)
                .collect::<Option<Vec<_>>>()?;
            let auth = AuthRepairHint {
                address,
                args: SorobanExpr::VecConstruct(args),
            };

            match &unique_auth {
                None => unique_auth = Some(auth),
                Some(existing) if existing == &auth => {}
                Some(_) => return None,
            }
        }
    }

    unique_auth
}

fn hint_value_to_soroban_expr(value: &HintValue) -> Option<SorobanExpr> {
    match value {
        HintValue::Bool(value) => Some(SorobanExpr::BoolLiteral(*value)),
        HintValue::U32(value) => Some(SorobanExpr::U32Literal(*value)),
        HintValue::I32(value) => Some(SorobanExpr::I32Literal(*value)),
        HintValue::U64(value) => Some(SorobanExpr::U64Literal(*value)),
        HintValue::I64(value) => Some(SorobanExpr::I64Literal(*value)),
        HintValue::Symbol(value) => Some(SorobanExpr::SymbolLiteral(value.clone())),
        HintValue::Void => Some(SorobanExpr::Void),
        HintValue::U128(value) => Some(SorobanExpr::U128Literal(*value)),
        HintValue::I128(value) => Some(SorobanExpr::I128Literal(*value)),
        HintValue::String(value) => Some(SorobanExpr::StringLiteral(value.clone())),
        HintValue::Bytes(value) => Some(SorobanExpr::BytesLiteral(value.clone())),
    }
}

fn repair_unknown_invoke_functions_from_hint(stmts: &mut [SorobanStmt], function: &SorobanExpr) {
    for stmt in stmts {
        repair_unknown_invoke_functions_in_stmt(stmt, function);
    }
}

fn repair_unknown_invoke_functions_in_stmt(stmt: &mut SorobanStmt, function: &SorobanExpr) {
    match stmt {
        SorobanStmt::Expr(expr) | SorobanStmt::Return(Some(expr)) => {
            repair_unknown_invoke_functions_in_expr(expr, function);
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            repair_unknown_invoke_functions_in_expr(value, function);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            repair_unknown_invoke_functions_in_expr(condition, function);
            repair_unknown_invoke_functions_from_hint(then_body, function);
            repair_unknown_invoke_functions_from_hint(else_body, function);
        }
        SorobanStmt::Match { scrutinee, arms } => {
            repair_unknown_invoke_functions_in_expr(scrutinee, function);
            for arm in arms {
                repair_unknown_invoke_functions_from_hint(&mut arm.body, function);
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) | SorobanStmt::For { body, .. } => {
            repair_unknown_invoke_functions_from_hint(body, function);
        }
        SorobanStmt::Return(None)
        | SorobanStmt::Comment(_)
        | SorobanStmt::Break
        | SorobanStmt::Continue => {}
    }
}

fn repair_unknown_invoke_functions_in_expr(expr: &mut SorobanExpr, replacement: &SorobanExpr) {
    match expr {
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
            repair_unknown_invoke_functions_in_expr(address, replacement);
            repair_unknown_invoke_function(function, replacement);
            for arg in args {
                repair_unknown_invoke_functions_in_expr(arg, replacement);
            }
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => {
            repair_unknown_invoke_functions_in_expr(key, replacement);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            repair_unknown_invoke_functions_in_expr(key, replacement);
            repair_unknown_invoke_functions_in_expr(value, replacement);
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            repair_unknown_invoke_functions_in_expr(key, replacement);
            repair_unknown_invoke_functions_in_expr(threshold, replacement);
            repair_unknown_invoke_functions_in_expr(extend_to, replacement);
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
        | SorobanExpr::Or(a, b) => {
            repair_unknown_invoke_functions_in_expr(a, replacement);
            repair_unknown_invoke_functions_in_expr(b, replacement);
        }
        SorobanExpr::Not(inner)
        | SorobanExpr::RequireAuth(inner)
        | SorobanExpr::AuthorizeAsCurrContract(inner)
        | SorobanExpr::ErrorFromCode(inner)
        | SorobanExpr::PanicWithError(inner)
        | SorobanExpr::CryptoSha256(inner)
        | SorobanExpr::CryptoKeccak256(inner)
        | SorobanExpr::PrngReseed(inner)
        | SorobanExpr::PrngBytesNew(inner)
        | SorobanExpr::PrngVecShuffle(inner)
        | SorobanExpr::StrkeyToAddress(inner)
        | SorobanExpr::AddressToStrkey(inner)
        | SorobanExpr::FieldAccess { object: inner, .. }
        | SorobanExpr::ValConvert { value: inner, .. }
        | SorobanExpr::CastAs { value: inner, .. }
        | SorobanExpr::Try(inner)
        | SorobanExpr::ValTag(inner)
        | SorobanExpr::Some(inner)
        | SorobanExpr::SretResult(inner) => {
            repair_unknown_invoke_functions_in_expr(inner, replacement);
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            repair_unknown_invoke_functions_in_expr(threshold, replacement);
            repair_unknown_invoke_functions_in_expr(extend_to, replacement);
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            repair_unknown_invoke_functions_in_expr(address, replacement);
            repair_unknown_invoke_functions_in_expr(args, replacement);
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for topic in topics {
                repair_unknown_invoke_functions_in_expr(topic, replacement);
            }
            repair_unknown_invoke_functions_in_expr(data, replacement);
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, value) in fields {
                repair_unknown_invoke_functions_in_expr(value, replacement);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. }
        | SorobanExpr::TupleConstruct(fields)
        | SorobanExpr::VecConstruct(fields)
        | SorobanExpr::Log(fields) => {
            for value in fields {
                repair_unknown_invoke_functions_in_expr(value, replacement);
            }
        }
        SorobanExpr::MapConstruct(entries) => {
            for (entry_key, value) in entries {
                repair_unknown_invoke_functions_in_expr(entry_key, replacement);
                repair_unknown_invoke_functions_in_expr(value, replacement);
            }
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            repair_unknown_invoke_functions_in_expr(object, replacement);
            for arg in args {
                repair_unknown_invoke_functions_in_expr(arg, replacement);
            }
        }
        SorobanExpr::VecTryIterFold { vec, init } => {
            repair_unknown_invoke_functions_in_expr(vec, replacement);
            repair_unknown_invoke_functions_in_expr(init, replacement);
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            repair_unknown_invoke_functions_in_expr(public_key, replacement);
            repair_unknown_invoke_functions_in_expr(message, replacement);
            repair_unknown_invoke_functions_in_expr(signature, replacement);
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            repair_unknown_invoke_functions_in_expr(msg_digest, replacement);
            repair_unknown_invoke_functions_in_expr(signature, replacement);
            repair_unknown_invoke_functions_in_expr(recovery_id, replacement);
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            repair_unknown_invoke_functions_in_expr(low, replacement);
            repair_unknown_invoke_functions_in_expr(high, replacement);
        }
        SorobanExpr::RawHostCall { args, .. } => {
            for arg in args {
                repair_unknown_invoke_functions_in_expr(arg, replacement);
            }
        }
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
        | SorobanExpr::ValTagName(_)
        | SorobanExpr::UnknownVal
        | SorobanExpr::CyclicSlot { .. } => {}
    }
}

fn repair_unknown_invoke_function(function: &mut Box<SorobanExpr>, replacement: &SorobanExpr) {
    if is_repairable_dynamic_invoke_function(function) {
        **function = replacement.clone();
    } else {
        repair_unknown_invoke_functions_in_expr(function, replacement);
    }
}

fn is_repairable_dynamic_invoke_function(expr: &SorobanExpr) -> bool {
    matches!(expr, SorobanExpr::UnknownVal | SorobanExpr::Local(_))
        || matches!(expr, SorobanExpr::NamedLocal(name) if name.starts_with("var_"))
        || is_linear_memory_object_key(expr)
}

fn repair_unknown_storage_keys_from_hint(stmts: &mut [SorobanStmt], key: &SorobanExpr) {
    for stmt in stmts {
        repair_unknown_storage_keys_in_stmt(stmt, key);
    }
}

fn repair_unknown_event_values_from_hint(stmts: &mut [SorobanStmt], hint: &EventRepairHint) {
    for stmt in stmts {
        repair_unknown_event_values_in_stmt(stmt, hint);
    }
}

fn repair_unknown_event_values_in_stmt(stmt: &mut SorobanStmt, hint: &EventRepairHint) {
    match stmt {
        SorobanStmt::Expr(expr) | SorobanStmt::Return(Some(expr)) => {
            repair_unknown_event_values_in_expr(expr, hint);
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            repair_unknown_event_values_in_expr(value, hint);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            repair_unknown_event_values_in_expr(condition, hint);
            repair_unknown_event_values_from_hint(then_body, hint);
            repair_unknown_event_values_from_hint(else_body, hint);
        }
        SorobanStmt::Match { scrutinee, arms } => {
            repair_unknown_event_values_in_expr(scrutinee, hint);
            for arm in arms {
                repair_unknown_event_values_from_hint(&mut arm.body, hint);
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) | SorobanStmt::For { body, .. } => {
            repair_unknown_event_values_from_hint(body, hint);
        }
        SorobanStmt::Return(None)
        | SorobanStmt::Comment(_)
        | SorobanStmt::Break
        | SorobanStmt::Continue => {}
    }
}

fn repair_unknown_event_values_in_expr(expr: &mut SorobanExpr, hint: &EventRepairHint) {
    match expr {
        SorobanExpr::PublishEvent { topics, data, .. } => {
            if topics.len() == hint.topics.len() {
                for (topic, replacement) in topics.iter_mut().zip(&hint.topics) {
                    repair_unknown_event_value(topic, replacement);
                }
            }
            repair_unknown_event_data(data, &hint.data);
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => {
            repair_unknown_event_values_in_expr(key, hint);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            repair_unknown_event_values_in_expr(key, hint);
            repair_unknown_event_values_in_expr(value, hint);
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            repair_unknown_event_values_in_expr(key, hint);
            repair_unknown_event_values_in_expr(threshold, hint);
            repair_unknown_event_values_in_expr(extend_to, hint);
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
        | SorobanExpr::Or(a, b) => {
            repair_unknown_event_values_in_expr(a, hint);
            repair_unknown_event_values_in_expr(b, hint);
        }
        SorobanExpr::Not(inner)
        | SorobanExpr::RequireAuth(inner)
        | SorobanExpr::AuthorizeAsCurrContract(inner)
        | SorobanExpr::ErrorFromCode(inner)
        | SorobanExpr::PanicWithError(inner)
        | SorobanExpr::CryptoSha256(inner)
        | SorobanExpr::CryptoKeccak256(inner)
        | SorobanExpr::PrngReseed(inner)
        | SorobanExpr::PrngBytesNew(inner)
        | SorobanExpr::PrngVecShuffle(inner)
        | SorobanExpr::StrkeyToAddress(inner)
        | SorobanExpr::AddressToStrkey(inner)
        | SorobanExpr::FieldAccess { object: inner, .. }
        | SorobanExpr::ValConvert { value: inner, .. }
        | SorobanExpr::CastAs { value: inner, .. }
        | SorobanExpr::Try(inner)
        | SorobanExpr::ValTag(inner)
        | SorobanExpr::Some(inner)
        | SorobanExpr::SretResult(inner) => {
            repair_unknown_event_values_in_expr(inner, hint);
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            repair_unknown_event_values_in_expr(threshold, hint);
            repair_unknown_event_values_in_expr(extend_to, hint);
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            repair_unknown_event_values_in_expr(address, hint);
            repair_unknown_event_values_in_expr(args, hint);
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
            repair_unknown_event_values_in_expr(address, hint);
            repair_unknown_event_values_in_expr(function, hint);
            for arg in args {
                repair_unknown_event_values_in_expr(arg, hint);
            }
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, value) in fields {
                repair_unknown_event_values_in_expr(value, hint);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. }
        | SorobanExpr::TupleConstruct(fields)
        | SorobanExpr::VecConstruct(fields)
        | SorobanExpr::Log(fields) => {
            for value in fields {
                repair_unknown_event_values_in_expr(value, hint);
            }
        }
        SorobanExpr::MapConstruct(entries) => {
            for (entry_key, value) in entries {
                repair_unknown_event_values_in_expr(entry_key, hint);
                repair_unknown_event_values_in_expr(value, hint);
            }
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            repair_unknown_event_values_in_expr(object, hint);
            for arg in args {
                repair_unknown_event_values_in_expr(arg, hint);
            }
        }
        SorobanExpr::VecTryIterFold { vec, init } => {
            repair_unknown_event_values_in_expr(vec, hint);
            repair_unknown_event_values_in_expr(init, hint);
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            repair_unknown_event_values_in_expr(public_key, hint);
            repair_unknown_event_values_in_expr(message, hint);
            repair_unknown_event_values_in_expr(signature, hint);
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            repair_unknown_event_values_in_expr(msg_digest, hint);
            repair_unknown_event_values_in_expr(signature, hint);
            repair_unknown_event_values_in_expr(recovery_id, hint);
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            repair_unknown_event_values_in_expr(low, hint);
            repair_unknown_event_values_in_expr(high, hint);
        }
        SorobanExpr::RawHostCall { args, .. } => {
            for arg in args {
                repair_unknown_event_values_in_expr(arg, hint);
            }
        }
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
        | SorobanExpr::ValTagName(_)
        | SorobanExpr::UnknownVal
        | SorobanExpr::CyclicSlot { .. } => {}
    }
}

fn repair_unknown_event_data(data: &mut SorobanExpr, replacements: &[SorobanExpr]) {
    if is_repairable_dynamic_event_value(data) {
        *data = event_data_replacement_expr(replacements);
        return;
    }

    match data {
        SorobanExpr::TupleConstruct(fields) | SorobanExpr::VecConstruct(fields)
            if fields.len() == replacements.len() =>
        {
            for (field, replacement) in fields.iter_mut().zip(replacements) {
                repair_unknown_event_value(field, replacement);
            }
        }
        _ => {}
    }
}

fn event_data_replacement_expr(replacements: &[SorobanExpr]) -> SorobanExpr {
    match replacements {
        [] => SorobanExpr::Void,
        [replacement] => replacement.clone(),
        replacements => SorobanExpr::TupleConstruct(replacements.to_vec()),
    }
}

fn repair_unknown_event_value(expr: &mut SorobanExpr, replacement: &SorobanExpr) {
    if is_repairable_dynamic_event_value(expr) {
        *expr = replacement.clone();
    }
}

fn repair_weak_auth_from_hint(stmts: &mut [SorobanStmt], hint: &AuthRepairHint) {
    for stmt in stmts {
        repair_weak_auth_in_stmt(stmt, hint);
    }
}

fn repair_weak_auth_in_stmt(stmt: &mut SorobanStmt, hint: &AuthRepairHint) {
    match stmt {
        SorobanStmt::Expr(expr) | SorobanStmt::Return(Some(expr)) => {
            repair_weak_auth_in_expr(expr, hint);
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            repair_weak_auth_in_expr(value, hint);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            repair_weak_auth_in_expr(condition, hint);
            repair_weak_auth_from_hint(then_body, hint);
            repair_weak_auth_from_hint(else_body, hint);
        }
        SorobanStmt::Match { scrutinee, arms } => {
            repair_weak_auth_in_expr(scrutinee, hint);
            for arm in arms {
                repair_weak_auth_from_hint(&mut arm.body, hint);
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) | SorobanStmt::For { body, .. } => {
            repair_weak_auth_from_hint(body, hint);
        }
        SorobanStmt::Return(None)
        | SorobanStmt::Comment(_)
        | SorobanStmt::Break
        | SorobanStmt::Continue => {}
    }
}

fn repair_weak_auth_in_expr(expr: &mut SorobanExpr, hint: &AuthRepairHint) {
    match expr {
        SorobanExpr::RequireAuth(inner) => {
            if let Some(address) = &hint.address {
                repair_weak_auth_operand(inner, address);
            }
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            if let Some(replacement) = &hint.address {
                repair_weak_auth_operand(address, replacement);
            }
            repair_weak_auth_operand(args, &hint.args);
        }
        SorobanExpr::AuthorizeAsCurrContract(args) => {
            if hint.address.is_none() {
                repair_weak_auth_operand(args, &hint.args);
            }
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            repair_weak_auth_in_expr(key, hint);
            repair_weak_auth_in_expr(value, hint);
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => repair_weak_auth_in_expr(key, hint),
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            repair_weak_auth_in_expr(key, hint);
            repair_weak_auth_in_expr(threshold, hint);
            repair_weak_auth_in_expr(extend_to, hint);
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            repair_weak_auth_in_expr(threshold, hint);
            repair_weak_auth_in_expr(extend_to, hint);
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
        | SorobanExpr::Or(a, b) => {
            repair_weak_auth_in_expr(a, hint);
            repair_weak_auth_in_expr(b, hint);
        }
        SorobanExpr::Not(inner)
        | SorobanExpr::ErrorFromCode(inner)
        | SorobanExpr::PanicWithError(inner)
        | SorobanExpr::CryptoSha256(inner)
        | SorobanExpr::CryptoKeccak256(inner)
        | SorobanExpr::PrngReseed(inner)
        | SorobanExpr::PrngBytesNew(inner)
        | SorobanExpr::PrngVecShuffle(inner)
        | SorobanExpr::StrkeyToAddress(inner)
        | SorobanExpr::AddressToStrkey(inner)
        | SorobanExpr::FieldAccess { object: inner, .. }
        | SorobanExpr::ValConvert { value: inner, .. }
        | SorobanExpr::CastAs { value: inner, .. }
        | SorobanExpr::Try(inner)
        | SorobanExpr::ValTag(inner)
        | SorobanExpr::Some(inner)
        | SorobanExpr::SretResult(inner) => repair_weak_auth_in_expr(inner, hint),
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for topic in topics {
                repair_weak_auth_in_expr(topic, hint);
            }
            repair_weak_auth_in_expr(data, hint);
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
            repair_weak_auth_in_expr(address, hint);
            repair_weak_auth_in_expr(function, hint);
            for arg in args {
                repair_weak_auth_in_expr(arg, hint);
            }
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, value) in fields {
                repair_weak_auth_in_expr(value, hint);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. }
        | SorobanExpr::TupleConstruct(fields)
        | SorobanExpr::VecConstruct(fields)
        | SorobanExpr::Log(fields) => {
            for value in fields {
                repair_weak_auth_in_expr(value, hint);
            }
        }
        SorobanExpr::MapConstruct(entries) => {
            for (entry_key, value) in entries {
                repair_weak_auth_in_expr(entry_key, hint);
                repair_weak_auth_in_expr(value, hint);
            }
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            repair_weak_auth_in_expr(object, hint);
            for arg in args {
                repair_weak_auth_in_expr(arg, hint);
            }
        }
        SorobanExpr::VecTryIterFold { vec, init } => {
            repair_weak_auth_in_expr(vec, hint);
            repair_weak_auth_in_expr(init, hint);
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            repair_weak_auth_in_expr(public_key, hint);
            repair_weak_auth_in_expr(message, hint);
            repair_weak_auth_in_expr(signature, hint);
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            repair_weak_auth_in_expr(msg_digest, hint);
            repair_weak_auth_in_expr(signature, hint);
            repair_weak_auth_in_expr(recovery_id, hint);
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            repair_weak_auth_in_expr(low, hint);
            repair_weak_auth_in_expr(high, hint);
        }
        SorobanExpr::RawHostCall { args, .. } => {
            for arg in args {
                repair_weak_auth_in_expr(arg, hint);
            }
        }
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
        | SorobanExpr::ValTagName(_)
        | SorobanExpr::UnknownVal
        | SorobanExpr::CyclicSlot { .. } => {}
    }
}

fn repair_weak_auth_operand(target: &mut Box<SorobanExpr>, replacement: &SorobanExpr) {
    if is_weak_auth_operand(target) {
        **target = replacement.clone();
    }
}

fn is_weak_auth_operand(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::UnknownVal | SorobanExpr::Local(_) => true,
        SorobanExpr::NamedLocal(name) => name.starts_with("var_"),
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            is_weak_auth_operand(value)
        }
        SorobanExpr::VecConstruct(values) => {
            !values.is_empty() && values.iter().all(is_weak_auth_operand)
        }
        SorobanExpr::MethodCall { object, method, .. }
            if matches!(
                method.as_str(),
                "push_back" | "push_front" | "insert" | "append"
            ) =>
        {
            is_weak_auth_operand(object)
        }
        _ => false,
    }
}

fn repair_unknown_storage_keys_in_stmt(stmt: &mut SorobanStmt, key: &SorobanExpr) {
    match stmt {
        SorobanStmt::Expr(expr) | SorobanStmt::Return(Some(expr)) => {
            repair_unknown_storage_keys_in_expr(expr, key);
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            repair_unknown_storage_keys_in_expr(value, key);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            repair_unknown_storage_keys_in_expr(condition, key);
            repair_unknown_storage_keys_from_hint(then_body, key);
            repair_unknown_storage_keys_from_hint(else_body, key);
        }
        SorobanStmt::Match { scrutinee, arms } => {
            repair_unknown_storage_keys_in_expr(scrutinee, key);
            for arm in arms {
                repair_unknown_storage_keys_from_hint(&mut arm.body, key);
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) | SorobanStmt::For { body, .. } => {
            repair_unknown_storage_keys_from_hint(body, key);
        }
        SorobanStmt::Return(None)
        | SorobanStmt::Comment(_)
        | SorobanStmt::Break
        | SorobanStmt::Continue => {}
    }
}

fn repair_unknown_storage_keys_in_expr(expr: &mut SorobanExpr, replacement: &SorobanExpr) {
    match expr {
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => {
            repair_unknown_storage_key(key, replacement);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            repair_unknown_storage_key(key, replacement);
            repair_unknown_storage_keys_in_expr(value, replacement);
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            repair_unknown_storage_key(key, replacement);
            repair_unknown_storage_keys_in_expr(threshold, replacement);
            repair_unknown_storage_keys_in_expr(extend_to, replacement);
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
        | SorobanExpr::Or(a, b) => {
            repair_unknown_storage_keys_in_expr(a, replacement);
            repair_unknown_storage_keys_in_expr(b, replacement);
        }
        SorobanExpr::Not(inner)
        | SorobanExpr::RequireAuth(inner)
        | SorobanExpr::AuthorizeAsCurrContract(inner)
        | SorobanExpr::ErrorFromCode(inner)
        | SorobanExpr::PanicWithError(inner)
        | SorobanExpr::CryptoSha256(inner)
        | SorobanExpr::CryptoKeccak256(inner)
        | SorobanExpr::PrngReseed(inner)
        | SorobanExpr::PrngBytesNew(inner)
        | SorobanExpr::PrngVecShuffle(inner)
        | SorobanExpr::StrkeyToAddress(inner)
        | SorobanExpr::AddressToStrkey(inner)
        | SorobanExpr::FieldAccess { object: inner, .. }
        | SorobanExpr::ValConvert { value: inner, .. }
        | SorobanExpr::CastAs { value: inner, .. }
        | SorobanExpr::Try(inner)
        | SorobanExpr::ValTag(inner)
        | SorobanExpr::Some(inner)
        | SorobanExpr::SretResult(inner) => {
            repair_unknown_storage_keys_in_expr(inner, replacement);
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            repair_unknown_storage_keys_in_expr(threshold, replacement);
            repair_unknown_storage_keys_in_expr(extend_to, replacement);
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            repair_unknown_storage_keys_in_expr(address, replacement);
            repair_unknown_storage_keys_in_expr(args, replacement);
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for topic in topics {
                repair_unknown_storage_keys_in_expr(topic, replacement);
            }
            repair_unknown_storage_keys_in_expr(data, replacement);
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
            repair_unknown_storage_keys_in_expr(address, replacement);
            repair_unknown_storage_keys_in_expr(function, replacement);
            for arg in args {
                repair_unknown_storage_keys_in_expr(arg, replacement);
            }
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, value) in fields {
                repair_unknown_storage_keys_in_expr(value, replacement);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. }
        | SorobanExpr::TupleConstruct(fields)
        | SorobanExpr::VecConstruct(fields)
        | SorobanExpr::Log(fields) => {
            for value in fields {
                repair_unknown_storage_keys_in_expr(value, replacement);
            }
        }
        SorobanExpr::MapConstruct(entries) => {
            for (entry_key, value) in entries {
                repair_unknown_storage_keys_in_expr(entry_key, replacement);
                repair_unknown_storage_keys_in_expr(value, replacement);
            }
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            repair_unknown_storage_keys_in_expr(object, replacement);
            for arg in args {
                repair_unknown_storage_keys_in_expr(arg, replacement);
            }
        }
        SorobanExpr::VecTryIterFold { vec, init } => {
            repair_unknown_storage_keys_in_expr(vec, replacement);
            repair_unknown_storage_keys_in_expr(init, replacement);
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            repair_unknown_storage_keys_in_expr(public_key, replacement);
            repair_unknown_storage_keys_in_expr(message, replacement);
            repair_unknown_storage_keys_in_expr(signature, replacement);
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            repair_unknown_storage_keys_in_expr(msg_digest, replacement);
            repair_unknown_storage_keys_in_expr(signature, replacement);
            repair_unknown_storage_keys_in_expr(recovery_id, replacement);
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            repair_unknown_storage_keys_in_expr(low, replacement);
            repair_unknown_storage_keys_in_expr(high, replacement);
        }
        SorobanExpr::RawHostCall { args, .. } => {
            for arg in args {
                repair_unknown_storage_keys_in_expr(arg, replacement);
            }
        }
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
        | SorobanExpr::ValTagName(_)
        | SorobanExpr::UnknownVal
        | SorobanExpr::CyclicSlot { .. } => {}
    }
}

fn repair_unknown_storage_key(key: &mut Box<SorobanExpr>, replacement: &SorobanExpr) {
    if is_repairable_dynamic_storage_key(key) {
        **key = replacement.clone();
    } else {
        repair_unknown_storage_keys_in_expr(key, replacement);
    }
}

fn is_repairable_dynamic_storage_key(expr: &SorobanExpr) -> bool {
    matches!(expr, SorobanExpr::UnknownVal) || is_linear_memory_object_key(expr)
}

fn is_repairable_dynamic_event_value(expr: &SorobanExpr) -> bool {
    matches!(expr, SorobanExpr::UnknownVal) || is_linear_memory_object_key(expr)
}

fn is_linear_memory_object_key(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::RawHostCall {
            module, function, ..
        } => {
            module == "Buf"
                && matches!(
                    function.as_str(),
                    "symbol_new_from_linear_memory" | "string_new_from_linear_memory"
                )
        }
        SorobanExpr::MethodCall { object, method, .. } => {
            matches!(
                method.as_str(),
                "symbol_new_from_linear_memory" | "string_new_from_linear_memory"
            ) && is_env_buf_call(object)
        }
        _ => false,
    }
}

fn is_env_buf_call(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } if method == "buf" && args.is_empty() && matches!(object.as_ref(), SorobanExpr::Env)
    )
}

/// Recursively convert `StorageGet { unwrap: true }` to `StorageGet { unwrap: false }`
/// in all expressions within the statement tree.
fn remove_storage_unwrap(stmts: &mut [SorobanStmt]) {
    for stmt in stmts.iter_mut() {
        remove_storage_unwrap_stmt(stmt);
    }
}

fn remove_storage_unwrap_stmt(stmt: &mut SorobanStmt) {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => remove_storage_unwrap_expr(e),
        SorobanStmt::Let { value, .. } => remove_storage_unwrap_expr(value),
        SorobanStmt::Assign { value, .. } => remove_storage_unwrap_expr(value),
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            remove_storage_unwrap(then_body);
            remove_storage_unwrap(else_body);
        }
        SorobanStmt::Match { arms, .. } => {
            for arm in arms {
                remove_storage_unwrap(&mut arm.body);
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => remove_storage_unwrap(body),
        _ => {}
    }
}

fn remove_storage_unwrap_expr(expr: &mut SorobanExpr) {
    if let SorobanExpr::StorageGet { unwrap, .. } = expr {
        *unwrap = false;
    }
}

/// Check if an expression is an identity-passthrough pattern on the given param:
/// - `param.get(0)` (single element)
/// - `TupleConstruct([param.get(0), param.get(1), ...])` (all sequential gets)
///
/// Elements may be wrapped in `ValConvert` layers.
fn is_identity_get_pattern(expr: &SorobanExpr, param_name: &str) -> bool {
    match expr {
        // Direct: param.get(0)
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } => {
            method == "get"
                && args.len() == 1
                && matches!(
                    &args[0],
                    SorobanExpr::U32Literal(0) | SorobanExpr::I32Literal(0)
                )
                && matches!(object.as_ref(), SorobanExpr::Param(n) if n == param_name)
        }
        // Tuple/Vec: (param.get(0), param.get(1), ...) or vec![param.get(0), ...]
        SorobanExpr::TupleConstruct(elems) | SorobanExpr::VecConstruct(elems) => {
            !elems.is_empty()
                && elems
                    .iter()
                    .enumerate()
                    .all(|(i, elem)| is_param_get_index(elem, param_name, i as u32))
        }
        _ => false,
    }
}

/// Check if an expression is `StructConstruct { f1: param.f1, f2: param.f2, ... }`
/// where all fields are just read from the same parameter — a struct validate-and-return.
fn is_identity_struct_reconstruct(expr: &SorobanExpr, param_name: &str) -> bool {
    if let SorobanExpr::StructConstruct { fields, .. } = expr {
        !fields.is_empty()
            && fields
                .iter()
                .all(|(_, value)| is_field_access_on_param(value, param_name))
    } else {
        false
    }
}

/// Check if an expression is `param.field_name`, possibly wrapped in ValConvert layers.
fn is_field_access_on_param(expr: &SorobanExpr, param_name: &str) -> bool {
    match expr {
        SorobanExpr::FieldAccess { object, .. } => {
            matches!(object.as_ref(), SorobanExpr::Param(n) if n == param_name)
        }
        SorobanExpr::ValConvert { value, .. } => is_field_access_on_param(value, param_name),
        _ => false,
    }
}

/// Check if an expression is `param.get(idx)`, possibly wrapped in ValConvert layers.
fn is_param_get_index(expr: &SorobanExpr, param_name: &str, idx: u32) -> bool {
    match expr {
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } => {
            method == "get"
                && args.len() == 1
                && matches!(&args[0], SorobanExpr::U32Literal(v) if *v == idx)
                && matches!(object.as_ref(), SorobanExpr::Param(n) if n == param_name)
        }
        SorobanExpr::ValConvert { value, .. } => is_param_get_index(value, param_name, idx),
        _ => false,
    }
}

/// Check if the expression is a bool literal and the return type is Bool.
/// The WASM `select` handler defaults to val1 for unknown conditions, which causes
/// bool validation wrappers to always resolve to `BoolLiteral(true)` instead of
/// preserving the parameter. Since `find_identity_passthrough_param` already verified
/// a param of matching type exists, this is a validate-and-return artifact.
fn is_identity_bool_literal(expr: &SorobanExpr, ret_ty: &stellar_xdr::curr::ScSpecTypeDef) -> bool {
    matches!(
        (expr, ret_ty),
        (
            SorobanExpr::BoolLiteral(_),
            stellar_xdr::curr::ScSpecTypeDef::Bool
        )
    )
}

/// Detect a data-carrying-enum identity round-trip — `fn f(v: E) -> E { v }` where
/// `E` is a `#[contracttype]` enum with data-carrying variants.
///
/// The SDK lowers such a function to: decode `v` (Val-tag guard, `len`, `get(0)`
/// discriminant), then a `match v { … }` whose arms each merely re-encode the *same*
/// variant they matched (e.g. arm `VarB` reads `v.get(1)` and rebuilds `VarB`). The
/// lifter recovers this as a `Match` over `Param(v)` with degenerate per-variant arm
/// skeletons; the optimizer then strips the no-effect arms, leaving an empty body that
/// codegen renders as `todo!("decompiled function body")` (see codegen/module.rs). The
/// unit-enum / struct / scalar round-trips already collapse via the existing identity
/// passes; only the data-carrying-enum match shape slips through.
///
/// This recognizes the round-trip (before optimization, where the match is still
/// present) and lets the caller collapse it to the faithful `Return(Param(v))`.
///
/// Gated tightly so it cannot fire on a real enum-*transforming* function: the body
/// must be nothing but decode preamble plus one `match` over `v`, every statement and
/// arm body must be side-effect-free and read only `v` (no storage/event/invoke/auth,
/// no other parameter), and each arm may only re-encode its *own* variant (a foreign
/// `SymbolLiteral`/`EnumConstruct` — i.e. a permutation/transform — disqualifies it).
fn is_enum_identity_roundtrip(body: &[SorobanStmt], param: &str) -> bool {
    let mut arms_seen: Option<&[MatchArm]> = None;
    for stmt in body {
        match stmt {
            SorobanStmt::Match { scrutinee, arms } => {
                if arms_seen.is_some() {
                    return false; // more than one match → not a simple round-trip
                }
                if !matches!(scrutinee, SorobanExpr::Param(p) if p == param) {
                    return false; // dispatch must be on the passthrough param
                }
                arms_seen = Some(arms);
            }
            other if enum_roundtrip_stmt_is_benign(other, param, None) => {}
            _ => return false,
        }
    }
    let Some(arms) = arms_seen else {
        return false; // no match → handled by the other identity passes
    };
    !arms.is_empty()
        && arms.iter().all(|arm| match &arm.pattern {
            // An enum-variant arm may re-encode only its own variant.
            MatchPattern::EnumVariant { variant, .. } => arm
                .body
                .iter()
                .all(|s| enum_roundtrip_stmt_is_benign(s, param, Some(variant))),
            // A catch-all arm must be benign with no variant re-encode at all.
            MatchPattern::Wildcard => arm
                .body
                .iter()
                .all(|s| enum_roundtrip_stmt_is_benign(s, param, None)),
            // A literal-dispatch match is an integer switch, not an enum round-trip.
            MatchPattern::Literal(_) => false,
        })
}

/// A statement is "benign" for [`is_enum_identity_roundtrip`] if it only decodes/reads
/// the passthrough param `v` and re-encodes the allowed `variant` (if any) — no writes,
/// no host side effects. `variant == Some(v)` permits `SymbolLiteral(v)`/`EnumConstruct`
/// of variant `v` only; `None` permits no variant re-encode.
fn enum_roundtrip_stmt_is_benign(stmt: &SorobanStmt, param: &str, variant: Option<&str>) -> bool {
    match stmt {
        // A validation guard: `if <read-only cond> { panic } ` with no else.
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            enum_roundtrip_expr_is_readonly(condition, param, variant)
                && else_body.is_empty()
                && then_body.iter().all(|t| {
                    matches!(
                        t,
                        SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_))
                    )
                })
        }
        SorobanStmt::Let { value, .. } => enum_roundtrip_expr_is_readonly(value, param, variant),
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
            enum_roundtrip_expr_is_readonly(e, param, variant)
        }
        SorobanStmt::Return(None) | SorobanStmt::Break | SorobanStmt::Continue => true,
        SorobanStmt::Comment(_) => true,
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => body
            .iter()
            .all(|s| enum_roundtrip_stmt_is_benign(s, param, variant)),
        // Assign (write), nested Match, and For are not part of a pure round-trip.
        _ => false,
    }
}

/// An expression is "read-only" for the enum round-trip if it is built only from
/// literals, reads of the passthrough param `v`, Val-tag inspection, and (when
/// `variant` is `Some`) a re-encode of *that* variant. Any storage/event/invoke/auth/
/// crypto op, any other parameter, or any foreign variant symbol returns false.
fn enum_roundtrip_expr_is_readonly(expr: &SorobanExpr, param: &str, variant: Option<&str>) -> bool {
    use SorobanExpr::*;
    // Free-function calls coerce `&Box<SorobanExpr>` → `&SorobanExpr` at the arg position.
    let recs = |es: &[SorobanExpr]| {
        es.iter()
            .all(|e| enum_roundtrip_expr_is_readonly(e, param, variant))
    };
    match expr {
        U32Literal(_) | I32Literal(_) | U64Literal(_) | I64Literal(_) | U128Literal(_)
        | I128Literal(_) | BoolLiteral(_) | StringLiteral(_) | BytesLiteral(_) | Void | None
        | Env | ValTagName(_) => true,
        Param(p) => p == param,
        SymbolLiteral(s) => variant == Option::Some(s.as_str()),
        Some(inner) | Not(inner) | ValTag(inner) => {
            enum_roundtrip_expr_is_readonly(inner, param, variant)
        }
        Add(a, b)
        | Sub(a, b)
        | Mul(a, b)
        | Div(a, b)
        | Rem(a, b)
        | Eq(a, b)
        | Ne(a, b)
        | Lt(a, b)
        | Le(a, b)
        | Gt(a, b)
        | Ge(a, b)
        | And(a, b)
        | Or(a, b) => {
            enum_roundtrip_expr_is_readonly(a, param, variant)
                && enum_roundtrip_expr_is_readonly(b, param, variant)
        }
        ValConvert { value, .. } | FieldAccess { object: value, .. } => {
            enum_roundtrip_expr_is_readonly(value, param, variant)
        }
        MethodCall {
            object,
            method,
            args,
        } => {
            matches!(
                method.as_str(),
                "get" | "len" | "first_unchecked" | "first" | "last" | "is_empty"
            ) && enum_roundtrip_expr_is_readonly(object, param, variant)
                && recs(args)
        }
        EnumConstruct {
            variant: v, fields, ..
        } => variant == Option::Some(v.as_str()) && recs(fields),
        TupleConstruct(es) | VecConstruct(es) => recs(es),
        // Everything else (storage/event/invoke/auth/crypto/struct-construct/…) has an
        // effect or escapes the param — not a pure read-only round-trip.
        _ => false,
    }
}

/// Run wasm-opt (binaryen) on the WASM binary via the system `wasm-opt` command.
///
/// Uses `-O2` optimization level with passes that simplify patterns for the lifter:
/// coalesce-locals, simplify-locals, dce, precompute, reorder-locals.
fn run_wasm_opt(wasm: &[u8]) -> Result<Vec<u8>, DecompileError> {
    use std::io::Write;
    use std::process::Command;

    let temp_dir = WasmOptTempDir::new()?;
    let input_path = temp_dir.path().join("input.wasm");
    let output_path = temp_dir.path().join("output.wasm");

    std::fs::File::create(&input_path)
        .and_then(|mut f| f.write_all(wasm))
        .map_err(|e| DecompileError::PreOptimize(format!("wasm-opt temp file: {e}")))?;

    let result = Command::new("wasm-opt")
        .arg("-O2")
        .arg("--enable-bulk-memory")
        .arg("--enable-sign-ext")
        .arg("--enable-mutable-globals")
        .arg("--enable-multivalue")
        .arg("--coalesce-locals")
        .arg("--simplify-locals")
        .arg("--dce")
        .arg("--precompute")
        .arg("--reorder-locals")
        .arg(&input_path)
        .arg("-o")
        .arg(&output_path)
        .output();

    match result {
        Ok(output) if output.status.success() => {
            let optimized = std::fs::read(&output_path).map_err(|e| {
                DecompileError::PreOptimize(format!("reading wasm-opt output: {e}"))
            })?;
            Ok(optimized)
        }
        Ok(output) => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            Err(DecompileError::PreOptimize(format!(
                "wasm-opt failed: {stderr}"
            )))
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Err(DecompileError::PreOptimize(
            "wasm-opt not found. Install binaryen: https://github.com/WebAssembly/binaryen"
                .to_string(),
        )),
        Err(e) => Err(DecompileError::PreOptimize(format!(
            "wasm-opt execution error: {e}"
        ))),
    }
}

struct WasmOptTempDir {
    path: std::path::PathBuf,
}

impl WasmOptTempDir {
    fn new() -> Result<Self, DecompileError> {
        let path = unique_wasm_opt_temp_dir_path();
        std::fs::create_dir(&path)
            .map_err(|e| DecompileError::PreOptimize(format!("wasm-opt temp dir: {e}")))?;
        Ok(Self { path })
    }

    fn path(&self) -> &std::path::Path {
        &self.path
    }
}

impl Drop for WasmOptTempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

fn unique_wasm_opt_temp_dir_path() -> std::path::PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};

    static COUNTER: AtomicU64 = AtomicU64::new(0);

    let pid = std::process::id();
    let seq = COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or_default();

    std::env::temp_dir().join(format!("stellar_decompile_wasm_opt_{pid}_{nanos}_{seq}"))
}

/// Convert a ScSpecTypeDef to a Rust type string for invoke_contract type parameters.
/// Returns None for types that can't be cleanly rendered as a string.
pub(crate) fn spec_type_to_string(spec: &stellar_xdr::curr::ScSpecTypeDef) -> Option<String> {
    use stellar_xdr::curr::ScSpecTypeDef;
    match spec {
        ScSpecTypeDef::U32 => Some("u32".into()),
        ScSpecTypeDef::I32 => Some("i32".into()),
        ScSpecTypeDef::U64 => Some("u64".into()),
        ScSpecTypeDef::I64 => Some("i64".into()),
        ScSpecTypeDef::U128 => Some("u128".into()),
        ScSpecTypeDef::I128 => Some("i128".into()),
        ScSpecTypeDef::Bool => Some("bool".into()),
        ScSpecTypeDef::Void => Some("()".into()),
        ScSpecTypeDef::Symbol => Some("Symbol".into()),
        ScSpecTypeDef::Address => Some("Address".into()),
        ScSpecTypeDef::MuxedAddress => Some("MuxedAddress".into()),
        ScSpecTypeDef::Bytes => Some("Bytes".into()),
        ScSpecTypeDef::String => Some("String".into()),
        ScSpecTypeDef::U256 => Some("U256".into()),
        ScSpecTypeDef::I256 => Some("I256".into()),
        ScSpecTypeDef::Timepoint => Some("Timepoint".into()),
        ScSpecTypeDef::Duration => Some("Duration".into()),
        ScSpecTypeDef::BytesN(b) => Some(format!("BytesN<{}>", b.n)),
        ScSpecTypeDef::Vec(v) => {
            let el = spec_type_to_string(&v.element_type)?;
            Some(format!("Vec<{el}>"))
        }
        ScSpecTypeDef::Map(m) => {
            let k = spec_type_to_string(&m.key_type)?;
            let v = spec_type_to_string(&m.value_type)?;
            Some(format!("Map<{k}, {v}>"))
        }
        ScSpecTypeDef::Option(o) => {
            let inner = spec_type_to_string(&o.value_type)?;
            Some(format!("Option<{inner}>"))
        }
        ScSpecTypeDef::Tuple(t) => {
            let elems: Option<Vec<String>> =
                t.value_types.iter().map(spec_type_to_string).collect();
            let elems = elems?;
            if elems.len() == 1 {
                Some(format!("({},)", elems[0]))
            } else {
                Some(format!("({})", elems.join(", ")))
            }
        }
        ScSpecTypeDef::Udt(u) => Some(u.name.to_string()),
        _ => None,
    }
}

/// Set the return_type on InvokeContract/TryInvokeContract expressions in tail position.
/// Walks the statement tree, only processing the last statement in each body.
/// Wrap a tail `Vec`/`Map` `.get(i)` (which yields `Option<T>`) in `.unwrap()` so a
/// function declared to return the element type `T` type-checks. Mirrors the tail
/// traversal of [`set_invoke_return_type_in_tail`]. The `.get` may be wrapped by a
/// (lifter-artifact) `ValConvert`/`SretResult`, which codegen renders transparently,
/// so wrapping the outer expression is sufficient.
fn wrap_tail_vec_get_unwrap(stmts: &mut [SorobanStmt]) {
    let Some(last) = stmts.last_mut() else {
        return;
    };
    match last {
        SorobanStmt::Expr(expr) | SorobanStmt::Return(Some(expr))
            if expr_is_or_wraps_vec_get(expr) =>
        {
            let inner = std::mem::replace(expr, SorobanExpr::Void);
            *expr = SorobanExpr::MethodCall {
                object: Box::new(inner),
                method: "unwrap".to_string(),
                args: vec![],
            };
        }
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            wrap_tail_vec_get_unwrap(then_body);
            wrap_tail_vec_get_unwrap(else_body);
        }
        SorobanStmt::Match { arms, .. } => {
            for arm in arms {
                wrap_tail_vec_get_unwrap(&mut arm.body);
            }
        }
        SorobanStmt::Block(body) => wrap_tail_vec_get_unwrap(body),
        _ => {}
    }
}

/// True if `expr` is a `Vec`/`Map` `.get(...)` call, possibly behind a transparent
/// `ValConvert`/`SretResult` wrapper. (`StorageGet` is a distinct variant, not a
/// `MethodCall`, so it is unaffected.)
fn expr_is_or_wraps_vec_get(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::MethodCall { method, .. } => method == "get",
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::SretResult(value) => {
            expr_is_or_wraps_vec_get(value)
        }
        _ => false,
    }
}

/// Stage 4b3b (issue #14, udt::add): drop a leaked tuple-scalar term from the
/// tail return of a fold-bearing function. `recover_vec_iter_fold` places UdtD's
/// `tup.0 + fold` inside the match arm, but wasm-opt also hoisted a copy of that
/// scalar and added it in the post-match composition, so the optimized return is
/// `Add(Add(<scrutinee>.field, a), b)` (renders `a.a + a + b`). Strip the leading
/// `<scrutinee param>.field` so the return is the faithful `a + b`.
///
/// Tightly gated: fires only when the body has a fold-bearing match arm and the
/// leaked term is a `FieldAccess` on a *fold-match scrutinee param* — so it never
/// touches a legitimate `param.field + …` in any other function.
fn strip_leaked_fold_scalar(body: &mut [SorobanStmt]) {
    let scrutinees = fold_match_scrutinee_params(body);
    if scrutinees.is_empty() {
        return;
    }
    let Some(last) = body.last_mut() else {
        return;
    };
    let expr = match last {
        SorobanStmt::Return(Some(e)) | SorobanStmt::Expr(e) => e,
        _ => return,
    };
    // Descend through transparent codegen wrappers to the composition `Add`.
    let mut cur = expr;
    while let SorobanExpr::ValConvert { value, .. } | SorobanExpr::SretResult(value) = cur {
        cur = value;
    }
    strip_leftmost_scrutinee_field(cur, &scrutinees);
}

/// Remove the leftmost leaf of a left-associated `Add` chain when it is a
/// `FieldAccess` on one of `scrutinees`. `((leak + x) + y)` → `(x + y)`.
fn strip_leftmost_scrutinee_field(expr: &mut SorobanExpr, scrutinees: &[String]) -> bool {
    if let SorobanExpr::Add(l, r) = expr {
        if is_scrutinee_field(l, scrutinees) {
            let rhs = std::mem::replace(r.as_mut(), SorobanExpr::Void);
            *expr = rhs;
            return true;
        }
        return strip_leftmost_scrutinee_field(l, scrutinees);
    }
    false
}

/// `expr` is `<param>.<field>` where `<param>` is one of `scrutinees`.
fn is_scrutinee_field(expr: &SorobanExpr, scrutinees: &[String]) -> bool {
    matches!(
        expr,
        SorobanExpr::FieldAccess { object, .. }
            if matches!(object.as_ref(), SorobanExpr::Param(p) if scrutinees.contains(p))
    )
}

/// Param names that are the scrutinee of a `Match` containing a `VecTryIterFold`
/// arm (i.e. a fold that `recover_vec_iter_fold` synthesized).
fn fold_match_scrutinee_params(stmts: &[SorobanStmt]) -> Vec<String> {
    let mut out = Vec::new();
    collect_fold_scrutinees(stmts, &mut out);
    out
}

fn collect_fold_scrutinees(stmts: &[SorobanStmt], out: &mut Vec<String>) {
    for s in stmts {
        match s {
            SorobanStmt::Match { scrutinee, arms } => {
                if let SorobanExpr::Param(p) = scrutinee
                    && arms
                        .iter()
                        .any(|a| a.body.iter().any(stmt_contains_vec_fold))
                {
                    out.push(p.clone());
                }
                for a in arms {
                    collect_fold_scrutinees(&a.body, out);
                }
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_fold_scrutinees(then_body, out);
                collect_fold_scrutinees(else_body, out);
            }
            SorobanStmt::Loop { body }
            | SorobanStmt::For { body, .. }
            | SorobanStmt::Block(body) => collect_fold_scrutinees(body, out),
            _ => {}
        }
    }
}

fn stmt_contains_vec_fold(s: &SorobanStmt) -> bool {
    match s {
        SorobanStmt::Assign { value, .. }
        | SorobanStmt::Expr(value)
        | SorobanStmt::Let { value, .. } => expr_contains_vec_fold(value),
        SorobanStmt::Return(Some(e)) => expr_contains_vec_fold(e),
        _ => false,
    }
}

fn expr_contains_vec_fold(e: &SorobanExpr) -> bool {
    match e {
        SorobanExpr::VecTryIterFold { .. } => true,
        SorobanExpr::Add(a, b) => expr_contains_vec_fold(a) || expr_contains_vec_fold(b),
        SorobanExpr::FieldAccess { object, .. } => expr_contains_vec_fold(object),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Stage 4b4: recover misrouted crypto struct-field arguments (issue #19, bls)
//
// Root cause: a single WASM local is reused for two distinct host-call results —
// a struct field (e.g. `proof.fp2`, a `BytesN<96>`) and the BLS scalar-field
// modulus (a 32-byte `u256_val_from_be_bytes(bytes_new_from_linear_memory(addr,32))`
// used to reduce the `Bls12381Fr` field). The lifter binds both to `var_N`, so the
// optimizer's dead-store removal + single-use inlining drops the field binding and
// inlines the modulus into the crypto call — `map_fp2_to_g2(<modulus>)` — which
// renders the non-existent `env.buf()` and fails to compile.
//
// A full fix is SSA-versioning of reused locals (deep, high-regression-risk). This
// is a narrow, registry-aware heuristic instead: it only fires for a known
// single-argument bls12_381 `map_*` host method whose argument is (or wraps) a raw
// `bytes_new_from_linear_memory` read, and rewrites it to the struct-param field
// uniquely identified by the method's expected byte width and the fact that the
// field is never otherwise referenced in the body. When the field is ambiguous it
// leaves the call unchanged rather than guess.

/// Expected input byte-width of the single-argument bls12_381 `map_*` host
/// functions whose struct-field argument a reused-local alias can misroute.
/// Returns `None` for methods this pass does not touch.
fn bls_map_input_size(method: &str) -> Option<u32> {
    match method {
        "map_fp_to_g1" => Some(48),  // Bls12381Fp  = BytesN<48>
        "map_fp2_to_g2" => Some(96), // Bls12381Fp2 = BytesN<96>
        _ => None,
    }
}

/// True if `expr` is (or transparently wraps) a raw `bytes_new_from_linear_memory`
/// read — the signature of the misrouted BLS modulus that displaced a struct field.
fn is_linear_mem_read(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::RawHostCall { function, .. } => function == "bytes_new_from_linear_memory",
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            is_linear_mem_read(value)
        }
        _ => false,
    }
}

/// Byte width of a crypto-aliasable struct field type (`BytesN<n>` or `U256`).
fn crypto_field_width(ty: &ScSpecTypeDef) -> Option<u32> {
    match ty {
        ScSpecTypeDef::BytesN(b) => Some(b.n),
        ScSpecTypeDef::U256 => Some(32),
        _ => None,
    }
}

/// Immutable sub-expressions of a `SorobanExpr` for the compound variants that can
/// carry a crypto-call argument or a field reference. Mirrors
/// `optimizer::expr_children`; variants without relevant sub-expressions yield none.
fn child_exprs(expr: &SorobanExpr) -> Vec<&SorobanExpr> {
    match expr {
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
        | SorobanExpr::Or(a, b) => vec![a.as_ref(), b.as_ref()],
        SorobanExpr::Not(a) | SorobanExpr::PanicWithError(a) | SorobanExpr::RequireAuth(a) => {
            vec![a.as_ref()]
        }
        SorobanExpr::ValConvert { value, .. }
        | SorobanExpr::CastAs { value, .. }
        | SorobanExpr::SretResult(value) => vec![value.as_ref()],
        SorobanExpr::MethodCall { object, args, .. } => {
            let mut c = vec![object.as_ref()];
            c.extend(args.iter());
            c
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => vec![key.as_ref()],
        SorobanExpr::StorageSet { key, value, .. } => vec![key.as_ref(), value.as_ref()],
        SorobanExpr::FieldAccess { object, .. } => vec![object.as_ref()],
        SorobanExpr::TupleConstruct(fields) | SorobanExpr::VecConstruct(fields) => {
            fields.iter().collect()
        }
        SorobanExpr::StructConstruct { fields, .. } => fields.iter().map(|(_, v)| v).collect(),
        SorobanExpr::RawHostCall { args, .. } => args.iter().collect(),
        _ => vec![],
    }
}

/// Mutable counterpart of [`child_exprs`].
fn child_exprs_mut(expr: &mut SorobanExpr) -> Vec<&mut SorobanExpr> {
    match expr {
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
        | SorobanExpr::Or(a, b) => vec![a.as_mut(), b.as_mut()],
        SorobanExpr::Not(a) | SorobanExpr::PanicWithError(a) | SorobanExpr::RequireAuth(a) => {
            vec![a.as_mut()]
        }
        SorobanExpr::ValConvert { value, .. }
        | SorobanExpr::CastAs { value, .. }
        | SorobanExpr::SretResult(value) => vec![value.as_mut()],
        SorobanExpr::MethodCall { object, args, .. } => {
            let mut c = vec![object.as_mut()];
            c.extend(args.iter_mut());
            c
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => vec![key.as_mut()],
        SorobanExpr::StorageSet { key, value, .. } => vec![key.as_mut(), value.as_mut()],
        SorobanExpr::FieldAccess { object, .. } => vec![object.as_mut()],
        SorobanExpr::TupleConstruct(fields) | SorobanExpr::VecConstruct(fields) => {
            fields.iter_mut().collect()
        }
        SorobanExpr::StructConstruct { fields, .. } => fields.iter_mut().map(|(_, v)| v).collect(),
        SorobanExpr::RawHostCall { args, .. } => args.iter_mut().collect(),
        _ => vec![],
    }
}

/// Visit every `SorobanExpr` node (recursively) in a statement list.
fn walk_exprs(stmts: &[SorobanStmt], f: &mut dyn FnMut(&SorobanExpr)) {
    fn visit(e: &SorobanExpr, f: &mut dyn FnMut(&SorobanExpr)) {
        f(e);
        for c in child_exprs(e) {
            visit(c, f);
        }
    }
    for s in stmts {
        match s {
            SorobanStmt::Expr(e)
            | SorobanStmt::Return(Some(e))
            | SorobanStmt::Let { value: e, .. }
            | SorobanStmt::Assign { value: e, .. } => visit(e, f),
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                visit(condition, f);
                walk_exprs(then_body, f);
                walk_exprs(else_body, f);
            }
            SorobanStmt::Match { scrutinee, arms } => {
                visit(scrutinee, f);
                for a in arms {
                    walk_exprs(&a.body, f);
                }
            }
            SorobanStmt::For {
                start, end, body, ..
            } => {
                visit(start, f);
                visit(end, f);
                walk_exprs(body, f);
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => walk_exprs(body, f),
            _ => {}
        }
    }
}

/// Rewrite a misrouted crypto argument inside one expression tree, consuming a
/// matching entry from `unconsumed` so a field is never reused across calls.
fn rewrite_crypto_args_expr(
    expr: &mut SorobanExpr,
    param: &str,
    unconsumed: &mut Vec<(String, u32)>,
) {
    for child in child_exprs_mut(expr) {
        rewrite_crypto_args_expr(child, param, unconsumed);
    }
    if let SorobanExpr::MethodCall { method, args, .. } = expr
        && let Some(size) = bls_map_input_size(method)
    {
        for arg in args.iter_mut() {
            if !is_linear_mem_read(arg) {
                continue;
            }
            let matching: Vec<usize> = unconsumed
                .iter()
                .enumerate()
                .filter(|(_, (_, w))| *w == size)
                .map(|(i, _)| i)
                .collect();
            if matching.len() == 1 {
                let (field, _) = unconsumed.remove(matching[0]);
                *arg = SorobanExpr::FieldAccess {
                    object: Box::new(SorobanExpr::Param(param.to_string())),
                    field,
                };
            }
        }
    }
}

/// Recurse [`rewrite_crypto_args_expr`] through a statement list.
fn rewrite_crypto_args_stmts(
    stmts: &mut [SorobanStmt],
    param: &str,
    unconsumed: &mut Vec<(String, u32)>,
) {
    for s in stmts {
        match s {
            SorobanStmt::Expr(e)
            | SorobanStmt::Return(Some(e))
            | SorobanStmt::Let { value: e, .. }
            | SorobanStmt::Assign { value: e, .. } => {
                rewrite_crypto_args_expr(e, param, unconsumed)
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                rewrite_crypto_args_expr(condition, param, unconsumed);
                rewrite_crypto_args_stmts(then_body, param, unconsumed);
                rewrite_crypto_args_stmts(else_body, param, unconsumed);
            }
            SorobanStmt::Match { scrutinee, arms } => {
                rewrite_crypto_args_expr(scrutinee, param, unconsumed);
                for a in arms {
                    rewrite_crypto_args_stmts(&mut a.body, param, unconsumed);
                }
            }
            SorobanStmt::For {
                start, end, body, ..
            } => {
                rewrite_crypto_args_expr(start, param, unconsumed);
                rewrite_crypto_args_expr(end, param, unconsumed);
                rewrite_crypto_args_stmts(body, param, unconsumed);
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                rewrite_crypto_args_stmts(body, param, unconsumed)
            }
            _ => {}
        }
    }
}

/// See the Stage 4b4 comment at the call site. Rewrites a misrouted
/// `bytes_new_from_linear_memory` argument of a bls12_381 `map_*` call back to the
/// struct-param field it should have referenced.
fn recover_crypto_field_args(
    body: &mut [SorobanStmt],
    params: &[FnParam],
    registry: &TypeRegistry,
) {
    // Find the unique struct parameter that has crypto-aliasable fields. Bail on
    // zero or more than one — the heuristic only disambiguates within one struct.
    let mut struct_param: Option<(String, Vec<(String, u32)>)> = None;
    for p in params {
        let ScSpecTypeDef::Udt(udt) = &p.type_def else {
            continue;
        };
        let Ok(tname) = udt.name.to_utf8_string() else {
            continue;
        };
        let Some(spec) = registry.get_struct(&tname) else {
            continue;
        };
        let fields: Vec<(String, u32)> = spec
            .fields
            .iter()
            .filter_map(|f| Some((f.name.to_utf8_string().ok()?, crypto_field_width(&f.type_)?)))
            .collect();
        if fields.is_empty() {
            continue;
        }
        if struct_param.is_some() {
            return; // ambiguous: more than one crypto struct param
        }
        struct_param = Some((p.name.clone(), fields));
    }
    let Some((param_name, crypto_fields)) = struct_param else {
        return;
    };

    // Fast exit unless a misrouted crypto argument is actually present.
    let mut has_misrouted = false;
    walk_exprs(body, &mut |e| {
        if let SorobanExpr::MethodCall { method, args, .. } = e
            && bls_map_input_size(method).is_some()
            && args.iter().any(is_linear_mem_read)
        {
            has_misrouted = true;
        }
    });
    if !has_misrouted {
        return;
    }

    // Crypto fields already referenced as `param.field` are not candidates.
    let mut consumed: std::collections::HashSet<String> = std::collections::HashSet::new();
    walk_exprs(body, &mut |e| {
        if let SorobanExpr::FieldAccess { object, field } = e
            && matches!(object.as_ref(), SorobanExpr::Param(p) if *p == param_name)
        {
            consumed.insert(field.clone());
        }
    });
    let mut unconsumed: Vec<(String, u32)> = crypto_fields
        .into_iter()
        .filter(|(n, _)| !consumed.contains(n))
        .collect();

    rewrite_crypto_args_stmts(body, &param_name, &mut unconsumed);
}

// ---------------------------------------------------------------------------
// Stage 4b5: bind data-carrying match-arm payloads (Fix D1)
// ---------------------------------------------------------------------------

/// Rewrite every `<scrutinee>.get(1)` payload read in `expr` to `NamedLocal(binding)`.
fn rebind_payload_get_expr(
    expr: &mut SorobanExpr,
    scrutinee: &SorobanExpr,
    binding: &str,
    changed: &mut bool,
) {
    if matches!(expr,
        SorobanExpr::MethodCall { object, method, args }
            if method == "get"
                && args.len() == 1
                && matches!(&args[0], SorobanExpr::U32Literal(1))
                && object.as_ref() == scrutinee)
    {
        *expr = SorobanExpr::NamedLocal(binding.to_string());
        *changed = true;
        return;
    }
    for child in child_exprs_mut(expr) {
        rebind_payload_get_expr(child, scrutinee, binding, changed);
    }
}

/// Recurse [`rebind_payload_get_expr`] through a statement list.
fn rebind_payload_get_stmts(
    stmts: &mut [SorobanStmt],
    scrutinee: &SorobanExpr,
    binding: &str,
    changed: &mut bool,
) {
    for s in stmts {
        match s {
            SorobanStmt::Expr(e)
            | SorobanStmt::Return(Some(e))
            | SorobanStmt::Let { value: e, .. }
            | SorobanStmt::Assign { value: e, .. } => {
                rebind_payload_get_expr(e, scrutinee, binding, changed)
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                rebind_payload_get_expr(condition, scrutinee, binding, changed);
                rebind_payload_get_stmts(then_body, scrutinee, binding, changed);
                rebind_payload_get_stmts(else_body, scrutinee, binding, changed);
            }
            SorobanStmt::Match {
                scrutinee: sc,
                arms,
            } => {
                rebind_payload_get_expr(sc, scrutinee, binding, changed);
                for a in arms {
                    rebind_payload_get_stmts(&mut a.body, scrutinee, binding, changed);
                }
            }
            SorobanStmt::For {
                start, end, body, ..
            } => {
                rebind_payload_get_expr(start, scrutinee, binding, changed);
                rebind_payload_get_expr(end, scrutinee, binding, changed);
                rebind_payload_get_stmts(body, scrutinee, binding, changed);
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                rebind_payload_get_stmts(body, scrutinee, binding, changed)
            }
            _ => {}
        }
    }
}

/// Walk every `Match` in `stmts`; for each data-carrying enum-variant arm (lifter marks
/// these with a single `_` binding) whose body still reads the payload via
/// `<scrutinee>.get(1)`, name the binding `v0` and rewrite those reads to it. Arms whose
/// payload is unused keep `_`. Recurses into nested control flow.
fn recover_enum_payload_bindings(stmts: &mut [SorobanStmt]) {
    for s in stmts {
        match s {
            SorobanStmt::Match { scrutinee, arms } => {
                let scrut = scrutinee.clone();
                for arm in arms.iter_mut() {
                    // Handle nested matches (with their own scrutinees) first.
                    recover_enum_payload_bindings(&mut arm.body);
                    if let MatchPattern::EnumVariant { bindings, .. } = &mut arm.pattern
                        && bindings.len() == 1
                        && bindings[0] == "_"
                    {
                        let name = "v0".to_string();
                        let mut changed = false;
                        rebind_payload_get_stmts(&mut arm.body, &scrut, &name, &mut changed);
                        if changed {
                            bindings[0] = name;
                        }
                    }
                }
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                recover_enum_payload_bindings(then_body);
                recover_enum_payload_bindings(else_body);
            }
            SorobanStmt::For { body, .. }
            | SorobanStmt::Loop { body }
            | SorobanStmt::Block(body) => recover_enum_payload_bindings(body),
            _ => {}
        }
    }
}

/// True when an expression already constructs a `Result`/`Option` value (`Ok`/`Err`/
/// `Some`/`None` or an error), so codegen's tail `Ok(..)` wrap must NOT be applied again.
fn expr_is_result_or_option_value(e: &SorobanExpr) -> bool {
    match e {
        SorobanExpr::None => true,
        SorobanExpr::ContractError { .. } | SorobanExpr::ErrorFromCode(_) => true,
        SorobanExpr::EnumConstruct { variant, .. } => {
            matches!(variant.as_str(), "Ok" | "Err" | "Some" | "None")
        }
        _ => false,
    }
}

/// Recover a `Result<Option<T>, E>`-returning enum dispatch (Fix D, issue #14, udt
/// `recursive_enum`).
///
/// After lifting + Fix D1, the match and the data-carrying arm's payload binding are
/// present, but three defects remain: (a) data-less arm(s) were dropped by arm-retain, so
/// the match is non-exhaustive; (b) the surviving arm's body is a bare tail `Expr`, and
/// codegen only `Ok(..)`-wraps `Return` values, so the wrap never fires; and (c) a
/// `Map::get` was lowered to a `contains_key` probe (a `bool`, not the `Option` the return
/// type needs). For a tail `match scrut { .. }` over a known union in a `Result<Option<_>,
/// _>` function, this re-emits the arms in declared order: every declared variant missing
/// from the match is restored as `=> Ok(None)` (only when it is data-less — we cannot
/// synthesize a data-carrying body), a tail `contains_key` is rewritten to `get`, and each
/// arm's tail `Expr(e)` becomes `Return(Some(e))` so codegen renders `Ok(e)`. Bails (no
/// edit) unless every arm is a single tail `Expr` and every missing variant is data-less.
fn recover_result_option_enum_match(
    body: &mut [SorobanStmt],
    return_type: &Option<ScSpecTypeDef>,
    registry: &TypeRegistry,
) {
    // Gate: function returns `Result<Option<_>, _>`.
    let Some(ScSpecTypeDef::Result(r)) = return_type else {
        return;
    };
    if !matches!(*r.ok_type, ScSpecTypeDef::Option(_)) {
        return;
    }
    // Operate on a tail `Match` over a known union.
    let Some(SorobanStmt::Match { arms, .. }) = body.last_mut() else {
        return;
    };
    let Some(union_name) = arms.iter().find_map(|a| match &a.pattern {
        MatchPattern::EnumVariant { type_name, .. } => Some(type_name.clone()),
        _ => None,
    }) else {
        return;
    };
    let Some(union) = registry.get_union(&union_name) else {
        return;
    };

    // Declared variant order: (name, has_data).
    use stellar_xdr::curr::ScSpecUdtUnionCaseV0;
    let declared: Vec<(String, bool)> = union
        .cases
        .iter()
        .filter_map(|case| match case {
            ScSpecUdtUnionCaseV0::VoidV0(v) => v.name.to_utf8_string().ok().map(|n| (n, false)),
            ScSpecUdtUnionCaseV0::TupleV0(t) => t.name.to_utf8_string().ok().map(|n| (n, true)),
        })
        .collect();
    if declared.is_empty() {
        return;
    }

    // Bail unless every existing arm is a single tail `Expr` we can normalize.
    if !arms
        .iter()
        .all(|a| matches!(a.body.as_slice(), [SorobanStmt::Expr(_)]))
    {
        return;
    }
    // Bail if any missing variant is data-carrying — we can only synthesize `Ok(None)`.
    let covered: std::collections::HashSet<&str> = arms
        .iter()
        .filter_map(|a| match &a.pattern {
            MatchPattern::EnumVariant { variant, .. } => Some(variant.as_str()),
            _ => None,
        })
        .collect();
    if declared
        .iter()
        .any(|(name, has_data)| *has_data && !covered.contains(name.as_str()))
    {
        return;
    }

    // Re-emit arms in declared order.
    let mut rebuilt: Vec<MatchArm> = Vec::with_capacity(declared.len());
    for (variant, _has_data) in &declared {
        if let Some(existing) = arms.iter().find(
            |a| matches!(&a.pattern, MatchPattern::EnumVariant { variant: v, .. } if v == variant),
        ) {
            let body = match existing.body.first() {
                Some(SorobanStmt::Expr(e)) if !expr_is_result_or_option_value(e) => {
                    let mut e = e.clone();
                    if let SorobanExpr::MethodCall { method, .. } = &mut e
                        && method == "contains_key"
                    {
                        *method = "get".to_string();
                    }
                    vec![SorobanStmt::Return(Some(e))]
                }
                _ => existing.body.clone(),
            };
            rebuilt.push(MatchArm {
                pattern: existing.pattern.clone(),
                body,
            });
        } else {
            // Missing data-less variant → `=> Ok(None)`.
            rebuilt.push(MatchArm {
                pattern: MatchPattern::EnumVariant {
                    type_name: union_name.clone(),
                    variant: variant.clone(),
                    bindings: Vec::new(),
                },
                body: vec![SorobanStmt::Return(Some(SorobanExpr::None))],
            });
        }
    }
    *arms = rebuilt;
}

fn set_invoke_return_type_in_tail(
    stmts: &mut [SorobanStmt],
    type_str: &str,
    spec: &stellar_xdr::curr::ScSpecTypeDef,
) {
    let Some(last) = stmts.last_mut() else {
        return;
    };
    match last {
        SorobanStmt::Expr(expr) | SorobanStmt::Return(Some(expr)) => {
            set_invoke_return_type_in_expr(expr, type_str, spec);
        }
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            set_invoke_return_type_in_tail(then_body, type_str, spec);
            set_invoke_return_type_in_tail(else_body, type_str, spec);
        }
        SorobanStmt::Match { arms, .. } => {
            for arm in arms {
                set_invoke_return_type_in_tail(&mut arm.body, type_str, spec);
            }
        }
        SorobanStmt::Block(body) => {
            set_invoke_return_type_in_tail(body, type_str, spec);
        }
        _ => {}
    }
}

/// Set the return_type on a single InvokeContract/TryInvokeContract expression.
fn set_invoke_return_type_in_expr(
    expr: &mut SorobanExpr,
    type_str: &str,
    spec: &stellar_xdr::curr::ScSpecTypeDef,
) {
    match expr {
        // invoke_contract::<T> returns T, so use the function's return type directly
        SorobanExpr::InvokeContract { return_type, .. }
            if !matches!(spec, stellar_xdr::curr::ScSpecTypeDef::Result(_)) =>
        {
            *return_type = Some(type_str.to_string());
        }
        // try_invoke_contract::<T> returns Result<T, _>, so extract the ok type
        SorobanExpr::TryInvokeContract { return_type, .. } => {
            if let stellar_xdr::curr::ScSpecTypeDef::Result(r) = spec
                && let Some(ok_str) = spec_type_to_string(&r.ok_type)
            {
                *return_type = Some(ok_str);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Stage 4f: Resolve Local(N) → Param(name) for unbound param locals
// ---------------------------------------------------------------------------

use crate::ir::high_level_ir::FnParam;

/// Replace `Local(N)` with `Param(param_name)` when N corresponds to a function
/// parameter slot and the local is never re-bound by a Let or Assign in the
/// function body.
fn resolve_param_locals(body: &mut [SorobanStmt], params: &[FnParam], param_local_base: u32) {
    if params.is_empty() {
        return;
    }

    // Build mapping: WASM local index → param name
    // Soroban wrappers often reserve local 0 for env; generic WASM does not.
    let mut index_to_name: std::collections::HashMap<u32, &str> = std::collections::HashMap::new();
    for (i, param) in params.iter().enumerate() {
        index_to_name.insert(param_local_base + i as u32, &param.name);
    }

    // Collect all locals that are re-bound (Let or Assign with target "var_N")
    let mut rebound: std::collections::HashSet<u32> = std::collections::HashSet::new();
    collect_rebound_locals(body, &mut rebound);

    // Remove rebound locals from the replacement set
    index_to_name.retain(|idx, _| !rebound.contains(idx));

    if index_to_name.is_empty() {
        return;
    }

    // Walk the tree and replace Local(N) → Param(name)
    for stmt in body.iter_mut() {
        replace_local_with_param_in_stmt(stmt, &index_to_name);
    }
}

fn infer_param_local_base(
    body: &[SorobanStmt],
    params: &[FnParam],
    preferred_base: u32,
    takes_env: bool,
) -> u32 {
    if params.is_empty() {
        return preferred_base;
    }

    let mut rebound = std::collections::HashSet::new();
    collect_rebound_locals(body, &mut rebound);

    let mut candidate_bases = vec![preferred_base];
    if preferred_base <= 1 {
        candidate_bases.push(0);
        if takes_env {
            candidate_bases.push(1);
        }
    }
    candidate_bases.sort_unstable();
    candidate_bases.dedup();

    let preferred_score = score_param_local_base(body, params.len(), preferred_base, &rebound);
    let mut best_base = preferred_base;
    let mut best_score = preferred_score;

    for base in candidate_bases {
        let score = score_param_local_base(body, params.len(), base, &rebound);
        if score.is_better_than(
            &best_score,
            base,
            best_base,
            params.len(),
            preferred_base,
            takes_env,
        ) {
            best_base = base;
            best_score = score;
        }
    }

    best_base
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct ParamBaseScore {
    total_hits: usize,
    distinct_slots: std::collections::BTreeSet<u32>,
}

impl ParamBaseScore {
    fn prefix_len(&self, param_local_base: u32) -> usize {
        let mut len = 0;
        while self
            .distinct_slots
            .contains(&(param_local_base + len as u32))
        {
            len += 1;
        }
        len
    }

    fn is_better_than(
        &self,
        other: &Self,
        self_base: u32,
        other_base: u32,
        param_count: usize,
        preferred_base: u32,
        takes_env: bool,
    ) -> bool {
        if takes_env && preferred_base == 0 && self_base != preferred_base {
            return false;
        }

        let self_prefix = self.prefix_len(self_base);
        let other_prefix = other.prefix_len(other_base);
        let min_override_prefix =
            if takes_env && preferred_base == 1 && self_base == 0 && other_base == preferred_base {
                2
            } else {
                param_count.min(2)
            };

        if self_prefix < min_override_prefix {
            return false;
        }

        self_prefix > other_prefix
            || (self_prefix == other_prefix
                && self.total_hits > other.total_hits
                && self_prefix > 0)
    }
}

fn score_param_local_base(
    stmts: &[SorobanStmt],
    param_count: usize,
    param_local_base: u32,
    rebound: &std::collections::HashSet<u32>,
) -> ParamBaseScore {
    let mut score = ParamBaseScore {
        total_hits: 0,
        distinct_slots: std::collections::BTreeSet::new(),
    };
    for stmt in stmts {
        score.merge(score_param_local_base_in_stmt(
            stmt,
            param_count,
            param_local_base,
            rebound,
        ));
    }
    score
}

impl ParamBaseScore {
    fn merge(&mut self, other: Self) {
        self.total_hits += other.total_hits;
        self.distinct_slots.extend(other.distinct_slots);
    }
}

fn score_param_local_base_in_stmt(
    stmt: &SorobanStmt,
    param_count: usize,
    param_local_base: u32,
    rebound: &std::collections::HashSet<u32>,
) -> ParamBaseScore {
    match stmt {
        SorobanStmt::Expr(expr) | SorobanStmt::Return(Some(expr)) => {
            score_param_local_base_in_expr(expr, param_count, param_local_base, rebound)
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            score_param_local_base_in_expr(value, param_count, param_local_base, rebound)
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            let mut score =
                score_param_local_base_in_expr(condition, param_count, param_local_base, rebound);
            score.merge(score_param_local_base(
                then_body,
                param_count,
                param_local_base,
                rebound,
            ));
            score.merge(score_param_local_base(
                else_body,
                param_count,
                param_local_base,
                rebound,
            ));
            score
        }
        SorobanStmt::Match { scrutinee, arms } => {
            let mut score =
                score_param_local_base_in_expr(scrutinee, param_count, param_local_base, rebound);
            for arm in arms {
                score.merge(score_param_local_base(
                    &arm.body,
                    param_count,
                    param_local_base,
                    rebound,
                ));
            }
            score
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            score_param_local_base(body, param_count, param_local_base, rebound)
        }
        _ => ParamBaseScore {
            total_hits: 0,
            distinct_slots: std::collections::BTreeSet::new(),
        },
    }
}

fn score_param_local_base_in_expr(
    expr: &SorobanExpr,
    param_count: usize,
    param_local_base: u32,
    rebound: &std::collections::HashSet<u32>,
) -> ParamBaseScore {
    let maps_to_param = |idx: u32| {
        let end = param_local_base.saturating_add(param_count as u32);
        idx >= param_local_base && idx < end && !rebound.contains(&idx)
    };

    match expr {
        SorobanExpr::Local(idx) => {
            if maps_to_param(*idx) {
                ParamBaseScore {
                    total_hits: 1,
                    distinct_slots: [*idx].into_iter().collect(),
                }
            } else {
                ParamBaseScore {
                    total_hits: 0,
                    distinct_slots: std::collections::BTreeSet::new(),
                }
            }
        }
        SorobanExpr::NamedLocal(_) => ParamBaseScore {
            total_hits: 0,
            distinct_slots: std::collections::BTreeSet::new(),
        },
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
            let mut score =
                score_param_local_base_in_expr(a, param_count, param_local_base, rebound);
            score.merge(score_param_local_base_in_expr(
                b,
                param_count,
                param_local_base,
                rebound,
            ));
            score
        }
        SorobanExpr::Not(inner)
        | SorobanExpr::RequireAuth(inner)
        | SorobanExpr::AuthorizeAsCurrContract(inner)
        | SorobanExpr::ErrorFromCode(inner)
        | SorobanExpr::PanicWithError(inner)
        | SorobanExpr::CryptoSha256(inner)
        | SorobanExpr::CryptoKeccak256(inner)
        | SorobanExpr::StrkeyToAddress(inner)
        | SorobanExpr::AddressToStrkey(inner)
        | SorobanExpr::PrngReseed(inner)
        | SorobanExpr::PrngBytesNew(inner)
        | SorobanExpr::ValTag(inner)
        | SorobanExpr::Some(inner)
        | SorobanExpr::SretResult(inner)
        | SorobanExpr::Try(inner) => {
            score_param_local_base_in_expr(inner, param_count, param_local_base, rebound)
        }
        SorobanExpr::FieldAccess { object, .. } => {
            score_param_local_base_in_expr(object, param_count, param_local_base, rebound)
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            let mut score =
                score_param_local_base_in_expr(object, param_count, param_local_base, rebound);
            for arg in args {
                score.merge(score_param_local_base_in_expr(
                    arg,
                    param_count,
                    param_local_base,
                    rebound,
                ));
            }
            score
        }
        SorobanExpr::VecTryIterFold { vec, init } => {
            let mut score =
                score_param_local_base_in_expr(vec, param_count, param_local_base, rebound);
            score.merge(score_param_local_base_in_expr(
                init,
                param_count,
                param_local_base,
                rebound,
            ));
            score
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => {
            score_param_local_base_in_expr(key, param_count, param_local_base, rebound)
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            let mut score =
                score_param_local_base_in_expr(key, param_count, param_local_base, rebound);
            score.merge(score_param_local_base_in_expr(
                value,
                param_count,
                param_local_base,
                rebound,
            ));
            score
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            let mut score =
                score_param_local_base_in_expr(key, param_count, param_local_base, rebound);
            score.merge(score_param_local_base_in_expr(
                threshold,
                param_count,
                param_local_base,
                rebound,
            ));
            score.merge(score_param_local_base_in_expr(
                extend_to,
                param_count,
                param_local_base,
                rebound,
            ));
            score
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            let mut score =
                score_param_local_base_in_expr(threshold, param_count, param_local_base, rebound);
            score.merge(score_param_local_base_in_expr(
                extend_to,
                param_count,
                param_local_base,
                rebound,
            ));
            score
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            let mut score =
                score_param_local_base_in_expr(address, param_count, param_local_base, rebound);
            score.merge(score_param_local_base_in_expr(
                args,
                param_count,
                param_local_base,
                rebound,
            ));
            score
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            let mut score = ParamBaseScore {
                total_hits: 0,
                distinct_slots: std::collections::BTreeSet::new(),
            };
            for topic in topics {
                score.merge(score_param_local_base_in_expr(
                    topic,
                    param_count,
                    param_local_base,
                    rebound,
                ));
            }
            score.merge(score_param_local_base_in_expr(
                data,
                param_count,
                param_local_base,
                rebound,
            ));
            score
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
            let mut score =
                score_param_local_base_in_expr(address, param_count, param_local_base, rebound);
            score.merge(score_param_local_base_in_expr(
                function,
                param_count,
                param_local_base,
                rebound,
            ));
            for arg in args {
                score.merge(score_param_local_base_in_expr(
                    arg,
                    param_count,
                    param_local_base,
                    rebound,
                ));
            }
            score
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            let mut score = ParamBaseScore {
                total_hits: 0,
                distinct_slots: std::collections::BTreeSet::new(),
            };
            for (_, value) in fields {
                score.merge(score_param_local_base_in_expr(
                    value,
                    param_count,
                    param_local_base,
                    rebound,
                ));
            }
            score
        }
        SorobanExpr::EnumConstruct { fields, .. }
        | SorobanExpr::TupleConstruct(fields)
        | SorobanExpr::VecConstruct(fields)
        | SorobanExpr::Log(fields) => {
            let mut score = ParamBaseScore {
                total_hits: 0,
                distinct_slots: std::collections::BTreeSet::new(),
            };
            for value in fields {
                score.merge(score_param_local_base_in_expr(
                    value,
                    param_count,
                    param_local_base,
                    rebound,
                ));
            }
            score
        }
        SorobanExpr::MapConstruct(entries) => {
            let mut score = ParamBaseScore {
                total_hits: 0,
                distinct_slots: std::collections::BTreeSet::new(),
            };
            for (k, v) in entries {
                score.merge(score_param_local_base_in_expr(
                    k,
                    param_count,
                    param_local_base,
                    rebound,
                ));
                score.merge(score_param_local_base_in_expr(
                    v,
                    param_count,
                    param_local_base,
                    rebound,
                ));
            }
            score
        }
        SorobanExpr::ContractError { .. }
        | SorobanExpr::Panic
        | SorobanExpr::UnknownVal
        | SorobanExpr::CyclicSlot { .. }
        | SorobanExpr::Void
        | SorobanExpr::None
        | SorobanExpr::Env
        | SorobanExpr::LedgerSequence
        | SorobanExpr::LedgerTimestamp
        | SorobanExpr::LedgerNetworkId
        | SorobanExpr::CurrentContractAddress
        | SorobanExpr::MaxLiveUntilLedger
        | SorobanExpr::CollectionNew(_)
        | SorobanExpr::BoolLiteral(_)
        | SorobanExpr::U32Literal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::I64Literal(_)
        | SorobanExpr::U128Literal(_)
        | SorobanExpr::I128Literal(_)
        | SorobanExpr::SymbolLiteral(_)
        | SorobanExpr::StringLiteral(_)
        | SorobanExpr::BytesLiteral(_)
        | SorobanExpr::ValTagName(_)
        | SorobanExpr::Param(_) => ParamBaseScore {
            total_hits: 0,
            distinct_slots: std::collections::BTreeSet::new(),
        },
        SorobanExpr::RawHostCall { args, .. } => {
            let mut score = ParamBaseScore {
                total_hits: 0,
                distinct_slots: std::collections::BTreeSet::new(),
            };
            for arg in args {
                score.merge(score_param_local_base_in_expr(
                    arg,
                    param_count,
                    param_local_base,
                    rebound,
                ));
            }
            score
        }
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            score_param_local_base_in_expr(value, param_count, param_local_base, rebound)
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            let mut score =
                score_param_local_base_in_expr(public_key, param_count, param_local_base, rebound);
            score.merge(score_param_local_base_in_expr(
                message,
                param_count,
                param_local_base,
                rebound,
            ));
            score.merge(score_param_local_base_in_expr(
                signature,
                param_count,
                param_local_base,
                rebound,
            ));
            score
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            let mut score =
                score_param_local_base_in_expr(msg_digest, param_count, param_local_base, rebound);
            score.merge(score_param_local_base_in_expr(
                signature,
                param_count,
                param_local_base,
                rebound,
            ));
            score.merge(score_param_local_base_in_expr(
                recovery_id,
                param_count,
                param_local_base,
                rebound,
            ));
            score
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            let mut score =
                score_param_local_base_in_expr(low, param_count, param_local_base, rebound);
            score.merge(score_param_local_base_in_expr(
                high,
                param_count,
                param_local_base,
                rebound,
            ));
            score
        }
        SorobanExpr::PrngVecShuffle(inner) => {
            score_param_local_base_in_expr(inner, param_count, param_local_base, rebound)
        }
    }
}

fn collect_rebound_locals(stmts: &[SorobanStmt], rebound: &mut std::collections::HashSet<u32>) {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Let { name, value, .. } => {
                if let Some(idx_str) = name.strip_prefix("var_")
                    && let Ok(idx) = idx_str.parse::<u32>()
                {
                    if is_param_alias_binding(idx, value) {
                        continue;
                    }
                    rebound.insert(idx);
                }
            }
            SorobanStmt::Assign { target, value } => {
                if let Some(idx_str) = target.strip_prefix("var_")
                    && let Ok(idx) = idx_str.parse::<u32>()
                {
                    if is_param_alias_binding(idx, value) {
                        continue;
                    }
                    rebound.insert(idx);
                }
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_rebound_locals(then_body, rebound);
                collect_rebound_locals(else_body, rebound);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms {
                    collect_rebound_locals(&arm.body, rebound);
                }
            }
            SorobanStmt::Loop { body } => collect_rebound_locals(body, rebound),
            SorobanStmt::Block(stmts) => collect_rebound_locals(stmts, rebound),
            _ => {}
        }
    }
}

fn is_param_alias_binding(idx: u32, value: &SorobanExpr) -> bool {
    matches!(value, SorobanExpr::Local(local_idx) if *local_idx == idx)
        || matches!(value, SorobanExpr::Param(_))
        || matches!(value, SorobanExpr::NamedLocal(name) if name == &format!("var_{idx}"))
        || matches!(value, SorobanExpr::ValConvert { value: inner, .. } if is_param_alias_binding(idx, inner))
        || matches!(value, SorobanExpr::CastAs { value: inner, .. } if is_param_alias_binding(idx, inner))
}

fn replace_local_with_param_in_stmt(
    stmt: &mut SorobanStmt,
    map: &std::collections::HashMap<u32, &str>,
) {
    match stmt {
        SorobanStmt::Expr(expr) => replace_local_with_param_in_expr(expr, map),
        SorobanStmt::Let { value, .. } => replace_local_with_param_in_expr(value, map),
        SorobanStmt::Assign { value, .. } => replace_local_with_param_in_expr(value, map),
        SorobanStmt::Return(Some(expr)) => replace_local_with_param_in_expr(expr, map),
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            replace_local_with_param_in_expr(condition, map);
            for s in then_body.iter_mut() {
                replace_local_with_param_in_stmt(s, map);
            }
            for s in else_body.iter_mut() {
                replace_local_with_param_in_stmt(s, map);
            }
        }
        SorobanStmt::Match { scrutinee, arms } => {
            replace_local_with_param_in_expr(scrutinee, map);
            for arm in arms.iter_mut() {
                for s in arm.body.iter_mut() {
                    replace_local_with_param_in_stmt(s, map);
                }
            }
        }
        SorobanStmt::Loop { body } => {
            for s in body.iter_mut() {
                replace_local_with_param_in_stmt(s, map);
            }
        }
        SorobanStmt::Block(stmts) => {
            for s in stmts.iter_mut() {
                replace_local_with_param_in_stmt(s, map);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Stage 4g: Detect whether a function body references `env`
// ---------------------------------------------------------------------------

/// Check if any statement in the tree generates an `env` reference in codegen.
fn stmts_use_env(stmts: &[SorobanStmt]) -> bool {
    stmts.iter().any(stmt_uses_env)
}

fn stmt_uses_env(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => expr_uses_env(e),
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => expr_uses_env(value),
        SorobanStmt::Return(None)
        | SorobanStmt::Comment(_)
        | SorobanStmt::Break
        | SorobanStmt::Continue => false,
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => expr_uses_env(condition) || stmts_use_env(then_body) || stmts_use_env(else_body),
        SorobanStmt::Match { scrutinee, arms } => {
            expr_uses_env(scrutinee) || arms.iter().any(|arm| stmts_use_env(&arm.body))
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => stmts_use_env(body),
        SorobanStmt::For {
            start, end, body, ..
        } => expr_uses_env(start) || expr_uses_env(end) || stmts_use_env(body),
    }
}

/// Check if an expression generates an `env` reference in the codegen output.
fn expr_uses_env(expr: &SorobanExpr) -> bool {
    match expr {
        // These variants directly emit `env.` or `&env` in codegen
        SorobanExpr::StorageGet { .. }
        | SorobanExpr::StorageSet { .. }
        | SorobanExpr::StorageHas { .. }
        | SorobanExpr::StorageRemove { .. }
        | SorobanExpr::StorageExtendTtl { .. }
        | SorobanExpr::ExtendInstanceAndCodeTtl { .. }
        | SorobanExpr::InvokeContract { .. }
        | SorobanExpr::TryInvokeContract { .. }
        | SorobanExpr::VecConstruct(_)
        | SorobanExpr::MapConstruct(_)
        | SorobanExpr::CollectionNew(_)
        | SorobanExpr::Log(_)
        | SorobanExpr::PanicWithError(_)
        | SorobanExpr::PublishEvent { .. }
        | SorobanExpr::CryptoSha256(_)
        | SorobanExpr::CryptoKeccak256(_)
        | SorobanExpr::CryptoEd25519Verify { .. }
        | SorobanExpr::CryptoSecp256k1Recover { .. }
        | SorobanExpr::PrngReseed(_)
        | SorobanExpr::PrngBytesNew(_)
        | SorobanExpr::PrngU64InRange { .. }
        | SorobanExpr::PrngVecShuffle(_)
        | SorobanExpr::StringLiteral(_)
        | SorobanExpr::BytesLiteral(_)
        | SorobanExpr::CurrentContractAddress
        | SorobanExpr::LedgerSequence
        | SorobanExpr::LedgerTimestamp
        | SorobanExpr::LedgerNetworkId
        | SorobanExpr::MaxLiveUntilLedger
        | SorobanExpr::AuthorizeAsCurrContract(_)
        | SorobanExpr::StrkeyToAddress(_)
        | SorobanExpr::AddressToStrkey(_)
        | SorobanExpr::RawHostCall { .. } => true,

        // SymbolLiteral uses env only for strings > 9 chars (Symbol::new(&env, ..))
        SorobanExpr::SymbolLiteral(s) => s.len() > 9,

        // Explicit env reference
        SorobanExpr::Env => true,

        // Recurse into sub-expressions for composite nodes
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
        | SorobanExpr::Or(a, b) => expr_uses_env(a) || expr_uses_env(b),
        SorobanExpr::Not(a) => expr_uses_env(a),
        SorobanExpr::FieldAccess { object, .. } => expr_uses_env(object),
        SorobanExpr::MethodCall { object, args, .. } => {
            expr_uses_env(object) || args.iter().any(expr_uses_env)
        }
        SorobanExpr::VecTryIterFold { vec, init } => expr_uses_env(vec) || expr_uses_env(init),
        SorobanExpr::StructConstruct { fields, .. } => fields.iter().any(|(_, v)| expr_uses_env(v)),
        SorobanExpr::EnumConstruct { fields, .. } => fields.iter().any(expr_uses_env),
        SorobanExpr::TupleConstruct(elems) => elems.iter().any(expr_uses_env),
        SorobanExpr::RequireAuth(a) | SorobanExpr::ErrorFromCode(a) => expr_uses_env(a),
        SorobanExpr::RequireAuthForArgs { address, args } => {
            expr_uses_env(address) || expr_uses_env(args)
        }
        SorobanExpr::ValConvert { value, .. }
        | SorobanExpr::CastAs { value, .. }
        | SorobanExpr::Try(value) => expr_uses_env(value),
        SorobanExpr::ValTag(inner) | SorobanExpr::Some(inner) | SorobanExpr::SretResult(inner) => {
            expr_uses_env(inner)
        }
        SorobanExpr::ContractError { .. } => false,

        // Leaves that never emit `env`
        SorobanExpr::U32Literal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::I64Literal(_)
        | SorobanExpr::U128Literal(_)
        | SorobanExpr::I128Literal(_)
        | SorobanExpr::BoolLiteral(_)
        | SorobanExpr::Void
        | SorobanExpr::None
        | SorobanExpr::Param(_)
        | SorobanExpr::Local(_)
        | SorobanExpr::NamedLocal(_)
        | SorobanExpr::Panic
        | SorobanExpr::ValTagName(_)
        | SorobanExpr::UnknownVal
        | SorobanExpr::CyclicSlot { .. } => false,
    }
}

fn replace_local_with_param_in_expr(
    expr: &mut SorobanExpr,
    map: &std::collections::HashMap<u32, &str>,
) {
    match expr {
        SorobanExpr::Local(idx) => {
            if let Some(name) = map.get(idx) {
                *expr = SorobanExpr::Param(name.to_string());
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
            replace_local_with_param_in_expr(a, map);
            replace_local_with_param_in_expr(b, map);
        }
        SorobanExpr::Not(a) => replace_local_with_param_in_expr(a, map),
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => {
            replace_local_with_param_in_expr(key, map);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            replace_local_with_param_in_expr(key, map);
            replace_local_with_param_in_expr(value, map);
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            replace_local_with_param_in_expr(key, map);
            replace_local_with_param_in_expr(threshold, map);
            replace_local_with_param_in_expr(extend_to, map);
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            replace_local_with_param_in_expr(threshold, map);
            replace_local_with_param_in_expr(extend_to, map);
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields.iter_mut() {
                replace_local_with_param_in_expr(v, map);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for f in fields.iter_mut() {
                replace_local_with_param_in_expr(f, map);
            }
        }
        SorobanExpr::TupleConstruct(fields) | SorobanExpr::VecConstruct(fields) => {
            for f in fields.iter_mut() {
                replace_local_with_param_in_expr(f, map);
            }
        }
        SorobanExpr::MapConstruct(entries) => {
            for (k, v) in entries.iter_mut() {
                replace_local_with_param_in_expr(k, map);
                replace_local_with_param_in_expr(v, map);
            }
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            replace_local_with_param_in_expr(object, map);
            for a in args.iter_mut() {
                replace_local_with_param_in_expr(a, map);
            }
        }
        SorobanExpr::FieldAccess { object, .. } => {
            replace_local_with_param_in_expr(object, map);
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
            replace_local_with_param_in_expr(address, map);
            replace_local_with_param_in_expr(function, map);
            for a in args.iter_mut() {
                replace_local_with_param_in_expr(a, map);
            }
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics.iter_mut() {
                replace_local_with_param_in_expr(t, map);
            }
            replace_local_with_param_in_expr(data, map);
        }
        SorobanExpr::RequireAuth(a) => replace_local_with_param_in_expr(a, map),
        SorobanExpr::RequireAuthForArgs { address, args } => {
            replace_local_with_param_in_expr(address, map);
            replace_local_with_param_in_expr(args, map);
        }
        SorobanExpr::AuthorizeAsCurrContract(a) => replace_local_with_param_in_expr(a, map),
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            replace_local_with_param_in_expr(value, map)
        }
        SorobanExpr::Log(args) => {
            for a in args.iter_mut() {
                replace_local_with_param_in_expr(a, map);
            }
        }
        SorobanExpr::PanicWithError(e)
        | SorobanExpr::ErrorFromCode(e)
        | SorobanExpr::CryptoSha256(e)
        | SorobanExpr::CryptoKeccak256(e)
        | SorobanExpr::PrngReseed(e)
        | SorobanExpr::PrngBytesNew(e)
        | SorobanExpr::PrngVecShuffle(e)
        | SorobanExpr::StrkeyToAddress(e)
        | SorobanExpr::AddressToStrkey(e) => {
            replace_local_with_param_in_expr(e, map);
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            replace_local_with_param_in_expr(public_key, map);
            replace_local_with_param_in_expr(message, map);
            replace_local_with_param_in_expr(signature, map);
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            replace_local_with_param_in_expr(msg_digest, map);
            replace_local_with_param_in_expr(signature, map);
            replace_local_with_param_in_expr(recovery_id, map);
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            replace_local_with_param_in_expr(low, map);
            replace_local_with_param_in_expr(high, map);
        }
        SorobanExpr::RawHostCall { args, .. } => {
            for a in args.iter_mut() {
                replace_local_with_param_in_expr(a, map);
            }
        }
        _ => {} // Leaves: literals, Param, Env, NamedLocal, CollectionNew, etc.
    }
}

// ---------------------------------------------------------------------------
// Stage 4h: Resolve unused params in InvokeContract/TryInvokeContract args
// ---------------------------------------------------------------------------

/// When the lifter produces artifact literals in cross-contract call args
/// (from branching Val-encoding wrappers), and the function has params that
/// are completely absent from the body, replace the artifacts with the
/// corresponding unused params.
/// Resolve unbound Local(N) in InvokeContract args by finding a preceding
/// Let binding with a matching typed value (e.g., ValConvert { FieldAccess }).
///
/// When the lifter's BrIf processing loses a local value, the InvokeContract
/// uses Local(N) directly. If there's a Let binding `var_M = ValConvert {
/// FieldAccess { obj, field }, type }` with the same target type, Local(N)
/// can be replaced with Local(M) — the field access that produces the value.
fn resolve_unbound_invoke_locals(stmts: &mut [SorobanStmt]) {
    // Collect Let bindings: track which locals have meaningful values
    // vs which are "effectively unbound" (bound to Local(N), UnknownVal, etc.)
    let mut meaningfully_defined: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut field_access_bindings: Vec<(u32, String)> = Vec::new(); // (idx, target_type)

    for stmt in stmts.iter() {
        if let SorobanStmt::Let { name, value, .. } = stmt
            && let Some(idx) = name
                .strip_prefix("var_")
                .and_then(|s| s.parse::<u32>().ok())
        {
            // Only count as "meaningfully defined" if the value is not
            // just a Local() reference or UnknownVal (which are artifacts
            // from bind_unbound_locals or branch-sequential execution)
            let is_meaningful = !matches!(value, SorobanExpr::Local(_) | SorobanExpr::UnknownVal);
            if is_meaningful {
                meaningfully_defined.insert(idx);
            }
            // Track ValConvert { FieldAccess } bindings
            if let SorobanExpr::ValConvert {
                value: inner,
                target_type,
            } = value
                && matches!(inner.as_ref(), SorobanExpr::FieldAccess { .. })
            {
                field_access_bindings.push((idx, target_type.clone()));
            }
        }
    }

    if field_access_bindings.is_empty() {
        return;
    }

    // Walk InvokeContract args and replace unbound/artifact Local(N)
    // wrapped in ValConvert with a matching field_access binding's Local(M)
    for stmt in stmts.iter_mut() {
        resolve_unbound_locals_in_stmt(stmt, &meaningfully_defined, &field_access_bindings);
    }
}

fn resolve_unbound_locals_in_stmt(
    stmt: &mut SorobanStmt,
    defined: &std::collections::HashSet<u32>,
    bindings: &[(u32, String)],
) {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
            resolve_unbound_locals_in_expr(e, defined, bindings);
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            resolve_unbound_locals_in_expr(value, defined, bindings);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            resolve_unbound_locals_in_expr(condition, defined, bindings);
            for s in then_body.iter_mut() {
                resolve_unbound_locals_in_stmt(s, defined, bindings);
            }
            for s in else_body.iter_mut() {
                resolve_unbound_locals_in_stmt(s, defined, bindings);
            }
        }
        SorobanStmt::Match { arms, .. } => {
            for arm in arms.iter_mut() {
                for s in arm.body.iter_mut() {
                    resolve_unbound_locals_in_stmt(s, defined, bindings);
                }
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            for s in body.iter_mut() {
                resolve_unbound_locals_in_stmt(s, defined, bindings);
            }
        }
        _ => {}
    }
}

fn resolve_unbound_locals_in_expr(
    expr: &mut SorobanExpr,
    defined: &std::collections::HashSet<u32>,
    bindings: &[(u32, String)],
) {
    match expr {
        // ValConvert { Local(N) or NamedLocal("var_N"), type } where N is not
        // meaningfully defined (artifact from bind_unbound_locals)
        SorobanExpr::ValConvert { value, target_type } => {
            let needs_resolve = match value.as_ref() {
                SorobanExpr::Local(idx) => !defined.contains(idx),
                SorobanExpr::NamedLocal(name) => name.starts_with("var_"),
                _ => false,
            };
            if needs_resolve
                && let Some((binding_idx, _)) = bindings.iter().find(|(_, t)| t == target_type)
            {
                **value = SorobanExpr::Local(*binding_idx);
            }
            resolve_unbound_locals_in_expr(value, defined, bindings);
        }
        // Recurse into sub-expressions
        SorobanExpr::InvokeContract { args, address, .. }
        | SorobanExpr::TryInvokeContract { args, address, .. } => {
            resolve_unbound_locals_in_expr(address, defined, bindings);
            for arg in args.iter_mut() {
                resolve_unbound_locals_in_expr(arg, defined, bindings);
            }
        }
        SorobanExpr::VecConstruct(elems) | SorobanExpr::TupleConstruct(elems) => {
            for e in elems.iter_mut() {
                resolve_unbound_locals_in_expr(e, defined, bindings);
            }
        }
        _ => {}
    }
}

fn resolve_unused_invoke_params(body: &mut [SorobanStmt], params: &[FnParam]) {
    if params.is_empty() {
        return;
    }

    // Collect all param names referenced in the body
    let mut used_names = std::collections::HashSet::new();
    collect_used_param_names_stmts(body, &mut used_names);

    // Find unused params (non-env, non-Address types — those don't produce artifact literals)
    let unused: Vec<&FnParam> = params
        .iter()
        .filter(|p| {
            !used_names.contains(p.name.as_str()) && is_artifact_prone_type_def(&p.type_def)
        })
        .collect();

    if unused.is_empty() {
        return;
    }

    // Walk the body and try to replace artifact literals in invoke args
    for stmt in body.iter_mut() {
        replace_invoke_artifact_literals_in_stmt(stmt, &unused);
    }
}

/// Types whose Val encoding uses branching (small vs object), producing
/// artifact literals when the lifter's branch-sequential execution corrupts values.
fn is_artifact_prone_type_def(spec: &stellar_xdr::curr::ScSpecTypeDef) -> bool {
    use stellar_xdr::curr::ScSpecTypeDef;
    matches!(
        spec,
        ScSpecTypeDef::U64
            | ScSpecTypeDef::I64
            | ScSpecTypeDef::U128
            | ScSpecTypeDef::I128
            | ScSpecTypeDef::Timepoint
            | ScSpecTypeDef::Duration
            | ScSpecTypeDef::U256
            | ScSpecTypeDef::I256
    )
}

/// Check if an expression is likely a Val-encoding artifact (not a meaningful constant).
/// Unwraps `ValConvert` layers which the lifter adds around Val-decoded values.
fn is_artifact_literal(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::I64Literal(n) => {
            // Small constants (0-255) are common real values, not artifacts.
            // Val-encoding artifacts are large values from (x << 8) | tag
            // or other bit manipulation.
            n.unsigned_abs() > 255
        }
        SorobanExpr::ValConvert { value, .. } => is_artifact_literal(value),
        _ => false,
    }
}

/// Check if an expression is an artifact composed of arithmetic over UnknownVal and
/// literals — produced by i128 multiply or other WASM helpers whose results can't be
/// resolved to named parameters. Contains no Param or host call references.
fn is_artifact_expression(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::UnknownVal => true,
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
        | SorobanExpr::Ge(a, b) => is_artifact_expression(a) && is_artifact_expression(b),
        SorobanExpr::Not(a) => is_artifact_expression(a),
        SorobanExpr::I64Literal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U32Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::BoolLiteral(_) => true,
        SorobanExpr::ValConvert { value, .. } => is_artifact_expression(value),
        _ => false,
    }
}

fn collect_used_param_names_stmts(
    stmts: &[SorobanStmt],
    used: &mut std::collections::HashSet<String>,
) {
    for stmt in stmts {
        collect_used_param_names_stmt(stmt, used);
    }
}

fn collect_used_param_names_stmt(stmt: &SorobanStmt, used: &mut std::collections::HashSet<String>) {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
            collect_used_param_names_expr(e, used);
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            collect_used_param_names_expr(value, used);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            collect_used_param_names_expr(condition, used);
            collect_used_param_names_stmts(then_body, used);
            collect_used_param_names_stmts(else_body, used);
        }
        SorobanStmt::Match { scrutinee, arms } => {
            collect_used_param_names_expr(scrutinee, used);
            for arm in arms {
                collect_used_param_names_stmts(&arm.body, used);
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            collect_used_param_names_stmts(body, used);
        }
        _ => {}
    }
}

fn collect_used_param_names_expr(expr: &SorobanExpr, used: &mut std::collections::HashSet<String>) {
    match expr {
        SorobanExpr::Param(name) => {
            used.insert(name.clone());
        }
        SorobanExpr::NamedLocal(name) => {
            used.insert(name.clone());
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
            collect_used_param_names_expr(a, used);
            collect_used_param_names_expr(b, used);
        }
        SorobanExpr::Not(a)
        | SorobanExpr::RequireAuth(a)
        | SorobanExpr::ErrorFromCode(a)
        | SorobanExpr::CryptoSha256(a)
        | SorobanExpr::CryptoKeccak256(a)
        | SorobanExpr::PrngReseed(a)
        | SorobanExpr::PrngBytesNew(a)
        | SorobanExpr::PrngVecShuffle(a)
        | SorobanExpr::StrkeyToAddress(a)
        | SorobanExpr::AddressToStrkey(a)
        | SorobanExpr::PanicWithError(a)
        | SorobanExpr::AuthorizeAsCurrContract(a)
        | SorobanExpr::ValConvert { value: a, .. }
        | SorobanExpr::FieldAccess { object: a, .. } => {
            collect_used_param_names_expr(a, used);
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            collect_used_param_names_expr(object, used);
            for a in args {
                collect_used_param_names_expr(a, used);
            }
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
            collect_used_param_names_expr(address, used);
            collect_used_param_names_expr(function, used);
            for a in args {
                collect_used_param_names_expr(a, used);
            }
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => {
            collect_used_param_names_expr(key, used);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            collect_used_param_names_expr(key, used);
            collect_used_param_names_expr(value, used);
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            collect_used_param_names_expr(key, used);
            collect_used_param_names_expr(threshold, used);
            collect_used_param_names_expr(extend_to, used);
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            collect_used_param_names_expr(threshold, used);
            collect_used_param_names_expr(extend_to, used);
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields {
                collect_used_param_names_expr(v, used);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for f in fields {
                collect_used_param_names_expr(f, used);
            }
        }
        SorobanExpr::TupleConstruct(elems)
        | SorobanExpr::VecConstruct(elems)
        | SorobanExpr::Log(elems) => {
            for e in elems {
                collect_used_param_names_expr(e, used);
            }
        }
        SorobanExpr::MapConstruct(entries) => {
            for (k, v) in entries {
                collect_used_param_names_expr(k, used);
                collect_used_param_names_expr(v, used);
            }
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics {
                collect_used_param_names_expr(t, used);
            }
            collect_used_param_names_expr(data, used);
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            collect_used_param_names_expr(address, used);
            collect_used_param_names_expr(args, used);
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            collect_used_param_names_expr(public_key, used);
            collect_used_param_names_expr(message, used);
            collect_used_param_names_expr(signature, used);
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            collect_used_param_names_expr(msg_digest, used);
            collect_used_param_names_expr(signature, used);
            collect_used_param_names_expr(recovery_id, used);
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            collect_used_param_names_expr(low, used);
            collect_used_param_names_expr(high, used);
        }
        SorobanExpr::RawHostCall { args, .. } => {
            for a in args {
                collect_used_param_names_expr(a, used);
            }
        }
        SorobanExpr::ContractError { .. } => {}
        // Leaves
        _ => {}
    }
}

fn replace_invoke_artifact_literals_in_stmt(stmt: &mut SorobanStmt, unused_params: &[&FnParam]) {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
            replace_invoke_artifact_literals_in_expr(e, unused_params);
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            replace_invoke_artifact_literals_in_expr(value, unused_params);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            replace_invoke_artifact_literals_in_expr(condition, unused_params);
            for s in then_body.iter_mut() {
                replace_invoke_artifact_literals_in_stmt(s, unused_params);
            }
            for s in else_body.iter_mut() {
                replace_invoke_artifact_literals_in_stmt(s, unused_params);
            }
        }
        SorobanStmt::Match { scrutinee, arms } => {
            replace_invoke_artifact_literals_in_expr(scrutinee, unused_params);
            for arm in arms.iter_mut() {
                for s in arm.body.iter_mut() {
                    replace_invoke_artifact_literals_in_stmt(s, unused_params);
                }
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            for s in body.iter_mut() {
                replace_invoke_artifact_literals_in_stmt(s, unused_params);
            }
        }
        _ => {}
    }
}

fn replace_invoke_artifact_literals_in_expr(expr: &mut SorobanExpr, unused_params: &[&FnParam]) {
    match expr {
        SorobanExpr::InvokeContract { args, .. } | SorobanExpr::TryInvokeContract { args, .. } => {
            // Count artifact literals/expressions in the args.
            // Artifact expressions include UnknownVal wrapped in arithmetic
            // from i128 encoding (e.g., `-(UnknownVal + (UnknownVal != 0))`).
            let artifact_indices: Vec<usize> = args
                .iter()
                .enumerate()
                .filter(|(_, a)| is_artifact_literal(a) || is_artifact_expression(a))
                .map(|(i, _)| i)
                .collect();

            // Replace when the artifact count is <= the unused param count.
            // Use the first N unused params for N artifact positions.
            if !artifact_indices.is_empty() && artifact_indices.len() <= unused_params.len() {
                for (idx, param) in artifact_indices.iter().zip(unused_params.iter()) {
                    args[*idx] = SorobanExpr::Param(param.name.clone());
                }
            }
        }
        SorobanExpr::StorageSet { value, .. }
            // Replace artifact literal or artifact expression in the storage value
            // with an unused param. Only when exactly 1 unused param.
            // Artifact expressions include i128 multiply remnants (e.g., `3 * todo!() + todo!()`)
            // where the computation lost its connection to the parameter.
            if unused_params.len() == 1
                && (is_artifact_literal(value) || is_artifact_expression(value))
            => {
                **value = SorobanExpr::Param(unused_params[0].name.clone());
            }
        // Recurse into sub-expressions that might contain InvokeContract/StorageSet
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
            replace_invoke_artifact_literals_in_expr(a, unused_params);
            replace_invoke_artifact_literals_in_expr(b, unused_params);
        }
        SorobanExpr::Not(a)
        | SorobanExpr::FieldAccess { object: a, .. }
        | SorobanExpr::ValConvert { value: a, .. } => {
            replace_invoke_artifact_literals_in_expr(a, unused_params);
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            replace_invoke_artifact_literals_in_expr(object, unused_params);
            for a in args.iter_mut() {
                replace_invoke_artifact_literals_in_expr(a, unused_params);
            }
        }
        _ => {} // Leaves and other non-recursive cases
    }
}

/// Detect pattern: [pre...] Let(name, artifact) Match(arms-with-side-effect-exprs) Expr/Return(name)
/// Transform: remove the Let and trailing return, making the match the tail expression.
fn promote_match_arm_exprs(body: &mut Vec<SorobanStmt>) {
    if body.len() < 2 {
        return;
    }

    // Check: last stmt is Return(Some(x)) or Expr(x) where x references a variable
    let tail_var = match body.last() {
        Some(SorobanStmt::Return(Some(e))) | Some(SorobanStmt::Expr(e)) => extract_local_name(e),
        _ => None,
    };
    let Some(tail_var) = tail_var else {
        return;
    };

    // Check: second-to-last is a Match with enum arms where all arms produce results
    let match_idx = body.len() - 2;
    let is_promotable_match = match &body[match_idx] {
        SorobanStmt::Match { arms, .. } => {
            let all_enum = arms
                .iter()
                .all(|a| matches!(a.pattern, MatchPattern::EnumVariant { .. }));
            let all_side_effect = arms.iter().all(|arm| {
                arm.body.len() == 1
                    && match &arm.body[0] {
                        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
                            is_result_producing_expr(e)
                        }
                        _ => false,
                    }
            });
            all_enum && all_side_effect
        }
        _ => false,
    };

    if !is_promotable_match {
        return;
    }

    // Remove trailing artifact return
    body.pop();

    // Convert Return(Some(expr)) in match arms to Expr(expr) so the match
    // can serve as a tail expression with implicit returns.
    if let Some(SorobanStmt::Match { arms, .. }) = body.last_mut() {
        for arm in arms.iter_mut() {
            if let Some(SorobanStmt::Return(Some(e))) = arm.body.first() {
                let expr = e.clone();
                arm.body[0] = SorobanStmt::Expr(expr);
            }
        }
    }

    // Remove the Let binding for the artifact variable if it exists.
    // The let value is an artifact if it's NOT a result-producing expr,
    // or if it's a .get(N) on a parameter (tuple element extraction artifact).
    if let Some(pos) = body
        .iter()
        .position(|s| matches!(s, SorobanStmt::Let { name, .. } if name == &tail_var))
    {
        let should_remove = match &body[pos] {
            SorobanStmt::Let { value, .. } => {
                !is_result_producing_expr(value) || is_param_get_artifact(value)
            }
            _ => false,
        };
        if should_remove {
            body.remove(pos);
        }
    }
}

fn extract_local_name(expr: &SorobanExpr) -> Option<String> {
    match expr {
        SorobanExpr::NamedLocal(name) | SorobanExpr::Param(name) => Some(name.clone()),
        _ => None,
    }
}

fn is_result_producing_expr(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::StorageGet { .. }
            | SorobanExpr::StorageHas { .. }
            | SorobanExpr::InvokeContract { .. }
            | SorobanExpr::TryInvokeContract { .. }
            | SorobanExpr::MethodCall { .. }
    )
}

/// Check if an expression is `param.get(N)` — a tuple element extraction artifact
/// that appears on enum parameters where .get() makes no semantic sense.
fn is_param_get_artifact(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::MethodCall { object, method, .. }
            if method == "get" && matches!(object.as_ref(), SorobanExpr::Param(_))
    )
}

/// Detect match arms with UnknownVal where the variant carries an integer enum type.
/// Replace with `val as i64` by changing bindings from `["_"]` to `["val"]` and
/// replacing UnknownVal with `ValConvert { NamedLocal("val"), "i64" }`.
fn recover_enum_cast_arms(stmts: &mut [SorobanStmt], registry: &TypeRegistry) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    if let MatchPattern::EnumVariant {
                        type_name,
                        variant,
                        bindings,
                    } = &mut arm.pattern
                        && bindings.len() == 1
                        && bindings[0] == "_"
                        && let Some(data_type) = registry.find_variant_data_type(type_name, variant)
                        && let Some(type_name_str) = registry.resolve_type_name(&data_type)
                        && registry.is_integer_enum(&type_name_str)
                        && arm_has_unknown_val(&arm.body)
                    {
                        bindings[0] = "val".to_string();
                        let replacement = SorobanExpr::CastAs {
                            value: Box::new(SorobanExpr::NamedLocal("val".to_string())),
                            target_type: "i64".to_string(),
                        };
                        replace_unknown_val_in_body(&mut arm.body, &replacement);
                    }
                }
                // Recurse into arm bodies
                for arm in arms.iter_mut() {
                    recover_enum_cast_arms(&mut arm.body, registry);
                }
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                recover_enum_cast_arms(then_body, registry);
                recover_enum_cast_arms(else_body, registry);
            }
            SorobanStmt::Loop { body, .. } => {
                recover_enum_cast_arms(body, registry);
            }
            SorobanStmt::Block(body) => {
                recover_enum_cast_arms(body, registry);
            }
            _ => {}
        }
    }
}

fn arm_has_unknown_val(body: &[SorobanStmt]) -> bool {
    body.iter().any(|s| match s {
        SorobanStmt::Assign { value, .. } => matches!(value, SorobanExpr::UnknownVal),
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
            matches!(e, SorobanExpr::UnknownVal)
        }
        _ => false,
    })
}

fn replace_unknown_val_in_body(body: &mut [SorobanStmt], replacement: &SorobanExpr) {
    for stmt in body.iter_mut() {
        match stmt {
            SorobanStmt::Assign { value, .. } if matches!(value, SorobanExpr::UnknownVal) => {
                *value = replacement.clone();
            }
            SorobanStmt::Expr(e) if matches!(e, SorobanExpr::UnknownVal) => {
                *e = replacement.clone();
            }
            SorobanStmt::Return(Some(e)) if matches!(e, SorobanExpr::UnknownVal) => {
                *e = replacement.clone();
            }
            _ => {}
        }
    }
}

/// Fix misidentified enum variant keys in instance storage operations.
///
/// When `EnumConstruct { variant: X, fields: [UnknownVal] }` (data-carrying variant
/// with unknown data) is used as a key in instance storage, and the union has a void
/// variant, replace with the void variant. Branch-sequential corruption causes the
/// lifter to pick up a data-carrying variant from a shared code path, but the actual
/// key is typically the simpler void variant (e.g., DataKey::Admin).
fn fix_misidentified_instance_keys(stmts: &mut [SorobanStmt], registry: &TypeRegistry) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Let { value, .. } => {
                fix_enum_unknown_to_void(value, registry);
            }
            SorobanStmt::Expr(e) => {
                fix_instance_storage_key(e, registry);
            }
            SorobanStmt::If {
                then_body,
                else_body,
                condition,
                ..
            } => {
                fix_instance_storage_key(condition, registry);
                fix_misidentified_instance_keys(then_body, registry);
                fix_misidentified_instance_keys(else_body, registry);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    fix_misidentified_instance_keys(&mut arm.body, registry);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                fix_misidentified_instance_keys(body, registry);
            }
            _ => {}
        }
    }
}

/// Check if an EnumConstruct with UnknownVal data should be a void variant.
/// Only replaces when used in instance storage context (not temporary/persistent).
fn fix_instance_storage_key(expr: &mut SorobanExpr, registry: &TypeRegistry) {
    match expr {
        SorobanExpr::StorageSet {
            storage_type: StorageType::Instance,
            key,
            ..
        }
        | SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key,
            ..
        }
        | SorobanExpr::StorageHas {
            storage_type: StorageType::Instance,
            key,
            ..
        } => {
            fix_enum_unknown_to_void(key, registry);
        }
        _ => {}
    }
}

/// Replace `EnumConstruct { variant, fields: [UnknownVal] }` with the union's
/// void variant when one exists.
fn fix_enum_unknown_to_void(expr: &mut SorobanExpr, registry: &TypeRegistry) {
    if let SorobanExpr::EnumConstruct {
        type_name,
        variant,
        fields,
    } = expr
    {
        // Only fix when the sole field is UnknownVal
        if fields.len() != 1 || !matches!(&fields[0], SorobanExpr::UnknownVal) {
            return;
        }

        // Find the union's void variant
        if let Some(union_spec) = registry.get_union(type_name) {
            use stellar_xdr::curr::ScSpecUdtUnionCaseV0;
            let void_variant = union_spec.cases.iter().find_map(|case| {
                if let ScSpecUdtUnionCaseV0::VoidV0(v) = case {
                    v.name.to_utf8_string().ok()
                } else {
                    None
                }
            });
            if let Some(void_name) = void_variant {
                *variant = void_name;
                fields.clear();
            }
        }
    }
}

/// Merge orphan `Expr(LedgerSequence)` into adjacent `StorageExtendTtl` args.
///
/// When `Expr(LedgerSequence)` precedes `Expr(StorageExtendTtl { threshold: Sub(_, UnknownVal) })`,
/// the `UnknownVal` should be `LedgerSequence` — they were split during function inlining.
/// Also handles `Neg(UnknownVal)` which represents `0 - unknown` → replace with `Neg(LedgerSequence)`.
fn merge_orphan_ledger_sequence(stmts: &mut Vec<SorobanStmt>) {
    let mut i = 0;
    while i < stmts.len() {
        let is_ledger_seq = matches!(&stmts[i], SorobanStmt::Expr(SorobanExpr::LedgerSequence));
        if is_ledger_seq {
            // Scan forward (within 5 stmts) for a StorageExtendTtl with UnknownVal
            let mut replaced = false;
            for j in (i + 1)..stmts.len().min(i + 6) {
                if let SorobanStmt::Expr(SorobanExpr::StorageExtendTtl {
                    threshold,
                    extend_to,
                    ..
                }) = &mut stmts[j]
                {
                    replaced |=
                        replace_unknown_in_sub_or_neg(threshold, &SorobanExpr::LedgerSequence);
                    replaced |=
                        replace_unknown_in_sub_or_neg(extend_to, &SorobanExpr::LedgerSequence);
                    break;
                }
            }
            if replaced {
                stmts.remove(i);
                continue;
            }
        }
        i += 1;
    }

    // Recurse into nested bodies
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                merge_orphan_ledger_sequence(then_body);
                merge_orphan_ledger_sequence(else_body);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    merge_orphan_ledger_sequence(&mut arm.body);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                merge_orphan_ledger_sequence(body);
            }
            _ => {}
        }
    }
}

/// Replace `UnknownVal` inside `Sub(_, UnknownVal)` or `Sub(0, UnknownVal)` (= `Neg`)
/// with the given replacement expression. Returns true if a replacement was made.
fn replace_unknown_in_sub_or_neg(expr: &mut SorobanExpr, replacement: &SorobanExpr) -> bool {
    match expr {
        // Sub(X, UnknownVal) → Sub(X, replacement)
        SorobanExpr::Sub(_, b) if matches!(b.as_ref(), SorobanExpr::UnknownVal) => {
            **b = replacement.clone();
            true
        }
        // Neg pattern: Sub(0, UnknownVal) → Sub(0, replacement)
        // Already handled above since Sub(I64Literal(0), UnknownVal) matches
        _ => false,
    }
}

/// Recover struct field operations in match arms.
///
/// When a match arm returns a bare struct/tuple binding (e.g., `udt_struct`)
/// but the context expects a primitive type (e.g., `i64`), synthesize field
/// access expressions from the struct's definition. For example:
///   `UdtEnum::UdtB(udt_struct) => udt_struct`
/// Recover storage keys for `extend_ttl` inside if-has guards.
///
/// When `if has(&key) { ...; extend_ttl(&todo!(), threshold, extend_to) }`,
/// the extend_ttl key should match the has() guard's key.
fn recover_extend_ttl_keys(stmts: &mut [SorobanStmt]) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                // Extract key from StorageHas condition
                let guard_key = if let SorobanExpr::StorageHas { key, .. } = condition {
                    Some(key.as_ref().clone())
                } else {
                    None
                };

                if let Some(ref key) = guard_key {
                    // Replace UnknownVal keys in extend_ttl within then_body
                    replace_extend_ttl_unknown_keys(then_body, key);
                }

                // Recurse
                recover_extend_ttl_keys(then_body);
                recover_extend_ttl_keys(else_body);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    recover_extend_ttl_keys(&mut arm.body);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                recover_extend_ttl_keys(body);
            }
            _ => {}
        }
    }
}

/// Replace UnknownVal keys in StorageExtendTtl statements with the given key.
fn replace_extend_ttl_unknown_keys(stmts: &mut [SorobanStmt], key: &SorobanExpr) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Expr(SorobanExpr::StorageExtendTtl { key: ttl_key, .. }) => {
                if matches!(ttl_key.as_ref(), SorobanExpr::UnknownVal) {
                    **ttl_key = key.clone();
                }
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                replace_extend_ttl_unknown_keys(then_body, key);
                replace_extend_ttl_unknown_keys(else_body, key);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    replace_extend_ttl_unknown_keys(&mut arm.body, key);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                replace_extend_ttl_unknown_keys(body, key);
            }
            _ => {}
        }
    }
}

/// becomes:
///   `UdtEnum::UdtB(udt_struct) => udt_struct.a + udt_struct.b`
fn recover_struct_field_arms(
    stmts: &mut [SorobanStmt],
    registry: &TypeRegistry,
    expected_type: &ScSpecTypeDef,
) {
    if !is_primitive_spec_type(expected_type) {
        return;
    }
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    if let MatchPattern::EnumVariant {
                        type_name,
                        variant,
                        bindings,
                    } = &arm.pattern
                    {
                        if bindings.len() != 1 || bindings[0] == "_" {
                            continue;
                        }
                        let binding_name = &bindings[0];
                        if !arm_value_is_binding(&arm.body, binding_name) {
                            continue;
                        }
                        let data_type = match registry.find_variant_data_type(type_name, variant) {
                            Some(dt) => dt,
                            None => continue,
                        };
                        let struct_name = match registry.resolve_type_name(&data_type) {
                            Some(n) => n,
                            None => continue,
                        };
                        let spec = match registry.get_struct(&struct_name) {
                            Some(s) => s,
                            None => continue,
                        };
                        // Filter fields whose type matches the expected primitive
                        let matching_fields: Vec<String> = spec
                            .fields
                            .iter()
                            .filter(|f| f.type_ == *expected_type)
                            .filter_map(|f| f.name.to_utf8_string().ok())
                            .collect();
                        if matching_fields.is_empty() {
                            continue;
                        }
                        let replacement = build_field_chain(binding_name, &matching_fields);
                        replace_binding_in_arm_body(&mut arm.body, binding_name, &replacement);
                    }
                }
                // Recurse into arm bodies
                for arm in arms.iter_mut() {
                    recover_struct_field_arms(&mut arm.body, registry, expected_type);
                }
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                recover_struct_field_arms(then_body, registry, expected_type);
                recover_struct_field_arms(else_body, registry, expected_type);
            }
            SorobanStmt::Loop { body, .. } => {
                recover_struct_field_arms(body, registry, expected_type);
            }
            SorobanStmt::Block(body) => {
                recover_struct_field_arms(body, registry, expected_type);
            }
            _ => {}
        }
    }
}

fn is_primitive_spec_type(ty: &ScSpecTypeDef) -> bool {
    matches!(
        ty,
        ScSpecTypeDef::I64
            | ScSpecTypeDef::U64
            | ScSpecTypeDef::I128
            | ScSpecTypeDef::U128
            | ScSpecTypeDef::I32
            | ScSpecTypeDef::U32
            | ScSpecTypeDef::I256
            | ScSpecTypeDef::U256
    )
}

/// Check if the arm body's last statement has a value that is just the bare binding.
fn arm_value_is_binding(body: &[SorobanStmt], binding: &str) -> bool {
    match body.last() {
        Some(SorobanStmt::Assign { value, .. })
        | Some(SorobanStmt::Return(Some(value)))
        | Some(SorobanStmt::Expr(value)) => {
            matches!(value, SorobanExpr::NamedLocal(n) if n == binding)
        }
        _ => false,
    }
}

/// Build a chain of `FieldAccess` expressions joined by `Add`.
/// For one field: `binding.field`
/// For multiple fields: `binding.a + binding.b + ...`
fn build_field_chain(binding: &str, fields: &[String]) -> SorobanExpr {
    let mut iter = fields.iter().map(|f| SorobanExpr::FieldAccess {
        object: Box::new(SorobanExpr::NamedLocal(binding.to_string())),
        field: f.clone(),
    });
    let first = iter.next().unwrap();
    iter.fold(first, |acc, fa| {
        SorobanExpr::Add(Box::new(acc), Box::new(fa))
    })
}

/// Replace the bare binding reference in the arm body with the synthesized expression.
fn replace_binding_in_arm_body(body: &mut [SorobanStmt], binding: &str, replacement: &SorobanExpr) {
    let Some(last) = body.last_mut() else {
        return;
    };
    let target = match last {
        SorobanStmt::Assign { value, .. } => value,
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => e,
        _ => return,
    };
    if matches!(target, SorobanExpr::NamedLocal(n) if n == binding) {
        *target = replacement.clone();
    }
}

/// Replace artifact let bindings used in match arms with named variant bindings.
/// Pattern: `let var_N = <artifact>` → match arms `EnumVariant(_) => var_N` become
/// `EnumVariant(binding) => binding`, and the let is removed if fully consumed.
fn replace_match_arm_artifact_refs(stmts: &mut Vec<SorobanStmt>, registry: &TypeRegistry) {
    // Collect artifact let bindings: (name, local_index)
    // The name is "var_N" and the Local(N) form may appear in match arm bodies.
    let artifact_lets: Vec<(String, Option<u32>)> = stmts
        .iter()
        .filter_map(|s| match s {
            SorobanStmt::Let {
                name,
                mutable: false,
                value,
                ..
            } if is_artifact_literal(value) && name.starts_with("var_") => {
                let idx = name
                    .strip_prefix("var_")
                    .and_then(|s| s.parse::<u32>().ok());
                Some((name.clone(), idx))
            }
            _ => None,
        })
        .collect();

    let mut consumed_names: Vec<String> = Vec::new();

    for (artifact_name, local_idx) in &artifact_lets {
        let mut all_replaceable = true;
        let mut replacements: Vec<(usize, usize, String)> = Vec::new();

        for (j, stmt) in stmts.iter().enumerate() {
            match stmt {
                SorobanStmt::Match { arms, .. } => {
                    for (arm_idx, arm) in arms.iter().enumerate() {
                        if !arm_body_references_local(&arm.body, artifact_name, *local_idx) {
                            continue;
                        }
                        if let MatchPattern::EnumVariant {
                            type_name,
                            variant,
                            bindings,
                        } = &arm.pattern
                            && bindings.len() == 1
                            && bindings[0] == "_"
                            && let Some(data_type) =
                                registry.find_variant_data_type(type_name, variant)
                        {
                            let is_int_enum = registry
                                .resolve_type_name(&data_type)
                                .is_some_and(|tn| registry.is_integer_enum(&tn));
                            if !is_int_enum {
                                let binding = derive_binding_name(&data_type, registry);
                                replacements.push((j, arm_idx, binding));
                                continue;
                            }
                        }
                        all_replaceable = false;
                    }
                }
                SorobanStmt::Let { name, .. } if name == artifact_name => {}
                _ => {
                    if stmt_references_local(stmt, artifact_name, *local_idx) {
                        all_replaceable = false;
                    }
                }
            }
        }

        if !all_replaceable || replacements.is_empty() {
            continue;
        }

        for &(match_idx, arm_idx, ref binding) in &replacements {
            if let SorobanStmt::Match { arms, .. } = &mut stmts[match_idx] {
                let arm = &mut arms[arm_idx];
                if let MatchPattern::EnumVariant { bindings, .. } = &mut arm.pattern
                    && bindings.len() == 1
                {
                    bindings[0] = binding.clone();
                }
                replace_local_in_body(&mut arm.body, artifact_name, *local_idx, binding);
            }
        }

        if all_replaceable {
            consumed_names.push(artifact_name.clone());
        }
    }

    if !consumed_names.is_empty() {
        stmts.retain(|s| {
            if let SorobanStmt::Let { name, .. } = s {
                !consumed_names.contains(name)
            } else {
                true
            }
        });
    }
}

/// Check if a statement body references a local by name or index.
fn arm_body_references_local(body: &[SorobanStmt], name: &str, idx: Option<u32>) -> bool {
    body.iter().any(|s| stmt_references_local(s, name, idx))
}

fn stmt_references_local(stmt: &SorobanStmt, name: &str, idx: Option<u32>) -> bool {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => expr_references_local(e, name, idx),
        SorobanStmt::Let { value, .. } => expr_references_local(value, name, idx),
        SorobanStmt::Assign { value, .. } => expr_references_local(value, name, idx),
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            expr_references_local(condition, name, idx)
                || then_body
                    .iter()
                    .any(|s| stmt_references_local(s, name, idx))
                || else_body
                    .iter()
                    .any(|s| stmt_references_local(s, name, idx))
        }
        SorobanStmt::Match { scrutinee, arms } => {
            expr_references_local(scrutinee, name, idx)
                || arms
                    .iter()
                    .any(|a| a.body.iter().any(|s| stmt_references_local(s, name, idx)))
        }
        SorobanStmt::Loop { body, .. } => body.iter().any(|s| stmt_references_local(s, name, idx)),
        SorobanStmt::Block(body) => body.iter().any(|s| stmt_references_local(s, name, idx)),
        _ => false,
    }
}

fn expr_references_local(expr: &SorobanExpr, name: &str, idx: Option<u32>) -> bool {
    match expr {
        SorobanExpr::NamedLocal(n) => n == name,
        SorobanExpr::Local(i) => idx == Some(*i),
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
            expr_references_local(a, name, idx) || expr_references_local(b, name, idx)
        }
        SorobanExpr::Not(e)
        | SorobanExpr::ValConvert { value: e, .. }
        | SorobanExpr::CastAs { value: e, .. } => expr_references_local(e, name, idx),
        _ => false,
    }
}

fn replace_local_in_body(
    body: &mut [SorobanStmt],
    old_name: &str,
    old_idx: Option<u32>,
    new_name: &str,
) {
    for stmt in body.iter_mut() {
        match stmt {
            SorobanStmt::Assign { value, .. } => {
                replace_local_in_expr(value, old_name, old_idx, new_name)
            }
            SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
                replace_local_in_expr(e, old_name, old_idx, new_name)
            }
            _ => {}
        }
    }
}

fn replace_local_in_expr(
    expr: &mut SorobanExpr,
    old_name: &str,
    old_idx: Option<u32>,
    new_name: &str,
) {
    match expr {
        SorobanExpr::NamedLocal(n) if n == old_name => {
            *n = new_name.to_string();
        }
        SorobanExpr::Local(i) if old_idx == Some(*i) => {
            *expr = SorobanExpr::NamedLocal(new_name.to_string());
        }
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            replace_local_in_expr(value, old_name, old_idx, new_name);
        }
        _ => {}
    }
}

fn derive_binding_name(type_def: &ScSpecTypeDef, registry: &TypeRegistry) -> String {
    if let Some(type_name) = registry.resolve_type_name(type_def) {
        // Convert CamelCase type name to snake_case for binding
        camel_to_snake_simple(&type_name)
    } else {
        "val".to_string()
    }
}

fn camel_to_snake_simple(s: &str) -> String {
    let mut result = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() {
            if i > 0 {
                result.push('_');
            }
            result.push(c.to_lowercase().next().unwrap());
        } else {
            result.push(c);
        }
    }
    result
}

/// Recover high-level event publish pattern.
/// Transforms `env.events().publish((symbol("name"), topic_vals...), EventStruct { data_fields })`
/// into `EventStruct { topic_fields, data_fields }.publish(&env)` when the event name
/// matches a known `#[contractevent]` struct in the registry.
fn recover_event_publish(
    stmts: &mut [SorobanStmt],
    registry: &TypeRegistry,
    params: &[crate::ir::high_level_ir::FnParam],
) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Expr(expr) | SorobanStmt::Return(Some(expr)) => {
                try_recover_event_expr(expr, registry, params);
            }
            SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
                try_recover_event_expr(value, registry, params);
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                recover_event_publish(then_body, registry, params);
                recover_event_publish(else_body, registry, params);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    recover_event_publish(&mut arm.body, registry, params);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                recover_event_publish(body, registry, params);
            }
            _ => {}
        }
    }
}

fn try_recover_event_expr(
    expr: &mut SorobanExpr,
    registry: &TypeRegistry,
    params: &[crate::ir::high_level_ir::FnParam],
) {
    if let SorobanExpr::PublishEvent {
        event_name,
        topics,
        data,
    } = expr
    {
        if event_name.is_some() {
            return; // Already named
        }

        // Extract inner topic expressions from the wrapping structure.
        // topics is Vec<SorobanExpr>, typically [TupleConstruct/VecConstruct([symbol, val1, ...])]
        let inner_topics: Vec<SorobanExpr> = if topics.len() == 1 {
            match &topics[0] {
                SorobanExpr::TupleConstruct(inner) | SorobanExpr::VecConstruct(inner) => {
                    inner.clone()
                }
                _ => topics.clone(),
            }
        } else {
            topics.clone()
        };

        // First topic should be the event name symbol
        if inner_topics.is_empty() {
            return;
        }
        let event_symbol = match &inner_topics[0] {
            SorobanExpr::SymbolLiteral(s) => s.clone(),
            _ => return,
        };

        // Look up the event in the registry
        let (struct_name, topic_field_names) = match registry.find_event_by_symbol(&event_symbol) {
            Some(info) => info,
            None => return,
        };

        // Topic values are inner_topics[1..] (after the event name symbol)
        let topic_values: Vec<&SorobanExpr> = inner_topics[1..].iter().collect();

        // topic_field_names and topic_values should match in count
        if topic_field_names.len() != topic_values.len() {
            return;
        }

        // Convert VecConstruct data to StructConstruct using event spec field names.
        // Events with multiple data fields are encoded as Vecs at the WASM level
        // (via vec_new_from_linear_memory), not as maps/structs.
        if let SorobanExpr::VecConstruct(elements) = data.as_ref() {
            // Get the event spec's non-topic field names
            if let Some(event_spec) = registry.get_event(&struct_name) {
                let data_field_names: Vec<String> = event_spec
                    .params
                    .iter()
                    .filter(|p| {
                        p.location != stellar_xdr::curr::ScSpecEventParamLocationV0::TopicList
                    })
                    .filter_map(|p| p.name.to_utf8_string().ok())
                    .collect();

                if data_field_names.len() == elements.len() {
                    let struct_fields: Vec<(String, SorobanExpr)> = data_field_names
                        .iter()
                        .zip(elements.iter())
                        .map(|(name, val)| (name.clone(), val.clone()))
                        .collect();
                    **data = SorobanExpr::StructConstruct {
                        type_name: struct_name.clone(),
                        fields: struct_fields,
                    };
                }
            }
        }

        // The data should be a StructConstruct — merge topic fields into it
        if let SorobanExpr::StructConstruct {
            type_name,
            fields: data_fields,
        } = data.as_mut()
        {
            // Prepend topic fields to the data fields
            let mut all_fields: Vec<(String, SorobanExpr)> = topic_field_names
                .iter()
                .zip(topic_values.iter())
                .map(|(name, val)| (name.clone(), (*val).clone()))
                .collect();
            all_fields.append(data_fields);

            // Fix MuxedAddress → Address conversion: when a field value is a Param
            // whose type is MuxedAddress but the event field type is Address, wrap
            // with .address() to extract the Address from the MuxedAddress.
            if let Some(event_spec) = registry.get_event(&struct_name) {
                for (field_name, field_val) in all_fields.iter_mut() {
                    if let SorobanExpr::Param(param_name) = field_val {
                        // Check if the param type is MuxedAddress
                        let is_muxed_param = params.iter().any(|p| {
                            p.name == *param_name
                                && matches!(
                                    p.type_def,
                                    stellar_xdr::curr::ScSpecTypeDef::MuxedAddress
                                )
                        });
                        // Check if the event field type is Address
                        let is_address_field = event_spec.params.iter().any(|p| {
                            p.name.to_utf8_string().ok().as_deref() == Some(field_name.as_str())
                                && matches!(p.type_, stellar_xdr::curr::ScSpecTypeDef::Address)
                        });
                        if is_muxed_param && is_address_field {
                            *field_val = SorobanExpr::MethodCall {
                                object: Box::new(SorobanExpr::Param(param_name.clone())),
                                method: "address".to_string(),
                                args: vec![],
                            };
                        }
                    }
                }
            }

            // Set the type name to the event struct name
            *type_name = struct_name.clone();
            *data_fields = all_fields;
            *event_name = Some(struct_name);
            // Clear topics — they're now in the struct
            topics.clear();
        }
    }
}

/// Recover enum variant construction from tuple patterns.
///
/// The Soroban SDK encodes `#[contracttype] enum` keys as tuples:
/// - Data-carrying variants: `(SymbolLiteral("Variant"), data)` → `Type::Variant(data)`
/// - Void variants: `SymbolLiteral("Variant")` → `Type::Variant`
///
/// This pass walks all expressions and replaces matching patterns with `EnumConstruct`.
/// Also handles indirect patterns where `let x = SymbolLiteral("Variant")` is followed
/// by `(x, data)` in later statements — inlines the symbol into the tuple and converts.
fn recover_enum_key_construction(stmts: &mut [SorobanStmt], registry: &TypeRegistry) {
    use std::collections::HashMap;

    // Pass 1: Direct pattern matching (SymbolLiteral directly in tuples)
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
                recover_enum_key_in_expr(e, registry);
            }
            SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
                recover_enum_key_in_expr(value, registry);
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                recover_enum_key_in_expr(condition, registry);
                recover_enum_key_construction(then_body, registry);
                recover_enum_key_construction(else_body, registry);
            }
            SorobanStmt::Match {
                scrutinee, arms, ..
            } => {
                recover_enum_key_in_expr(scrutinee, registry);
                for arm in arms.iter_mut() {
                    recover_enum_key_construction(&mut arm.body, registry);
                }
            }
            SorobanStmt::Loop { body, .. } => {
                recover_enum_key_construction(body, registry);
            }
            SorobanStmt::Block(body) => {
                recover_enum_key_construction(body, registry);
            }
            _ => {}
        }
    }

    // Pass 2: Indirect pattern — `let x = symbol_short!("Variant"); let y = (x, data)`
    // Collect symbol bindings first
    let mut symbol_bindings: HashMap<String, String> = HashMap::new();
    for stmt in stmts.iter() {
        if let SorobanStmt::Let {
            name,
            value: SorobanExpr::SymbolLiteral(sym),
            ..
        } = stmt
        {
            symbol_bindings.insert(name.clone(), sym.clone());
        }
    }

    if symbol_bindings.is_empty() {
        return;
    }

    // Convert tuples with indirect symbol references
    for stmt in stmts.iter_mut() {
        resolve_indirect_enum_key_in_stmt(stmt, &symbol_bindings, registry);
    }
}

/// Resolve indirect enum key patterns in a statement tree.
/// When a tuple `(NamedLocal("x"), data)` references a symbol binding
/// `let x = symbol_short!("Variant")`, convert to `EnumConstruct`.
fn resolve_indirect_enum_key_in_stmt(
    stmt: &mut SorobanStmt,
    symbol_bindings: &std::collections::HashMap<String, String>,
    registry: &TypeRegistry,
) {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
            resolve_indirect_enum_key_in_expr(e, symbol_bindings, registry);
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            resolve_indirect_enum_key_in_expr(value, symbol_bindings, registry);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            resolve_indirect_enum_key_in_expr(condition, symbol_bindings, registry);
            for s in then_body.iter_mut() {
                resolve_indirect_enum_key_in_stmt(s, symbol_bindings, registry);
            }
            for s in else_body.iter_mut() {
                resolve_indirect_enum_key_in_stmt(s, symbol_bindings, registry);
            }
        }
        SorobanStmt::Match {
            scrutinee, arms, ..
        } => {
            resolve_indirect_enum_key_in_expr(scrutinee, symbol_bindings, registry);
            for arm in arms.iter_mut() {
                for s in arm.body.iter_mut() {
                    resolve_indirect_enum_key_in_stmt(s, symbol_bindings, registry);
                }
            }
        }
        SorobanStmt::Loop { body, .. } => {
            for s in body.iter_mut() {
                resolve_indirect_enum_key_in_stmt(s, symbol_bindings, registry);
            }
        }
        SorobanStmt::Block(body) => {
            for s in body.iter_mut() {
                resolve_indirect_enum_key_in_stmt(s, symbol_bindings, registry);
            }
        }
        _ => {}
    }
}

/// Resolve indirect enum key patterns in an expression.
fn resolve_indirect_enum_key_in_expr(
    expr: &mut SorobanExpr,
    symbol_bindings: &std::collections::HashMap<String, String>,
    registry: &TypeRegistry,
) {
    // Try to convert this expression
    let fields = match expr {
        SorobanExpr::TupleConstruct(f) | SorobanExpr::VecConstruct(f) => Some(f),
        _ => None,
    };
    if let Some(fields) = fields
        && fields.len() == 2
    {
        let variant_name = match &fields[0] {
            SorobanExpr::NamedLocal(name) | SorobanExpr::Param(name) => {
                symbol_bindings.get(name).cloned()
            }
            // Local(N) maps to `var_N` bindings
            SorobanExpr::Local(idx) => {
                let var_name = format!("var_{}", idx);
                symbol_bindings.get(&var_name).cloned()
            }
            _ => None,
        };
        if let Some(variant_name) = variant_name
            && let Some((union_name, has_data)) = registry.find_union_variant(&variant_name)
            && has_data
        {
            *expr = SorobanExpr::EnumConstruct {
                type_name: union_name,
                variant: variant_name,
                fields: vec![fields[1].clone()],
            };
            return;
        }
    }

    // Recurse into sub-expressions (only the ones commonly containing tuple patterns)
    match expr {
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => {
            resolve_indirect_enum_key_in_expr(key, symbol_bindings, registry);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            resolve_indirect_enum_key_in_expr(key, symbol_bindings, registry);
            resolve_indirect_enum_key_in_expr(value, symbol_bindings, registry);
        }
        SorobanExpr::StorageExtendTtl { key, .. } => {
            resolve_indirect_enum_key_in_expr(key, symbol_bindings, registry);
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            resolve_indirect_enum_key_in_expr(object, symbol_bindings, registry);
            for arg in args.iter_mut() {
                resolve_indirect_enum_key_in_expr(arg, symbol_bindings, registry);
            }
        }
        SorobanExpr::TupleConstruct(fields) | SorobanExpr::VecConstruct(fields) => {
            for field in fields.iter_mut() {
                resolve_indirect_enum_key_in_expr(field, symbol_bindings, registry);
            }
        }
        _ => {}
    }
}

/// Recursively walk an expression tree, replacing tuple enum key patterns with EnumConstruct.
fn recover_enum_key_in_expr(expr: &mut SorobanExpr, registry: &TypeRegistry) {
    // First, try to convert this expression itself
    if let Some(replacement) = try_convert_enum_key(expr, registry) {
        *expr = replacement;
        return;
    }

    // Recurse into sub-expressions
    match expr {
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => {
            recover_enum_key_in_expr(key, registry);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            recover_enum_key_in_expr(key, registry);
            recover_enum_key_in_expr(value, registry);
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            recover_enum_key_in_expr(key, registry);
            recover_enum_key_in_expr(threshold, registry);
            recover_enum_key_in_expr(extend_to, registry);
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            recover_enum_key_in_expr(object, registry);
            for arg in args.iter_mut() {
                recover_enum_key_in_expr(arg, registry);
            }
        }
        SorobanExpr::TupleConstruct(fields) | SorobanExpr::VecConstruct(fields) => {
            for field in fields.iter_mut() {
                recover_enum_key_in_expr(field, registry);
            }
        }
        SorobanExpr::Not(inner)
        | SorobanExpr::ValConvert { value: inner, .. }
        | SorobanExpr::CastAs { value: inner, .. }
        | SorobanExpr::ErrorFromCode(inner) => {
            recover_enum_key_in_expr(inner, registry);
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
        | SorobanExpr::Or(a, b) => {
            recover_enum_key_in_expr(a, registry);
            recover_enum_key_in_expr(b, registry);
        }
        SorobanExpr::InvokeContract { args, .. } | SorobanExpr::TryInvokeContract { args, .. } => {
            for arg in args.iter_mut() {
                recover_enum_key_in_expr(arg, registry);
            }
        }
        // The admin-auth idiom threads a keyed load into the auth target
        // (`get(&Admin).unwrap().require_auth()`) — recurse so its key
        // upgrades like any other storage key.
        SorobanExpr::RequireAuth(target) => {
            recover_enum_key_in_expr(target, registry);
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            recover_enum_key_in_expr(address, registry);
            recover_enum_key_in_expr(args, registry);
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, val) in fields.iter_mut() {
                recover_enum_key_in_expr(val, registry);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for field in fields.iter_mut() {
                recover_enum_key_in_expr(field, registry);
            }
        }
        SorobanExpr::FieldAccess { object, .. } => {
            recover_enum_key_in_expr(object, registry);
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics.iter_mut() {
                recover_enum_key_in_expr(t, registry);
            }
            recover_enum_key_in_expr(data, registry);
        }
        _ => {}
    }
}

/// Try to convert a single expression to an EnumConstruct.
/// Returns Some(replacement) if the expression matches a known union variant pattern.
fn try_convert_enum_key(expr: &SorobanExpr, registry: &TypeRegistry) -> Option<SorobanExpr> {
    match expr {
        // Data-carrying variant: (SymbolLiteral("Variant"), data) → Type::Variant(data)
        SorobanExpr::TupleConstruct(fields) | SorobanExpr::VecConstruct(fields)
            if fields.len() == 2 =>
        {
            if let SorobanExpr::SymbolLiteral(variant_name) = &fields[0]
                && let Some((union_name, has_data)) = registry.find_union_variant(variant_name)
                && has_data
            {
                return Some(SorobanExpr::EnumConstruct {
                    type_name: union_name,
                    variant: variant_name.clone(),
                    fields: vec![fields[1].clone()],
                });
            }
            None
        }
        // Unit variant in its host encoding: Vec[SymbolLiteral("Variant")] →
        // Type::Variant. `#[contracttype]` unions vec-wrap unit variants too, so
        // a recovered key arrives as a 1-element vec; without this arm only the
        // inner symbol upgrades, leaving a double-wrapped `vec![&env, Key::V]`.
        SorobanExpr::TupleConstruct(fields) | SorobanExpr::VecConstruct(fields)
            if fields.len() == 1 =>
        {
            if let SorobanExpr::SymbolLiteral(variant_name) = &fields[0]
                && let Some((union_name, has_data)) = registry.find_union_variant(variant_name)
                && !has_data
            {
                return Some(SorobanExpr::EnumConstruct {
                    type_name: union_name,
                    variant: variant_name.clone(),
                    fields: vec![],
                });
            }
            None
        }
        // Void variant used as storage key: SymbolLiteral("Variant") → Type::Variant
        SorobanExpr::SymbolLiteral(name) => {
            if let Some((union_name, has_data)) = registry.find_union_variant(name)
                && !has_data
            {
                return Some(SorobanExpr::EnumConstruct {
                    type_name: union_name,
                    variant: name.clone(),
                    fields: vec![],
                });
            }
            None
        }
        _ => None,
    }
}

/// Check if a type is numeric (integer or float).
fn is_numeric_type(ty: &ScSpecTypeDef) -> bool {
    matches!(
        ty,
        ScSpecTypeDef::I32
            | ScSpecTypeDef::U32
            | ScSpecTypeDef::I64
            | ScSpecTypeDef::U64
            | ScSpecTypeDef::I128
            | ScSpecTypeDef::U128
            | ScSpecTypeDef::I256
            | ScSpecTypeDef::U256
            | ScSpecTypeDef::Timepoint
            | ScSpecTypeDef::Duration
    )
}

/// Replace BoolLiteral(false) → 0 and BoolLiteral(true) → 1 in all return/tail positions
/// of a function body. Recurses into if/match/loop/block arms.
/// This fixes Val-decoded 0x00/0x01 that should be numeric zero/one in non-bool functions.
fn fix_bool_literal_returns(stmts: &mut [SorobanStmt]) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
                fix_bool_literal_expr(e);
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                fix_bool_literal_returns(then_body);
                fix_bool_literal_returns(else_body);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    fix_bool_literal_returns(&mut arm.body);
                }
            }
            SorobanStmt::Loop { body, .. } | SorobanStmt::Block(body) => {
                fix_bool_literal_returns(body);
            }
            _ => {}
        }
    }
}

fn fix_bool_literal_expr(e: &mut SorobanExpr) {
    match e {
        SorobanExpr::BoolLiteral(false) => *e = SorobanExpr::I64Literal(0),
        SorobanExpr::BoolLiteral(true) => *e = SorobanExpr::I64Literal(1),
        // ValConvert { BoolLiteral(false), "i128" } → I64Literal(0)
        SorobanExpr::ValConvert { value, .. }
            if matches!(value.as_ref(), SorobanExpr::BoolLiteral(_)) =>
        {
            let val = matches!(value.as_ref(), SorobanExpr::BoolLiteral(true));
            *e = SorobanExpr::I64Literal(if val { 1 } else { 0 });
        }
        _ => {}
    }
}

/// Strip `Return(Some(expr))` from void functions where the returned value
/// is a pure expression (Param, Local, NamedLocal, literal). These are leftovers
/// Convert VecConstruct to TupleConstruct in tail position for tuple-returning functions.
///
/// The SDK encodes tuple returns as `vec_new_from_linear_memory`, producing
/// `VecConstruct([Env, val1, val2, ...])` in the IR. For functions whose spec
/// declares a tuple return type, convert the tail VecConstruct to TupleConstruct
/// by stripping the leading `Env` element.
fn convert_vec_to_tuple_return(stmts: &mut [SorobanStmt], expected_elements: usize) {
    // Convert every explicit `return vec![..]` — the return is not always the last
    // statement (a trailing dead `panic!()` from the WASM `unreachable` can follow
    // it), so scan rather than only checking the tail.
    for stmt in stmts.iter_mut() {
        if let SorobanStmt::Return(Some(expr)) = stmt {
            convert_vec_expr_to_tuple(expr, expected_elements);
        }
    }
    // Also handle a tail-position implicit return (`vec![..]` as the last expr).
    if let Some(SorobanStmt::Expr(expr)) = stmts.last_mut() {
        convert_vec_expr_to_tuple(expr, expected_elements);
    }
}

/// Type the operands that participate in i128/u128 arithmetic. Recovered share-math
/// otherwise leaves values defaulting to `soroban_sdk::Val`, which doesn't type-check:
///   - an untyped `invoke_contract` (a token `balance(...)`) → `return_type = i128`;
///   - a storage get inline in the arithmetic → wrapped so codegen emits a
///     `get::<_, i128>` turbofish (Rust won't infer the generic value type);
///   - a `let` binding whose value is a storage get and whose name feeds i128
///     arithmetic → its value is likewise typed, so the binding is `i128`.
fn coerce_i128_invoke_types(stmts: &mut [SorobanStmt], params: &[FnParam]) -> I128Use {
    // Retype invokes and inline-arithmetic gets, collecting the storage keys read as
    // i128 (the caller types every get of those keys, including in other functions).
    let mut used = I128Use::default();
    coerce_i128_collect(stmts, params, &mut used);
    used
}

/// What a function's i128 arithmetic depends on, gathered to type the storage gets
/// that feed it.
#[derive(Default)]
struct I128Use {
    /// Names of locals referenced as i128 operands.
    #[allow(dead_code)]
    locals: std::collections::HashSet<String>,
    /// Storage keys read as i128 (e.g. `DataKey::ReserveA`).
    keys: Vec<SorobanExpr>,
}

fn coerce_i128_collect(stmts: &mut [SorobanStmt], params: &[FnParam], used: &mut I128Use) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
                coerce_i128_invoke_in_expr(e, params, used)
            }
            SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
                coerce_i128_invoke_in_expr(value, params, used)
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                coerce_i128_invoke_in_expr(condition, params, used);
                coerce_i128_collect(then_body, params, used);
                coerce_i128_collect(else_body, params, used);
            }
            SorobanStmt::Match { scrutinee, arms } => {
                coerce_i128_invoke_in_expr(scrutinee, params, used);
                for arm in arms {
                    coerce_i128_collect(&mut arm.body, params, used);
                }
            }
            SorobanStmt::Loop { body }
            | SorobanStmt::Block(body)
            | SorobanStmt::For { body, .. } => coerce_i128_collect(body, params, used),
            _ => {}
        }
    }
}

/// Wrap every storage get of a known-i128 key (collected from i128 arithmetic) so
/// codegen emits a `get::<_, i128>` turbofish. A get's generic value type is not
/// inferred from a tuple return or a `let` binding alone, so this types the reads
/// that arithmetic didn't already reach (`get_rsrvs`, dead `let reserve_a`, …).
fn type_i128_key_gets(stmts: &mut [SorobanStmt], keys: &[SorobanExpr]) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
                type_i128_key_gets_in_expr(e, keys)
            }
            SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
                type_i128_key_gets_in_expr(value, keys)
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                type_i128_key_gets_in_expr(condition, keys);
                type_i128_key_gets(then_body, keys);
                type_i128_key_gets(else_body, keys);
            }
            SorobanStmt::Match { scrutinee, arms } => {
                type_i128_key_gets_in_expr(scrutinee, keys);
                for arm in arms {
                    type_i128_key_gets(&mut arm.body, keys);
                }
            }
            SorobanStmt::Loop { body }
            | SorobanStmt::Block(body)
            | SorobanStmt::For { body, .. } => type_i128_key_gets(body, keys),
            _ => {}
        }
    }
}

fn type_i128_key_gets_in_expr(e: &mut SorobanExpr, keys: &[SorobanExpr]) {
    // A bare get of an i128 key → wrap it (don't recurse into the new wrapper).
    if let SorobanExpr::StorageGet { key, .. } = e
        && keys.contains(&**key)
    {
        let inner = std::mem::replace(e, SorobanExpr::Void);
        *e = SorobanExpr::CastAs {
            value: Box::new(inner),
            target_type: "i128".to_string(),
        };
        return;
    }
    // An already-typed get → leave as-is (avoid double-wrapping).
    if let SorobanExpr::CastAs { value, .. } = e
        && matches!(value.as_ref(), SorobanExpr::StorageGet { .. })
    {
        return;
    }
    match e {
        SorobanExpr::InvokeContract { address, args, .. }
        | SorobanExpr::TryInvokeContract { address, args, .. } => {
            type_i128_key_gets_in_expr(address, keys);
            for a in args.iter_mut() {
                type_i128_key_gets_in_expr(a, keys);
            }
        }
        _ => {
            for c in child_exprs_mut(e) {
                type_i128_key_gets_in_expr(c, keys);
            }
        }
    }
}

fn coerce_i128_invoke_in_expr(e: &mut SorobanExpr, params: &[FnParam], used: &mut I128Use) {
    // Recurse into every child first — including `invoke_contract` args, which the
    // shared `child_exprs_mut` walker skips but which hold the share-math (e.g. a
    // `(amount * total / reserve).into_val()` transfer argument).
    match e {
        SorobanExpr::InvokeContract { address, args, .. }
        | SorobanExpr::TryInvokeContract { address, args, .. } => {
            coerce_i128_invoke_in_expr(address, params, used);
            for a in args.iter_mut() {
                coerce_i128_invoke_in_expr(a, params, used);
            }
        }
        _ => {
            for c in child_exprs_mut(e) {
                coerce_i128_invoke_in_expr(c, params, used);
            }
        }
    }
    // After recursion, if this node is i128 arithmetic, type its operands i128.
    if matches!(
        e,
        SorobanExpr::Add(..)
            | SorobanExpr::Sub(..)
            | SorobanExpr::Mul(..)
            | SorobanExpr::Div(..)
            | SorobanExpr::Rem(..)
    ) && expr_is_i128(e, params)
    {
        force_i128_deep(e, used);
    }
}

/// True when `e` is statically known to be 128-bit: a 128-bit literal, a 128-bit
/// parameter, an `invoke_contract` already typed 128-bit, or arithmetic with such
/// an operand.
fn expr_is_i128(e: &SorobanExpr, params: &[FnParam]) -> bool {
    match e {
        SorobanExpr::I128Literal(_) | SorobanExpr::U128Literal(_) => true,
        SorobanExpr::Param(n) => params.iter().any(|p| {
            p.name == *n && matches!(p.type_def, ScSpecTypeDef::I128 | ScSpecTypeDef::U128)
        }),
        SorobanExpr::InvokeContract {
            return_type: Some(t),
            ..
        }
        | SorobanExpr::TryInvokeContract {
            return_type: Some(t),
            ..
        } => t == "i128" || t == "u128",
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Rem(a, b) => expr_is_i128(a, params) || expr_is_i128(b, params),
        _ => false,
    }
}

/// Type every operand within an i128 arithmetic subtree as `i128`, and record the
/// names of local references so their `let` bindings can be typed too. Only recurses
/// through arithmetic nodes — a nested non-arithmetic child keeps its own type.
/// Untyped `invoke_contract`s get `return_type = i128`; storage gets (whose generic
/// value type Rust will not infer from arithmetic alone) get wrapped so codegen can
/// emit a `get::<_, i128>` turbofish.
fn force_i128_deep(e: &mut SorobanExpr, used: &mut I128Use) {
    match e {
        SorobanExpr::InvokeContract { return_type, .. }
        | SorobanExpr::TryInvokeContract { return_type, .. }
            if return_type.is_none() =>
        {
            *return_type = Some("i128".to_string());
        }
        SorobanExpr::StorageGet { key, .. } => {
            used.keys.push((**key).clone());
            let inner = std::mem::replace(e, SorobanExpr::Void);
            *e = SorobanExpr::CastAs {
                value: Box::new(inner),
                target_type: "i128".to_string(),
            };
        }
        // Record locals used in i128 arithmetic so `type_i128_let_bindings` can type
        // their `let name = <storage get>` declarations.
        SorobanExpr::NamedLocal(name) => {
            used.locals.insert(name.clone());
        }
        SorobanExpr::Local(idx) => {
            used.locals.insert(format!("var_{idx}"));
        }
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Rem(a, b) => {
            force_i128_deep(a, used);
            force_i128_deep(b, used);
        }
        _ => {}
    }
}

fn convert_vec_expr_to_tuple(expr: &mut SorobanExpr, expected_elements: usize) {
    if let SorobanExpr::VecConstruct(elements) = expr {
        // Strip leading Env element: vec![&env, val1, val2] → (val1, val2)
        let data_elements: Vec<SorobanExpr> = elements
            .iter()
            .filter(|e| !matches!(e, SorobanExpr::Env))
            .cloned()
            .collect();

        if data_elements.len() == expected_elements {
            *expr = SorobanExpr::TupleConstruct(data_elements);
        }
    }
}

/// from the lifter's parameter validation recovery. Preserves side-effectful returns
/// as standalone `Expr(e)` statements.
fn strip_returns_in_void_fn(stmts: &mut Vec<SorobanStmt>) {
    let mut i = 0;
    while i < stmts.len() {
        match &stmts[i] {
            // Remove pure return values (leftover from parameter validation)
            SorobanStmt::Return(Some(e)) if is_pure_value(e) => {
                stmts.remove(i);
                continue;
            }
            // Side-effectful return → keep as Expr
            SorobanStmt::Return(Some(_)) => {
                if let SorobanStmt::Return(Some(e)) =
                    std::mem::replace(&mut stmts[i], SorobanStmt::Return(None))
                {
                    stmts[i] = SorobanStmt::Expr(e);
                }
            }
            // Remove standalone pure expressions (artifact references to params/locals)
            SorobanStmt::Expr(e) if is_pure_value(e) => {
                stmts.remove(i);
                continue;
            }
            _ => {}
        }
        // Recurse into nested bodies
        match &mut stmts[i] {
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                strip_returns_in_void_fn(then_body);
                strip_returns_in_void_fn(else_body);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    strip_returns_in_void_fn(&mut arm.body);
                }
            }
            SorobanStmt::Loop { body, .. } | SorobanStmt::Block(body) => {
                strip_returns_in_void_fn(body);
            }
            _ => {}
        }
        i += 1;
    }
}

/// Drop let bindings that are no longer referenced in subsequent statements.
/// Converts `let var_N = side_effect();` to `side_effect();` when var_N is dead.
/// Removes pure dead lets entirely.
fn drop_dead_lets(stmts: &mut Vec<SorobanStmt>) {
    let mut i = 0;
    while i < stmts.len() {
        if let SorobanStmt::Let { name, value, .. } = &stmts[i]
            && !name_referenced_in(&stmts[i + 1..], name)
        {
            if is_pure_value(value) {
                stmts.remove(i);
                continue;
            } else {
                // Side-effectful → keep as Expr
                if let SorobanStmt::Let { value, .. } =
                    std::mem::replace(&mut stmts[i], SorobanStmt::Return(None))
                {
                    stmts[i] = SorobanStmt::Expr(value);
                }
            }
        }
        i += 1;
    }
}

/// Check if a variable name appears anywhere in a list of statements.
fn name_referenced_in(stmts: &[SorobanStmt], name: &str) -> bool {
    stmts.iter().any(|s| stmt_references_name(s, name))
}

fn stmt_references_name(stmt: &SorobanStmt, name: &str) -> bool {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => expr_references_name(e, name),
        SorobanStmt::Let { value, .. } => expr_references_name(value, name),
        SorobanStmt::Assign { value, target, .. } => {
            target == name || expr_references_name(value, name)
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            expr_references_name(condition, name)
                || name_referenced_in(then_body, name)
                || name_referenced_in(else_body, name)
        }
        SorobanStmt::Match { scrutinee, arms } => {
            expr_references_name(scrutinee, name)
                || arms.iter().any(|a| name_referenced_in(&a.body, name))
        }
        SorobanStmt::Loop { body, .. } | SorobanStmt::Block(body) => name_referenced_in(body, name),
        _ => false,
    }
}

fn expr_references_name(expr: &SorobanExpr, name: &str) -> bool {
    match expr {
        SorobanExpr::NamedLocal(n) | SorobanExpr::Param(n) => n == name,
        SorobanExpr::Local(idx) => format!("var_{}", idx) == name,
        // Conservatively: any complex expression might reference the name.
        // This is only used for dead-let cleanup in void functions,
        // so a false positive just preserves the let binding.
        _ => true,
    }
}

/// Check if an expression is a pure value (no side effects, safe to discard).
fn is_pure_value(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::Param(_)
        | SorobanExpr::Local(_)
        | SorobanExpr::NamedLocal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U32Literal(_)
        | SorobanExpr::I64Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::I128Literal(_)
        | SorobanExpr::U128Literal(_)
        | SorobanExpr::BoolLiteral(_)
        | SorobanExpr::UnknownVal => true,
        SorobanExpr::ValConvert { value, .. } => is_pure_value(value),
        // TupleConstruct/VecConstruct is pure when all elements are pure
        SorobanExpr::TupleConstruct(fields) | SorobanExpr::VecConstruct(fields) => {
            fields.iter().all(is_pure_value)
        }
        _ => false,
    }
}

// Stage 4q: Replace incomplete struct reconstructions with parameter references
// ---------------------------------------------------------------------------

/// Check if a struct construction has artifact fields (UnknownVal, Local(N), or unresolved var_N).
fn struct_has_artifacts(fields: &[(String, SorobanExpr)]) -> bool {
    fields.iter().any(|(_, v)| {
        matches!(v, SorobanExpr::UnknownVal)
            || matches!(v, SorobanExpr::Local(_))
            || matches!(v, SorobanExpr::NamedLocal(n) if n.starts_with("var_"))
    })
}

/// Replace incomplete struct reconstructions with parameter references.
/// When StructConstruct has artifact fields and a parameter of the same type exists
/// (unambiguously), replace the entire StructConstruct with Param(name).
fn replace_incomplete_struct_with_param(
    body: &mut [SorobanStmt],
    params: &[FnParam],
    registry: &TypeRegistry,
) {
    if params.is_empty() {
        return;
    }
    for stmt in body.iter_mut() {
        replace_incomplete_struct_in_stmt(stmt, params, registry);
    }
}

fn replace_incomplete_struct_in_stmt(
    stmt: &mut SorobanStmt,
    params: &[FnParam],
    registry: &TypeRegistry,
) {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
            replace_incomplete_struct_in_expr(e, params, registry);
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            replace_incomplete_struct_in_expr(value, params, registry);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            replace_incomplete_struct_in_expr(condition, params, registry);
            for s in then_body.iter_mut() {
                replace_incomplete_struct_in_stmt(s, params, registry);
            }
            for s in else_body.iter_mut() {
                replace_incomplete_struct_in_stmt(s, params, registry);
            }
        }
        SorobanStmt::Match { scrutinee, arms } => {
            replace_incomplete_struct_in_expr(scrutinee, params, registry);
            for arm in arms.iter_mut() {
                for s in arm.body.iter_mut() {
                    replace_incomplete_struct_in_stmt(s, params, registry);
                }
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            for s in body.iter_mut() {
                replace_incomplete_struct_in_stmt(s, params, registry);
            }
        }
        _ => {}
    }
}

fn replace_incomplete_struct_in_expr(
    expr: &mut SorobanExpr,
    params: &[FnParam],
    registry: &TypeRegistry,
) {
    // First, try to replace this expression itself if it's an incomplete StructConstruct
    if let SorobanExpr::StructConstruct { type_name, fields } = expr
        && struct_has_artifacts(fields)
    {
        // Find params whose type resolves to this struct type
        let matching: Vec<&FnParam> = params
            .iter()
            .filter(|p| {
                registry.resolve_type_name(&p.type_def).as_deref() == Some(type_name.as_str())
            })
            .collect();
        // Only replace when exactly one param matches (no ambiguity)
        if matching.len() == 1 {
            cov_mark::hit!(stage_4q_struct_replaced_with_param);
            *expr = SorobanExpr::Param(matching[0].name.clone());
            return;
        }
    }

    // Recurse into sub-expressions
    match expr {
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields.iter_mut() {
                replace_incomplete_struct_in_expr(v, params, registry);
            }
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            replace_incomplete_struct_in_expr(key, params, registry);
            replace_incomplete_struct_in_expr(value, params, registry);
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => {
            replace_incomplete_struct_in_expr(key, params, registry);
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
        | SorobanExpr::Or(a, b) => {
            replace_incomplete_struct_in_expr(a, params, registry);
            replace_incomplete_struct_in_expr(b, params, registry);
        }
        SorobanExpr::Not(a)
        | SorobanExpr::FieldAccess { object: a, .. }
        | SorobanExpr::ValConvert { value: a, .. }
        | SorobanExpr::CastAs { value: a, .. } => {
            replace_incomplete_struct_in_expr(a, params, registry);
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            replace_incomplete_struct_in_expr(object, params, registry);
            for a in args.iter_mut() {
                replace_incomplete_struct_in_expr(a, params, registry);
            }
        }
        SorobanExpr::InvokeContract { args, .. } | SorobanExpr::TryInvokeContract { args, .. } => {
            for a in args.iter_mut() {
                replace_incomplete_struct_in_expr(a, params, registry);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for f in fields.iter_mut() {
                replace_incomplete_struct_in_expr(f, params, registry);
            }
        }
        SorobanExpr::TupleConstruct(elems) | SorobanExpr::VecConstruct(elems) => {
            for e in elems.iter_mut() {
                replace_incomplete_struct_in_expr(e, params, registry);
            }
        }
        SorobanExpr::MapConstruct(entries) => {
            for (k, v) in entries.iter_mut() {
                replace_incomplete_struct_in_expr(k, params, registry);
                replace_incomplete_struct_in_expr(v, params, registry);
            }
        }
        SorobanExpr::RequireAuth(inner)
        | SorobanExpr::RequireAuthForArgs { address: inner, .. } => {
            replace_incomplete_struct_in_expr(inner, params, registry);
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics.iter_mut() {
                replace_incomplete_struct_in_expr(t, params, registry);
            }
            replace_incomplete_struct_in_expr(data, params, registry);
        }
        _ => {}
    }
}

// Stage 4s: Recover map_unpack getter pattern
// ---------------------------------------------------------------------------

/// Recover `if has(key) { map_unpack(get(key).unwrap(), keys_ptr, ...) }` patterns
/// in getter functions. When the function returns a type that matches a field of the
/// unpacked struct, replace the body with `storage.get(key).unwrap().field`.
fn recover_map_unpack_getter(
    func: &mut crate::ir::high_level_ir::ContractFn,
    registry: &TypeRegistry,
) {
    let ret_type = match &func.return_type {
        Some(t) => t.clone(),
        None => return,
    };

    // Look for the pattern: body is a single If with StorageHas condition
    // whose then_body contains a map_unpack_to_linear_memory call.
    if func.body.len() != 1 {
        return;
    }

    let (storage_type, key_expr, unpack_count) = match &func.body[0] {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } if else_body.is_empty() => {
            // Condition must be StorageHas
            let (st, key) = match condition {
                SorobanExpr::StorageHas {
                    storage_type, key, ..
                } => (*storage_type, key.as_ref().clone()),
                _ => return,
            };
            // Try to extract count from map_unpack_to_linear_memory call (if present)
            let map_unpack_count = then_body.iter().find_map(|s| match s {
                SorobanStmt::Expr(SorobanExpr::RawHostCall { function, args, .. })
                    if function == "map_unpack_to_linear_memory" =>
                {
                    args.last().and_then(|a| match a {
                        SorobanExpr::I32Literal(n) => Some(*n as usize),
                        SorobanExpr::U32Literal(n) => Some(*n as usize),
                        _ => None,
                    })
                }
                SorobanStmt::Expr(SorobanExpr::MethodCall { method, args, .. })
                    if method == "map_unpack_to_linear_memory" =>
                {
                    args.last().and_then(|a| match a {
                        SorobanExpr::I32Literal(n) => Some(*n as usize),
                        SorobanExpr::U32Literal(n) => Some(*n as usize),
                        _ => None,
                    })
                }
                _ => None,
            });
            // Fallback: if no map_unpack count, check if the body has a StorageGet
            // with matching key (the FieldAccess pass-through resolved the unpack).
            // Only for pure getters (no non-env params) to avoid matching functions
            // like increment(env, incr) that read-modify-write.
            // Use count=0 to signal "no specific count filter".
            let is_pure_getter = func.params.is_empty();
            let count = map_unpack_count.unwrap_or_else(|| {
                if !is_pure_getter {
                    return usize::MAX;
                }
                let has_matching_get = then_body.iter().any(|s| {
                    fn expr_has_storage_get(e: &SorobanExpr) -> bool {
                        matches!(e, SorobanExpr::StorageGet { .. })
                            || matches!(e, SorobanExpr::MethodCall { object, method, .. }
                                if method == "unwrap" && expr_has_storage_get(object))
                    }
                    match s {
                        SorobanStmt::Let { value, .. } => expr_has_storage_get(value),
                        SorobanStmt::Expr(e) => expr_has_storage_get(e),
                        _ => false,
                    }
                });
                if has_matching_get { 0 } else { usize::MAX }
            });
            if count == usize::MAX {
                return;
            }
            (st, key, count)
        }
        _ => return,
    };

    // Case 1: Return type IS a known struct (optionally matching field count).
    // The function returns the whole struct (e.g., get_state() -> State).
    if let Some(ret_name) = registry.resolve_type_name(&ret_type)
        && let Some(spec) = registry.structs.get(&ret_name)
        && (unpack_count == 0 || spec.fields.len() == unpack_count)
    {
        let get_expr = SorobanExpr::StorageGet {
            storage_type,
            key: Box::new(key_expr.clone()),
            unwrap: true,
            on_missing: None,
        };
        cov_mark::hit!(stage_4s_getter_recovered);
        func.body = vec![SorobanStmt::Return(Some(get_expr))];
        func.takes_env = true;
        return;
    }

    // Case 2: Return type matches a FIELD of a struct.
    // For getter functions, the return type uniquely identifies which field is read.
    let ret_type_str = spec_type_to_string(&ret_type);
    let ret_type_str = match ret_type_str {
        Some(s) => s,
        None => return,
    };

    // Collect matching (struct_name, field_name) pairs from structs that:
    // 1. Have the right field count (matching unpack_count)
    // 2. Have a field whose type matches the return type
    let mut all_matches: Vec<(String, String)> = Vec::new();
    for (struct_name, spec) in &registry.structs {
        if unpack_count > 0 && spec.fields.len() != unpack_count {
            continue;
        }
        for field in spec.fields.iter() {
            let field_type_str = spec_type_to_string(&field.type_);
            if field_type_str.as_deref() == Some(&ret_type_str)
                && let Ok(field_name) = field.name.to_utf8_string()
            {
                all_matches.push((struct_name.clone(), field_name));
            }
        }
    }

    // Disambiguate: if multiple fields match, try using the function name.
    // SDK getter functions are conventionally named after the field they return
    // (e.g., fn name() -> String returns the "name" field).
    let resolved = if all_matches.len() == 1 {
        Some(all_matches[0].1.clone())
    } else if all_matches.len() > 1 {
        // Check if the function name matches exactly one of the field names
        all_matches
            .iter()
            .find(|(_, field_name)| field_name == &func.name)
            .map(|(_, field_name)| field_name.clone())
    } else {
        None
    };

    if let Some(field_name) = resolved {
        let get_expr = SorobanExpr::StorageGet {
            storage_type,
            key: Box::new(key_expr.clone()),
            unwrap: true,
            on_missing: None,
        };
        let field_expr = SorobanExpr::FieldAccess {
            object: Box::new(get_expr),
            field: field_name,
        };
        cov_mark::hit!(stage_4s_getter_recovered);
        func.body = vec![SorobanStmt::Return(Some(field_expr))];
        func.takes_env = true;
    }
}

// Stage 4t: Recover broken struct getter bodies
// ---------------------------------------------------------------------------

/// Recover getter functions whose bodies are broken (contain unresolved vars or
/// empty/todo). When a DataKey union variant matches the return type or function
/// name, synthesize the storage read.
fn recover_broken_struct_getter(
    func: &mut crate::ir::high_level_ir::ContractFn,
    registry: &TypeRegistry,
) {
    // Must have a return type
    let ret_type = match &func.return_type {
        Some(t) => t.clone(),
        None => return,
    };

    // Body must be broken: contains Local(N), NamedLocal("var_N"), todo, or is empty
    let body_is_broken = func.body.is_empty()
        || func.body.iter().any(stmt_has_unresolved_var)
        || func.body.iter().any(|s| {
            matches!(
                s,
                SorobanStmt::Expr(SorobanExpr::UnknownVal)
                    | SorobanStmt::Return(Some(SorobanExpr::UnknownVal))
            )
        });
    if !body_is_broken {
        return;
    }

    // The return type name (for struct matching) or the function name (for field matching)
    let ret_name = registry.resolve_type_name(&ret_type);

    // Look for a DataKey union with a variant matching the return type or function name
    use stellar_xdr::curr::ScSpecUdtUnionCaseV0;
    for (union_name, spec) in &registry.unions {
        for case in spec.cases.iter() {
            match case {
                ScSpecUdtUnionCaseV0::VoidV0(v) => {
                    if let Ok(variant_name) = v.name.to_utf8_string() {
                        // Void variant: match by return type name (e.g., Offer → DataKey::Offer)
                        if ret_name.as_deref() == Some(&variant_name) && func.params.is_empty() {
                            let key_expr = SorobanExpr::EnumConstruct {
                                type_name: union_name.clone(),
                                variant: variant_name,
                                fields: vec![],
                            };
                            let get_expr = SorobanExpr::StorageGet {
                                storage_type: StorageType::Instance,
                                key: Box::new(key_expr),
                                unwrap: true,
                                on_missing: None,
                            };
                            cov_mark::hit!(stage_4t_broken_getter_recovered);
                            func.body = vec![SorobanStmt::Return(Some(get_expr))];
                            func.takes_env = true;
                            return;
                        }
                    }
                }
                ScSpecUdtUnionCaseV0::TupleV0(t) => {
                    if let Ok(variant_name) = t.name.to_utf8_string() {
                        // Data-carrying variant: match when func has exactly 1 non-env param
                        // whose type matches the variant's data type, and the function name
                        // contains the variant name (case-insensitive).
                        // E.g., balance_shares(user: Address) → DataKey::Shares(Address)
                        if func.params.len() == 1
                            && t.type_.len() == 1
                            && func.params[0].type_def == t.type_[0]
                            && func
                                .name
                                .to_lowercase()
                                .contains(&variant_name.to_lowercase())
                        {
                            let key_expr = SorobanExpr::EnumConstruct {
                                type_name: union_name.clone(),
                                variant: variant_name,
                                fields: vec![SorobanExpr::Param(func.params[0].name.clone())],
                            };
                            let get_expr = SorobanExpr::StorageGet {
                                storage_type: StorageType::Persistent,
                                key: Box::new(key_expr),
                                unwrap: true,
                                on_missing: None,
                            };
                            cov_mark::hit!(stage_4t_broken_getter_recovered);
                            func.body = vec![SorobanStmt::Return(Some(get_expr))];
                            func.takes_env = true;
                            return;
                        }
                    }
                }
            }
        }
    }
}

/// Check if a statement contains unresolved variables (Local(N) or var_N).
fn stmt_has_unresolved_var(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => expr_has_unresolved_var(e),
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            expr_has_unresolved_var(value)
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            expr_has_unresolved_var(condition)
                || then_body.iter().any(stmt_has_unresolved_var)
                || else_body.iter().any(stmt_has_unresolved_var)
        }
        SorobanStmt::Match { scrutinee, arms } => {
            expr_has_unresolved_var(scrutinee)
                || arms
                    .iter()
                    .any(|a| a.body.iter().any(stmt_has_unresolved_var))
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            body.iter().any(stmt_has_unresolved_var)
        }
        _ => false,
    }
}

fn expr_has_unresolved_var(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::Local(_) => true,
        SorobanExpr::NamedLocal(n) if n.starts_with("var_") => true,
        SorobanExpr::VecConstruct(elems) | SorobanExpr::TupleConstruct(elems) => {
            elems.iter().any(expr_has_unresolved_var)
        }
        _ => false,
    }
}

/// Remove `Let { value: SymbolLiteral(_), ... }` bindings that shadow function parameters.
/// These are enum discriminant artifacts from the lifter (e.g., `let amount = symbol_short!("Allowance")`)
/// that incorrectly shadow parameters with wrong values. Recurses into nested bodies.
/// Recover return values from has-guarded StorageGet in non-void functions.
///
/// Pattern: `if has(key) { get(key).unwrap(); side_effects... }` where the
/// get() result is discarded. In the original source, the get result was the
/// return value (e.g., `read_balance` returning `i128`). WASM local reuse +
/// dead-store elimination converted the Let to a bare Expr.
///
/// Transform: capture the get result in a Let, add it as a tail return,
/// and add an else branch with the appropriate zero value.
fn recover_has_get_return_value(
    func: &mut crate::ir::high_level_ir::ContractFn,
    _registry: &TypeRegistry,
) {
    // Only for functions with numeric return types where we know the default value.
    let zero_expr = match &func.return_type {
        Some(ScSpecTypeDef::I128) => SorobanExpr::I128Literal(0),
        Some(ScSpecTypeDef::I64) => SorobanExpr::I64Literal(0),
        Some(ScSpecTypeDef::I32) => SorobanExpr::I32Literal(0),
        Some(ScSpecTypeDef::U128) => SorobanExpr::U128Literal(0),
        Some(ScSpecTypeDef::U64) => SorobanExpr::U64Literal(0),
        Some(ScSpecTypeDef::U32) => SorobanExpr::U32Literal(0),
        Some(ScSpecTypeDef::Bool) => SorobanExpr::BoolLiteral(false),
        _ => return,
    };

    recover_has_get_in_stmts(&mut func.body, &zero_expr);
}

fn recover_has_get_in_stmts(stmts: &mut [SorobanStmt], zero_expr: &SorobanExpr) {
    for stmt in stmts.iter_mut() {
        if let SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } = stmt
        {
            // Recurse into nested bodies first.
            recover_has_get_in_stmts(then_body, zero_expr);
            recover_has_get_in_stmts(else_body, zero_expr);

            // Check pattern: condition is StorageHas, body starts with Expr(StorageGet),
            // body has more than 1 statement, and else is empty.
            let is_has_condition = matches!(condition, SorobanExpr::StorageHas { .. });
            if !is_has_condition || !else_body.is_empty() || then_body.len() < 2 {
                continue;
            }

            // Check that body[0] is a standalone Expr(StorageGet { unwrap: true })
            // with matching key and storage type.
            let (has_st, has_key) = if let SorobanExpr::StorageHas { storage_type, key } = condition
            {
                (*storage_type, key.clone())
            } else {
                continue;
            };

            let matches_get = matches!(
                &then_body[0],
                SorobanStmt::Expr(SorobanExpr::StorageGet {
                    storage_type,
                    key,
                    unwrap: true,
                    ..
                }) if *storage_type == has_st && *key == has_key
            );

            if !matches_get {
                continue;
            }

            // Transform: convert Expr(StorageGet) to Let, add tail return + else default.
            let binding_name = "value".to_string();

            // Replace body[0] with Let binding.
            let get_expr = if let SorobanStmt::Expr(e) = &then_body[0] {
                e.clone()
            } else {
                continue;
            };
            then_body[0] = SorobanStmt::Let {
                name: binding_name.clone(),
                mutable: false,
                value: get_expr,
            };

            // Remove redundant key re-creation lets: when the has() key is
            // NamedLocal("X") and the then-body re-creates `let X = ...`,
            // it's a WASM local reuse artifact. The outer-scope binding
            // already provides the same value, so the inner Let is redundant.
            if let SorobanExpr::NamedLocal(key_name) = has_key.as_ref() {
                let key_name = key_name.clone();
                then_body.retain(
                    |stmt| !matches!(stmt, SorobanStmt::Let { name, .. } if *name == key_name),
                );
            }

            // Append the variable as a tail return at the end of then_body.
            then_body.push(SorobanStmt::Expr(SorobanExpr::NamedLocal(binding_name)));

            // Add else branch with zero default.
            *else_body = vec![SorobanStmt::Expr(zero_expr.clone())];
        }

        // Also recurse into Match/Loop/Block.
        match stmt {
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    recover_has_get_in_stmts(&mut arm.body, zero_expr);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                recover_has_get_in_stmts(body, zero_expr);
            }
            _ => {}
        }
    }
}

fn remove_symbol_param_shadows(stmts: &mut Vec<SorobanStmt>, param_names: &[String]) {
    stmts.retain(|stmt| {
        if let SorobanStmt::Let {
            name,
            value: SorobanExpr::SymbolLiteral(_),
            ..
        } = stmt
        {
            !param_names.contains(name)
        } else {
            true
        }
    });
    // Recurse into nested bodies
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                remove_symbol_param_shadows(then_body, param_names);
                remove_symbol_param_shadows(else_body, param_names);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    remove_symbol_param_shadows(&mut arm.body, param_names);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                remove_symbol_param_shadows(body, param_names);
            }
            _ => {}
        }
    }
}

/// Bind orphan `Expr(StorageGet)` to a named variable when the key's variant
/// matches a known struct type. Converts:
///   `env.storage().instance().get(&DataKey::Offer).unwrap();`
/// to:
///   `let offer = env.storage().instance().get(&DataKey::Offer).unwrap();`
fn bind_orphan_struct_get(
    func: &mut crate::ir::high_level_ir::ContractFn,
    registry: &TypeRegistry,
) {
    // Only for void functions (non-void already have return value handling)
    let is_void =
        func.return_type.is_none() || matches!(func.return_type, Some(ScSpecTypeDef::Void));
    if !is_void {
        return;
    }

    for stmt in func.body.iter_mut() {
        if let SorobanStmt::Expr(SorobanExpr::StorageGet {
            key, unwrap: true, ..
        }) = stmt
        {
            // Derive a binding name from the key expression:
            // - EnumConstruct { variant } → snake_case(variant) if matches a struct
            // - NamedLocal(name) → "value" (key is a variable, result is the stored value)
            // - SymbolLiteral(s) → snake_case(s)
            let binding_name = match key.as_ref() {
                SorobanExpr::EnumConstruct { variant, .. } => {
                    let variant_lower = variant.to_lowercase();
                    if registry
                        .structs
                        .keys()
                        .any(|s| s.to_lowercase() == variant_lower)
                    {
                        Some(camel_to_snake(variant))
                    } else {
                        // Unit variant (e.g., DataKey::Admin) — use variant name
                        Some(camel_to_snake(variant))
                    }
                }
                SorobanExpr::NamedLocal(name) => {
                    // Key is a variable reference — use the variable name
                    // e.g., `let admin = DataKey::Admin; get(&admin).unwrap()`
                    // → `let admin_value = get(&admin).unwrap()`
                    Some(format!("{}_value", name))
                }
                _ => None,
            };

            if let Some(name) = binding_name {
                // Convert Expr(StorageGet) → Let(name, StorageGet)
                let SorobanStmt::Expr(get_expr) =
                    std::mem::replace(stmt, SorobanStmt::Expr(SorobanExpr::Void))
                else {
                    continue;
                };
                *stmt = SorobanStmt::Let {
                    name,
                    mutable: false,
                    value: get_expr,
                };
            }
        }
    }
}

fn camel_to_snake(s: &str) -> String {
    let mut result = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() {
            if i > 0 {
                result.push('_');
            }
            result.push(c.to_lowercase().next().unwrap());
        } else {
            result.push(c);
        }
    }
    result
}

/// Replace `FieldAccess { object: StorageGet { key: UnknownVal }, field }` with
/// `FieldAccess { object: NamedLocal(var_name), field }` when a preceding Let
/// binding already loaded from the same storage type with a known key.
fn resolve_unknown_key_field_access(stmts: &mut [SorobanStmt]) {
    // Collect Let bindings with StorageGet values that have known keys.
    let mut bindings: Vec<(String, StorageType)> = Vec::new();
    for stmt in stmts.iter() {
        if let SorobanStmt::Let {
            name,
            value:
                SorobanExpr::StorageGet {
                    storage_type,
                    key,
                    unwrap: true,
                    ..
                },
            ..
        } = stmt
            && !matches!(key.as_ref(), SorobanExpr::UnknownVal)
        {
            bindings.push((name.clone(), *storage_type));
        }
    }

    if bindings.is_empty() {
        return;
    }

    // Walk statements and replace UnknownVal-keyed StorageGet in FieldAccess.
    for stmt in stmts.iter_mut() {
        replace_unknown_get_in_stmt(stmt, &bindings);
    }
}

fn replace_unknown_get_in_stmt(stmt: &mut SorobanStmt, bindings: &[(String, StorageType)]) {
    match stmt {
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            replace_unknown_get_in_expr(value, bindings);
        }
        SorobanStmt::Expr(expr) | SorobanStmt::Return(Some(expr)) => {
            replace_unknown_get_in_expr(expr, bindings);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            replace_unknown_get_in_expr(condition, bindings);
            for s in then_body.iter_mut() {
                replace_unknown_get_in_stmt(s, bindings);
            }
            for s in else_body.iter_mut() {
                replace_unknown_get_in_stmt(s, bindings);
            }
        }
        SorobanStmt::Match { scrutinee, arms } => {
            replace_unknown_get_in_expr(scrutinee, bindings);
            for arm in arms.iter_mut() {
                for s in arm.body.iter_mut() {
                    replace_unknown_get_in_stmt(s, bindings);
                }
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            for s in body.iter_mut() {
                replace_unknown_get_in_stmt(s, bindings);
            }
        }
        _ => {}
    }
}

fn replace_unknown_get_in_expr(expr: &mut SorobanExpr, bindings: &[(String, StorageType)]) {
    // Target: FieldAccess { object: StorageGet { key: UnknownVal, unwrap: true }, field }
    if let SorobanExpr::FieldAccess { object, .. } = expr {
        if let SorobanExpr::StorageGet {
            storage_type,
            key,
            unwrap: true,
            ..
        } = object.as_ref()
            && matches!(key.as_ref(), SorobanExpr::UnknownVal)
            && let Some((name, _)) = bindings.iter().find(|(_, st)| st == storage_type)
        {
            **object = SorobanExpr::NamedLocal(name.clone());
            return;
        }
        // Recurse into FieldAccess object
        replace_unknown_get_in_expr(object, bindings);
        return;
    }

    // Recurse into other expression types
    match expr {
        SorobanExpr::MethodCall { object, args, .. } => {
            replace_unknown_get_in_expr(object, bindings);
            for arg in args.iter_mut() {
                replace_unknown_get_in_expr(arg, bindings);
            }
        }
        SorobanExpr::Not(inner)
        | SorobanExpr::ValConvert { value: inner, .. }
        | SorobanExpr::CastAs { value: inner, .. } => {
            replace_unknown_get_in_expr(inner, bindings);
        }
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Eq(a, b)
        | SorobanExpr::Ne(a, b)
        | SorobanExpr::Lt(a, b)
        | SorobanExpr::Gt(a, b) => {
            replace_unknown_get_in_expr(a, bindings);
            replace_unknown_get_in_expr(b, bindings);
        }
        SorobanExpr::VecConstruct(elems) | SorobanExpr::TupleConstruct(elems) => {
            for e in elems.iter_mut() {
                replace_unknown_get_in_expr(e, bindings);
            }
        }
        SorobanExpr::RequireAuth(inner)
        | SorobanExpr::RequireAuthForArgs { address: inner, .. } => {
            replace_unknown_get_in_expr(inner, bindings);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            replace_unknown_get_in_expr(key, bindings);
            replace_unknown_get_in_expr(value, bindings);
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields.iter_mut() {
                replace_unknown_get_in_expr(v, bindings);
            }
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
            replace_unknown_get_in_expr(address, bindings);
            replace_unknown_get_in_expr(function, bindings);
            for arg in args.iter_mut() {
                replace_unknown_get_in_expr(arg, bindings);
            }
        }
        _ => {}
    }
}

/// Fix `RequireAuth(NamedLocal("admin"))` when `admin` is bound to an EnumConstruct
/// and a separate `admin_value = StorageGet { key: admin }` exists. The require_auth
/// should reference the loaded value (Address), not the enum key.
fn fix_require_auth_on_enum_key(stmts: &mut [SorobanStmt]) {
    // Phase 1: collect pairs (key_name → value_name) where key is EnumConstruct
    // and value is StorageGet using that key.
    let mut key_to_value: Vec<(String, String)> = Vec::new();
    for w in stmts.windows(2) {
        if let (
            SorobanStmt::Let {
                name: key_name,
                value: SorobanExpr::EnumConstruct { .. },
                ..
            },
            SorobanStmt::Let {
                name: val_name,
                value:
                    SorobanExpr::StorageGet {
                        key, unwrap: true, ..
                    },
                ..
            },
        ) = (&w[0], &w[1])
            && let SorobanExpr::NamedLocal(k) = key.as_ref()
            && k == key_name
        {
            key_to_value.push((key_name.clone(), val_name.clone()));
        }
    }

    if key_to_value.is_empty() {
        return;
    }

    // Phase 2: replace RequireAuth(NamedLocal(key)) → RequireAuth(NamedLocal(value))
    for stmt in stmts.iter_mut() {
        fix_auth_in_stmt(stmt, &key_to_value);
    }
}

fn fix_auth_in_stmt(stmt: &mut SorobanStmt, pairs: &[(String, String)]) {
    match stmt {
        SorobanStmt::Expr(expr) => fix_auth_in_expr(expr, pairs),
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            fix_auth_in_expr(value, pairs)
        }
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            for s in then_body.iter_mut() {
                fix_auth_in_stmt(s, pairs);
            }
            for s in else_body.iter_mut() {
                fix_auth_in_stmt(s, pairs);
            }
        }
        _ => {}
    }
}

fn fix_auth_in_expr(expr: &mut SorobanExpr, pairs: &[(String, String)]) {
    if let SorobanExpr::RequireAuth(inner) = expr {
        if let SorobanExpr::NamedLocal(name) = inner.as_ref()
            && let Some((_, val_name)) = pairs.iter().find(|(k, _)| k == name)
        {
            **inner = SorobanExpr::NamedLocal(val_name.clone());
            return;
        }
        fix_auth_in_expr(inner, pairs);
    }
    // Also fix in PublishEvent topics and nested expressions
    match expr {
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics.iter_mut() {
                fix_named_local_in_expr(t, pairs);
            }
            fix_auth_in_expr(data, pairs);
        }
        SorobanExpr::VecConstruct(elems) | SorobanExpr::TupleConstruct(elems) => {
            for e in elems.iter_mut() {
                fix_named_local_in_expr(e, pairs);
            }
        }
        _ => {}
    }
}

/// Replace NamedLocal(key_name) with NamedLocal(value_name) in any expression,
/// recursing into VecConstruct/TupleConstruct elements.
fn fix_named_local_in_expr(expr: &mut SorobanExpr, pairs: &[(String, String)]) {
    match expr {
        SorobanExpr::NamedLocal(name) => {
            if let Some((_, val_name)) = pairs.iter().find(|(k, _)| k == name) {
                *expr = SorobanExpr::NamedLocal(val_name.clone());
            }
        }
        SorobanExpr::VecConstruct(elems) | SorobanExpr::TupleConstruct(elems) => {
            for e in elems.iter_mut() {
                fix_named_local_in_expr(e, pairs);
            }
        }
        _ => {}
    }
}

/// Fix BoolLiteral(false/true) in StorageSet value positions and StructConstruct
/// field values. Val-decoded 0x00/0x01 should be numeric 0/1 in storage contexts.
fn fix_bool_in_storage_set(stmts: &mut [SorobanStmt]) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Expr(SorobanExpr::StorageSet { value, .. }) => {
                fix_bool_to_int(value);
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                fix_bool_in_storage_set(then_body);
                fix_bool_in_storage_set(else_body);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    fix_bool_in_storage_set(&mut arm.body);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                fix_bool_in_storage_set(body);
            }
            _ => {}
        }
    }
}

fn fix_bool_to_int(expr: &mut SorobanExpr) {
    match expr {
        SorobanExpr::BoolLiteral(false) => *expr = SorobanExpr::I64Literal(0),
        SorobanExpr::BoolLiteral(true) => *expr = SorobanExpr::I64Literal(1),
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields.iter_mut() {
                fix_bool_to_int(v);
            }
        }
        _ => {}
    }
}

/// Resolve unbound `NamedLocal("var_N")` and `Local(N)` in event publish data
/// to matching function parameters. When the event data references an unresolved
/// body local, check if any unused function parameter could provide the value.
fn resolve_event_data_params(
    stmts: &mut [SorobanStmt],
    params: &[crate::ir::high_level_ir::FnParam],
    param_local_base: u32,
) {
    if params.is_empty() {
        return;
    }

    // Collect param names that are used in the function body (excluding event data)
    let mut used_params: std::collections::HashSet<String> = std::collections::HashSet::new();
    collect_param_uses(stmts, &mut used_params);
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Expr(SorobanExpr::PublishEvent { topics, data, .. }) => {
                resolve_var_to_param(
                    data,
                    params,
                    &used_params,
                    topics,
                    param_local_base,
                    true,
                    true,
                );
            }
            SorobanStmt::Expr(SorobanExpr::MethodCall {
                method,
                object,
                args,
            }) if is_event_publish_method_call(method, object, args) => {
                let sibling_topics = event_publish_struct_topics(object, params);
                resolve_var_to_param(
                    object,
                    params,
                    &used_params,
                    &sibling_topics,
                    param_local_base,
                    true,
                    true,
                );
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                resolve_event_data_params(then_body, params, param_local_base);
                resolve_event_data_params(else_body, params, param_local_base);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    resolve_event_data_params(&mut arm.body, params, param_local_base);
                }
            }
            _ => {}
        }
    }
}

fn is_event_publish_method_call(method: &str, object: &SorobanExpr, args: &[SorobanExpr]) -> bool {
    method == "publish"
        && matches!(object, SorobanExpr::StructConstruct { .. })
        && matches!(args, [arg] if is_env_like_publish_arg(arg))
}

fn is_env_like_publish_arg(arg: &SorobanExpr) -> bool {
    expr_uses_env(arg)
        || matches!(arg, SorobanExpr::Param(name) if name == "env")
        || matches!(arg, SorobanExpr::NamedLocal(name) if name == "env")
}

fn event_publish_struct_topics(
    object: &SorobanExpr,
    params: &[crate::ir::high_level_ir::FnParam],
) -> Vec<SorobanExpr> {
    match object {
        SorobanExpr::StructConstruct { fields, .. } => {
            let mut topics: Vec<SorobanExpr> =
                fields.iter().map(|(_, value)| value.clone()).collect();
            for (name, value) in fields {
                if !is_unresolved_event_value(value)
                    && params.iter().any(|param| param.name == *name)
                {
                    topics.push(SorobanExpr::Param(name.clone()));
                }
            }
            topics
        }
        _ => Vec::new(),
    }
}

fn is_unresolved_event_value(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::Local(_) | SorobanExpr::UnknownVal => true,
        SorobanExpr::NamedLocal(name) => name.starts_with("var_"),
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            is_unresolved_event_value(value)
        }
        _ => false,
    }
}

fn resolve_var_to_param(
    expr: &mut SorobanExpr,
    params: &[crate::ir::high_level_ir::FnParam],
    _used_params: &std::collections::HashSet<String>,
    topics: &[SorobanExpr],
    param_local_base: u32,
    allow_index_fallback: bool,
    allow_candidate_fallback: bool,
) {
    // Unwrap ValConvert wrappers to reach the inner expression
    if let SorobanExpr::ValConvert { value: inner, .. } = expr {
        resolve_var_to_param(
            inner,
            params,
            _used_params,
            topics,
            param_local_base,
            allow_index_fallback,
            allow_candidate_fallback,
        );
        return;
    }

    // Collect param names used in topics (to exclude from data candidates).
    // Recurse into VecConstruct/TupleConstruct since topics may be wrapped.
    let mut topic_param_names: std::collections::HashSet<String> = std::collections::HashSet::new();
    for t in topics {
        collect_param_names_from_expr(t, &mut topic_param_names);
    }

    // Find data candidates: params NOT used as topics, NOT env, NOT Address-like
    let data_candidates: Vec<&crate::ir::high_level_ir::FnParam> = params
        .iter()
        .filter(|p| {
            p.name != "env"
                && !topic_param_names.contains(&p.name)
                && !matches!(
                    p.type_def,
                    stellar_xdr::curr::ScSpecTypeDef::Address
                        | stellar_xdr::curr::ScSpecTypeDef::Void
                )
        })
        .collect();

    match expr {
        SorobanExpr::NamedLocal(name) if name.starts_with("var_") => {
            for param in params {
                if param.name != "env" && param.name == *name {
                    *expr = SorobanExpr::Param(param.name.clone());
                    return;
                }
            }
            if allow_candidate_fallback && data_candidates.len() == 1 {
                *expr = SorobanExpr::Param(data_candidates[0].name.clone());
            }
        }
        SorobanExpr::Local(idx) => {
            if allow_candidate_fallback && data_candidates.len() == 1 {
                *expr = SorobanExpr::Param(data_candidates[0].name.clone());
            } else if allow_index_fallback {
                let param_idx = idx.saturating_sub(param_local_base) as usize;
                if let Some(param) = params.get(param_idx)
                    && param.name != "env"
                    && !topic_param_names.contains(&param.name)
                {
                    *expr = SorobanExpr::Param(param.name.clone());
                }
            }
        }
        SorobanExpr::UnknownVal if allow_candidate_fallback && data_candidates.len() == 1 => {
            *expr = SorobanExpr::Param(data_candidates[0].name.clone());
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (field_name, value) in fields.iter_mut() {
                if allow_candidate_fallback
                    && is_unresolved_event_value(value)
                    && !topic_param_names.contains(field_name)
                    && params.iter().any(|param| param.name == *field_name)
                {
                    *value = SorobanExpr::Param(field_name.clone());
                    continue;
                }
                match value {
                    SorobanExpr::StructConstruct { .. } => {
                        resolve_var_to_param(
                            value,
                            params,
                            _used_params,
                            topics,
                            param_local_base,
                            false,
                            false,
                        );
                    }
                    _ => {
                        resolve_var_to_param(
                            value,
                            params,
                            _used_params,
                            topics,
                            param_local_base,
                            allow_index_fallback,
                            allow_candidate_fallback,
                        );
                    }
                }
            }
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            resolve_var_to_param(
                object,
                params,
                _used_params,
                topics,
                param_local_base,
                allow_index_fallback,
                allow_candidate_fallback,
            );
            for arg in args.iter_mut() {
                resolve_var_to_param(
                    arg,
                    params,
                    _used_params,
                    topics,
                    param_local_base,
                    allow_index_fallback,
                    allow_candidate_fallback,
                );
            }
        }
        _ => {}
    }
}

fn collect_param_uses(stmts: &[SorobanStmt], used: &mut std::collections::HashSet<String>) {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Expr(expr) | SorobanStmt::Return(Some(expr)) => {
                collect_param_uses_expr(expr, used);
            }
            SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
                collect_param_uses_expr(value, used);
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                collect_param_uses_expr(condition, used);
                collect_param_uses(then_body, used);
                collect_param_uses(else_body, used);
            }
            _ => {}
        }
    }
}

fn collect_param_uses_expr(expr: &SorobanExpr, used: &mut std::collections::HashSet<String>) {
    if let SorobanExpr::Param(name) = expr {
        used.insert(name.clone());
    }
    // Simple recursion for common cases
    match expr {
        SorobanExpr::RequireAuth(inner) | SorobanExpr::Not(inner) => {
            collect_param_uses_expr(inner, used);
        }
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Eq(a, b)
        | SorobanExpr::Lt(a, b) => {
            collect_param_uses_expr(a, used);
            collect_param_uses_expr(b, used);
        }
        SorobanExpr::FieldAccess { object, .. } => {
            collect_param_uses_expr(object, used);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            collect_param_uses_expr(key, used);
            collect_param_uses_expr(value, used);
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for v in fields {
                collect_param_uses_expr(v, used);
            }
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields {
                collect_param_uses_expr(v, used);
            }
        }
        _ => {}
    }
}

fn collect_param_names_from_expr(
    expr: &SorobanExpr,
    names: &mut std::collections::HashSet<String>,
) {
    match expr {
        SorobanExpr::Param(name) | SorobanExpr::NamedLocal(name) => {
            names.insert(name.clone());
        }
        SorobanExpr::VecConstruct(elems) | SorobanExpr::TupleConstruct(elems) => {
            for e in elems {
                collect_param_names_from_expr(e, names);
            }
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, value) in fields {
                collect_param_names_from_expr(value, names);
            }
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            collect_param_names_from_expr(object, names);
            for arg in args {
                collect_param_names_from_expr(arg, names);
            }
        }
        SorobanExpr::FieldAccess { object, .. } => {
            collect_param_names_from_expr(object, names);
        }
        SorobanExpr::ValConvert { value: inner, .. } => {
            collect_param_names_from_expr(inner, names);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stellar_xdr::curr::ScSpecTypeDef;

    #[test]
    fn convert_vec_to_tuple_return_handles_return_before_trailing_stmt() {
        // A tuple return is not always the last statement — a dead `panic!()` from
        // the WASM `unreachable` can follow it. The conversion must still fire.
        let mut body = vec![
            SorobanStmt::Return(Some(SorobanExpr::VecConstruct(vec![
                SorobanExpr::Env,
                SorobanExpr::I128Literal(1),
                SorobanExpr::I128Literal(2),
            ]))),
            SorobanStmt::Expr(SorobanExpr::Panic),
        ];
        convert_vec_to_tuple_return(&mut body, 2);
        match &body[0] {
            SorobanStmt::Return(Some(SorobanExpr::TupleConstruct(items))) => {
                assert_eq!(items.len(), 2, "(i128, i128) return becomes a 2-tuple");
            }
            other => panic!("expected a tuple return, got {other:?}"),
        }
    }

    #[test]
    fn coerce_i128_invoke_types_retypes_call_in_subtraction() {
        // `balance() - amount` where `balance` is an untyped cross-contract call:
        // the call must be retyped `i128` so `Val - i128` becomes `i128 - i128`.
        let params = vec![FnParam {
            name: "amount".to_string(),
            type_def: ScSpecTypeDef::I128,
        }];
        let invoke = SorobanExpr::InvokeContract {
            address: Box::new(SorobanExpr::Param("token".to_string())),
            function: Box::new(SorobanExpr::SymbolLiteral("balance".to_string())),
            args: vec![],
            return_type: None,
        };
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::Sub(
            Box::new(invoke),
            Box::new(SorobanExpr::Param("amount".to_string())),
        ))];
        let _ = coerce_i128_invoke_types(&mut body, &params);
        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::Sub(a, _)) => assert!(
                matches!(a.as_ref(), SorobanExpr::InvokeContract { return_type: Some(t), .. } if t == "i128"),
                "the balance() call should be typed i128, got {a:?}"
            ),
            other => panic!("unexpected body: {other:?}"),
        }
    }

    fn storage_hints(function_name: &str, keys: Vec<HintValue>) -> DecompileHints {
        DecompileHints::with_functions(vec![crate::FunctionHints::with_storage(
            function_name,
            keys.into_iter().map(crate::StorageHint::new),
        )])
    }

    fn auth_hints(
        function_name: &str,
        auth: Vec<(Option<HintValue>, Vec<HintValue>)>,
    ) -> DecompileHints {
        let mut function_hints = crate::FunctionHints::new(function_name);
        for (address, args) in auth {
            function_hints.push_auth(crate::AuthHint::new(address, args));
        }
        DecompileHints::with_functions(vec![function_hints])
    }

    fn event_hints(
        function_name: &str,
        events: Vec<(Vec<HintValue>, Vec<HintValue>)>,
    ) -> DecompileHints {
        let mut function_hints = crate::FunctionHints::new(function_name);
        for (topics, data) in events {
            function_hints.push_event(crate::EventHint::new(topics, data));
        }
        DecompileHints::with_functions(vec![function_hints])
    }

    fn invoke_hints(function_name: &str, functions: Vec<Option<HintValue>>) -> DecompileHints {
        let mut function_hints = crate::FunctionHints::new(function_name);
        for function in functions {
            function_hints.push_invoke(crate::InvokeHint::new(function, Vec::new()));
        }
        DecompileHints::with_functions(vec![function_hints])
    }

    /// Test convenience: filter `hints.functions` by name to a Vec the four
    /// `unique_*_for_function` helpers can consume. In the pipeline this is
    /// done via a HashMap built once per run; in tests we filter per call
    /// for clarity.
    fn matching<'a>(hints: &'a DecompileHints, function_name: &str) -> Vec<&'a FunctionHints> {
        hints
            .functions
            .iter()
            .filter(|fh| fh.function_name == function_name)
            .collect()
    }

    fn invoke_contract_with_function(function: SorobanExpr) -> SorobanExpr {
        SorobanExpr::InvokeContract {
            address: Box::new(SorobanExpr::Param("contract".to_string())),
            function: Box::new(function),
            args: vec![SorobanExpr::U64Literal(7)],
            return_type: None,
        }
    }

    fn try_invoke_contract_with_function(function: SorobanExpr) -> SorobanExpr {
        SorobanExpr::TryInvokeContract {
            address: Box::new(SorobanExpr::Param("contract".to_string())),
            function: Box::new(function),
            args: vec![SorobanExpr::U64Literal(7)],
            return_type: None,
        }
    }

    fn weak_buf_symbol_call() -> SorobanExpr {
        SorobanExpr::RawHostCall {
            module: "Buf".to_string(),
            function: "symbol_new_from_linear_memory".to_string(),
            args: vec![SorobanExpr::U32Literal(0), SorobanExpr::U32Literal(8)],
        }
    }

    fn weak_buf_string_call() -> SorobanExpr {
        SorobanExpr::RawHostCall {
            module: "Buf".to_string(),
            function: "string_new_from_linear_memory".to_string(),
            args: vec![SorobanExpr::U32Literal(8), SorobanExpr::U32Literal(5)],
        }
    }

    #[test]
    fn invoke_hints_repair_weak_function_names_when_unambiguous() {
        let hints = invoke_hints(
            "transfer",
            vec![
                Some(HintValue::Symbol("approve".to_string())),
                Some(HintValue::Symbol("approve".to_string())),
            ],
        );
        let replacement = unique_invoke_hint_function_for_function(&matching(&hints, "transfer"))
            .expect("hint should be unique");
        let mut body = vec![
            SorobanStmt::Expr(invoke_contract_with_function(SorobanExpr::UnknownVal)),
            SorobanStmt::Expr(try_invoke_contract_with_function(weak_buf_symbol_call())),
        ];

        repair_unknown_invoke_functions_from_hint(&mut body, &replacement);

        for stmt in &body {
            let function = match stmt {
                SorobanStmt::Expr(SorobanExpr::InvokeContract { function, .. })
                | SorobanStmt::Expr(SorobanExpr::TryInvokeContract { function, .. }) => function,
                other => panic!("unexpected stmt shape: {other:?}"),
            };
            assert!(matches!(
                function.as_ref(),
                SorobanExpr::SymbolLiteral(symbol) if symbol == "approve"
            ));
        }
    }

    #[test]
    fn invoke_hints_do_not_repair_when_function_name_is_ambiguous() {
        let hints = invoke_hints(
            "transfer",
            vec![
                Some(HintValue::Symbol("approve".to_string())),
                Some(HintValue::Symbol("revoke".to_string())),
            ],
        );
        let mut body = vec![SorobanStmt::Expr(invoke_contract_with_function(
            SorobanExpr::UnknownVal,
        ))];

        if let Some(replacement) =
            unique_invoke_hint_function_for_function(&matching(&hints, "transfer"))
        {
            repair_unknown_invoke_functions_from_hint(&mut body, &replacement);
        }

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::InvokeContract { function, .. }) => {
                assert!(matches!(function.as_ref(), SorobanExpr::UnknownVal));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn invoke_hints_do_not_repair_when_function_name_is_unsupported() {
        let hints = invoke_hints("transfer", vec![Some(HintValue::U64(7))]);
        let mut body = vec![SorobanStmt::Expr(invoke_contract_with_function(
            SorobanExpr::UnknownVal,
        ))];

        if let Some(replacement) =
            unique_invoke_hint_function_for_function(&matching(&hints, "transfer"))
        {
            repair_unknown_invoke_functions_from_hint(&mut body, &replacement);
        }

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::InvokeContract { function, .. }) => {
                assert!(matches!(function.as_ref(), SorobanExpr::UnknownVal));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn invoke_hints_preserve_concrete_function_expressions() {
        let hints = invoke_hints(
            "transfer",
            vec![Some(HintValue::Symbol("approve".to_string()))],
        );
        let replacement = unique_invoke_hint_function_for_function(&matching(&hints, "transfer"))
            .expect("hint should be unique");
        let mut body = vec![SorobanStmt::Expr(invoke_contract_with_function(
            SorobanExpr::SymbolLiteral("existing".to_string()),
        ))];

        repair_unknown_invoke_functions_from_hint(&mut body, &replacement);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::InvokeContract { function, .. }) => {
                assert!(matches!(
                    function.as_ref(),
                    SorobanExpr::SymbolLiteral(symbol) if symbol == "existing"
                ));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn storage_hints_repair_unknown_storage_keys_when_unambiguous() {
        let hints = storage_hints("read", vec![HintValue::Symbol("Balance".to_string())]);
        let replacement = unique_storage_hint_key_for_function(&matching(&hints, "read"))
            .expect("hint should be unique");
        let mut body = vec![
            SorobanStmt::Expr(SorobanExpr::StorageGet {
                storage_type: StorageType::Persistent,
                key: Box::new(SorobanExpr::UnknownVal),
                unwrap: true,
                on_missing: None,
            }),
            SorobanStmt::Expr(SorobanExpr::StorageSet {
                storage_type: StorageType::Persistent,
                key: Box::new(SorobanExpr::UnknownVal),
                value: Box::new(SorobanExpr::U64Literal(7)),
            }),
            SorobanStmt::Expr(SorobanExpr::StorageHas {
                storage_type: StorageType::Persistent,
                key: Box::new(SorobanExpr::UnknownVal),
            }),
            SorobanStmt::Expr(SorobanExpr::StorageRemove {
                storage_type: StorageType::Persistent,
                key: Box::new(SorobanExpr::UnknownVal),
            }),
            SorobanStmt::Expr(SorobanExpr::StorageExtendTtl {
                storage_type: StorageType::Persistent,
                key: Box::new(SorobanExpr::UnknownVal),
                threshold: Box::new(SorobanExpr::U32Literal(10)),
                extend_to: Box::new(SorobanExpr::U32Literal(20)),
            }),
        ];

        repair_unknown_storage_keys_from_hint(&mut body, &replacement);

        for stmt in &body {
            let key = match stmt {
                SorobanStmt::Expr(SorobanExpr::StorageGet { key, .. })
                | SorobanStmt::Expr(SorobanExpr::StorageSet { key, .. })
                | SorobanStmt::Expr(SorobanExpr::StorageHas { key, .. })
                | SorobanStmt::Expr(SorobanExpr::StorageRemove { key, .. })
                | SorobanStmt::Expr(SorobanExpr::StorageExtendTtl { key, .. }) => key,
                other => panic!("unexpected stmt shape: {other:?}"),
            };
            assert!(matches!(
                key.as_ref(),
                SorobanExpr::SymbolLiteral(symbol) if symbol == "Balance"
            ));
        }
    }

    #[test]
    fn storage_hints_do_not_repair_when_key_is_ambiguous() {
        let hints = storage_hints(
            "read",
            vec![
                HintValue::Symbol("Balance".to_string()),
                HintValue::Symbol("Allowance".to_string()),
            ],
        );
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::StorageGet {
            storage_type: StorageType::Persistent,
            key: Box::new(SorobanExpr::UnknownVal),
            unwrap: true,
            on_missing: None,
        })];

        if let Some(replacement) = unique_storage_hint_key_for_function(&matching(&hints, "read")) {
            repair_unknown_storage_keys_from_hint(&mut body, &replacement);
        }

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::StorageGet { key, .. }) => {
                assert!(matches!(key.as_ref(), SorobanExpr::UnknownVal));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn storage_hints_repair_string_storage_keys_when_unambiguous() {
        let hints = storage_hints("read", vec![HintValue::String("account".to_string())]);
        let replacement = unique_storage_hint_key_for_function(&matching(&hints, "read"))
            .expect("hint should be unique");
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::StorageGet {
            storage_type: StorageType::Persistent,
            key: Box::new(SorobanExpr::UnknownVal),
            unwrap: true,
            on_missing: None,
        })];

        repair_unknown_storage_keys_from_hint(&mut body, &replacement);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::StorageGet { key, .. }) => {
                assert!(matches!(
                    key.as_ref(),
                    SorobanExpr::StringLiteral(value) if value == "account"
                ));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn storage_hints_support_wide_integer_keys() {
        let u128_hints = storage_hints("read", vec![HintValue::U128(42)]);
        assert!(matches!(
            unique_storage_hint_key_for_function(&matching(&u128_hints, "read")),
            Some(SorobanExpr::U128Literal(42))
        ));

        let i128_hints = storage_hints("read", vec![HintValue::I128(-42)]);
        assert!(matches!(
            unique_storage_hint_key_for_function(&matching(&i128_hints, "read")),
            Some(SorobanExpr::I128Literal(-42))
        ));
    }

    #[test]
    fn storage_hints_repair_bytes_storage_keys_when_unambiguous() {
        let hints = storage_hints("read", vec![HintValue::Bytes(vec![1, 2, 3])]);
        let replacement = unique_storage_hint_key_for_function(&matching(&hints, "read"))
            .expect("Bytes hint should now repair");
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::StorageGet {
            storage_type: StorageType::Persistent,
            key: Box::new(SorobanExpr::UnknownVal),
            unwrap: true,
            on_missing: None,
        })];

        repair_unknown_storage_keys_from_hint(&mut body, &replacement);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::StorageGet { key, .. }) => {
                assert!(matches!(
                    key.as_ref(),
                    SorobanExpr::BytesLiteral(b) if b == &[1u8, 2, 3]
                ));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn storage_hints_do_not_repair_when_keys_are_ambiguous() {
        // Distinct keys (Symbol vs Bytes) — both individually supported,
        // but ambiguous together, so hint repair must abstain.
        let hints = storage_hints(
            "read",
            vec![
                HintValue::Symbol("Balance".to_string()),
                HintValue::Bytes(vec![1, 2, 3]),
            ],
        );

        assert!(unique_storage_hint_key_for_function(&matching(&hints, "read")).is_none());
    }

    #[test]
    fn storage_hints_do_not_replace_non_unknown_storage_keys() {
        let replacement = SorobanExpr::SymbolLiteral("Balance".to_string());
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::StorageGet {
            storage_type: StorageType::Persistent,
            key: Box::new(SorobanExpr::SymbolLiteral("Existing".to_string())),
            unwrap: true,
            on_missing: None,
        })];

        repair_unknown_storage_keys_from_hint(&mut body, &replacement);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::StorageGet { key, .. }) => {
                assert!(matches!(
                    key.as_ref(),
                    SorobanExpr::SymbolLiteral(symbol) if symbol == "Existing"
                ));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn event_hints_repair_unknown_event_topics_and_data_when_unambiguous() {
        let hints = event_hints(
            "transfer",
            vec![(
                vec![HintValue::Symbol("transfer".to_string())],
                vec![HintValue::U64(10)],
            )],
        );
        let replacement = unique_event_hint_for_function(&matching(&hints, "transfer"))
            .expect("hint should be unique");
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::PublishEvent {
            event_name: None,
            topics: vec![SorobanExpr::UnknownVal],
            data: Box::new(SorobanExpr::UnknownVal),
        })];

        repair_unknown_event_values_from_hint(&mut body, &replacement);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::PublishEvent { topics, data, .. }) => {
                assert!(matches!(
                    &topics[0],
                    SorobanExpr::SymbolLiteral(symbol) if symbol == "transfer"
                ));
                assert!(matches!(data.as_ref(), SorobanExpr::U64Literal(10)));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn event_hints_repair_weak_buf_event_topics_and_tuple_data_fields() {
        let hints = event_hints(
            "transfer",
            vec![(
                vec![
                    HintValue::Symbol("transfer".to_string()),
                    HintValue::String("memo".to_string()),
                ],
                vec![HintValue::U64(10), HintValue::Bool(true)],
            )],
        );
        let replacement = unique_event_hint_for_function(&matching(&hints, "transfer"))
            .expect("hint should be unique");
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::PublishEvent {
            event_name: None,
            topics: vec![weak_buf_symbol_call(), weak_buf_string_call()],
            data: Box::new(SorobanExpr::TupleConstruct(vec![
                SorobanExpr::UnknownVal,
                weak_buf_symbol_call(),
            ])),
        })];

        repair_unknown_event_values_from_hint(&mut body, &replacement);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::PublishEvent { topics, data, .. }) => {
                assert!(matches!(
                    &topics[0],
                    SorobanExpr::SymbolLiteral(symbol) if symbol == "transfer"
                ));
                assert!(matches!(
                    &topics[1],
                    SorobanExpr::StringLiteral(value) if value == "memo"
                ));
                assert!(matches!(
                    data.as_ref(),
                    SorobanExpr::TupleConstruct(fields)
                        if matches!(fields.as_slice(), [SorobanExpr::U64Literal(10), SorobanExpr::BoolLiteral(true)])
                ));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn event_hints_do_not_repair_when_event_is_ambiguous() {
        let hints = event_hints(
            "transfer",
            vec![
                (
                    vec![HintValue::Symbol("transfer".to_string())],
                    vec![HintValue::U64(10)],
                ),
                (
                    vec![HintValue::Symbol("mint".to_string())],
                    vec![HintValue::U64(10)],
                ),
            ],
        );
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::PublishEvent {
            event_name: None,
            topics: vec![SorobanExpr::UnknownVal],
            data: Box::new(SorobanExpr::UnknownVal),
        })];

        if let Some(replacement) = unique_event_hint_for_function(&matching(&hints, "transfer")) {
            repair_unknown_event_values_from_hint(&mut body, &replacement);
        }

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::PublishEvent { topics, data, .. }) => {
                assert!(matches!(&topics[0], SorobanExpr::UnknownVal));
                assert!(matches!(data.as_ref(), SorobanExpr::UnknownVal));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn event_hints_repair_when_event_contains_bytes_values() {
        // Previously Bytes was unsupported and short-circuited the entire
        // hint-repair path. Now BytesLiteral exists in the IR; verify a
        // bytes data hint surfaces as a BytesLiteral in the repaired event.
        let hints = event_hints(
            "transfer",
            vec![(
                vec![HintValue::Symbol("transfer".to_string())],
                vec![HintValue::Bytes(vec![1, 2, 3])],
            )],
        );

        let hint = unique_event_hint_for_function(&matching(&hints, "transfer"))
            .expect("Bytes-valued event hint should now repair");
        assert!(matches!(
            &hint.data[0],
            SorobanExpr::BytesLiteral(b) if b == &[1u8, 2, 3]
        ));
    }

    #[test]
    fn event_hints_preserve_concrete_event_expressions() {
        let hints = event_hints(
            "transfer",
            vec![(
                vec![HintValue::Symbol("transfer".to_string())],
                vec![HintValue::U64(10)],
            )],
        );
        let replacement = unique_event_hint_for_function(&matching(&hints, "transfer"))
            .expect("hint should be unique");
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::PublishEvent {
            event_name: None,
            topics: vec![SorobanExpr::SymbolLiteral("existing".to_string())],
            data: Box::new(SorobanExpr::U64Literal(7)),
        })];

        repair_unknown_event_values_from_hint(&mut body, &replacement);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::PublishEvent { topics, data, .. }) => {
                assert!(matches!(
                    &topics[0],
                    SorobanExpr::SymbolLiteral(symbol) if symbol == "existing"
                ));
                assert!(matches!(data.as_ref(), SorobanExpr::U64Literal(7)));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn auth_hints_repair_weak_require_auth_for_args() {
        let hints = auth_hints(
            "transfer",
            vec![(
                Some(HintValue::Symbol("admin".to_string())),
                vec![HintValue::Symbol("spend".to_string()), HintValue::U64(7)],
            )],
        );
        let hint = unique_auth_hint_for_function(&matching(&hints, "transfer"))
            .expect("auth hint should be unique");
        let mut body = vec![
            SorobanStmt::Expr(SorobanExpr::RequireAuth(Box::new(SorobanExpr::UnknownVal))),
            SorobanStmt::Expr(SorobanExpr::RequireAuthForArgs {
                address: Box::new(SorobanExpr::UnknownVal),
                args: Box::new(SorobanExpr::NamedLocal("var_4".to_string())),
            }),
        ];

        repair_weak_auth_from_hint(&mut body, &hint);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::RequireAuth(address)) => {
                assert!(matches!(
                    address.as_ref(),
                    SorobanExpr::SymbolLiteral(symbol) if symbol == "admin"
                ));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
        match &body[1] {
            SorobanStmt::Expr(SorobanExpr::RequireAuthForArgs { address, args }) => {
                assert!(matches!(
                    address.as_ref(),
                    SorobanExpr::SymbolLiteral(symbol) if symbol == "admin"
                ));
                assert!(matches!(
                    args.as_ref(),
                    SorobanExpr::VecConstruct(values)
                        if matches!(values.as_slice(), [
                            SorobanExpr::SymbolLiteral(symbol),
                            SorobanExpr::U64Literal(7),
                        ] if symbol == "spend")
                ));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn auth_hints_repair_weak_vector_builder_args() {
        let hints = auth_hints(
            "transfer",
            vec![(
                Some(HintValue::Symbol("admin".to_string())),
                vec![HintValue::U32(7)],
            )],
        );
        let hint = unique_auth_hint_for_function(&matching(&hints, "transfer"))
            .expect("auth hint should be unique");
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::RequireAuthForArgs {
            address: Box::new(SorobanExpr::UnknownVal),
            args: Box::new(SorobanExpr::MethodCall {
                object: Box::new(SorobanExpr::NamedLocal("var_2".to_string())),
                method: "push_back".to_string(),
                args: vec![SorobanExpr::U32Literal(7)],
            }),
        })];

        repair_weak_auth_from_hint(&mut body, &hint);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::RequireAuthForArgs { address, args }) => {
                assert!(matches!(
                    address.as_ref(),
                    SorobanExpr::SymbolLiteral(symbol) if symbol == "admin"
                ));
                assert!(matches!(
                    args.as_ref(),
                    SorobanExpr::VecConstruct(values)
                        if matches!(values.as_slice(), [SorobanExpr::U32Literal(7)])
                ));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn auth_hints_do_not_repair_when_ambiguous() {
        let hints = auth_hints(
            "transfer",
            vec![
                (
                    Some(HintValue::Symbol("admin".to_string())),
                    vec![HintValue::U64(1)],
                ),
                (
                    Some(HintValue::Symbol("admin".to_string())),
                    vec![HintValue::U64(2)],
                ),
            ],
        );
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::RequireAuthForArgs {
            address: Box::new(SorobanExpr::UnknownVal),
            args: Box::new(SorobanExpr::UnknownVal),
        })];

        if let Some(hint) = unique_auth_hint_for_function(&matching(&hints, "transfer")) {
            repair_weak_auth_from_hint(&mut body, &hint);
        }

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::RequireAuthForArgs { address, args }) => {
                assert!(matches!(address.as_ref(), SorobanExpr::UnknownVal));
                assert!(matches!(args.as_ref(), SorobanExpr::UnknownVal));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn auth_hints_repair_when_args_contain_bytes_values() {
        // Bytes args used to short-circuit hint repair. With BytesLiteral in
        // the IR they now flow through; verify a Bytes arg surfaces correctly.
        let hints = auth_hints(
            "transfer",
            vec![(
                Some(HintValue::Symbol("admin".to_string())),
                vec![HintValue::Bytes(vec![1, 2, 3])],
            )],
        );

        let hint = unique_auth_hint_for_function(&matching(&hints, "transfer"))
            .expect("Bytes-valued auth args hint should now repair");
        match &hint.args {
            SorobanExpr::VecConstruct(items) => {
                assert!(matches!(
                    &items[0],
                    SorobanExpr::BytesLiteral(b) if b == &[1u8, 2, 3]
                ));
            }
            other => panic!("expected VecConstruct, got: {other:?}"),
        }

        // Bytes is also valid as an address hint value now.
        let bytes_address_hints = auth_hints(
            "transfer",
            vec![(
                Some(HintValue::Bytes(vec![9, 9, 9])),
                vec![HintValue::U64(1)],
            )],
        );
        let bytes_addr_hint =
            unique_auth_hint_for_function(&matching(&bytes_address_hints, "transfer"))
                .expect("Bytes-valued auth address hint should now repair");
        assert!(matches!(
            &bytes_addr_hint.address,
            Some(SorobanExpr::BytesLiteral(b)) if b == &[9u8, 9, 9]
        ));
    }

    #[test]
    fn auth_hints_preserve_concrete_auth_expressions() {
        let hints = auth_hints(
            "transfer",
            vec![(
                Some(HintValue::Symbol("admin".to_string())),
                vec![HintValue::Symbol("hinted".to_string())],
            )],
        );
        let hint = unique_auth_hint_for_function(&matching(&hints, "transfer"))
            .expect("auth hint should be unique");
        let mut body = vec![
            SorobanStmt::Expr(SorobanExpr::RequireAuth(Box::new(SorobanExpr::Param(
                "user".to_string(),
            )))),
            SorobanStmt::Expr(SorobanExpr::RequireAuthForArgs {
                address: Box::new(SorobanExpr::Param("user".to_string())),
                args: Box::new(SorobanExpr::VecConstruct(vec![SorobanExpr::SymbolLiteral(
                    "existing".to_string(),
                )])),
            }),
        ];

        repair_weak_auth_from_hint(&mut body, &hint);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::RequireAuth(address)) => {
                assert!(matches!(address.as_ref(), SorobanExpr::Param(name) if name == "user"));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
        match &body[1] {
            SorobanStmt::Expr(SorobanExpr::RequireAuthForArgs { address, args }) => {
                assert!(matches!(address.as_ref(), SorobanExpr::Param(name) if name == "user"));
                assert!(matches!(
                    args.as_ref(),
                    SorobanExpr::VecConstruct(values)
                        if matches!(values.as_slice(), [SorobanExpr::SymbolLiteral(symbol)] if symbol == "existing")
                ));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    fn test_params() -> Vec<crate::ir::high_level_ir::FnParam> {
        vec![
            crate::ir::high_level_ir::FnParam {
                name: "a".to_string(),
                type_def: ScSpecTypeDef::I64,
            },
            crate::ir::high_level_ir::FnParam {
                name: "b".to_string(),
                type_def: ScSpecTypeDef::I64,
            },
        ]
    }

    #[test]
    fn resolve_param_locals_uses_slot_zero_when_env_is_elided() {
        let mut body = vec![SorobanStmt::Return(Some(SorobanExpr::Add(
            Box::new(SorobanExpr::Local(0)),
            Box::new(SorobanExpr::Local(1)),
        )))];

        resolve_param_locals(&mut body, &test_params(), 0);

        match &body[0] {
            SorobanStmt::Return(Some(SorobanExpr::Add(left, right))) => {
                assert!(matches!(left.as_ref(), SorobanExpr::Param(name) if name == "a"));
                assert!(matches!(right.as_ref(), SorobanExpr::Param(name) if name == "b"));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_param_locals_skips_env_slot_when_present_in_wasm() {
        let mut body = vec![SorobanStmt::Return(Some(SorobanExpr::Add(
            Box::new(SorobanExpr::Local(1)),
            Box::new(SorobanExpr::Local(2)),
        )))];

        resolve_param_locals(&mut body, &test_params(), 1);

        match &body[0] {
            SorobanStmt::Return(Some(SorobanExpr::Add(left, right))) => {
                assert!(matches!(left.as_ref(), SorobanExpr::Param(name) if name == "a"));
                assert!(matches!(right.as_ref(), SorobanExpr::Param(name) if name == "b"));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn infer_param_local_base_keeps_preferred_slot_zero_for_env_elided_wrappers() {
        let body = vec![SorobanStmt::Return(Some(SorobanExpr::Add(
            Box::new(SorobanExpr::Local(1)),
            Box::new(SorobanExpr::Local(2)),
        )))];

        let inferred = infer_param_local_base(&body, &test_params(), 0, true);

        assert_eq!(inferred, 0);
    }

    #[test]
    fn infer_param_local_base_keeps_preferred_base_on_tie() {
        let body = vec![SorobanStmt::Return(Some(SorobanExpr::Local(1)))];

        let inferred = infer_param_local_base(&body, &test_params(), 0, true);

        assert_eq!(inferred, 0);
    }

    #[test]
    fn resolve_param_locals_does_not_shift_names_on_ambiguous_tie() {
        let mut body = vec![SorobanStmt::Return(Some(SorobanExpr::Local(1)))];
        let inferred = infer_param_local_base(&body, &test_params(), 0, true);

        resolve_param_locals(&mut body, &test_params(), inferred);

        match &body[0] {
            SorobanStmt::Return(Some(SorobanExpr::Param(name))) => assert_eq!(name, "b"),
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn infer_param_local_base_does_not_shift_for_stray_temp_local() {
        let body = vec![SorobanStmt::Return(Some(SorobanExpr::Local(2)))];

        let inferred = infer_param_local_base(&body, &test_params(), 0, true);

        assert_eq!(inferred, 0);
    }

    #[test]
    fn resolve_param_locals_keeps_stray_temp_local_unmapped() {
        let mut body = vec![SorobanStmt::Return(Some(SorobanExpr::Local(2)))];
        let inferred = infer_param_local_base(&body, &test_params(), 0, true);

        resolve_param_locals(&mut body, &test_params(), inferred);

        match &body[0] {
            SorobanStmt::Return(Some(SorobanExpr::Local(2))) => {}
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn infer_param_local_base_keeps_preferred_base_when_hidden_slots_precede_params() {
        let body = vec![SorobanStmt::Return(Some(SorobanExpr::Add(
            Box::new(SorobanExpr::Local(0)),
            Box::new(SorobanExpr::Local(1)),
        )))];

        let inferred = infer_param_local_base(&body, &test_params(), 2, true);

        assert_eq!(inferred, 2);
    }

    #[test]
    fn resolve_param_locals_does_not_map_hidden_leading_slots_to_params() {
        let mut body = vec![SorobanStmt::Return(Some(SorobanExpr::Add(
            Box::new(SorobanExpr::Local(0)),
            Box::new(SorobanExpr::Local(1)),
        )))];
        let inferred = infer_param_local_base(&body, &test_params(), 2, true);

        resolve_param_locals(&mut body, &test_params(), inferred);

        match &body[0] {
            SorobanStmt::Return(Some(SorobanExpr::Add(left, right))) => {
                assert!(matches!(left.as_ref(), SorobanExpr::Local(0)));
                assert!(matches!(right.as_ref(), SorobanExpr::Local(1)));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn infer_param_local_base_ignores_named_var_slot_like_debug_names() {
        let body = vec![SorobanStmt::Return(Some(SorobanExpr::NamedLocal(
            "var_1".to_string(),
        )))];

        let inferred = infer_param_local_base(&body, &test_params(), 0, true);

        assert_eq!(inferred, 0);
    }

    #[test]
    fn named_var_slot_like_debug_names_do_not_shift_local_param_mapping() {
        let mut body = vec![
            SorobanStmt::Expr(SorobanExpr::NamedLocal("var_1".to_string())),
            SorobanStmt::Return(Some(SorobanExpr::Local(0))),
        ];
        let inferred = infer_param_local_base(&body, &test_params(), 0, true);

        resolve_param_locals(&mut body, &test_params(), inferred);

        match &body[1] {
            SorobanStmt::Return(Some(SorobanExpr::Param(name))) => assert_eq!(name, "a"),
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_param_locals_keeps_same_slot_aliases_mappable() {
        let mut body = vec![
            SorobanStmt::Let {
                name: "var_3".to_string(),
                mutable: false,
                value: SorobanExpr::Local(3),
            },
            SorobanStmt::Return(Some(SorobanExpr::Local(3))),
        ];

        resolve_param_locals(&mut body, &test_params(), 2);

        match &body[1] {
            SorobanStmt::Return(Some(SorobanExpr::Param(name))) => assert_eq!(name, "b"),
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_param_locals_keeps_param_aliases_mappable() {
        let mut body = vec![
            SorobanStmt::Let {
                name: "var_3".to_string(),
                mutable: false,
                value: SorobanExpr::Param("b".to_string()),
            },
            SorobanStmt::Return(Some(SorobanExpr::Local(3))),
        ];

        resolve_param_locals(&mut body, &test_params(), 2);

        match &body[1] {
            SorobanStmt::Return(Some(SorobanExpr::Param(name))) => assert_eq!(name, "b"),
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_param_locals_keeps_wrapped_param_aliases_mappable() {
        let mut body = vec![
            SorobanStmt::Let {
                name: "var_3".to_string(),
                mutable: false,
                value: SorobanExpr::ValConvert {
                    value: Box::new(SorobanExpr::Local(3)),
                    target_type: "i128".to_string(),
                },
            },
            SorobanStmt::Return(Some(SorobanExpr::Local(3))),
        ];

        resolve_param_locals(&mut body, &test_params(), 2);

        match &body[0] {
            SorobanStmt::Let {
                value: SorobanExpr::ValConvert { value, .. },
                ..
            } => {
                assert!(matches!(value.as_ref(), SorobanExpr::Param(name) if name == "b"));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
        match &body[1] {
            SorobanStmt::Return(Some(SorobanExpr::Param(name))) => assert_eq!(name, "b"),
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_event_data_params_repairs_struct_publish_artifacts() {
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::StructConstruct {
                type_name: "Transfer".to_string(),
                fields: vec![
                    ("from".to_string(), SorobanExpr::Param("from".to_string())),
                    ("to".to_string(), SorobanExpr::Param("to".to_string())),
                    (
                        "amount".to_string(),
                        SorobanExpr::NamedLocal("var_3".to_string()),
                    ),
                ],
            }),
            method: "publish".to_string(),
            args: vec![SorobanExpr::Env],
        })];
        let params = vec![
            crate::ir::high_level_ir::FnParam {
                name: "from".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "to".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "amount".to_string(),
                type_def: ScSpecTypeDef::I128,
            },
        ];

        resolve_event_data_params(&mut body, &params, 1);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::MethodCall { object, .. }) => match object.as_ref() {
                SorobanExpr::StructConstruct { fields, .. } => {
                    assert!(matches!(&fields[2].1, SorobanExpr::Param(name) if name == "amount"));
                }
                other => panic!("unexpected object shape: {other:?}"),
            },
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_event_data_params_excludes_sibling_topic_fields_for_struct_publish() {
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::StructConstruct {
                type_name: "Transfer".to_string(),
                fields: vec![
                    ("from".to_string(), SorobanExpr::Param("from".to_string())),
                    (
                        "to".to_string(),
                        SorobanExpr::MethodCall {
                            object: Box::new(SorobanExpr::Param("to".to_string())),
                            method: "address".to_string(),
                            args: vec![],
                        },
                    ),
                    (
                        "amount".to_string(),
                        SorobanExpr::NamedLocal("var_3".to_string()),
                    ),
                ],
            }),
            method: "publish".to_string(),
            args: vec![SorobanExpr::Env],
        })];
        let params = vec![
            crate::ir::high_level_ir::FnParam {
                name: "from".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "to".to_string(),
                type_def: ScSpecTypeDef::MuxedAddress,
            },
            crate::ir::high_level_ir::FnParam {
                name: "amount".to_string(),
                type_def: ScSpecTypeDef::I128,
            },
        ];

        resolve_event_data_params(&mut body, &params, 1);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::MethodCall { object, .. }) => match object.as_ref() {
                SorobanExpr::StructConstruct { fields, .. } => {
                    assert!(matches!(&fields[2].1, SorobanExpr::Param(name) if name == "amount"));
                }
                other => panic!("unexpected object shape: {other:?}"),
            },
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_event_data_params_repairs_top_level_struct_local_fields() {
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::StructConstruct {
                type_name: "Transfer".to_string(),
                fields: vec![
                    ("from".to_string(), SorobanExpr::Param("from".to_string())),
                    ("to".to_string(), SorobanExpr::Param("to".to_string())),
                    ("amount".to_string(), SorobanExpr::Local(3)),
                ],
            }),
            method: "publish".to_string(),
            args: vec![SorobanExpr::Env],
        })];
        let params = vec![
            crate::ir::high_level_ir::FnParam {
                name: "from".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "to".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "amount".to_string(),
                type_def: ScSpecTypeDef::I128,
            },
        ];

        resolve_event_data_params(&mut body, &params, 1);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::MethodCall { object, .. }) => match object.as_ref() {
                SorobanExpr::StructConstruct { fields, .. } => {
                    assert!(matches!(&fields[2].1, SorobanExpr::Param(name) if name == "amount"));
                }
                other => panic!("unexpected object shape: {other:?}"),
            },
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_event_data_params_honors_env_elided_local_numbering_for_publish() {
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::StructConstruct {
                type_name: "Transfer".to_string(),
                fields: vec![
                    ("from".to_string(), SorobanExpr::Param("from".to_string())),
                    ("to".to_string(), SorobanExpr::Param("to".to_string())),
                    ("amount".to_string(), SorobanExpr::Local(2)),
                ],
            }),
            method: "publish".to_string(),
            args: vec![SorobanExpr::Env],
        })];
        let params = vec![
            crate::ir::high_level_ir::FnParam {
                name: "from".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "to".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "amount".to_string(),
                type_def: ScSpecTypeDef::I128,
            },
        ];

        resolve_event_data_params(&mut body, &params, 0);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::MethodCall { object, .. }) => match object.as_ref() {
                SorobanExpr::StructConstruct { fields, .. } => {
                    assert!(matches!(&fields[2].1, SorobanExpr::Param(name) if name == "amount"));
                }
                other => panic!("unexpected object shape: {other:?}"),
            },
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_event_data_params_does_not_index_guess_nested_struct_fields() {
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::StructConstruct {
                type_name: "Payload".to_string(),
                fields: vec![(
                    "nested".to_string(),
                    SorobanExpr::StructConstruct {
                        type_name: "Inner".to_string(),
                        fields: vec![("amount".to_string(), SorobanExpr::Local(3))],
                    },
                )],
            }),
            method: "publish".to_string(),
            args: vec![SorobanExpr::Env],
        })];
        let params = vec![
            crate::ir::high_level_ir::FnParam {
                name: "from".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "to".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "amount".to_string(),
                type_def: ScSpecTypeDef::I128,
            },
            crate::ir::high_level_ir::FnParam {
                name: "fee".to_string(),
                type_def: ScSpecTypeDef::I128,
            },
        ];

        resolve_event_data_params(&mut body, &params, 1);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::MethodCall { object, .. }) => match object.as_ref() {
                SorobanExpr::StructConstruct { fields, .. } => match &fields[0].1 {
                    SorobanExpr::StructConstruct { fields, .. } => {
                        assert!(matches!(&fields[0].1, SorobanExpr::Local(3)));
                    }
                    other => panic!("unexpected nested object shape: {other:?}"),
                },
                other => panic!("unexpected object shape: {other:?}"),
            },
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_event_data_params_does_not_single_candidate_guess_nested_var_names() {
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::StructConstruct {
                type_name: "Payload".to_string(),
                fields: vec![(
                    "nested".to_string(),
                    SorobanExpr::StructConstruct {
                        type_name: "Inner".to_string(),
                        fields: vec![(
                            "amount".to_string(),
                            SorobanExpr::NamedLocal("var_7".to_string()),
                        )],
                    },
                )],
            }),
            method: "publish".to_string(),
            args: vec![SorobanExpr::Env],
        })];
        let params = vec![
            crate::ir::high_level_ir::FnParam {
                name: "from".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "amount".to_string(),
                type_def: ScSpecTypeDef::I128,
            },
        ];

        resolve_event_data_params(&mut body, &params, 1);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::MethodCall { object, .. }) => match object.as_ref() {
                SorobanExpr::StructConstruct { fields, .. } => match &fields[0].1 {
                    SorobanExpr::StructConstruct { fields, .. } => {
                        assert!(
                            matches!(&fields[0].1, SorobanExpr::NamedLocal(name) if name == "var_7")
                        );
                    }
                    other => panic!("unexpected nested object shape: {other:?}"),
                },
                other => panic!("unexpected object shape: {other:?}"),
            },
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_event_data_params_does_not_rewrite_non_event_publish_methods() {
        let mut body = vec![SorobanStmt::Expr(SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::MethodCall {
                object: Box::new(SorobanExpr::Local(2)),
                method: "builder".to_string(),
                args: vec![],
            }),
            method: "publish".to_string(),
            args: vec![SorobanExpr::Env],
        })];
        let params = vec![
            crate::ir::high_level_ir::FnParam {
                name: "from".to_string(),
                type_def: ScSpecTypeDef::Address,
            },
            crate::ir::high_level_ir::FnParam {
                name: "amount".to_string(),
                type_def: ScSpecTypeDef::I128,
            },
        ];

        resolve_event_data_params(&mut body, &params, 0);

        match &body[0] {
            SorobanStmt::Expr(SorobanExpr::MethodCall { object, .. }) => match object.as_ref() {
                SorobanExpr::MethodCall { object, .. } => {
                    assert!(matches!(object.as_ref(), SorobanExpr::Local(2)));
                }
                other => panic!("unexpected object shape: {other:?}"),
            },
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn unique_wasm_opt_temp_dir_paths_do_not_reuse_fixed_names() {
        let first = unique_wasm_opt_temp_dir_path();
        let second = unique_wasm_opt_temp_dir_path();

        assert_ne!(first, second);
        assert_ne!(
            first.file_name().and_then(|name| name.to_str()),
            Some("stellar_decompile_opt_input.wasm")
        );
        assert_ne!(
            second.file_name().and_then(|name| name.to_str()),
            Some("stellar_decompile_opt_output.wasm")
        );
    }

    #[test]
    fn wasm_opt_temp_dir_cleans_up_its_workspace() {
        let path = {
            let temp_dir = WasmOptTempDir::new().expect("temp dir should be created");
            let marker = temp_dir.path().join("marker.txt");
            std::fs::write(&marker, b"ok").expect("marker should be written");
            assert!(temp_dir.path().exists());
            temp_dir.path().to_path_buf()
        };

        assert!(!path.exists());
    }

    fn single_test_param() -> Vec<crate::ir::high_level_ir::FnParam> {
        vec![crate::ir::high_level_ir::FnParam {
            name: "arg".to_string(),
            type_def: ScSpecTypeDef::I64,
        }]
    }

    #[test]
    fn infer_param_local_base_keeps_env_slot_for_single_param_wrapper() {
        let body = vec![SorobanStmt::Return(Some(SorobanExpr::Local(0)))];

        let inferred = infer_param_local_base(&body, &single_test_param(), 1, true);

        assert_eq!(inferred, 1);
    }

    #[test]
    fn resolve_param_locals_does_not_remap_env_slot_to_single_param() {
        let mut body = vec![SorobanStmt::Return(Some(SorobanExpr::Local(0)))];
        let inferred = infer_param_local_base(&body, &single_test_param(), 1, true);

        resolve_param_locals(&mut body, &single_test_param(), inferred);

        match &body[0] {
            SorobanStmt::Return(Some(SorobanExpr::Local(0))) => {}
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    #[test]
    fn resolve_param_locals_does_not_shift_slot_zero_params_when_temp_mimics_env_shift() {
        let mut body = vec![SorobanStmt::Return(Some(SorobanExpr::Add(
            Box::new(SorobanExpr::Local(1)),
            Box::new(SorobanExpr::Local(2)),
        )))];
        let inferred = infer_param_local_base(&body, &test_params(), 0, true);

        resolve_param_locals(&mut body, &test_params(), inferred);

        match &body[0] {
            SorobanStmt::Return(Some(SorobanExpr::Add(left, right))) => {
                assert!(matches!(left.as_ref(), SorobanExpr::Param(name) if name == "b"));
                assert!(matches!(right.as_ref(), SorobanExpr::Local(2)));
            }
            other => panic!("unexpected stmt shape: {other:?}"),
        }
    }

    // ----- Val tag expression walkers (issue #4) ----------------------

    /// Every `&mut SorobanExpr` repair walker must traverse `ValTag` (recurse into
    /// its inner value) and treat `ValTagName` as a leaf, without panicking. A
    /// `ValTag` wrapping a benign `Param` is left unchanged by each repair.
    #[test]
    fn repair_walkers_traverse_val_tag_expressions() {
        let tag = || SorobanExpr::ValTag(Box::new(SorobanExpr::Param("v".to_string())));
        let name = || SorobanExpr::ValTagName("VecObject".to_string());
        let replacement = SorobanExpr::Param("repl".to_string());

        let mut e = tag();
        repair_unknown_invoke_functions_in_expr(&mut e, &replacement);
        assert_eq!(e, tag());
        let mut e = name();
        repair_unknown_invoke_functions_in_expr(&mut e, &replacement);
        assert_eq!(e, name());

        let mut e = tag();
        repair_unknown_storage_keys_in_expr(&mut e, &replacement);
        assert_eq!(e, tag());

        let event_hint = EventRepairHint {
            topics: Vec::new(),
            data: Vec::new(),
        };
        let mut e = tag();
        repair_unknown_event_values_in_expr(&mut e, &event_hint);
        assert_eq!(e, tag());
        let mut e = name();
        repair_unknown_event_values_in_expr(&mut e, &event_hint);
        assert_eq!(e, name());

        let auth_hint = AuthRepairHint {
            address: None,
            args: SorobanExpr::Void,
        };
        let mut e = tag();
        repair_weak_auth_in_expr(&mut e, &auth_hint);
        assert_eq!(e, tag());

        // Read-only scorer: traverses ValTag, scores the inner param.
        let rebound = std::collections::HashSet::new();
        let score = score_param_local_base_in_expr(&tag(), 0, 0, &rebound);
        assert_eq!(score.total_hits, 0);
    }

    // ---------------------------------------------------------------------
    // Phase 1: data-carrying-enum identity round-trip recognition.
    // ---------------------------------------------------------------------

    fn enum_arm(variant: &str, body: Vec<SorobanStmt>) -> MatchArm {
        MatchArm {
            pattern: MatchPattern::EnumVariant {
                type_name: "E".into(),
                variant: variant.into(),
                bindings: vec![],
            },
            body,
        }
    }

    /// The aquarius-style decode→match→re-encode identity shape: each arm reads `v`
    /// and re-encodes only its own variant. Must be recognized as identity.
    #[test]
    fn enum_identity_roundtrip_accepts_self_reencode() {
        let body = vec![
            // decode preamble: tag guard + len + discriminant read
            SorobanStmt::If {
                condition: SorobanExpr::Ne(
                    Box::new(SorobanExpr::ValTag(Box::new(SorobanExpr::Param(
                        "v".into(),
                    )))),
                    Box::new(SorobanExpr::ValTagName("VecObject".into())),
                ),
                then_body: vec![SorobanStmt::Expr(SorobanExpr::Panic)],
                else_body: vec![],
            },
            SorobanStmt::Expr(SorobanExpr::MethodCall {
                object: Box::new(SorobanExpr::Param("v".into())),
                method: "get".into(),
                args: vec![SorobanExpr::U32Literal(0)],
            }),
            SorobanStmt::Match {
                scrutinee: SorobanExpr::Param("v".into()),
                arms: vec![
                    enum_arm(
                        "VarA",
                        vec![SorobanStmt::Expr(SorobanExpr::SymbolLiteral("VarA".into()))],
                    ),
                    enum_arm(
                        "VarB",
                        vec![
                            SorobanStmt::Let {
                                name: "x".into(),
                                mutable: false,
                                value: SorobanExpr::FieldAccess {
                                    object: Box::new(SorobanExpr::MethodCall {
                                        object: Box::new(SorobanExpr::Param("v".into())),
                                        method: "get".into(),
                                        args: vec![SorobanExpr::U32Literal(1)],
                                    }),
                                    field: "a".into(),
                                },
                            },
                            SorobanStmt::Expr(SorobanExpr::SymbolLiteral("VarB".into())),
                        ],
                    ),
                ],
            },
        ];
        assert!(is_enum_identity_roundtrip(&body, "v"));
    }

    /// A permutation `match v { VarA => VarB, .. }` re-encodes a FOREIGN variant — it
    /// is NOT an identity and must be rejected (so it is not collapsed to `v`).
    #[test]
    fn enum_identity_roundtrip_rejects_foreign_variant_reencode() {
        let body = vec![SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("v".into()),
            arms: vec![enum_arm(
                "VarA",
                // arm VarA re-encodes VarB → transform, not identity
                vec![SorobanStmt::Expr(SorobanExpr::SymbolLiteral("VarB".into()))],
            )],
        }];
        assert!(!is_enum_identity_roundtrip(&body, "v"));
    }

    /// An arm with a side effect (storage write) or that reads another parameter is
    /// real logic, not a round-trip — must be rejected.
    #[test]
    fn enum_identity_roundtrip_rejects_side_effects_and_foreign_param() {
        let with_store = vec![SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("v".into()),
            arms: vec![enum_arm(
                "VarA",
                vec![SorobanStmt::Expr(SorobanExpr::StorageSet {
                    storage_type: StorageType::Persistent,
                    key: Box::new(SorobanExpr::SymbolLiteral("k".into())),
                    value: Box::new(SorobanExpr::Param("v".into())),
                })],
            )],
        }];
        assert!(!is_enum_identity_roundtrip(&with_store, "v"));

        let foreign_param = vec![SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("v".into()),
            arms: vec![enum_arm(
                "VarA",
                vec![SorobanStmt::Expr(SorobanExpr::Param("other".into()))],
            )],
        }];
        assert!(!is_enum_identity_roundtrip(&foreign_param, "v"));
    }

    /// No match (the other identity passes handle empty / single-get bodies), or a
    /// scrutinee that isn't the passthrough param → not this recognizer's job.
    #[test]
    fn enum_identity_roundtrip_rejects_non_match_and_wrong_scrutinee() {
        assert!(!is_enum_identity_roundtrip(
            &[SorobanStmt::Return(Some(SorobanExpr::Param("v".into())))],
            "v"
        ));
        let wrong_scrutinee = vec![SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("w".into()),
            arms: vec![enum_arm(
                "VarA",
                vec![SorobanStmt::Expr(SorobanExpr::SymbolLiteral("VarA".into()))],
            )],
        }];
        assert!(!is_enum_identity_roundtrip(&wrong_scrutinee, "v"));
    }
}
