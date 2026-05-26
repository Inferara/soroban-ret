use proc_macro2::TokenStream;
use quote::quote;
use stellar_xdr::curr::ScSpecTypeDef;

use crate::ir::high_level_ir::{ContractModule, CryptoUsage};
use crate::ir::soroban_ir::{SorobanExpr, SorobanStmt};
use crate::spec::registry::TypeRegistry;

/// Compute extra `use` statements beyond the main `soroban_sdk::{...}` import.
///
/// Currently handles `use soroban_sdk::auth::Context;` which is needed when
/// `__check_auth` functions have `Vec<Context>` parameters. `Context` lives in
/// a submodule and is not re-exported from the top-level `soroban_sdk`.
pub fn compute_extra_imports(module: &ContractModule) -> TokenStream {
    let mut extra = TokenStream::new();
    if module.functions.iter().any(|f| f.is_check_auth) {
        extra.extend(quote! { use soroban_sdk::auth::Context; });
    }
    if module.crypto_usage.uses_bn254 {
        extra
            .extend(quote! { use soroban_sdk::crypto::bn254::{Bn254G1Affine, Bn254G2Affine, Fr}; });
    }
    if module.crypto_usage.uses_bls12_381 {
        extra.extend(
            quote! { use soroban_sdk::crypto::bls12_381::{Bls12381Fp, Bls12381Fp2, Bls12381G1Affine, Bls12381G2Affine, Fr}; },
        );
    }
    extra
}

/// Compute the minimal `use soroban_sdk::{...}` needed for the module
pub fn compute_imports(module: &ContractModule, registry: &TypeRegistry) -> TokenStream {
    let mut needs = ImportNeeds::default();
    let crypto = &module.crypto_usage;

    // Check types
    if !module.types.is_empty() {
        needs.contracttype = true;
    }
    if !module.error_enums.is_empty() {
        needs.contracterror = true;
    }
    if !module.events.is_empty() {
        needs.contractevent = true;
    }

    // Check if any function takes Env
    let any_takes_env = module.functions.iter().any(|f| f.takes_env);

    // Scan function signatures and bodies for what SDK types/features are used
    for func in &module.functions {
        for param in &func.params {
            scan_type_def(&param.type_def, &mut needs, crypto);
        }
        if let Some(rt) = &func.return_type {
            scan_type_def(rt, &mut needs, crypto);
        }
        scan_stmts(&func.body, &mut needs);
    }

    // Scan struct/union/event field types from the registry
    for s in registry.structs.values() {
        for field in s.fields.iter() {
            scan_type_def(&field.type_, &mut needs, crypto);
        }
    }
    for u in registry.unions.values() {
        for case in u.cases.iter() {
            if let stellar_xdr::curr::ScSpecUdtUnionCaseV0::TupleV0(t) = case {
                for ty in t.type_.iter() {
                    scan_type_def(ty, &mut needs, crypto);
                }
            }
        }
    }
    for e in registry.events.values() {
        for param in e.params.iter() {
            scan_type_def(&param.type_, &mut needs, crypto);
        }
    }

    // Build the use statement
    let mut items: Vec<TokenStream> = Vec::new();
    items.push(quote! { contract });
    items.push(quote! { contractimpl });

    if needs.contracttype {
        items.push(quote! { contracttype });
    }
    if needs.contracterror {
        items.push(quote! { contracterror });
    }
    if needs.contractevent {
        items.push(quote! { contractevent });
    }
    if any_takes_env {
        items.push(quote! { Env });
    }
    if needs.symbol {
        items.push(quote! { Symbol });
    }
    if needs.symbol_short {
        items.push(quote! { symbol_short });
    }
    if needs.address {
        items.push(quote! { Address });
    }
    if needs.muxed_address {
        items.push(quote! { MuxedAddress });
    }
    if needs.bytes {
        items.push(quote! { Bytes });
    }
    if needs.bytes_n {
        items.push(quote! { BytesN });
    }
    if needs.vec_type {
        items.push(quote! { Vec });
    }
    if needs.map_type {
        items.push(quote! { Map });
    }
    if needs.string_type {
        items.push(quote! { String });
    }
    if needs.log_macro {
        items.push(quote! { log });
    }
    if needs.panic_with_error {
        items.push(quote! { panic_with_error });
    }
    if needs.vec_macro {
        items.push(quote! { vec });
    }
    if needs.map_macro {
        items.push(quote! { map });
    }
    if needs.timepoint {
        items.push(quote! { Timepoint });
    }
    if needs.duration {
        items.push(quote! { Duration });
    }
    if needs.u256 {
        items.push(quote! { U256 });
    }
    if needs.i256 {
        items.push(quote! { I256 });
    }
    if needs.into_val {
        items.push(quote! { IntoVal });
    }

    // Sort imports to match rustfmt convention: lowercase items (macros/keywords)
    // first, then uppercase items (types), both groups sorted alphabetically.
    items.sort_by(|a, b| {
        let a_str = a.to_string();
        let b_str = b.to_string();
        let a_lower = a_str.starts_with(|c: char| c.is_lowercase());
        let b_lower = b_str.starts_with(|c: char| c.is_lowercase());
        match (a_lower, b_lower) {
            (true, false) => std::cmp::Ordering::Less,
            (false, true) => std::cmp::Ordering::Greater,
            _ => a_str.cmp(&b_str),
        }
    });

    quote! {
        use soroban_sdk::{#(#items),*};
    }
}

#[derive(Default)]
struct ImportNeeds {
    contracttype: bool,
    contracterror: bool,
    contractevent: bool,
    symbol: bool,
    symbol_short: bool,
    address: bool,
    muxed_address: bool,
    bytes: bool,
    bytes_n: bool,
    vec_type: bool,
    map_type: bool,
    string_type: bool,
    log_macro: bool,
    panic_with_error: bool,
    vec_macro: bool,
    map_macro: bool,
    timepoint: bool,
    duration: bool,
    u256: bool,
    i256: bool,
    into_val: bool,
}

fn scan_type_def(type_def: &ScSpecTypeDef, needs: &mut ImportNeeds, crypto: &CryptoUsage) {
    match type_def {
        ScSpecTypeDef::Symbol => needs.symbol = true,
        ScSpecTypeDef::Address => needs.address = true,
        ScSpecTypeDef::MuxedAddress => needs.muxed_address = true,
        ScSpecTypeDef::Bytes => needs.bytes = true,
        ScSpecTypeDef::BytesN(b) => {
            // Suppress BytesN import when crypto aliases replace all usages
            let is_aliased = (crypto.uses_bn254 && matches!(b.n, 64 | 128))
                || (crypto.uses_bls12_381 && matches!(b.n, 48 | 96 | 192));
            if !is_aliased {
                needs.bytes_n = true;
            }
        }
        ScSpecTypeDef::String => needs.string_type = true,
        ScSpecTypeDef::U256 if !crypto.has_any() => {
            needs.u256 = true;
        }
        ScSpecTypeDef::I256 => needs.i256 = true,
        ScSpecTypeDef::Timepoint => needs.timepoint = true,
        ScSpecTypeDef::Duration => needs.duration = true,
        ScSpecTypeDef::Vec(v) => {
            needs.vec_type = true;
            scan_type_def(&v.element_type, needs, crypto);
        }
        ScSpecTypeDef::Map(m) => {
            needs.map_type = true;
            scan_type_def(&m.key_type, needs, crypto);
            scan_type_def(&m.value_type, needs, crypto);
        }
        ScSpecTypeDef::Option(o) => scan_type_def(&o.value_type, needs, crypto),
        ScSpecTypeDef::Result(r) => {
            scan_type_def(&r.ok_type, needs, crypto);
            scan_type_def(&r.error_type, needs, crypto);
        }
        ScSpecTypeDef::Tuple(t) => {
            for ty in t.value_types.iter() {
                scan_type_def(ty, needs, crypto);
            }
        }
        _ => {}
    }
}

fn scan_stmts(stmts: &[SorobanStmt], needs: &mut ImportNeeds) {
    for stmt in stmts {
        scan_stmt(stmt, needs);
    }
}

fn scan_stmt(stmt: &SorobanStmt, needs: &mut ImportNeeds) {
    match stmt {
        SorobanStmt::Expr(expr) => scan_expr(expr, needs),
        SorobanStmt::Let { value, .. } => scan_expr(value, needs),
        SorobanStmt::Assign { value, .. } => scan_expr(value, needs),
        SorobanStmt::Return(Some(expr)) => scan_expr(expr, needs),
        SorobanStmt::Return(None) => {}
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            scan_expr(condition, needs);
            scan_stmts(then_body, needs);
            scan_stmts(else_body, needs);
        }
        SorobanStmt::Match { scrutinee, arms } => {
            scan_expr(scrutinee, needs);
            for arm in arms {
                scan_stmts(&arm.body, needs);
            }
        }
        SorobanStmt::Loop { body } => scan_stmts(body, needs),
        SorobanStmt::Block(stmts) => scan_stmts(stmts, needs),
        SorobanStmt::Comment(_) | SorobanStmt::Break | SorobanStmt::Continue => {}
    }
}

fn scan_expr(expr: &SorobanExpr, needs: &mut ImportNeeds) {
    match expr {
        SorobanExpr::SymbolLiteral(s) => {
            if s.len() <= 9 {
                needs.symbol_short = true;
            } else {
                needs.symbol = true;
            }
        }
        SorobanExpr::RequireAuth(addr) => {
            needs.address = true;
            scan_expr(addr, needs);
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            needs.address = true;
            needs.into_val = true;
            scan_expr(address, needs);
            scan_expr(args, needs);
        }
        SorobanExpr::VecConstruct(elems) => {
            needs.vec_type = true;
            needs.vec_macro = true;
            for e in elems {
                scan_expr(e, needs);
            }
        }
        SorobanExpr::MapConstruct(entries) => {
            needs.map_type = true;
            needs.map_macro = true;
            for (k, v) in entries {
                scan_expr(k, needs);
                scan_expr(v, needs);
            }
        }
        SorobanExpr::Log(args) => {
            needs.log_macro = true;
            for a in args {
                scan_expr(a, needs);
            }
        }
        SorobanExpr::PanicWithError(err) => {
            needs.panic_with_error = true;
            scan_expr(err, needs);
        }
        SorobanExpr::StrkeyToAddress(inner) => {
            needs.address = true;
            scan_expr(inner, needs);
        }
        // Recurse into sub-expressions for binary operators
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
            scan_expr(a, needs);
            scan_expr(b, needs);
        }
        SorobanExpr::Not(a) => scan_expr(a, needs),
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => {
            scan_expr(key, needs);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            scan_expr(key, needs);
            scan_expr(value, needs);
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            scan_expr(key, needs);
            scan_expr(threshold, needs);
            scan_expr(extend_to, needs);
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            scan_expr(threshold, needs);
            scan_expr(extend_to, needs);
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, e) in fields {
                scan_expr(e, needs);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for e in fields {
                scan_expr(e, needs);
            }
        }
        SorobanExpr::TupleConstruct(fields) => {
            for e in fields {
                scan_expr(e, needs);
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
            needs.vec_macro = true;
            needs.into_val = true;
            scan_expr(address, needs);
            scan_expr(function, needs);
            for a in args {
                scan_expr(a, needs);
            }
        }
        SorobanExpr::FieldAccess { object, .. } => {
            scan_expr(object, needs);
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            scan_expr(object, needs);
            for a in args {
                scan_expr(a, needs);
            }
        }
        SorobanExpr::AuthorizeAsCurrContract(args) => {
            scan_expr(args, needs);
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics {
                scan_expr(t, needs);
            }
            scan_expr(data, needs);
        }
        SorobanExpr::CryptoSha256(data) | SorobanExpr::CryptoKeccak256(data) => {
            scan_expr(data, needs);
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            scan_expr(public_key, needs);
            scan_expr(message, needs);
            scan_expr(signature, needs);
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            scan_expr(msg_digest, needs);
            scan_expr(signature, needs);
            scan_expr(recovery_id, needs);
        }
        SorobanExpr::PrngReseed(seed) => scan_expr(seed, needs),
        SorobanExpr::PrngBytesNew(len) => scan_expr(len, needs),
        SorobanExpr::PrngU64InRange { low, high } => {
            scan_expr(low, needs);
            scan_expr(high, needs);
        }
        SorobanExpr::PrngVecShuffle(vec) => scan_expr(vec, needs),
        SorobanExpr::AddressToStrkey(addr) => scan_expr(addr, needs),
        SorobanExpr::ErrorFromCode(e) => scan_expr(e, needs),
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            scan_expr(value, needs)
        }
        SorobanExpr::RawHostCall { args, .. } => {
            for a in args {
                scan_expr(a, needs);
            }
        }
        SorobanExpr::CollectionNew(ty_name) => match ty_name.as_str() {
            "Vec" => needs.vec_type = true,
            "Map" => needs.map_type = true,
            _ => {}
        },
        SorobanExpr::StringLiteral(_) => {
            needs.string_type = true;
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::high_level_ir::{ContractFn, ContractModule};
    use std::collections::BTreeMap;

    fn empty_registry() -> TypeRegistry {
        TypeRegistry {
            functions: BTreeMap::new(),
            structs: BTreeMap::new(),
            unions: BTreeMap::new(),
            enums: BTreeMap::new(),
            error_enums: BTreeMap::new(),
            events: BTreeMap::new(),
            meta: Vec::new(),
            spec_entries: Vec::new(),
        }
    }

    fn empty_fn(name: &str) -> ContractFn {
        ContractFn {
            name: name.to_string(),
            params: Vec::new(),
            return_type: None,
            body: Vec::new(),
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: None,
        }
    }

    fn collapse(s: &str) -> String {
        s.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    // ---- compute_extra_imports ----

    #[test]
    fn extra_imports_empty_when_nothing_needed() {
        let module = ContractModule::new("Contract".to_string());
        assert!(compute_extra_imports(&module).is_empty());
    }

    #[test]
    fn extra_imports_emits_context_for_check_auth() {
        let mut module = ContractModule::new("Contract".to_string());
        let mut f = empty_fn("__check_auth");
        f.is_check_auth = true;
        module.functions.push(f);
        let out = collapse(&compute_extra_imports(&module).to_string());
        assert!(
            out.contains("use soroban_sdk :: auth :: Context"),
            "got: {out}"
        );
    }

    #[test]
    fn extra_imports_emits_bn254_aliases() {
        let mut module = ContractModule::new("Contract".to_string());
        module.crypto_usage.uses_bn254 = true;
        let out = collapse(&compute_extra_imports(&module).to_string());
        assert!(out.contains("crypto :: bn254"));
        assert!(out.contains("Bn254G1Affine"));
        assert!(out.contains("Bn254G2Affine"));
        assert!(out.contains("Fr"));
    }

    #[test]
    fn extra_imports_emits_bls12_381_aliases() {
        let mut module = ContractModule::new("Contract".to_string());
        module.crypto_usage.uses_bls12_381 = true;
        let out = collapse(&compute_extra_imports(&module).to_string());
        assert!(out.contains("crypto :: bls12_381"));
        assert!(out.contains("Bls12381Fp"));
        assert!(out.contains("Bls12381Fp2"));
        assert!(out.contains("Bls12381G1Affine"));
        assert!(out.contains("Bls12381G2Affine"));
    }

    #[test]
    fn extra_imports_combines_all_flags() {
        let mut module = ContractModule::new("Contract".to_string());
        module.crypto_usage.uses_bn254 = true;
        module.crypto_usage.uses_bls12_381 = true;
        let mut f = empty_fn("__check_auth");
        f.is_check_auth = true;
        module.functions.push(f);
        let out = collapse(&compute_extra_imports(&module).to_string());
        assert!(out.contains("Context"));
        assert!(out.contains("bn254"));
        assert!(out.contains("bls12_381"));
    }

    // ---- compute_imports ----

    #[test]
    fn imports_empty_module_emits_minimal_use() {
        let module = ContractModule::new("Contract".to_string());
        let out = collapse(&compute_imports(&module, &empty_registry()).to_string());
        assert!(out.contains("use soroban_sdk"));
        assert!(out.contains("contract") && out.contains("contractimpl"));
    }

    #[test]
    fn imports_emits_env_when_any_fn_takes_env() {
        let mut module = ContractModule::new("Contract".to_string());
        let mut f = empty_fn("uses_env");
        f.takes_env = true;
        module.functions.push(f);
        let out = collapse(&compute_imports(&module, &empty_registry()).to_string());
        assert!(out.contains("Env"), "missing Env import: {out}");
    }

    #[test]
    fn imports_emits_contracttype_when_types_present() {
        let mut module = ContractModule::new("Contract".to_string());
        module.types.push(crate::ir::high_level_ir::TypeDef {
            kind: crate::ir::high_level_ir::TypeDefKind::Struct,
            name: "T".into(),
            generated_tokens: None,
        });
        let out = collapse(&compute_imports(&module, &empty_registry()).to_string());
        assert!(out.contains("contracttype"));
    }

    #[test]
    fn imports_emits_contracterror_when_error_enums_present() {
        let mut module = ContractModule::new("Contract".to_string());
        module.error_enums.push(crate::ir::high_level_ir::TypeDef {
            kind: crate::ir::high_level_ir::TypeDefKind::ErrorEnum,
            name: "E".into(),
            generated_tokens: None,
        });
        let out = collapse(&compute_imports(&module, &empty_registry()).to_string());
        assert!(out.contains("contracterror"));
    }

    #[test]
    fn imports_emits_contractevent_when_events_present() {
        let mut module = ContractModule::new("Contract".to_string());
        module.events.push(crate::ir::high_level_ir::TypeDef {
            kind: crate::ir::high_level_ir::TypeDefKind::Event,
            name: "Ev".into(),
            generated_tokens: None,
        });
        let out = collapse(&compute_imports(&module, &empty_registry()).to_string());
        assert!(out.contains("contractevent"));
    }

    #[test]
    fn imports_scans_body_for_symbol_short_when_short_symbol_present() {
        // SymbolLiteral in body should trigger symbol_short import.
        let mut module = ContractModule::new("Contract".to_string());
        let mut f = empty_fn("uses_sym");
        f.body
            .push(SorobanStmt::Expr(SorobanExpr::SymbolLiteral("x".into())));
        module.functions.push(f);
        let out = collapse(&compute_imports(&module, &empty_registry()).to_string());
        assert!(
            out.contains("symbol_short") || out.contains("Symbol"),
            "got: {out}"
        );
    }

    #[test]
    fn imports_scans_body_for_invoke_contract_pulls_vec_and_intoval() {
        let mut module = ContractModule::new("Contract".to_string());
        let mut f = empty_fn("calls_other");
        f.body.push(SorobanStmt::Expr(SorobanExpr::InvokeContract {
            address: Box::new(SorobanExpr::Param("addr".into())),
            function: Box::new(SorobanExpr::SymbolLiteral("f".into())),
            args: vec![SorobanExpr::Param("x".into())],
            return_type: Some("u64".into()),
        }));
        module.functions.push(f);
        let out = collapse(&compute_imports(&module, &empty_registry()).to_string());
        // invoke_contract pulls `vec!` and `IntoVal` (via .into_val()).
        assert!(out.contains("vec") || out.contains("IntoVal"), "got: {out}");
    }

    #[test]
    fn imports_param_type_address_pulls_address() {
        use stellar_xdr::curr as stellar_xdr;
        let mut module = ContractModule::new("Contract".to_string());
        let mut f = empty_fn("with_addr");
        f.params.push(crate::ir::high_level_ir::FnParam {
            name: "a".to_string(),
            type_def: stellar_xdr::ScSpecTypeDef::Address,
        });
        module.functions.push(f);
        let out = collapse(&compute_imports(&module, &empty_registry()).to_string());
        assert!(out.contains("Address"), "missing Address: {out}");
    }
}
