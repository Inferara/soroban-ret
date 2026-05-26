use crate::spec::registry::TypeRegistry;
/// Dispatch peeling.
///
/// Soroban contracts export wrapper functions that convert Val arguments to typed
/// params, call the real function, and convert the result back. This module identifies
/// exported functions and maps them to spec entries.
///
/// With LTO optimization (opt-level "z"), the 2-3 layer dispatch chain may be
/// inlined into a single function. We handle this by working from exports + spec
/// rather than trying to recognize the wrapper structure.
use crate::wasm::WasmModule;

/// A resolved contract function: maps an export to its spec entry.
#[derive(Debug)]
pub struct ResolvedFunction {
    pub export_name: String,
    pub func_index: u32,
    pub is_constructor: bool,
    pub is_check_auth: bool,
}

/// Resolve all exported contract functions against the spec.
pub fn resolve_exports(module: &WasmModule, registry: &TypeRegistry) -> Vec<ResolvedFunction> {
    let mut resolved = Vec::new();

    for export in module.exports.contract_functions() {
        // Skip exports that don't correspond to spec functions
        // (there might be internal helpers exported)
        let is_spec_fn = registry.get_function(&export.name).is_some();
        let is_constructor = export.name == "__constructor";
        let is_check_auth = export.name == "__check_auth";

        if is_spec_fn || is_constructor || is_check_auth {
            resolved.push(ResolvedFunction {
                export_name: export.name.clone(),
                func_index: export.func_index,
                is_constructor,
                is_check_auth,
            });
        }
    }

    resolved
}

/// Resolve all exported functions for generic (non-Soroban) WASM.
/// Includes all user-visible exports, filtering out toolchain internals.
pub fn resolve_exports_generic(module: &WasmModule) -> Vec<ResolvedFunction> {
    module
        .exports
        .contract_functions()
        .filter(|e| !e.name.starts_with('_'))
        .map(|export| ResolvedFunction {
            export_name: export.name.clone(),
            func_index: export.func_index,
            is_constructor: false,
            is_check_auth: false,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn load(wasm: &[u8]) -> (WasmModule, TypeRegistry) {
        let module = WasmModule::parse(wasm).expect("wasm parse");
        let registry = TypeRegistry::from_wasm(wasm).expect("spec extract");
        (module, registry)
    }

    #[test]
    fn resolve_exports_picks_up_spec_functions() {
        let wasm = include_bytes!("../../../../tests/fixtures/test_add_u64.wasm");
        let (module, registry) = load(wasm);
        let resolved = resolve_exports(&module, &registry);
        assert!(
            resolved.iter().any(|r| r.export_name == "add"),
            "expected `add` export among resolved: {:?}",
            resolved.iter().map(|r| &r.export_name).collect::<Vec<_>>()
        );
        // All resolved spec fns should have constructor/check_auth = false.
        for r in &resolved {
            if r.export_name != "__constructor" && r.export_name != "__check_auth" {
                assert!(!r.is_constructor && !r.is_check_auth);
            }
        }
    }

    #[test]
    fn resolve_exports_picks_up_constructor() {
        let wasm = include_bytes!("../../../../tests/fixtures/test_constructor.wasm");
        let (module, registry) = load(wasm);
        let resolved = resolve_exports(&module, &registry);
        let ctor = resolved
            .iter()
            .find(|r| r.export_name == "__constructor")
            .expect("__constructor should be resolved");
        assert!(ctor.is_constructor);
        assert!(!ctor.is_check_auth);
    }

    #[test]
    fn resolve_exports_picks_up_check_auth() {
        let wasm = include_bytes!("../../../../tests/fixtures/test_account.wasm");
        let (module, registry) = load(wasm);
        let resolved = resolve_exports(&module, &registry);
        let auth = resolved
            .iter()
            .find(|r| r.export_name == "__check_auth")
            .expect("__check_auth should be resolved");
        assert!(auth.is_check_auth);
        assert!(!auth.is_constructor);
    }

    #[test]
    fn resolve_exports_skips_non_spec_non_magic_exports() {
        let wasm = include_bytes!("../../../../tests/fixtures/test_add_u64.wasm");
        let (module, registry) = load(wasm);
        let resolved = resolve_exports(&module, &registry);
        // Every resolved name must be in spec OR be a magic name.
        for r in &resolved {
            let is_spec = registry.get_function(&r.export_name).is_some();
            let is_magic = r.export_name == "__constructor" || r.export_name == "__check_auth";
            assert!(
                is_spec || is_magic,
                "unexpected non-spec, non-magic export: {}",
                r.export_name
            );
        }
    }

    #[test]
    fn resolve_exports_generic_filters_underscore_prefix() {
        let wasm = include_bytes!("../../../../tests/fixtures/test_add_u64.wasm");
        let module = WasmModule::parse(wasm).expect("parse");
        let resolved = resolve_exports_generic(&module);
        for r in &resolved {
            assert!(
                !r.export_name.starts_with('_'),
                "generic mode must skip underscore-prefixed exports, got: {}",
                r.export_name
            );
            assert!(!r.is_constructor);
            assert!(!r.is_check_auth);
        }
    }
}
