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
