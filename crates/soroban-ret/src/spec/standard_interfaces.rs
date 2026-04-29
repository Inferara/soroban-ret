use std::collections::HashSet;

use super::registry::TypeRegistry;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StandardInterface {
    Sep41Token,
    StellarAsset,
}

/// SEP-41 Token Interface required functions
const SEP41_FUNCTIONS: &[&str] = &[
    "allowance",
    "approve",
    "balance",
    "decimals",
    "name",
    "symbol",
    "transfer",
    "transfer_from",
    "burn",
    "burn_from",
];

/// Stellar Asset Interface additional functions (on top of SEP-41)
const STELLAR_ASSET_EXTRA: &[&str] = &[
    "set_admin",
    "admin",
    "set_authorized",
    "authorized",
    "mint",
    "clawback",
];

pub fn detect_standard_interfaces(registry: &TypeRegistry) -> Vec<StandardInterface> {
    let mut interfaces = Vec::new();
    let fn_names: HashSet<&str> = registry.functions.keys().map(|s| s.as_str()).collect();

    let has_sep41 = SEP41_FUNCTIONS.iter().all(|f| fn_names.contains(f));
    if has_sep41 {
        let has_stellar_asset = STELLAR_ASSET_EXTRA.iter().all(|f| fn_names.contains(f));
        if has_stellar_asset {
            interfaces.push(StandardInterface::StellarAsset);
        } else {
            interfaces.push(StandardInterface::Sep41Token);
        }
    }

    interfaces
}

#[cfg(test)]
mod tests {
    use super::*;
    use ::stellar_xdr::curr::{ScSpecFunctionInputV0, ScSpecFunctionV0, ScSpecTypeDef};
    use std::collections::BTreeMap;

    fn make_fn(name: &str) -> ScSpecFunctionV0 {
        ScSpecFunctionV0 {
            doc: "".try_into().unwrap(),
            name: name.try_into().unwrap(),
            inputs: Vec::<ScSpecFunctionInputV0>::new().try_into().unwrap(),
            outputs: Vec::<ScSpecTypeDef>::new().try_into().unwrap(),
        }
    }

    fn registry_with_functions(names: &[&str]) -> TypeRegistry {
        let mut functions = BTreeMap::new();
        for n in names {
            functions.insert((*n).to_string(), make_fn(n));
        }
        TypeRegistry {
            functions,
            structs: BTreeMap::new(),
            unions: BTreeMap::new(),
            enums: BTreeMap::new(),
            error_enums: BTreeMap::new(),
            events: BTreeMap::new(),
            meta: Vec::new(),
            spec_entries: Vec::new(),
        }
    }

    #[test]
    fn detects_sep41_only_when_all_required_functions_present() {
        let r = registry_with_functions(SEP41_FUNCTIONS);
        assert_eq!(
            detect_standard_interfaces(&r),
            vec![StandardInterface::Sep41Token]
        );
    }

    #[test]
    fn detects_stellar_asset_when_sep41_plus_extras_present() {
        let mut all: Vec<&str> = SEP41_FUNCTIONS.to_vec();
        all.extend_from_slice(STELLAR_ASSET_EXTRA);
        let r = registry_with_functions(&all);
        assert_eq!(
            detect_standard_interfaces(&r),
            vec![StandardInterface::StellarAsset]
        );
    }

    #[test]
    fn no_interface_detected_when_one_sep41_fn_missing() {
        // omit "balance"
        let partial: Vec<&str> = SEP41_FUNCTIONS
            .iter()
            .copied()
            .filter(|f| *f != "balance")
            .collect();
        let r = registry_with_functions(&partial);
        assert!(detect_standard_interfaces(&r).is_empty());
    }

    #[test]
    fn no_interface_detected_for_empty_registry() {
        let r = registry_with_functions(&[]);
        assert!(detect_standard_interfaces(&r).is_empty());
    }

    #[test]
    fn missing_one_stellar_extra_falls_back_to_sep41() {
        // SEP-41 complete but missing "mint" from the extras
        let mut funcs: Vec<&str> = SEP41_FUNCTIONS.to_vec();
        funcs.extend(STELLAR_ASSET_EXTRA.iter().copied().filter(|f| *f != "mint"));
        let r = registry_with_functions(&funcs);
        assert_eq!(
            detect_standard_interfaces(&r),
            vec![StandardInterface::Sep41Token]
        );
    }
}
