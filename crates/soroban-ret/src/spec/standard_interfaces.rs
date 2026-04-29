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
