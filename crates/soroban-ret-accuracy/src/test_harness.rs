//! Unified test harness combining decompilation, AST comparison, and scoring.

use crate::ast_compare::{compare_interfaces, extract_interface};
use crate::metrics::{AccuracyReport, ComplexityLevel, ContractReport};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

// ---------------------------------------------------------------------------
// Contract discovery
// ---------------------------------------------------------------------------

/// Name overrides from WASM fixture name to SDK test directory name.
const NAME_OVERRIDES: &[(&str, &str)] = &[
    ("associated_types", "associated_type"),
    (
        "associated_types_contracttrait",
        "associated_type_contracttrait",
    ),
];

/// WASM files that don't correspond to SDK test directories.
const SKIP_WASMS: &[&str] = &["contract", "contract_with_constructor"];

/// A discovered contract with paths to its WASM fixture and original source.
#[derive(Debug, Clone)]
pub struct ContractEntry {
    pub name: String,
    pub wasm_path: PathBuf,
    pub sdk_src_dir: Option<PathBuf>,
    pub level: ComplexityLevel,
}

/// Discover all contracts from WASM fixtures and SDK sources.
pub fn discover_contracts(fixtures_dir: &Path, sdk_tests_dir: &Path) -> Vec<ContractEntry> {
    let mut contracts = Vec::new();

    let mut wasm_files: Vec<_> = std::fs::read_dir(fixtures_dir)
        .into_iter()
        .flatten()
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.path()
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("test_") && n.ends_with(".wasm"))
        })
        .map(|e| e.path())
        .collect();
    wasm_files.sort();

    for wasm_path in wasm_files {
        let stem = wasm_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("")
            .to_string();
        let contract_name = stem.strip_prefix("test_").unwrap_or(&stem).to_string();

        if SKIP_WASMS.contains(&contract_name.as_str()) {
            continue;
        }

        let sdk_dir_name = NAME_OVERRIDES
            .iter()
            .find(|(k, _)| *k == contract_name.as_str())
            .map(|(_, v)| *v)
            .unwrap_or(&contract_name);

        let sdk_src_dir = sdk_tests_dir.join(sdk_dir_name).join("src");
        let sdk_src = if sdk_src_dir.is_dir() {
            Some(sdk_src_dir)
        } else {
            None
        };

        let level = ComplexityLevel::for_contract(&contract_name);
        contracts.push(ContractEntry {
            name: contract_name,
            wasm_path,
            sdk_src_dir: sdk_src,
            level,
        });
    }

    contracts
}

// ---------------------------------------------------------------------------
// Source reading
// ---------------------------------------------------------------------------

/// Read and concatenate all non-test .rs files from an SDK source directory.
pub fn read_original_source(sdk_src_dir: &Path) -> String {
    let mut parts = Vec::new();

    // lib.rs first
    let lib_rs = sdk_src_dir.join("lib.rs");
    if lib_rs.exists()
        && let Ok(content) = std::fs::read_to_string(&lib_rs)
    {
        parts.push(content);
    }

    // Other .rs files alphabetically (skip lib.rs and test.rs)
    if let Ok(entries) = std::fs::read_dir(sdk_src_dir) {
        let mut other_files: Vec<PathBuf> = entries
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| {
                p.extension().is_some_and(|e| e == "rs")
                    && p.file_name()
                        .and_then(|n| n.to_str())
                        .is_some_and(|n| n != "lib.rs" && n != "test.rs")
            })
            .collect();
        other_files.sort();

        for f in other_files {
            if let Ok(content) = std::fs::read_to_string(&f) {
                parts.push(content);
            }
        }
    }

    parts.join("\n")
}

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

/// Run the full accuracy measurement on discovered contracts.
///
/// Decompiles each WASM, parses both original and decompiled source with `syn`,
/// and produces per-function accuracy scores.
pub fn run_accuracy(contracts: &[ContractEntry], filter: Option<&str>) -> AccuracyReport {
    let mut reports = BTreeMap::new();
    let mut skipped: Vec<String> = Vec::new();

    for entry in contracts {
        // Skip if filtering and not matching
        if let Some(f) = filter
            && entry.name != f
        {
            continue;
        }

        // Skip if no SDK source available — record it so the caller can tell a
        // genuine "no reference source" (e.g. liquidity_pool) from a missing
        // submodule that silently shrank the scored set.
        let sdk_src_dir = match &entry.sdk_src_dir {
            Some(d) => d,
            None => {
                skipped.push(entry.name.clone());
                continue;
            }
        };

        // Read original source
        let original_source = read_original_source(sdk_src_dir);

        // Decompile
        let wasm_data = match std::fs::read(&entry.wasm_path) {
            Ok(data) => data,
            Err(e) => {
                reports.insert(
                    entry.name.clone(),
                    ContractReport::error(&entry.name, format!("Read error: {e}")),
                );
                continue;
            }
        };

        let decompiled_source = match soroban_ret::decompile(&wasm_data) {
            Ok(source) => source,
            Err(e) => {
                reports.insert(
                    entry.name.clone(),
                    ContractReport::error(&entry.name, format!("Decompile error: {e}")),
                );
                continue;
            }
        };

        // Extract interfaces
        let orig_iface = match extract_interface(&original_source) {
            Ok(iface) => iface,
            Err(e) => {
                reports.insert(
                    entry.name.clone(),
                    ContractReport::error(&entry.name, format!("Original parse error: {e}")),
                );
                continue;
            }
        };

        let decomp_iface = match extract_interface(&decompiled_source) {
            Ok(iface) => iface,
            Err(e) => {
                reports.insert(
                    entry.name.clone(),
                    ContractReport::error(&entry.name, format!("Decompiled parse error: {e}")),
                );
                continue;
            }
        };

        // Compare
        let comparison = compare_interfaces(&orig_iface, &decomp_iface);
        reports.insert(
            entry.name.clone(),
            ContractReport::from_comparison(&entry.name, &comparison),
        );
    }

    let mut report = AccuracyReport::from_contracts(reports);
    report.skipped = skipped;
    report
}
