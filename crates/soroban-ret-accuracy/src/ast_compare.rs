//! AST-level comparison of original and decompiled Rust source code.
//!
//! Uses `syn` to parse Rust source and extract a `ContractInterface` consisting
//! of types, functions, annotations, and structural elements.  Comparison
//! produces a `ComparisonResult` with per-component scores and detailed diffs.

use quote::ToTokens;
use std::collections::{BTreeMap, BTreeSet};
use syn::{Attribute, Expr, Fields, Item, Pat, Type};

// ---------------------------------------------------------------------------
// Extracted interface types
// ---------------------------------------------------------------------------

/// A contract interface extracted from Rust source code.
#[derive(Debug, Default)]
pub struct ContractInterface {
    /// Named types (structs, enums) keyed by type name.
    pub types: BTreeMap<String, TypeInfo>,
    /// Functions inside `#[contractimpl]` blocks, keyed by function name.
    pub functions: BTreeMap<String, FunctionInfo>,
    /// Which Soroban annotations are present (e.g. "contract", "contractimpl").
    pub annotations: BTreeSet<String>,
    /// Structural elements.
    pub structure: StructureInfo,
}

/// Extracted type definition.
#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub kind: TypeKind,
    /// Struct fields or enum variants, keyed by name.
    pub members: BTreeMap<String, MemberInfo>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
    Struct,
    TupleStruct,
    Enum,
}

/// A struct field or enum variant.
#[derive(Debug, Clone)]
pub struct MemberInfo {
    /// Type string (for struct fields or data-carrying enum variants).
    pub type_str: Option<String>,
    /// Discriminant value (for integer enums).
    pub discriminant: Option<i64>,
}

/// Extracted function signature and body info.
#[derive(Debug, Clone)]
pub struct FunctionInfo {
    /// Parameters (excluding `env: Env`).
    pub params: Vec<ParamInfo>,
    /// Return type as string (None for void).
    pub return_type: Option<String>,
    /// Raw function body source text.
    pub body_source: String,
    /// Detected operations in the body (for fingerprinting).
    pub operations: BTreeSet<String>,
}

#[derive(Debug, Clone)]
pub struct ParamInfo {
    pub name: String,
    pub type_str: String,
}

/// Structural elements of the source file.
#[derive(Debug, Default, Clone)]
pub struct StructureInfo {
    pub has_no_std: bool,
    pub has_use_soroban_sdk: bool,
    pub has_contract_struct: bool,
    pub has_contractimpl: bool,
}

// ---------------------------------------------------------------------------
// Comparison result
// ---------------------------------------------------------------------------

/// Result of comparing original vs decompiled contract interfaces.
#[derive(Debug)]
pub struct ComparisonResult {
    pub types_score: f64,
    pub signatures_score: f64,
    pub annotations_score: f64,
    pub bodies_score: f64,
    pub structure_score: f64,
    pub overall_score: f64,

    /// Artifact quality score (100.0 = no artifacts, decreases with artifacts).
    /// Tracked separately — not folded into overall_score.
    pub artifact_score: f64,

    /// Per-function comparison details.
    pub function_details: BTreeMap<String, FunctionComparison>,
    /// Types present in original but missing in decompiled.
    pub missing_types: Vec<String>,
    /// Types present in decompiled but not in original.
    pub extra_types: Vec<String>,
}

/// Per-function comparison detail.
#[derive(Debug)]
pub struct FunctionComparison {
    pub present: bool,
    pub signature_score: f64,
    pub body_score: f64,
    pub param_diffs: Vec<String>,
    pub return_type_match: bool,
    pub operations_found: Vec<String>,
    pub operations_missing: Vec<String>,
    /// Count of decompilation artifacts (todo!(), var_N, etc.) in the body.
    pub artifact_count: usize,
}

// ---------------------------------------------------------------------------
// Extraction
// ---------------------------------------------------------------------------

/// Extract a `ContractInterface` from Rust source code.
///
/// Strips `#[cfg(test)]` items, `#[test]` functions, and `mod test;` before
/// extraction so only the contract's public interface is captured.
pub fn extract_interface(source: &str) -> Result<ContractInterface, String> {
    // Pre-strip test blocks (simpler to do as text before parsing)
    let cleaned = strip_test_blocks(source);
    let file = syn::parse_str::<syn::File>(&cleaned).map_err(|e| format!("Parse error: {e}"))?;

    let mut iface = ContractInterface::default();

    // Check structural elements
    for attr in &file.attrs {
        if is_attr_named(attr, "no_std") {
            iface.structure.has_no_std = true;
        }
    }

    for item in &file.items {
        match item {
            Item::Use(use_item) => {
                let s = use_item.to_token_stream().to_string();
                if s.contains("soroban_sdk") {
                    iface.structure.has_use_soroban_sdk = true;
                }
            }
            Item::Struct(s) => {
                extract_struct(&mut iface, s);
            }
            Item::Enum(e) => {
                extract_enum(&mut iface, e);
            }
            Item::Impl(imp) => {
                extract_impl(&mut iface, imp);
            }
            _ => {}
        }
    }

    Ok(iface)
}

fn extract_struct(iface: &mut ContractInterface, s: &syn::ItemStruct) {
    let name = s.ident.to_string();

    // Check annotations
    let anns = extract_soroban_annotations(&s.attrs);
    for ann in &anns {
        iface.annotations.insert(ann.clone());
    }

    // Check if this is the #[contract] struct
    if has_attr(&s.attrs, "contract") {
        iface.structure.has_contract_struct = true;
        iface.annotations.insert("contract".to_string());
        return; // Don't add contract struct to types
    }

    // Skip non-Soroban structs (no #[contracttype], #[contracterror], #[contractevent])
    // These are plain Rust structs that don't appear in the WASM spec section
    if !anns
        .iter()
        .any(|a| a == "contracttype" || a == "contracterror" || a == "contractevent")
    {
        return;
    }

    match &s.fields {
        Fields::Named(named) => {
            let mut members = BTreeMap::new();
            for field in &named.named {
                if let Some(ident) = &field.ident {
                    members.insert(
                        ident.to_string(),
                        MemberInfo {
                            type_str: Some(normalize_type_str(&type_to_string(&field.ty))),
                            discriminant: None,
                        },
                    );
                }
            }
            iface.types.insert(
                name,
                TypeInfo {
                    kind: TypeKind::Struct,
                    members,
                },
            );
        }
        Fields::Unnamed(unnamed) => {
            let mut members = BTreeMap::new();
            for (i, field) in unnamed.unnamed.iter().enumerate() {
                members.insert(
                    i.to_string(),
                    MemberInfo {
                        type_str: Some(normalize_type_str(&type_to_string(&field.ty))),
                        discriminant: None,
                    },
                );
            }
            iface.types.insert(
                name,
                TypeInfo {
                    kind: TypeKind::TupleStruct,
                    members,
                },
            );
        }
        Fields::Unit => {
            iface.types.insert(
                name,
                TypeInfo {
                    kind: TypeKind::Struct,
                    members: BTreeMap::new(),
                },
            );
        }
    }
}

fn extract_enum(iface: &mut ContractInterface, e: &syn::ItemEnum) {
    let name = e.ident.to_string();

    for ann in extract_soroban_annotations(&e.attrs) {
        iface.annotations.insert(ann);
    }

    let mut members = BTreeMap::new();
    for variant in &e.variants {
        let var_name = variant.ident.to_string();

        let type_str = match &variant.fields {
            Fields::Unnamed(f) if f.unnamed.len() == 1 => Some(normalize_type_str(
                &type_to_string(&f.unnamed.first().unwrap().ty),
            )),
            Fields::Unnamed(f) => {
                let types: Vec<String> = f.unnamed.iter().map(|f| type_to_string(&f.ty)).collect();
                Some(normalize_type_str(&format!("({})", types.join(", "))))
            }
            _ => None,
        };

        let discriminant = variant.discriminant.as_ref().and_then(|(_, expr)| {
            if let Expr::Lit(lit) = expr {
                if let syn::Lit::Int(int_lit) = &lit.lit {
                    int_lit.base10_parse::<i64>().ok()
                } else {
                    None
                }
            } else {
                None
            }
        });

        members.insert(
            var_name,
            MemberInfo {
                type_str,
                discriminant,
            },
        );
    }

    iface.types.insert(
        name,
        TypeInfo {
            kind: TypeKind::Enum,
            members,
        },
    );
}

fn extract_impl(iface: &mut ContractInterface, imp: &syn::ItemImpl) {
    if has_attr(&imp.attrs, "contractimpl") {
        iface.annotations.insert("contractimpl".to_string());
        iface.structure.has_contractimpl = true;

        for item in &imp.items {
            if let syn::ImplItem::Fn(method) = item
                && (matches!(method.vis, syn::Visibility::Public(_)) || imp.trait_.is_some())
            {
                extract_function(iface, method);
            }
        }
    }
}

fn extract_function(iface: &mut ContractInterface, method: &syn::ImplItemFn) {
    let name = method.sig.ident.to_string();

    // Extract parameters (skip self and Env)
    let params: Vec<ParamInfo> = method
        .sig
        .inputs
        .iter()
        .filter_map(|arg| {
            if let syn::FnArg::Typed(pat_type) = arg {
                let param_name = match pat_type.pat.as_ref() {
                    Pat::Ident(ident) => ident.ident.to_string(),
                    _ => return None,
                };
                let type_str = normalize_type_str(&type_to_string(&pat_type.ty));

                // Skip Env parameters (references stripped by type_to_string)
                if type_str == "Env" {
                    return None;
                }

                Some(ParamInfo {
                    name: param_name,
                    type_str,
                })
            } else {
                None // skip &self
            }
        })
        .collect();

    // Extract return type
    let return_type = match &method.sig.output {
        syn::ReturnType::Default => None,
        syn::ReturnType::Type(_, ty) => {
            let s = normalize_type_str(&type_to_string(ty));
            if s == "()" { None } else { Some(s) }
        }
    };

    // Get body source text
    let body_source = method.block.to_token_stream().to_string();

    // Fingerprint operations in body
    let operations = fingerprint_operations(&body_source);

    iface.functions.insert(
        name,
        FunctionInfo {
            params,
            return_type,
            body_source,
            operations,
        },
    );
}

// ---------------------------------------------------------------------------
// Operation fingerprinting (replaces Python regex approach)
// ---------------------------------------------------------------------------

/// Detect operation patterns in function body source text.
fn fingerprint_operations(body: &str) -> BTreeSet<String> {
    let mut ops = BTreeSet::new();

    // Storage operations — normalize whitespace for matching
    let body_normalized: String = body.chars().filter(|c| !c.is_whitespace()).collect();
    let storage_patterns = [
        (".storage().persistent().set(", "persistent.set"),
        (".storage().persistent().get(", "persistent.get"),
        (".storage().persistent().remove(", "persistent.remove"),
        (".storage().persistent().has(", "persistent.has"),
        (".storage().temporary().set(", "temporary.set"),
        (".storage().temporary().get(", "temporary.get"),
        (".storage().instance().set(", "instance.set"),
        (".storage().instance().get(", "instance.get"),
        (".storage().instance().has(", "instance.has"),
    ];
    for (pattern, op) in &storage_patterns {
        let pat_normalized: String = pattern.chars().filter(|c| !c.is_whitespace()).collect();
        if body_normalized.contains(&pat_normalized) {
            ops.insert(op.to_string());
        }
    }

    // Auth
    if body.contains("require_auth") {
        if body.contains("require_auth_for_args") {
            ops.insert("require_auth_for_args".to_string());
        } else {
            ops.insert("require_auth".to_string());
        }
    }

    // Arithmetic operators
    if body.contains(" + ") {
        ops.insert("add".to_string());
    }
    if body.contains(" - ") {
        ops.insert("sub".to_string());
    }
    // Detect multiplication but not dereference: in syn-tokenized output,
    // multiplication looks like `expr * expr` (alphanumeric or `)` before ` * `),
    // while dereference looks like `+ * expr` (operator before ` * `).
    {
        let bytes = body.as_bytes();
        let mut i = 0;
        while i + 2 < bytes.len() {
            if bytes[i] == b' '
                && bytes[i + 1] == b'*'
                && bytes[i + 2] == b' '
                && i > 0
                && (bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b')')
            {
                ops.insert("mul".to_string());
                break;
            }
            i += 1;
        }
    }

    // Control flow
    if body.contains(" if ") || body.starts_with("if ") {
        ops.insert("if".to_string());
    }
    if body.contains("match ") {
        ops.insert("match".to_string());
    }
    if body.contains("loop {") || body.contains("loop{") {
        ops.insert("loop".to_string());
    }

    // Events
    if body.contains("publish") {
        ops.insert("publish".to_string());
    }

    // Cross-contract
    if body.contains("invoke_contract") {
        ops.insert("invoke_contract".to_string());
    }

    // Symbols
    if body.contains("symbol_short") {
        ops.insert("symbol_short".to_string());
    }

    // Error handling
    if body.contains("Ok (") || body.contains("Ok(") {
        ops.insert("Ok".to_string());
    }
    if body.contains("Err (") || body.contains("Err(") {
        ops.insert("Err".to_string());
    }
    if body.contains("panic") {
        ops.insert("panic".to_string());
    }

    ops
}

// ---------------------------------------------------------------------------
// Comparison
// ---------------------------------------------------------------------------

/// Combine the five per-component scores into the overall accuracy score.
///
/// Weights are policy: types 25 %, signatures 20 %, annotations 15 %,
/// bodies 30 %, structure 10 % (sum 100 %). Kept as a standalone function so
/// the weighting is unit-testable independently of the comparison machinery.
pub fn weighted_overall(
    types_score: f64,
    signatures_score: f64,
    annotations_score: f64,
    bodies_score: f64,
    structure_score: f64,
) -> f64 {
    0.25 * types_score
        + 0.20 * signatures_score
        + 0.15 * annotations_score
        + 0.30 * bodies_score
        + 0.10 * structure_score
}

/// Compare original and decompiled contract interfaces.
///
/// Weights: types 25%, signatures 20%, annotations 15%, bodies 30%, structure 10%.
pub fn compare_interfaces(
    original: &ContractInterface,
    decompiled: &ContractInterface,
) -> ComparisonResult {
    let types_score = score_types(&original.types, &decompiled.types);
    let signatures_score = score_signatures(&original.functions, &decompiled.functions);
    let annotations_score = score_annotations(&original.annotations, &decompiled.annotations);
    let (bodies_score, function_details) = score_bodies(&original.functions, &decompiled.functions);
    let structure_score = score_structure(&original.structure, &decompiled.structure);

    let overall_score = weighted_overall(
        types_score,
        signatures_score,
        annotations_score,
        bodies_score,
        structure_score,
    );

    let missing_types: Vec<String> = original
        .types
        .keys()
        .filter(|k| !decompiled.types.contains_key(*k))
        .cloned()
        .collect();
    let extra_types: Vec<String> = decompiled
        .types
        .keys()
        .filter(|k| !original.types.contains_key(*k))
        .cloned()
        .collect();

    // Compute artifact score: 100.0 when all functions have zero artifacts,
    // decreasing by 5 percentage points per artifact (capped at 0.0).
    // Tracked separately — not folded into overall_score.
    let total_artifacts: usize = function_details.values().map(|fc| fc.artifact_count).sum();
    let artifact_score = (100.0 - total_artifacts as f64 * 5.0).max(0.0);

    ComparisonResult {
        types_score,
        signatures_score,
        annotations_score,
        bodies_score,
        structure_score,
        overall_score,
        artifact_score,
        function_details,
        missing_types,
        extra_types,
    }
}

fn score_types(orig: &BTreeMap<String, TypeInfo>, decomp: &BTreeMap<String, TypeInfo>) -> f64 {
    if orig.is_empty() {
        return 100.0;
    }

    let mut total = 0.0_f64;
    let mut earned = 0.0_f64;

    for (name, orig_info) in orig {
        total += 1.0;
        let decomp_info = match decomp.get(name) {
            Some(info) => {
                earned += 1.0;
                info
            }
            None => continue,
        };

        match orig_info.kind {
            TypeKind::Enum => {
                for (var_name, var_info) in &orig_info.members {
                    total += 1.0;
                    if let Some(decomp_var) = decomp_info.members.get(var_name) {
                        earned += 1.0;
                        if let Some(disc) = var_info.discriminant {
                            total += 0.5;
                            if decomp_var.discriminant == Some(disc) {
                                earned += 0.5;
                            }
                        }
                        if var_info.type_str.is_some() {
                            total += 0.5;
                            if var_info.type_str == decomp_var.type_str {
                                earned += 0.5;
                            }
                        }
                    }
                }
            }
            TypeKind::Struct | TypeKind::TupleStruct => {
                for (field_name, field_info) in &orig_info.members {
                    total += 1.0;
                    if let Some(decomp_field) = decomp_info.members.get(field_name) {
                        earned += 1.0;
                        total += 1.0;
                        if field_info.type_str == decomp_field.type_str {
                            earned += 1.0;
                        }
                    }
                }
            }
        }
    }

    if total == 0.0 {
        100.0
    } else {
        (earned / total) * 100.0
    }
}

fn score_signatures(
    orig: &BTreeMap<String, FunctionInfo>,
    decomp: &BTreeMap<String, FunctionInfo>,
) -> f64 {
    if orig.is_empty() {
        return 100.0;
    }

    let mut total = 0.0_f64;
    let mut earned = 0.0_f64;

    for (name, orig_fn) in orig {
        total += 1.0;
        let decomp_fn = match decomp.get(name) {
            Some(f) => {
                earned += 1.0;
                f
            }
            None => continue,
        };

        total += 1.0;
        if orig_fn.params.len() == decomp_fn.params.len() {
            earned += 1.0;
        }

        for (i, op) in orig_fn.params.iter().enumerate() {
            total += 1.0;
            if let Some(dp) = decomp_fn.params.get(i) {
                if op.type_str == dp.type_str || is_associated_type(&op.type_str) {
                    earned += 1.0;
                }
                // Parameter name check (half weight — less critical than types).
                // Strip leading underscores: Rust convention `_foo` for unused params
                // doesn't match XDR spec names which never have underscores.
                total += 0.5;
                let orig_name = op.name.trim_start_matches('_');
                let decomp_name = dp.name.trim_start_matches('_');
                if orig_name == decomp_name {
                    earned += 0.5;
                }
            }
        }

        total += 1.0;
        if orig_fn.return_type == decomp_fn.return_type
            || orig_fn
                .return_type
                .as_ref()
                .is_some_and(|rt| is_associated_type(rt))
        {
            earned += 1.0;
        }
    }

    if total == 0.0 {
        100.0
    } else {
        (earned / total) * 100.0
    }
}

fn score_annotations(orig: &BTreeSet<String>, decomp: &BTreeSet<String>) -> f64 {
    if orig.is_empty() {
        return 100.0;
    }
    let total = orig.len() as f64;
    let matched = orig.intersection(decomp).count() as f64;
    (matched / total) * 100.0
}

fn score_bodies(
    orig: &BTreeMap<String, FunctionInfo>,
    decomp: &BTreeMap<String, FunctionInfo>,
) -> (f64, BTreeMap<String, FunctionComparison>) {
    let mut details = BTreeMap::new();

    if orig.is_empty() {
        return (100.0, details);
    }

    let mut total = 0.0_f64;
    let mut earned = 0.0_f64;

    for (name, orig_fn) in orig {
        let decomp_fn = decomp.get(name);

        if decomp_fn.is_none() {
            let ops_count = orig_fn.operations.len().max(1);
            total += ops_count as f64;
            details.insert(
                name.clone(),
                FunctionComparison {
                    present: false,
                    signature_score: 0.0,
                    body_score: 0.0,
                    param_diffs: vec!["function missing".to_string()],
                    return_type_match: false,
                    operations_found: vec![],
                    operations_missing: orig_fn.operations.iter().cloned().collect(),
                    artifact_count: 0,
                },
            );
            continue;
        }
        let decomp_fn = decomp_fn.unwrap();
        let artifacts = count_artifacts(&decomp_fn.body_source);

        // Check for pure-todo!() body (stub function with no real operations).
        // If the body has a mix of real ops and todo!(), score normally.
        // If the original also has no operations, a todo-stub is acceptable.
        let is_pure_todo = {
            let s = &decomp_fn.body_source;
            let has_todo = s.contains("todo !") || s.contains("todo!");
            has_todo && decomp_fn.operations.is_empty()
        };
        if is_pure_todo && !orig_fn.operations.is_empty() {
            let ops_count = orig_fn.operations.len();
            total += ops_count as f64;
            details.insert(
                name.clone(),
                FunctionComparison {
                    present: true,
                    signature_score: 0.0,
                    body_score: 0.0,
                    param_diffs: vec![],
                    return_type_match: orig_fn.return_type == decomp_fn.return_type,
                    operations_found: vec![],
                    operations_missing: orig_fn.operations.iter().cloned().collect(),
                    artifact_count: artifacts,
                },
            );
            continue;
        }

        let mut fn_found = Vec::new();
        let mut fn_missing = Vec::new();
        let mut fn_ops_checked = false;

        for op in &orig_fn.operations {
            fn_ops_checked = true;
            total += 1.0;
            if decomp_fn.operations.contains(op) {
                earned += 1.0;
                fn_found.push(op.clone());
            } else {
                fn_missing.push(op.clone());
            }
        }

        if !fn_ops_checked {
            // No specific operations in original — give credit if decompiled has
            // any body at all (even a todo stub is acceptable for empty functions).
            total += 1.0;
            if !decomp_fn.body_source.is_empty() {
                earned += 1.0;
            }
        }

        let body_score = if fn_ops_checked {
            let fn_total = (fn_found.len() + fn_missing.len()) as f64;
            if fn_total > 0.0 {
                (fn_found.len() as f64 / fn_total) * 100.0
            } else {
                100.0
            }
        } else {
            100.0
        };

        // Per-function signature score
        let mut sig_total = 0.0_f64;
        let mut sig_earned = 0.0_f64;
        let mut param_diffs = Vec::new();

        sig_total += 1.0;
        if orig_fn.params.len() == decomp_fn.params.len() {
            sig_earned += 1.0;
        } else {
            param_diffs.push(format!(
                "param count: {} vs {}",
                orig_fn.params.len(),
                decomp_fn.params.len()
            ));
        }

        for (i, op) in orig_fn.params.iter().enumerate() {
            sig_total += 1.0;
            if let Some(dp) = decomp_fn.params.get(i) {
                if op.type_str == dp.type_str || is_associated_type(&op.type_str) {
                    sig_earned += 1.0;
                } else {
                    param_diffs.push(format!(
                        "param {}: {} ({}) vs {} ({})",
                        i, op.name, op.type_str, dp.name, dp.type_str
                    ));
                }
            } else {
                param_diffs.push(format!("param {} missing", i));
            }
        }

        sig_total += 1.0;
        let return_match = orig_fn.return_type == decomp_fn.return_type
            || orig_fn
                .return_type
                .as_ref()
                .is_some_and(|rt| is_associated_type(rt));
        if return_match {
            sig_earned += 1.0;
        } else {
            param_diffs.push(format!(
                "return: {:?} vs {:?}",
                orig_fn.return_type, decomp_fn.return_type
            ));
        }

        let sig_score = if sig_total > 0.0 {
            (sig_earned / sig_total) * 100.0
        } else {
            100.0
        };

        details.insert(
            name.clone(),
            FunctionComparison {
                present: true,
                signature_score: sig_score,
                body_score,
                param_diffs,
                return_type_match: return_match,
                operations_found: fn_found,
                operations_missing: fn_missing,
                artifact_count: artifacts,
            },
        );
    }

    let score = if total == 0.0 {
        100.0
    } else {
        (earned / total) * 100.0
    };
    (score, details)
}

fn score_structure(orig: &StructureInfo, decomp: &StructureInfo) -> f64 {
    let checks: &[(bool, bool)] = &[
        (orig.has_no_std, decomp.has_no_std),
        (orig.has_use_soroban_sdk, decomp.has_use_soroban_sdk),
        (orig.has_contract_struct, decomp.has_contract_struct),
        (orig.has_contractimpl, decomp.has_contractimpl),
    ];

    let mut total = 0;
    let mut matched = 0;
    for (orig_val, decomp_val) in checks {
        if *orig_val {
            total += 1;
            if *decomp_val {
                matched += 1;
            }
        }
    }

    if total == 0 {
        100.0
    } else {
        (matched as f64 / total as f64) * 100.0
    }
}

// ---------------------------------------------------------------------------
// Artifact counting
// ---------------------------------------------------------------------------

/// Count decompilation artifacts in a function body source string.
///
/// Artifacts are residual decompiler placeholders that indicate incomplete
/// recovery: `todo!("unknown value")`, `todo!("host call: ...")`,
/// `todo!("decompiled function body")`, and `var_N` temporary names.
fn count_artifacts(body_source: &str) -> usize {
    let mut count = 0;

    // Count todo!("unknown value") occurrences
    count += body_source.matches("todo !(\"unknown value\")").count();
    count += body_source.matches("todo!(\"unknown value\")").count();

    // Count todo!("host call: ...") occurrences
    count += body_source.matches("todo !(\"host call").count();
    count += body_source.matches("todo!(\"host call").count();

    // Count todo!("decompiled function body") occurrences
    count += body_source
        .matches("todo !(\"decompiled function body\")")
        .count();
    count += body_source
        .matches("todo!(\"decompiled function body\")")
        .count();

    // Count var_N temporary variable names (word boundary: preceded by space/paren/comma)
    for word in body_source.split(|c: char| !c.is_alphanumeric() && c != '_') {
        if word.starts_with("var_")
            && word[4..].chars().all(|c| c.is_ascii_digit())
            && word.len() > 4
        {
            count += 1;
        }
    }

    count
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn type_to_string(ty: &Type) -> String {
    strip_references(ty).to_token_stream().to_string()
}

/// Recursively strip reference types and lifetime parameters from a syn Type.
/// WASM erases references, so `&'a Address` should compare equal to `Address`.
fn strip_references(ty: &Type) -> Type {
    match ty {
        Type::Reference(r) => strip_references(&r.elem),
        Type::Path(p) => {
            let mut p = p.clone();
            for seg in &mut p.path.segments {
                if let syn::PathArguments::AngleBracketed(ref mut args) = seg.arguments {
                    args.args = args
                        .args
                        .iter()
                        .filter_map(|arg| match arg {
                            syn::GenericArgument::Lifetime(_) => None,
                            syn::GenericArgument::Type(t) => {
                                Some(syn::GenericArgument::Type(strip_references(t)))
                            }
                            other => Some(other.clone()),
                        })
                        .collect();
                    if args.args.is_empty() {
                        seg.arguments = syn::PathArguments::None;
                    }
                }
            }
            Type::Path(p)
        }
        Type::Tuple(t) => {
            let mut t = t.clone();
            t.elems = t.elems.iter().map(strip_references).collect();
            Type::Tuple(t)
        }
        _ => ty.clone(),
    }
}

/// Canonicalize a rendered type string for comparison: strips `soroban_sdk::`,
/// collapses whitespace, removes spacing around `< > , ::`, and maps known
/// aliases. Public so the spec-consistency checker can render `ScSpecTypeDef`s
/// into the same canonical form the syn-extracted interface uses.
pub fn normalize_type_str(s: &str) -> String {
    let mut t = s.to_string();
    // Strip soroban_sdk:: prefix
    t = t.replace("soroban_sdk ::", "");
    t = t.replace("soroban_sdk::", "");
    // Collapse whitespace
    t = t.split_whitespace().collect::<Vec<_>>().join(" ");
    // Remove spaces around < > , ::
    t = t.replace(" < ", "<");
    t = t.replace(" > ", ">");
    t = t.replace("< ", "<");
    t = t.replace(" >", ">");
    t = t.replace(" , ", ", ");
    t = t.replace(" :: ", "::");
    // Normalize known Soroban type aliases (after whitespace normalization)
    // Hash<N> is pub type Hash<const N: usize> = BytesN<N>
    t = t.replace("Hash<", "BytesN<");
    t.trim().to_string()
}

/// Check if a type string is an unrecoverable associated type (Self::X).
/// WASM resolves associated types to their concrete types, so the decompiler
/// can never recover the original `Self::X` form.
fn is_associated_type(s: &str) -> bool {
    s.starts_with("Self::") || s.starts_with("Self ::") || s.contains("< Self")
}

fn has_attr(attrs: &[Attribute], name: &str) -> bool {
    attrs.iter().any(|a| is_attr_named(a, name))
}

fn is_attr_named(attr: &Attribute, name: &str) -> bool {
    let path = attr.path();
    // Check last segment for both `#[name]` and `#[soroban_sdk::name]`
    path.segments.last().is_some_and(|seg| seg.ident == name)
}

fn extract_soroban_annotations(attrs: &[Attribute]) -> Vec<String> {
    let soroban_attrs = [
        "contract",
        "contractimpl",
        "contracttype",
        "contracterror",
        "contractevent",
    ];
    let mut found = Vec::new();
    for attr in attrs {
        for ann in &soroban_attrs {
            if is_attr_named(attr, ann) {
                found.push(ann.to_string());
            }
        }
    }
    found
}

/// Strip `#[cfg(test)]` blocks and `#[test]` functions from source text.
fn strip_test_blocks(source: &str) -> String {
    let mut result = source.to_string();

    // Remove `mod test;` declarations
    result = result
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !trimmed.starts_with("mod test;") && !trimmed.starts_with("pub mod test;")
        })
        .collect::<Vec<_>>()
        .join("\n");

    // Remove #[cfg(test)] mod ... { ... } blocks
    result = strip_braced_blocks(&result, "#[cfg(test)]");

    // Remove #[test] fn blocks
    result = strip_braced_blocks(&result, "#[test]");

    result
}

/// Strip blocks following a marker attribute.
fn strip_braced_blocks(source: &str, marker: &str) -> String {
    let mut result = source.to_string();
    while let Some(marker_pos) = result.find(marker) {
        let after_marker = &result[marker_pos + marker.len()..];
        let Some(brace_offset) = after_marker.find('{') else {
            break;
        };
        let brace_pos = marker_pos + marker.len() + brace_offset;

        let mut depth = 1;
        let mut i = brace_pos + 1;
        let bytes = result.as_bytes();
        while i < bytes.len() && depth > 0 {
            match bytes[i] {
                b'{' => depth += 1,
                b'}' => depth -= 1,
                _ => {}
            }
            i += 1;
        }
        result = format!("{}{}", &result[..marker_pos], &result[i..]);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-9;

    /// Each component contributes exactly its documented weight when it is the
    /// only non-zero score: 25/20/15/30/10.
    #[test]
    fn weighted_overall_isolates_each_component() {
        assert!((weighted_overall(100.0, 0.0, 0.0, 0.0, 0.0) - 25.0).abs() < EPS);
        assert!((weighted_overall(0.0, 100.0, 0.0, 0.0, 0.0) - 20.0).abs() < EPS);
        assert!((weighted_overall(0.0, 0.0, 100.0, 0.0, 0.0) - 15.0).abs() < EPS);
        assert!((weighted_overall(0.0, 0.0, 0.0, 100.0, 0.0) - 30.0).abs() < EPS);
        assert!((weighted_overall(0.0, 0.0, 0.0, 0.0, 100.0) - 10.0).abs() < EPS);
    }

    /// All components perfect ⇒ overall 100; weights sum to 1.
    #[test]
    fn weighted_overall_is_one_hundred_when_perfect() {
        assert!((weighted_overall(100.0, 100.0, 100.0, 100.0, 100.0) - 100.0).abs() < EPS);
    }

    /// A self-comparison of a real contract scores a perfect 100 overall — the
    /// end-to-end alpha-equivalence sanity check.
    #[test]
    fn self_compare_is_perfect() {
        let source = r#"
            #![no_std]
            use soroban_sdk::{contract, contractimpl};

            #[contract]
            pub struct Contract;

            #[contractimpl]
            impl Contract {
                pub fn add(a: u64, b: u64) -> u64 {
                    a + b
                }
            }
        "#;
        let iface = extract_interface(source).expect("extract");
        let result = compare_interfaces(&iface, &iface);
        assert!(
            (result.overall_score - 100.0).abs() < EPS,
            "expected 100.0, got {}",
            result.overall_score
        );
    }
}
