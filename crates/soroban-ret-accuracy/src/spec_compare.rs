//! Spec-consistency checking: does the generated Rust match the contract's own
//! `contractspecv0`?
//!
//! Unlike [`crate::ast_compare`] (which compares decompiled source against a
//! *reference source*, available only for the SDK fixtures), this compares
//! against the spec embedded in the WASM itself — so it works on **every**
//! contract, including the mainnet corpus that has no reference source.
//!
//! The expected interface is rendered from the spec via the SAME
//! [`generate_type_ident`] codegen uses, then normalized with the SAME
//! [`normalize_type_str`] the syn extractor uses, so type strings are
//! comparable.

use std::collections::{BTreeMap, BTreeSet};

use soroban_ret::codegen::types::generate_type_ident;
use soroban_ret::spec::TypeRegistry;
use stellar_xdr::curr::{ScSpecTypeDef, ScSpecUdtUnionCaseV0};

use crate::ast_compare::{
    ContractInterface, FunctionInfo, MemberInfo, ParamInfo, StructureInfo, TypeInfo, TypeKind,
    compare_interfaces, extract_interface, normalize_type_str,
};

/// Render a spec type into the canonical string form the extractor produces.
fn render_type(td: &ScSpecTypeDef) -> String {
    normalize_type_str(&generate_type_ident(td).to_string())
}

/// Build the *expected* [`ContractInterface`] directly from the spec registry.
pub fn spec_interface_from_registry(reg: &TypeRegistry) -> ContractInterface {
    let mut iface = ContractInterface::default();

    for (name, f) in &reg.functions {
        let params = f
            .inputs
            .iter()
            .map(|i| ParamInfo {
                name: i.name.to_string(),
                type_str: render_type(&i.type_),
            })
            .collect();
        let return_type = match f.outputs.iter().next() {
            None => None,
            Some(ScSpecTypeDef::Void) => None,
            Some(td) => Some(render_type(td)),
        };
        iface.functions.insert(
            name.clone(),
            FunctionInfo {
                params,
                return_type,
                body_source: String::new(),
                operations: BTreeSet::new(),
            },
        );
    }

    for (name, s) in &reg.structs {
        let members = s
            .fields
            .iter()
            .map(|fld| {
                (
                    fld.name.to_string(),
                    MemberInfo {
                        type_str: Some(render_type(&fld.type_)),
                        discriminant: None,
                    },
                )
            })
            .collect();
        iface.types.insert(
            name.clone(),
            TypeInfo {
                kind: TypeKind::Struct,
                members,
            },
        );
    }

    // Integer enums and error enums both render as discriminant-bearing enums.
    for (name, e) in &reg.enums {
        let members = e
            .cases
            .iter()
            .map(|c| {
                (
                    c.name.to_string(),
                    MemberInfo {
                        type_str: None,
                        discriminant: Some(i64::from(c.value)),
                    },
                )
            })
            .collect();
        iface.types.insert(
            name.clone(),
            TypeInfo {
                kind: TypeKind::Enum,
                members,
            },
        );
    }
    for (name, e) in &reg.error_enums {
        let members = e
            .cases
            .iter()
            .map(|c| {
                (
                    c.name.to_string(),
                    MemberInfo {
                        type_str: None,
                        discriminant: Some(i64::from(c.value)),
                    },
                )
            })
            .collect();
        iface.types.insert(
            name.clone(),
            TypeInfo {
                kind: TypeKind::Enum,
                members,
            },
        );
    }

    // Unions render as data-carrying enums.
    for (name, u) in &reg.unions {
        let mut members = BTreeMap::new();
        for c in u.cases.iter() {
            let (cname, type_str) = match c {
                ScSpecUdtUnionCaseV0::VoidV0(v) => (v.name.to_string(), None),
                ScSpecUdtUnionCaseV0::TupleV0(t) => {
                    let types: Vec<String> = t.type_.iter().map(render_type).collect();
                    let ts = if types.len() == 1 {
                        types[0].clone()
                    } else {
                        format!("({})", types.join(", "))
                    };
                    (t.name.to_string(), Some(normalize_type_str(&ts)))
                }
            };
            members.insert(
                cname,
                MemberInfo {
                    type_str,
                    discriminant: None,
                },
            );
        }
        iface.types.insert(
            name.clone(),
            TypeInfo {
                kind: TypeKind::Enum,
                members,
            },
        );
    }

    if !iface.functions.is_empty() {
        iface.annotations.insert("contract".to_string());
        iface.annotations.insert("contractimpl".to_string());
    }
    if !reg.structs.is_empty() || !reg.enums.is_empty() || !reg.unions.is_empty() {
        iface.annotations.insert("contracttype".to_string());
    }
    if !reg.error_enums.is_empty() {
        iface.annotations.insert("contracterror".to_string());
    }
    iface.structure = StructureInfo {
        has_no_std: true,
        has_use_soroban_sdk: true,
        has_contract_struct: !iface.functions.is_empty(),
        has_contractimpl: !iface.functions.is_empty(),
    };

    iface
}

/// Outcome of comparing generated source against the spec.
#[derive(Debug, Default)]
pub struct SpecConsistency {
    /// Number of exported functions in the spec (excluding `__`-prefixed).
    pub spec_fns: usize,
    /// Spec functions absent from, or with an arity mismatch in, the generated
    /// source. Each entry is a genuine spec violation.
    pub fn_violations: Vec<String>,
    /// Generated functions not present in the spec (excluding `__`-prefixed).
    pub extra_fns: Vec<String>,
    /// Graded signature similarity (params/return), 0..=100.
    pub signatures_score: f64,
    /// Graded type-definition similarity (UDTs/enums/errors), 0..=100.
    pub types_score: f64,
}

/// Compare the decompiled `generated_source` against `reg` (the spec).
///
/// `__constructor`/`__check_auth` are excluded from the function checks (the
/// decompiler renames them; their spec/source names need not align).
pub fn check_spec_consistency(
    reg: &TypeRegistry,
    generated_source: &str,
) -> Result<SpecConsistency, String> {
    let spec = spec_interface_from_registry(reg);
    let generated = extract_interface(generated_source)?;

    let mut fn_violations = Vec::new();
    let mut spec_fns = 0usize;
    for (name, f) in &spec.functions {
        if name.starts_with("__") {
            continue;
        }
        spec_fns += 1;
        match generated.functions.get(name) {
            None => fn_violations.push(format!("{name}: declared in spec, absent from output")),
            Some(gf) if gf.params.len() != f.params.len() => fn_violations.push(format!(
                "{name}: arity mismatch (spec {}, output {})",
                f.params.len(),
                gf.params.len()
            )),
            _ => {}
        }
    }

    let extra_fns = generated
        .functions
        .keys()
        .filter(|n| !n.starts_with("__") && !spec.functions.contains_key(*n))
        .cloned()
        .collect();

    let cmp = compare_interfaces(&spec, &generated);

    Ok(SpecConsistency {
        spec_fns,
        fn_violations,
        extra_fns,
        signatures_score: cmp.signatures_score,
        types_score: cmp.types_score,
    })
}
