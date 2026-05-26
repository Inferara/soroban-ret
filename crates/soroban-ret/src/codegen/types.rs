use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use stellar_xdr::curr as stellar_xdr;
use stellar_xdr::{
    ScSpecEventV0, ScSpecTypeDef, ScSpecUdtEnumV0, ScSpecUdtErrorEnumV0, ScSpecUdtStructV0,
    ScSpecUdtUnionV0,
};

use crate::ir::high_level_ir::CryptoUsage;

/// Generate a struct type definition, stripping `export = false` from soroban-spec-rust output
pub fn generate_struct(spec: &ScSpecUdtStructV0) -> TokenStream {
    let tokens = soroban_spec_rust::types::generate_struct(spec).unwrap_or_default();
    strip_export_false(tokens)
}

/// Generate a union (complex enum) type definition
pub fn generate_union(spec: &ScSpecUdtUnionV0) -> TokenStream {
    let tokens = soroban_spec_rust::types::generate_union(spec).unwrap_or_default();
    strip_export_false(tokens)
}

/// Generate an integer enum type definition
pub fn generate_enum(spec: &ScSpecUdtEnumV0) -> TokenStream {
    let tokens = soroban_spec_rust::types::generate_enum(spec).unwrap_or_default();
    strip_export_false(tokens)
}

/// Generate an error enum type definition
pub fn generate_error_enum(spec: &ScSpecUdtErrorEnumV0) -> TokenStream {
    let tokens = soroban_spec_rust::types::generate_error_enum(spec).unwrap_or_default();
    strip_export_false(tokens)
}

/// Generate an event type definition
pub fn generate_event(spec: &ScSpecEventV0) -> TokenStream {
    let tokens = soroban_spec_rust::types::generate_event(spec).unwrap_or_default();
    strip_export_false(tokens)
}

/// Generate a Rust type identifier from a spec type definition.
/// Emits unqualified names for SDK types that are imported via `use soroban_sdk::{...}`.
pub fn generate_type_ident(spec: &ScSpecTypeDef) -> TokenStream {
    match spec {
        ScSpecTypeDef::Val => quote! { soroban_sdk::Val },
        ScSpecTypeDef::Symbol => quote! { Symbol },
        ScSpecTypeDef::Error => quote! { soroban_sdk::Error },
        ScSpecTypeDef::Bytes => quote! { Bytes },
        ScSpecTypeDef::Address => quote! { Address },
        ScSpecTypeDef::MuxedAddress => quote! { MuxedAddress },
        ScSpecTypeDef::String => quote! { String },
        ScSpecTypeDef::Timepoint => quote! { Timepoint },
        ScSpecTypeDef::Duration => quote! { Duration },
        ScSpecTypeDef::U256 => quote! { U256 },
        ScSpecTypeDef::I256 => quote! { I256 },
        ScSpecTypeDef::BytesN(b) => {
            let n = proc_macro2::Literal::u32_unsuffixed(b.n);
            quote! { BytesN<#n> }
        }
        ScSpecTypeDef::Vec(v) => {
            let el = generate_type_ident(&v.element_type);
            quote! { Vec<#el> }
        }
        ScSpecTypeDef::Map(m) => {
            let k = generate_type_ident(&m.key_type);
            let v = generate_type_ident(&m.value_type);
            quote! { Map<#k, #v> }
        }
        ScSpecTypeDef::Option(o) => {
            let inner = generate_type_ident(&o.value_type);
            quote! { Option<#inner> }
        }
        ScSpecTypeDef::Result(r) => {
            let ok = generate_type_ident(&r.ok_type);
            let err = generate_type_ident(&r.error_type);
            quote! { Result<#ok, #err> }
        }
        ScSpecTypeDef::Tuple(t) => {
            let elems: Vec<_> = t.value_types.iter().map(generate_type_ident).collect();
            if elems.len() == 1 {
                let elem = &elems[0];
                quote! { (#elem,) }
            } else {
                quote! { (#(#elems),*) }
            }
        }
        // Primitives, Void, Udt — delegate to upstream
        other => soroban_spec_rust::types::generate_type_ident(other).unwrap_or_default(),
    }
}

/// Strip `export = false` and the `soroban_sdk::` path from generated attribute macros.
/// soroban-spec-rust generates `#[soroban_sdk::contracttype(export = false)]`
/// but decompiled contracts import these macros via `use soroban_sdk::{contracttype, ...}`
/// so they should appear as `#[contracttype]`, `#[contracterror]`, `#[contractevent]`.
fn strip_export_false(tokens: TokenStream) -> TokenStream {
    let source = tokens.to_string();

    // Strip export=false and soroban_sdk:: prefix in one pass (longer patterns first).
    // Handle both spacing variants that proc_macro2 may produce (with/without space before paren).
    let source = source
        .replace(
            "soroban_sdk :: contracttype (export = false)",
            "contracttype",
        )
        .replace(
            "soroban_sdk :: contracttype(export = false)",
            "contracttype",
        )
        .replace(
            "soroban_sdk :: contracterror (export = false)",
            "contracterror",
        )
        .replace(
            "soroban_sdk :: contracterror(export = false)",
            "contracterror",
        )
        // Strip remaining soroban_sdk:: prefix (cases without export=false)
        .replace("soroban_sdk :: contracttype", "contracttype")
        .replace("soroban_sdk :: contracterror", "contracterror")
        .replace("soroban_sdk :: contractevent", "contractevent")
        // Strip soroban_sdk:: from field types — these are imported via use soroban_sdk::{...}
        .replace("soroban_sdk :: ", "");

    // For events, also strip `export = false` from topic-bearing attributes
    let source = source
        .replace(", export = false)", ")")
        .replace(", export = false )", ")");

    source.parse().unwrap_or(tokens)
}

// ---------------------------------------------------------------------------
// Crypto type alias support
// ---------------------------------------------------------------------------

/// Resolve a spec type to a crypto type alias, if applicable.
fn resolve_crypto_alias(
    spec: &ScSpecTypeDef,
    crypto: &CryptoUsage,
    hint: Option<&str>,
) -> Option<TokenStream> {
    match spec {
        ScSpecTypeDef::BytesN(b) if crypto.uses_bn254 => match b.n {
            64 => Some(quote! { Bn254G1Affine }),
            128 => Some(quote! { Bn254G2Affine }),
            _ => None,
        },
        ScSpecTypeDef::BytesN(b) if crypto.uses_bls12_381 => match b.n {
            48 => Some(quote! { Bls12381Fp }),
            96 => {
                if hint.is_some_and(|h| h.to_lowercase().contains("fp2")) {
                    Some(quote! { Bls12381Fp2 })
                } else {
                    Some(quote! { Bls12381G1Affine })
                }
            }
            192 => Some(quote! { Bls12381G2Affine }),
            _ => None,
        },
        ScSpecTypeDef::U256 if crypto.uses_bn254 || crypto.uses_bls12_381 => Some(quote! { Fr }),
        _ => None,
    }
}

/// Like `generate_type_ident` but applies crypto type alias mapping.
/// Recurses into compound types (Vec, Map, Option, Result, Tuple).
pub fn generate_type_ident_crypto(
    spec: &ScSpecTypeDef,
    crypto: &CryptoUsage,
    hint: Option<&str>,
) -> TokenStream {
    // Check for direct crypto alias first
    if let Some(alias) = resolve_crypto_alias(spec, crypto, hint) {
        return alias;
    }
    // For compound types, recurse with crypto context (no hint for inner types)
    match spec {
        ScSpecTypeDef::Vec(v) => {
            let el = generate_type_ident_crypto(&v.element_type, crypto, None);
            quote! { Vec<#el> }
        }
        ScSpecTypeDef::Map(m) => {
            let k = generate_type_ident_crypto(&m.key_type, crypto, None);
            let v = generate_type_ident_crypto(&m.value_type, crypto, None);
            quote! { Map<#k, #v> }
        }
        ScSpecTypeDef::Option(o) => {
            let inner = generate_type_ident_crypto(&o.value_type, crypto, None);
            quote! { Option<#inner> }
        }
        ScSpecTypeDef::Result(r) => {
            let ok = generate_type_ident_crypto(&r.ok_type, crypto, None);
            let err = generate_type_ident_crypto(&r.error_type, crypto, None);
            quote! { Result<#ok, #err> }
        }
        ScSpecTypeDef::Tuple(t) => {
            let elems: Vec<_> = t
                .value_types
                .iter()
                .map(|ty| generate_type_ident_crypto(ty, crypto, None))
                .collect();
            if elems.len() == 1 {
                let elem = &elems[0];
                quote! { (#elem,) }
            } else {
                quote! { (#(#elems),*) }
            }
        }
        // Non-compound, non-crypto: delegate to base
        other => generate_type_ident(other),
    }
}

/// Generate a struct type definition with crypto type aliases applied to fields.
pub fn generate_struct_with_crypto(spec: &ScSpecUdtStructV0, crypto: &CryptoUsage) -> TokenStream {
    let name = format_ident!("{}", spec.name.to_utf8_string().unwrap_or_default());
    // Check if any field maps to a crypto type (which doesn't implement Ord)
    let has_unorderable_field = spec.fields.iter().any(|f| {
        let field_name_str = f.name.to_utf8_string().unwrap_or_default();
        resolve_crypto_alias(&f.type_, crypto, Some(&field_name_str)).is_some()
    });
    let fields: Vec<_> = spec
        .fields
        .iter()
        .map(|f| {
            let fname = format_ident!("{}", f.name.to_utf8_string().unwrap_or_default());
            let field_name_str = f.name.to_utf8_string().unwrap_or_default();
            let ftype = generate_type_ident_crypto(&f.type_, crypto, Some(&field_name_str));
            quote! { pub #fname: #ftype }
        })
        .collect();
    // Crypto types (Bls12381Fp, Fr, etc.) don't implement Ord/PartialOrd
    let derives = if has_unorderable_field {
        quote! { #[derive(Debug, Clone, Eq, PartialEq)] }
    } else {
        quote! { #[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)] }
    };
    quote! {
        #[contracttype]
        #derives
        pub struct #name {
            #(#fields),*
        }
    }
}

#[cfg(test)]
mod tests {
    use super::stellar_xdr::{
        ScSpecTypeBytesN, ScSpecTypeMap, ScSpecTypeOption, ScSpecTypeResult, ScSpecTypeTuple,
        ScSpecTypeUdt, ScSpecTypeVec,
    };
    use super::*;

    fn render(spec: &ScSpecTypeDef) -> String {
        generate_type_ident(spec).to_string().replace(' ', "")
    }

    #[test]
    fn generate_type_ident_scalars() {
        assert_eq!(render(&ScSpecTypeDef::Val), "soroban_sdk::Val");
        assert_eq!(render(&ScSpecTypeDef::Symbol), "Symbol");
        assert_eq!(render(&ScSpecTypeDef::Error), "soroban_sdk::Error");
        assert_eq!(render(&ScSpecTypeDef::Bytes), "Bytes");
        assert_eq!(render(&ScSpecTypeDef::Address), "Address");
        assert_eq!(render(&ScSpecTypeDef::MuxedAddress), "MuxedAddress");
        assert_eq!(render(&ScSpecTypeDef::String), "String");
        assert_eq!(render(&ScSpecTypeDef::Timepoint), "Timepoint");
        assert_eq!(render(&ScSpecTypeDef::Duration), "Duration");
        assert_eq!(render(&ScSpecTypeDef::U256), "U256");
        assert_eq!(render(&ScSpecTypeDef::I256), "I256");
    }

    #[test]
    fn generate_type_ident_bytesn() {
        let t = ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 32 });
        assert_eq!(render(&t), "BytesN<32>");
        let t = ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 64 });
        assert_eq!(render(&t), "BytesN<64>");
    }

    #[test]
    fn generate_type_ident_vec_of_u256() {
        let t = ScSpecTypeDef::Vec(Box::new(ScSpecTypeVec {
            element_type: Box::new(ScSpecTypeDef::U256),
        }));
        assert_eq!(render(&t), "Vec<U256>");
    }

    #[test]
    fn generate_type_ident_map_address_bytes() {
        let t = ScSpecTypeDef::Map(Box::new(ScSpecTypeMap {
            key_type: Box::new(ScSpecTypeDef::Address),
            value_type: Box::new(ScSpecTypeDef::Bytes),
        }));
        assert_eq!(render(&t), "Map<Address,Bytes>");
    }

    #[test]
    fn generate_type_ident_option_string() {
        let t = ScSpecTypeDef::Option(Box::new(ScSpecTypeOption {
            value_type: Box::new(ScSpecTypeDef::String),
        }));
        assert_eq!(render(&t), "Option<String>");
    }

    #[test]
    fn generate_type_ident_result_u256_error() {
        let t = ScSpecTypeDef::Result(Box::new(ScSpecTypeResult {
            ok_type: Box::new(ScSpecTypeDef::U256),
            error_type: Box::new(ScSpecTypeDef::Error),
        }));
        assert_eq!(render(&t), "Result<U256,soroban_sdk::Error>");
    }

    #[test]
    fn generate_type_ident_tuple_single_uses_trailing_comma() {
        let t = ScSpecTypeDef::Tuple(Box::new(ScSpecTypeTuple {
            value_types: vec![ScSpecTypeDef::Address].try_into().unwrap(),
        }));
        // single-element tuple form `(T,)`
        assert_eq!(render(&t), "(Address,)");
    }

    #[test]
    fn generate_type_ident_tuple_multi() {
        let t = ScSpecTypeDef::Tuple(Box::new(ScSpecTypeTuple {
            value_types: vec![
                ScSpecTypeDef::Address,
                ScSpecTypeDef::Bytes,
                ScSpecTypeDef::U256,
            ]
            .try_into()
            .unwrap(),
        }));
        assert_eq!(render(&t), "(Address,Bytes,U256)");
    }

    #[test]
    fn generate_type_ident_nested_vec_of_map() {
        // Vec<Map<Address, Option<U256>>>
        let inner_opt = ScSpecTypeDef::Option(Box::new(ScSpecTypeOption {
            value_type: Box::new(ScSpecTypeDef::U256),
        }));
        let inner_map = ScSpecTypeDef::Map(Box::new(ScSpecTypeMap {
            key_type: Box::new(ScSpecTypeDef::Address),
            value_type: Box::new(inner_opt),
        }));
        let outer = ScSpecTypeDef::Vec(Box::new(ScSpecTypeVec {
            element_type: Box::new(inner_map),
        }));
        assert_eq!(render(&outer), "Vec<Map<Address,Option<U256>>>");
    }

    #[test]
    fn generate_type_ident_delegates_for_udt() {
        // Udt name should appear in the output (delegates to upstream).
        let t = ScSpecTypeDef::Udt(ScSpecTypeUdt {
            name: "MyType".try_into().unwrap(),
        });
        let out = render(&t);
        assert!(out.contains("MyType"), "expected MyType in {out}");
    }

    #[test]
    fn strip_export_false_removes_contracttype_attr_with_space() {
        let input: TokenStream =
            "# [soroban_sdk :: contracttype (export = false)] pub struct Foo {}"
                .parse()
                .unwrap();
        let out = strip_export_false(input).to_string();
        assert!(
            out.contains("# [contracttype]"),
            "expected `# [contracttype]` in {out}"
        );
        assert!(!out.contains("export = false"), "stale attr in {out}");
        assert!(!out.contains("soroban_sdk ::"), "stale prefix in {out}");
    }

    #[test]
    fn strip_export_false_removes_contracterror_attr() {
        let input: TokenStream =
            "# [soroban_sdk :: contracterror (export = false)] pub enum E { A = 1 }"
                .parse()
                .unwrap();
        let out = strip_export_false(input).to_string();
        assert!(out.contains("# [contracterror]"));
        assert!(!out.contains("export = false"));
    }

    #[test]
    fn strip_export_false_strips_contractevent_export_false_inside_attr() {
        // contractevent uses `topics = [...], export = false`; the trailing
        // `, export = false` strip handles this.
        let input: TokenStream =
            "# [soroban_sdk :: contractevent (topics = [foo], export = false)] pub struct E {}"
                .parse()
                .unwrap();
        let out = strip_export_false(input).to_string();
        assert!(out.contains("contractevent"));
        assert!(!out.contains("export = false"));
        assert!(out.contains("topics = [foo]"));
    }

    #[test]
    fn strip_export_false_strips_path_from_field_types() {
        let input: TokenStream = "pub field : soroban_sdk :: Address".parse().unwrap();
        let out = strip_export_false(input).to_string();
        assert!(out.contains("Address"));
        assert!(!out.contains("soroban_sdk"), "stale path in {out}");
    }

    #[test]
    fn resolve_crypto_alias_bn254_bytesn_sizes() {
        let bn = CryptoUsage {
            uses_bn254: true,
            uses_bls12_381: false,
        };
        let t = ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 64 });
        let out = resolve_crypto_alias(&t, &bn, None).expect("should alias");
        assert_eq!(out.to_string().replace(' ', ""), "Bn254G1Affine");

        let t = ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 128 });
        let out = resolve_crypto_alias(&t, &bn, None).expect("should alias");
        assert_eq!(out.to_string().replace(' ', ""), "Bn254G2Affine");

        // Non-matching size returns None.
        let t = ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 32 });
        assert!(resolve_crypto_alias(&t, &bn, None).is_none());
    }

    #[test]
    fn resolve_crypto_alias_bls_fp2_hint() {
        let bls = CryptoUsage {
            uses_bn254: false,
            uses_bls12_381: true,
        };
        // 96-byte BytesN without hint → G1Affine
        let t = ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 96 });
        let out = resolve_crypto_alias(&t, &bls, None).expect("alias");
        assert_eq!(out.to_string().replace(' ', ""), "Bls12381G1Affine");
        // Same size with "fp2" hint → Fp2
        let out = resolve_crypto_alias(&t, &bls, Some("some_fp2_param")).expect("alias");
        assert_eq!(out.to_string().replace(' ', ""), "Bls12381Fp2");
        // 48 → Fp; 192 → G2Affine
        let t48 = ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 48 });
        assert_eq!(
            resolve_crypto_alias(&t48, &bls, None)
                .unwrap()
                .to_string()
                .replace(' ', ""),
            "Bls12381Fp"
        );
        let t192 = ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 192 });
        assert_eq!(
            resolve_crypto_alias(&t192, &bls, None)
                .unwrap()
                .to_string()
                .replace(' ', ""),
            "Bls12381G2Affine"
        );
    }

    #[test]
    fn resolve_crypto_alias_u256_to_fr() {
        let bls = CryptoUsage {
            uses_bn254: false,
            uses_bls12_381: true,
        };
        let out = resolve_crypto_alias(&ScSpecTypeDef::U256, &bls, None).expect("alias");
        assert_eq!(out.to_string().replace(' ', ""), "Fr");
        let none = CryptoUsage::default();
        assert!(resolve_crypto_alias(&ScSpecTypeDef::U256, &none, None).is_none());
    }

    #[test]
    fn generate_type_ident_crypto_recurses_into_vec() {
        let bn = CryptoUsage {
            uses_bn254: true,
            uses_bls12_381: false,
        };
        let inner = ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 64 });
        let outer = ScSpecTypeDef::Vec(Box::new(ScSpecTypeVec {
            element_type: Box::new(inner),
        }));
        let out = generate_type_ident_crypto(&outer, &bn, None)
            .to_string()
            .replace(' ', "");
        assert_eq!(out, "Vec<Bn254G1Affine>");
    }

    #[test]
    fn generate_type_ident_crypto_falls_back_for_non_crypto() {
        let none = CryptoUsage::default();
        let out = generate_type_ident_crypto(&ScSpecTypeDef::Address, &none, None)
            .to_string()
            .replace(' ', "");
        assert_eq!(out, "Address");
    }
}
