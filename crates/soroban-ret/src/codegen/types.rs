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
