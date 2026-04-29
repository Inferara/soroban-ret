use stellar_xdr::ScSpecTypeDef;
use stellar_xdr::curr as stellar_xdr;

/// Returns true if this type requires the Env to be passed
pub fn type_needs_env(type_def: &ScSpecTypeDef) -> bool {
    matches!(
        type_def,
        ScSpecTypeDef::Vec(_)
            | ScSpecTypeDef::Map(_)
            | ScSpecTypeDef::Bytes
            | ScSpecTypeDef::BytesN(_)
            | ScSpecTypeDef::String
            | ScSpecTypeDef::Symbol
            | ScSpecTypeDef::Address
            | ScSpecTypeDef::MuxedAddress
    )
}

/// Returns true if this is a primitive type that maps directly to a Rust primitive
pub fn is_primitive(type_def: &ScSpecTypeDef) -> bool {
    matches!(
        type_def,
        ScSpecTypeDef::U32
            | ScSpecTypeDef::I32
            | ScSpecTypeDef::U64
            | ScSpecTypeDef::I64
            | ScSpecTypeDef::U128
            | ScSpecTypeDef::I128
            | ScSpecTypeDef::Bool
            | ScSpecTypeDef::Void
    )
}

/// Returns true if this is a user-defined type
pub fn is_udt(type_def: &ScSpecTypeDef) -> bool {
    matches!(type_def, ScSpecTypeDef::Udt(_))
}

/// Get the name of a UDT type, if it is one
pub fn udt_name(type_def: &ScSpecTypeDef) -> Option<String> {
    if let ScSpecTypeDef::Udt(u) = type_def {
        u.name.to_utf8_string().ok()
    } else {
        None
    }
}

/// Check if a function signature has an Env parameter (first param)
/// In Soroban, all contract functions receive Env, but it's implicit in the spec
pub fn function_takes_env(_func: &stellar_xdr::ScSpecFunctionV0) -> bool {
    // All Soroban contract functions take Env as first parameter
    // This is NOT listed in the spec - it's always implicitly present
    true
}

/// Get the storage type name from a discriminant value
/// In Soroban, storage types are encoded as:
/// 0 = Temporary, 1 = Persistent, 2 = Instance
pub fn storage_type_name(discriminant: u64) -> &'static str {
    match discriminant {
        0 => "temporary",
        1 => "persistent",
        2 => "instance",
        _ => "unknown",
    }
}
