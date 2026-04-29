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

#[cfg(test)]
mod tests {
    use super::{
        ScSpecTypeDef, function_takes_env, is_primitive, is_udt, storage_type_name, type_needs_env,
        udt_name,
    };
    use ::stellar_xdr::curr::{
        ScSpecFunctionInputV0, ScSpecFunctionV0, ScSpecTypeBytesN, ScSpecTypeMap, ScSpecTypeUdt,
        ScSpecTypeVec,
    };

    fn udt(name: &str) -> ScSpecTypeDef {
        ScSpecTypeDef::Udt(ScSpecTypeUdt {
            name: name.try_into().unwrap(),
        })
    }

    #[test]
    fn type_needs_env_compound_types() {
        let elem = ScSpecTypeDef::U32;
        assert!(type_needs_env(&ScSpecTypeDef::Vec(Box::new(
            ScSpecTypeVec {
                element_type: Box::new(elem.clone()),
            }
        ))));
        assert!(type_needs_env(&ScSpecTypeDef::Map(Box::new(
            ScSpecTypeMap {
                key_type: Box::new(elem.clone()),
                value_type: Box::new(elem.clone()),
            }
        ))));
        assert!(type_needs_env(&ScSpecTypeDef::Bytes));
        assert!(type_needs_env(&ScSpecTypeDef::BytesN(ScSpecTypeBytesN {
            n: 32
        })));
        assert!(type_needs_env(&ScSpecTypeDef::String));
        assert!(type_needs_env(&ScSpecTypeDef::Symbol));
        assert!(type_needs_env(&ScSpecTypeDef::Address));
        assert!(type_needs_env(&ScSpecTypeDef::MuxedAddress));
    }

    #[test]
    fn type_needs_env_primitives_do_not() {
        for t in [
            ScSpecTypeDef::U32,
            ScSpecTypeDef::I32,
            ScSpecTypeDef::U64,
            ScSpecTypeDef::I64,
            ScSpecTypeDef::U128,
            ScSpecTypeDef::I128,
            ScSpecTypeDef::Bool,
            ScSpecTypeDef::Void,
        ] {
            assert!(!type_needs_env(&t), "primitive should not need env: {t:?}");
        }
    }

    #[test]
    fn primitives_classified_correctly() {
        for t in [
            ScSpecTypeDef::U32,
            ScSpecTypeDef::I32,
            ScSpecTypeDef::U64,
            ScSpecTypeDef::I64,
            ScSpecTypeDef::U128,
            ScSpecTypeDef::I128,
            ScSpecTypeDef::Bool,
            ScSpecTypeDef::Void,
        ] {
            assert!(is_primitive(&t), "should be primitive: {t:?}");
        }
        assert!(!is_primitive(&ScSpecTypeDef::Bytes));
        assert!(!is_primitive(&ScSpecTypeDef::Address));
        assert!(!is_primitive(&udt("Foo")));
    }

    #[test]
    fn udt_detection_and_name() {
        let foo = udt("Foo");
        assert!(is_udt(&foo));
        assert_eq!(udt_name(&foo).as_deref(), Some("Foo"));

        assert!(!is_udt(&ScSpecTypeDef::U32));
        assert_eq!(udt_name(&ScSpecTypeDef::U32), None);
        assert_eq!(udt_name(&ScSpecTypeDef::Bytes), None);
    }

    #[test]
    fn function_takes_env_is_always_true() {
        let f = ScSpecFunctionV0 {
            doc: "".try_into().unwrap(),
            name: "any".try_into().unwrap(),
            inputs: Vec::<ScSpecFunctionInputV0>::new().try_into().unwrap(),
            outputs: Vec::<ScSpecTypeDef>::new().try_into().unwrap(),
        };
        assert!(function_takes_env(&f));
    }

    #[test]
    fn storage_type_name_maps_all_known_discriminants() {
        assert_eq!(storage_type_name(0), "temporary");
        assert_eq!(storage_type_name(1), "persistent");
        assert_eq!(storage_type_name(2), "instance");
        assert_eq!(storage_type_name(3), "unknown");
        assert_eq!(storage_type_name(99), "unknown");
    }
}
