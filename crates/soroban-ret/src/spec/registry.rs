use std::collections::BTreeMap;

/// Convert CamelCase to lowercase (e.g., "Transfer" → "transfer").
fn camel_to_lower(s: &str) -> String {
    s.to_lowercase()
}
use stellar_xdr::curr as stellar_xdr;
use stellar_xdr::{
    ScMetaEntry, ScMetaV0, ScSpecEntry, ScSpecEventParamLocationV0, ScSpecEventV0,
    ScSpecFunctionV0, ScSpecTypeDef, ScSpecUdtEnumV0, ScSpecUdtErrorEnumV0, ScSpecUdtStructV0,
    ScSpecUdtUnionV0,
};

#[derive(thiserror::Error, Debug)]
pub enum RegistryError {
    #[error("failed to extract spec: {0}")]
    SpecExtraction(#[from] soroban_spec::read::FromWasmError),
    #[error("failed to extract meta: {0}")]
    MetaExtraction(#[from] soroban_meta::read::FromWasmError),
}

#[derive(Debug)]
pub struct TypeRegistry {
    pub functions: BTreeMap<String, ScSpecFunctionV0>,
    pub structs: BTreeMap<String, ScSpecUdtStructV0>,
    pub unions: BTreeMap<String, ScSpecUdtUnionV0>,
    pub enums: BTreeMap<String, ScSpecUdtEnumV0>,
    pub error_enums: BTreeMap<String, ScSpecUdtErrorEnumV0>,
    pub events: BTreeMap<String, ScSpecEventV0>,
    pub meta: Vec<ScMetaEntry>,
    pub spec_entries: Vec<ScSpecEntry>,
}

impl TypeRegistry {
    pub fn from_wasm(wasm: &[u8]) -> Result<Self, RegistryError> {
        let spec_entries = soroban_spec::read::from_wasm(wasm).unwrap_or_default();
        let meta = soroban_meta::read::from_wasm(wasm).unwrap_or_default();

        let mut functions = BTreeMap::new();
        let mut structs = BTreeMap::new();
        let mut unions = BTreeMap::new();
        let mut enums = BTreeMap::new();
        let mut error_enums = BTreeMap::new();
        let mut events = BTreeMap::new();

        for entry in &spec_entries {
            match entry {
                ScSpecEntry::FunctionV0(f) => {
                    if let Ok(name) = f.name.to_utf8_string() {
                        functions.insert(name, f.clone());
                    }
                }
                ScSpecEntry::UdtStructV0(s) => {
                    if let Ok(name) = s.name.to_utf8_string() {
                        structs.insert(name, s.clone());
                    }
                }
                ScSpecEntry::UdtUnionV0(u) => {
                    if let Ok(name) = u.name.to_utf8_string() {
                        unions.insert(name, u.clone());
                    }
                }
                ScSpecEntry::UdtEnumV0(e) => {
                    if let Ok(name) = e.name.to_utf8_string() {
                        enums.insert(name, e.clone());
                    }
                }
                ScSpecEntry::UdtErrorEnumV0(e) => {
                    if let Ok(name) = e.name.to_utf8_string() {
                        error_enums.insert(name, e.clone());
                    }
                }
                ScSpecEntry::EventV0(e) => {
                    if let Ok(name) = e.name.to_utf8_string() {
                        events.insert(name, e.clone());
                    }
                }
            }
        }

        Ok(Self {
            functions,
            structs,
            unions,
            enums,
            error_enums,
            events,
            meta,
            spec_entries,
        })
    }

    pub fn get_function(&self, name: &str) -> Option<&ScSpecFunctionV0> {
        self.functions.get(name)
    }

    pub fn get_struct(&self, name: &str) -> Option<&ScSpecUdtStructV0> {
        self.structs.get(name)
    }

    pub fn get_union(&self, name: &str) -> Option<&ScSpecUdtUnionV0> {
        self.unions.get(name)
    }

    pub fn get_enum(&self, name: &str) -> Option<&ScSpecUdtEnumV0> {
        self.enums.get(name)
    }

    pub fn get_error_enum(&self, name: &str) -> Option<&ScSpecUdtErrorEnumV0> {
        self.error_enums.get(name)
    }

    pub fn get_event(&self, name: &str) -> Option<&ScSpecEventV0> {
        self.events.get(name)
    }

    pub fn function_names(&self) -> Vec<&str> {
        self.functions.keys().map(|s| s.as_str()).collect()
    }

    pub fn has_constructor(&self) -> bool {
        self.functions.contains_key("__constructor")
    }

    pub fn sdk_version(&self) -> Option<String> {
        for entry in &self.meta {
            let ScMetaEntry::ScMetaV0(ScMetaV0 { key, val }) = entry;
            if key.to_utf8_string().ok().as_deref() == Some("rssdkver") {
                return val.to_utf8_string().ok();
            }
        }
        None
    }

    /// Look up a contract error code across all `#[contracterror]` enums.
    /// Returns `(enum_name, variant_name)` if found.
    pub fn lookup_error_variant(&self, code: u32) -> Option<(String, String)> {
        for (enum_name, spec) in &self.error_enums {
            for case in spec.cases.iter() {
                if case.value == code
                    && let Ok(vname) = case.name.to_utf8_string()
                {
                    return Some((enum_name.clone(), vname));
                }
            }
        }
        None
    }

    pub fn resolve_type_name(&self, type_def: &ScSpecTypeDef) -> Option<String> {
        if let ScSpecTypeDef::Udt(u) = type_def {
            u.name.to_utf8_string().ok()
        } else {
            None
        }
    }

    /// Look up the data type of a specific variant within a union.
    /// Returns the first type from TupleV0 variants, None for VoidV0 variants.
    pub fn find_variant_data_type(
        &self,
        union_name: &str,
        variant_name: &str,
    ) -> Option<ScSpecTypeDef> {
        use stellar_xdr::ScSpecUdtUnionCaseV0;
        let spec = self.unions.get(union_name)?;
        for case in spec.cases.iter() {
            if let ScSpecUdtUnionCaseV0::TupleV0(t) = case
                && t.name.to_utf8_string().ok().as_deref() == Some(variant_name)
            {
                return t.type_.first().cloned();
            }
        }
        None
    }

    /// Check if a type name refers to an integer enum (not a union/struct).
    pub fn is_integer_enum(&self, type_name: &str) -> bool {
        self.enums.contains_key(type_name)
    }

    /// Find an event by its symbol name (typically snake_case event name matching
    /// the struct name). Returns the struct-style name and ordered topic field names.
    pub fn find_event_by_symbol(&self, symbol: &str) -> Option<(String, Vec<String>)> {
        for (name, spec) in &self.events {
            if name.eq_ignore_ascii_case(symbol) || camel_to_lower(name) == symbol || name == symbol
            {
                let topic_fields: Vec<String> = spec
                    .params
                    .iter()
                    .filter(|p| p.location == ScSpecEventParamLocationV0::TopicList)
                    .filter_map(|p| p.name.to_utf8_string().ok())
                    .collect();
                return Some((name.clone(), topic_fields));
            }
        }
        None
    }

    /// Look up a variant name across all unions.
    /// Returns `(union_name, has_data)` where `has_data` indicates whether the
    /// variant carries associated data (TupleV0 vs VoidV0).
    /// If the variant name exists in multiple unions, returns None to avoid ambiguity.
    pub fn find_union_variant(&self, variant_name: &str) -> Option<(String, bool)> {
        use stellar_xdr::ScSpecUdtUnionCaseV0;
        let mut found: Option<(String, bool)> = None;
        for (union_name, spec) in &self.unions {
            for case in spec.cases.iter() {
                let (case_name, has_data) = match case {
                    ScSpecUdtUnionCaseV0::VoidV0(v) => (v.name.to_utf8_string().ok(), false),
                    ScSpecUdtUnionCaseV0::TupleV0(t) => (t.name.to_utf8_string().ok(), true),
                };
                if case_name.as_deref() == Some(variant_name) {
                    if found.is_some() {
                        // Ambiguous — variant name exists in multiple unions
                        return None;
                    }
                    found = Some((union_name.clone(), has_data));
                }
            }
        }
        found
    }

    /// Find a union (complex enum) whose variant names match the given list.
    /// Returns `(union_name, variant_has_data)` where `variant_has_data[i]` is
    /// true if the i-th variant carries associated data (TupleV0).
    pub fn find_union_by_variants(&self, variant_names: &[String]) -> Option<(String, Vec<bool>)> {
        use stellar_xdr::ScSpecUdtUnionCaseV0;

        for (name, spec) in &self.unions {
            let spec_variants: Vec<String> = spec
                .cases
                .iter()
                .filter_map(|case| match case {
                    ScSpecUdtUnionCaseV0::VoidV0(v) => v.name.to_utf8_string().ok(),
                    ScSpecUdtUnionCaseV0::TupleV0(t) => t.name.to_utf8_string().ok(),
                })
                .collect();
            if spec_variants == variant_names {
                let has_data: Vec<bool> = spec
                    .cases
                    .iter()
                    .map(|case| matches!(case, ScSpecUdtUnionCaseV0::TupleV0(_)))
                    .collect();
                return Some((name.clone(), has_data));
            }
        }
        None
    }
}
