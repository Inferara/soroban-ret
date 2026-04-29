/// Export table analyzer.
///
/// Extracts exported function names and identifies contract entry points.

#[derive(Debug, Clone)]
pub struct ExportEntry {
    pub name: String,
    pub func_index: u32,
}

#[derive(Debug, Default)]
pub struct ExportTable {
    pub functions: Vec<ExportEntry>,
}

impl ExportTable {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
        }
    }

    pub fn add(&mut self, name: String, func_index: u32) {
        self.functions.push(ExportEntry { name, func_index });
    }

    /// Get all contract entry points (excluding memory, table, global exports).
    /// Also excludes the `_` export which is the WASM memory export in some cases.
    pub fn contract_functions(&self) -> impl Iterator<Item = &ExportEntry> {
        self.functions
            .iter()
            .filter(|e| !is_non_function_export(&e.name))
    }

    /// Check if a specific function name is exported
    pub fn has_function(&self, name: &str) -> bool {
        self.functions.iter().any(|e| e.name == name)
    }

    /// Get export by name
    pub fn get_function(&self, name: &str) -> Option<&ExportEntry> {
        self.functions.iter().find(|e| e.name == name)
    }

    /// Check for constructor export
    pub fn has_constructor(&self) -> bool {
        self.has_function("__constructor")
    }

    /// Check for auth hook export
    pub fn has_check_auth(&self) -> bool {
        self.has_function("__check_auth")
    }
}

fn is_non_function_export(name: &str) -> bool {
    // These are standard WASM exports that are not contract functions
    matches!(name, "memory" | "__data_end" | "__heap_base")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn populated_table() -> ExportTable {
        let mut t = ExportTable::new();
        t.add("memory".into(), 0);
        t.add("__data_end".into(), 0);
        t.add("__heap_base".into(), 0);
        t.add("transfer".into(), 5);
        t.add("balance".into(), 6);
        t.add("__constructor".into(), 7);
        t.add("__check_auth".into(), 8);
        t
    }

    #[test]
    fn add_appends_in_order() {
        let t = populated_table();
        assert_eq!(t.functions.len(), 7);
        assert_eq!(t.functions[3].name, "transfer");
        assert_eq!(t.functions[3].func_index, 5);
    }

    #[test]
    fn contract_functions_filters_well_known_non_functions() {
        let t = populated_table();
        let names: Vec<&str> = t.contract_functions().map(|e| e.name.as_str()).collect();
        assert_eq!(
            names,
            vec!["transfer", "balance", "__constructor", "__check_auth"]
        );
    }

    #[test]
    fn has_function_lookup() {
        let t = populated_table();
        assert!(t.has_function("transfer"));
        assert!(!t.has_function("does_not_exist"));
    }

    #[test]
    fn get_function_returns_entry_when_present() {
        let t = populated_table();
        let entry = t.get_function("balance").expect("entry");
        assert_eq!(entry.func_index, 6);
        assert!(t.get_function("missing").is_none());
    }

    #[test]
    fn has_constructor_detects_double_underscore_export() {
        let t = populated_table();
        assert!(t.has_constructor());

        let mut empty = ExportTable::new();
        empty.add("foo".into(), 0);
        assert!(!empty.has_constructor());
    }

    #[test]
    fn has_check_auth_detects_double_underscore_export() {
        let t = populated_table();
        assert!(t.has_check_auth());

        let mut empty = ExportTable::new();
        empty.add("transfer".into(), 0);
        assert!(!empty.has_check_auth());
    }

    #[test]
    fn export_table_default_constructs_empty() {
        let t = ExportTable::default();
        assert_eq!(t.functions.len(), 0);
    }
}
