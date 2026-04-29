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
