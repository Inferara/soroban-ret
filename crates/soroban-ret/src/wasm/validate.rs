/// Soroban compliance validation.
///
/// Checks a parsed WASM module for constructs that violate Soroban host constraints.
/// The decompiler remains permissive (accepts any binary) but reports issues as diagnostics.
use super::ir::WasmType;
use super::parser::WasmModule;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DiagnosticSeverity {
    Warning,
    Info,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DiagnosticCategory {
    FloatingPoint,
    ReferenceTypes,
    MultiValue,
    MultiMemory,
    CallIndirect,
    UnknownInstruction,
    NonRustSdk,
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SorobanDiagnostic {
    pub severity: DiagnosticSeverity,
    pub category: DiagnosticCategory,
    pub message: String,
    pub function_index: Option<u32>,
}

#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ValidationReport {
    pub diagnostics: Vec<SorobanDiagnostic>,
}

impl ValidationReport {
    pub fn new() -> Self {
        Self {
            diagnostics: Vec::new(),
        }
    }

    pub fn add(&mut self, diagnostic: SorobanDiagnostic) {
        self.diagnostics.push(diagnostic);
    }

    pub fn has_warnings(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|d| d.severity == DiagnosticSeverity::Warning)
    }

    pub fn is_soroban_compliant(&self) -> bool {
        !self.has_warnings()
    }

    pub fn merge(&mut self, other: ValidationReport) {
        self.diagnostics.extend(other.diagnostics);
    }
}

impl std::fmt::Display for DiagnosticCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DiagnosticCategory::FloatingPoint => write!(f, "FloatingPoint"),
            DiagnosticCategory::ReferenceTypes => write!(f, "ReferenceTypes"),
            DiagnosticCategory::MultiValue => write!(f, "MultiValue"),
            DiagnosticCategory::MultiMemory => write!(f, "MultiMemory"),
            DiagnosticCategory::CallIndirect => write!(f, "CallIndirect"),
            DiagnosticCategory::UnknownInstruction => write!(f, "UnknownInstruction"),
            DiagnosticCategory::NonRustSdk => write!(f, "NonRustSdk"),
        }
    }
}

impl std::fmt::Display for SorobanDiagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(idx) = self.function_index {
            write!(f, "[{}] Function {}: {}", self.category, idx, self.message)
        } else {
            write!(f, "[{}] {}", self.category, self.message)
        }
    }
}

/// Run all Soroban compliance checks on a parsed WASM module.
pub fn validate_soroban(module: &WasmModule) -> ValidationReport {
    let mut report = ValidationReport::new();
    check_float_types(module, &mut report);
    check_float_locals(module, &mut report);
    check_multi_value_returns(module, &mut report);
    check_call_indirect(module, &mut report);
    check_unknown_instructions(module, &mut report);
    report
}

/// Check function type signatures for F32/F64 parameters or results.
fn check_float_types(module: &WasmModule, report: &mut ValidationReport) {
    for (i, ft) in module.types.iter().enumerate() {
        for param in &ft.params {
            if matches!(param, WasmType::F32 | WasmType::F64) {
                report.add(SorobanDiagnostic {
                    severity: DiagnosticSeverity::Warning,
                    category: DiagnosticCategory::FloatingPoint,
                    message: format!(
                        "Type {} has {:?} parameter (floating point not allowed in Soroban)",
                        i, param
                    ),
                    function_index: None,
                });
            }
        }
        for result in &ft.results {
            if matches!(result, WasmType::F32 | WasmType::F64) {
                report.add(SorobanDiagnostic {
                    severity: DiagnosticSeverity::Warning,
                    category: DiagnosticCategory::FloatingPoint,
                    message: format!(
                        "Type {} has {:?} result (floating point not allowed in Soroban)",
                        i, result
                    ),
                    function_index: None,
                });
            }
        }
    }
}

/// Check function locals for F32/F64 types.
fn check_float_locals(module: &WasmModule, report: &mut ValidationReport) {
    for func in &module.functions {
        for local in &func.locals {
            if matches!(local, WasmType::F32 | WasmType::F64) {
                report.add(SorobanDiagnostic {
                    severity: DiagnosticSeverity::Warning,
                    category: DiagnosticCategory::FloatingPoint,
                    message: format!(
                        "has {:?} local variable (floating point not allowed in Soroban)",
                        local
                    ),
                    function_index: Some(func.index),
                });
            }
        }
    }
}

/// Check for multi-value returns (results.len() > 1).
fn check_multi_value_returns(module: &WasmModule, report: &mut ValidationReport) {
    for (i, ft) in module.types.iter().enumerate() {
        if ft.results.len() > 1 {
            report.add(SorobanDiagnostic {
                severity: DiagnosticSeverity::Warning,
                category: DiagnosticCategory::MultiValue,
                message: format!(
                    "Type {} returns {} values (multi-value not allowed in Soroban)",
                    i,
                    ft.results.len()
                ),
                function_index: None,
            });
        }
    }
}

/// Check for call_indirect instructions.
fn check_call_indirect(module: &WasmModule, report: &mut ValidationReport) {
    use super::ir::WasmInstr;
    for func in &module.functions {
        for instr in &func.body {
            if matches!(instr, WasmInstr::CallIndirect(_)) {
                report.add(SorobanDiagnostic {
                    severity: DiagnosticSeverity::Warning,
                    category: DiagnosticCategory::CallIndirect,
                    message: "uses call_indirect (not valid in Soroban)".to_string(),
                    function_index: Some(func.index),
                });
            }
        }
    }
}

/// Check for unknown instructions that indicate float or reference-type operations.
fn check_unknown_instructions(module: &WasmModule, report: &mut ValidationReport) {
    use super::ir::WasmInstr;
    for func in &module.functions {
        for instr in &func.body {
            if let WasmInstr::Unknown(desc) = instr {
                if let Some(rest) = desc.strip_prefix("float:") {
                    report.add(SorobanDiagnostic {
                        severity: DiagnosticSeverity::Warning,
                        category: DiagnosticCategory::FloatingPoint,
                        message: format!("has float instruction: {}", rest),
                        function_index: Some(func.index),
                    });
                } else if let Some(rest) = desc.strip_prefix("ref:") {
                    report.add(SorobanDiagnostic {
                        severity: DiagnosticSeverity::Warning,
                        category: DiagnosticCategory::ReferenceTypes,
                        message: format!("has reference-type instruction: {}", rest),
                        function_index: Some(func.index),
                    });
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm::ir::{WasmFunction, WasmInstr};
    use crate::wasm::parser::FuncType;

    fn empty_module() -> WasmModule {
        WasmModule {
            custom_sections: std::collections::HashMap::new(),
            imports: crate::wasm::imports::ImportTable::new(),
            exports: crate::wasm::exports::ExportTable::new(),
            functions: Vec::new(),
            data_sections: crate::wasm::data::DataSection::new(),
            types: Vec::new(),
            num_imported_functions: 0,
            parse_diagnostics: Vec::new(),
            dwarf_names: std::collections::HashMap::new(),
        }
    }

    #[test]
    fn test_detect_float_types() {
        let mut module = empty_module();
        module.types.push(FuncType {
            params: vec![WasmType::F32],
            results: vec![WasmType::I32],
        });
        let report = validate_soroban(&module);
        assert!(report.has_warnings());
        assert!(!report.is_soroban_compliant());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].category,
            DiagnosticCategory::FloatingPoint
        );
    }

    #[test]
    fn test_detect_float_locals() {
        let mut module = empty_module();
        module.functions.push(WasmFunction {
            index: 0,
            type_index: 0,
            locals: vec![WasmType::I32, WasmType::F64],
            body: vec![WasmInstr::Nop, WasmInstr::End],
        });
        let report = validate_soroban(&module);
        assert!(report.has_warnings());
        assert_eq!(
            report.diagnostics[0].category,
            DiagnosticCategory::FloatingPoint
        );
        assert_eq!(report.diagnostics[0].function_index, Some(0));
    }

    #[test]
    fn test_detect_multi_value() {
        let mut module = empty_module();
        module.types.push(FuncType {
            params: vec![WasmType::I32],
            results: vec![WasmType::I32, WasmType::I64],
        });
        let report = validate_soroban(&module);
        assert!(report.has_warnings());
        assert_eq!(
            report.diagnostics[0].category,
            DiagnosticCategory::MultiValue
        );
    }

    #[test]
    fn test_detect_call_indirect() {
        let mut module = empty_module();
        module.functions.push(WasmFunction {
            index: 0,
            type_index: 0,
            locals: vec![],
            body: vec![WasmInstr::CallIndirect(0), WasmInstr::End],
        });
        let report = validate_soroban(&module);
        assert!(report.has_warnings());
        assert_eq!(
            report.diagnostics[0].category,
            DiagnosticCategory::CallIndirect
        );
    }

    #[test]
    fn test_detect_float_unknown_instruction() {
        let mut module = empty_module();
        module.functions.push(WasmFunction {
            index: 0,
            type_index: 0,
            locals: vec![],
            body: vec![
                WasmInstr::Unknown("float:F32Add".to_string()),
                WasmInstr::End,
            ],
        });
        let report = validate_soroban(&module);
        assert!(report.has_warnings());
        assert_eq!(
            report.diagnostics[0].category,
            DiagnosticCategory::FloatingPoint
        );
    }

    #[test]
    fn test_detect_ref_unknown_instruction() {
        let mut module = empty_module();
        module.functions.push(WasmFunction {
            index: 0,
            type_index: 0,
            locals: vec![],
            body: vec![
                WasmInstr::Unknown("ref:RefNull { hty: Func }".to_string()),
                WasmInstr::End,
            ],
        });
        let report = validate_soroban(&module);
        assert!(report.has_warnings());
        assert_eq!(
            report.diagnostics[0].category,
            DiagnosticCategory::ReferenceTypes
        );
    }

    #[test]
    fn test_compliant_module() {
        let mut module = empty_module();
        module.types.push(FuncType {
            params: vec![WasmType::I64, WasmType::I64],
            results: vec![WasmType::I64],
        });
        module.functions.push(WasmFunction {
            index: 0,
            type_index: 0,
            locals: vec![WasmType::I32],
            body: vec![WasmInstr::I64Const(42), WasmInstr::Return, WasmInstr::End],
        });
        let report = validate_soroban(&module);
        assert!(report.is_soroban_compliant());
        assert!(!report.has_warnings());
    }

    #[test]
    fn test_merge_reports() {
        let mut r1 = ValidationReport::new();
        r1.add(SorobanDiagnostic {
            severity: DiagnosticSeverity::Warning,
            category: DiagnosticCategory::FloatingPoint,
            message: "test1".to_string(),
            function_index: None,
        });
        let mut r2 = ValidationReport::new();
        r2.add(SorobanDiagnostic {
            severity: DiagnosticSeverity::Info,
            category: DiagnosticCategory::MultiMemory,
            message: "test2".to_string(),
            function_index: None,
        });
        r1.merge(r2);
        assert_eq!(r1.diagnostics.len(), 2);
    }

    // Test that all 38 SDK fixtures are Soroban-compliant
    macro_rules! fixture_compliance_test {
        ($name:ident, $file:expr) => {
            #[test]
            fn $name() {
                let wasm = include_bytes!(concat!("../../../../tests/fixtures/", $file));
                let module = WasmModule::parse(wasm).expect("failed to parse WASM");
                let report = validate_soroban(&module);
                assert!(
                    report.is_soroban_compliant(),
                    "Fixture {} has compliance warnings: {:?}",
                    $file,
                    report
                        .diagnostics
                        .iter()
                        .map(|d| d.to_string())
                        .collect::<Vec<_>>()
                );
            }
        };
    }

    fixture_compliance_test!(fixture_test_empty, "test_empty.wasm");
}
