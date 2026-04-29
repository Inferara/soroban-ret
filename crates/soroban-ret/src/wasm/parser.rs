/// WASM binary parser.
///
/// Uses wasmparser to extract all sections from a Soroban WASM binary.
use std::collections::HashMap;
use wasmparser::{Parser, Payload, TypeRef};

use super::data::DataSection;
use super::exports::ExportTable;
use super::imports::ImportTable;
use super::ir::{WasmFunction, WasmInstr, WasmType, convert_operator, convert_val_type};

#[derive(Debug)]
pub struct FuncType {
    pub params: Vec<WasmType>,
    pub results: Vec<WasmType>,
}

#[derive(Debug)]
pub struct WasmModule {
    pub custom_sections: HashMap<String, Vec<u8>>,
    pub imports: ImportTable,
    pub exports: ExportTable,
    pub functions: Vec<WasmFunction>,
    pub data_sections: DataSection,
    pub types: Vec<FuncType>,
    /// Number of imported functions (these come before defined functions in the index space)
    pub num_imported_functions: u32,
    /// Diagnostics collected during parsing
    pub parse_diagnostics: Vec<super::validate::SorobanDiagnostic>,
    /// Variable names extracted from DWARF debug sections, keyed by (func_index, local_index).
    /// Populated only when the `dwarf` feature is enabled and debug sections are present.
    pub dwarf_names: HashMap<(u32, u32), String>,
}

impl WasmModule {
    pub fn parse(wasm: &[u8]) -> Result<Self, String> {
        let mut custom_sections = HashMap::new();
        let mut imports = ImportTable::new();
        let mut exports = ExportTable::new();
        let mut data_sections = DataSection::new();
        let mut types = Vec::new();
        let mut function_type_indices = Vec::new();
        let mut function_bodies: Vec<(Vec<WasmType>, Vec<WasmInstr>)> = Vec::new();
        let mut num_imported_functions: u32 = 0;
        let mut parse_diagnostics: Vec<super::validate::SorobanDiagnostic> = Vec::new();
        let mut global_init_values: Vec<Option<i64>> = Vec::new();

        for payload in Parser::new(0).parse_all(wasm) {
            let payload = payload.map_err(|e| format!("WASM parse error: {}", e))?;

            match payload {
                Payload::CustomSection(section) => {
                    custom_sections.insert(section.name().to_string(), section.data().to_vec());
                }

                Payload::TypeSection(reader) => {
                    for ty in reader {
                        let ty = ty.map_err(|e| format!("type section error: {}", e))?;
                        // wasmparser 0.247: CompositeType wraps a CompositeInnerType in `inner`.
                        for sub_type in ty.into_types() {
                            if let wasmparser::CompositeInnerType::Func(func_type) =
                                sub_type.composite_type.inner
                            {
                                let params = func_type
                                    .params()
                                    .iter()
                                    .filter_map(convert_val_type)
                                    .collect();
                                let results = func_type
                                    .results()
                                    .iter()
                                    .filter_map(convert_val_type)
                                    .collect();
                                types.push(FuncType { params, results });
                            }
                        }
                    }
                }

                Payload::ImportSection(reader) => {
                    // wasmparser 0.247: the import reader yields `Imports<'a>`, an enum
                    // with three variants (`Single`, `Compact1`, `Compact2`) describing
                    // how the binary groups module/name/type triples. We flatten all
                    // shapes back to `(module, name, ty)` tuples.
                    let mut handle = |module: &str, name: &str, ty: TypeRef| match ty {
                        TypeRef::Func(type_index) => {
                            imports.add(module, name, type_index);
                            num_imported_functions += 1;
                        }
                        TypeRef::Global(_) => {
                            // Imported globals have no initializer in the module, so
                            // they cannot be resolved to a concrete constant here.
                            global_init_values.push(None);
                        }
                        _ => {}
                    };
                    for group in reader {
                        let group = group.map_err(|e| format!("import section error: {}", e))?;
                        match group {
                            wasmparser::Imports::Single(_, import) => {
                                handle(import.module, import.name, import.ty);
                            }
                            wasmparser::Imports::Compact1 { module, items } => {
                                for item in items {
                                    let item =
                                        item.map_err(|e| format!("import section error: {}", e))?;
                                    handle(module, item.name, item.ty);
                                }
                            }
                            wasmparser::Imports::Compact2 { module, ty, names } => {
                                for name in names {
                                    let name =
                                        name.map_err(|e| format!("import section error: {}", e))?;
                                    handle(module, name, ty);
                                }
                            }
                        }
                    }
                }

                Payload::GlobalSection(reader) => {
                    for global in reader {
                        let global = global.map_err(|e| format!("global section error: {}", e))?;
                        let value = eval_const_expr(&global.init_expr, &global_init_values);
                        global_init_values.push(value);
                    }
                }

                Payload::FunctionSection(reader) => {
                    for func in reader {
                        let type_index =
                            func.map_err(|e| format!("function section error: {}", e))?;
                        function_type_indices.push(type_index);
                    }
                }

                Payload::ExportSection(reader) => {
                    for export in reader {
                        let export = export.map_err(|e| format!("export section error: {}", e))?;
                        if let wasmparser::ExternalKind::Func = export.kind {
                            exports.add(export.name.to_string(), export.index);
                        }
                    }
                }

                Payload::CodeSectionEntry(body) => {
                    // Cap total locals per function to bound memory in the face of
                    // adversarial WASM (e.g. count = u32::MAX which would otherwise
                    // request gigabytes from the allocator and abort).
                    const MAX_LOCALS_PER_FUNCTION: u32 = 1_000_000;
                    let mut locals = Vec::new();
                    let mut total_locals: u32 = 0;
                    let local_reader = body
                        .get_locals_reader()
                        .map_err(|e| format!("code section error: {}", e))?;
                    for local in local_reader {
                        let (count, val_type) =
                            local.map_err(|e| format!("local read error: {}", e))?;
                        total_locals = total_locals.checked_add(count).ok_or_else(|| {
                            format!(
                                "function locals count overflows u32 (limit {} per function)",
                                MAX_LOCALS_PER_FUNCTION
                            )
                        })?;
                        if total_locals > MAX_LOCALS_PER_FUNCTION {
                            return Err(format!(
                                "function declares {} locals, exceeding the {} cap",
                                total_locals, MAX_LOCALS_PER_FUNCTION
                            ));
                        }
                        if let Some(wt) = convert_val_type(&val_type) {
                            for _ in 0..count {
                                locals.push(wt);
                            }
                        }
                    }

                    let mut instructions = Vec::new();
                    let op_reader = body
                        .get_operators_reader()
                        .map_err(|e| format!("code section error: {}", e))?;
                    for op in op_reader {
                        let op = op.map_err(|e| format!("operator read error: {}", e))?;
                        instructions.push(convert_operator(&op));
                    }

                    function_bodies.push((locals, instructions));
                }

                Payload::DataSection(reader) => {
                    for data in reader {
                        let data = data.map_err(|e| format!("data section error: {}", e))?;
                        match data.kind {
                            wasmparser::DataKind::Active {
                                memory_index: 0,
                                offset_expr,
                            } => {
                                // Try to evaluate the offset expression
                                if let Some(offset) =
                                    eval_data_offset_expr(&offset_expr, &global_init_values)
                                {
                                    data_sections.add(offset, data.data.to_vec());
                                } else {
                                    parse_diagnostics.push(super::validate::SorobanDiagnostic {
                                        severity: super::validate::DiagnosticSeverity::Warning,
                                        category:
                                            super::validate::DiagnosticCategory::UnknownInstruction,
                                        message: "Could not resolve active data segment offset expression"
                                            .to_string(),
                                        function_index: None,
                                    });
                                }
                            }
                            wasmparser::DataKind::Active {
                                memory_index,
                                offset_expr,
                            } => {
                                // Non-zero memory index — not valid in Soroban, but still process data
                                parse_diagnostics.push(super::validate::SorobanDiagnostic {
                                    severity: super::validate::DiagnosticSeverity::Warning,
                                    category: super::validate::DiagnosticCategory::MultiMemory,
                                    message: format!(
                                        "Data segment targets memory index {} (only memory 0 allowed in Soroban)",
                                        memory_index
                                    ),
                                    function_index: None,
                                });
                                if let Some(offset) =
                                    eval_data_offset_expr(&offset_expr, &global_init_values)
                                {
                                    data_sections.add(offset, data.data.to_vec());
                                } else {
                                    parse_diagnostics.push(super::validate::SorobanDiagnostic {
                                        severity: super::validate::DiagnosticSeverity::Warning,
                                        category:
                                            super::validate::DiagnosticCategory::UnknownInstruction,
                                        message: format!(
                                            "Could not resolve active data segment offset expression for memory index {}",
                                            memory_index
                                        ),
                                        function_index: None,
                                    });
                                }
                            }
                            wasmparser::DataKind::Passive => {
                                // Passive data segment, store at offset 0
                                data_sections.add(0, data.data.to_vec());
                            }
                        }
                    }
                }

                _ => {} // Skip other sections
            }
        }

        // Build WasmFunction objects
        let mut functions = Vec::new();
        for (i, (locals, body)) in function_bodies.into_iter().enumerate() {
            let index = num_imported_functions + i as u32;
            let type_index = function_type_indices.get(i).copied().unwrap_or(0);
            functions.push(WasmFunction {
                index,
                type_index,
                locals,
                body,
            });
        }

        let dwarf_names = HashMap::new();

        Ok(WasmModule {
            custom_sections,
            imports,
            exports,
            functions,
            data_sections,
            types,
            num_imported_functions,
            parse_diagnostics,
            dwarf_names,
        })
    }

    /// Get a function by its absolute index (including imports)
    pub fn get_function(&self, index: u32) -> Option<&WasmFunction> {
        if index < self.num_imported_functions {
            return None; // It's an import, not a defined function
        }
        let local_index = (index - self.num_imported_functions) as usize;
        self.functions.get(local_index)
    }

    /// Get the type signature for a function index
    pub fn get_func_type(&self, index: u32) -> Option<&FuncType> {
        if index < self.num_imported_functions {
            // For imports, look up from import table
            let import = self.imports.get_by_index(index)?;
            self.types.get(import.type_index as usize)
        } else {
            let func = self.get_function(index)?;
            self.types.get(func.type_index as usize)
        }
    }
}

/// Evaluate a constant expression to an i64 when all referenced globals are known.
fn eval_const_expr(expr: &wasmparser::ConstExpr, globals: &[Option<i64>]) -> Option<i64> {
    // wasmparser 0.247: ConstExpr exposes an OperatorsReader (was BinaryReader::read_operator).
    let mut reader = expr.get_operators_reader();
    let value = match reader.read().ok()? {
        wasmparser::Operator::I32Const { value } => value as i64,
        wasmparser::Operator::I64Const { value } => value,
        wasmparser::Operator::GlobalGet { global_index } => {
            globals.get(global_index as usize).copied().flatten()?
        }
        wasmparser::Operator::End => return None,
        _ => return None,
    };

    match reader.read().ok()? {
        wasmparser::Operator::End if reader.eof() => Some(value),
        _ => None,
    }
}

/// Evaluate a constant init expression to get a non-negative u32 data offset.
fn eval_data_offset_expr(expr: &wasmparser::ConstExpr, globals: &[Option<i64>]) -> Option<u32> {
    let value = eval_const_expr(expr, globals)?;
    u32::try_from(value).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_data_offset_from_global_get() {
        let wasm = wat::parse_str(
            r#"(module
                (memory (export "memory") 1)
                (global $base i32 (i32.const 16))
                (data (global.get $base) "hello")
            )"#,
        )
        .expect("failed to parse WAT");

        let module = WasmModule::parse(&wasm).expect("failed to parse WASM");

        assert_eq!(
            module.data_sections.read_string(16, 5),
            Some("hello".to_string())
        );
        assert!(module.data_sections.read_string(0, 5).is_none());
        assert!(module.parse_diagnostics.is_empty());
    }

    #[test]
    fn test_reject_multi_operator_data_offset_expr() {
        let wasm = wat::parse_str(
            r#"(module
                (memory (export "memory") 1)
                (global $base i32 (i32.const 16))
                (data (i32.add (global.get $base) (i32.const 4)) "hello")
            )"#,
        )
        .expect("failed to parse WAT");

        let module = WasmModule::parse(&wasm).expect("failed to parse WASM");

        assert!(module.data_sections.read_string(16, 5).is_none());
        assert!(module.data_sections.read_string(20, 5).is_none());
        assert!(
            module.parse_diagnostics.iter().any(|d| d
                .message
                .contains("Could not resolve active data segment offset expression")),
            "expected unresolved offset diagnostic"
        );
    }
}
