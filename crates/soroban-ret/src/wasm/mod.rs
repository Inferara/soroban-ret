pub mod data;
pub mod exports;
pub mod imports;
pub mod ir;
pub mod parser;
pub mod validate;

pub use data::{DataSection, DataSegment};
pub use exports::{ExportEntry, ExportTable};
pub use imports::{HostFunction, HostModule, ImportTable};
pub use ir::{BlockType, WasmBasicBlock, WasmFunction, WasmInstr, WasmType};
pub use parser::{FuncType, WasmModule};
pub use validate::{DiagnosticCategory, DiagnosticSeverity, SorobanDiagnostic, ValidationReport};
