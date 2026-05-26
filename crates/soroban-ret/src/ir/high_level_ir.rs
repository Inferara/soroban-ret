use stellar_xdr::curr::ScSpecTypeDef;

use super::soroban_ir::SorobanStmt;
use crate::wasm::WasmType;

/// Tracks which crypto submodules a contract uses, enabling type alias mapping.
#[derive(Debug, Default)]
pub struct CryptoUsage {
    pub uses_bn254: bool,
    pub uses_bls12_381: bool,
}

impl CryptoUsage {
    pub fn has_any(&self) -> bool {
        self.uses_bn254 || self.uses_bls12_381
    }
}

/// A complete decompiled contract module
#[derive(Debug)]
pub struct ContractModule {
    pub name: String,
    pub types: Vec<TypeDef>,
    pub error_enums: Vec<TypeDef>,
    pub events: Vec<TypeDef>,
    pub contract_struct: String,
    pub functions: Vec<ContractFn>,
    pub has_constructor: bool,
    pub standard_interfaces: Vec<String>,
    pub crypto_usage: CryptoUsage,
    /// Whether the input was detected as a Soroban contract
    pub is_soroban: bool,
}

/// A type definition (struct, enum, error enum, event)
#[derive(Debug, Clone)]
pub struct TypeDef {
    pub kind: TypeDefKind,
    pub name: String,
    /// Pre-generated token stream from soroban-spec-rust (if available)
    pub generated_tokens: Option<proc_macro2::TokenStream>,
}

#[derive(Debug, Clone)]
pub enum TypeDefKind {
    Struct,
    TupleStruct,
    Union,
    Enum,
    ErrorEnum,
    Event,
}

/// A contract function
#[derive(Debug)]
pub struct ContractFn {
    pub name: String,
    pub params: Vec<FnParam>,
    pub return_type: Option<ScSpecTypeDef>,
    pub body: Vec<SorobanStmt>,
    pub takes_env: bool,
    pub is_constructor: bool,
    pub is_check_auth: bool,
    /// The dispatch wrapper calls a bare `unreachable` trap function after the body.
    /// This indicates the original source ends with `panic!()`, but the panic is
    /// lost during inlining because the body's WASM return creates a terminating loop.
    /// The pipeline appends Panic after optimization when this flag is set.
    pub wrapper_panics: bool,
    /// Whether the lifter detected host calls during body lifting. When true but
    /// the body is empty after optimization, the function had real logic that was
    /// lost during lifting — should NOT be treated as an identity passthrough.
    pub had_host_calls: bool,
    /// Number of leading WASM parameter slots not represented in `params`.
    /// This tracks the concrete local layout, which may differ from `takes_env`
    /// when LTO elides Env or lowering introduces non-source parameter slots.
    pub wasm_param_base: u32,
    /// Raw WASM type signature for generic (non-Soroban) functions.
    /// When present, codegen uses this instead of ScSpecTypeDef-based params/return_type.
    pub wasm_signature: Option<WasmFnSignature>,
}

/// Raw WASM function type signature, used for generic (non-Soroban) WASM decompilation.
#[derive(Debug, Clone)]
pub struct WasmFnSignature {
    pub params: Vec<WasmType>,
    pub results: Vec<WasmType>,
}

#[derive(Debug, Clone)]
pub struct FnParam {
    pub name: String,
    pub type_def: ScSpecTypeDef,
}

impl ContractModule {
    pub fn new(name: String) -> Self {
        Self {
            name,
            types: Vec::new(),
            error_enums: Vec::new(),
            events: Vec::new(),
            contract_struct: "Contract".to_string(),
            functions: Vec::new(),
            has_constructor: false,
            standard_interfaces: Vec::new(),
            crypto_usage: CryptoUsage::default(),
            is_soroban: true,
        }
    }
}
