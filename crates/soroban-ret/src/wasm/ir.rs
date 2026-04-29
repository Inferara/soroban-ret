/// Simplified WASM instruction IR for decompilation.
///
/// Translates wasmparser's `Operator` enum into a simpler representation
/// focused on instructions that appear in Soroban contracts.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmType {
    I32,
    I64,
    F32,
    F64,
}

#[derive(Debug, Clone)]
pub enum BlockType {
    Empty,
    Value(WasmType),
    FuncType(u32),
}

#[derive(Debug, Clone)]
pub enum WasmInstr {
    // Constants
    I32Const(i32),
    I64Const(i64),

    // Local variables
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),

    // Global variables
    GlobalGet(u32),
    GlobalSet(u32),

    // Arithmetic - i32
    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,

    // Arithmetic - i64
    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,

    // Comparison - i32
    I32Eqz,
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeS,
    I32LeU,
    I32GeS,
    I32GeU,

    // Comparison - i64
    I64Eqz,
    I64Eq,
    I64Ne,
    I64LtS,
    I64LtU,
    I64GtS,
    I64GtU,
    I64LeS,
    I64LeU,
    I64GeS,
    I64GeU,

    // Bitwise - i32
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,

    // Bitwise - i64
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,

    // Conversion
    I32WrapI64,
    I64ExtendI32S,
    I64ExtendI32U,

    // Memory loads (offset)
    I32Load(u32),
    I64Load(u32),
    I32Store(u32),
    I64Store(u32),
    I32Load8S(u32),
    I32Load8U(u32),
    I32Load16S(u32),
    I32Load16U(u32),
    I64Load8S(u32),
    I64Load8U(u32),
    I64Load16S(u32),
    I64Load16U(u32),
    I64Load32S(u32),
    I64Load32U(u32),

    // Memory stores (offset)
    I32Store8(u32),
    I32Store16(u32),
    I64Store8(u32),
    I64Store16(u32),
    I64Store32(u32),

    // Control flow
    Block { block_type: BlockType },
    Loop { block_type: BlockType },
    If { block_type: BlockType },
    Else,
    End,
    Br(u32),
    BrIf(u32),
    BrTable { targets: Vec<u32>, default: u32 },
    Return,
    Unreachable,

    // Calls
    Call(u32),
    CallIndirect(u32),

    // Stack manipulation
    Drop,
    Select,

    // Misc
    Nop,
    MemorySize,
    MemoryGrow,

    // Catch-all for unsupported operators
    Unknown(String),
}

#[derive(Debug)]
pub struct WasmBasicBlock {
    pub instructions: Vec<WasmInstr>,
}

#[derive(Debug)]
pub struct WasmFunction {
    pub index: u32,
    pub type_index: u32,
    pub locals: Vec<WasmType>,
    pub body: Vec<WasmInstr>,
}

/// Convert a wasmparser `BlockType` to our IR `BlockType`.
pub fn convert_block_type(bt: &wasmparser::BlockType) -> BlockType {
    match bt {
        wasmparser::BlockType::Empty => BlockType::Empty,
        wasmparser::BlockType::Type(vt) => match vt {
            wasmparser::ValType::I32 => BlockType::Value(WasmType::I32),
            wasmparser::ValType::I64 => BlockType::Value(WasmType::I64),
            wasmparser::ValType::F32 => BlockType::Value(WasmType::F32),
            wasmparser::ValType::F64 => BlockType::Value(WasmType::F64),
            _ => BlockType::Empty,
        },
        wasmparser::BlockType::FuncType(idx) => BlockType::FuncType(*idx),
    }
}

/// Convert a wasmparser `ValType` to our IR `WasmType`.
pub fn convert_val_type(vt: &wasmparser::ValType) -> Option<WasmType> {
    match vt {
        wasmparser::ValType::I32 => Some(WasmType::I32),
        wasmparser::ValType::I64 => Some(WasmType::I64),
        wasmparser::ValType::F32 => Some(WasmType::F32),
        wasmparser::ValType::F64 => Some(WasmType::F64),
        _ => None,
    }
}

/// Convert a wasmparser `Operator` to our IR `WasmInstr`.
pub fn convert_operator(op: &wasmparser::Operator<'_>) -> WasmInstr {
    use wasmparser::Operator;
    match op {
        // Constants
        Operator::I32Const { value } => WasmInstr::I32Const(*value),
        Operator::I64Const { value } => WasmInstr::I64Const(*value),

        // Locals
        Operator::LocalGet { local_index } => WasmInstr::LocalGet(*local_index),
        Operator::LocalSet { local_index } => WasmInstr::LocalSet(*local_index),
        Operator::LocalTee { local_index } => WasmInstr::LocalTee(*local_index),

        // Globals
        Operator::GlobalGet { global_index } => WasmInstr::GlobalGet(*global_index),
        Operator::GlobalSet { global_index } => WasmInstr::GlobalSet(*global_index),

        // i32 arithmetic
        Operator::I32Add => WasmInstr::I32Add,
        Operator::I32Sub => WasmInstr::I32Sub,
        Operator::I32Mul => WasmInstr::I32Mul,
        Operator::I32DivS => WasmInstr::I32DivS,
        Operator::I32DivU => WasmInstr::I32DivU,
        Operator::I32RemS => WasmInstr::I32RemS,
        Operator::I32RemU => WasmInstr::I32RemU,

        // i64 arithmetic
        Operator::I64Add => WasmInstr::I64Add,
        Operator::I64Sub => WasmInstr::I64Sub,
        Operator::I64Mul => WasmInstr::I64Mul,
        Operator::I64DivS => WasmInstr::I64DivS,
        Operator::I64DivU => WasmInstr::I64DivU,
        Operator::I64RemS => WasmInstr::I64RemS,
        Operator::I64RemU => WasmInstr::I64RemU,

        // i32 comparison
        Operator::I32Eqz => WasmInstr::I32Eqz,
        Operator::I32Eq => WasmInstr::I32Eq,
        Operator::I32Ne => WasmInstr::I32Ne,
        Operator::I32LtS => WasmInstr::I32LtS,
        Operator::I32LtU => WasmInstr::I32LtU,
        Operator::I32GtS => WasmInstr::I32GtS,
        Operator::I32GtU => WasmInstr::I32GtU,
        Operator::I32LeS => WasmInstr::I32LeS,
        Operator::I32LeU => WasmInstr::I32LeU,
        Operator::I32GeS => WasmInstr::I32GeS,
        Operator::I32GeU => WasmInstr::I32GeU,

        // i64 comparison
        Operator::I64Eqz => WasmInstr::I64Eqz,
        Operator::I64Eq => WasmInstr::I64Eq,
        Operator::I64Ne => WasmInstr::I64Ne,
        Operator::I64LtS => WasmInstr::I64LtS,
        Operator::I64LtU => WasmInstr::I64LtU,
        Operator::I64GtS => WasmInstr::I64GtS,
        Operator::I64GtU => WasmInstr::I64GtU,
        Operator::I64LeS => WasmInstr::I64LeS,
        Operator::I64LeU => WasmInstr::I64LeU,
        Operator::I64GeS => WasmInstr::I64GeS,
        Operator::I64GeU => WasmInstr::I64GeU,

        // i32 bitwise
        Operator::I32And => WasmInstr::I32And,
        Operator::I32Or => WasmInstr::I32Or,
        Operator::I32Xor => WasmInstr::I32Xor,
        Operator::I32Shl => WasmInstr::I32Shl,
        Operator::I32ShrS => WasmInstr::I32ShrS,
        Operator::I32ShrU => WasmInstr::I32ShrU,

        // i64 bitwise
        Operator::I64And => WasmInstr::I64And,
        Operator::I64Or => WasmInstr::I64Or,
        Operator::I64Xor => WasmInstr::I64Xor,
        Operator::I64Shl => WasmInstr::I64Shl,
        Operator::I64ShrS => WasmInstr::I64ShrS,
        Operator::I64ShrU => WasmInstr::I64ShrU,

        // Conversions
        Operator::I32WrapI64 => WasmInstr::I32WrapI64,
        Operator::I64ExtendI32S => WasmInstr::I64ExtendI32S,
        Operator::I64ExtendI32U => WasmInstr::I64ExtendI32U,

        // Memory loads
        Operator::I32Load { memarg } => WasmInstr::I32Load(memarg.offset as u32),
        Operator::I64Load { memarg } => WasmInstr::I64Load(memarg.offset as u32),
        Operator::I32Load8S { memarg } => WasmInstr::I32Load8S(memarg.offset as u32),
        Operator::I32Load8U { memarg } => WasmInstr::I32Load8U(memarg.offset as u32),
        Operator::I32Load16S { memarg } => WasmInstr::I32Load16S(memarg.offset as u32),
        Operator::I32Load16U { memarg } => WasmInstr::I32Load16U(memarg.offset as u32),
        Operator::I64Load8S { memarg } => WasmInstr::I64Load8S(memarg.offset as u32),
        Operator::I64Load8U { memarg } => WasmInstr::I64Load8U(memarg.offset as u32),
        Operator::I64Load16S { memarg } => WasmInstr::I64Load16S(memarg.offset as u32),
        Operator::I64Load16U { memarg } => WasmInstr::I64Load16U(memarg.offset as u32),
        Operator::I64Load32S { memarg } => WasmInstr::I64Load32S(memarg.offset as u32),
        Operator::I64Load32U { memarg } => WasmInstr::I64Load32U(memarg.offset as u32),

        // Memory stores
        Operator::I32Store { memarg } => WasmInstr::I32Store(memarg.offset as u32),
        Operator::I64Store { memarg } => WasmInstr::I64Store(memarg.offset as u32),
        Operator::I32Store8 { memarg } => WasmInstr::I32Store8(memarg.offset as u32),
        Operator::I32Store16 { memarg } => WasmInstr::I32Store16(memarg.offset as u32),
        Operator::I64Store8 { memarg } => WasmInstr::I64Store8(memarg.offset as u32),
        Operator::I64Store16 { memarg } => WasmInstr::I64Store16(memarg.offset as u32),
        Operator::I64Store32 { memarg } => WasmInstr::I64Store32(memarg.offset as u32),

        // Control flow
        Operator::Block { blockty } => WasmInstr::Block {
            block_type: convert_block_type(blockty),
        },
        Operator::Loop { blockty } => WasmInstr::Loop {
            block_type: convert_block_type(blockty),
        },
        Operator::If { blockty } => WasmInstr::If {
            block_type: convert_block_type(blockty),
        },
        Operator::Else => WasmInstr::Else,
        Operator::End => WasmInstr::End,
        Operator::Br { relative_depth } => WasmInstr::Br(*relative_depth),
        Operator::BrIf { relative_depth } => WasmInstr::BrIf(*relative_depth),
        Operator::BrTable { targets } => {
            let target_list: Vec<u32> = targets.targets().filter_map(|t| t.ok()).collect();
            WasmInstr::BrTable {
                targets: target_list,
                default: targets.default(),
            }
        }
        Operator::Return => WasmInstr::Return,
        Operator::Unreachable => WasmInstr::Unreachable,

        // Calls
        Operator::Call { function_index } => WasmInstr::Call(*function_index),
        Operator::CallIndirect { type_index, .. } => WasmInstr::CallIndirect(*type_index),

        // Stack
        Operator::Drop => WasmInstr::Drop,
        Operator::Select => WasmInstr::Select,

        // Misc
        Operator::Nop => WasmInstr::Nop,
        Operator::MemorySize { .. } => WasmInstr::MemorySize,
        Operator::MemoryGrow { .. } => WasmInstr::MemoryGrow,

        // Floating-point operations (not allowed in Soroban)
        Operator::F32Const { .. }
        | Operator::F64Const { .. }
        | Operator::F32Add
        | Operator::F32Sub
        | Operator::F32Mul
        | Operator::F32Div
        | Operator::F64Add
        | Operator::F64Sub
        | Operator::F64Mul
        | Operator::F64Div
        | Operator::F32Load { .. }
        | Operator::F64Load { .. }
        | Operator::F32Store { .. }
        | Operator::F64Store { .. }
        | Operator::F32Eq
        | Operator::F32Ne
        | Operator::F32Lt
        | Operator::F32Gt
        | Operator::F32Le
        | Operator::F32Ge
        | Operator::F64Eq
        | Operator::F64Ne
        | Operator::F64Lt
        | Operator::F64Gt
        | Operator::F64Le
        | Operator::F64Ge
        | Operator::F32Abs
        | Operator::F32Neg
        | Operator::F32Ceil
        | Operator::F32Floor
        | Operator::F32Sqrt
        | Operator::F64Abs
        | Operator::F64Neg
        | Operator::F64Ceil
        | Operator::F64Floor
        | Operator::F64Sqrt
        | Operator::I32TruncF32S
        | Operator::I32TruncF32U
        | Operator::I32TruncF64S
        | Operator::I32TruncF64U
        | Operator::I64TruncF32S
        | Operator::I64TruncF32U
        | Operator::I64TruncF64S
        | Operator::I64TruncF64U
        | Operator::F32ConvertI32S
        | Operator::F32ConvertI32U
        | Operator::F32ConvertI64S
        | Operator::F32ConvertI64U
        | Operator::F64ConvertI32S
        | Operator::F64ConvertI32U
        | Operator::F64ConvertI64S
        | Operator::F64ConvertI64U
        | Operator::F32DemoteF64
        | Operator::F64PromoteF32
        | Operator::I32ReinterpretF32
        | Operator::I64ReinterpretF64
        | Operator::F32ReinterpretI32
        | Operator::F64ReinterpretI64 => WasmInstr::Unknown(format!("float:{:?}", op)),

        // Reference-type operations (not allowed in Soroban wasm32v1-none)
        Operator::RefNull { .. }
        | Operator::RefIsNull
        | Operator::TableGet { .. }
        | Operator::TableSet { .. } => WasmInstr::Unknown(format!("ref:{:?}", op)),

        // Catch-all
        other => WasmInstr::Unknown(format!("{:?}", other)),
    }
}
