//! Structurize: convert flat WASM instruction sequences into a structured tree.
//!
//! WASM has structured control flow (block/loop/if/else/end nest perfectly),
//! so this is a simple recursive descent parse of the flat instruction stream.

use crate::wasm::ir::{BlockType, WasmInstr};

/// A structured control flow node.
#[derive(Debug, Clone)]
pub enum StructuredBlock {
    /// A plain instruction (not control flow).
    Instruction(WasmInstr),
    /// A `block...end` construct.
    Block {
        block_type: BlockType,
        body: Vec<StructuredBlock>,
    },
    /// A `loop...end` construct.
    Loop {
        block_type: BlockType,
        body: Vec<StructuredBlock>,
    },
    /// An `if...else...end` construct.
    IfElse {
        block_type: BlockType,
        then_body: Vec<StructuredBlock>,
        else_body: Vec<StructuredBlock>,
    },
}

/// Maximum control-flow nesting depth handled by the recursive parser.
///
/// Real Rust SDK contracts nest at most a few dozen blocks; 1024 is several
/// orders of magnitude past anything legitimate. Adversarial WASM with deeper
/// nesting is truncated rather than allowed to overflow the stack.
const MAX_RECURSION_DEPTH: u32 = 1024;

/// Parse a flat instruction sequence into a structured tree.
pub fn structurize(instrs: &[WasmInstr]) -> Vec<StructuredBlock> {
    let mut cursor = 0;
    parse_sequence(instrs, &mut cursor, false, 0)
}

/// Skip past the matching `End` for a block we have already entered.
///
/// Used when recursion depth has been exhausted: we cannot keep building
/// nested `StructuredBlock` nodes, so we drop the current block's body
/// and advance the cursor past its terminator. `nest` starts at 1 because
/// the caller has already consumed the opening Block/Loop/If.
fn skip_to_matching_end(instrs: &[WasmInstr], cursor: &mut usize) {
    let mut nest: u32 = 1;
    while *cursor < instrs.len() && nest > 0 {
        match &instrs[*cursor] {
            WasmInstr::Block { .. } | WasmInstr::Loop { .. } | WasmInstr::If { .. } => {
                nest = nest.saturating_add(1);
            }
            WasmInstr::End => {
                nest -= 1;
                if nest == 0 {
                    *cursor += 1;
                    return;
                }
            }
            _ => {}
        }
        *cursor += 1;
    }
}

fn parse_sequence(
    instrs: &[WasmInstr],
    cursor: &mut usize,
    in_block: bool,
    depth: u32,
) -> Vec<StructuredBlock> {
    let mut result = Vec::new();

    while *cursor < instrs.len() {
        match &instrs[*cursor] {
            WasmInstr::Block { block_type } => {
                let block_type = block_type.clone();
                *cursor += 1;
                if depth >= MAX_RECURSION_DEPTH {
                    skip_to_matching_end(instrs, cursor);
                    result.push(StructuredBlock::Block {
                        block_type,
                        body: Vec::new(),
                    });
                    continue;
                }
                let body = parse_sequence(instrs, cursor, true, depth + 1);
                result.push(StructuredBlock::Block { block_type, body });
            }
            WasmInstr::Loop { block_type } => {
                let block_type = block_type.clone();
                *cursor += 1;
                if depth >= MAX_RECURSION_DEPTH {
                    skip_to_matching_end(instrs, cursor);
                    result.push(StructuredBlock::Loop {
                        block_type,
                        body: Vec::new(),
                    });
                    continue;
                }
                let body = parse_sequence(instrs, cursor, true, depth + 1);
                result.push(StructuredBlock::Loop { block_type, body });
            }
            WasmInstr::If { block_type } => {
                let block_type = block_type.clone();
                *cursor += 1;
                if depth >= MAX_RECURSION_DEPTH {
                    skip_to_matching_end(instrs, cursor);
                    result.push(StructuredBlock::IfElse {
                        block_type,
                        then_body: Vec::new(),
                        else_body: Vec::new(),
                    });
                    continue;
                }
                let then_body = parse_sequence(instrs, cursor, true, depth + 1);

                let else_body =
                    if *cursor < instrs.len() && matches!(instrs[*cursor], WasmInstr::Else) {
                        *cursor += 1;
                        parse_sequence(instrs, cursor, true, depth + 1)
                    } else {
                        Vec::new()
                    };

                result.push(StructuredBlock::IfElse {
                    block_type,
                    then_body,
                    else_body,
                });
            }
            WasmInstr::Else => {
                // Don't advance cursor; caller handles Else.
                return result;
            }
            WasmInstr::End => {
                if in_block {
                    *cursor += 1;
                }
                return result;
            }
            other => {
                result.push(StructuredBlock::Instruction(other.clone()));
                *cursor += 1;
            }
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm::ir::{BlockType, WasmInstr};

    #[test]
    fn test_structurize_simple_block() {
        let instrs = vec![
            WasmInstr::Block {
                block_type: BlockType::Empty,
            },
            WasmInstr::I32Const(42),
            WasmInstr::End,
        ];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1);
        match &result[0] {
            StructuredBlock::Block { body, .. } => {
                assert_eq!(body.len(), 1);
                match &body[0] {
                    StructuredBlock::Instruction(WasmInstr::I32Const(42)) => {}
                    other => panic!("expected I32Const(42), got {:?}", other),
                }
            }
            other => panic!("expected Block, got {:?}", other),
        }
    }

    #[test]
    fn test_structurize_if_else() {
        let instrs = vec![
            WasmInstr::If {
                block_type: BlockType::Empty,
            },
            WasmInstr::I32Const(1),
            WasmInstr::Else,
            WasmInstr::I32Const(2),
            WasmInstr::End,
        ];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1);
        match &result[0] {
            StructuredBlock::IfElse {
                then_body,
                else_body,
                ..
            } => {
                assert_eq!(then_body.len(), 1);
                assert_eq!(else_body.len(), 1);
            }
            other => panic!("expected IfElse, got {:?}", other),
        }
    }

    #[test]
    fn test_structurize_nested_blocks() {
        let instrs = vec![
            WasmInstr::Block {
                block_type: BlockType::Empty,
            },
            WasmInstr::Block {
                block_type: BlockType::Empty,
            },
            WasmInstr::I32Const(1),
            WasmInstr::End,
            WasmInstr::End,
        ];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1);
        match &result[0] {
            StructuredBlock::Block { body, .. } => {
                assert_eq!(body.len(), 1);
                match &body[0] {
                    StructuredBlock::Block { body: inner, .. } => {
                        assert_eq!(inner.len(), 1);
                    }
                    other => panic!("expected inner Block, got {:?}", other),
                }
            }
            other => panic!("expected Block, got {:?}", other),
        }
    }

    #[test]
    fn test_structurize_loop() {
        let instrs = vec![
            WasmInstr::Loop {
                block_type: BlockType::Empty,
            },
            WasmInstr::BrIf(0),
            WasmInstr::End,
        ];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1);
        match &result[0] {
            StructuredBlock::Loop { body, .. } => {
                assert_eq!(body.len(), 1);
            }
            other => panic!("expected Loop, got {:?}", other),
        }
    }

    #[test]
    fn test_structurize_if_without_else() {
        let instrs = vec![
            WasmInstr::If {
                block_type: BlockType::Empty,
            },
            WasmInstr::I32Const(1),
            WasmInstr::End,
        ];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1);
        match &result[0] {
            StructuredBlock::IfElse {
                then_body,
                else_body,
                ..
            } => {
                assert_eq!(then_body.len(), 1);
                assert_eq!(else_body.len(), 0);
            }
            other => panic!("expected IfElse, got {:?}", other),
        }
    }

    #[test]
    fn test_structurize_empty_input() {
        let instrs = vec![];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 0);
    }

    #[test]
    fn test_structurize_does_not_stack_overflow_on_deep_nesting() {
        // Synthesise a WASM block-nest 4x deeper than the recursion limit. The
        // parser must finish without overflowing the thread stack.
        let depth = (MAX_RECURSION_DEPTH as usize) * 4;
        let mut instrs = Vec::with_capacity(depth * 2);
        for _ in 0..depth {
            instrs.push(WasmInstr::Block {
                block_type: BlockType::Empty,
            });
        }
        for _ in 0..depth {
            instrs.push(WasmInstr::End);
        }
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1, "single outermost block at top level");
    }

    #[test]
    fn test_structurize_eof_inside_unclosed_block_does_not_panic() {
        // Malformed: Block opened with no matching End. Parser should consume
        // available body without panicking.
        let instrs = vec![
            WasmInstr::Block {
                block_type: BlockType::Empty,
            },
            WasmInstr::I32Const(1),
            WasmInstr::I32Const(2),
            // (no End)
        ];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1);
        match &result[0] {
            StructuredBlock::Block { body, .. } => {
                assert_eq!(body.len(), 2);
            }
            other => panic!("expected Block, got {:?}", other),
        }
    }

    #[test]
    fn test_structurize_eof_inside_unclosed_if_does_not_panic() {
        // Malformed: If opened with no matching End or Else.
        let instrs = vec![
            WasmInstr::If {
                block_type: BlockType::Empty,
            },
            WasmInstr::I32Const(7),
            // (no End, no Else)
        ];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1);
        match &result[0] {
            StructuredBlock::IfElse {
                then_body,
                else_body,
                ..
            } => {
                assert_eq!(then_body.len(), 1);
                assert!(else_body.is_empty());
            }
            other => panic!("expected IfElse, got {:?}", other),
        }
    }

    #[test]
    fn test_structurize_top_level_else_truncates_sequence() {
        // Malformed: Else at top level. Parser returns immediately at the Else,
        // preserving any prefix instructions and discarding the rest.
        let instrs = vec![
            WasmInstr::I32Const(1),
            WasmInstr::Else,
            WasmInstr::I32Const(2),
        ];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1);
        match &result[0] {
            StructuredBlock::Instruction(WasmInstr::I32Const(1)) => {}
            other => panic!("expected only the prefix I32Const(1), got {:?}", other),
        }
    }

    #[test]
    fn test_structurize_top_level_end_truncates_sequence() {
        // Malformed: End at top level. Parser returns without advancing cursor;
        // the End and any tail instructions are dropped.
        let instrs = vec![
            WasmInstr::I32Const(1),
            WasmInstr::End,
            WasmInstr::I32Const(2),
        ];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1);
        match &result[0] {
            StructuredBlock::Instruction(WasmInstr::I32Const(1)) => {}
            other => panic!("expected only the prefix I32Const(1), got {:?}", other),
        }
    }

    #[test]
    fn test_skip_to_matching_end_handles_nested_blocks() {
        // Drive skip_to_matching_end through MAX_RECURSION_DEPTH+1 nesting so
        // that the recursion limit triggers; each nested Block must be skipped
        // past its End, leaving cursor positioned past the outermost End.
        let extra = 5_usize;
        let depth = MAX_RECURSION_DEPTH as usize + extra;
        let mut instrs = Vec::with_capacity(depth * 2);
        for _ in 0..depth {
            instrs.push(WasmInstr::Block {
                block_type: BlockType::Empty,
            });
        }
        for _ in 0..depth {
            instrs.push(WasmInstr::End);
        }
        let result = structurize(&instrs);
        // The outermost wrapper is preserved; inner depth-exhausted blocks
        // appear as empty-bodied Block nodes.
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_structurize_br_table_in_nested_blocks() {
        let instrs = vec![
            WasmInstr::Block {
                block_type: BlockType::Empty,
            },
            WasmInstr::Block {
                block_type: BlockType::Empty,
            },
            WasmInstr::Block {
                block_type: BlockType::Empty,
            },
            WasmInstr::I32Const(0),
            WasmInstr::BrTable {
                targets: vec![0, 1, 2],
                default: 2,
            },
            WasmInstr::End,
            WasmInstr::I32Const(10),
            WasmInstr::End,
            WasmInstr::I32Const(20),
            WasmInstr::End,
        ];
        let result = structurize(&instrs);
        assert_eq!(result.len(), 1);
        match &result[0] {
            StructuredBlock::Block { body, .. } => {
                // body should have: inner Block, then I32Const(20)
                assert_eq!(body.len(), 2);
            }
            other => panic!("expected Block, got {:?}", other),
        }
    }
}
