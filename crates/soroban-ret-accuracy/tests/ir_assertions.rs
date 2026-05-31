//! Exercises the `ir_assertions` fluent DSL against real decompiled IR.
//!
//! Besides validating the decompiler's recovered IR (signatures, type kinds,
//! variant/field structure, body operations), this test is what keeps the
//! `ir_assertions` module live — it is otherwise unreferenced API surface.

use soroban_ret::decompile_to_ir;
use soroban_ret::ir::SorobanExpr;
use soroban_ret_accuracy::ir_assertions::ContractAssertions;

const ADD_U64: &[u8] = include_bytes!("../../../tests/fixtures/test_add_u64.wasm");
const ERRORS: &[u8] = include_bytes!("../../../tests/fixtures/test_errors.wasm");
const UDT: &[u8] = include_bytes!("../../../tests/fixtures/test_udt.wasm");

#[test]
fn add_u64_signatures_and_body() {
    let ir = decompile_to_ir(ADD_U64).expect("decompile add_u64");
    let c = ContractAssertions::new(&ir.contract_module, &ir.registry);

    c.assert_fn("add")
        .has_param("a", "u64")
        .has_param("b", "u64")
        .returns("u64")
        // `add` must actually compute an addition in its body.
        .body_contains_expr(|e| matches!(e, SorobanExpr::Add(..)));
}

#[test]
fn errors_types_and_signature() {
    let ir = decompile_to_ir(ERRORS).expect("decompile errors");
    let c = ContractAssertions::new(&ir.contract_module, &ir.registry);

    c.assert_type("Flag")
        .is_enum()
        .has_variant("A")
        .has_variant("E");
    c.assert_type("Error").is_enum().has_variant("AnError");
    c.assert_fn("hello").has_param("flag", "Flag");
}

#[test]
fn udt_type_structure() {
    let ir = decompile_to_ir(UDT).expect("decompile udt");
    let c = ContractAssertions::new(&ir.contract_module, &ir.registry);

    // Data-carrying union: UdtB(UdtStruct) must be recognized as a tuple variant.
    c.assert_type("UdtEnum")
        .is_union()
        .has_variant("UdtA")
        .has_variant("UdtB")
        .variant_has_data("UdtB");
    // Plain discriminant enum.
    c.assert_type("UdtEnum2")
        .is_enum()
        .has_variant("A")
        .has_variant("B");
    // Named-field struct.
    c.assert_type("UdtStruct")
        .is_struct()
        .has_field("a")
        .has_field("b")
        .has_field("c");
}
