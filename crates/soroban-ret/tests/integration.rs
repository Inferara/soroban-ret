/// Integration tests for the soroban-ret pipeline.
///
/// Smoke tests that the full decompilation pipeline produces correct output
/// for the 18 deliverable fixtures (Levels 1-4): simple arithmetic, basic
/// storage, custom types, events, auth, and cross-contract calls.
use soroban_ret::{DecompileOptions, decompile, decompile_with_options};

// -------------------------------------------------------------------------
// Level 1: simple arithmetic + empty contracts
// -------------------------------------------------------------------------

#[test]
fn test_decompile_empty() {
    let wasm = include_bytes!("../../../tests/fixtures/test_empty.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("#![no_std]"), "missing no_std");
    assert!(source.contains("#[contract]"), "missing contract attr");
}

#[test]
fn test_decompile_empty2() {
    let wasm = include_bytes!("../../../tests/fixtures/test_empty2.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("#![no_std]"), "missing no_std");
    assert!(source.contains("#[contract]"), "missing contract attr");
}

#[test]
fn test_decompile_zero() {
    let wasm = include_bytes!("../../../tests/fixtures/test_zero.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("#![no_std]"), "missing no_std");
    assert!(source.contains("#[contract]"), "missing contract attr");
}

#[test]
fn test_decompile_add_u64() {
    let wasm = include_bytes!("../../../tests/fixtures/test_add_u64.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("#[contractimpl]"), "missing contractimpl");
    assert!(source.contains("pub fn add"), "missing add function");
    assert!(source.contains("a: u64"), "missing param a");
    assert!(source.contains("b: u64"), "missing param b");
    assert!(source.contains("-> u64"), "missing return type");
    assert!(source.contains("a + b"), "missing add expression");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_add_u128() {
    let wasm = include_bytes!("../../../tests/fixtures/test_add_u128.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn add"), "missing add function");
    assert!(source.contains("u128"), "missing u128 type");
    assert!(source.contains("a + b"), "missing add expression");
}

#[test]
fn test_decompile_add_i128() {
    let wasm = include_bytes!("../../../tests/fixtures/test_add_i128.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn add"), "missing add function");
    assert!(source.contains("i128"), "missing i128 type");
    assert!(source.contains("a + b"), "missing add expression");
}

#[test]
fn test_decompile_tuples() {
    let wasm = include_bytes!("../../../tests/fixtures/test_tuples.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn tuple1"), "missing tuple1 function");
    assert!(source.contains("pub fn tuple2"), "missing tuple2 function");
    assert!(
        source.contains("(u32, i64)"),
        "missing 2-element tuple type"
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

// -------------------------------------------------------------------------
// Level 2: basic storage, mutability, logging, generics
// -------------------------------------------------------------------------

#[test]
fn test_decompile_contract_data() {
    let wasm = include_bytes!("../../../tests/fixtures/test_contract_data.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn put"), "missing put function");
    assert!(source.contains("pub fn get"), "missing get function");
    assert!(source.contains("pub fn del"), "missing del function");
    assert!(source.contains("storage()"), "missing storage access");
    assert!(
        source.contains("persistent()"),
        "missing persistent storage"
    );
    assert!(source.contains(".set("), "missing set call");
    assert!(source.contains(".get("), "missing get call");
    assert!(source.contains(".remove("), "missing remove call");
    assert!(source.contains("key"), "missing key param reference");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_mutability() {
    let wasm = include_bytes!("../../../tests/fixtures/test_mutability.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn calc"), "missing calc function");
    assert!(source.contains("-> u32"), "missing return type");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_logging() {
    let wasm = include_bytes!("../../../tests/fixtures/test_logging.wasm");
    // Logging contract should at least decompile cleanly. The log! macro is
    // stripped at compile time so body recovery is best-effort.
    decompile(wasm).expect("decompilation failed");
}

#[test]
fn test_decompile_generics() {
    let wasm = include_bytes!("../../../tests/fixtures/test_generics.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn exec"), "missing exec function");
    assert!(source.contains("-> u32"), "missing return type");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

// -------------------------------------------------------------------------
// Level 3: custom types, errors, events, constructor
// -------------------------------------------------------------------------

#[test]
fn test_decompile_udt() {
    let wasm = include_bytes!("../../../tests/fixtures/test_udt.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub struct UdtTuple"), "missing UdtTuple");
    assert!(source.contains("pub struct UdtStruct"), "missing UdtStruct");
    assert!(source.contains("pub enum UdtEnum"), "missing UdtEnum");
    assert!(source.contains("pub enum UdtEnum2"), "missing UdtEnum2");
    assert!(source.contains("contracttype"), "missing contracttype");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_errors() {
    let wasm = include_bytes!("../../../tests/fixtures/test_errors.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub enum Flag"), "missing Flag enum");
    assert!(source.contains("pub enum Error"), "missing Error enum");
    assert!(source.contains("AnError = 1"), "missing error variant");
    assert!(source.contains("contracttype"), "missing contracttype");
    assert!(source.contains("contracterror"), "missing contracterror");
    assert!(source.contains("persisted"), "symbol not decoded");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_events() {
    let wasm = include_bytes!("../../../tests/fixtures/test_events.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(
        source.contains("pub struct Transfer"),
        "missing Transfer event"
    );
    assert!(
        source.contains("contractevent"),
        "missing contractevent attr"
    );
    assert!(source.contains("#[topic]"), "missing topic attr");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_constructor() {
    let wasm = include_bytes!("../../../tests/fixtures/test_constructor.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("__constructor"), "missing constructor");
    assert!(source.contains("pub enum DataKey"), "missing DataKey type");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

// -------------------------------------------------------------------------
// Level 4: auth, account check-auth, cross-contract calls
// -------------------------------------------------------------------------

#[test]
fn test_decompile_auth() {
    let wasm = include_bytes!("../../../tests/fixtures/test_auth.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("require_auth"), "missing require_auth");
    assert!(source.contains("pub fn fn1"), "missing fn1");
    assert!(source.contains("pub fn fn2"), "missing fn2");
    assert!(source.contains("a.require_auth()"), "auth target wrong");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_account() {
    let wasm = include_bytes!("../../../tests/fixtures/test_account.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(
        source.contains("__check_auth"),
        "missing __check_auth function"
    );
    assert!(
        source.contains("auth::Context"),
        "missing auth::Context import"
    );
    assert!(
        source.contains("Vec<Context>"),
        "missing Vec<Context> parameter"
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_invoke_contract() {
    let wasm = include_bytes!("../../../tests/fixtures/test_invoke_contract.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(
        source.contains("invoke_contract"),
        "missing invoke_contract call"
    );
    assert!(
        source.contains("pub fn add_with"),
        "missing add_with function"
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

// -------------------------------------------------------------------------
// Option / api surface
// -------------------------------------------------------------------------

#[test]
fn test_decompile_spec_only() {
    let wasm = include_bytes!("../../../tests/fixtures/test_contract_data.wasm");
    let mut options = DecompileOptions::default();
    options.spec_only = true;
    let result = decompile_with_options(wasm, &options).expect("decompilation failed");
    assert!(
        result.source.contains("todo!"),
        "spec-only should have todo! in body"
    );
}

// -------------------------------------------------------------------------
// Smoke tests covering all 18 deliverable fixtures
// -------------------------------------------------------------------------

const ALL_FIXTURES: &[(&str, &[u8])] = &[
    (
        "test_empty",
        include_bytes!("../../../tests/fixtures/test_empty.wasm"),
    ),
    (
        "test_empty2",
        include_bytes!("../../../tests/fixtures/test_empty2.wasm"),
    ),
    (
        "test_zero",
        include_bytes!("../../../tests/fixtures/test_zero.wasm"),
    ),
    (
        "test_add_u64",
        include_bytes!("../../../tests/fixtures/test_add_u64.wasm"),
    ),
    (
        "test_add_u128",
        include_bytes!("../../../tests/fixtures/test_add_u128.wasm"),
    ),
    (
        "test_add_i128",
        include_bytes!("../../../tests/fixtures/test_add_i128.wasm"),
    ),
    (
        "test_tuples",
        include_bytes!("../../../tests/fixtures/test_tuples.wasm"),
    ),
    (
        "test_contract_data",
        include_bytes!("../../../tests/fixtures/test_contract_data.wasm"),
    ),
    (
        "test_mutability",
        include_bytes!("../../../tests/fixtures/test_mutability.wasm"),
    ),
    (
        "test_logging",
        include_bytes!("../../../tests/fixtures/test_logging.wasm"),
    ),
    (
        "test_generics",
        include_bytes!("../../../tests/fixtures/test_generics.wasm"),
    ),
    (
        "test_udt",
        include_bytes!("../../../tests/fixtures/test_udt.wasm"),
    ),
    (
        "test_errors",
        include_bytes!("../../../tests/fixtures/test_errors.wasm"),
    ),
    (
        "test_events",
        include_bytes!("../../../tests/fixtures/test_events.wasm"),
    ),
    (
        "test_constructor",
        include_bytes!("../../../tests/fixtures/test_constructor.wasm"),
    ),
    (
        "test_auth",
        include_bytes!("../../../tests/fixtures/test_auth.wasm"),
    ),
    (
        "test_account",
        include_bytes!("../../../tests/fixtures/test_account.wasm"),
    ),
    (
        "test_invoke_contract",
        include_bytes!("../../../tests/fixtures/test_invoke_contract.wasm"),
    ),
];

#[test]
fn test_all_fixtures_decompile() {
    for (name, wasm) in ALL_FIXTURES {
        let result = decompile(wasm);
        assert!(result.is_ok(), "{name} failed: {:?}", result.err());
    }
}

#[test]
fn test_all_fixtures_no_artifacts() {
    for (name, wasm) in ALL_FIXTURES {
        let source = decompile(wasm).unwrap_or_else(|e| panic!("{name} failed: {e}"));
        assert!(
            !source.contains("todo!(\"unknown value\")"),
            "{name} has todo!(\"unknown value\") artifact"
        );
        assert!(
            !source.contains("todo!(\"host call"),
            "{name} has unresolved host call artifact"
        );
        // Check for unresolved var_N temporary names
        for word in source.split(|c: char| !c.is_alphanumeric() && c != '_') {
            assert!(
                !(word.starts_with("var_")
                    && word.len() > 4
                    && word[4..].chars().all(|c| c.is_ascii_digit())),
                "{name} has unresolved variable '{word}'"
            );
        }
    }
}
