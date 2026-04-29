#[test]
fn parses_test_empty_wasm() {
    let wasm = include_bytes!("../../../tests/fixtures/test_empty.wasm");
    let module = soroban_ret::WasmModule::parse(wasm).expect("parse");
    assert!(!module.functions.is_empty(), "expect at least one function");
    // contractspecv0 / contractmetav0 should be present on a Soroban-built wasm
    assert!(
        module.custom_sections.contains_key("contractspecv0"),
        "expect contractspecv0 custom section"
    );
}

#[test]
fn extracts_spec_from_test_empty() {
    let wasm = include_bytes!("../../../tests/fixtures/test_empty.wasm");
    let _ = soroban_ret::TypeRegistry::from_wasm(wasm).expect("spec");
}
