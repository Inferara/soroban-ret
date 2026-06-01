//! TEMPORARY diagnostic — dumps optimized IR for chosen functions.
use soroban_ret::{decompile_to_ir, ir::ContractFn};

#[test]
fn dump_ir() {
    let fixture = std::env::var("DBG_FIXTURE").unwrap_or_else(|_| "test_bls".into());
    let only = std::env::var("DBG_FN").unwrap_or_default();
    let path = format!(
        "{}/../../tests/fixtures/{fixture}.wasm",
        env!("CARGO_MANIFEST_DIR")
    );
    let wasm = std::fs::read(&path).unwrap();
    let ir = decompile_to_ir(&wasm).unwrap();
    for f in &ir.contract_module.functions {
        let ContractFn { name, body, .. } = f;
        if only.is_empty() || name == &only {
            eprintln!("=== {name} ({} stmts) ===", body.len());
            eprintln!("{body:#?}");
        }
    }
}
