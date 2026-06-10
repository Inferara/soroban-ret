//! Dump a WASM binary as WAT for bytecode-level analysis.
//! Usage: `cargo run -p soroban-ret --features wasmprinter --example dumpwat -- <wasm>`

#[cfg(feature = "wasmprinter")]
fn main() {
    let path = std::env::args().nth(1).expect("usage: dumpwat <wasm>");
    let wasm = std::fs::read(&path).unwrap();
    println!("{}", soroban_ret::wasm_to_wat(&wasm).unwrap());
}

#[cfg(not(feature = "wasmprinter"))]
fn main() {
    eprintln!("dumpwat requires the `wasmprinter` feature: cargo run --features wasmprinter --example dumpwat -- <wasm>");
    std::process::exit(1);
}
