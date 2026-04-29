use clap::Parser;
use std::{fs, path::PathBuf};

#[derive(Parser)]
#[command(name = "soroban-ret", version)]
struct Cli {
    input: PathBuf,
}

fn main() {
    let cli = Cli::parse();

    let wasm = fs::read(&cli.input).expect("read wasm");
    let module = soroban_ret::WasmModule::parse(&wasm).expect("parse wasm");
    let registry = soroban_ret::TypeRegistry::from_wasm(&wasm).expect("spec");

    eprintln!(
        "Functions: {}, Types: {}, Imports: {}",
        registry.functions.len(),
        registry.structs.len() + registry.unions.len() + registry.enums.len(),
        module.imports.functions.len()
    );
}
