use clap::Parser;
use std::{fs, path::PathBuf};

#[derive(Parser)]
#[command(name = "soroban-ret", version)]
struct Cli {
    input: PathBuf,
    #[arg(short, long)]
    output: Option<PathBuf>,
    #[arg(long)]
    spec_only: bool,
    #[arg(short, long)]
    verbose: bool,
}

fn main() {
    let cli = Cli::parse();
    env_logger::Builder::from_env(
        env_logger::Env::default().default_filter_or(if cli.verbose { "debug" } else { "warn" }),
    )
    .init();

    let wasm = fs::read(&cli.input).expect("read wasm");
    let module = soroban_ret::WasmModule::parse(&wasm).expect("parse wasm");
    let registry = soroban_ret::TypeRegistry::from_wasm(&wasm).expect("spec");

    // Stage 1+2 only: emit a structured summary until later stages land.
    eprintln!(
        "Functions: {}, Types: {}, Imports: {}",
        registry.functions.len(),
        registry.structs.len() + registry.unions.len() + registry.enums.len(),
        module.imports.functions.len()
    );

    let _ = (cli.output, cli.spec_only);
}
