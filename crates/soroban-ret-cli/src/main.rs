use clap::Parser;
use std::fs;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "soroban-ret")]
#[command(about = "Stellar Soroban Smart Contracts Reverse Engineering Tool")]
#[command(version)]
struct Cli {
    /// Path to the input WASM file
    input: PathBuf,

    /// Path to write the output Rust file (defaults to stdout)
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Only output type definitions and function signatures (no bodies).
    /// Incompatible with --info (which short-circuits before this would apply).
    #[arg(long, conflicts_with = "info")]
    spec_only: bool,

    /// Pre-optimize WASM with wasm-opt (binaryen) before decompiling.
    /// Requires `wasm-opt` to be installed.
    #[arg(long, short = 'O')]
    pre_optimize: bool,

    /// Print contract metadata (SDK version, functions, types) and exit
    #[arg(long)]
    info: bool,

    /// Force generic WASM decompilation mode (no Soroban assumptions).
    /// Incompatible with --info (which always runs in Auto mode).
    #[arg(long, conflicts_with = "info")]
    generic: bool,

    /// Enable verbose logging
    #[arg(short, long)]
    verbose: bool,
}

fn main() {
    let cli = Cli::parse();

    if cli.verbose {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("debug")).init();
    } else {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("warn")).init();
    }

    let wasm = match fs::read(&cli.input) {
        Ok(bytes) => bytes,
        Err(e) => {
            eprintln!("Error reading {}: {}", cli.input.display(), e);
            std::process::exit(1);
        }
    };

    if cli.info {
        match soroban_ret::decompile_to_ir(&wasm) {
            Ok(ir) => {
                eprintln!("Contract Info:");
                eprintln!("  WASM size:   {} bytes", wasm.len());
                eprintln!(
                    "  SDK version: {}",
                    ir.sdk_version.as_deref().unwrap_or("unknown")
                );
                eprintln!("  Functions:   {}", ir.contract_module.functions.len());
                eprintln!("  Types:       {}", ir.contract_module.types.len());
                eprintln!("  Error enums: {}", ir.contract_module.error_enums.len());
                eprintln!("  Events:      {}", ir.contract_module.events.len());
                if ir.contract_module.has_constructor {
                    eprintln!("  Constructor: yes");
                }
                if !ir.standard_interfaces.is_empty() {
                    eprintln!("  Interfaces:  {}", ir.standard_interfaces.join(", "));
                }
                if !ir.validation.diagnostics.is_empty() {
                    for diag in &ir.validation.diagnostics {
                        eprintln!("  Diagnostic:  {diag}");
                    }
                }
                eprintln!();
                let fmt_type = |spec| {
                    soroban_ret::codegen::types::generate_type_ident(spec)
                        .to_string()
                        .replace(" < ", "<")
                        .replace(" > ", ">")
                        .replace(" >", ">")
                        .replace("< ", "<")
                        .replace(" ,", ",")
                };
                for func in &ir.contract_module.functions {
                    let env = if func.takes_env { "env: Env, " } else { "" };
                    let params: Vec<String> = func
                        .params
                        .iter()
                        .map(|p| format!("{}: {}", p.name, fmt_type(&p.type_def)))
                        .collect();
                    let ret = func
                        .return_type
                        .as_ref()
                        .map(|rt| format!(" -> {}", fmt_type(rt)))
                        .unwrap_or_default();
                    eprintln!("  fn {}({}{}){}", func.name, env, params.join(", "), ret);
                }
                return;
            }
            Err(e) => {
                eprintln!("Error: {e}");
                std::process::exit(1);
            }
        }
    }

    let mode = if cli.generic {
        soroban_ret::DecompileMode::Generic
    } else {
        soroban_ret::DecompileMode::Auto
    };

    let mut options = soroban_ret::DecompileOptions::default();
    options.spec_only = cli.spec_only;
    options.pre_optimize = cli.pre_optimize;
    options.mode = mode;

    match soroban_ret::decompile_with_options(&wasm, &options) {
        Ok(result) => {
            if !result.validation.diagnostics.is_empty() {
                let has_warnings = !result.validation.is_soroban_compliant();
                if has_warnings {
                    eprintln!("Soroban compliance warnings:");
                }
                for diag in &result.validation.diagnostics {
                    if has_warnings || diag.severity == soroban_ret::DiagnosticSeverity::Info {
                        eprintln!("  {diag}");
                    }
                }
                eprintln!();
            }

            if let Some(output_path) = cli.output {
                if let Err(e) = fs::write(&output_path, &result.source) {
                    eprintln!("Error writing {}: {}", output_path.display(), e);
                    std::process::exit(1);
                }
                eprintln!("Decompiled to {}", output_path.display());
            } else {
                print!("{}", result.source);
            }
        }
        Err(e) => {
            eprintln!("Decompilation error: {e}");
            std::process::exit(1);
        }
    }
}
