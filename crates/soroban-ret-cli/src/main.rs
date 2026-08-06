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

    /// Emit per-contract recovery signals as JSON to stdout and exit: how many
    /// exported functions were fully recovered, which ones lost their logic,
    /// and how many unresolved `todo!()` holes remain. Intended for UIs that
    /// display decompiled source and need an honest, per-contract confidence
    /// signal — the project's corpus-wide accuracy figures do not transfer to
    /// an individual contract.
    ///
    /// Incompatible with --spec-only, which skips body lifting: there would be
    /// no recovery to measure, and the counts would be pure noise.
    #[arg(long, conflicts_with_all = ["info", "spec_only"])]
    report: bool,

    /// Force generic WASM decompilation mode (no Soroban assumptions).
    /// Incompatible with --info (which always runs in Auto mode).
    #[arg(long, conflicts_with = "info")]
    generic: bool,

    /// Enable verbose logging
    #[arg(short, long)]
    verbose: bool,
}

/// Render the per-contract recovery signals as a JSON document.
///
/// Deliberately reports **counts**, not a single "recovered %". The project's
/// published aggregates (corpus mean restoration, corpus behavioral-match rate)
/// are corpus metrics and say nothing about any individual contract; a
/// per-contract percentage derived from them would overstate. Counts of
/// functions and holes are checkable against the source next to them.
fn render_report(wasm: &[u8], result: &soroban_ret::DecompileResult) -> Option<String> {
    // `None` under `--spec-only`, which clap already rejects for `--report`;
    // handled rather than unwrapped so a future flag combination cannot turn an
    // un-measurable report into a confident-looking one.
    let r = result.recovery.as_ref()?;

    let diagnostics: Vec<_> = result
        .validation
        .diagnostics
        .iter()
        .map(|d| {
            serde_json::json!({
                "severity": match d.severity {
                    soroban_ret::DiagnosticSeverity::Warning => "warning",
                    soroban_ret::DiagnosticSeverity::Info => "info",
                    _ => "unknown",
                },
                "category": d.category.to_string(),
                "message": d.message,
                "function_index": d.function_index,
            })
        })
        .collect();

    let functions: Vec<_> = r
        .functions
        .iter()
        .map(|f| {
            serde_json::json!({
                "name": f.name,
                "status": f.status.label(),
                "fully_recovered": f.status.is_fully_recovered(),
                "logic_lost": f.status.is_lost(),
                "unknown_nodes": f.unknown_nodes,
                "total_nodes": f.total_nodes,
                "missing_host_calls": f.missing_host_calls,
            })
        })
        .collect();

    let doc = serde_json::json!({
        "soroban_ret_version": soroban_ret::VERSION,
        "wasm_size": wasm.len(),
        "sdk_version": result.sdk_version,
        "standard_interfaces": result.standard_interfaces,
        "soroban_compliant": result.validation.is_soroban_compliant(),
        "diagnostics": diagnostics,
        "summary": r.summary(),
        "functions_total": r.spec_functions(),
        "functions_fully_recovered": r.fully_recovered(),
        "functions_partial": r.partial(),
        "functions_logic_lost": r.lost(),
        "holes": {
            "total": r.artifacts.total,
            "unknown_value": r.artifacts.unknown_value,
            "host_call": r.artifacts.host_call,
            "stub": r.artifacts.stub,
            "var_n": r.artifacts.var_n,
        },
        "functions": functions,
        "notice": "Experimental reconstruction. Signatures and types come from the \
                   contract's own contractspecv0 metadata; function bodies are inferred \
                   from bytecode and may be incomplete. These counts measure completeness, \
                   not correctness.",
    });

    Some(format!(
        "{}\n",
        serde_json::to_string_pretty(&doc).unwrap_or_default()
    ))
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

    if cli.report {
        match soroban_ret::decompile_with_options(&wasm, &options) {
            Ok(result) => match render_report(&wasm, &result) {
                Some(json) => print!("{json}"),
                None => {
                    eprintln!(
                        "Error: no recovery report available for this decompilation \
                         (function bodies were not lifted)."
                    );
                    std::process::exit(1);
                }
            },
            Err(e) => {
                eprintln!("Decompilation error: {e}");
                std::process::exit(1);
            }
        }
        return;
    }

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
