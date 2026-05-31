//! CLI binary for measuring decompiler accuracy.
//!
//! Replaces `scripts/measure_accuracy.py` with a Rust implementation.
//!
//! Usage:
//!   cargo run -p soroban-ret-accuracy --bin accuracy
//!   cargo run -p soroban-ret-accuracy --bin accuracy -- --contract auth
//!   cargo run -p soroban-ret-accuracy --bin accuracy -- --json
//!   cargo run -p soroban-ret-accuracy --bin accuracy -- --detail auth

use clap::Parser;
use soroban_ret_accuracy::{
    report,
    test_harness::{discover_contracts, run_accuracy},
};
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "accuracy",
    about = "Measure soroban-ret accuracy against SDK test contracts",
    version
)]
struct Cli {
    /// Run for a single contract (e.g. 'auth', 'add_u64').
    #[arg(long)]
    contract: Option<String>,

    /// Output results as JSON.
    #[arg(long)]
    json: bool,

    /// Show per-function detail for a contract.
    #[arg(long)]
    detail: Option<String>,

    /// Exit with code 1 if overall average is below this threshold.
    #[arg(long)]
    min_overall: Option<f64>,

    /// Compare against a committed baseline JSON (from `--json`) and exit 1 if
    /// any contract regresses by more than `--tolerance` percentage points.
    #[arg(long)]
    against: Option<PathBuf>,

    /// Maximum allowed per-contract regression, in percentage points, when
    /// `--against` is used. Absorbs floating-point / snapshot noise.
    #[arg(long, default_value_t = 0.5)]
    tolerance: f64,

    /// Path to the fixtures directory (default: tests/fixtures).
    #[arg(long)]
    fixtures: Option<PathBuf>,

    /// Path to the SDK tests directory (default: the bundled
    /// `vendor/rs-soroban-sdk/tests` submodule, falling back to
    /// `~/GitHub/rs-soroban-sdk/tests`).
    #[arg(long)]
    sdk_tests: Option<PathBuf>,
}

fn main() {
    let cli = Cli::parse();

    // Resolve paths
    let project_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."));

    let fixtures_dir = cli
        .fixtures
        .unwrap_or_else(|| project_root.join("tests").join("fixtures"));
    let sdk_tests_dir = cli.sdk_tests.unwrap_or_else(|| {
        // Prefer the in-repo submodule pinned to the fixtures' SDK version;
        // fall back to a developer checkout under ~/GitHub.
        let vendored = project_root
            .join("vendor")
            .join("rs-soroban-sdk")
            .join("tests");
        if vendored.is_dir() {
            vendored
        } else {
            dirs::home_dir()
                .unwrap_or_else(|| PathBuf::from("~"))
                .join("GitHub")
                .join("rs-soroban-sdk")
                .join("tests")
        }
    });

    if !fixtures_dir.is_dir() {
        eprintln!(
            "ERROR: Fixtures directory not found: {}",
            fixtures_dir.display()
        );
        std::process::exit(2);
    }

    if !sdk_tests_dir.is_dir() {
        eprintln!(
            "WARNING: SDK tests directory not found: {}",
            sdk_tests_dir.display()
        );
        eprintln!("Some contracts may be skipped.");
    }

    // Discover contracts
    let contracts = discover_contracts(&fixtures_dir, &sdk_tests_dir);

    if let Some(ref name) = cli.contract
        && !contracts.iter().any(|c| c.name == *name)
    {
        eprintln!("ERROR: Contract '{}' not found", name);
        let names: Vec<_> = contracts.iter().map(|c| c.name.as_str()).collect();
        eprintln!("Available: {}", names.join(", "));
        std::process::exit(2);
    }

    // Run accuracy measurement
    let accuracy_report = run_accuracy(&contracts, cli.contract.as_deref());

    // Output
    if let Some(ref detail_name) = cli.detail {
        if let Some(detail) = report::render_detail(&accuracy_report, detail_name) {
            print!("{}", detail);
        } else {
            eprintln!("Contract '{}' not found in results", detail_name);
            std::process::exit(2);
        }
    } else if cli.json {
        println!("{}", report::render_json(&accuracy_report));
    } else {
        print!("{}", report::render_table(&accuracy_report));
    }

    // Regression gate against a committed baseline.
    if let Some(ref baseline_path) = cli.against
        && !regression_check(&accuracy_report, baseline_path, cli.tolerance)
    {
        std::process::exit(1);
    }

    // Threshold check
    if let Some(min) = cli.min_overall
        && accuracy_report.overall_score < min
    {
        std::process::exit(1);
    }
}

/// Compare the current report against a committed baseline. Prints a
/// `contract | baseline | current | delta` table and returns `false` if any
/// contract regresses by more than `tolerance` percentage points (or vanished
/// from the current run). New contracts are reported but never fail the gate.
fn regression_check(
    current: &soroban_ret_accuracy::metrics::AccuracyReport,
    baseline_path: &PathBuf,
    tolerance: f64,
) -> bool {
    let baseline: soroban_ret_accuracy::metrics::AccuracyReport =
        match std::fs::read_to_string(baseline_path) {
            Ok(s) => match serde_json::from_str(&s) {
                Ok(r) => r,
                Err(e) => {
                    eprintln!(
                        "ERROR: could not parse baseline {}: {e}",
                        baseline_path.display()
                    );
                    std::process::exit(2);
                }
            },
            Err(e) => {
                eprintln!(
                    "ERROR: could not read baseline {}: {e}",
                    baseline_path.display()
                );
                std::process::exit(2);
            }
        };

    let mut regressions: Vec<String> = Vec::new();
    println!("\nRegression vs {}", baseline_path.display());
    println!(
        "{:<34} {:>8} {:>8} {:>8}",
        "Contract", "Base", "Current", "Delta"
    );
    println!("{}", "-".repeat(62));
    for (name, base) in &baseline.contracts {
        match current.contracts.get(name) {
            Some(cur) => {
                let delta = cur.overall_score - base.overall_score;
                let flag = if delta < -tolerance {
                    "  <-- REGRESSED"
                } else {
                    ""
                };
                println!(
                    "{:<34} {:>8.1} {:>8.1} {:>+8.1}{}",
                    name, base.overall_score, cur.overall_score, delta, flag
                );
                if delta < -tolerance {
                    regressions.push(name.clone());
                }
            }
            None => {
                println!(
                    "{name:<34} {:>8.1} {:>8} {:>8}",
                    base.overall_score, "MISSING", ""
                );
                regressions.push(name.clone());
            }
        }
    }
    let overall_delta = current.overall_score - baseline.overall_score;
    println!("{}", "-".repeat(62));
    println!(
        "{:<34} {:>8.1} {:>8.1} {:>+8.1}",
        "OVERALL", baseline.overall_score, current.overall_score, overall_delta
    );

    if regressions.is_empty() {
        println!("\nOK: no contract regressed by more than {tolerance} pp (tolerance).");
        true
    } else {
        println!(
            "\nFAIL: {} contract(s) regressed by more than {tolerance} pp: {}",
            regressions.len(),
            regressions.join(", ")
        );
        false
    }
}
