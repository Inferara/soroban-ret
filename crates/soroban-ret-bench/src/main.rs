//! `bench` — run the reference-free restoration benchmark over a WASM corpus.
//!
//! Examples:
//!   bench                                  # table to stdout for the default corpus
//!   bench --html report.html --json out.json
//!   bench --against benchmark-data/baseline.json --markdown
//!   bench --update-baseline                # refresh benchmark-data/baseline.json

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::Parser;
use soroban_ret_bench::{diff, markdown, metrics, report_html};

#[derive(Parser)]
#[command(
    name = "bench",
    about = "Reference-free restoration benchmark for the soroban-ret decompiler"
)]
struct Cli {
    /// Corpus directory of `.wasm` files (an adjacent `manifest.json` is used for labels).
    #[arg(long, default_value = "benchmark-data/mainnet")]
    corpus: PathBuf,
    /// Write the full JSON report to this path.
    #[arg(long)]
    json: Option<PathBuf>,
    /// Write the self-contained HTML report to this path.
    #[arg(long)]
    html: Option<PathBuf>,
    /// Diff against a committed baseline JSON; emits improved/reduced/no-change.
    #[arg(long)]
    against: Option<PathBuf>,
    /// Print the Markdown summary table to stdout.
    #[arg(long)]
    markdown: bool,
    /// Verdict tolerance in percentage points.
    #[arg(long, default_value_t = 0.1, value_parser = parse_tolerance)]
    tolerance: f64,
    /// Write the trimmed baseline to `<corpus>/../baseline.json`.
    #[arg(long)]
    update_baseline: bool,
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    let report = match metrics::run(&cli.corpus) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: failed to read corpus {}: {e}", cli.corpus.display());
            return ExitCode::from(2);
        }
    };

    // Optional baseline diff (best-effort: a missing/garbled baseline warns, not fails).
    let diff_report = cli
        .against
        .as_ref()
        .and_then(|p| match std::fs::read_to_string(p) {
            Ok(text) => match serde_json::from_str::<metrics::Baseline>(&text) {
                Ok(b) => Some(diff::diff(&report, &b, cli.tolerance)),
                Err(e) => {
                    eprintln!("warning: could not parse baseline {}: {e}", p.display());
                    None
                }
            },
            Err(e) => {
                eprintln!("warning: could not read baseline {}: {e}", p.display());
                None
            }
        });

    if let Some(p) = &cli.json {
        let json = serde_json::to_string_pretty(&report).expect("serialize report");
        if let Err(e) = write_file(p, &(json + "\n")) {
            eprintln!("error: writing JSON {}: {e}", p.display());
            return ExitCode::from(2);
        }
        eprintln!("wrote {}", p.display());
    }

    if let Some(p) = &cli.html {
        let html = report_html::render(&report, diff_report.as_ref());
        if let Err(e) = write_file(p, &html) {
            eprintln!("error: writing HTML {}: {e}", p.display());
            return ExitCode::from(2);
        }
        eprintln!("wrote {}", p.display());
    }

    if cli.update_baseline {
        let baseline = metrics::Baseline::from(&report);
        let path = cli
            .corpus
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join("baseline.json");
        let json = serde_json::to_string_pretty(&baseline).expect("serialize baseline");
        if let Err(e) = write_file(&path, &(json + "\n")) {
            eprintln!("error: writing baseline {}: {e}", path.display());
            return ExitCode::from(2);
        }
        eprintln!("wrote baseline {}", path.display());
    }

    // Default to the Markdown table when no file output was requested.
    let show_md =
        cli.markdown || (cli.html.is_none() && cli.json.is_none() && !cli.update_baseline);
    if show_md {
        print!("{}", markdown::render(&report, diff_report.as_ref()));
    }

    ExitCode::SUCCESS
}

/// Tolerance must be a sane percentage-point value; a negative tolerance would
/// make `classify()` call nearly every delta improved/reduced.
fn parse_tolerance(s: &str) -> Result<f64, String> {
    let v: f64 = s.parse().map_err(|e| format!("{e}"))?;
    if !(0.0..=100.0).contains(&v) {
        return Err("must be between 0 and 100 percentage points".into());
    }
    Ok(v)
}

fn write_file(path: &Path, contents: &str) -> std::io::Result<()> {
    if let Some(dir) = path.parent()
        && !dir.as_os_str().is_empty()
    {
        std::fs::create_dir_all(dir)?;
    }
    std::fs::write(path, contents)
}
