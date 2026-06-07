//! Compact Markdown table + verdict — for stdout, `$GITHUB_STEP_SUMMARY`, and
//! the sticky PR comment. No per-contract detail (that lives in the HTML report).

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::diff::DiffReport;
use crate::metrics::BenchReport;

/// Marker line so the CI step can find/replace its sticky PR comment.
pub const STICKY_MARKER: &str = "<!-- soroban-ret-bench -->";

/// Render the report (optionally with a baseline diff) as GitHub-flavoured
/// Markdown.
pub fn render(report: &BenchReport, diff: Option<&DiffReport>) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "{STICKY_MARKER}");
    let _ = writeln!(out, "## 🛰️ Restoration benchmark");
    let _ = writeln!(out);

    match diff {
        Some(d) => {
            let _ = writeln!(
                out,
                "**Overall: {:.1}%** {} {:+.1} vs baseline ({:.1}%) — {} contracts",
                report.overall_restoration,
                d.overall_verdict.arrow(),
                d.overall_delta,
                d.overall_baseline,
                report.contracts.len(),
            );
            let _ = writeln!(out);
            let _ = writeln!(
                out,
                "Verdict: **{} improved, {} reduced, {} no change** (tolerance ±{:.1} pp).",
                d.improved, d.reduced, d.no_change, d.tolerance,
            );
        }
        None => {
            let _ = writeln!(
                out,
                "**Overall: {:.1}%** — {} contracts (no baseline to compare).",
                report.overall_restoration,
                report.contracts.len(),
            );
        }
    }
    let _ = writeln!(out);

    // Per-file delta lookup for the Δ column.
    let deltas: BTreeMap<&str, &crate::diff::ContractDelta> = diff
        .map(|d| d.deltas.iter().map(|x| (x.file.as_str(), x)).collect())
        .unwrap_or_default();

    if diff.is_some() {
        let _ = writeln!(
            out,
            "| Contract | Restoration | Δ | Spec fns | Clean | Partial | Lost | Artifacts | Disasm (ms) |"
        );
        let _ = writeln!(out, "|---|---:|---:|---:|---:|---:|---:|---:|---:|");
    } else {
        let _ = writeln!(
            out,
            "| Contract | Restoration | Spec fns | Clean | Partial | Lost | Artifacts | Disasm (ms) |"
        );
        let _ = writeln!(out, "|---|---:|---:|---:|---:|---:|---:|---:|");
    }

    for c in &report.contracts {
        let label = c.entity.clone().unwrap_or_else(|| c.file.clone());
        let restoration = if c.error.is_some() {
            "error".to_string()
        } else {
            format!("{:.1}%", c.restoration_pct)
        };
        if diff.is_some() {
            let dcell = match deltas.get(c.file.as_str()) {
                Some(d) => format!("{} {:+.1}", d.verdict.arrow(), d.delta),
                None => "—".to_string(),
            };
            let _ = writeln!(
                out,
                "| {} | {} | {} | {} | {} | {} | {} | {} | {:.3} |",
                md_escape(&label),
                restoration,
                dcell,
                c.spec_functions,
                c.fn_clean,
                c.fn_partial,
                c.fn_logic_lost,
                c.artifacts.total,
                c.disasm_ms,
            );
        } else {
            let _ = writeln!(
                out,
                "| {} | {} | {} | {} | {} | {} | {} | {:.3} |",
                md_escape(&label),
                restoration,
                c.spec_functions,
                c.fn_clean,
                c.fn_partial,
                c.fn_logic_lost,
                c.artifacts.total,
                c.disasm_ms,
            );
        }
    }

    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "_Restoration % is a reference-free proxy: the mean per-exported-function \
         recovery (clean Rust vs. `todo!()`/unknown). Disassembly time is reported \
         but excluded from the verdict._"
    );
    out
}

fn md_escape(s: &str) -> String {
    s.replace('|', "\\|")
}
