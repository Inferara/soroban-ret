//! Multi-format accuracy report rendering.

use crate::metrics::AccuracyReport;
use std::fmt::Write;

/// Render the accuracy report as a terminal-friendly table.
pub fn render_table(report: &AccuracyReport) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "{}", "=".repeat(80));
    let _ = writeln!(out, "SOROBAN DECOMPILER ACCURACY REPORT");
    let _ = writeln!(out, "{}", "=".repeat(80));
    let _ = writeln!(out);

    let _ = writeln!(
        out,
        "{:<30} {:>5} {:>5} {:>5} {:>5} {:>5}  {:>7}  {:>3}",
        "Contract", "Types", "Sigs", "Annot", "Body", "Struc", "Overall", "Lvl"
    );
    let _ = writeln!(out, "{}", "-".repeat(80));

    for (name, r) in &report.contracts {
        let error_mark = if r.error.is_some() { " *" } else { "" };
        let _ = writeln!(
            out,
            "{:<30} {:>5.1} {:>5.1} {:>5.1} {:>5.1} {:>5.1}  {:>6.1}%  {:>3}{}",
            name,
            r.types_score,
            r.signatures_score,
            r.annotations_score,
            r.bodies_score,
            r.structure_score,
            r.overall_score,
            r.level,
            error_mark
        );
    }

    // Print errors
    let errors: Vec<_> = report
        .contracts
        .iter()
        .filter_map(|(n, r)| r.error.as_ref().map(|e| (n.clone(), e.clone())))
        .collect();
    if !errors.is_empty() {
        let _ = writeln!(out);
        let _ = writeln!(out, "* Decompilation errors:");
        for (name, err) in &errors {
            let _ = writeln!(out, "  {}: {}", name, err);
        }
    }

    // Level summaries
    let _ = writeln!(out);
    for (level, summary) in &report.levels {
        let status = if summary.meets_target {
            "OK"
        } else {
            "BELOW TARGET"
        };
        let _ = writeln!(
            out,
            "Level {} ({:<8}):  avg {:>5.1}%  (target >={}%)  [{}]",
            level, summary.name, summary.average, summary.target, status
        );
    }

    let _ = writeln!(out);
    let _ = writeln!(
        out,
        "OVERALL AVERAGE ACCURACY: {:.1}%",
        report.overall_score
    );
    let _ = writeln!(out, "{}", "=".repeat(80));

    out
}

/// Render the accuracy report as JSON.
pub fn render_json(report: &AccuracyReport) -> String {
    serde_json::to_string_pretty(report).unwrap_or_else(|e| format!("JSON error: {e}"))
}

/// Render a detailed per-function report for a single contract.
pub fn render_detail(report: &AccuracyReport, contract_name: &str) -> Option<String> {
    let contract = report.contracts.get(contract_name)?;
    let mut out = String::new();

    let _ = writeln!(
        out,
        "Contract: {} (Level {})",
        contract.name, contract.level
    );
    let _ = writeln!(out, "{}", "-".repeat(60));
    let _ = writeln!(out, "  Types:       {:>5.1}%", contract.types_score);
    let _ = writeln!(out, "  Signatures:  {:>5.1}%", contract.signatures_score);
    let _ = writeln!(out, "  Annotations: {:>5.1}%", contract.annotations_score);
    let _ = writeln!(out, "  Bodies:      {:>5.1}%", contract.bodies_score);
    let _ = writeln!(out, "  Structure:   {:>5.1}%", contract.structure_score);
    let _ = writeln!(out, "  Overall:     {:>5.1}%", contract.overall_score);
    if contract.artifact_score < 100.0 {
        let _ = writeln!(out, "  Artifacts:   {:>5.1}%", contract.artifact_score);
    }
    let _ = writeln!(out);

    if contract.functions.is_empty() {
        let _ = writeln!(out, "  (no functions)");
    } else {
        let _ = writeln!(out, "  Functions:");
        for (fname, fr) in &contract.functions {
            let present_mark = if fr.present { "+" } else { "-" };
            let _ = writeln!(
                out,
                "    {} {} (sig={:.1}%, body={:.1}%)",
                present_mark, fname, fr.signature_score, fr.body_score
            );

            if !fr.param_diffs.is_empty() {
                for diff in &fr.param_diffs {
                    let _ = writeln!(out, "        diff: {}", diff);
                }
            }
            if !fr.operations_missing.is_empty() {
                let _ = writeln!(
                    out,
                    "        missing ops: {}",
                    fr.operations_missing.join(", ")
                );
            }
            if !fr.operations_found.is_empty() {
                let _ = writeln!(out, "        found ops: {}", fr.operations_found.join(", "));
            }
            if fr.artifact_count > 0 {
                let _ = writeln!(out, "        artifacts: {}", fr.artifact_count);
            }
        }
    }

    Some(out)
}
