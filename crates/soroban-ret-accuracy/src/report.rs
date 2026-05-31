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
    if report.skipped.is_empty() {
        let _ = writeln!(out, "Scored {} contracts.", report.scored_count);
    } else {
        let _ = writeln!(
            out,
            "Scored {} contracts, skipped {} for missing reference source: {}",
            report.scored_count,
            report.skipped.len(),
            report.skipped.join(", ")
        );
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metrics::{AccuracyReport, ContractReport, FunctionReport};
    use std::collections::BTreeMap;

    fn func() -> FunctionReport {
        FunctionReport {
            present: true,
            signature_score: 90.0,
            body_score: 75.0,
            param_diffs: vec!["a: u64 vs u32".to_string()],
            return_type_match: true,
            operations_found: vec!["add".to_string()],
            operations_missing: vec!["match".to_string()],
            artifact_count: 2,
        }
    }

    fn contract(name: &str, level: u8, score: f64, artifact: f64, with_fn: bool) -> ContractReport {
        let mut functions = BTreeMap::new();
        if with_fn {
            functions.insert("do_it".to_string(), func());
        }
        ContractReport {
            name: name.to_string(),
            level,
            types_score: score,
            signatures_score: score,
            annotations_score: score,
            bodies_score: score,
            structure_score: score,
            overall_score: score,
            artifact_score: artifact,
            functions,
            error: None,
        }
    }

    fn sample_report() -> AccuracyReport {
        let mut gamma = ContractReport::error("gamma", "Decompile error: boom".to_string());
        gamma.level = 3; // keep level 3 deterministic for the BELOW-TARGET assertion

        let mut map = BTreeMap::new();
        map.insert("alpha".to_string(), contract("alpha", 3, 95.0, 80.0, true));
        map.insert("beta".to_string(), contract("beta", 3, 50.0, 100.0, false));
        map.insert(
            "delta".to_string(),
            contract("delta", 1, 100.0, 100.0, false),
        );
        map.insert("gamma".to_string(), gamma);

        let mut report = AccuracyReport::from_contracts(map);
        report.skipped = vec!["liquidity_pool".to_string()];
        report
    }

    #[test]
    fn render_table_covers_all_sections() {
        let t = render_table(&sample_report());
        assert!(t.contains("alpha") && t.contains("beta") && t.contains("delta"));
        assert!(t.contains("OVERALL AVERAGE ACCURACY"));
        assert!(t.contains("Level 1") && t.contains("Level 3"));
        assert!(t.contains("[OK]"), "level 1 meets target → OK:\n{t}");
        assert!(
            t.contains("BELOW TARGET"),
            "level 3 dragged below target:\n{t}"
        );
        assert!(t.contains("* Decompilation errors:"));
        assert!(t.contains("gamma: Decompile error: boom"));
        assert!(t.contains("skipped 1 for missing reference source: liquidity_pool"));
    }

    #[test]
    fn render_table_scored_line_without_skips() {
        let mut map = BTreeMap::new();
        map.insert(
            "alpha".to_string(),
            contract("alpha", 1, 100.0, 100.0, false),
        );
        let t = render_table(&AccuracyReport::from_contracts(map));
        assert!(t.contains("Scored 1 contracts."), "{t}");
    }

    #[test]
    fn render_detail_present_absent_and_missing() {
        let r = sample_report();

        let d = render_detail(&r, "alpha").expect("alpha exists");
        assert!(d.contains("Contract: alpha (Level 3)"));
        assert!(d.contains("Functions:") && d.contains("do_it"));
        assert!(d.contains("found ops: add"));
        assert!(d.contains("missing ops: match"));
        assert!(d.contains("diff: a: u64 vs u32"));
        assert!(d.contains("artifacts: 2"));
        assert!(d.contains("Artifacts:"), "artifact_score < 100 line:\n{d}");

        let g = render_detail(&r, "beta").expect("beta exists");
        assert!(g.contains("(no functions)"));

        assert!(render_detail(&r, "does-not-exist").is_none());
    }

    #[test]
    fn render_json_round_trips() {
        let r = sample_report();
        let json = render_json(&r);
        assert!(json.contains("\"overall_score\""));
        let back: AccuracyReport = serde_json::from_str(&json).expect("parse");
        assert_eq!(back.overall_score, r.overall_score);
        assert_eq!(back.contracts.len(), r.contracts.len());
    }
}
