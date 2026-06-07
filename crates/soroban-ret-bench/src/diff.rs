//! Compare a fresh run against the committed baseline and classify each contract
//! (and the overall score) as improved / reduced / no-change.
//!
//! Only restoration % drives the verdict — disassembly time is intentionally
//! excluded (it is noisy across CI runners).

use serde::Serialize;

use crate::metrics::{Baseline, BenchReport};

#[derive(Serialize, Clone, Copy, Debug, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Verdict {
    Improved,
    Reduced,
    NoChange,
    /// Present now, absent from the baseline.
    New,
    /// In the baseline, absent now.
    Removed,
}

impl Verdict {
    pub fn arrow(self) -> &'static str {
        match self {
            Verdict::Improved => "▲",
            Verdict::Reduced => "▼",
            Verdict::NoChange => "=",
            Verdict::New => "✚",
            Verdict::Removed => "✖",
        }
    }
}

fn classify(delta: f64, tolerance: f64) -> Verdict {
    if delta > tolerance {
        Verdict::Improved
    } else if delta < -tolerance {
        Verdict::Reduced
    } else {
        Verdict::NoChange
    }
}

#[derive(Serialize, Clone, Debug)]
pub struct ContractDelta {
    pub file: String,
    pub current: Option<f64>,
    pub baseline: Option<f64>,
    pub delta: f64,
    pub verdict: Verdict,
}

#[derive(Serialize, Clone, Debug)]
pub struct DiffReport {
    pub overall_current: f64,
    pub overall_baseline: f64,
    pub overall_delta: f64,
    pub overall_verdict: Verdict,
    pub tolerance: f64,
    pub improved: usize,
    pub reduced: usize,
    pub no_change: usize,
    pub deltas: Vec<ContractDelta>,
}

/// Build a per-file + overall diff. `deltas` is keyed by file and includes
/// rows that are New (only in `report`) or Removed (only in `baseline`).
pub fn diff(report: &BenchReport, baseline: &Baseline, tolerance: f64) -> DiffReport {
    use std::collections::BTreeMap;

    let base: BTreeMap<&str, f64> = baseline
        .contracts
        .iter()
        .map(|c| (c.file.as_str(), c.restoration_pct))
        .collect();
    let cur: BTreeMap<&str, f64> = report
        .contracts
        .iter()
        .map(|c| (c.file.as_str(), c.restoration_pct))
        .collect();

    let mut files: Vec<&str> = base.keys().chain(cur.keys()).copied().collect();
    files.sort();
    files.dedup();

    let mut deltas = Vec::new();
    let (mut improved, mut reduced, mut no_change) = (0, 0, 0);
    for f in files {
        let c = cur.get(f).copied();
        let b = base.get(f).copied();
        let (delta, verdict) = match (c, b) {
            (Some(c), Some(b)) => {
                // `restoration_pct` is quantized to 0.1 pp at source
                // (metrics.rs), so the true delta is a multiple of 0.1 and
                // rounding here only strips float noise from `c - b`.
                // Classifying the unrounded difference would flip
                // exactly-at-tolerance deltas nondeterministically (e.g.
                // 0.4 - 0.3 = 0.10000000000000003 > 0.1 → false Improved).
                // Pinned by tests/diff.rs.
                let d = round(c - b, 1);
                let v = classify(d, tolerance);
                match v {
                    Verdict::Improved => improved += 1,
                    Verdict::Reduced => reduced += 1,
                    _ => no_change += 1,
                }
                (d, v)
            }
            (Some(_), None) => (0.0, Verdict::New),
            (None, Some(_)) => (0.0, Verdict::Removed),
            (None, None) => unreachable!(),
        };
        deltas.push(ContractDelta {
            file: f.to_string(),
            current: c,
            baseline: b,
            delta,
            verdict,
        });
    }

    // Same float-noise rationale as the per-contract deltas above: overall
    // restoration is 1-dp quantized at source, round before classifying.
    let overall_delta = round(report.overall_restoration - baseline.overall_restoration, 1);
    DiffReport {
        overall_current: report.overall_restoration,
        overall_baseline: baseline.overall_restoration,
        overall_delta,
        overall_verdict: classify(overall_delta, tolerance),
        tolerance,
        improved,
        reduced,
        no_change,
        deltas,
    }
}

fn round(x: f64, places: i32) -> f64 {
    let f = 10f64.powi(places);
    (x * f).round() / f
}
