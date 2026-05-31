//! Per-contract and per-function accuracy metrics.

use crate::ast_compare::{ComparisonResult, FunctionComparison};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// Complexity levels
// ---------------------------------------------------------------------------

/// Complexity level for a contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ComplexityLevel {
    Trivial = 1,
    Simple = 2,
    Complex = 3,
    Runtime = 4,
    Advanced = 5,
}

impl ComplexityLevel {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Trivial => "Trivial",
            Self::Simple => "Simple",
            Self::Complex => "Complex",
            Self::Runtime => "Runtime",
            Self::Advanced => "Advanced",
        }
    }

    pub fn target(&self) -> f64 {
        match self {
            Self::Trivial => 98.0,
            Self::Simple => 95.0,
            Self::Complex => 92.0,
            Self::Runtime => 88.0,
            Self::Advanced => 80.0,
        }
    }

    /// Return the level for a contract name. Defaults to Advanced.
    pub fn for_contract(name: &str) -> Self {
        match name {
            "empty" | "empty2" | "add_u64" | "add_u128" | "add_i128" | "zero" | "tuples" => {
                Self::Trivial
            }
            "contract_data" | "mutability" | "generics" => Self::Simple,
            "logging" => Self::Advanced, // log! macro stripped in release WASM builds
            "udt" | "errors" | "events" | "events_ref" | "constructor" => Self::Complex,
            "auth" | "account" | "invoke_contract" => Self::Runtime,
            _ => Self::Advanced,
        }
    }
}

// ---------------------------------------------------------------------------
// Report types
// ---------------------------------------------------------------------------

/// Full accuracy report for a set of contracts.
#[derive(Debug, Serialize, Deserialize)]
pub struct AccuracyReport {
    pub contracts: BTreeMap<String, ContractReport>,
    pub levels: BTreeMap<u8, LevelSummary>,
    pub overall_score: f64,
}

/// Per-contract accuracy report.
#[derive(Debug, Serialize, Deserialize)]
pub struct ContractReport {
    pub name: String,
    pub level: u8,
    pub types_score: f64,
    pub signatures_score: f64,
    pub annotations_score: f64,
    pub bodies_score: f64,
    pub structure_score: f64,
    pub overall_score: f64,
    /// Artifact quality score (100.0 = no artifacts). Not included in overall_score.
    pub artifact_score: f64,
    pub functions: BTreeMap<String, FunctionReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Per-function accuracy breakdown.
#[derive(Debug, Serialize, Deserialize)]
pub struct FunctionReport {
    pub present: bool,
    pub signature_score: f64,
    pub body_score: f64,
    pub param_diffs: Vec<String>,
    pub return_type_match: bool,
    pub operations_found: Vec<String>,
    pub operations_missing: Vec<String>,
    /// Count of decompilation artifacts in the function body.
    pub artifact_count: usize,
}

/// Summary for a complexity level.
#[derive(Debug, Serialize, Deserialize)]
pub struct LevelSummary {
    pub name: String,
    pub target: f64,
    pub average: f64,
    pub meets_target: bool,
    pub count: usize,
}

// ---------------------------------------------------------------------------
// Building reports
// ---------------------------------------------------------------------------

impl ContractReport {
    /// Build a report from a comparison result.
    pub fn from_comparison(name: &str, comparison: &ComparisonResult) -> Self {
        let level = ComplexityLevel::for_contract(name);

        let functions: BTreeMap<String, FunctionReport> = comparison
            .function_details
            .iter()
            .map(|(fname, fc)| (fname.clone(), FunctionReport::from_comparison(fc)))
            .collect();

        ContractReport {
            name: name.to_string(),
            level: level as u8,
            types_score: round1(comparison.types_score),
            signatures_score: round1(comparison.signatures_score),
            annotations_score: round1(comparison.annotations_score),
            bodies_score: round1(comparison.bodies_score),
            structure_score: round1(comparison.structure_score),
            overall_score: round1(comparison.overall_score),
            artifact_score: round1(comparison.artifact_score),
            functions,
            error: None,
        }
    }

    /// Build an error report when decompilation fails.
    pub fn error(name: &str, error: String) -> Self {
        ContractReport {
            name: name.to_string(),
            level: ComplexityLevel::for_contract(name) as u8,
            types_score: 0.0,
            signatures_score: 0.0,
            annotations_score: 0.0,
            bodies_score: 0.0,
            structure_score: 0.0,
            overall_score: 0.0,
            artifact_score: 0.0,
            functions: BTreeMap::new(),
            error: Some(error),
        }
    }
}

impl FunctionReport {
    fn from_comparison(fc: &FunctionComparison) -> Self {
        FunctionReport {
            present: fc.present,
            signature_score: round1(fc.signature_score),
            body_score: round1(fc.body_score),
            param_diffs: fc.param_diffs.clone(),
            return_type_match: fc.return_type_match,
            operations_found: fc.operations_found.clone(),
            operations_missing: fc.operations_missing.clone(),
            artifact_count: fc.artifact_count,
        }
    }
}

impl AccuracyReport {
    /// Build a report from individual contract reports.
    pub fn from_contracts(contracts: BTreeMap<String, ContractReport>) -> Self {
        let mut levels: BTreeMap<u8, Vec<f64>> = BTreeMap::new();
        let mut all_scores = Vec::new();

        for report in contracts.values() {
            levels
                .entry(report.level)
                .or_default()
                .push(report.overall_score);
            all_scores.push(report.overall_score);
        }

        let level_summaries: BTreeMap<u8, LevelSummary> = levels
            .into_iter()
            .map(|(level_num, scores)| {
                let avg = scores.iter().sum::<f64>() / scores.len() as f64;
                let cl = match level_num {
                    1 => ComplexityLevel::Trivial,
                    2 => ComplexityLevel::Simple,
                    3 => ComplexityLevel::Complex,
                    4 => ComplexityLevel::Runtime,
                    _ => ComplexityLevel::Advanced,
                };
                (
                    level_num,
                    LevelSummary {
                        name: cl.name().to_string(),
                        target: cl.target(),
                        average: round1(avg),
                        meets_target: avg >= cl.target(),
                        count: scores.len(),
                    },
                )
            })
            .collect();

        let overall = if all_scores.is_empty() {
            0.0
        } else {
            round1(all_scores.iter().sum::<f64>() / all_scores.len() as f64)
        };

        AccuracyReport {
            contracts,
            levels: level_summaries,
            overall_score: overall,
        }
    }
}

fn round1(v: f64) -> f64 {
    (v * 10.0).round() / 10.0
}
