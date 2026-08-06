//! Reference-free restoration metrics.
//!
//! Mainnet binaries have no original source, so "restoration %" is derived
//! entirely from the decompiler's own output: how much of each function lifted
//! to concrete Rust versus how much collapsed into `todo!()` / unknown markers.
//!
//! The headline score is **graded per exported function** (see [`score_fn`]):
//! the denominator is the contract's `contractspecv0` function list (the
//! authoritative public interface), and each function contributes a 0..1
//! recovery fraction. Artifact category counts and disassembly timing are
//! reported alongside but are not part of the headline percentage.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use serde::{Deserialize, Serialize};

/// Number of times Stage-1 disassembly is timed; the median is reported.
const DISASM_SAMPLES: usize = 5;

// ---------------------------------------------------------------------------
// Output shapes
// ---------------------------------------------------------------------------

/// The recovery types are owned by the published `soroban-ret` crate
/// (`soroban_ret::recovery`) so the decompiler, this benchmark and the accuracy
/// harness all count the same things. They used to be duplicated here and in
/// `soroban-ret-accuracy`, which is exactly how three copies drift apart.
pub use soroban_ret::recovery::{ArtifactCounts, FnStatus, count_artifacts, score_fn};

/// Per-function benchmark record. Alias kept for the existing report/baseline
/// field names; the type itself lives in the library.
pub type FnBench = soroban_ret::recovery::FnRecovery;

/// Per-contract benchmark record (full, volatile — used for `--json` and HTML).
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct ContractBench {
    pub file: String,
    pub entity: Option<String>,
    pub contract_id: Option<String>,
    pub wasm_size: usize,
    /// 0.0..=100.0, rounded to 1 decimal.
    pub restoration_pct: f64,
    pub spec_functions: usize,
    pub fn_clean: usize,
    pub fn_partial: usize,
    pub fn_logic_lost: usize,
    pub artifacts: ArtifactCounts,
    /// Median Stage-1 disassembly time, milliseconds (rounded to 3 decimals).
    pub disasm_ms: f64,
    /// Full pipeline time, milliseconds (rounded to 3 decimals).
    pub total_ms: f64,
    pub sdk_version: Option<String>,
    pub standard_interfaces: Vec<String>,
    pub diagnostics: Vec<String>,
    /// Set when decompilation failed; the row then scores 0%.
    pub error: Option<String>,
    pub functions: Vec<FnBench>,
}

/// Full benchmark report for one corpus run.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct BenchReport {
    pub corpus: String,
    /// Equal-weight mean of `restoration_pct` across all corpus files.
    pub overall_restoration: f64,
    pub contracts: Vec<ContractBench>,
}

// ---------------------------------------------------------------------------
// Committed baseline (trimmed, stable subset — what `--against` diffs against)
// ---------------------------------------------------------------------------

/// Stable per-contract subset stored in `benchmark-data/baseline.json`.
/// Excludes timings and per-function detail so git diffs only show genuine
/// changes in restoration quality.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct BaselineContract {
    pub file: String,
    pub entity: Option<String>,
    pub restoration_pct: f64,
    pub spec_functions: usize,
    pub fn_clean: usize,
    pub fn_partial: usize,
    pub fn_logic_lost: usize,
    pub artifacts_total: usize,
    pub wasm_size: usize,
    pub error: Option<String>,
}

/// Committed baseline document.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Baseline {
    pub corpus: String,
    pub overall_restoration: f64,
    pub contracts: Vec<BaselineContract>,
}

impl From<&BenchReport> for Baseline {
    fn from(r: &BenchReport) -> Self {
        Baseline {
            corpus: r.corpus.clone(),
            overall_restoration: r.overall_restoration,
            contracts: r
                .contracts
                .iter()
                .map(|c| BaselineContract {
                    file: c.file.clone(),
                    entity: c.entity.clone(),
                    restoration_pct: c.restoration_pct,
                    spec_functions: c.spec_functions,
                    fn_clean: c.fn_clean,
                    fn_partial: c.fn_partial,
                    fn_logic_lost: c.fn_logic_lost,
                    artifacts_total: c.artifacts.total,
                    wasm_size: c.wasm_size,
                    error: c.error.clone(),
                })
                .collect(),
        }
    }
}

// ---------------------------------------------------------------------------
// Per-contract benchmark
// ---------------------------------------------------------------------------

fn round(x: f64, places: i32) -> f64 {
    let f = 10f64.powi(places);
    (x * f).round() / f
}

fn median_disasm_ms(wasm: &[u8]) -> f64 {
    let mut samples = Vec::with_capacity(DISASM_SAMPLES);
    for _ in 0..DISASM_SAMPLES {
        let t = Instant::now();
        // Stage-1 disassembly in isolation; the corpus is known-parseable.
        let _ = soroban_ret::WasmModule::parse(wasm);
        samples.push(t.elapsed().as_secs_f64() * 1000.0);
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    samples[samples.len() / 2]
}

/// Benchmark a single WASM binary.
pub fn bench_wasm(
    file: String,
    wasm: &[u8],
    entity: Option<String>,
    contract_id: Option<String>,
) -> ContractBench {
    let wasm_size = wasm.len();
    let disasm_ms = round(median_disasm_ms(wasm), 3);

    let t = Instant::now();
    let ir = soroban_ret::decompile_to_ir(wasm);
    let total_ms = round(t.elapsed().as_secs_f64() * 1000.0, 3);

    let mut c = ContractBench {
        file,
        entity,
        contract_id,
        wasm_size,
        restoration_pct: 0.0,
        spec_functions: 0,
        fn_clean: 0,
        fn_partial: 0,
        fn_logic_lost: 0,
        artifacts: ArtifactCounts::default(),
        disasm_ms,
        total_ms,
        sdk_version: None,
        standard_interfaces: Vec::new(),
        diagnostics: Vec::new(),
        error: None,
        functions: Vec::new(),
    };

    let ir = match ir {
        Ok(ir) => ir,
        Err(e) => {
            c.error = Some(e.to_string());
            return c;
        }
    };

    c.sdk_version = ir.sdk_version.clone();
    c.standard_interfaces = ir.standard_interfaces.clone();
    c.diagnostics = ir
        .validation
        .diagnostics
        .iter()
        .map(|d| d.to_string())
        .collect();
    // The per-function verdicts and hole counts are computed by the decompiler
    // itself (`soroban_ret::recovery`), so this benchmark and any embedder read
    // the same numbers off the same code path.
    //
    // Absent only under `spec_only`, which this benchmark never sets. Recorded
    // as an error rather than defaulted to zeros: a contract silently scoring
    // 0 % would read as a catastrophic regression in the ratchet.
    let Some(recovery) = ir.recovery else {
        c.error = Some("no recovery report (bodies not lifted)".to_string());
        return c;
    };
    c.artifacts = recovery.artifacts.clone();

    let fns = recovery.functions.clone();
    c.spec_functions = fns.len();
    for f in &fns {
        // `FnStatus` is `#[non_exhaustive]`; a future variant lands in the
        // partial bucket until this is taught about it.
        if f.status.is_fully_recovered() {
            c.fn_clean += 1;
        } else if f.status.is_lost() {
            c.fn_logic_lost += 1;
        } else {
            c.fn_partial += 1;
        }
    }
    // The mean lives here, not in the library: a single contract-level
    // percentage is the number most likely to be misread as a correctness
    // claim, so the library deliberately exposes only counts and per-function
    // scores. As a corpus-wide *trend* line, which is all this benchmark uses
    // it for, it is sound.
    let mean = if fns.is_empty() {
        0.0
    } else {
        fns.iter().map(|f| f.score).sum::<f64>() / fns.len() as f64
    };
    c.restoration_pct = round(mean * 100.0, 1);
    c.functions = fns;
    c
}

// ---------------------------------------------------------------------------
// Corpus run
// ---------------------------------------------------------------------------

/// Read `<corpus>/manifest.json` into a `file -> (entity, contract_id)` map.
/// Returns an empty map if the manifest is absent or unreadable.
fn load_manifest(corpus: &Path) -> BTreeMap<String, (Option<String>, Option<String>)> {
    let mut map = BTreeMap::new();
    let Ok(text) = std::fs::read_to_string(corpus.join("manifest.json")) else {
        return map;
    };
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else {
        return map;
    };
    if let Some(arr) = json.get("contracts").and_then(|v| v.as_array()) {
        for entry in arr {
            let Some(file) = entry.get("wasm_file").and_then(|v| v.as_str()) else {
                continue;
            };
            let entity = entry
                .get("entity")
                .and_then(|v| v.as_str())
                .map(String::from);
            let cid = entry
                .get("contract_id")
                .and_then(|v| v.as_str())
                .map(String::from);
            map.insert(file.to_string(), (entity, cid));
        }
    }
    map
}

/// Benchmark every `*.wasm` in `corpus` (sorted by file name).
pub fn run(corpus: &Path) -> std::io::Result<BenchReport> {
    let manifest = load_manifest(corpus);

    let mut files: Vec<_> = std::fs::read_dir(corpus)?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("wasm"))
        .collect();
    files.sort();

    let mut contracts = Vec::with_capacity(files.len());
    for path in files {
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_string();
        let (entity, cid) = manifest.get(&name).cloned().unwrap_or((None, None));
        match std::fs::read(&path) {
            Ok(wasm) => contracts.push(bench_wasm(name, &wasm, entity, cid)),
            Err(e) => {
                let mut c = bench_wasm(name, &[], entity, cid);
                c.error = Some(format!("read error: {e}"));
                contracts.push(c);
            }
        }
    }

    let overall = if contracts.is_empty() {
        0.0
    } else {
        round(
            contracts.iter().map(|c| c.restoration_pct).sum::<f64>() / contracts.len() as f64,
            1,
        )
    };

    Ok(BenchReport {
        corpus: normalize_corpus_path(corpus),
        overall_restoration: overall,
        contracts,
    })
}

/// The corpus string is committed inside `baseline.json`; keep it stable across
/// platforms and input spelling (Windows separators, trailing slash, `./`).
fn normalize_corpus_path(corpus: &Path) -> String {
    let s = corpus.display().to_string().replace('\\', "/");
    let s = s.trim_end_matches('/');
    s.strip_prefix("./").unwrap_or(s).to_string()
}
