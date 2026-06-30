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
use soroban_ret::ir::{ContractFn, MatchPattern, SorobanExpr, SorobanStmt};

/// Number of times Stage-1 disassembly is timed; the median is reported.
const DISASM_SAMPLES: usize = 5;

// ---------------------------------------------------------------------------
// Output shapes
// ---------------------------------------------------------------------------

/// Per-category `todo!()` / `var_N` artifact counts, matching the accounting in
/// `soroban-ret-accuracy`'s `count_artifacts` so the numbers line up with the
/// project's existing artifact tracking.
#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq, Eq)]
pub struct ArtifactCounts {
    pub unknown_value: usize,
    pub host_call: usize,
    pub stub: usize,
    pub var_n: usize,
    pub total: usize,
}

/// Recovery verdict for a single exported function.
#[derive(Serialize, Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum FnStatus {
    /// Body lifted with zero unrecovered nodes.
    Clean,
    /// Body present but contains some unrecovered nodes.
    Partial,
    /// Body collapsed to empty although the lifter saw host calls — real logic
    /// was lost (see `ContractFn::had_host_calls`).
    LogicLost,
    /// Empty body with no host calls — an identity/passthrough; nothing to restore.
    Trivial,
    /// Declared in the spec but absent from the lifted module.
    Missing,
}

/// Per-function benchmark record.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct FnBench {
    pub name: String,
    pub status: FnStatus,
    /// 0.0..=1.0 recovery fraction.
    pub score: f64,
    pub total_nodes: usize,
    pub unknown_nodes: usize,
    /// Distinct unrecovered host calls (`module::function`) referenced by the body.
    pub missing_host_calls: Vec<String>,
}

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
// Scoring
// ---------------------------------------------------------------------------

/// Accumulated traversal statistics for one function body.
#[derive(Default)]
struct NodeStats {
    /// Total expression nodes visited.
    total: usize,
    /// Nodes the decompiler could not lift (each renders as a `todo!()`):
    /// `UnknownVal`, `CyclicSlot`, `RawHostCall`.
    unknown: usize,
    /// `module::function` of each unrecovered `RawHostCall`.
    host_calls: Vec<String>,
}

/// Grade one exported function's recovery in `[0.0, 1.0]`.
///
/// - empty body + `had_host_calls` → `0.0` (logic lost)
/// - empty body + no host calls    → `1.0` (trivial/passthrough)
/// - non-empty body                → `clean_nodes / total_nodes`
pub fn score_fn(name: &str, f: &ContractFn) -> FnBench {
    if f.body.is_empty() {
        let (status, score) = if f.had_host_calls {
            (FnStatus::LogicLost, 0.0)
        } else {
            (FnStatus::Trivial, 1.0)
        };
        return FnBench {
            name: name.to_string(),
            status,
            score,
            total_nodes: 0,
            unknown_nodes: 0,
            missing_host_calls: Vec::new(),
        };
    }

    let mut s = NodeStats::default();
    walk_body(&f.body, &mut s);
    let score = if s.total == 0 {
        // Body has only control flow / comments and no expression nodes — nothing
        // was left unrecovered.
        1.0
    } else {
        (s.total - s.unknown) as f64 / s.total as f64
    };
    let status = if s.unknown == 0 {
        FnStatus::Clean
    } else {
        FnStatus::Partial
    };
    s.host_calls.sort();
    s.host_calls.dedup();
    FnBench {
        name: name.to_string(),
        status,
        score,
        total_nodes: s.total,
        unknown_nodes: s.unknown,
        missing_host_calls: s.host_calls,
    }
}

fn walk_body(body: &[SorobanStmt], s: &mut NodeStats) {
    for st in body {
        walk_stmt(st, s);
    }
}

fn walk_stmt(st: &SorobanStmt, s: &mut NodeStats) {
    match st {
        SorobanStmt::Expr(e) => walk_expr(e, s),
        SorobanStmt::Let { value, .. } => walk_expr(value, s),
        SorobanStmt::Assign { value, .. } => walk_expr(value, s),
        SorobanStmt::Return(Some(e)) => walk_expr(e, s),
        SorobanStmt::Return(None) => {}
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            walk_expr(condition, s);
            walk_body(then_body, s);
            walk_body(else_body, s);
        }
        SorobanStmt::Match { scrutinee, arms } => {
            walk_expr(scrutinee, s);
            for arm in arms {
                if let MatchPattern::Literal(e) = &arm.pattern {
                    walk_expr(e, s);
                }
                walk_body(&arm.body, s);
            }
        }
        SorobanStmt::Loop { body } => walk_body(body, s),
        SorobanStmt::For {
            start, end, body, ..
        } => {
            walk_expr(start, s);
            walk_expr(end, s);
            walk_body(body, s);
        }
        SorobanStmt::Block(b) => walk_body(b, s),
        SorobanStmt::Comment(_) | SorobanStmt::Break | SorobanStmt::Continue => {}
    }
}

/// Visit every expression node, counting totals and the unrecovered markers.
///
/// The match is exhaustive on purpose: if `SorobanExpr` gains a variant, this
/// fails to compile and forces the metric to account for it.
fn walk_expr(e: &SorobanExpr, s: &mut NodeStats) {
    s.total += 1;
    match e {
        // Unrecovered markers (each renders as a `todo!()`).
        SorobanExpr::UnknownVal | SorobanExpr::CyclicSlot { .. } => s.unknown += 1,
        SorobanExpr::RawHostCall {
            module,
            function,
            args,
        } => {
            s.unknown += 1;
            s.host_calls.push(format!("{module}::{function}"));
            for a in args {
                walk_expr(a, s);
            }
        }

        // Leaves with no expression children.
        SorobanExpr::U32Literal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::I64Literal(_)
        | SorobanExpr::U128Literal(_)
        | SorobanExpr::I128Literal(_)
        | SorobanExpr::BoolLiteral(_)
        | SorobanExpr::SymbolLiteral(_)
        | SorobanExpr::StringLiteral(_)
        | SorobanExpr::BytesLiteral(_)
        | SorobanExpr::Void
        | SorobanExpr::None
        | SorobanExpr::Param(_)
        | SorobanExpr::Local(_)
        | SorobanExpr::NamedLocal(_)
        | SorobanExpr::Env
        | SorobanExpr::ContractError { .. }
        | SorobanExpr::Panic
        | SorobanExpr::LedgerSequence
        | SorobanExpr::LedgerTimestamp
        | SorobanExpr::LedgerNetworkId
        | SorobanExpr::CurrentContractAddress
        | SorobanExpr::MaxLiveUntilLedger
        | SorobanExpr::CollectionNew(_)
        | SorobanExpr::ValTagName(_) => {}

        // Single child.
        SorobanExpr::Some(b)
        | SorobanExpr::Not(b)
        | SorobanExpr::RequireAuth(b)
        | SorobanExpr::AuthorizeAsCurrContract(b)
        | SorobanExpr::ErrorFromCode(b)
        | SorobanExpr::PanicWithError(b)
        | SorobanExpr::CryptoSha256(b)
        | SorobanExpr::CryptoKeccak256(b)
        | SorobanExpr::PrngReseed(b)
        | SorobanExpr::PrngBytesNew(b)
        | SorobanExpr::PrngVecShuffle(b)
        | SorobanExpr::StrkeyToAddress(b)
        | SorobanExpr::AddressToStrkey(b)
        | SorobanExpr::SretResult(b)
        | SorobanExpr::ValTag(b)
        | SorobanExpr::ValConvert { value: b, .. }
        | SorobanExpr::CastAs { value: b, .. }
        | SorobanExpr::Try(b) => walk_expr(b, s),

        // Two children.
        SorobanExpr::Add(a, b)
        | SorobanExpr::Sub(a, b)
        | SorobanExpr::Mul(a, b)
        | SorobanExpr::Div(a, b)
        | SorobanExpr::Rem(a, b)
        | SorobanExpr::Eq(a, b)
        | SorobanExpr::Ne(a, b)
        | SorobanExpr::Lt(a, b)
        | SorobanExpr::Le(a, b)
        | SorobanExpr::Gt(a, b)
        | SorobanExpr::Ge(a, b)
        | SorobanExpr::And(a, b)
        | SorobanExpr::Or(a, b)
        | SorobanExpr::RequireAuthForArgs {
            address: a,
            args: b,
        }
        | SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold: a,
            extend_to: b,
        }
        | SorobanExpr::VecTryIterFold { vec: a, init: b } => {
            walk_expr(a, s);
            walk_expr(b, s);
        }

        // Storage.
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => walk_expr(key, s),
        SorobanExpr::StorageSet { key, value, .. } => {
            walk_expr(key, s);
            walk_expr(value, s);
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            walk_expr(key, s);
            walk_expr(threshold, s);
            walk_expr(extend_to, s);
        }

        // Events / calls.
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics {
                walk_expr(t, s);
            }
            walk_expr(data, s);
        }
        SorobanExpr::InvokeContract {
            address,
            function,
            args,
            ..
        }
        | SorobanExpr::TryInvokeContract {
            address,
            function,
            args,
            ..
        } => {
            walk_expr(address, s);
            walk_expr(function, s);
            for a in args {
                walk_expr(a, s);
            }
        }

        // Constructors / access.
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields {
                walk_expr(v, s);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for v in fields {
                walk_expr(v, s);
            }
        }
        SorobanExpr::TupleConstruct(items)
        | SorobanExpr::VecConstruct(items)
        | SorobanExpr::Log(items) => {
            for v in items {
                walk_expr(v, s);
            }
        }
        SorobanExpr::MapConstruct(pairs) => {
            for (k, v) in pairs {
                walk_expr(k, s);
                walk_expr(v, s);
            }
        }
        SorobanExpr::FieldAccess { object, .. } => walk_expr(object, s),
        SorobanExpr::MethodCall { object, args, .. } => {
            walk_expr(object, s);
            for a in args {
                walk_expr(a, s);
            }
        }

        // Crypto with multiple children.
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            walk_expr(public_key, s);
            walk_expr(message, s);
            walk_expr(signature, s);
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            walk_expr(msg_digest, s);
            walk_expr(signature, s);
            walk_expr(recovery_id, s);
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            walk_expr(low, s);
            walk_expr(high, s);
        }
    }
}

// ---------------------------------------------------------------------------
// Artifact counting (mirrors soroban-ret-accuracy::ast_compare::count_artifacts)
// ---------------------------------------------------------------------------

/// Count `todo!()` / `var_N` artifacts in generated source, by category.
pub fn count_artifacts(src: &str) -> ArtifactCounts {
    let count_both = |a: &str, b: &str| src.matches(a).count() + src.matches(b).count();
    let unknown_value = count_both("todo!(\"unknown value\")", "todo !(\"unknown value\")");
    let host_call = count_both("todo!(\"host call", "todo !(\"host call");
    let stub = count_both(
        "todo!(\"decompiled function body\")",
        "todo !(\"decompiled function body\")",
    );

    let mut var_n = 0;
    for word in src.split(|c: char| !c.is_alphanumeric() && c != '_') {
        if word.len() > 4
            && word.starts_with("var_")
            && word[4..].chars().all(|c| c.is_ascii_digit())
        {
            var_n += 1;
        }
    }

    ArtifactCounts {
        unknown_value,
        host_call,
        stub,
        var_n,
        total: unknown_value + host_call + stub + var_n,
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
    c.artifacts = count_artifacts(&ir.source);

    // Index lifted functions by name for spec lookup.
    let lifted: BTreeMap<&str, &ContractFn> = ir
        .contract_module
        .functions
        .iter()
        .map(|f| (f.name.as_str(), f))
        .collect();

    // Denominator = spec (contractspecv0) functions; fall back to the lifted set
    // when there is no spec (non-Rust SDK contracts).
    let names: Vec<String> = if !ir.registry.functions.is_empty() {
        ir.registry.functions.keys().cloned().collect()
    } else {
        ir.contract_module
            .functions
            .iter()
            .map(|f| f.name.clone())
            .collect()
    };

    let mut fns = Vec::with_capacity(names.len());
    for name in &names {
        let fb = match lifted.get(name.as_str()) {
            Some(f) => score_fn(name, f),
            None => FnBench {
                name: name.clone(),
                status: FnStatus::Missing,
                score: 0.0,
                total_nodes: 0,
                unknown_nodes: 0,
                missing_host_calls: Vec::new(),
            },
        };
        fns.push(fb);
    }

    c.spec_functions = fns.len();
    for f in &fns {
        match f.status {
            FnStatus::Clean | FnStatus::Trivial => c.fn_clean += 1,
            FnStatus::Partial => c.fn_partial += 1,
            FnStatus::LogicLost | FnStatus::Missing => c.fn_logic_lost += 1,
        }
    }
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
