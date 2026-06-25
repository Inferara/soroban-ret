//! Corpus structural-soundness ratchet (correctness-first).
//!
//! Decompiles every mainnet corpus contract and counts *hard* compile errors in
//! the generated Rust (`scripts/check-corpus-soundness.sh`). `todo!()` compiles,
//! so every counted error is a genuinely-wrong construct — output that looks like
//! code but does not type-check. The assert is a **ratchet**: the total must not
//! exceed [`ERROR_CEILING`]. Lower the ceiling as correctness fixes land; never
//! raise it without understanding why a change made output more wrong.
//!
//! Skipped unless `SOROBAN_RET_CORPUS_SOUNDNESS=1` (it compiles soroban-sdk for
//! `wasm32v1-none` — slow, needs the target installed plus crates.io access),
//! mirroring the `compile_back` gate.
//!
//! Run it explicitly:
//! ```text
//! SOROBAN_RET_CORPUS_SOUNDNESS=1 cargo test -p soroban-ret --test corpus_soundness -- --nocapture
//! ```

use std::process::Command;

/// Max tolerated hard compile errors across the whole mainnet corpus.
///
/// History (drive this down): 1339 (pre correctness-guard) → 1318 (break-outside-
/// loop + error-sentinel-access + undeclared-assignment husks).
const ERROR_CEILING: u32 = 1318;

#[test]
fn corpus_soundness_within_ceiling() {
    if std::env::var("SOROBAN_RET_CORPUS_SOUNDNESS").as_deref() != Ok("1") {
        eprintln!(
            "skipping corpus_soundness: set SOROBAN_RET_CORPUS_SOUNDNESS=1 to run the \
             <={ERROR_CEILING}-hard-error ratchet (compiles soroban-sdk for wasm32v1-none)"
        );
        return;
    }

    let script = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../scripts/check-corpus-soundness.sh"
    );
    let output = Command::new("bash")
        .arg(script)
        .output()
        .expect("failed to spawn scripts/check-corpus-soundness.sh");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("{stdout}\n{stderr}");

    let total = stdout
        .lines()
        .rev()
        .find_map(|l| {
            l.strip_prefix("TOTAL_ERRORS=")
                .and_then(|s| s.trim().parse::<u32>().ok())
        })
        .expect("could not parse TOTAL_ERRORS from check-corpus-soundness.sh output");

    assert!(
        total <= ERROR_CEILING,
        "corpus hard-error total {total} exceeds the {ERROR_CEILING} ceiling — a change made \
         decompiled output more wrong; investigate before raising the ceiling"
    );
}
