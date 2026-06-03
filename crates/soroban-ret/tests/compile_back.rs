//! Compile-back gate (RFP "≥95% compile success").
//!
//! Decompiles every `test_*.wasm` fixture and `cargo check`s the generated Rust
//! against `soroban-sdk` for the wasm32 contract target, asserting the
//! non-skipped pass rate is at least [`FLOOR_PCT`]. The heavy lifting lives in
//! `scripts/check-compilable.sh` (out-of-workspace verify crate, cached across
//! runs); this test wraps it so the gate is reachable under `cargo test`.
//!
//! It is **skipped unless `SOROBAN_RET_COMPILE_BACK=1` is set**, because it
//! compiles `soroban-sdk` for `wasm32v1-none` — slow, and needs the target
//! installed plus crates.io access — which would bloat the default
//! `cargo test --workspace` run. Mirrors the opt-in/skip pattern used by the
//! accuracy crate's `e2e_known_anchors` harness test.
//!
//! Run it explicitly:
//! ```text
//! SOROBAN_RET_COMPILE_BACK=1 cargo test -p soroban-ret --test compile_back -- --nocapture
//! ```

use std::process::Command;

/// Minimum non-skipped compile-back success rate, per the RFP gate.
const FLOOR_PCT: u32 = 95;

#[test]
fn compile_back_meets_floor() {
    if std::env::var("SOROBAN_RET_COMPILE_BACK").as_deref() != Ok("1") {
        eprintln!(
            "skipping compile_back: set SOROBAN_RET_COMPILE_BACK=1 to run the \
             >={FLOOR_PCT}% compile-back gate (compiles soroban-sdk for wasm32v1-none)"
        );
        return;
    }

    // CARGO_MANIFEST_DIR is crates/soroban-ret; the script lives at the repo root.
    let script = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../scripts/check-compilable.sh"
    );
    let output = Command::new("bash")
        .arg(script)
        .output()
        .expect("failed to spawn scripts/check-compilable.sh");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("{stdout}\n{stderr}");

    // The script's final tally line is: "Compile success (of non-skipped): NN%".
    let pct = stdout
        .lines()
        .rev()
        .find_map(|l| {
            l.strip_prefix("Compile success (of non-skipped): ")
                .and_then(|s| s.trim().trim_end_matches('%').parse::<u32>().ok())
        })
        .expect("could not parse compile-success percentage from check-compilable.sh output");

    assert!(
        pct >= FLOOR_PCT,
        "compile-back success {pct}% is below the {FLOOR_PCT}% floor"
    );
}
