#!/usr/bin/env bash
#
# Compile-back gate: decompile every fixture, then `cargo check` the generated
# Rust against soroban-sdk for the wasm32 contract target. Reports per-fixture
# PASS/FAIL/SKIP and a final tally.
#
# The verify crate lives outside the repo (in $HOME/.cache) so Cargo workspace
# auto-discovery doesn't pull it into the soroban-ret workspace, and so the
# soroban-sdk build artifacts are cached across runs.
#
# Usage: scripts/check-compilable.sh [fixture-glob]
#   default glob: tests/fixtures/test_*.wasm
set -u

REPO_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VERIFY_DIR="$HOME/.cache/soroban-ret-verify"
GLOB="${1:-tests/fixtures/test_*.wasm}"
BIN="$REPO_DIR/target/debug/soroban-ret"

mkdir -p "$VERIFY_DIR/src"
cat > "$VERIFY_DIR/Cargo.toml" << 'TOML'
[package]
name = "soroban-ret-verify"
version = "0.0.0"
edition = "2021"

[dependencies]
soroban-sdk = "=25.3.1"

[lib]
crate-type = ["cdylib"]

[workspace]
TOML

# Build the CLI once up front.
cargo build -q -p soroban-ret-cli --manifest-path "$REPO_DIR/Cargo.toml" || exit 2

PASS=0; FAIL=0; SKIP=0
FAILED_NAMES=()

for wasm in "$REPO_DIR"/$GLOB; do
    name=$(basename "$wasm" .wasm)
    "$BIN" "$wasm" 2>/dev/null > "$VERIFY_DIR/src/lib.rs"

    if grep -q 'todo!' "$VERIFY_DIR/src/lib.rs"; then
        echo "SKIP $name (empty/stub body)"
        SKIP=$((SKIP + 1))
        continue
    fi

    if (cd "$VERIFY_DIR" && cargo check --target wasm32v1-none 2>/dev/null) >/dev/null 2>&1; then
        echo "PASS $name"
        PASS=$((PASS + 1))
    else
        echo "FAIL $name"
        FAILED_NAMES+=("$name")
        FAIL=$((FAIL + 1))
    fi
done

TOTAL=$((PASS + FAIL + SKIP))
echo ""
echo "Results: $PASS pass, $FAIL fail, $SKIP skip ($TOTAL total)"
if [ "$FAIL" -gt 0 ]; then
    echo "Failed: ${FAILED_NAMES[*]}"
fi
COMPILABLE=$((PASS + FAIL))
if [ "$COMPILABLE" -gt 0 ]; then
    PCT=$((PASS * 100 / COMPILABLE))
    echo "Compile success (of non-skipped): ${PCT}%"
fi
