#!/usr/bin/env bash
#
# Corpus structural-soundness gate (correctness-first).
#
# Decompiles every mainnet corpus contract and `cargo check`s the generated Rust
# against soroban-sdk for the wasm32 contract target, counting *hard* compile
# errors. Unlike `check-compilable.sh` (the fixture gate, which SKIPS any output
# containing `todo!`), this does NOT skip: `todo!()` compiles fine, so every hard
# error is a genuinely-wrong construct the lifter emitted — output that *looks*
# like code but does not type-check. The metric this drives is "wrong output",
# not "incomplete output".
#
# Prints a per-contract error count and a `TOTAL_ERRORS=<n>` line consumed by the
# `corpus_soundness` opt-in test. Lower is better; 0 means the whole corpus
# compiles (with `todo!()` husks standing in for unrecovered values).
#
# The verify crate lives outside the repo (in $HOME/.cache) so Cargo workspace
# auto-discovery doesn't pull it in, and so soroban-sdk artifacts cache across
# runs.
#
# Usage: scripts/check-corpus-soundness.sh [corpus-glob]
#   default glob: benchmark-data/mainnet/*.wasm
set -u

REPO_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VERIFY_DIR="$HOME/.cache/soroban-ret-verify"
GLOB="${1:-benchmark-data/mainnet/*.wasm}"
BIN="$REPO_DIR/target/debug/soroban-ret"

mkdir -p "$VERIFY_DIR/src"
cat > "$VERIFY_DIR/Cargo.toml" << 'TOML'
[package]
name = "soroban-ret-verify"
version = "0.0.0"
edition = "2021"

[dependencies]
soroban-sdk = "=26.0.1"

[lib]
crate-type = ["cdylib"]

[workspace]
TOML

cargo build -q -p soroban-ret-cli --manifest-path "$REPO_DIR/Cargo.toml" || exit 2

TOTAL=0
CLEAN=0
COUNT=0
for wasm in "$REPO_DIR"/$GLOB; do
    name=$(basename "$wasm" .wasm)
    "$BIN" "$wasm" 2>/dev/null > "$VERIFY_DIR/src/lib.rs"
    errs=$( (cd "$VERIFY_DIR" && cargo check --target wasm32v1-none --message-format=short 2>&1) \
            | grep -cE 'src/lib\.rs.*error\[E[0-9]+\]' )
    COUNT=$((COUNT + 1))
    TOTAL=$((TOTAL + errs))
    if [ "$errs" -eq 0 ]; then
        CLEAN=$((CLEAN + 1))
        echo "CLEAN $name"
    else
        echo "ERR   $name ($errs)"
    fi
done

echo ""
echo "Contracts: $COUNT, clean-compiling: $CLEAN"
echo "TOTAL_ERRORS=$TOTAL"
