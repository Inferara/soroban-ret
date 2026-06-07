#!/usr/bin/env bash
#
# Regenerate the committed restoration baseline `benchmark-data/baseline.json`
# from the mainnet WASM corpus in `benchmark-data/mainnet/`.
#
# The baseline is the trimmed, stable per-contract subset (restoration %, fn
# buckets, artifact totals) that the per-PR benchmark CI diffs against to mark
# improved / reduced / no-change. Run this and commit the result whenever a
# decompiler change legitimately moves restoration numbers; on `main`, CI runs
# it automatically (see .github/workflows/benchmark.yml).
#
# Usage: scripts/rebuild-benchmark-baseline.sh [corpus-dir]
set -euo pipefail

# Run from the repo root with a RELATIVE corpus path so the committed baseline's
# `corpus` field is stable across machines (otherwise CI would re-commit it on
# every push).
cd "$(dirname "$0")/.."
CORPUS="${1:-benchmark-data/mainnet}"

if [ ! -d "$CORPUS" ]; then
    echo "error: corpus dir not found: $CORPUS" >&2
    exit 2
fi

echo "Building soroban-ret-bench (release)..."
cargo build --release -p soroban-ret-bench

echo "Benchmarking corpus: $CORPUS"
./target/release/bench --corpus "$CORPUS" --update-baseline

echo "Baseline written: $(dirname "$CORPUS")/baseline.json"
