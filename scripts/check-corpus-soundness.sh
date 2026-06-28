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
set -o pipefail

REPO_DIR="$(cd "$(dirname "$0")/.." && pwd)"
VERIFY_DIR="$HOME/.cache/soroban-ret-verify"
GLOB="${1:-benchmark-data/mainnet/*.wasm}"
BIN="$REPO_DIR/target/debug/soroban-ret"
TARGET="wasm32v1-none"

# Preflight: a broken environment (missing target, no registry access, wrong
# toolchain) makes `cargo check` fail for reasons unrelated to the decompiled
# code. Without this the error grep would see no `error[E…]` lines and report 0,
# silently passing the ratchet against output that never actually compiled.
if ! rustup target list --installed 2>/dev/null | grep -qx "$TARGET"; then
    echo "FATAL: rust target '$TARGET' is not installed (rustup target add $TARGET)" >&2
    exit 2
fi

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
    # Capture output and exit status separately: cargo's status (0 iff the crate
    # compiled) is the source of truth for clean-vs-broken, NOT the error grep —
    # which can't tell "compiled, 0 errors" from "cargo never ran rustc on our
    # file". The grep only quantifies the ratchet metric (E-coded errors).
    out=$( cd "$VERIFY_DIR" && cargo check --target "$TARGET" --message-format=short --color never 2>&1 )
    status=$?
    # Match bytes, not characters: decompiled source can carry non-UTF-8 bytes in
    # identifiers/messages, and GNU grep in a UTF-8 locale (the CI default) then
    # fails to match present lines, whereas `LC_ALL=C grep -a` treats input as
    # raw text. Without this the gate spuriously trips the FATAL guard below.
    errs=$( printf '%s\n' "$out" | LC_ALL=C grep -acE 'src/lib\.rs.*error\[E[0-9]+\]' )
    COUNT=$((COUNT + 1))
    if [ "$status" -eq 0 ]; then
        CLEAN=$((CLEAN + 1))
        echo "CLEAN $name"
    else
        # Non-zero exit with no diagnostic referencing the generated file means
        # the build broke for an environment reason (registry, toolchain, …),
        # not because the decompiled code is wrong. Abort loudly rather than
        # silently scoring 0 and passing the ratchet on untrusted output.
        if ! printf '%s\n' "$out" | LC_ALL=C grep -qaE 'src/lib\.rs.*error'; then
            echo "FATAL: cargo check failed for $name with no diagnostics against the generated file (broken environment?)" >&2
            printf '%s\n' "$out" | tail -20 >&2
            exit 2
        fi
        TOTAL=$((TOTAL + errs))
        echo "ERR   $name ($errs)"
    fi
done

echo ""
echo "Contracts: $COUNT, clean-compiling: $CLEAN"
echo "TOTAL_ERRORS=$TOTAL"
