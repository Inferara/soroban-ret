#!/usr/bin/env bash
#
# Rebuild the WASM test fixtures from the pinned `vendor/rs-soroban-sdk`
# submodule. Each fixture `tests/fixtures/test_<X>.wasm` is the release wasm32
# build artifact of the SDK test crate `test_<X>`, so the fixtures track the
# exact SDK version the submodule is pinned to (read it back with
# `soroban-ret --info <fixture>`).
#
# Fixtures without a matching SDK crate are NOT rebuilt and are listed at the
# end (e.g. `test_liquidity_pool.wasm`, which originates from soroban-examples,
# and the prefixless `contract*.wasm` smoke fixtures).
#
# Notes on the build flags:
#   - SOROBAN_SDK_BUILD_SYSTEM_SUPPORTS_SPEC_SHAKING_V2=1 is required: the v26+
#     test crates enable the `experimental_spec_shaking_v2` feature, whose build
#     script otherwise errors out unless the build system signals support.
#   - We deliberately do NOT set `--cfg soroban_sdk_internal_no_rssdkver_meta`
#     (which the SDK's own Makefile uses for binary stability). Keeping the
#     `rssdkver` metadata is what lets each fixture report its SDK version.
#
# Usage: scripts/rebuild-fixtures.sh
set -euo pipefail

REPO_DIR="$(cd "$(dirname "$0")/.." && pwd)"
SDK_DIR="$REPO_DIR/vendor/rs-soroban-sdk"
FIXTURES_DIR="$REPO_DIR/tests/fixtures"
TARGET="wasm32v1-none"
WASM_OUT="$SDK_DIR/target/$TARGET/release"

if [ ! -d "$SDK_DIR/tests" ]; then
    echo "ERROR: submodule not checked out: $SDK_DIR" >&2
    echo "Run: git submodule update --init --recursive" >&2
    exit 2
fi

# SDK test crate package names (the wasm artifact names).
SDK_CRATES=$(cd "$SDK_DIR" && cargo metadata --no-deps --format-version 1 \
    | python3 -c "import json,sys; print('\n'.join(p['name'] for p in json.load(sys.stdin)['packages'] if p['name'].startswith('test_')))")

build_pkgs=()
skipped=()
for wasm in "$FIXTURES_DIR"/test_*.wasm; do
    crate="$(basename "$wasm" .wasm)"   # e.g. test_add_u64
    if echo "$SDK_CRATES" | grep -qx "$crate"; then
        build_pkgs+=("--package" "$crate")
    else
        skipped+=("$crate")
    fi
done

echo "Building ${#build_pkgs[@]} package flags into $TARGET (release)..."
( cd "$SDK_DIR" \
  && SOROBAN_SDK_BUILD_SYSTEM_SUPPORTS_SPEC_SHAKING_V2=1 \
     cargo build --release --target "$TARGET" "${build_pkgs[@]}" )

copied=0
for ((i=1; i<${#build_pkgs[@]}; i+=2)); do
    crate="${build_pkgs[$i]}"
    src="$WASM_OUT/$crate.wasm"
    dst="$FIXTURES_DIR/$crate.wasm"
    if [ -f "$src" ]; then
        cp "$src" "$dst"
        copied=$((copied + 1))
    else
        echo "WARN: expected artifact missing: $src" >&2
    fi
done

echo ""
echo "Rebuilt $copied fixtures from $(cd "$SDK_DIR" && git describe --tags 2>/dev/null || git rev-parse --short HEAD)."
if [ "${#skipped[@]}" -gt 0 ]; then
    echo "Not rebuilt (no matching SDK crate, left as-is): ${skipped[*]}"
fi
