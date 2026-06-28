[![Build](https://github.com/Inferara/soroban-ret/actions/workflows/build.yml/badge.svg)](https://github.com/Inferara/soroban-ret/actions/workflows/build.yml)
[![codecov](https://codecov.io/gh/Inferara/soroban-ret/branch/main/graph/badge.svg?token=U1F2477BLC)](https://codecov.io/gh/Inferara/soroban-ret)
[![soroban-ret on crates.io](https://img.shields.io/crates/v/soroban-ret.svg?label=soroban-ret)](https://crates.io/crates/soroban-ret)
[![soroban-ret-cli on crates.io](https://img.shields.io/crates/v/soroban-ret-cli.svg?label=soroban-ret-cli)](https://crates.io/crates/soroban-ret-cli)

# Reverse-engineering tool for Stellar Soroban smart contracts

## Status

Early development. The current cut covers the full five-stage pipeline, with
partial decompilation working end-to-end for contracts limited to simple
arithmetic, basic storage, custom types, events, auth, and cross-contract
calls.

- **Stage 1** — WASM parsing: sections, imports, exports, function bodies, data segments, custom sections (`contractspecv0`, `contractmetav0`, `contractenvmetav0`).
- **Stage 2** — Spec extraction: typed lookup tables for functions, structs, unions, enums, error enums, and events from the contract's `contractspecv0` XDR; SEP-41 / Stellar Asset standard-interface detection; SDK version from `contractmetav0`.
- **Stage 3** — Pattern matcher: host-call lifting, control-flow structurization, dispatch peeling, wrapper detection.
- **Stage 4** — IR optimizer + post-optimization passes: constant folding, has/get fusion, storage-key recovery, enum-key construction, event-publish recovery, auth/cross-contract repair, dead-code elimination.
- **Stage 5** — Rust source emitter: type definitions via `soroban-spec-rust`, function bodies, module assembly with `#[contract]`/`#[contractimpl]`, formatting via `prettyplease`.

## Install

The library and CLI are published as separate crates.

```bash
# Use as a library
cargo add soroban-ret

# Install the CLI (provides the `soroban-ret` binary)
cargo install soroban-ret-cli
```

## CLI usage

```bash
# Print decompiled Rust to stdout
soroban-ret path/to/contract.wasm

# Write decompiled Rust to a file
soroban-ret path/to/contract.wasm -o lib.rs

# Print only type definitions and function signatures
soroban-ret path/to/contract.wasm --spec-only

# Print contract metadata (SDK version, function/type counts, signatures)
soroban-ret path/to/contract.wasm --info

# Force generic WASM mode (no Soroban assumptions)
soroban-ret path/to/contract.wasm --generic
```

Flags:

| Flag | Purpose |
|---|---|
| `-o, --output <FILE>` | Write decompiled source to a file instead of stdout |
| `--spec-only` | Emit only type definitions and function signatures |
| `-O, --pre-optimize` | Pre-optimize the WASM with `wasm-opt` before decompilation (requires binaryen) |
| `--info` | Print contract metadata (SDK version, functions, types, events) and exit |
| `--generic` | Force generic WASM mode (no Soroban assumptions) |
| `-v, --verbose` | Enable debug logging |

## Library usage

```rust
use soroban_ret::{decompile, decompile_with_options, DecompileOptions};

let wasm = std::fs::read("contract.wasm")?;

// Simple: WASM bytes → formatted Rust source.
let source: String = decompile(&wasm)?;
println!("{source}");

// With options + metadata.
let mut options = DecompileOptions::default();
options.spec_only = true;
let result = decompile_with_options(&wasm, &options)?;
println!("SDK version: {:?}", result.sdk_version);
println!("Standard interfaces: {:?}", result.standard_interfaces);
for diag in &result.validation.diagnostics {
    eprintln!("diag: {diag}");
}
```

For lower-level inspection (raw parsed WASM, typed spec registry, validation
diagnostics) the stage-1 / stage-2 APIs are still public:

```rust
use soroban_ret::{TypeRegistry, WasmModule};

let module = WasmModule::parse(&wasm)?;
let registry = TypeRegistry::from_wasm(&wasm)?;
```

Validation diagnostics for non-Soroban-compliant constructs (floats, reference
types, multi-memory, `call_indirect`, etc.) are available via
`WasmModule::parse_diagnostics`.

## Build from source

Requires a stable Rust toolchain (MSRV declared in the workspace `Cargo.toml`).

```bash
git clone https://github.com/Inferara/soroban-ret.git
cd soroban-ret

cargo build --workspace
cargo test --workspace
cargo run -p soroban-ret-cli -- path/to/contract.wasm
```

## Validation

`cargo test --workspace` runs the fast gates by default, including:

- **Accuracy** — interface similarity vs the SDK reference sources (≈98 % over 37 contracts).
- **Spec-consistency** — generated signatures/types vs each contract's own `contractspecv0` (covers the mainnet corpus too, which has no reference source).
- **Structural plausibility** — a ratchet on per-contract recovery vs `benchmark-data/baseline.json`.

Three heavier gates compile decompiled output back for `wasm32v1-none` and are opt-in via env var (also run in CI):

```bash
# ≥95% of fixtures recompile (cargo check)
SOROBAN_RET_COMPILE_BACK=1 cargo test -p soroban-ret --test compile_back

# mainnet corpus hard-error ratchet
SOROBAN_RET_CORPUS_SOUNDNESS=1 cargo test -p soroban-ret --test corpus_soundness

# functional equivalence: recompile to wasm, run BOTH the original and
# recompiled contract through soroban-env-host, and diff their outputs
SOROBAN_RET_EQUIV=1 cargo test -p soroban-ret-equiv --test equivalence
```

The equivalence harness differentially executes scalar-invocable functions and
reports a behavioral-match metric; see
[`docs/pattern-coverage.md`](docs/pattern-coverage.md) for its scope and the
current divergence baseline.

## Roadmap

| Stage | Scope | Status |
|---|---|---|
| 1 | WASM parser | done |
| 2 | Spec extractor + standard-interface detector | done |
| 3 | Pattern matcher: host-call lifting, control-flow structurization, wrapper detection | done (partial) |
| 4 | IR optimizer + post-optimization passes | done (partial) |
| 5 | Rust source emitter | done (partial) |

"Partial" reflects the current deliverable scope: simple arithmetic, basic
storage, custom types, events, auth, and cross-contract calls produce
compilable Rust with correct types and signatures. Coverage of more advanced
patterns (allowance flows, complex token contracts, snapshot-quality
recovery) is on the roadmap.

A per-pattern audit of code, fixtures, and explicit assertions lives in
[`docs/pattern-coverage.md`](docs/pattern-coverage.md).

## Acknowledgements

This project is funded by the [Stellar Community Fund](https://communityfund.stellar.org/).

`soroban-ret` reverse-engineers Soroban contracts back into readable Rust source, giving developers and auditors on [Stellar](https://stellar.org/) the ability to inspect, review, and verify on-chain code that ships only as compiled WASM.

![SCF banner](assets/scf_banner.png)

## Contributing

Contributions are welcome!

## License

This project is licensed under the Apache License 2.0. See [LICENSE](./LICENSE) for details.
