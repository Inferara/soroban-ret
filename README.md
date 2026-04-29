# Reverse-engineering tool for Stellar Soroban smart contracts

## Status

Early development. The current cut covers two pipeline stages:

- **Stage 1** — WASM parsing: sections, imports, exports, function bodies, data segments, custom sections (`contractspecv0`, `contractmetav0`, `contractenvmetav0`).
- **Stage 2** — Spec extraction: typed lookup tables for functions, structs, unions, enums, error enums, and events from the contract's `contractspecv0` XDR; SEP-41 / Stellar Asset standard-interface detection; SDK version from `contractmetav0`.

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
soroban-ret path/to/contract.wasm
```

Output is a one-line summary of the parsed module, e.g.:

```
Functions: 13, Types: 4, Imports: 27
```

Flags:

| Flag | Effect |
|---|---|
| `-o, --output <path>` | (reserved for source output once codegen lands) |
| `--spec-only` | (reserved for spec-only emission once codegen lands) |
| `-v, --verbose` | enable `debug`-level logging |

## Library usage

```rust
use soroban_ret::{TypeRegistry, WasmModule};

let wasm = std::fs::read("contract.wasm")?;

let module = WasmModule::parse(&wasm)?;
println!("imports: {}", module.imports.functions.len());
println!("functions: {}", module.functions.len());

let registry = TypeRegistry::from_wasm(&wasm)?;
for name in registry.functions.keys() {
    println!("fn {name}");
}
```

Validation diagnostics for non-Soroban-compliant constructs (floats, reference types, multi-memory, `call_indirect`, etc.) are available via `WasmModule::parse_diagnostics`.

## Build from source

Requires a stable Rust toolchain (MSRV declared in the workspace `Cargo.toml`).

```bash
git clone https://github.com/Inferara/soroban-ret.git
cd soroban-ret

cargo build --workspace
cargo test --workspace
cargo run -p soroban-ret-cli -- path/to/contract.wasm
```

## Roadmap

| Stage | Scope | Status |
|---|---|---|
| 1 | WASM parser | done |
| 2 | Spec extractor + standard-interface detector | done |
| 3 | Pattern matcher: host-call lifting, control-flow structurization, wrapper detection | planned |
| 4 | IR optimizer + post-optimization passes | planned |
| 5 | Rust source emitter | planned |

## License

Apache-2.0. See [LICENSE](LICENSE).
