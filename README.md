[![Build](https://github.com/Inferara/soroban-ret/actions/workflows/build.yml/badge.svg)](https://github.com/Inferara/soroban-ret/actions/workflows/build.yml)
[![codecov](https://codecov.io/gh/Inferara/soroban-ret/branch/main/graph/badge.svg?token=U1F2477BLC)](https://codecov.io/gh/Inferara/soroban-ret)
[![soroban-ret on crates.io](https://img.shields.io/crates/v/soroban-ret.svg?label=soroban-ret)](https://crates.io/crates/soroban-ret)
[![soroban-ret-cli on crates.io](https://img.shields.io/crates/v/soroban-ret-cli.svg?label=soroban-ret-cli)](https://crates.io/crates/soroban-ret-cli)

# Reverse-engineering tool for Stellar Soroban smart contracts

## Status

Early development. The full five-stage pipeline is implemented. Small and
mid-size contracts — arithmetic, storage, custom types, events, auth,
cross-contract calls — decompile end-to-end into Rust that compiles back for
`wasm32v1-none` and behaves identically to the original under the Soroban host
(38 of the 39 fixtures compile back; `test_liquidity_pool` is the current
exception, and every executed fixture matches the original's behavior). Large
mainnet contracts recover correct interfaces but only partial bodies.

**Read the output as a reconstruction, not as the original source.** Two parts
of it carry very different confidence:

- **Signatures, types, error enums and events are recovered, not inferred.**
  They come from the contract's own `contractspecv0` metadata section, which
  the SDK embeds at build time. Cross-checked on every contract by the
  spec-consistency gate.
- **Function bodies are inferred from bytecode.** Where a value cannot be
  proven, the decompiler emits a `todo!("unknown value")` hole rather than a
  guess. Fabricating plausible stand-ins — empty collections, invented storage
  keys, tag-only symbols — is treated as a **bug class**, not a nicety: see
  [#36](https://github.com/Inferara/soroban-ret/issues/36) and the v0.0.4
  entries in [`CHANGELOG.md`](CHANGELOG.md). A hole is honest; a wrong value
  that compiles is not.

Stages:

- **Stage 1** — WASM parsing: sections, imports, exports, function bodies, data segments, custom sections (`contractspecv0`, `contractmetav0`, `contractenvmetav0`).
- **Stage 2** — Spec extraction: typed lookup tables for functions, structs, unions, enums, error enums, and events from the contract's `contractspecv0` XDR; SEP-41 / Stellar Asset standard-interface detection; SDK version from `contractmetav0`.
- **Stage 3** — Pattern matcher: host-call lifting, control-flow structurization, dispatch peeling, wrapper detection, loop-structure recovery (carried-seed admissibility, vec accumulators, const-loop evaluation).
- **Stage 4** — IR optimizer + post-optimization passes: constant folding, has/get fusion, storage-key recovery (including `DataKey` constructors evaluated against real frame state), fallible/defaulting storage-getter recovery, checked-arithmetic restoration, enum-key construction, event-publish recovery, auth/cross-contract repair, dead-code elimination.
- **Stage 5** — Rust source emitter: type definitions via `soroban-spec-rust`, function bodies, module assembly with `#[contract]`/`#[contractimpl]`, formatting via `prettyplease`.

## Browser Usage

Most parts of the Reverse Engineering Tool can be accessed directly via the [Stellar Security Portal](https://stellarsecurityportal.com/dev-tools).

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
| `--report` | Emit per-contract recovery signals as JSON and exit (see [below](#per-contract-recovery-signals)) |
| `--generic` | Force generic WASM mode (no Soroban assumptions) |
| `-v, --verbose` | Enable debug logging |

`--info` short-circuits before decompilation, so it cannot be combined with
`--spec-only`, `--generic` or `--report`.

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
use soroban_ret::wasm::validate::validate_soroban;

let module = WasmModule::parse(&wasm)?;
let registry = TypeRegistry::from_wasm(&wasm)?;

// Diagnostics for non-Soroban-compliant constructs (floats, reference types,
// multi-memory, `call_indirect`, …). `parse_diagnostics` is a public *field*
// carrying what stage 1 noticed while parsing; `validate_soroban` runs the
// full check over an already-parsed module.
for diag in &module.parse_diagnostics {
    eprintln!("parse: {diag}");
}
let report = validate_soroban(&module);
println!("soroban-compliant: {}", report.is_soroban_compliant());
```

To measure how much of a contract was recovered, use `decompile_to_ir`, which
exposes the lifted module before codegen:

```rust
let ir = soroban_ret::decompile_to_ir(&wasm)?;
for func in &ir.contract_module.functions {
    // An empty body plus `had_host_calls` means real logic was lost during
    // lifting — not an identity passthrough.
    if func.body.is_empty() && func.had_host_calls {
        eprintln!("logic lost: {}", func.name);
    }
}
```

### Per-contract recovery signals

Every decompile carries a [`RecoveryReport`](crates/soroban-ret/src/recovery.rs)
answering "how much of *this* contract came back?" — computed from the contract
in front of you, with no corpus or baseline involved:

```rust
let result = soroban_ret::decompile_with_options(&wasm, &options)?;
let r = &result.recovery;

println!("{}", r.summary());        // "38 of 75 functions fully recovered · 379 unresolved holes"
println!("holes: {}", r.holes());   // total todo!()/var_N markers
println!("lost:  {}", r.lost());    // functions whose logic is gone

for f in r.lost_functions() {
    // Surface these loudly: the body on screen does not represent on-chain behavior.
    eprintln!("  {} [{}]", f.name, f.status.label());
}
```

The same data is available from the CLI as JSON, for UIs that shell out:

```bash
soroban-ret contract.wasm --report
```

It reports **counts, not a "recovered %"** — deliberately. The corpus figures in
[Validation](#validation) are corpus means and do not describe any individual
contract, so a per-contract percentage derived from them would overstate.
`"38 of 75 functions fully recovered · 379 unresolved holes"` is checkable
against the source beside it.

These counts grade **completeness, not correctness**: a function reported as
fully recovered contains no unrecovered nodes, which does not make its logic
right. Pair them with an "experimental / reconstruction" caveat. Enable the
`serde` feature to serialize the types.

## Build from source

Requires a stable Rust toolchain (MSRV 1.95.0, declared in the workspace
`Cargo.toml`). The three heavy gates additionally need the
`wasm32v1-none` target (`rustup target add wasm32v1-none`), since they compile
decompiled output back into a real contract.

```bash
git clone https://github.com/Inferara/soroban-ret.git
cd soroban-ret

cargo build --workspace
cargo test --workspace
cargo run -p soroban-ret-cli -- path/to/contract.wasm
```

Note the CLI binary is built from `soroban-ret-cli`, not `soroban-ret` —
`cargo build -p soroban-ret` will not refresh it.

## Validation

`cargo test --workspace` runs the fast gates by default:

- **Accuracy** — interface similarity vs the SDK reference sources: **98.3 %** over 37 scored contracts (2 skipped for lacking a reference source).
- **Spec-consistency** — generated signatures/types vs each contract's own `contractspecv0`, across all 63 contracts including the mainnet corpus, which has no reference source: **0** dropped/extra functions, **0** arity mismatches, mean signature similarity **98.9 %**.
- **Structural plausibility** — a ratchet on per-contract recovery vs `benchmark-data/baseline.json` (corpus mean restoration **92.4 %**).

Three heavier gates compile decompiled output back for `wasm32v1-none` and are opt-in via env var (also run in CI):

```bash
# ≥95% of fixtures recompile (cargo check) — currently 38/39 = 97%
SOROBAN_RET_COMPILE_BACK=1 cargo test -p soroban-ret --test compile_back

# mainnet corpus hard-error ratchet — currently 326 errors, 3 of 24 clean
SOROBAN_RET_CORPUS_SOUNDNESS=1 cargo test -p soroban-ret --test corpus_soundness

# functional equivalence: recompile to wasm, run BOTH the original and
# recompiled contract through soroban-env-host, and diff their outputs
# — currently 99.2% behavioral match, 4 divergences
SOROBAN_RET_EQUIV=1 cargo test -p soroban-ret-equiv --test equivalence
```

These three are **error-count ratchets pinned to rustc 1.95.0**
(`RUSTUP_TOOLCHAIN`, as in CI): rustc diagnostics drift across floating
`stable` releases, so numbers measured on another toolchain are not comparable.

> **These are corpus metrics, not per-contract guarantees.** 92.4 % is an
> equal-weight mean across 24 mainnet contracts, and it is *correctness-blind* —
> it grades how much lifted to concrete Rust, not whether the result is right.
> 99.2 % is a match rate over the narrow slice the equivalence harness can
> actually execute (scalar-argument functions on contracts whose output
> recompiles — 3 of the 24 corpus contracts today). Neither figure transfers to
> an arbitrary contract; for a per-contract signal use
> [`DecompileResult::recovery`](#per-contract-recovery-signals), which is
> computed from that contract alone.

All four remaining equivalence divergences are honest `todo!()` holes that trap,
not fabricated values. See [`docs/pattern-coverage.md`](docs/pattern-coverage.md)
for each gate's scope, methodology and current baseline.

## Roadmap

| Stage | Scope | Status |
|---|---|---|
| 1 | WASM parser | done |
| 2 | Spec extractor + standard-interface detector | done |
| 3 | Pattern matcher: host-call lifting, control-flow structurization, wrapper detection | done (partial) |
| 4 | IR optimizer + post-optimization passes | done (partial) |
| 5 | Rust source emitter | done (partial) |

"Partial" no longer means missing patterns — the sixteen tracked patterns are
implemented and tested. It means **lost dataflow**: on large mainnet contracts
the lifter cannot always prove where a value came from, so it emits a hole
instead of a guess. The frontier is tracked as open issues:

- [#34](https://github.com/Inferara/soroban-ret/issues/34) — no memory-SSA /
  reaching-definitions: values lost across branches, calls and deep helpers
  (the master lever).
- [#66](https://github.com/Inferara/soroban-ret/issues/66) /
  [#67](https://github.com/Inferara/soroban-ret/issues/67) — lost guard
  conditions, the 500+ `if todo!("unknown value")` class.
- [#68](https://github.com/Inferara/soroban-ret/issues/68) — `aqua-rewards`
  checkpoint/derivation math.
- [#69](https://github.com/Inferara/soroban-ret/issues/69) — the final 4
  equivalence divergences.

Allowance / balance helper recovery is shipped but **not yet validated** — no
fixture exercises it. Trait-based contracts are recovered as a flat
`impl Contract`, which is not a gap but a limit of the format: `contractspecv0`
carries no trait entry, so the trait shape is erased at compile time and cannot
be recovered from bytecode.

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
