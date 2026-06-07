# Mainnet contract corpus (benchmark data)

Real Soroban contracts pulled straight from **Stellar mainnet** (`public`
network) for testing/benchmarking the decompiler against production bytecode.

The set is the curated [Stellar Lab mainnet contract-list][lab] — the most
notable live protocols: oracles (Band, Reflector, Lightecho), AMMs
(Soroswap, Phoenix, Aqua, Comet), the full **Blend** lending suite, **FxDAO**,
Soroban Domains, XycLoans, and a few Stellar Asset Contracts.

[lab]: https://lab.stellar.org/smart-contracts/contract-list?$=network$id=mainnet

## Contents

| | |
|---|---|
| Contracts listed   | 28 |
| WASM downloaded     | 24 (**22 unique** binaries) |
| Stellar Asset Contracts | 4 — built-in SAC, no uploaded WASM (BLND Token, XLM/PHO/USDC SAC) |
| Missing / archived  | 0 |

Two pairs share identical bytecode (recorded in `manifest.json` → `shared_wasm`):
- both **Reflector** oracle instances
- **Blend Fixed Pool** and **Blend Yieldblox Pool** (same pool WASM)

Each code-bearing contract is one file named `<entity>-<contract-id-prefix>.wasm`.
`manifest.json` is the source of truth: per-contract entity name, full contract
id, executable kind, WASM hash, file name, byte size, and `sha256_verified`.

## Integrity

A contract's WASM hash **is** the sha256 of its code, so every file is
self-verifying:

```bash
shasum -a 256 reflector-CAFJZQWS.wasm
# == the wasm_hash for that contract in manifest.json
```

The fetcher checks this on download and refuses to write a mismatching file.

## Refreshing / extending

```bash
python3 scripts/fetch_benchmark_wasm.py
```

Resolves each `C...` id → contract instance → `ContractExecutable` → WASM via
public Soroban RPC (`getLedgerEntries`), then writes the files + manifest here.
To add contracts, append `(entity, contract_id)` rows to `CONTRACTS` in that
script and re-run. SACs are reported and skipped (they have no uploaded code).

## Quick smoke test

All 24 binaries decompile without error:

```bash
for f in benchmark-data/mainnet/*.wasm; do target/release/soroban-ret "$f" >/dev/null || echo "FAIL $f"; done
```

## Restoration benchmark

This corpus drives `soroban-ret-bench` — a **reference-free** benchmark (mainnet
binaries have no original source). For each contract it computes a *restoration
%* = the mean per-exported-function recovery (concrete Rust vs. `todo!()` /
unknown markers), plus artifact counts and Stage-1 disassembly time.

```bash
# Table to stdout for the default corpus (benchmark-data/mainnet):
cargo run -p soroban-ret-bench

# Full self-contained HTML dashboard + JSON, diffed against the committed baseline:
cargo run -p soroban-ret-bench -- \
  --against benchmark-data/baseline.json \
  --html benchmark-report.html --json benchmark-results.json
```

`baseline.json` (one directory up) is the committed snapshot every PR is diffed
against to mark **improved / reduced / no-change**; the `Benchmark` GitHub
Action posts that table on each PR and refreshes the baseline on merge to
`main`. Regenerate it manually with `scripts/rebuild-benchmark-baseline.sh`.

The headline % is deliberately graded per function, so a large body with a few
`todo!()`s still scores high — watch the **Artifacts** column for the sharper,
per-`todo!()` development signal.
