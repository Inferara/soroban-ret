# Test Fixtures

This directory holds the WASM contracts used by `crates/soroban-ret/tests/integration.rs`
and `crates/soroban-ret-cli/tests/cli.rs`. Each `.wasm` file is a real Soroban
SDK build artifact — not synthetic — so the integration suite exercises the
decompiler against representative output from the upstream toolchain.

## Provenance

Most fixtures come from the Stellar `rs-soroban-sdk` test suite (the SDK ships
contracts under `soroban-sdk/test_contracts/` and `soroban-sdk-macros/test_contracts/`
that are built into `.wasm` for the SDK's own integration tests). A few come from
`soroban-examples`. The fixtures here were captured from those upstream sources
at the SDK version reported by each fixture's own `contractmetav0` section —
run `soroban-ret --info <fixture>` to read it back.

| Fixture | Origin | Demonstrates |
|---|---|---|
| `contract.wasm` | rs-soroban-sdk | Minimal `#[contract]` smoke contract |
| `contract_with_constructor.wasm` | rs-soroban-sdk | `__constructor` entry point |
| `test_account.wasm` | rs-soroban-sdk | `__check_auth` custom-account contract |
| `test_add_i128.wasm` | rs-soroban-sdk | i128 arithmetic shape |
| `test_add_u128.wasm` | rs-soroban-sdk | u128 arithmetic shape |
| `test_add_u64.wasm` | rs-soroban-sdk | u64 arithmetic shape |
| `test_alloc.wasm` | rs-soroban-sdk | Allocator-using contract |
| `test_auth.wasm` | rs-soroban-sdk | `require_auth` / `require_auth_for_args` |
| `test_constructor.wasm` | rs-soroban-sdk | `__constructor` with state setup |
| `test_contract_data.wasm` | rs-soroban-sdk | persistent/temporary/instance storage |
| `test_empty.wasm` | synthetic | Smallest possible contract (1-fn no-op) |
| `test_empty2.wasm` | synthetic | Empty contract for boundary testing |
| `test_errors.wasm` | rs-soroban-sdk | `#[contracterror]` enum + `Result<T, E>` |
| `test_events.wasm` | rs-soroban-sdk | `#[contractevent]` + `Topics::publish` |
| `test_events_ref.wasm` | rs-soroban-sdk | Events with reference data |
| `test_fuzz.wasm` | rs-soroban-sdk | Fuzz target contract |
| `test_generics.wasm` | rs-soroban-sdk | Generic functions in contractimpl |
| `test_import_contract.wasm` | rs-soroban-sdk | `#[contractclient]` cross-import |
| `test_invoke_contract.wasm` | rs-soroban-sdk | `env.invoke_contract::<T>` cross-call |
| `test_liquidity_pool.wasm` | soroban-examples | Larger real-world contract |
| `test_logging.wasm` | rs-soroban-sdk | `log!` macro |
| `test_macros.wasm` | rs-soroban-sdk | macro-heavy patterns |
| `test_modular.wasm` | rs-soroban-sdk | Multi-module contract |
| `test_multiimpl.wasm` | rs-soroban-sdk | Multiple `#[contractimpl]` blocks |
| `test_mutability.wasm` | rs-soroban-sdk | Mutable bindings |
| `test_tuples.wasm` | rs-soroban-sdk | Tuple parameters and returns |
| `test_udt.wasm` | rs-soroban-sdk | `#[contracttype]` structs/enums/tuples |
| `test_zero.wasm` | synthetic | Trivial-body boundary case |

## Regeneration

There is no automated rebuild script yet — these are pinned binaries committed
to the repo so the integration suite is hermetic. To regenerate:

1. Clone the SDK at the version you want to target:
   ```bash
   git clone --depth 1 --branch v22.0.0 https://github.com/stellar/rs-soroban-sdk
   ```
2. Build the SDK test contracts (the SDK has its own `Makefile` /
   `cargo xtask` flow that produces `.wasm` outputs into a `target/` subtree).
3. Copy the resulting `.wasm` files into this directory, preserving the
   filenames in the table above.
4. Run `cargo test -p soroban-ret --test integration` and review any diffs.

For `soroban-examples`-origin fixtures, follow the same flow against
`https://github.com/stellar/soroban-examples`.

## Adding a new fixture

1. Drop the `.wasm` here with a descriptive `test_*.wasm` name.
2. Add a row to the table above explaining where it came from and what it
   exercises.
3. Add the filename to the `ALL_FIXTURES` constant in
   `crates/soroban-ret/tests/integration.rs`.
4. Either add a targeted assertion in `integration.rs` or rely on the
   generic `test_all_fixtures_decompile` / `test_all_fixtures_no_artifacts`
   sweeps to verify no panics and no `var_N` / `todo!(...)` placeholders
   leak into the output.
