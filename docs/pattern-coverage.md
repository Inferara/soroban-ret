# Pattern Coverage

## Scope

This document is the auditable artifact of the `soroban-ret` development plan.

The sixteen items are:

> Struct pack/unpack · Enum dispatch · Integer enum · Tuple struct · Error
> handling · Auth · Event · Cross-contract call · Crypto · Control flow
> reconstruction · Variable naming heuristics · Constructor · Check-auth ·
> Function body codegen (complex) · Validate Level 3 contracts · Validate
> Level 4 contracts

All file paths below are relative to the repository root.

## Pattern coverage table

| # | Pattern | Code | Fixture(s) | Test(s) |
|---|---|---|---|---|
| 1 | Struct pack/unpack | `crates/soroban-ret/src/pattern/lifter.rs:5478` `detect_load_struct_wrapper`; `:5749` `detect_map_unpack_decode_wrapper`; `:5918` `detect_struct_construct_wrapper`; `crates/soroban-ret/src/pipeline.rs:5282` Stage 4s | `tests/fixtures/test_udt.wasm`, `tests/fixtures/test_liquidity_pool.wasm` | `test_decompile_udt`, `test_decompile_liquidity_pool_keys` |
| 2 | Enum dispatch | `crates/soroban-ret/src/pattern/lifter.rs:7146` `detect_enum_dispatch_wrapper`; `:4041` `symbol_index_in_linear_memory` handler reading the CASES array | `tests/fixtures/test_constructor.wasm`, `tests/fixtures/contract_with_constructor.wasm`, `tests/fixtures/test_liquidity_pool.wasm` | `test_decompile_constructor`, `test_decompile_contract_with_constructor`, `test_decompile_liquidity_pool_keys` |
| 3 | Integer enum | `crates/soroban-ret/src/pipeline.rs:445` Stage 4j (integer enum cast arm recovery) | `tests/fixtures/test_errors.wasm` (`Flag` is a `u32`-discriminant enum) | `test_decompile_errors` — asserts `if flag == Flag::A` / `else if flag == Flag::C` / `else if flag == Flag::D` chain and `A = 0` … `E = 4` discriminants |
| 4 | Tuple struct | `crates/soroban-ret/src/pattern/lifter.rs:5392` `detect_vec_unpack_wrapper` | `tests/fixtures/test_tuples.wasm`, `tests/fixtures/test_udt.wasm` | `test_decompile_tuples` (asserts `(u32, i64)`) |
| 5 | Error handling | `crates/soroban-ret/src/ir/soroban_ir.rs:134` `SorobanExpr::ContractError`; `crates/soroban-ret/src/codegen/functions.rs:533` codegen for `panic_with_error!` and `Error::from_contract_error(N)` | `tests/fixtures/test_errors.wasm` | `test_decompile_errors` — asserts `#[contracterror]`, `AnError = 1`, `panic_with_error!`, `from_contract_error`, `Result<Symbol, Error>` |
| 6 | Auth | `crates/soroban-ret/src/ir/soroban_ir.rs:77` `SorobanExpr::RequireAuth`; `:78` `RequireAuthForArgs`; `crates/soroban-ret/src/pattern/host_calls.rs:102,107` host-call lifting; `crates/soroban-ret/src/pipeline.rs:601` Stage 4x (RequireAuth + EnumConstruct fixup) | `tests/fixtures/test_auth.wasm`, `tests/fixtures/test_account.wasm` | `test_decompile_auth` — asserts `a.require_auth()` and the in-order chain `require_auth_for_args` → `invoke_contract` in `fn2` |
| 7 | Event | `crates/soroban-ret/src/ir/soroban_ir.rs:85` `SorobanExpr::PublishEvent`; `crates/soroban-ret/src/pipeline.rs:465` Stage 4l (event publish recovery) | `tests/fixtures/test_events.wasm`, `tests/fixtures/test_events_ref.wasm` | `test_decompile_events`, `test_decompile_events_ref`, `snapshot_test_events` — asserts `#[contractevent]`, `pub struct Transfer`, `#[topic]`, in-fn `.publish(&env)` ordering |
| 8 | Cross-contract call | `crates/soroban-ret/src/ir/soroban_ir.rs:92` `SorobanExpr::InvokeContract`; `:100` `TryInvokeContract`; `crates/soroban-ret/src/pipeline.rs:302` Stage 4b (cross-contract return type inference) | `tests/fixtures/test_invoke_contract.wasm`, `tests/fixtures/test_import_contract.wasm` | `test_decompile_invoke_contract`, `test_decompile_import_contract` — asserts `env.invoke_contract::<i32>` with `vec![&env, x.into_val(&env), y.into_val(&env)]` argument order |
| 9 | Crypto | `crates/soroban-ret/src/pattern/host_calls.rs:170` `lift_crypto_call` (BLS12-381 g1/g2/msm/pairing, BN254, SHA-256, Keccak-256, Ed25519, secp256k1); `crates/soroban-ret/src/codegen/types.rs:168` `generate_type_ident_crypto` (Bls12381Fp, Bls12381Fp2, Bls12381G1Affine, Bls12381G2Affine, Bn254G1Affine, Bn254G2Affine, Fr type aliases) | `tests/fixtures/test_bls.wasm`, `tests/fixtures/test_bn254.wasm` | `test_decompile_bls`, `test_decompile_bn254` — asserts `Bls12381` / `Bn254` aliases, `soroban_sdk::crypto::{bls12_381, bn254}` imports, `env.crypto().bls12_381() / .bn254()` dispatch |
| 10 | Control flow reconstruction | `crates/soroban-ret/src/pattern/structurize.rs:39` `structurize`; `crates/soroban-ret/src/ir/optimizer.rs:665` `collapse_trivial_loops`; `crates/soroban-ret/src/pattern/lifter.rs` BrIf guard-chain handling, match-arm continuation reattachment, phi-merge recovery | `tests/fixtures/test_errors.wasm` (br_table → if-chain), `tests/fixtures/test_auth.wasm`, `tests/fixtures/test_fuzz.wasm` | `test_decompile_errors` (if-chain shape), `test_decompile_auth_control_flow` (no residual `loop {`), `test_decompile_fuzz` |
| 11 | Variable naming heuristics | `crates/soroban-ret/src/ir/optimizer.rs:4547` `propagate_variable_names`; `:4891` `deshadow_variable_names` | exercised indirectly by every fixture (30) | `test_all_fixtures_no_artifacts` (negative regression sweep across all fixtures: no `var_N`, no `todo!("unknown value")`, no `todo!("host call`) |
| 12 | Constructor | `crates/soroban-ret/src/pattern/dispatch.rs:30` `__constructor` detection; `crates/soroban-ret/src/ir/high_level_ir.rs:62` `ContractFn::is_constructor`; `crates/soroban-ret/src/codegen/module.rs` constructor emission | `tests/fixtures/test_constructor.wasm`, `tests/fixtures/contract_with_constructor.wasm`, `tests/fixtures/test_liquidity_pool.wasm` | `test_decompile_constructor`, `test_decompile_contract_with_constructor` (asserts in-order DataKey variants + storage tier writes), `test_decompile_liquidity_pool_keys`, `snapshot_contract_with_constructor` |
| 13 | Check-auth | `crates/soroban-ret/src/pattern/dispatch.rs:31` `__check_auth` detection; `crates/soroban-ret/src/ir/high_level_ir.rs:63` `ContractFn::is_check_auth`; `crates/soroban-ret/src/codegen/imports.rs` `auth::Context` import injection | `tests/fixtures/test_account.wasm` | `test_decompile_account` — asserts `__check_auth`, `auth::Context`, `Vec<Context>` |
| 14 | Function body codegen (complex) | `crates/soroban-ret/src/codegen/functions.rs` (≈1.4 kLOC: tail-expression returns, `let mut … = match`/`if` combining, while-loop emission, nested struct construction, match arm tail-expression promotion, `Result` wrapping) | every Level 3+4 fixture exercises a non-trivial body | implicit via every full-body test; explicit shapes in `test_decompile_liquidity_pool_keys`, `test_decompile_udt`, `test_decompile_contract_with_constructor` |
| 15 | Validate Level 3 (udt, errors, events, constructor) | n/a — validation deliverable | `tests/fixtures/test_udt.wasm`, `tests/fixtures/test_errors.wasm`, `tests/fixtures/test_events.wasm`, `tests/fixtures/test_constructor.wasm` | `test_decompile_udt`, `test_decompile_errors`, `test_decompile_events`, `test_decompile_constructor`, plus `snapshot_test_errors` and `snapshot_test_events` |
| 16 | Validate Level 4 (auth, account, invoke_contract) | n/a — validation deliverable | `tests/fixtures/test_auth.wasm`, `tests/fixtures/test_account.wasm`, `tests/fixtures/test_invoke_contract.wasm` | `test_decompile_auth`, `test_decompile_auth_control_flow`, `test_decompile_account`, `test_decompile_invoke_contract` |

## Methodology

Each pattern's test uses a combination of:

- **Positive assertion** on output shape via either:
  - `assert!(source.contains(…))` for single substrings;
  - `assert_ordered(haystack, label, &[…needles…])` for top-level declaration
    order (e.g. `#[contracttype]` before `#[contract]`);
  - `assert_in_fn(source, fn_signature, &[…needles…])` to confirm that
    a sequence of needles appears *inside the body of a specific function*,
    in order. Function bodies are extracted by brace-counting from the
    function signature.
- **Negative assertion** on artifact absence — every Level 3+ test ends with
  `assert!(!source.contains("todo!("))`, and the global
  `test_all_fixtures_no_artifacts` test walks all 30 fixtures asserting that
  none emits `todo!("unknown value")`, `todo!("host call`, or `var_N`
  temporary names.
- **Snapshot regression** via `insta` for the three most attribute-heavy
  fixtures (`test_errors`, `test_events`, `contract_with_constructor`). The
  snapshots are stored under
  `crates/soroban-ret/tests/snapshots/integration__*.snap` and freeze the
  full decompiled source (line breaks, attribute order, trailing newlines).
  Run `cargo insta review` to accept intentional changes.

Every claim in the pattern coverage table maps to a concrete test function
the reader can `rg` for inside `crates/soroban-ret/tests/integration.rs`.

## Known incomplete patterns

These are documented up-front rather than hidden behind the validation
checkbox:

- **Logging body recovery is best-effort.** The `log!` macro is stripped at
  compile time, so there is no Soroban host call to detect; only the function
  signature and surrounding scaffolding can be recovered. `test_logging.wasm`
  asserts the function signature only.
- **Allowance / balance helper recovery is shipped but partially validated.**
  `detect_balance_helper_wrapper`, `detect_spend_allowance_wrapper`, and
  `detect_write_allowance_wrapper` are present in
  `crates/soroban-ret/src/pattern/lifter.rs` (line 6191+). Full validation is
  planned in the `v0.0.3`.
- **Storage key recovery for unmodelled cross-contract returns falls back to
  heuristics.** When a remote `invoke_contract` return type cannot be
  inferred from the local spec, the post-optimization Stage 4b runs a small
  set of heuristics; pathological cases may emit `UnknownVal` (treated as
  `todo!(` artifact and caught by the negative regression test).
- **`#![no_std]` reformatting of pretty-printed output is best-effort.**
  Module-level attributes are written in a specific order; the snapshot tests
  guard against unintended reordering.

## Where to look next

- Source for the tests above: `crates/soroban-ret/tests/integration.rs`.
- Smoke list of every fixture exercised today:
  `ALL_FIXTURES` constant in the same file (30 entries).
- Snapshots: `crates/soroban-ret/tests/snapshots/`.
- For **quantitative** accuracy measurement (per-contract scoring against a
  reference Rust source), see the `soroban-ret-accuracy` crate planned in
  the `v0.0.3`.
