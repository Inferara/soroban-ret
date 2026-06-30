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
  reference Rust source), see the `soroban-ret-accuracy` crate
  (`cargo run -p soroban-ret-accuracy --bin accuracy`).

## Tranche 3: accuracy framework, compile-fidelity & known gaps

### Accuracy measurement (`soroban-ret-accuracy`)

The `soroban-ret-accuracy` crate scores each fixture's decompiled output against
its canonical SDK source using `syn`-based interface extraction and weighted
component comparison (types 25 %, signatures 20 %, annotations 15 %, bodies 30 %,
structure 10 %). Reference sources come from the **`vendor/rs-soroban-sdk`
submodule pinned to v26.0.1** (commit `f52b6aa…`), the exact SDK version+commit
every fixture reports in `contractmetav0`.

> **What the score means (and doesn't).** Each component is a *recall* measure:
> it checks that the decompiled output *contains* the reference's interface and
> body operation-kinds (e.g. an `if`, a `match`, a `panic`, a `.persistent().set`),
> not that the logic is semantically equivalent. Extra or wrong operations are not
> penalized, and a 100 % score is **not** a behavioral-equivalence proof — it means
> "every operation kind the reference uses is present." The complementary
> `scripts/check-compilable.sh` gate is the "does it actually build" check.

- `cargo run -p soroban-ret-accuracy --bin accuracy` — table report.
- `… -- --json > accuracy-baseline.json` — machine-readable baseline.
- `… -- --against accuracy-baseline.json --tolerance 0.5` — regression gate
  (exit 1 if any contract drops > 0.5 pp from the committed baseline).

Current status (v26.0.1): **98.3 % overall** over 37 scored contracts
(`liquidity_pool` is skipped for lacking a reference source), every complexity
level meets its target (L1 = 100 %, L2 = 100 %, L3 = 100 %, L4 = 100 %,
L5 = 96.6 % ≥ 80 %). `import_contract` (74.3) and `logging` (70.0, release WASM
strips `log!`) sit below their individual level targets but are absorbed by the
level averages. The committed baseline is `accuracy-baseline.json` at the repo
root; refresh it via an explicit PR when output changes intentionally.

### Compile-back fidelity (`scripts/check-compilable.sh`)

The accuracy metric is interface/fingerprint-based and does **not** check that
output compiles. `scripts/check-compilable.sh` decompiles every fixture and runs
`cargo check --target wasm32v1-none` against `soroban-sdk` (pin `=26.0.1`); the
`compile_back` test gate (`SOROBAN_RET_COMPILE_BACK=1`) wraps it with a 95 %
floor. Current status: **38/38 non-skipped compile (100 %)**, including
`test_liquidity_pool` (its earlier `E0284 into_val` type-inference failure has
since been resolved). `test_liquidity_pool` is still *skipped by the accuracy
metric* — for lack of a reference source to score against, which is unrelated to
compile-back. Two earlier compile-fidelity codegen fixes landed in
`crates/soroban-ret/src/ir/optimizer.rs`:

- **`remove_val_tag_guards`** strips SDK argument-validation guards of the shape
  `if v.get_tag() != Tag::X { panic!() }`. The lifter's `ValTag`/`ValTagName`
  recovery surfaced these, but `Val::get_tag()` and `Tag` are not public
  `soroban_sdk` API, so they did not compile. The typed parameter already
  implies the check; the SDK re-inserts the marshalling on rebuild.
- **Orphan linear-memory marshalling removal** (in `remove_orphan_host_calls`)
  drops standalone `*_to_linear_memory` / `*_from_linear_memory` host calls
  (e.g. `map_unpack_to_linear_memory`) whose result is discarded — pure SDK
  (de)serialization that codegen rendered as non-public `env.map()…` API.

### Spec-consistency (`tests/spec_consistency.rs`)

Beyond *interface similarity vs a reference source* (the accuracy metric, which
only covers the SDK fixtures), this gate checks the generated Rust against the
contract's **own** `contractspecv0` — so it covers **every** contract including
the 24 mainnet corpus contracts that have no reference source. It builds the
expected interface from the spec (via the same `generate_type_ident` codegen
uses) and asserts, across all 63 contracts (39 fixtures + 24 corpus): **0**
dropped/extra functions and **0** arity mismatches, with mean signature
similarity **~99 %** and type similarity **~99 %**. Runs in the default
`cargo test` (decompile + `syn`, no wasm build).

### Structural plausibility (`crates/soroban-ret-bench/tests/plausibility.rs`)

Turns the corpus restoration numbers — previously *report-only* in
`benchmark.yml` — into an asserted ratchet against `benchmark-data/baseline.json`.
Fails if any corpus contract regresses (fewer clean functions, more logic-lost
functions, or more decompilation artifacts). Improvements pass; an intentional
change refreshes the baseline (`scripts/rebuild-benchmark-baseline.sh`). Runs in
the default `cargo test`.

### Functional equivalence (`crates/soroban-ret-equiv`, `SOROBAN_RET_EQUIV=1`)

The strongest check: it **recompiles** decompiled output to a real `.wasm`
(`cargo build --target wasm32v1-none`), registers BOTH the original and
recompiled contract in a `soroban-sdk` test host (`soroban-env-host`), invokes
each scalar-invocable exported function with boundary + seeded-random inputs,
and compares the outcomes (lowered to canonical `ScVal`). A divergence is a
decompiler correctness limitation; the gate is a ratchet on the divergence
count, like the corpus-soundness gate.

Current baseline: **63 functions / 474 cases executed; 63 contracts checked
(39 fixtures + all 24 mainnet corpus, of which 22 do not yet recompile and are
reported as `not_recompilable`), 99.2 % behavioral match, 4 known
divergences** — the sole remaining decompiler limitation the harness surfaced:
`test_alloc::num_list` loses its populate-loop and returns an empty `Vec`.
(Previously 60 / 87.3 %; the fallible-storage-get recovery in the lifter
eliminated `unknown-oracle`'s 56 empty-storage divergences — getters whose value
and missing-key contract-error branch were lost to a `has`/`extend_ttl` +
`todo!()` husk now recover `env.storage().<dur>().get(&key).ok_or(Error::Variant)`
with the error code read from the helper's bytecode. Before that, 75 / 82.3 % → 60
came from the `checked_add`/`checked_sub` → `.ok_or(..)` recovery.)

**Coverage is intrinsically limited** (by design): only functions invocable with
generated scalar arguments and no required storage/auth state are executed;
aggregate/UDT-argument functions, and the renamed `__constructor`/`__check_auth`,
are skipped, as are contracts whose output does not recompile. It is a
correctness sanity-check + behavioral-match metric, not a full-corpus
differential test.

### Known gaps

- **Trait-based contracts decompile to a flat `impl Contract`.** Contracts
  written with `#[contractimpl(contracttrait)]` / `impl Trait for Contract`
  (the `contracttrait_*` and `associated_types*` fixtures) carry **no** trait
  information in the compiled WASM: `contractspecv0` (XDR `ScSpecEntry`) has only
  `FunctionV0`/`UdtStructV0`/`UdtUnionV0`/`UdtEnumV0`/`UdtErrorEnumV0`/`EventV0`
  — there is no trait-function entry, and the trait name/membership is erased at
  compile time (verified: no trait strings in any contracttrait fixture). The
  decompiler therefore emits a semantically-equivalent flat impl, which compiles
  and scores 100 % on the accuracy metric. Recovering the original
  `trait T { … } impl T for Contract` shape is **not possible** from the bytecode
  alone and is out of scope.
