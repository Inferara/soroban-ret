# Pattern Coverage

## Scope

This document is the auditable artifact of the `soroban-ret` development plan.

The sixteen items are:

> Struct pack/unpack · Enum dispatch · Integer enum · Tuple struct · Error
> handling · Auth · Event · Cross-contract call · Crypto · Control flow
> reconstruction · Variable naming heuristics · Constructor · Check-auth ·
> Function body codegen (complex) · Validate Level 3 contracts · Validate
> Level 4 contracts

All file paths below are relative to the repository root. Code references name
the **file and the item** (a `fn`, an enum variant, or a `Stage 4x` comment)
rather than a line number: the lifter and pipeline churn constantly, so line
numbers rot within a commit or two. Every reference below is greppable —
`rg '<symbol>' crates/`.

## Pattern coverage table

| # | Pattern | Code | Fixture(s) | Test(s) |
|---|---|---|---|---|
| 1 | Struct pack/unpack | `crates/soroban-ret/src/pattern/lifter.rs` `detect_load_struct_wrapper`, `detect_map_unpack_decode_wrapper`, `detect_struct_construct_wrapper`; `crates/soroban-ret/src/pipeline.rs` Stage 4s | `tests/fixtures/test_udt.wasm`, `tests/fixtures/test_liquidity_pool.wasm` | `test_decompile_udt`, `test_decompile_liquidity_pool_keys` |
| 2 | Enum dispatch | `crates/soroban-ret/src/pattern/lifter.rs` `detect_enum_dispatch_wrapper`; the `(HostModule::Buf, "symbol_index_in_linear_memory")` handler reading the CASES array | `tests/fixtures/test_constructor.wasm`, `tests/fixtures/contract_with_constructor.wasm`, `tests/fixtures/test_liquidity_pool.wasm` | `test_decompile_constructor`, `test_decompile_contract_with_constructor`, `test_decompile_liquidity_pool_keys` |
| 3 | Integer enum | `crates/soroban-ret/src/pipeline.rs` Stage 4j (integer enum cast arm recovery) | `tests/fixtures/test_errors.wasm` (`Flag` is a `u32`-discriminant enum) | `test_decompile_errors` — asserts `if flag == Flag::A` / `else if flag == Flag::C` / `else if flag == Flag::D` chain and `A = 0` … `E = 4` discriminants |
| 4 | Tuple struct | `crates/soroban-ret/src/pattern/lifter.rs` `detect_vec_unpack_wrapper` | `tests/fixtures/test_tuples.wasm`, `tests/fixtures/test_udt.wasm` | `test_decompile_tuples` (asserts `(u32, i64)`) |
| 5 | Error handling | `crates/soroban-ret/src/ir/soroban_ir.rs` `SorobanExpr::ContractError`; `crates/soroban-ret/src/codegen/functions.rs` codegen for `panic_with_error!` and `Error::from_contract_error(N)` | `tests/fixtures/test_errors.wasm` | `test_decompile_errors` — asserts `#[contracterror]`, `AnError = 1`, `panic_with_error!`, `from_contract_error`, `Result<Symbol, Error>` |
| 6 | Auth | `crates/soroban-ret/src/ir/soroban_ir.rs` `SorobanExpr::RequireAuth`, `RequireAuthForArgs`; `crates/soroban-ret/src/pattern/host_calls.rs` `"require_auth"` / `"require_auth_for_args"` lifting; `crates/soroban-ret/src/pipeline.rs` Stage 4x (RequireAuth + EnumConstruct fixup) | `tests/fixtures/test_auth.wasm`, `tests/fixtures/test_account.wasm` | `test_decompile_auth` — asserts `a.require_auth()` and the in-order chain `require_auth_for_args` → `invoke_contract` in `fn2` |
| 7 | Event | `crates/soroban-ret/src/ir/soroban_ir.rs` `SorobanExpr::PublishEvent`; `crates/soroban-ret/src/pipeline.rs` Stage 4l (event publish recovery) | `tests/fixtures/test_events.wasm`, `tests/fixtures/test_events_ref.wasm` | `test_decompile_events`, `test_decompile_events_ref`, `snapshot_test_events` — asserts `#[contractevent]`, `pub struct Transfer`, `#[topic]`, in-fn `.publish(&env)` ordering |
| 8 | Cross-contract call | `crates/soroban-ret/src/ir/soroban_ir.rs` `SorobanExpr::InvokeContract`, `TryInvokeContract`; `crates/soroban-ret/src/pipeline.rs` Stage 4b (cross-contract return type inference) | `tests/fixtures/test_invoke_contract.wasm`, `tests/fixtures/test_import_contract.wasm` | `test_decompile_invoke_contract`, `test_decompile_import_contract` — asserts `env.invoke_contract::<i32>` with `vec![&env, x.into_val(&env), y.into_val(&env)]` argument order |
| 9 | Crypto | `crates/soroban-ret/src/pattern/host_calls.rs` `lift_crypto_call` (BLS12-381 g1/g2/msm/pairing, BN254, SHA-256, Keccak-256, Ed25519, secp256k1); `crates/soroban-ret/src/codegen/types.rs` `generate_type_ident_crypto` (Bls12381Fp, Bls12381Fp2, Bls12381G1Affine, Bls12381G2Affine, Bn254G1Affine, Bn254G2Affine, Fr type aliases) | `tests/fixtures/test_bls.wasm`, `tests/fixtures/test_bn254.wasm` | `test_decompile_bls`, `test_decompile_bn254` — asserts `Bls12381` / `Bn254` aliases, `soroban_sdk::crypto::{bls12_381, bn254}` imports, `env.crypto().bls12_381() / .bn254()` dispatch |
| 10 | Control flow reconstruction | `crates/soroban-ret/src/pattern/structurize.rs` `structurize`; `crates/soroban-ret/src/ir/optimizer.rs` `collapse_trivial_loops`; `crates/soroban-ret/src/pattern/lifter.rs` BrIf guard-chain handling, match-arm continuation reattachment, phi-merge recovery | `tests/fixtures/test_errors.wasm` (br_table → if-chain), `tests/fixtures/test_auth.wasm`, `tests/fixtures/test_fuzz.wasm` | `test_decompile_errors` (if-chain shape), `test_decompile_auth_control_flow` (no residual `loop {`), `test_decompile_fuzz` |
| 11 | Variable naming heuristics | `crates/soroban-ret/src/ir/optimizer.rs` `propagate_variable_names`, `deshadow_variable_names` | exercised indirectly by every fixture (40) | `test_all_fixtures_no_artifacts` (negative regression sweep across all fixtures: no `var_N`, no `todo!("unknown value")`, no `todo!("host call`) |
| 12 | Constructor | `crates/soroban-ret/src/pattern/dispatch.rs` `__constructor` detection; `crates/soroban-ret/src/ir/high_level_ir.rs` `ContractFn::is_constructor`; `crates/soroban-ret/src/codegen/module.rs` constructor emission | `tests/fixtures/test_constructor.wasm`, `tests/fixtures/contract_with_constructor.wasm`, `tests/fixtures/test_liquidity_pool.wasm` | `test_decompile_constructor`, `test_decompile_contract_with_constructor` (asserts in-order DataKey variants + storage tier writes), `test_decompile_liquidity_pool_keys`, `snapshot_contract_with_constructor` |
| 13 | Check-auth | `crates/soroban-ret/src/pattern/dispatch.rs` `__check_auth` detection; `crates/soroban-ret/src/ir/high_level_ir.rs` `ContractFn::is_check_auth`; `crates/soroban-ret/src/codegen/imports.rs` `auth::Context` import injection | `tests/fixtures/test_account.wasm` | `test_decompile_account` — asserts `__check_auth`, `auth::Context`, `Vec<Context>` |
| 14 | Function body codegen (complex) | `crates/soroban-ret/src/codegen/functions.rs` (≈3.8 kLOC: tail-expression returns, `let mut … = match`/`if` combining, while-loop emission, nested struct construction, match arm tail-expression promotion, `Result` wrapping) | every Level 3+4 fixture exercises a non-trivial body | implicit via every full-body test; explicit shapes in `test_decompile_liquidity_pool_keys`, `test_decompile_udt`, `test_decompile_contract_with_constructor` |
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
  `test_all_fixtures_no_artifacts` test walks all 40 fixtures asserting that
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
- **Allowance / balance helper recovery is shipped but still unvalidated.**
  `detect_balance_helper_wrapper`, `detect_spend_allowance_wrapper`, and
  `detect_write_allowance_wrapper` are present in
  `crates/soroban-ret/src/pattern/lifter.rs` and carry `cov_mark::hit!`
  instrumentation, but **no fixture exercises them and no `cov_mark::check!`
  asserts the hit** — they fire only on mainnet corpus contracts, where there
  is no reference source to check the result against. A token-contract fixture
  is the prerequisite for validating them; no target release is committed.
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
  `ALL_FIXTURES` constant in the same file (40 entries; `tests/fixtures/`
  holds 43 `.wasm` in total, of which 39 are the `test_*.wasm` the
  compile-back and equivalence gates sweep).
- Snapshots: `crates/soroban-ret/tests/snapshots/`.
- For **quantitative** accuracy measurement (per-contract scoring against a
  reference Rust source), see the `soroban-ret-accuracy` crate
  (`cargo run -p soroban-ret-accuracy --bin accuracy`).

## Validation gates: measured status

> All figures in this section were re-measured on **2026-08-06** against `main`
> at `799aa90` (v0.0.4). The three heavy gates are pinned to **rustc 1.95.0**
> (`RUSTUP_TOOLCHAIN`, as in `.github/workflows/build.yml`): they are hard
> error-count ratchets, and rustc diagnostics drift across floating `stable`
> releases. Numbers measured on another toolchain are not comparable.

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
(`liquidity_pool` and `sub_u64` are skipped for lacking a reference source —
`sub_u64` is a decompiler-authored fixture added with the `checked_sub`
recovery, not an SDK example), every complexity
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
floor.

Current status: **38 pass / 1 fail / 0 skip of 39 fixtures — 97 %** (gate
passes; floor is 95 %). The single failure is **`test_liquidity_pool`**, which
does *not* currently compile back: it emits 3 hard errors (`E0282` un-inferable
type, `E0369` an operator on a lost-typed value, `E0382` a use-after-move).
This fixture has regressed since the earlier "38/38, 100 %" reading — its
original `E0284 into_val` failure was fixed, but the deeper i128 share-math
reconstruction now surfaces different type errors. It is also *skipped by the
accuracy metric*, for lack of a reference source — an unrelated exclusion.

Note the difference in denominator between the two fixture gates: compile-back
sweeps the 39 `test_*.wasm` fixtures, while `ALL_FIXTURES` (the artifact-sweep
in `integration.rs`) covers 40. `check-compilable.sh` *skips* any output
containing `todo!` as unscoreable; currently nothing is skipped, so the pass
rate is over the full set.

Two earlier compile-fidelity codegen fixes landed in
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

### Spec-consistency (`crates/soroban-ret-accuracy/tests/spec_consistency.rs`)

Beyond *interface similarity vs a reference source* (the accuracy metric, which
only covers the SDK fixtures), this gate checks the generated Rust against the
contract's **own** `contractspecv0` — so it covers **every** contract including
the 24 mainnet corpus contracts that have no reference source. It builds the
expected interface from the spec (via the same `generate_type_ident` codegen
uses) and asserts, across all 63 contracts (39 fixtures + 24 corpus): **0**
dropped/extra functions and **0** arity mismatches on both halves, with mean
signature similarity **98.9 %** and type similarity **98.6 %**. Runs in the
default `cargo test` (decompile + `syn`, no wasm build; ~12 s).

Run it explicitly:

```text
cargo test -p soroban-ret-accuracy --test spec_consistency -- --nocapture
```

### Structural plausibility (`crates/soroban-ret-bench/tests/plausibility.rs`)

Turns the corpus restoration numbers — previously *report-only* in
`benchmark.yml` — into an asserted ratchet against `benchmark-data/baseline.json`.
Fails if any corpus contract regresses (fewer clean functions, more logic-lost
functions, or more decompilation artifacts). Improvements pass; an intentional
change refreshes the baseline (`scripts/rebuild-benchmark-baseline.sh`). Runs in
the default `cargo test`.

The headline restoration figure this produces — **92.4 %**
(`benchmark-data/baseline.json` → `overall_restoration`) — is the equal-weight
mean of per-contract `restoration_pct` across the 24 corpus contracts. It is
**correctness-blind**: it grades how much of each function lifted to concrete
Rust versus how much collapsed into `todo!()`, not whether what was recovered is
right. It is a corpus mean, not a per-contract guarantee, and should never be
quoted as one.

> Was 92.8 % before the `FnStatus::Trivial` classification was tightened (see
> below). No decompiler output changed — `artifacts_total` is identical for all
> 24 contracts — only the grading of two functions whose empty bodies render as
> `todo!()` stubs. The lower number is the more honest one.

#### Per-contract recovery signals (`soroban_ret::recovery`)

The same per-function verdicts and hole counts this gate aggregates are exposed
by the published library, on `DecompileResult::recovery` / `DecompileIR::recovery`
and via `soroban-ret --report` (JSON). That is the supported way to show a
per-contract confidence signal in a UI — the corpus figures above must not be
used for it. The module deliberately exposes **counts, not a headline
percentage**; see its docs for why.

The library owns the canonical implementation. `soroban-ret-bench` and
`soroban-ret-accuracy` each previously kept their own copy of the artifact
counter, which is how three copies drift apart; both now delegate.

**`FnStatus::Trivial` is narrower than it was.** An empty body was graded
`Trivial` ("nothing to restore") whenever the lifter saw no host calls — even
when the function declares a non-`Void` return type, in which case codegen
renders the body as `todo!("decompiled function body")` and the function traps
at runtime. Two corpus functions were affected, `aqua-rewards::get_pools_plane`
and `digicus::version`; the latter is independently recorded by the equivalence
harness as diverging (original returns `U32(0)`, recompiled traps). Both are now
`LogicLost`. A "fully recovered" badge on a function that traps is the
deceptively-clean bug class this project treats as a defect, so the baseline was
refreshed rather than the grading kept.

### Corpus soundness (`crates/soroban-ret/tests/corpus_soundness.rs`, `SOROBAN_RET_CORPUS_SOUNDNESS=1`)

The "wrong output" ratchet, and the counterpart to compile-back. It decompiles
every mainnet corpus contract and `cargo check`s the result for
`wasm32v1-none`, counting **hard** `error[E…]` diagnostics. Unlike
`check-compilable.sh` it does **not** skip output containing `todo!` — a
`todo!()` compiles fine, so every hard error is a genuinely-wrong construct the
lifter emitted: output that *looks* like code but does not type-check. The
metric is "wrong output", not "incomplete output".

Current status: **326 hard errors across 24 contracts** (ceiling 326), with
**3 contracts compiling cleanly** — `digicus`, `fxdao-oracle`, `unknown-oracle`.
Down from 1042 at the start of the v0.0.4 cycle. Every intermediate *rise* in
this ratchet has been an audited, deliberate unmask (fixing a type error
un-suppresses pre-existing brokenness rustc's error recovery was hiding); see
the running commentary in the `ERROR_CEILING` docstring, which is the
authoritative history.

```text
SOROBAN_RET_CORPUS_SOUNDNESS=1 cargo test -p soroban-ret --test corpus_soundness -- --nocapture
```

### Functional equivalence (`crates/soroban-ret-equiv`, `SOROBAN_RET_EQUIV=1`)

The strongest check: it **recompiles** decompiled output to a real `.wasm`
(`cargo build --target wasm32v1-none`), registers BOTH the original and
recompiled contract in a `soroban-sdk` test host (`soroban-env-host`), invokes
each scalar-invocable exported function with boundary + seeded-random inputs,
and compares the outcomes (lowered to canonical `ScVal`). A divergence is a
decompiler correctness limitation; the gate is a ratchet on the divergence
count, like the corpus-soundness gate.

Current baseline: **68 functions / 479 cases executed; 63 contracts checked
(39 fixtures + all 24 mainnet corpus), 0 errored, 99.2 % behavioral match,
4 divergences** (ceiling 4).

**22 of the 63 are reported `not_recompilable`** and are therefore never
executed: 21 of the 24 mainnet corpus contracts, plus the `test_liquidity_pool`
fixture. Only `digicus`, `fxdao-oracle` and `unknown-oracle` recompile from the
corpus — the same three the corpus-soundness gate reports as clean-compiling.

All 4 divergences are in **`digicus`** (`clear_repos`, `get_repos`,
`get_repos_and_issues`, `version`). Each is an **honest `todo!()` hole**: the
recompiled function reaches an unrecovered value and traps as
`Error(Context, InvalidAction)` where the original returns a real value or its
own `Error(Contract, #1)`. **No divergence is a fabricated wrong value** — the
distinction that matters for any consumer surfacing these results.

History of this ratchet: 75 / 82.3 % → 60 (the `checked_add`/`checked_sub` →
`.ok_or(..)` recovery) → 4 (the fallible-storage-get recovery eliminated
`unknown-oracle`'s 56 empty-storage divergences) → 9 (issue #38 t19 *unmasked*
`num_list`: the fixture became recompilable for the first time, exposing
divergences previously hidden behind a compile error) → 8 → 6 → **4** (t21/t23
recovered the vec accumulator and the populate→push value relay; t24's
wrapping-exact `<<` render and dead-counter elimination closed the last two
`test_alloc` overflow cases). `test_alloc` now matches on every generated
input, including overflow — the earlier claim that `num_list` "loses its
populate-loop and returns an empty `Vec`" no longer holds.

**Coverage is intrinsically limited** (by design): only functions invocable with
generated scalar arguments (`bool`/`u32`/`i32`/`u64`/`i64`/`u128`/`i128`, ≤48
input vectors per function) and no required storage/auth state are executed;
aggregate/UDT-argument functions, and the renamed `__constructor`/`__check_auth`,
are skipped, as are contracts whose output does not recompile. It is a
correctness sanity-check + behavioral-match metric, **not** a full-corpus
differential test — and the 99.2 % is a match rate over that narrow executed
slice, not a per-contract correctness guarantee.

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

- **The remaining frontier is dataflow, not pattern coverage.** The sixteen
  patterns above are implemented and tested; what still collapses to `todo!()`
  on large mainnet contracts is value provenance across branches, calls and
  loops. Tracked as open issues rather than described here, so the list cannot
  go stale:

  - [#34](https://github.com/Inferara/soroban-ret/issues/34) — no memory-SSA /
    reaching-definitions: values lost across branches, calls and deep helpers
    (the master lever).
  - [#66](https://github.com/Inferara/soroban-ret/issues/66) — lost guard
    conditions, the 500+ `if todo!("unknown value")` class;
    [#67](https://github.com/Inferara/soroban-ret/issues/67) is its
    `ValueNotInitialized` starter bucket.
  - [#68](https://github.com/Inferara/soroban-ret/issues/68) — `aqua-rewards`
    checkpoint/derivation math, the deep #34 remainder.
  - [#69](https://github.com/Inferara/soroban-ret/issues/69) — close the final
    4 equivalence divergences (the `digicus` todo-panics).

- **No published per-contract accuracy signal.** The benchmark HTML/JSON report
  is a per-commit GitHub Actions artifact (`.github/workflows/benchmark.yml`),
  not a hosted page; the only stable, linkable artifact is
  `benchmark-data/baseline.json`, which CI rewrites on every push to `main`
  (cite it at a tag, not at `main`). Consumers wanting a per-contract hole
  count today should count the marker strings in the emitted source
  (`todo!("unknown value")`, `todo!("host call`, `todo!("decompiled function
  body")`, `var_N` — matching `count_artifacts` in
  `crates/soroban-ret-bench/src/metrics.rs`, and noting that `prettyplease` can
  emit the spaced `todo !(` form), or walk the IR from `decompile_to_ir()`.
  Neither `soroban-ret-bench` nor `soroban-ret-equiv` is published to
  crates.io (`publish = false`).
