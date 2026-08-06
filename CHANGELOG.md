# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added — per-contract recovery signals

- New public `soroban_ret::recovery` module: per-function recovery verdicts
  (`FnStatus::{Clean, Partial, LogicLost, Trivial, Missing}`) and
  unresolved-hole counts by category, computed from the contract in front of
  you with no corpus baseline involved. Surfaced on `DecompileResult::recovery`
  and `DecompileIR::recovery` (both `#[non_exhaustive]`, so this is additive),
  and as JSON via the new `soroban-ret --report` CLI flag. Intended for UIs that
  display decompiled source and need an honest per-contract confidence signal:
  the project's corpus-wide figures are corpus means and do not describe an
  individual contract.
- `soroban_ret::VERSION`, and an optional `serde` feature deriving
  `Serialize`/`Deserialize` on the recovery types.
- The report is `None` under `DecompileOptions::spec_only`, which skips body
  lifting: grading those empty bodies would report a fully-recovered contract
  as mostly "logic lost". `--report` rejects `--spec-only` for the same reason.
  An unmeasured result must not be mistakable for a measured one.
- The library now owns the canonical artifact counter. `soroban-ret-bench` and
  `soroban-ret-accuracy` each kept their own copy; both now delegate.

### Fixed — deceptively-clean function grading

- `FnStatus::Trivial` no longer covers a function whose empty body must still
  return a value. Codegen renders such a body as
  `todo!("decompiled function body")`, which traps at runtime, so grading it
  "fully recovered" was the deceptively-clean bug class. Two corpus functions
  were affected — `aqua-rewards::get_pools_plane` and `digicus::version`, the
  latter independently recorded by the equivalence harness as diverging
  (original returns `U32(0)`, recompiled traps). Both are now `LogicLost`.
  Corpus mean restoration moves **92.8 % → 92.4 %** with **no change to any
  decompiled output** (`artifacts_total` is identical for all 24 contracts);
  `benchmark-data/baseline.json` refreshed accordingly.

### Documentation

- `README.md` and `docs/pattern-coverage.md` re-measured against `main`: the
  compile-back gate is **38/39 = 97 %**, not the previously documented 38/38 =
  100 % (`test_liquidity_pool` regressed to 3 hard errors); the 4 equivalence
  divergences are `digicus`, not `test_alloc::num_list` (closed in #64). Added
  the corpus-soundness gate, refreshed every stale count, and replaced rotted
  line-number code references with greppable symbol names.

## [0.0.4] - 2026-07-26

The correctness-first release: two multi-tranche programs — memory-SSA-style
value recovery (#34, 16 tranches) and loop-structure recovery (#38, 7
tranches) — landed end to end, driving the mainnet-corpus hard-error ratchet
**1042 → 326** (−68%) and closing the behavioral-equivalence story to **4
divergences / 99.2% match**, every one an honest `todo!()` panic, none a
silently wrong value.

### Fixed — fabrication classes eliminated

- Lost `Map`/`Vec` values are no longer fabricated as empty collections;
  unrecoverable collections surface as honest holes (#36, #39).
- Symbol-builder loops no longer fabricate tag-only `SymbolSmall` keys: the
  DkEval const-loop evaluator recovers the **real** encoded symbols
  (`Symbol::new(&env, "AssetRecord")`, real invoke symbols) at lift time
  (#61, #62).
- `blend-backstop`'s `user_balance` recovered from a bare `panic!()` collapse
  to its real storage protocol (#33).
- Never-type (`!`) rooted values render so the panic semantics are exact and
  the output compiles — operators, reference args, and generic storage ops
  no longer produce guaranteed type errors (#54).
- Compiler-internal size arithmetic renders wrapping-exact (`count << 2`
  instead of `count * 4`) and dead vestigial counters are eliminated, so
  recompiled output no longer traps on overflow inputs where the original
  wrapped (#64).

### Added — recovery capabilities

- Storage-getter recovery classes: defaulting u128 getters, fallible struct
  getters with proven multi-field layouts and TTL protocols, value-returning
  getters (`.unwrap_or_else(|| panic_with_error!(..))`), and defaulting
  `Map`/`Vec` getters (#41–#47).
- Keyed `DataKey` recovery through frame-built descriptors: DkEval executes
  the real constructor bytecode against provenance-checked frame state, so
  wrong bare unit keys become true keyed variants
  (`Positions(user)`, `ResConfig(asset.clone())`) (#50, #51).
- Fallible storage-decode discriminants modeled (`OptionDecodeDisc`), folding
  re-encoded `.unwrap()` None-arms instead of leaving opaque scrutinees (#40).
- Loop-structure program (#57–#60, #62–#64): carried-seed admissibility,
  helper statement adoption, functional vec-accumulator recovery
  (`let mut vec = Vec::new(&env); … vec.push_back(x)`), const-loop
  evaluation, and the populate→push value relay — `test_alloc`'s `num_list`
  now decompiles **hole-free** and behaviorally matches the original on
  every generated input, including overflow cases.
- Reaching-definition groundwork: append-only slot-def journal with
  unique-def fill, if-result value joins, sound-join read poisoning backed by
  a corpus-measured taint census (#41, #48, #49).

### Changed

- Corpus soundness ratchet (hard compile errors across the 24-contract
  mainnet corpus): **1042 → 326**, with every intermediate rise an audited,
  documented honesty unmask. Three contracts now decompile to cleanly
  compiling Rust (digicus, fxdao-oracle, unknown-oracle).
- Codegen soundness sweep: registry-typed construct-field admissibility,
  adopted defaults, construct arity, semantic recoveries
  (`first_index_of(x) == 2` → `.is_none()`, `Bytes` append chains) (#52–#56).
- The functional-equivalence gate itemizes every divergence with inputs and
  both outcomes; ceiling ratcheted 8 → 6 → 4 across the loop program.

## [0.0.3] - 2026-07-02

The verification-infrastructure release: every later correctness claim is
backed by gates introduced here.

### Added

- `soroban-ret-equiv`: functional-equivalence gate — decompile → recompile →
  run both contracts in `soroban-env-host` → diff outcomes per input (#28).
- Mainnet corpus (24 deployed contracts) with restoration benchmark,
  structural-plausibility ratchet, and corpus soundness (hard-compile-error)
  ratchet (#22, #23, #25).
- Accuracy framework for IR-level assertions (#18).
- Checked-arithmetic recovery: `a.checked_add(b).ok_or(err)` restored from
  the overflow-unsafe `Ok(a + b)` collapse (behavioral match 82.3% → 87.3%)
  (#29).
- Fallible storage-getter recovery:
  `env.storage().<dur>().get::<_, T>(&key).ok_or(Error::V)` rebuilt from
  helper bytecode, error codes included (match 87.3% → 99.2%) (#30).
- Big-contract recovery batch: enum variants, i128 soft-arithmetic
  reconstruction, `Symbol`-from-linear-memory builders, router token-list
  validation, cross-contract invoke return types (aquarius −85% todos).

### Changed

- Correctness-first corpus compilation: host-call lowering, lost-value tail
  completion, correctness-guard husk passes (ratchet 1318 → 1042)
  (#26, #27, #31).

## [0.0.2] - 2026-05-29

### Added

- WASM-level CFG analysis distinguishing compiler safety-net `unreachable`
  traps from real panics (#13).
- Linear-memory points-to modeling of the shadow stack (#9).
- Iterative fixpoint dataflow over loops (#6).
- Guard-chain shadowing recovery (#10) and broader `Val` type support (#4).
- Base decompilation pipeline hardening and expanded test coverage (#3, #5).

## [0.0.1] - 2026-04-30

### Added

- Initial release: WASM parsing, Soroban spec/type recovery, base
  decompilation pipeline, CI workflows, and the publish process.

[0.0.4]: https://github.com/Inferara/soroban-ret/compare/v0.0.3...v0.0.4
[0.0.3]: https://github.com/Inferara/soroban-ret/compare/v0.0.2...v0.0.3
[0.0.2]: https://github.com/Inferara/soroban-ret/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/Inferara/soroban-ret/releases/tag/v0.0.1
