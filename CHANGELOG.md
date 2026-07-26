# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
