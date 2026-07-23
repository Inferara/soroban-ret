//! Corpus structural-soundness ratchet (correctness-first).
//!
//! Decompiles every mainnet corpus contract and counts *hard* compile errors in
//! the generated Rust (`scripts/check-corpus-soundness.sh`). `todo!()` compiles,
//! so every counted error is a genuinely-wrong construct — output that looks like
//! code but does not type-check. The assert is a **ratchet**: the total must not
//! exceed [`ERROR_CEILING`]. Lower the ceiling as correctness fixes land; never
//! raise it without understanding why a change made output more wrong.
//!
//! Skipped unless `SOROBAN_RET_CORPUS_SOUNDNESS=1` (it compiles soroban-sdk for
//! `wasm32v1-none` — slow, needs the target installed plus crates.io access),
//! mirroring the `compile_back` gate.
//!
//! Run it explicitly:
//! ```text
//! SOROBAN_RET_CORPUS_SOUNDNESS=1 cargo test -p soroban-ret --test corpus_soundness -- --nocapture
//! ```

use std::process::Command;

/// Max tolerated hard compile errors across the whole mainnet corpus.
///
/// History (drive this down): 1339 (pre correctness-guard) → 1318 (break-outside-
/// loop + error-sentinel-access + undeclared-assignment husks) → 1295 (`Val`
/// turbofish for un-inferable storage gets + heterogeneous key vecs → `Vec<Val>`;
/// fxdao-oracle becomes the first corpus contract to compile cleanly) → 1259
/// (`Address` annotation for `require_auth()`-ed gets + tail-aware discarded-get
/// detection). The latter drop nets −36 but raised two contracts by +1/+2 as
/// faithful type fixes *unmasked* pre-existing latent errors (E0382 moves, lost
/// Val-tag husks) that an earlier type error had hidden — not new wrongness.
/// → 1234 (recognise collection bool-methods `contains_key`/`contains`/`is_empty`
/// in `is_bool_typed`, so the existing `bool == 1 → bool` fold fires on
/// `map.contains_key(k) == 1`; fixes E0308 "expected bool, found integer",
/// aqua-amm −25, zero regression).
/// → 1201 (fold tautological SDK type-tag guards `<param>.get_tag() == Tag::<T>`
/// to a constant when the param type uniquely fixes the tag — Address/Vec/Map/
/// Bytes/String/u32/i32; clears E0599 `get_tag`/E0433 `Tag`. unknown-oracle −10,
/// band −9. Nets −33; aqua-rewards +5 as folding a broken guard *condition* lets
/// rustc see the (always-reached) body's pre-existing lost-key/value errors it
/// had been suppressing — faithful unmasking, not new wrongness.
/// → 1199 (annotate un-inferable empty `Map::new`/`Vec::new` collections whose
/// value type the lifter lost — `Map::<_, Val>::new` / `Vec::<Val>::new`,
/// pinning only the value param. Fires only when the collection is reached
/// exclusively through value-agnostic methods (`keys`/`contains_key`/`len`/
/// `is_empty`), so it never over-constrains a typed collection. digicus 3→2
/// getter Maps recovered → 3→1; zero other-contract drift.
/// → 1194 (recognise the SDK's empty-tuple encoding of `Result<(), E>`'s ok-type
/// in `needs_ok_unit_tail`, not only `Void`, so codegen appends the missing
/// `Ok(())` success tail — fixes E0308 "expected `Result<(), E>`, found `()`".
/// Gated to a unit ok-type, so a lost `Result<T, E>` value stays honest.
/// unknown-oracle −4, soroswap ×2 −4; phoenix +1 / xycloans +2 are *faithful
/// rustc unmasking* — the correct `Ok(())` clears the tail type error that was
/// suppressing pre-existing un-inferable `.get()` (E0284) errors, now visible.
/// → 1188 (clone a non-Copy `Address` param consumed by value in ≥2 `DataKey`
/// enum-construct payloads — `DataKey::Balance(addr)` keying several storage ops
/// each move-s it, E0382. A host-handle `.clone()` is a refcount bump = same
/// value, faithful. Gated to ≥2 enum-field uses of a non-Copy param, so it is a
/// no-op on compiling output. E0382 6→0; blend-pool-factory −3, comet −2,
/// blend-emitter −1; zero regressions, snapshots byte-identical.
/// → 1134 (lost-value tail completion — the non-unit analog of the `Ok(())` tail.
/// Lever 1: a non-unit-returning fn whose body lost its success value ends in a
/// `()`-typed, non-diverging tail (an `if cond { extend_ttl }` with no else) →
/// append `todo!()` (the value is unrecoverable; an honest hole, not a wrong
/// recovery). Lever 2: a fabricated literal in the success tail whose scalar class
/// can never unify with `Result<T, E>`'s scalar `T` (`Ok(false)` / a `ValConvert`
/// of it in `-> Result<u128, E>`) → `todo!()`; numeric↔numeric never fires
/// (unsuffixed integer literals coerce). Both retreat only to the safe `todo!()`
/// harbor on a *guaranteed* compile error, so they are strict no-ops on clean
/// output (snapshots byte-identical, compile-back 38/38). unknown-oracle 6→0
/// becomes the 2nd corpus contract to compile cleanly; the lost-`()` tail spans
/// 19/24 contracts (E0308 309→265). Zero per-contract regressions — unlike Lever
/// B these fire on husk-bodied getters with nothing latent to unmask.
/// → 1042 (Phase-1 host-call lowering + near-miss closeout, -92): (1) E0284 fix —
/// `annotate_uninferable_gets` now treats a `Result<(), E>` fn's codegen-
/// synthesized `Ok(())`/`todo!()` tail correctly, so a trailing discarded `.get()`
/// is `Val`-annotated rather than mistaken for the return (-7). (2) Faithful host-
/// call lowering: `update_current_contract_wasm` -> `env.deployer()`,
/// `address_to_strkey`/`strkey_to_address` -> `Address::to_string`/`from_string`,
/// `bytes_new` -> `Bytes::new(&env)` (-29; `bytes_new`'s aqua-amm -31 unmasks
/// pre-existing E0308s in reflector x2/soroban-domains, faithful). (3) Husks of
/// guaranteed-non-compiling constructs: type-impossible `<handle param> != <int>`
/// (E0308), `Val`-tag guards with a `break`/`continue` body (E0433), and a lost
/// invoke arg's `.into_val()` on `!` (E0277) (-56). Zero per-contract regressions
/// except the documented `bytes_new` unmasking; snapshots byte-identical.
/// → 1064 (blend-backstop `user_balance` body recovery, +22 — the FIRST net rise
/// in this ceiling's history, and a deliberate exception to the "drive it down"
/// rule above). Root cause: `detect_map_unpack_decode_wrapper` mis-claimed
/// *fallible* storage getters (those that branch on `has_contract_data` with a
/// missing-key default), emitting synthetic field accesses at a wrong output
/// layout and silently dropping the `has`/default/`extend_ttl` protocol — so
/// `user_balance` collapsed to a bare, misleading `panic!()`. Fix A now refuses
/// such helpers (they inline generically, preserving control flow); Fix B splices
/// the SDK multi-param tag-guard `if` at an entrypoint so the then-branch tail
/// value survives (a depth-0 `Return`-in-`if` was dropped, emptying the body);
/// Fix C stubs a value-returning body that collapsed to a lone `panic!()` after
/// host calls were observed to `todo!()`. Removing the mis-claim is a *net
/// structural win* (band artifacts 107→38, blend pools 154→109 ×2, comet 58→33;
/// several contracts gain clean functions), but it UNMASKS pre-existing lost-key
/// `todo!()`s in the two getters that were being hidden behind wrong-but-clean
/// field accesses: aqua-rewards +26, soroban-domains +24. Every added error was
/// verified to be a genuine `todo!("unknown value")` (zero new fabricated
/// Maps/keys/types; no cleanly-recovered function regressed) — deceptively-clean
/// wrong output traded for honest holes, the opposite of "more wrong". The
/// alternative (narrowing Fix A to blend-backstop's exact shape) was rejected
/// because it would preserve known-wrong-but-clean output elsewhere purely to
/// keep this metric green. Closing the exposed getters is Phase-2 dataflow work
/// (reaching-defs / consumer-type), not a soundness regression.
/// → 1131 (issue #36: lost collections no longer fabricated as empty
/// `Map::new`/`Vec::new`, +67 — the second deliberate honesty rise). A lost
/// `Map`/`Vec` used to render as an EMPTY one wherever a stale `map_new`/
/// `vec_new` def survived an unmodeled phi (an inlined `get(&k).unwrap_or_else
/// (|| vec![])` helper collapsing to its default arm; a loop's `map_put`
/// reassignment chain invisible post-loop; a zero-arg invoke's empty args vec
/// wrapped as a fabricated argument). Empty collections COMPILE, so this
/// ratchet could never see them: `Map::<_, Val>::new(&env).contains_key(k)`
/// (always-false), `set(&key, &Map::new(&env))` (stores fabricated empty) all
/// read as intentional. Corpus fabrications 121 → 33 (every survivor verified
/// a genuine construction: accumulators feeding now-lost loops, per-path
/// default arms whose loaded value escapes via `return get(&k).unwrap()`,
/// fresh-vec builds). The +67 is fully audited: aqua-amm +54 = +53 E0599
/// "method not found in `!`" (honest `todo!()` receivers where the fabricated
/// empty map/vec sat) +1 E0277 `into_val` on `!`; digicus +5 (same class, and
/// its old E0283 — CAUSED by a fabricated map — disappeared); reflector +2 x2,
/// blend +2/+1/+1 same class. All other error buckets byte-identical; zero new
/// fabrication. test_alloc's "clean" fixture status was itself the bug (a
/// fabricated always-empty `Vec::new(&env)` return) and is now honestly
/// artifacted — see integration.rs. Recovering these values for real is #34
/// (reaching-defs) / #38 (loop-carried collections); an `unwrap_or_else`
/// default-arm RECOVERY (rendering the true `get(&k).unwrap_or_else(|| …)`)
/// is the natural #35-family follow-up.
/// → 1127 (issue #35: fallible storage-decode discriminant modeling, −4).
/// `seed_option_decode_status` marks the `[disc@0, value@8]` output slot of
/// void has+get decode helpers with `StackVal::OptionDecodeDisc`; the IfElse
/// handler folds ONLY the bare-trap `if disc == 0 { unreachable }` consumer
/// (the `.unwrap()`'s None-arm re-encoded — the rendered `get(..).unwrap()`
/// keeps the panic-on-missing semantics), while every other consumer degrades
/// to the honest `todo!()`. Corpus `todo == 0`/`!= 0` scrutinees 199 → 166,
/// with full clean getter recoveries (blend-emitter `get_backstop` et al.) and
/// two restored success-arm guards (reflector/soroban-domains bodies that
/// previously ran UNconditionally — structural fidelity up, +1 honest artifact
/// each, baseline refreshed). Equivalence stays 100.0%/0.
/// → 1124 (issue #34 groundwork, −3). Three additive lift-time capabilities:
/// a provable value join for `if (result T)` arms (the SDK's small/object Val
/// encode/decode split of one source), a value-slot link binding a fallible
/// getter's `+8` slot to its inlined `get(..)`'s `let` binding, and a
/// unique-reaching-def journal fill for slots the state map lost. Recovers
/// reflector's `config.history_retention_period` set-value and a `fee_config
/// .len()` binding (−3 net); surfaces 2 previously-dropped honest husk
/// statements (+3 `todo!()`, corpus 1357→1360 — completeness, not loss).
/// → 1120 (issue #34 tranche 2, −4). Defaulting-u128-getter recovery
/// (`detect_defaulting_u128_getter` + append-only seed →
/// `get::<_, u128>(&key).unwrap_or(0)`, aqua `TokenShare`), pure TryFromVal
/// decode-helper payload seeding (`detect_tryfromval_decode_helper`,
/// u64/u128/i128 classes, disc stays honest), and reference-wrapping
/// `HostCallResult` purity — reflector ×2 resolve a lost `&todo!()` storage
/// key to its real `var_3_2` binding (−2 todos each; corpus 1360→1356).
/// → 1143 (issue #34 tranche 5: fallible-struct-getter call-site recovery,
/// +23 — the third deliberate honesty rise, aqua-rewards only; every other
/// contract byte-identical, soroswap — the PR-#44 gap-fabrication
/// counterexample — included). The t4-banked recognizer is wired as an
/// early-recognizer arm (binding + limb/field seeds + proven TTL bumps, no
/// inlining), and the aqua `PoolRewardConfig` key now resolves by EXECUTING
/// the descriptor ctor's real bytecode over its proven-zero gap row
/// (`gap_row_proven_zero` + `DkEval.gap_zero`; DkEval's stores refusing
/// absolute addresses is what makes a completed eval a proof the row is
/// never written). The +23 decomposes, fully audited: +8 rustc
/// error-RECOVERY unmasks — the `todo!() + todo!()` unit-arith loops are
/// byte-identical in both outputs, previously suppressed by the broken
/// untyped `vp_value.expired_at` reads this tranche fixes (now typed
/// `get::<_, PoolRewardConfig>(..).unwrap_or(zero).expired_at`); +15 honest
/// holes (lost-key `&todo!()` triples, one un-inferable surfaced `Map::new`)
/// inside real storage protocol that was previously hidden behind single
/// whole-body `todo!("decompiled return value")` collapses. Zero new
/// fabrication; corpus todos 1217→1230 measured by the same unmask.
/// → 1123 (issue #34 tranche 6: value-returning getter classes, −20,
/// aqua-rewards only). Two zero-parameter `() -> i64` getter classes are
/// recognized at their call sites and NEVER inlined — the helper's value
/// used to die at its internal block-result joins: the fallible value
/// getter (`get(&K).unwrap_or_else(|| panic_with_error!(env, E))`, the
/// TryFromVal tag guard's constant naming the type — 77 pins `Address`)
/// and the defaulting map getter (`get(&K).unwrap_or(Map::new(&env))`,
/// the empty map being the helper's own proven `select` arm, not a
/// fabrication). The value is bound ONCE and consumers reference the
/// binding — a per-consumer re-read clone would silently drop map
/// mutations (`.set` on a fresh temporary compiles); on the immutable
/// binding a mutator is a loud E0596. Fixes aqua's 8 cross-contract
/// invoke targets (`&todo!()` → the TokenShare share-token `Address`
/// read), `get_gauges`-class tails (full clean typed recovery), and
/// REMOVES the mis-structured `if has(&k) { return get(&k).unwrap() }`
/// early-returns the generic inline used to fabricate from the helper's
/// internal return. Corpus todos 1230→1208.
/// → 1094 (issue #34 tranche 7: the Vec-defaulting getter, the tag-75 /
/// vec_new sibling of tranche 6's map getter, −29). `detect_defaulting_map_getter`
/// generalized to `detect_defaulting_collection_getter` over a
/// `CollectionKind` table — the INVERTED tag guard's constant (75 VecObject
/// / 76 MapObject) selects the kind, and the select's default-arm
/// constructor must match it (`vec_new` for 75, `map_new` for 76) — so a
/// mismatched guard/ctor pair is refused. Recovers aqua's `EmPauseAdmins`
/// access-control list reader across `enable/disable_emergency_mode` et al.:
/// the lost `todo!().first_index_of(admin)` receiver becomes the real
/// `get(&vec![Symbol("EmPauseAdmins")]).unwrap_or(Vec::new(&env))`, and its
/// sret error path resolves (`panic!()` → the registry-typed
/// `panic_with_error!(AccessControlError::Unauthorized)`). The empty vec is
/// the helper's own proven `select` arm (46/46 `Vec::new` are `unwrap_or`
/// defaults, zero bare fabrications); keys are each module's own proven
/// const-keys (verified `EmPauseAdmins`/`StableSwapPoolHash` present in the
/// aqua-amm wasm). Corpus todos 1208→1162.
/// → 1051 (issue #34 tranche 10: the frame-descriptor DataKey ctor fold,
/// −43). The `(i32) -> i64` descriptor-pointer ctor whose row is built at
/// RUNTIME in the caller's frame (`i32.store` selector, `i64.store` payload
/// Vals) is folded by executing the ctor's real bytecode under `DkEval`,
/// seeding the descriptor row from the abstract frame slots — constants
/// concretely, runtime payloads as move-only `Arg` tokens. Slots are seeded
/// only when the ordered store log justifies them (the slot's current value
/// IS its last logged real store, at the store instruction's exact width);
/// an unjustified or missing slot fails the ctor's load and refuses the
/// fold. Recovers aqua-rewards' user-keyed protocols
/// (`vec![Symbol("WorkingBalance"), user]`, `UserRewardsState`; todos
/// 311→232) and corrects blend-fixed/yieldblox's WRONG bare unit keys into
/// the true keyed variants (`ResConfig` → `ResConfig(asset)`,
/// `Positions(user)` — each pool's +4 todos are honest payload holes inside
/// now-correct variant shapes). Corpus `todo!` lines 1240→1166.
/// → 903 (issue #34 tranche 11: DkEval constant-cell narrow reads +
/// `i64.load32_u`, and the heterogeneous-key-vec fix, −148). The evaluator
/// now services a narrower load fully inside a wider CONSTANT cell by
/// little-endian byte extraction (an `i64.store`d discriminant read back
/// with `i32.load` — blend-backstop's descriptor shape; symbolic cells
/// still refuse), unlocking keyed folds there (bare WRONG
/// `BackstopDataKey::UserBalance` unit keys → true `PoolBalance(pool)`)
/// and aqua-amm's hash-keyed `vec![Symbol("TokensSetPools"), sha256(..)]`.
/// `is_heterogeneous_val_vec` then broadened to "any known class beside an
/// unknown-typed element" (was: two known classes, or numeric+unknown), so
/// keyed vecs `[Symbol, payload]` render as `Vec<Val>` via per-element
/// `IntoVal` — faithful (identical per-element ScVal) and the only type a
/// heterogeneous key vec can have. Fixed 87 hash-key + dozens of
/// pre-existing Symbol/Address-mix E0308s: aqua-rewards 228→143,
/// aqua-amm 272→213, comet 55→50; blend-backstop 26→29 is the faithful
/// unmask of its REMAINING bare fn-pointer `UserBalance` keys (E0277)
/// surfacing once neighboring sites compile.
/// → 749 (issue #34 tranche 12: codegen soundness sweep, −154). Three
/// levers, each replacing a guaranteed-non-compiling render with either the
/// faithful construct or an honest hole: (1) surviving raw
/// `bytes_new_from_linear_memory` lowers late (stage 4b4b, AFTER the BLS
/// field-argument recovery that claims some of the same sites) to real
/// static bytes `Bytes::from_slice(&env, &[..])` under a strict in-segment
/// read, else `todo!()` — never the fabricated `env.buf()` API; (2)
/// `serialize_to_bytes` lifts to the SDK's real `val.to_xdr(&env)`
/// (`soroban_sdk::xdr::ToXdr` imported on use) instead of the non-existent
/// `env.to_xdr(val)`; (3) a method call or field access on a `!`-rooted
/// receiver (`todo!().contains_key(..)`, E0599/E0609 — rustc refuses method
/// resolution on `!`) renders as `todo!()` outright, which is EXACT: the
/// receiver panics before the arguments evaluate either way
/// (`is_never_rooted`, transitive through method/field chains and bare
/// `ValConvert` wrappers, deliberately NOT through type-pinning `CastAs`).
/// aqua-amm 213→129, aqua-rewards 143→113, reflectors −3 todos each.
/// → 734 (issue #34 tranche 13: registry-typed construct-field
/// admissibility, −15). New pipeline stage 4m3 (AFTER 4m's enum-key
/// construction so key payloads are visible): a struct/union construct
/// field whose expression type PROVABLY contradicts the registry's field
/// spec holes to an honest `todo!()` — soroban-domains'
/// `SubDomain { node: ContractErrors::InvalidParent, .. }` (an error enum
/// in a BytesN field), blend-emitter's `LastDistro(symbol_short!(..))`
/// (a fabricated Symbol where the spec says Address), lightecho's
/// error-sentinel "price". A `Hash<32>` digest feeding a `BytesN<32>` slot
/// coerces faithfully via `.to_bytes()` instead (identical bytes). Only
/// airtight contradictions fire — params/locals/method results are left
/// untouched; numeric-in-numeric always unifies; integer enums stay
/// 0/1-plausible for Bool/numeric slots. `child_exprs`/`child_exprs_mut`
/// walkers gained the missing EnumConstruct/MapConstruct arms (construct
/// payloads were invisible to every walker-based pass before).
/// → 479 (issue #34 tranche 14: never-value rendering discipline, −255;
/// digicus becomes the THIRD clean-compiling contract, zero per-contract
/// regressions). One principle, five renders: a `!`-rooted ("never") value —
/// an already-lost `todo!()` and anything provably downstream of one — must
/// render so the `!` can coerce, because every other position is a
/// GUARANTEED rustc error with identical runtime behavior (the todo panics
/// first either way). (1) Operators: `todo!() == 0`, `a - todo!()` fall back
/// `!`→`()` in operator traits (E0277 "can't compare `()` with `i32`") →
/// whole expression is `todo!()`; right-operand collapse only when the left
/// operand is effect-free (never skips a real side effect); `&&`/`||`
/// excluded (they type-check). (2) By-ref args: `&todo!()` is `&!` and does
/// NOT coerce (E0308 "expected `&Address`, found `&!`") → render bare at
/// concrete-typed sites (invoke address/function, crypto, prng, strkey).
/// (3) Generic storage ops can't infer from `!`: `set`/`get`/`has`/`remove`/
/// `extend_ttl` with a never key/value render it bare AND pin that generic
/// to `Val` (`set::<_, soroban_sdk::Val>(&k, todo!())`). (4) Unbound locals
/// (E0425 — `let var_2 = var_2.append(..)` self-reference residue of a lost
/// accumulation loop; uses after a branch-scoped binding's join) substitute
/// `UnknownVal`: the defining flow was not threaded, so the value at the use
/// IS unknown. (5) Locals whose EVERY binding is `!`-rooted (fixpoint, so
/// never-ness flows through `let b = a.len();`) husk their uses — the
/// binding panics before any use runs; a local with one real binding is
/// untouched (its `let` unifies to the real type). `child_exprs(_mut)`
/// completed the remaining child-bearing variants (crypto/invoke/event/
/// prng/ttl/Try/Some/Log — uses inside them were invisible to every walker).
/// aqua-amm 129→65, aqua-rewards 99→49, blend-backstop 32→9, blend pools
/// 67→43 ×2, reflectors 18→9 ×2, soroswap 14→4/36→29, digicus 1→0 CLEAN.
const ERROR_CEILING: u32 = 479;

#[test]
fn corpus_soundness_within_ceiling() {
    if std::env::var("SOROBAN_RET_CORPUS_SOUNDNESS").as_deref() != Ok("1") {
        eprintln!(
            "skipping corpus_soundness: set SOROBAN_RET_CORPUS_SOUNDNESS=1 to run the \
             <={ERROR_CEILING}-hard-error ratchet (compiles soroban-sdk for wasm32v1-none)"
        );
        return;
    }

    let script = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../scripts/check-corpus-soundness.sh"
    );
    let output = Command::new("bash")
        .arg(script)
        .output()
        .expect("failed to spawn scripts/check-corpus-soundness.sh");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("{stdout}\n{stderr}");

    let total = stdout
        .lines()
        .rev()
        .find_map(|l| {
            l.strip_prefix("TOTAL_ERRORS=")
                .and_then(|s| s.trim().parse::<u32>().ok())
        })
        .expect("could not parse TOTAL_ERRORS from check-corpus-soundness.sh output");

    assert!(
        total <= ERROR_CEILING,
        "corpus hard-error total {total} exceeds the {ERROR_CEILING} ceiling — a change made \
         decompiled output more wrong; investigate before raising the ceiling"
    );
}
