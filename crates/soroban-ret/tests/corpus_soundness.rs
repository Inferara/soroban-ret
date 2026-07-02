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
const ERROR_CEILING: u32 = 1042;

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
