/// Integration tests for the soroban-ret pipeline.
///
/// Smoke tests that the full decompilation pipeline produces correct output
/// for the 18 deliverable fixtures (Levels 1-4): simple arithmetic, basic
/// storage, custom types, events, auth, and cross-contract calls.
use soroban_ret::{DecompileOptions, decompile, decompile_with_options};

// -------------------------------------------------------------------------
// Assertion helpers
//
// `assert!(source.contains("x"))` catches missing content but accepts any
// arrangement. The helpers below enforce ordering and scoping so that
// rearranged or cross-pollinated output (e.g. a body fragment leaking into
// a sibling function) fails the test.
// -------------------------------------------------------------------------

/// Find `needle` in `haystack`; return its end offset on success.
fn find_after(haystack: &str, needle: &str, from: usize) -> Option<usize> {
    haystack[from..].find(needle).map(|rel| from + rel)
}

/// Locate every `needle` (in order) inside `haystack`. Returns (start_offset,
/// end_offset) for the matched span, panicking with a precise diagnostic on
/// the first item that is missing or appears out of order.
#[track_caller]
fn assert_ordered(haystack: &str, label: &str, needles: &[&str]) -> (usize, usize) {
    let mut cursor = 0usize;
    let mut start = None;
    let mut last_seen: Option<&str> = None;
    for &needle in needles {
        match find_after(haystack, needle, cursor) {
            Some(at) => {
                if start.is_none() {
                    start = Some(at);
                }
                cursor = at + needle.len();
                last_seen = Some(needle);
            }
            None => {
                let context = last_seen
                    .map(|p| format!(" (previous match: {p:?})"))
                    .unwrap_or_default();
                panic!(
                    "{label}: expected {needle:?} after previous matches but it was missing\
                     {context}\n\n--- source ---\n{haystack}"
                );
            }
        }
    }
    (start.unwrap_or(0), cursor)
}

/// Assert that each item in `needles` appears within the same function body
/// (the brace-delimited region following `fn_signature`), in the given order.
/// Function body extraction uses a tiny brace counter rather than regex.
#[track_caller]
fn assert_in_fn(source: &str, fn_signature: &str, needles: &[&str]) {
    let sig_pos = source.find(fn_signature).unwrap_or_else(|| {
        panic!("missing fn signature {fn_signature:?}\n--- source ---\n{source}")
    });
    let open = source[sig_pos..]
        .find('{')
        .map(|r| sig_pos + r)
        .unwrap_or_else(|| panic!("no opening brace after {fn_signature:?}"));
    let body_start = open + 1;
    let mut depth = 1i32;
    let mut idx = body_start;
    let bytes = source.as_bytes();
    while idx < bytes.len() && depth > 0 {
        match bytes[idx] {
            b'{' => depth += 1,
            b'}' => depth -= 1,
            _ => {}
        }
        idx += 1;
    }
    assert!(
        depth == 0,
        "unbalanced braces after {fn_signature:?}: {}",
        &source[sig_pos..]
    );
    let body = &source[body_start..idx - 1];
    assert_ordered(body, &format!("fn {fn_signature:?} body"), needles);
}

// -------------------------------------------------------------------------
// Level 1: simple arithmetic + empty contracts
// -------------------------------------------------------------------------

#[test]
fn test_decompile_empty() {
    let wasm = include_bytes!("../../../tests/fixtures/test_empty.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("#![no_std]"), "missing no_std");
    assert!(source.contains("#[contract]"), "missing contract attr");
}

#[test]
fn test_decompile_empty2() {
    let wasm = include_bytes!("../../../tests/fixtures/test_empty2.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("#![no_std]"), "missing no_std");
    assert!(source.contains("#[contract]"), "missing contract attr");
}

#[test]
fn test_decompile_zero() {
    let wasm = include_bytes!("../../../tests/fixtures/test_zero.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("#![no_std]"), "missing no_std");
    assert!(source.contains("#[contract]"), "missing contract attr");
}

#[test]
fn test_decompile_add_u64() {
    let wasm = include_bytes!("../../../tests/fixtures/test_add_u64.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // Top-level order: prelude (no_std), contract attr, impl block, then add fn signature.
    assert_ordered(
        &source,
        "test_add_u64",
        &[
            "#![no_std]",
            "#[contract]",
            "#[contractimpl]",
            "pub fn add",
            "a: u64",
            "b: u64",
            "-> u64",
        ],
    );
    // `a + b` must live inside `pub fn add`, not leak into another fn.
    assert_in_fn(&source, "pub fn add", &["a + b"]);
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
    // `safe_add`/`safe_add_two` must recover the overflow-checked form, NOT the
    // unsafe `Ok(a + b)` (which traps on overflow under `overflow-checks`).
    assert!(
        source.contains("checked_add") && source.contains(".ok_or("),
        "safe_add not recovered to checked_add().ok_or(): {source}"
    );
    assert!(
        !source.contains("Ok(a + b)"),
        "checked_add collapsed to unsafe Ok(a + b)"
    );
    // Per-function error scoping: the UDT-typed `safe_add_two` renders its enum.
    assert!(
        source.contains("MyError::Overflow"),
        "safe_add_two error not scoped to MyError"
    );
}

#[test]
fn test_decompile_sub_u64() {
    let wasm = include_bytes!("../../../tests/fixtures/test_sub_u64.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // `checked_sub` recovery reads op + operand order from the bytecode (the
    // arithmetic shortcut's fallback would otherwise hard-code `Add`).
    assert!(
        source.contains("checked_sub") && source.contains(".ok_or("),
        "safe_sub not recovered to checked_sub().ok_or(): {source}"
    );
    assert!(
        source.contains("MyError::Underflow"),
        "safe_sub_two error not scoped to MyError"
    );
    assert!(
        !source.contains("Ok(a + b)") && !source.contains("Ok(a - b)"),
        "checked_sub collapsed to an unsafe wrapping op"
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_unknown_oracle_fallible_gets() {
    // A mainnet oracle whose getters were lifting to a lossy
    // `if has(k){extend_ttl} todo!()` husk — dropping the value AND the
    // missing-key contract error. The fallible-storage-get recovery restores
    // `env.storage().<dur>().get(&key).ok_or(Error::Variant)` with the error code
    // read from the helper's bytecode (named variants from the spec).
    let wasm = include_bytes!("../../../benchmark-data/mainnet/unknown-oracle-CAWGFKEL.wasm");
    let source = decompile(wasm).expect("decompilation failed");

    // Direct getters: the recovered `get(..).ok_or(..)` IS the return value.
    assert_in_fn(
        &source,
        "pub fn get_admin",
        &[".instance()", "Admin", ".ok_or(Error::Uninitialized)"],
    );
    assert_in_fn(
        &source,
        "pub fn get_price",
        &[
            ".temporary()",
            "&chain_id",
            ".ok_or(Error::NoGasDataForChain)",
        ],
    );
    // `get_gas_price` returns the UDT `ChainData`: the `get::<_, ChainData>`
    // turbofish pins the value type the `.ok_or` can't infer.
    assert_in_fn(
        &source,
        "pub fn get_gas_price",
        &["get::<_, ChainData>", ".ok_or(Error::NoGasDataForChain)"],
    );

    // Computed getter: the leading fallible read is recovered as a `?` early-return
    // guard (faithful on the empty-storage path); the lost arithmetic stays `todo!()`.
    // The key is the helper's own argument — NOT a fabricated literal.
    assert_in_fn(
        &source,
        "pub fn get_transaction_gas_cost_in_usd",
        &[
            "&other_chain_id",
            ".ok_or(Error::NoGasDataForChain)?",
            "todo!(",
        ],
    );
}

#[test]
fn test_lost_collections_render_honest_holes() {
    // Issue #36: a LOST `Map`/`Vec` used to render as a fabricated EMPTY one
    // (`Map::new(&env)`), which compiles and reads as an intentional empty
    // collection — silent-wrong output the soundness ratchet cannot see.
    //
    // digicus `get_repos` is the canonical collapse: the helper is
    // `get("repos").unwrap_or_else(|| Map::new(&env))`, and branch-sequential
    // lifting made the default arm the extracted value, fabricating
    // `Map::new(&env).keys()` (always-empty). The lost value must be an honest
    // `todo!()` hole instead.
    let wasm = include_bytes!("../../../benchmark-data/mainnet/digicus-CCZLARB4.wasm");
    let source = decompile(wasm).expect("decompilation failed");

    let sig = source.find("pub fn get_repos(").unwrap();
    let end = sig
        + source[sig..]
            .find("\n    pub fn ")
            .unwrap_or(source.len() - sig);
    let body = &source[sig..end];
    assert!(
        !body.contains("Map::new(&env)") && !body.contains("Map::<_, Val>::new(&env)"),
        "get_repos must not fabricate an empty map for the lost storage value:\n{body}"
    );
    assert!(
        body.contains("todo!("),
        "get_repos' lost map must surface as an honest todo!() hole:\n{body}"
    );

    // The FAITHFUL counterpart must survive: blend-backstop `reward_zone` is
    // `if has(RZ) { return get(&RZ).unwrap(); } Vec::new(&env)` — the loaded
    // value escapes through the early return, so the trailing empty vec is a
    // genuine per-path default arm, not a fabrication.
    let wasm = include_bytes!("../../../benchmark-data/mainnet/blend-backstop-CAQQR5SW.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert_in_fn(
        &source,
        "pub fn reward_zone",
        &[".get(&symbol_short!(\"RZ\"))", "Vec::new(&env)"],
    );
}

#[test]
fn test_option_decode_trap_guard_folds_to_clean_getter() {
    // Issue #35: blend-emitter's storage getters go through a void decode
    // helper writing `[disc@0, value@8]` (`0 = missing`); the caller's
    // `if disc == 0 { unreachable }` is the `.unwrap()`'s None-panic
    // re-encoded. Before, the unmodeled disc slot rendered as
    // `if todo!("unknown value") == 0 { panic!(); }` after every getter and
    // the value was lost. With the discriminant seeded, the bare-trap guard
    // folds and the loaded value flows to the return.
    let wasm = include_bytes!("../../../benchmark-data/mainnet/blend-emitter-CCOQM6S7.wasm");
    let source = decompile(wasm).expect("decompilation failed");

    let sig = source.find("pub fn get_backstop(").unwrap();
    let end = sig
        + source[sig..]
            .find("\n    pub fn ")
            .unwrap_or(source.len() - sig);
    let body = &source[sig..end];
    assert!(
        body.contains(".get(&symbol_short!(\"Backstop\"))") && body.contains(".unwrap()"),
        "get_backstop must recover the clean `get(..).unwrap()` getter:\n{body}"
    );
    assert!(
        !body.contains("todo!("),
        "get_backstop's decode-status guard must fold away, not render as todo:\n{body}"
    );

    // Negative control: `initialize`'s guard carries REAL logic (the
    // AlreadyInitialized panic_with_error path) — it must NOT fold; the
    // discriminant stays an honest hole.
    let sig = source.find("pub fn initialize(").unwrap();
    let end = sig
        + source[sig..]
            .find("\n    pub fn ")
            .unwrap_or(source.len() - sig);
    let body = &source[sig..end];
    assert!(
        body.contains("AlreadyInitializedError"),
        "initialize's already-initialized guard is real control flow and must survive:\n{body}"
    );
}

#[test]
fn test_decompile_blend_backstop_user_balance_body() {
    // `user_balance` is a fallible storage getter: `if has(k) { get + unpack +
    // extend_ttl } else { default }`. `detect_map_unpack_decode_wrapper` used to
    // mis-claim its `get_user_balance` helper as a pure decode wrapper, emitting
    // wrong-layout field accesses and dropping the whole protocol, so the body
    // collapsed to a bare, misleading `panic!()`. Three fixes restore it: the
    // detector now refuses fallible getters (they inline generically), the SDK
    // multi-param tag-guard `if` is spliced so the then-branch survives, and a
    // value-returning body that collapsed to a lone `panic!()` is stubbed honest.
    let wasm = include_bytes!("../../../benchmark-data/mainnet/blend-backstop-CAQQR5SW.wasm");
    let source = decompile(wasm).expect("decompilation failed");

    // The real persistent-storage protocol is recovered, NOT a bare `panic!()`.
    // Since t16, the keyed `UserBalance` variant carries its (lost) payload as
    // an honest `todo!()` hole — the registry declares it a tuple variant, so
    // the earlier bare `BackstopDataKey::UserBalance` was an uncompilable fn
    // item, not a value.
    assert_in_fn(
        &source,
        "pub fn user_balance",
        &[
            ".persistent()",
            ".has(&BackstopDataKey::UserBalance(",
            ".get::<_, Val>(&BackstopDataKey::UserBalance(",
            ".extend_ttl(",
            "&BackstopDataKey::UserBalance(todo!(",
        ],
    );

    // The misleading `panic!()` is gone: a lost value is an honest `todo!()`
    // hole, never a fabricated diverging panic. (`panic!()` as a substring would
    // also match `panic_with_error!`, so check the exact bare-panic statement.)
    // Bound the slice at the *next* `pub fn` so the test is not coupled to which
    // sibling function happens to follow `user_balance`.
    let sig = source.find("pub fn user_balance").unwrap();
    let end = source[sig + 1..]
        .find("pub fn ")
        .map(|r| sig + 1 + r)
        .unwrap_or(source.len());
    let body = &source[sig..end];
    assert!(
        !body.contains("panic!()"),
        "user_balance must not collapse to a bare panic!() — lost content is todo!():\n{body}"
    );
}

#[test]
fn test_decompile_add_u128() {
    let wasm = include_bytes!("../../../tests/fixtures/test_add_u128.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn add"), "missing add function");
    assert!(source.contains("u128"), "missing u128 type");
    assert!(source.contains("a + b"), "missing add expression");
}

#[test]
fn test_decompile_add_i128() {
    let wasm = include_bytes!("../../../tests/fixtures/test_add_i128.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn add"), "missing add function");
    assert!(source.contains("i128"), "missing i128 type");
    assert!(source.contains("a + b"), "missing add expression");
}

#[test]
fn test_decompile_tuples() {
    let wasm = include_bytes!("../../../tests/fixtures/test_tuples.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn tuple1"), "missing tuple1 function");
    assert!(source.contains("pub fn tuple2"), "missing tuple2 function");
    assert!(
        source.contains("(u32, i64)"),
        "missing 2-element tuple type"
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

// -------------------------------------------------------------------------
// Level 2: basic storage, mutability, logging, generics
// -------------------------------------------------------------------------

#[test]
fn test_decompile_contract_data() {
    let wasm = include_bytes!("../../../tests/fixtures/test_contract_data.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // Each storage op must live inside its dedicated fn — assert by scope,
    // not by raw substring (which would pass even if `.set` leaked into `get`).
    assert_in_fn(
        &source,
        "pub fn put",
        &["env.storage()", ".persistent()", ".set(&key, &val)"],
    );
    assert_in_fn(
        &source,
        "pub fn get",
        &["env.storage()", ".persistent()", ".get(&key)"],
    );
    assert_in_fn(
        &source,
        "pub fn del",
        &["env.storage()", ".persistent()", ".remove(&key)"],
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_mutability() {
    let wasm = include_bytes!("../../../tests/fixtures/test_mutability.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn calc"), "missing calc function");
    assert!(source.contains("-> u32"), "missing return type");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_logging() {
    let wasm = include_bytes!("../../../tests/fixtures/test_logging.wasm");
    // Logging contract should at least decompile cleanly. The log! macro is
    // stripped at compile time so body recovery is best-effort.
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn hello"), "missing hello function");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_mutability_expression() {
    let wasm = include_bytes!("../../../tests/fixtures/test_mutability.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // Body has `b * 2 + a` — exercises operator precedence (binary `*` inside `+`).
    // Require the canonical form: a loose fallback (any "b * 2" plus any "+ a")
    // accepted wrong operand orders like `c + a + b * 2`.
    assert!(
        source.contains("b * 2 + a"),
        "missing canonical precedence-sensitive expression `b * 2 + a`: {source}"
    );
}

#[test]
fn test_decompile_generics() {
    let wasm = include_bytes!("../../../tests/fixtures/test_generics.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn exec"), "missing exec function");
    assert!(source.contains("-> u32"), "missing return type");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

// -------------------------------------------------------------------------
// Level 3: custom types, errors, events, constructor
// -------------------------------------------------------------------------

#[test]
fn test_decompile_udt() {
    let wasm = include_bytes!("../../../tests/fixtures/test_udt.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub struct UdtTuple"), "missing UdtTuple");
    assert!(source.contains("pub struct UdtStruct"), "missing UdtStruct");
    assert!(source.contains("pub enum UdtEnum"), "missing UdtEnum");
    assert!(source.contains("pub enum UdtEnum2"), "missing UdtEnum2");
    assert!(source.contains("contracttype"), "missing contracttype");
    // Regression guard for #14: `add`'s UdtD arm must recover the Vec-fold idiom
    // (VecTryIterFold / recover_vec_iter_fold pass), and the post-match
    // composition must be the faithful `a + b` — not the spurious `a.a + a + b`
    // that wasm-opt's hoisted `tup.0` leaks into the return.
    assert_in_fn(
        &source,
        "fn add",
        &[
            "tup.0 + tup.1.try_iter().fold(0i64, |sum, i| sum + i.unwrap())",
            "a + b",
        ],
    );
    assert!(
        !source.contains("a.a + a + b"),
        "regressed: spurious a.a leak in udt::add (#14)"
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_errors() {
    let wasm = include_bytes!("../../../tests/fixtures/test_errors.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // Top-level declaration order: Flag is `#[contracttype]`, Error is
    // `#[contracterror]`, then the impl block. Each variant of Flag must
    // appear in its declared order (A=0, B=1, C=2, D=3, E=4); a reordered
    // discriminant list would be a regression.
    assert_ordered(
        &source,
        "test_errors top-level",
        &[
            "#[contracttype]",
            "pub enum Flag",
            "A = 0",
            "B = 1",
            "C = 2",
            "D = 3",
            "E = 4",
            "#[contracterror]",
            "pub enum Error",
            "AnError = 1",
            "#[contract]",
            "#[contractimpl]",
            "pub fn hello",
            "Result<Symbol, Error>",
        ],
    );
    // The hello body must perform a `set("persisted", &1)` BEFORE the
    // if-chain dispatches over Flag. Verify the if-arm order matches the
    // source (A → C → D → fallthrough) — a reordered chain would silently
    // change the contract's semantics.
    assert_in_fn(
        &source,
        "pub fn hello",
        &[
            "env.storage()",
            ".persistent()",
            ".set(&symbol_short!(\"persisted\")",
            "if flag == Flag::A",
            "Ok(symbol_short!",
            "else if flag == Flag::C",
            "Err(Error::AnError)",
            "else if flag == Flag::D",
            "panic!()",
            "panic_with_error!",
            "from_contract_error",
        ],
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_events() {
    let wasm = include_bytes!("../../../tests/fixtures/test_events.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // Event struct + field order matters: `from` and `to` are topics; `amount`
    // and `to_muxed_id` are payload fields. A reordered struct breaks ABI.
    assert_ordered(
        &source,
        "test_events Transfer event",
        &[
            "contractevent",
            "topics = [\"transfer\"]",
            "pub struct Transfer",
            "#[topic]",
            "pub from: Address",
            "#[topic]",
            "pub to: Address",
            "pub amount: i128",
            "pub to_muxed_id: Option<u64>",
        ],
    );
    // failed_transfer constructs Transfer then publishes then panics — in that order.
    assert_in_fn(
        &source,
        "pub fn failed_transfer",
        &[
            "Transfer {",
            "from,",
            "to,",
            "amount,",
            "to_muxed_id: None,",
            ".publish(&env)",
            "panic!()",
        ],
    );
    // transfer extracts the MuxedAddress before constructing the event.
    assert_in_fn(
        &source,
        "pub fn transfer",
        &["Transfer {", "to: to.address()", ".publish(&env)"],
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_events_ref() {
    let wasm = include_bytes!("../../../tests/fixtures/test_events_ref.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // Mirror of test_events — events_ref is the by-reference event API variant.
    assert!(source.contains("pub struct Transfer"));
    assert!(source.contains("contractevent"));
    assert!(source.contains("#[topic]"));
    assert!(source.contains(".publish(&env)"));
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_constructor() {
    let wasm = include_bytes!("../../../tests/fixtures/test_constructor.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("__constructor"), "missing constructor");
    assert!(source.contains("pub enum DataKey"), "missing DataKey type");
    // Regression guard for #16: the storage-dispatch match arms must be filled
    // (each tier's StorageGet), not recovered as `()`. Fixed by dd80099's
    // fill_empty_storage_dispatch_arms. The match returns Option<i64>.
    assert_in_fn(
        &source,
        "fn get_data",
        &[
            "DataKey::Persistent(_) => env.storage().persistent().get(&key)",
            "DataKey::Temp(_) => env.storage().temporary().get(&key)",
            "DataKey::Instance(_) => env.storage().instance().get(&key)",
        ],
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

// -------------------------------------------------------------------------
// Level 4: auth, account check-auth, cross-contract calls
// -------------------------------------------------------------------------

#[test]
fn test_decompile_auth() {
    let wasm = include_bytes!("../../../tests/fixtures/test_auth.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // fn1: require_auth on the parameter, then return 2.
    assert_in_fn(&source, "pub fn fn1", &["a.require_auth()", "2"]);
    // fn2: require_auth_for_args MUST come before invoke_contract — that's the
    // contract's whole point (authorise *then* dispatch).
    assert_in_fn(
        &source,
        "pub fn fn2",
        &[
            "a.require_auth_for_args(",
            ".into_val(&env)",
            "env.invoke_contract::<u64>",
            "&sub",
            "symbol_short!(\"fn1\")",
        ],
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_account() {
    let wasm = include_bytes!("../../../tests/fixtures/test_account.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(
        source.contains("__check_auth"),
        "missing __check_auth function"
    );
    assert!(
        source.contains("auth::Context"),
        "missing auth::Context import"
    );
    assert!(
        source.contains("Vec<Context>"),
        "missing Vec<Context> parameter"
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_invoke_contract() {
    let wasm = include_bytes!("../../../tests/fixtures/test_invoke_contract.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // add: simple a + b body.
    assert_in_fn(&source, "pub fn add", &["a + b"]);
    // add_with: the cross-contract call must dispatch to `add` with x and y
    // marshalled in that order via `vec![&env, x..., y...]`. If the argument
    // order is rearranged the contract semantics break.
    assert_in_fn(
        &source,
        "pub fn add_with",
        &[
            "env.invoke_contract::<i32>",
            "&contract_id",
            "symbol_short!(\"add\")",
            "vec![&env",
            "x.into_val(&env)",
            "y.into_val(&env)",
        ],
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

// -------------------------------------------------------------------------
// Extended scope: token-adjacent + multi-impl patterns
//
// These fixtures exercise wrapper detectors that are not reached by the
// Levels 1-4 fixtures (keyed-storage dispatch, multi-impl merging, panic
// bodies, alternate cross-contract param naming). They give us a smoke
// signal that the ported lifter still handles the broader pattern space.
// -------------------------------------------------------------------------

#[test]
fn test_decompile_liquidity_pool_keys() {
    let wasm = include_bytes!("../../../tests/fixtures/test_liquidity_pool.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // Constructor must produce distinct DataKey variants for each storage set;
    // this exercises the keyed-storage wrapper detector + enum key construction.
    assert!(
        source.contains("DataKey::TokenA"),
        "missing DataKey::TokenA"
    );
    assert!(
        source.contains("DataKey::TokenB"),
        "missing DataKey::TokenB"
    );
    assert!(
        source.contains("DataKey::TotalShares"),
        "missing DataKey::TotalShares"
    );
}

#[test]
fn test_decompile_import_contract() {
    let wasm = include_bytes!("../../../tests/fixtures/test_import_contract.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(
        source.contains("pub fn add_with"),
        "missing add_with function"
    );
    assert!(
        source.contains("invoke_contract"),
        "missing invoke_contract call"
    );
    assert!(
        source.contains("contract_id: Address"),
        "missing contract_id parameter"
    );
    assert!(source.contains("x: u64"), "missing x parameter");
    assert!(source.contains("y: u64"), "missing y parameter");
    // Regression guards for #15 (SDK v26.0.1 invoke_contract codegen):
    // - infallible call carries the return-type generic `::<u64>`
    // - fallible call uses the two-generic `::<u64, _>` form with the inner
    //   Result unwrapped via `.map(|r| r.unwrap()).map_err(|e| e.unwrap())`.
    assert_in_fn(&source, "fn add_with", &["env.invoke_contract::<u64>("]);
    assert_in_fn(
        &source,
        "fn safe_add_with",
        &[
            "env.try_invoke_contract::<u64, _>(",
            ".map(|r| r.unwrap())",
            ".map_err(|e| e.unwrap())",
        ],
    );
}

#[test]
fn test_decompile_modular() {
    let wasm = include_bytes!("../../../tests/fixtures/test_modular.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // Each fn returns its name's value — scope the literal check per-body so
    // `one` returning `2` or `zero` returning `1` cannot pass.
    assert_in_fn(&source, "pub fn one", &["1"]);
    assert_in_fn(&source, "pub fn two", &["2"]);
    assert_in_fn(&source, "pub fn zero", &["0"]);
}

#[test]
fn test_decompile_multiimpl() {
    let wasm = include_bytes!("../../../tests/fixtures/test_multiimpl.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // Fixture has three exported empty fns that are merged into one impl block.
    assert!(source.contains("pub fn empty(") || source.contains("pub fn empty "));
    assert!(source.contains("pub fn empty2"));
    assert!(source.contains("pub fn empty3"));
    assert!(source.contains("#[contractimpl]"));
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_macros() {
    let wasm = include_bytes!("../../../tests/fixtures/test_macros.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn empty(") || source.contains("pub fn empty "));
    assert!(source.contains("pub fn empty2"));
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_alloc() {
    // `num_list(count)` builds `[0, 1, …, count-1]` by pushing in a loop. The
    // loop-carried pushes are still lost (issue #38 frontier), but the LOSS
    // must surface as honest `todo!()` holes — issue #36: before, the whole
    // loop was dropped and the fn fabricated a bare `Vec::new(&env)` return,
    // silently-wrong "always empty" output that read as intentional.
    let wasm = include_bytes!("../../../tests/fixtures/test_alloc.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn num_list"), "missing num_list fn");
    assert!(
        source.contains("-> Vec<u32>"),
        "missing Vec<u32> return type"
    );
    assert!(source.contains("count: u32"), "missing count param");
    assert!(
        source.contains("while count != 0") || source.contains("loop"),
        "the vec-building loop must not be dropped:\n{source}"
    );
    // The lost pushes/return must surface as honest holes. The positive
    // todo!() check is the load-bearing assertion — the whitespace-sensitive
    // negative alone would silently pass if codegen's indentation changed.
    assert!(
        source.contains("todo!("),
        "num_list's lost loop content must surface as todo!() holes:\n{source}"
    );
    assert!(
        !source.contains("Vec::new(&env)\n    }"),
        "num_list must not fabricate an empty-vec return:\n{source}"
    );
}

#[test]
fn test_decompile_plain_contract() {
    // The minimal `contract.wasm` fixture exercises the basic happy path
    // with a single `add(u64, u64) -> u64` export.
    let wasm = include_bytes!("../../../tests/fixtures/contract.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn add"), "missing add function");
    assert!(source.contains("a + b"), "missing addition expression");
    assert!(source.contains("u64"), "missing u64 type");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_contract_with_constructor() {
    // contract_with_constructor.wasm exercises:
    //  - all three storage durabilities (persistent, temporary, instance)
    //  - DataKey enum with tuple variants
    //  - match expression dispatch over DataKey
    //  - __constructor host function
    let wasm = include_bytes!("../../../tests/fixtures/contract_with_constructor.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // DataKey variants must appear in declared order.
    assert_ordered(
        &source,
        "DataKey enum",
        &[
            "pub enum DataKey",
            "Persistent(u32)",
            "Temp(u32)",
            "Instance(u32)",
        ],
    );
    // Constructor body: each storage tier is written once, in source order
    // (persistent, then temporary, then instance), each on its own DataKey
    // variant. A swap would point the writes at the wrong storage tier.
    assert_in_fn(
        &source,
        "pub fn __constructor",
        &[
            "env.storage()",
            ".persistent()",
            ".set(&DataKey::Persistent(init_key)",
            "&init_value",
            "env.storage()",
            ".temporary()",
            ".set(&DataKey::Temp(init_key * 2)",
            "&init_value",
            "env.storage()",
            ".instance()",
            ".set(&DataKey::Instance(init_key * 3)",
            "&init_value",
        ],
    );
    // get_data: match-arm order mirrors the enum declaration.
    assert_in_fn(
        &source,
        "pub fn get_data",
        &[
            "match key",
            "DataKey::Persistent(_)",
            ".persistent()",
            ".get(&key)",
            "DataKey::Temp(_)",
            ".temporary()",
            ".get(&key)",
            "DataKey::Instance(_)",
            ".instance()",
            ".get(&key)",
        ],
    );
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
}

#[test]
fn test_decompile_fuzz() {
    let wasm = include_bytes!("../../../tests/fixtures/test_fuzz.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn run"), "missing run function");
    assert!(source.contains("if"), "missing conditional in run function");
    assert!(source.contains("panic!()"), "missing panic in run function");
}

// -------------------------------------------------------------------------
// Crypto patterns
//
// Exercises `pattern/host_calls.rs::lift_crypto_call` and the crypto type
// alias generation in `codegen/types.rs::generate_type_ident_crypto`.
// -------------------------------------------------------------------------

#[test]
fn test_decompile_bls() {
    let wasm = include_bytes!("../../../tests/fixtures/test_bls.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    // Type aliases for BLS12-381 must resolve via generate_type_ident_crypto.
    assert!(
        source.contains("Bls12381"),
        "missing BLS12-381 type alias: {source}"
    );
    assert!(
        source.contains("soroban_sdk::crypto::bls12_381"),
        "missing bls12_381 module import"
    );
    // Host calls dispatched through env.crypto().bls12_381().
    assert!(
        source.contains("env.crypto().bls12_381()"),
        "missing crypto().bls12_381() dispatch"
    );
    // Regression guard for #19 defect 1 (shared with #20): Vec::get must keep
    // its .unwrap() panic-guard so the Option<Bls12381Fr> result type-checks
    // against the element return type. Fixed by the wrap_tail_vec_get_unwrap
    // pipeline pass (pipeline.rs).
    assert_in_fn(&source, "fn fr_vec_get", &["values.get(index).unwrap()"]);
    // Regression guard for #19 defect 2: the proof.fp2 struct-field argument must
    // be recovered (not a raw linear-memory load). Fixed by the Stage 4b4
    // struct-field re-attribution pass (pipeline.rs).
    assert_in_fn(&source, "fn dummy_verify", &["map_fp2_to_g2(&proof.fp2)"]);
    // Negative: no decompiler artifacts.
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
    assert!(
        !source.contains("RawHostCall"),
        "unexpected RawHostCall artifact"
    );
    assert!(
        !source.contains("env.buf("),
        "regressed: bogus env.buf() artifact (#19 defect 2)"
    );
    assert!(
        !source.contains("bytes_new_from_linear_memory"),
        "regressed: raw linear-memory load leaked into output (#19 defect 2)"
    );
}

#[test]
fn test_decompile_bn254() {
    let wasm = include_bytes!("../../../tests/fixtures/test_bn254.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(
        source.contains("Bn254"),
        "missing BN254 type alias: {source}"
    );
    assert!(
        source.contains("soroban_sdk::crypto::bn254"),
        "missing bn254 module import"
    );
    assert!(
        source.contains("env.crypto().bn254()"),
        "missing crypto().bn254() dispatch"
    );
    // Regression guard for #20: Vec::get must keep its .unwrap() panic-guard so
    // the Option<Fr> result type-checks against the Fr return type. Fixed by the
    // wrap_tail_vec_get_unwrap pipeline pass (pipeline.rs).
    assert_in_fn(&source, "fn fr_vec_get", &["values.get(index).unwrap()"]);
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
    assert!(
        !source.contains("RawHostCall"),
        "unexpected RawHostCall artifact"
    );
}

// -------------------------------------------------------------------------
// Control flow reconstruction
//
// `test_decompile_auth` covers the positive in-order shape of fn2's body.
// This test adds the complementary *negative* claim that structurize +
// `collapse_trivial_loops` left no residual `loop { ... break; }` wrapping.
// None of the canonical Level 1-4 fixtures should emit a bare `loop {`
// block — real iteration codegens to `while` (see `codegen/functions.rs`
// while-loop emission).
// -------------------------------------------------------------------------

#[test]
fn test_decompile_auth_control_flow() {
    let wasm = include_bytes!("../../../tests/fixtures/test_auth.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(
        !source.contains("loop {"),
        "expected control flow collapsed; residual `loop {{` block present:\n{source}"
    );
}

// -------------------------------------------------------------------------
// Option / api surface
// -------------------------------------------------------------------------

#[test]
fn test_decompile_spec_only() {
    let wasm = include_bytes!("../../../tests/fixtures/test_contract_data.wasm");
    let mut options = DecompileOptions::default();
    options.spec_only = true;
    let result = decompile_with_options(wasm, &options).expect("decompilation failed");
    assert!(
        result.source.contains("todo!"),
        "spec-only should have todo! in body"
    );
}

// -------------------------------------------------------------------------
// Smoke tests covering all 30 fixtures (18 deliverable + 10 extended + 2 crypto)
// -------------------------------------------------------------------------

const ALL_FIXTURES: &[(&str, &[u8])] = &[
    (
        "test_empty",
        include_bytes!("../../../tests/fixtures/test_empty.wasm"),
    ),
    (
        "test_empty2",
        include_bytes!("../../../tests/fixtures/test_empty2.wasm"),
    ),
    (
        "test_zero",
        include_bytes!("../../../tests/fixtures/test_zero.wasm"),
    ),
    (
        "test_add_u64",
        include_bytes!("../../../tests/fixtures/test_add_u64.wasm"),
    ),
    (
        "test_sub_u64",
        include_bytes!("../../../tests/fixtures/test_sub_u64.wasm"),
    ),
    (
        "test_add_u128",
        include_bytes!("../../../tests/fixtures/test_add_u128.wasm"),
    ),
    (
        "test_add_i128",
        include_bytes!("../../../tests/fixtures/test_add_i128.wasm"),
    ),
    (
        "test_tuples",
        include_bytes!("../../../tests/fixtures/test_tuples.wasm"),
    ),
    (
        "test_contract_data",
        include_bytes!("../../../tests/fixtures/test_contract_data.wasm"),
    ),
    (
        "test_mutability",
        include_bytes!("../../../tests/fixtures/test_mutability.wasm"),
    ),
    (
        "test_logging",
        include_bytes!("../../../tests/fixtures/test_logging.wasm"),
    ),
    (
        "test_generics",
        include_bytes!("../../../tests/fixtures/test_generics.wasm"),
    ),
    (
        "test_udt",
        include_bytes!("../../../tests/fixtures/test_udt.wasm"),
    ),
    (
        "test_errors",
        include_bytes!("../../../tests/fixtures/test_errors.wasm"),
    ),
    (
        "test_events",
        include_bytes!("../../../tests/fixtures/test_events.wasm"),
    ),
    (
        "test_constructor",
        include_bytes!("../../../tests/fixtures/test_constructor.wasm"),
    ),
    (
        "test_auth",
        include_bytes!("../../../tests/fixtures/test_auth.wasm"),
    ),
    (
        "test_account",
        include_bytes!("../../../tests/fixtures/test_account.wasm"),
    ),
    (
        "test_invoke_contract",
        include_bytes!("../../../tests/fixtures/test_invoke_contract.wasm"),
    ),
    // Extended scope (Tranche 2 fixture broadening)
    (
        "contract",
        include_bytes!("../../../tests/fixtures/contract.wasm"),
    ),
    (
        "contract_with_constructor",
        include_bytes!("../../../tests/fixtures/contract_with_constructor.wasm"),
    ),
    // NOTE: test_alloc is intentionally NOT here. Its `num_list` builds a vec
    // in a loop; the loop's pushes are still lost, and before issue #36 the
    // output fabricated a bare `Vec::new(&env)` return — deceptively clean,
    // silently wrong (always-empty). The honest output carries `todo!()`
    // holes, so it cannot pass the no-artifacts gate until loop-carried
    // collection recovery lands (issue #38).
    (
        "test_events_ref",
        include_bytes!("../../../tests/fixtures/test_events_ref.wasm"),
    ),
    (
        "test_fuzz",
        include_bytes!("../../../tests/fixtures/test_fuzz.wasm"),
    ),
    (
        "test_import_contract",
        include_bytes!("../../../tests/fixtures/test_import_contract.wasm"),
    ),
    (
        "test_liquidity_pool",
        include_bytes!("../../../tests/fixtures/test_liquidity_pool.wasm"),
    ),
    (
        "test_macros",
        include_bytes!("../../../tests/fixtures/test_macros.wasm"),
    ),
    (
        "test_modular",
        include_bytes!("../../../tests/fixtures/test_modular.wasm"),
    ),
    (
        "test_multiimpl",
        include_bytes!("../../../tests/fixtures/test_multiimpl.wasm"),
    ),
    (
        "test_bls",
        include_bytes!("../../../tests/fixtures/test_bls.wasm"),
    ),
    (
        "test_bn254",
        include_bytes!("../../../tests/fixtures/test_bn254.wasm"),
    ),
    // Level 5: trait-based contracts, associated types, workspace (Tranche 3)
    (
        "test_associated_types",
        include_bytes!("../../../tests/fixtures/test_associated_types.wasm"),
    ),
    (
        "test_associated_types_contracttrait",
        include_bytes!("../../../tests/fixtures/test_associated_types_contracttrait.wasm"),
    ),
    (
        "test_contracttrait_impl_full",
        include_bytes!("../../../tests/fixtures/test_contracttrait_impl_full.wasm"),
    ),
    (
        "test_contracttrait_impl_partial",
        include_bytes!("../../../tests/fixtures/test_contracttrait_impl_partial.wasm"),
    ),
    (
        "test_contracttrait_path_crate",
        include_bytes!("../../../tests/fixtures/test_contracttrait_path_crate.wasm"),
    ),
    (
        "test_contracttrait_path_global",
        include_bytes!("../../../tests/fixtures/test_contracttrait_path_global.wasm"),
    ),
    (
        "test_contracttrait_path_relative",
        include_bytes!("../../../tests/fixtures/test_contracttrait_path_relative.wasm"),
    ),
    (
        "test_contracttrait_path_self",
        include_bytes!("../../../tests/fixtures/test_contracttrait_path_self.wasm"),
    ),
    (
        "test_contracttrait_path_super",
        include_bytes!("../../../tests/fixtures/test_contracttrait_path_super.wasm"),
    ),
    (
        "test_workspace_contract",
        include_bytes!("../../../tests/fixtures/test_workspace_contract.wasm"),
    ),
];

#[test]
fn test_all_fixtures_decompile() {
    for (name, wasm) in ALL_FIXTURES {
        let result = decompile(wasm);
        assert!(result.is_ok(), "{name} failed: {:?}", result.err());
    }
}

// Fixtures with a known, tracked `todo!("unknown value")` gap that is NOT a
// truncation artifact. test_liquidity_pool's i128 share-math is now reconstructed
// (the soft-arith multiply/divide helpers are classified and lowered to clean
// `Mul`/`Div`, operands rebuilt from their limb pairs, and the carry/borrow-flag
// leaks dropped), so it no longer needs an exemption — the list is empty and every
// fixture is held to the full no-artifact bar.
const KNOWN_I128_TODO_FIXTURES: &[&str] = &[];

#[test]
fn test_all_fixtures_no_artifacts() {
    for (name, wasm) in ALL_FIXTURES {
        let source = decompile(wasm).unwrap_or_else(|e| panic!("{name} failed: {e}"));
        if !KNOWN_I128_TODO_FIXTURES.contains(name) {
            assert!(
                !source.contains("todo!(\"unknown value\")"),
                "{name} has todo!(\"unknown value\") artifact"
            );
        }
        assert!(
            !source.contains("todo!(\"host call"),
            "{name} has unresolved host call artifact"
        );
        // No fixture should fall back to a whole-empty-body placeholder. This guards
        // the enum-variants identity round-trip recovery (the data-carrying-enum
        // `fn f(v: E) -> E` decode→match→re-encode that previously stripped to an
        // empty body); applies to every fixture, including the known-i128 one.
        assert!(
            !source.contains("todo!(\"decompiled function body\")"),
            "{name} has an empty-body todo!(\"decompiled function body\") artifact"
        );
        // Check for unresolved var_N temporary names. Skipped for the known i128
        // fixtures: the unreconstructed share-math leaves intermediate `var_N`
        // operands (same root cause as the todo!() gap above).
        if !KNOWN_I128_TODO_FIXTURES.contains(name) {
            for word in source.split(|c: char| !c.is_alphanumeric() && c != '_') {
                assert!(
                    !(word.starts_with("var_")
                        && word.len() > 4
                        && word[4..].chars().all(|c| c.is_ascii_digit())),
                    "{name} has unresolved variable '{word}'"
                );
            }
        }
    }
}

// -------------------------------------------------------------------------
// Real-contract regression fixtures (issue #7)
//
// Large real Soroban DeFi contracts (Aquarius AMM, Blend lending) that spill
// aggregates to the shadow stack and dispatch on cross-contract `Result`s.
// They exercise the points-to model, dynamic offsets, and cycle handling at a
// scale the synthetic fixtures don't. Asserted to decompile without panicking —
// a frame-slot cycle or unbounded recursion here would have crashed the lifter.
// (They are intentionally NOT in ALL_FIXTURES: full reconstruction still leaves
// `todo!()` placeholders, so they can't pass the no-artifacts gate yet.)
// -------------------------------------------------------------------------

#[test]
fn aquarius_decompiles_without_panicking() {
    let wasm = include_bytes!("../../../tests/fixtures/aquarius.wasm");
    let src = decompile(wasm).expect("aquarius.wasm should decompile");
    assert!(
        src.contains("fn estimate_swap"),
        "estimate_swap should be emitted"
    );
}

// Layer B (issue #12): the token-sort validation guard inlined into
// `estimate_swap` reaches its error via a multi-level `br_if` to a
// `fail_with_error` tail. Without recovery the condition surfaces as a bare
// `break` and the specific `TokensNotSorted` contract error is lost (the panic
// leaks out as a sibling stray that the optimizer drops). Assert the nested
// `if cond { panic_with_error!(…TokensNotSorted) }` is reconstructed, scoped to
// the `estimate_swap` body so an unrelated occurrence can't satisfy it.
#[test]
fn aquarius_estimate_swap_recovers_tokens_not_sorted_guard() {
    let wasm = include_bytes!("../../../tests/fixtures/aquarius.wasm");
    let src = decompile(wasm).expect("aquarius.wasm should decompile");
    let start = src
        .find("fn estimate_swap")
        .expect("estimate_swap should be emitted");
    let body = &src[start..];
    let end = body[1..]
        .find("\n    fn ")
        .map(|rel| rel + 1)
        .unwrap_or(body.len());
    let body = &body[..end];
    assert!(
        body.contains("TokensNotSorted"),
        "estimate_swap should recover the TokensNotSorted validation panic, got:\n{body}"
    );
    assert!(
        body.contains("panic_with_error!"),
        "TokensNotSorted should surface as a nested panic_with_error!, got:\n{body}"
    );
}

// `estimate_swap` looks up `token_in`/`token_out` with `Vec::first_index_of`, whose
// `Option<u32>` result the SDK decodes with a tiny helper and `br_table`s on the
// tag (`None`/object → unreachable, `Some(small)` → continue, i.e. `.unwrap()`).
// The tag load used to degrade to `UnknownVal`, discarding the match and rendering
// `if todo!("unknown value") == LiquidityPoolType::ConstantProduct { ... }`. Assert
// the decode is recovered to clean `.first_index_of(..).unwrap()` and the mislabeled
// enum comparison is gone, scoped to the `estimate_swap` body.
#[test]
fn aquarius_estimate_swap_recovers_first_index_of_unwrap() {
    let wasm = include_bytes!("../../../tests/fixtures/aquarius.wasm");
    let src = decompile(wasm).expect("aquarius.wasm should decompile");
    let start = src
        .find("fn estimate_swap(")
        .expect("estimate_swap should be emitted");
    let after = &src[start..];
    let brace_start = after.find('{').expect("no { after fn estimate_swap");
    let mut depth = 0i32;
    let mut end = after.len();
    for (i, c) in after[brace_start..].char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = brace_start + i + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    let body = &after[..end];
    assert!(
        body.contains("first_index_of(token_in).unwrap()")
            && body.contains("first_index_of(token_out).unwrap()"),
        "estimate_swap should recover both first_index_of Option decodes as .unwrap(), got:\n{body}"
    );
    assert!(
        !body.contains("LiquidityPoolType::ConstantProduct"),
        "the first_index_of tag must not be mislabeled as a LiquidityPoolType match, got:\n{body}"
    );
    // Narrowed from a body-wide no-todo assert (issue #36): the body now
    // legitimately carries honest holes where an always-empty
    // `Map::<_, Val>::new(&env)` receiver used to be fabricated. The #12
    // regression this guards is the first_index_of RECEIVER/dispatch decaying
    // back to a lost value.
    assert!(
        !body.contains("first_index_of(todo!") && !body.contains("match todo!"),
        "the recovered first_index_of dispatch should leave no unknown-value todo!, got:\n{body}"
    );
}

#[test]
fn aquarius_recovers_tokens_sorted_validation_loop() {
    // The router's sorted+unique token validation is inlined into ~27 accessors and
    // lifts to a structurally-mangled loop (lost induction/bound, unconditional
    // mid-loop break) leaving ~4 todo!() each. Its intent is recovered from the
    // unique TokensNotSorted + DuplicatesNotAllowed error-code pair, and lifted to a
    // clean `for i in 1..tokens.len() { ... }`.
    let wasm = include_bytes!("../../../tests/fixtures/aquarius.wasm");
    let src = decompile(wasm).expect("aquarius.wasm should decompile");

    let start = src
        .find("fn get_total_outstanding_reward")
        .expect("get_total_outstanding_reward should be emitted");
    let after = &src[start..];
    let brace_start = after.find('{').expect("no { after fn");
    let mut depth = 0i32;
    let mut end = brace_start;
    for (i, c) in after[brace_start..].char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = brace_start + i + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    let body = &after[..end];
    assert!(
        body.contains("for i in 1..tokens.len()"),
        "validation should lift to a clean for-loop, got:\n{body}"
    );
    assert!(
        body.contains("TokensNotSorted") && body.contains("DuplicatesNotAllowed"),
        "recovered validation must keep both panic conditions, got:\n{body}"
    );
    // The mangled loop's todo!()s (induction/bound) must be gone from the
    // recovered validation for-loop. Extract exactly the for-loop block by brace
    // matching (a robust boundary, independent of whatever code follows it).
    let val_start = body
        .find("for i in 1..tokens.len()")
        .expect("for-loop present");
    let val = &body[val_start..];
    let vbrace = val.find('{').expect("no { after for");
    let mut d = 0i32;
    let mut vend = vbrace;
    for (i, c) in val[vbrace..].char_indices() {
        match c {
            '{' => d += 1,
            '}' => {
                d -= 1;
                if d == 0 {
                    vend = vbrace + i + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    assert!(
        !val[..vend].contains("todo!"),
        "recovered validation loop must have no todo!, got:\n{}",
        &val[..vend]
    );
}

#[test]
fn aquarius_recovers_invoke_return_types_and_drops_tag_assert_husks() {
    // A cross-contract `invoke_contract` whose result feeds the SDK's `Val -> T`
    // type assertion lifts as `invoke::<Val>(...); if todo!() != 69 { panic!() }`.
    // The tag (69 = I128Object) names the return type, so the invoke is typed
    // `::<i128>` and the husk is dropped — but only genuine type tags in bare-
    // panic assertion form; ambiguous tags (Tag::True == 1) stay untouched.
    let wasm = include_bytes!("../../../tests/fixtures/aquarius.wasm");
    let src = decompile(wasm).expect("aquarius.wasm should decompile");

    let start = src
        .find("fn get_total_outstanding_reward")
        .expect("get_total_outstanding_reward should be emitted");
    let after = &src[start..];
    let brace_start = after.find('{').expect("no { after fn");
    let mut depth = 0i32;
    let mut end = brace_start;
    for (i, c) in after[brace_start..].char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = brace_start + i + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    let body = &after[..end];

    // The balance invoke's I128Object assertion recovers an `i128` return type.
    assert!(
        body.contains("invoke_contract::<i128>"),
        "i128 invoke return type should be recovered, got:\n{body}"
    );
    // The bare-panic type-tag assertion husks (I128Object / VecObject) are gone.
    assert!(
        !body.contains("!= 69 {") && !body.contains("!= 75 {"),
        "SDK Val->T type-assertion husks should be dropped, got:\n{body}"
    );
    // ...but the ambiguous `== 1` guard (Tag::True, not a type assertion) stays
    // as an `if` with its `panic!()` body: dropping it would be a wrong
    // recovery, not noise removal. Since t14 the condition itself renders as
    // `todo!()` (comparing an unknown value against 1 is unknown, and
    // `todo!() == 1` is a guaranteed E0277 — `!` falls back to `()` in operator
    // traits), so the preserved guard reads `if todo!("unknown value") { panic!(); }`.
    assert!(
        body.contains("if todo!(\"unknown value\") {\n            panic!();"),
        "ambiguous non-type-tag guards must be preserved (as an if-with-panic \
         whose condition is an honest hole), got:\n{body}"
    );
}

#[test]
fn aquarius_recovers_descriptor_pointer_datakey_storage_keys() {
    // Long-symbol storage keys built via a constant descriptor-pointer chain
    // (`126 → 270 → 66 → 64 → encoder`): the `(i32 desc_ptr) -> i64` key
    // constructor reads a 1-byte enum discriminant from static data and builds the
    // key Symbol. Previously these accessors degraded to `get(&todo!())` because the
    // recovered symbol never reached the storage op; now the constructor resolves the
    // variant name from its own ordered string table, indexed by the discriminant.
    let wasm = include_bytes!("../../../tests/fixtures/aquarius.wasm");
    let src = decompile(wasm).expect("aquarius.wasm should decompile");

    let start = src
        .find("fn get_conc_pool_payment_amount")
        .expect("get_conc_pool_payment_amount should be emitted");
    let after = &src[start..];
    // Extract exactly the function body by matching braces.
    let brace_start = after.find('{').expect("no { after fn get_conc");
    let mut depth = 0i32;
    let mut end = brace_start;
    for (i, c) in after[brace_start..].char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = brace_start + i + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    let body = &after[..end];
    assert!(
        body.contains(r#"Symbol::new(&env, "InitConcentratedPoolPaymentAmt")"#),
        "get_conc should recover the long-symbol DataKey, got:\n{body}"
    );
    assert!(
        !body.contains("todo!"),
        "get_conc should have no todo! after key recovery, got:\n{body}"
    );

    // Sibling accessors through the same constructor resolve their own discriminants.
    assert!(
        src.contains(r#"Symbol::new(&env, "InitPoolPaymentToken")"#),
        "get_init_pool_payment_token should recover its key symbol"
    );
    assert!(
        src.contains(r#"Symbol::new(&env, "InitStablePoolPaymentAmount")"#),
        "get_stable_pool_payment_amount should recover its key symbol"
    );
}

// TODO(#11): inspection harness for the still-truncated `estimate_swap` case.
// The locus-1 CFG-of-safety-net-unreachable fix landed but does not address
// estimate_swap, whose truncation is driven by a top-level `PanicWithError`
// from an inlined `call $fail_with_error` (separate follow-up).
#[test]
#[ignore]
fn _dump_aquarius_estimate_swap() {
    let wasm = include_bytes!("../../../tests/fixtures/aquarius.wasm");
    let src = decompile(wasm).expect("aquarius.wasm should decompile");
    let Some(start) = src.find("fn estimate_swap") else {
        panic!("estimate_swap not found in output");
    };
    let after = &src[start..];
    let brace_start = after.find('{').expect("no { after fn estimate_swap");
    let mut depth = 0i32;
    let mut end = brace_start;
    for (i, c) in after[brace_start..].char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = brace_start + i + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    eprintln!("--- estimate_swap body ---\n{}\n--- end ---", &after[..end]);
}

// TODO(#11): same as above for the test_fuzz `run` function — kept as a
// canary for any future regression that might confuse user-explicit `panic!()`
// (which compiles to `call $rust_panic_helper; unreachable`) with a safety-net
// trap.
#[test]
#[ignore]
fn _dump_test_fuzz_run() {
    let wasm = include_bytes!("../../../tests/fixtures/test_fuzz.wasm");
    let src = decompile(wasm).expect("test_fuzz.wasm should decompile");
    eprintln!("--- full test_fuzz source ---\n{}\n--- end ---", src);
}

// TODO(#11): count todo!() occurrences in aquarius/blend to track progress.
// Note: this count is a *surface* metric, not a quality one. Fixing truncation
// elsewhere typically EXPOSES previously-hidden code that contains more
// `todo!()` placeholders, so the number can go up while decompilation quality
// improves. Compare against the body shape (see _dump_*) when interpreting.
//
// Phase-3 baseline (constant-`br_table` dispatch folding landed): aquarius 726,
// blend 74 — down from aquarius 1118 after `fold_constant_matches` learned to
// evaluate mixed-literal-type constant selectors (`i64(2) - i32(1)`) via
// `const_eval_i128`, collapsing inlined storage-key builders to their single
// live arm. The remaining tail is the hard class: host-call results / frame-slot
// values the lifter degrades to `UnknownVal` across control-flow boundaries
// (~252 in guards, ~171 in runtime-discriminant dispatches, ~28 loop-carry
// inits). Recovering those needs lifter SSA/loop-carry propagation, not an
// optimizer rewrite.
#[test]
#[ignore]
fn _count_aquarius_blend_todos() {
    let aquarius = decompile(include_bytes!("../../../tests/fixtures/aquarius.wasm"))
        .expect("aquarius decompile");
    let blend =
        decompile(include_bytes!("../../../tests/fixtures/blend.wasm")).expect("blend decompile");
    eprintln!(
        "[#11 progress] aquarius todo!() count = {}",
        aquarius.matches("todo!(").count()
    );
    eprintln!(
        "[#11 progress] blend todo!() count = {}",
        blend.matches("todo!(").count()
    );
}

#[test]
fn blend_decompiles_without_panicking() {
    let wasm = include_bytes!("../../../tests/fixtures/blend.wasm");
    let src = decompile(wasm).expect("blend.wasm should decompile");
    assert!(!src.is_empty(), "blend should produce output");
}

// -------------------------------------------------------------------------
// Snapshot tests
//
// Substring assertions (`assert_ordered` / `assert_in_fn`) catch missing
// content but accept any whitespace, attribute order, or trailing junk.
// Snapshot the three most attribute-heavy fixtures so the full decompiled
// shape (line breaks, attribute order, trailing newlines) is regression-
// protected end-to-end. Run `cargo insta review` to accept intentional
// changes.
// -------------------------------------------------------------------------

#[test]
fn snapshot_test_errors() {
    let wasm = include_bytes!("../../../tests/fixtures/test_errors.wasm");
    let source = decompile(wasm).expect("decompile test_errors");
    insta::assert_snapshot!("test_errors", source);
}

#[test]
fn snapshot_test_events() {
    let wasm = include_bytes!("../../../tests/fixtures/test_events.wasm");
    let source = decompile(wasm).expect("decompile test_events");
    insta::assert_snapshot!("test_events", source);
}

#[test]
fn snapshot_contract_with_constructor() {
    let wasm = include_bytes!("../../../tests/fixtures/contract_with_constructor.wasm");
    let source = decompile(wasm).expect("decompile contract_with_constructor");
    insta::assert_snapshot!("contract_with_constructor", source);
}

/// Regression for issue #6 (iterative/fixpoint dataflow over loops). A bounded
/// loop with a loop-carried accumulator must recover the accumulation as a
/// mutable variable the loop updates, instead of dropping the loop body and
/// emitting `todo!()`. The fixture computes `sum(0..5)`.
#[test]
fn loop_carried_accumulator_is_recovered() {
    let wat = r#"(module
      (func (export "accumulate") (result i64)
        (local $i i64) (local $acc i64)
        (local.set $i (i64.const 0))
        (local.set $acc (i64.const 0))
        (block $exit
          (loop $top
            (br_if $exit (i64.eq (local.get $i) (i64.const 5)))
            (local.set $acc (i64.add (local.get $acc) (local.get $i)))
            (local.set $i (i64.add (local.get $i) (i64.const 1)))
            (br $top)))
        (local.get $acc)))"#;
    let wasm = wat::parse_str(wat).expect("assemble wat");
    let source = decompile(&wasm).expect("decompilation failed");

    // The loop body is recovered, not dropped to a stub.
    assert!(
        !source.contains("todo!"),
        "loop dropped to todo!():\n{source}"
    );
    // The accumulator (var_1) becomes a `let mut` declared before the loop.
    assert!(
        source.contains("let mut var_1 = 0"),
        "accumulator not recovered as `let mut`:\n{source}"
    );
    // The counter is dead after the loop, so the counted loop renders as a
    // `for` over the recovered range (DoD #2) rather than a `while`.
    assert!(
        source.contains("for var_0 in 0..5"),
        "counted loop not rendered as a `for` range:\n{source}"
    );
    // The accumulation `acc = acc + i` runs in the loop body, and the explicit
    // counter step is gone (the range steps it).
    assert!(
        source.contains("var_1 = (var_1 + var_0)"),
        "accumulation not recovered:\n{source}"
    );
    assert!(
        !source.contains("var_0 = (var_0 + 1)"),
        "counter step should be subsumed by the `for` range:\n{source}"
    );
    // The function returns the accumulated value.
    assert!(
        source.contains("var_1\n") || source.contains("var_1 }"),
        "missing tail return of accumulator:\n{source}"
    );
}

/// Regression for issue #6 — the headline aquarius case: a loop-carried
/// accumulator spilled to the shadow-stack frame (the Rust SDK's
/// `global.get 0; i32.sub; local.tee; global.set 0` frame) round-trips through
/// linear memory each iteration. Baseline degraded the self-referential slot to
/// `UnknownVal` and the function returned nothing (`todo!`). It must now be
/// promoted to a `let mut` scalar the loop mutates, and the post-loop load must
/// return it. The fixture computes `sum(0..5)` through a frame slot.
#[test]
fn loop_carried_frame_slot_accumulator_is_recovered() {
    let wat = r#"(module
      (memory (export "memory") 1)
      (global (mut i32) (i32.const 65536))
      (func (export "sum_spilled") (result i64)
        (local $fp i32) (local $i i64)
        (global.set 0 (local.tee $fp (i32.sub (global.get 0) (i32.const 16))))
        (i64.store offset=8 (local.get $fp) (i64.const 0))
        (local.set $i (i64.const 0))
        (block $exit
          (loop $top
            (br_if $exit (i64.eq (local.get $i) (i64.const 5)))
            (i64.store offset=8 (local.get $fp)
              (i64.add (i64.load offset=8 (local.get $fp)) (local.get $i)))
            (local.set $i (i64.add (local.get $i) (i64.const 1)))
            (br $top)))
        (global.set 0 (i32.add (local.get $fp) (i32.const 16)))
        (i64.load offset=8 (local.get $fp))))"#;
    let wasm = wat::parse_str(wat).expect("assemble wat");
    let source = decompile(&wasm).expect("decompilation failed");

    // The spilled value is recovered: no dropped body, a `while`, and the
    // accumulator + counter both become mutable variables the loop updates.
    assert!(
        !source.contains("todo!"),
        "spilled accumulator dropped to todo!():\n{source}"
    );
    // The promoted frame slot becomes a `let mut` and the counted loop renders
    // as a `for` over the recovered range with the counter scoped to it.
    assert!(
        source.contains("let mut") && source.contains("for var_1 in 0..5"),
        "frame-slot loop not recovered as a `for` range:\n{source}"
    );
    // The accumulator (promoted frame slot var_2) is summed across iterations
    // and returned.
    assert!(
        source.contains("var_2 = (var_2 + var_1)"),
        "spilled accumulation not recovered:\n{source}"
    );
}

/// Issue #6 robustness: step, direction, and liveness variants of recovered
/// counted loops, plus a never-crash check for unhandled shapes.
#[test]
fn loop_recovery_loop_variants() {
    let decomp = |wat: &str| {
        let wasm = wat::parse_str(wat).expect("wat assembles");
        decompile(&wasm).expect("decompile must not error")
    };

    // Non-unit step renders a `.step_by` range. (sum of 0,2,4)
    let step2 = decomp(
        r#"(module (func (export "f") (result i64)
            (local $i i64) (local $acc i64)
            (local.set $i (i64.const 0)) (local.set $acc (i64.const 0))
            (block $e (loop $t
              (br_if $e (i64.eq (local.get $i) (i64.const 6)))
              (local.set $acc (i64.add (local.get $acc) (local.get $i)))
              (local.set $i (i64.add (local.get $i) (i64.const 2))) (br $t)))
            (local.get $acc)))"#,
    );
    assert!(
        step2.contains("for var_0 in (0..6).step_by(2)"),
        "non-unit step not rendered as step_by range:\n{step2}"
    );
    assert!(
        !step2.contains("todo!"),
        "step2 regressed to todo!:\n{step2}"
    );

    // A descending counter is recovered but stays a `while` (a `for` range can't
    // count down), not dropped to `todo!`.
    let down = decomp(
        r#"(module (func (export "f") (result i64)
            (local $i i64) (local $acc i64)
            (local.set $i (i64.const 5)) (local.set $acc (i64.const 0))
            (block $e (loop $t
              (br_if $e (i64.eq (local.get $i) (i64.const 0)))
              (local.set $acc (i64.add (local.get $acc) (local.get $i)))
              (local.set $i (i64.sub (local.get $i) (i64.const 1))) (br $t)))
            (local.get $acc)))"#,
    );
    assert!(
        down.contains("while var_0 != 0") && !down.contains("for var_0"),
        "descending counter should stay a while, not a for:\n{down}"
    );
    assert!(
        !down.contains("todo!"),
        "countdown regressed to todo!:\n{down}"
    );

    // A counter read after the loop is live-out: `for` would scope it away, so
    // the loop must stay a `while`.
    let live = decomp(
        r#"(module (func (export "f") (result i64)
            (local $i i64) (local $acc i64)
            (local.set $i (i64.const 0)) (local.set $acc (i64.const 0))
            (block $e (loop $t
              (br_if $e (i64.eq (local.get $i) (i64.const 5)))
              (local.set $acc (i64.add (local.get $acc) (local.get $i)))
              (local.set $i (i64.add (local.get $i) (i64.const 1))) (br $t)))
            (i64.add (local.get $i) (local.get $acc))))"#,
    );
    assert!(
        live.contains("while var_0 != 5") && !live.contains("for var_0"),
        "live-out counter must keep the loop a while:\n{live}"
    );

    // Unhandled shapes must degrade gracefully (no panic, no error) — nested
    // counted loops and an infinite loop with no counter.
    let _ = decomp(
        r#"(module (func (export "f") (result i64)
            (local $i i64) (local $j i64) (local $acc i64)
            (local.set $acc (i64.const 0)) (local.set $i (i64.const 0))
            (block $eo (loop $to
              (br_if $eo (i64.eq (local.get $i) (i64.const 3)))
              (local.set $j (i64.const 0))
              (block $ei (loop $ti
                (br_if $ei (i64.eq (local.get $j) (i64.const 3)))
                (local.set $acc (i64.add (local.get $acc) (local.get $j)))
                (local.set $j (i64.add (local.get $j) (i64.const 1))) (br $ti)))
              (local.set $i (i64.add (local.get $i) (i64.const 1))) (br $to)))
            (local.get $acc)))"#,
    );
    let _ = decomp(r#"(module (func (export "f") (loop $t (br $t))))"#);

    // A step that does not evenly reach the `== end` bound must NOT become a
    // `for` range (it would change the iteration count); it stays a `while`.
    let nondiv = decomp(
        r#"(module (func (export "f") (result i64)
            (local $i i64) (local $acc i64)
            (local.set $i (i64.const 0)) (local.set $acc (i64.const 0))
            (block $e (loop $t
              (br_if $e (i64.eq (local.get $i) (i64.const 5)))
              (local.set $acc (i64.add (local.get $acc) (local.get $i)))
              (local.set $i (i64.add (local.get $i) (i64.const 2))) (br $t)))
            (local.get $acc)))"#,
    );
    assert!(
        !nondiv.contains("for var_0"),
        "non-dividing step must not become a for range:\n{nondiv}"
    );

    // An accumulator initialized from a parameter (non-literal init) is NOT
    // recovered — recovering it would rename the `let mut` onto the immutable
    // param, mutating it (non-compiling). Falls back to valid output instead.
    let param_init = decomp(
        r#"(module (func (export "f") (param $base i64) (result i64)
            (local $i i64) (local $acc i64)
            (local.set $acc (local.get $base)) (local.set $i (i64.const 0))
            (block $e (loop $t
              (br_if $e (i64.eq (local.get $i) (i64.const 5)))
              (local.set $acc (i64.add (local.get $acc) (local.get $i)))
              (local.set $i (i64.add (local.get $i) (i64.const 1))) (br $t)))
            (local.get $acc)))"#,
    );
    assert!(
        !param_init.contains("arg0 = ") && !param_init.contains("arg0 +="),
        "must not emit assignment to an immutable parameter:\n{param_init}"
    );
}
