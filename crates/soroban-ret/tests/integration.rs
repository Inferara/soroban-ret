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
    let wasm = include_bytes!("../../../tests/fixtures/test_alloc.wasm");
    let source = decompile(wasm).expect("decompilation failed");
    assert!(source.contains("pub fn num_list"), "missing num_list fn");
    assert!(
        source.contains("-> Vec<u32>"),
        "missing Vec<u32> return type"
    );
    assert!(source.contains("Vec::new(&env)"), "missing Vec::new(&env)");
    assert!(source.contains("count: u32"), "missing count param");
    assert!(!source.contains("todo!("), "unexpected todo! artifact");
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
// Smoke tests covering all 28 fixtures (18 deliverable + 10 extended)
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
    (
        "test_alloc",
        include_bytes!("../../../tests/fixtures/test_alloc.wasm"),
    ),
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
];

#[test]
fn test_all_fixtures_decompile() {
    for (name, wasm) in ALL_FIXTURES {
        let result = decompile(wasm);
        assert!(result.is_ok(), "{name} failed: {:?}", result.err());
    }
}

#[test]
fn test_all_fixtures_no_artifacts() {
    for (name, wasm) in ALL_FIXTURES {
        let source = decompile(wasm).unwrap_or_else(|e| panic!("{name} failed: {e}"));
        assert!(
            !source.contains("todo!(\"unknown value\")"),
            "{name} has todo!(\"unknown value\") artifact"
        );
        assert!(
            !source.contains("todo!(\"host call"),
            "{name} has unresolved host call artifact"
        );
        // Check for unresolved var_N temporary names
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
