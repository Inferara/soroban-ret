//! Exercises the `ir_assertions` fluent DSL against real decompiled IR.
//!
//! Besides validating the decompiler's recovered IR (signatures, type kinds,
//! variant/field structure, body operations), this test is what keeps the
//! `ir_assertions` module live — it is otherwise unreferenced API surface.

use soroban_ret::decompile_to_ir;
use soroban_ret::ir::{MatchArm, MatchPattern, SorobanExpr, SorobanStmt, StorageType};
use soroban_ret_accuracy::ir_assertions::{
    ContractAssertions, collect_exprs, count_exprs, walk_exprs, walk_stmts,
};

const ADD_U64: &[u8] = include_bytes!("../../../tests/fixtures/test_add_u64.wasm");
const ERRORS: &[u8] = include_bytes!("../../../tests/fixtures/test_errors.wasm");
const UDT: &[u8] = include_bytes!("../../../tests/fixtures/test_udt.wasm");
const FUZZ: &[u8] = include_bytes!("../../../tests/fixtures/test_fuzz.wasm");
const EVENTS: &[u8] = include_bytes!("../../../tests/fixtures/test_events.wasm");
const CONSTRUCTOR: &[u8] = include_bytes!("../../../tests/fixtures/test_constructor.wasm");

// Feature-diverse fixtures: between them their bodies exercise the bulk of the
// `walk_expr`/`walk_stmt` arms (binops, method calls, field access, matches,
// loops, storage, auth, events, cross-contract calls, crypto, logging).
const WALK_FIXTURES: &[(&str, &[u8])] = &[
    ("errors", ERRORS),
    ("udt", UDT),
    ("add_u64", ADD_U64),
    ("fuzz", FUZZ),
    ("events", EVENTS),
    (
        "logging",
        include_bytes!("../../../tests/fixtures/test_logging.wasm"),
    ),
    (
        "invoke_contract",
        include_bytes!("../../../tests/fixtures/test_invoke_contract.wasm"),
    ),
    (
        "auth",
        include_bytes!("../../../tests/fixtures/test_auth.wasm"),
    ),
    (
        "bls",
        include_bytes!("../../../tests/fixtures/test_bls.wasm"),
    ),
    ("constructor", CONSTRUCTOR),
    (
        "tuples",
        include_bytes!("../../../tests/fixtures/test_tuples.wasm"),
    ),
];

#[test]
fn add_u64_signatures_and_body() {
    let ir = decompile_to_ir(ADD_U64).expect("decompile add_u64");
    let c = ContractAssertions::new(&ir.contract_module, &ir.registry);

    c.assert_fn("add")
        .has_param("a", "u64")
        .has_param("b", "u64")
        .returns("u64")
        // `add` must actually compute an addition in its body.
        .body_contains_expr(|e| matches!(e, SorobanExpr::Add(..)));
}

#[test]
fn errors_types_and_signature() {
    let ir = decompile_to_ir(ERRORS).expect("decompile errors");
    let c = ContractAssertions::new(&ir.contract_module, &ir.registry);

    c.assert_type("Flag")
        .is_enum()
        .has_variant("A")
        .has_variant("E");
    c.assert_type("Error").is_enum().has_variant("AnError");
    c.assert_fn("hello").has_param("flag", "Flag");
}

#[test]
fn udt_type_structure() {
    let ir = decompile_to_ir(UDT).expect("decompile udt");
    let c = ContractAssertions::new(&ir.contract_module, &ir.registry);

    // Data-carrying union: UdtB(UdtStruct) must be recognized as a tuple variant.
    c.assert_type("UdtEnum")
        .is_union()
        .has_variant("UdtA")
        .has_variant("UdtB")
        .variant_has_data("UdtB");
    // Plain discriminant enum.
    c.assert_type("UdtEnum2")
        .is_enum()
        .has_variant("A")
        .has_variant("B");
    // Named-field struct.
    c.assert_type("UdtStruct")
        .is_struct()
        .has_field("a")
        .has_field("b")
        .has_field("c");
}

#[test]
fn walkers_traverse_real_ir() {
    let mut total_exprs = 0usize;
    for (name, wasm) in WALK_FIXTURES {
        let ir = decompile_to_ir(wasm).unwrap_or_else(|e| panic!("{name} decompile: {e}"));
        for f in &ir.contract_module.functions {
            // `|_| false` never short-circuits → forces full recursive traversal of
            // every walk_expr / walk_stmt arm reachable in this body.
            let _ = walk_exprs(&f.body, &|_| false);
            let _ = walk_stmts(&f.body, &|_| false);
            // `|_| true` exercises the early-return path.
            let _ = walk_exprs(&f.body, &|_| true);
            let _ = walk_stmts(&f.body, &|_| true);
            // collect_exprs / count_exprs cover the collecting variants of the walk.
            total_exprs += collect_exprs(&f.body).len();
            let _ = count_exprs(&f.body, &|e| matches!(e, SorobanExpr::MethodCall { .. }));
        }
    }
    assert!(
        total_exprs > 0,
        "expected to collect expressions from real IR"
    );
}

#[test]
fn assertion_methods_breadth() {
    // --- errors: counts, signature, body queries, match lookup ---
    let ir = decompile_to_ir(ERRORS).expect("decompile errors");
    let c = ContractAssertions::new(&ir.contract_module, &ir.registry);

    // Dynamic counts keep the assertions executing the methods without hardcoding.
    c.has_function_count(ir.contract_module.functions.len());
    let type_total = ir.contract_module.types.len()
        + ir.contract_module.error_enums.len()
        + ir.contract_module.events.len();
    c.has_type_count(type_total);

    let symbol = |e: &SorobanExpr| matches!(e, SorobanExpr::SymbolLiteral(_));
    let n_symbols = c.assert_fn("hello").count_expr(symbol);
    c.assert_fn("hello")
        .takes_env()
        .has_param("flag", "Flag")
        .has_param_count(1)
        .body_contains_expr(symbol)
        .body_lacks_expr(|e| matches!(e, SorobanExpr::CryptoSha256(_)))
        .body_lacks_stmt(|s| matches!(s, SorobanStmt::For { .. }))
        .has_expr_count(n_symbols, symbol);
    let n_stmts = c.assert_fn("hello").body().len();
    c.assert_fn("hello").has_stmt_count(n_stmts);
    // Match lookup over a Result-returning dispatch (does not assert shape — just
    // exercises the accessor on real IR).
    let _ = c.assert_fn("hello").first_match_arms();
    if let Some(si) = ir.contract_module.standard_interfaces.first() {
        c.has_standard_interface(si);
    }

    // --- add_u64: return type + arithmetic body, body_contains_stmt ---
    let ir = decompile_to_ir(ADD_U64).expect("decompile add_u64");
    ContractAssertions::new(&ir.contract_module, &ir.registry)
        .assert_fn("add")
        .returns("u64")
        .body_contains_stmt(|s| !matches!(s, SorobanStmt::Comment(_)));

    // --- fuzz: a void-returning function ---
    let ir = decompile_to_ir(FUZZ).expect("decompile fuzz");
    ContractAssertions::new(&ir.contract_module, &ir.registry)
        .assert_fn("run")
        .returns_void();

    // --- constructor: constructor detection (name discovered dynamically) ---
    let ir = decompile_to_ir(CONSTRUCTOR).expect("decompile constructor");
    let c = ContractAssertions::new(&ir.contract_module, &ir.registry);
    if let Some(ctor) = ir
        .contract_module
        .functions
        .iter()
        .find(|f| f.is_constructor)
    {
        c.has_constructor();
        c.assert_fn(&ctor.name).is_constructor();
    }

    // --- events: event type kind (name discovered dynamically) ---
    let ir = decompile_to_ir(EVENTS).expect("decompile events");
    let c = ContractAssertions::new(&ir.contract_module, &ir.registry);
    if let Some(ev) = ir.contract_module.events.first() {
        c.assert_type(&ev.name).is_event();
    }
}

// --- Synthetic tree covering every walk_expr / walk_stmt arm -----------------
// Real fixtures don't exercise every IR variant (crypto multi-arg, PRNG, TTL
// extension, map construction, …). This builds one representative per arm group
// and drives the walkers over it so the recursive traversal is fully covered.

fn leaf() -> SorobanExpr {
    SorobanExpr::SymbolLiteral("s".to_string())
}

fn bx(e: SorobanExpr) -> Box<SorobanExpr> {
    Box::new(e)
}

fn one_of_each_expr() -> Vec<SorobanExpr> {
    use SorobanExpr::*;
    vec![
        Add(bx(leaf()), bx(leaf())), // binary-op group
        Not(bx(leaf())),             // unary group
        StorageGet {
            storage_type: StorageType::Persistent,
            key: bx(leaf()),
            unwrap: true,
            on_missing: Option::None,
        },
        StorageSet {
            storage_type: StorageType::Temporary,
            key: bx(leaf()),
            value: bx(leaf()),
        },
        StorageExtendTtl {
            storage_type: StorageType::Instance,
            key: bx(leaf()),
            threshold: bx(leaf()),
            extend_to: bx(leaf()),
        },
        ExtendInstanceAndCodeTtl {
            threshold: bx(leaf()),
            extend_to: bx(leaf()),
        },
        RequireAuthForArgs {
            address: bx(leaf()),
            args: bx(leaf()),
        },
        PublishEvent {
            event_name: Option::Some("e".to_string()),
            topics: vec![leaf()],
            data: bx(leaf()),
        },
        InvokeContract {
            address: bx(leaf()),
            function: bx(leaf()),
            args: vec![leaf()],
            return_type: Option::Some("u64".to_string()),
        },
        TryInvokeContract {
            address: bx(leaf()),
            function: bx(leaf()),
            args: vec![leaf()],
            return_type: Option::None,
        },
        StructConstruct {
            type_name: "S".to_string(),
            fields: vec![("f".to_string(), leaf())],
        },
        EnumConstruct {
            type_name: "E".to_string(),
            variant: "V".to_string(),
            fields: vec![leaf()],
        },
        TupleConstruct(vec![leaf()]),
        VecConstruct(vec![leaf()]),
        MapConstruct(vec![(leaf(), leaf())]),
        FieldAccess {
            object: bx(leaf()),
            field: "f".to_string(),
        },
        MethodCall {
            object: bx(leaf()),
            method: "m".to_string(),
            args: vec![leaf()],
        },
        CryptoEd25519Verify {
            public_key: bx(leaf()),
            message: bx(leaf()),
            signature: bx(leaf()),
        },
        CryptoSecp256k1Recover {
            msg_digest: bx(leaf()),
            signature: bx(leaf()),
            recovery_id: bx(leaf()),
        },
        PrngU64InRange {
            low: bx(leaf()),
            high: bx(leaf()),
        },
        Log(vec![leaf()]),
        RawHostCall {
            module: "m".to_string(),
            function: "f".to_string(),
            args: vec![leaf()],
        },
        ValConvert {
            value: bx(leaf()),
            target_type: "u64".to_string(),
        },
        CastAs {
            value: bx(leaf()),
            target_type: "i64".to_string(),
        },
        SretResult(bx(leaf())),
        Some(bx(leaf())),
        ValTag(bx(leaf())),
        // leaf arm (no sub-expressions)
        UnknownVal,
        Void,
        None,
        Env,
        Panic,
        LedgerSequence,
        CurrentContractAddress,
        ContractError {
            error_code: 1,
            error_type: Option::None,
            variant_name: Option::None,
        },
        CollectionNew("Vec".to_string()),
        CyclicSlot {
            frame_id: 0,
            offset: 0,
        },
        ValTagName("Tag".to_string()),
        Param("p".to_string()),
        Local(0),
        NamedLocal("n".to_string()),
    ]
}

fn synthetic_body() -> Vec<SorobanStmt> {
    use SorobanStmt::*;
    vec![
        // All representative exprs nested under one Log → walk_expr recurses each.
        Expr(SorobanExpr::Log(one_of_each_expr())),
        Let {
            name: "x".to_string(),
            mutable: true,
            value: leaf(),
        },
        Assign {
            target: "x".to_string(),
            value: leaf(),
        },
        Return(Some(leaf())),
        Return(Option::None),
        If {
            condition: leaf(),
            then_body: vec![Expr(leaf()), Break],
            else_body: vec![Continue],
        },
        Match {
            scrutinee: leaf(),
            arms: vec![
                MatchArm {
                    pattern: MatchPattern::Wildcard,
                    body: vec![Expr(leaf())],
                },
                MatchArm {
                    pattern: MatchPattern::Literal(leaf()),
                    body: vec![Break],
                },
                MatchArm {
                    pattern: MatchPattern::EnumVariant {
                        type_name: "E".to_string(),
                        variant: "V".to_string(),
                        bindings: vec!["x".to_string()],
                    },
                    body: vec![Continue],
                },
            ],
        },
        Loop {
            body: vec![Expr(leaf()), Break],
        },
        Block(vec![Expr(leaf())]),
        For {
            var: "i".to_string(),
            start: leaf(),
            end: leaf(),
            step: 1,
            body: vec![Expr(leaf()), Continue],
        },
        Comment("c".to_string()),
        Break,
        Continue,
    ]
}

#[test]
fn walkers_cover_all_arms_synthetic() {
    let body = synthetic_body();

    // `|_| false` visits every arm without short-circuiting and returns false.
    assert!(!walk_exprs(&body, &|_| false));
    assert!(!walk_stmts(&body, &|_| false));

    // Early-return paths (a present expr / stmt matches).
    assert!(walk_exprs(&body, &|e| matches!(
        e,
        SorobanExpr::SymbolLiteral(_)
    )));
    assert!(walk_stmts(&body, &|s| matches!(s, SorobanStmt::Break)));

    // Collecting variants of the traversal.
    let all = collect_exprs(&body);
    assert!(
        all.len() > 40,
        "expected a rich tree, collected {}",
        all.len()
    );
    assert!(count_exprs(&body, &|e| matches!(e, SorobanExpr::MethodCall { .. })) >= 1);
}
