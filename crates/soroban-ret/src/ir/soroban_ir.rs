/// A Soroban-aware expression
#[derive(Debug, Clone, PartialEq)]
pub enum SorobanExpr {
    // Literals
    U32Literal(u32),
    I32Literal(i32),
    U64Literal(u64),
    I64Literal(i64),
    U128Literal(u128),
    I128Literal(i128),
    BoolLiteral(bool),
    SymbolLiteral(String),
    StringLiteral(String),
    BytesLiteral(Vec<u8>),
    Void,
    /// Rust `None` for Option-typed fields where the decompiled value is Void/unknown.
    None,
    /// Rust `Some(inner)` for Option-typed values recovered from Option-return
    /// marshalling (e.g. `if cond { None } else { Some(vec.first_unchecked()) }`).
    Some(Box<SorobanExpr>),

    // Variables
    Param(String),
    Local(u32),
    /// A local variable with a propagated meaningful name (from spec-driven naming).
    NamedLocal(String),
    Env,

    // Arithmetic
    Add(Box<SorobanExpr>, Box<SorobanExpr>),
    Sub(Box<SorobanExpr>, Box<SorobanExpr>),
    Mul(Box<SorobanExpr>, Box<SorobanExpr>),
    Div(Box<SorobanExpr>, Box<SorobanExpr>),
    Rem(Box<SorobanExpr>, Box<SorobanExpr>),

    // Comparison
    Eq(Box<SorobanExpr>, Box<SorobanExpr>),
    Ne(Box<SorobanExpr>, Box<SorobanExpr>),
    Lt(Box<SorobanExpr>, Box<SorobanExpr>),
    Le(Box<SorobanExpr>, Box<SorobanExpr>),
    Gt(Box<SorobanExpr>, Box<SorobanExpr>),
    Ge(Box<SorobanExpr>, Box<SorobanExpr>),

    // Logical
    And(Box<SorobanExpr>, Box<SorobanExpr>),
    Or(Box<SorobanExpr>, Box<SorobanExpr>),
    Not(Box<SorobanExpr>),

    // Storage operations
    StorageGet {
        storage_type: StorageType,
        key: Box<SorobanExpr>,
        unwrap: bool,
        /// `Some(err)` renders `.get(&k).ok_or(err)` instead of
        /// `.get(&k).unwrap()` / `.get(&k)`. Recovered from a fallible-get helper
        /// whose missing-key path returns a contract error (`err` is always a
        /// `ContractError`). Mutually exclusive with `unwrap` (when `Some`,
        /// `unwrap` is `false`). All other construction sites set `None`, leaving
        /// their output byte-identical.
        on_missing: Option<Box<SorobanExpr>>,
    },
    StorageSet {
        storage_type: StorageType,
        key: Box<SorobanExpr>,
        value: Box<SorobanExpr>,
    },
    StorageHas {
        storage_type: StorageType,
        key: Box<SorobanExpr>,
    },
    StorageRemove {
        storage_type: StorageType,
        key: Box<SorobanExpr>,
    },
    StorageExtendTtl {
        storage_type: StorageType,
        key: Box<SorobanExpr>,
        threshold: Box<SorobanExpr>,
        extend_to: Box<SorobanExpr>,
    },
    ExtendInstanceAndCodeTtl {
        threshold: Box<SorobanExpr>,
        extend_to: Box<SorobanExpr>,
    },

    // Auth
    RequireAuth(Box<SorobanExpr>),
    RequireAuthForArgs {
        address: Box<SorobanExpr>,
        args: Box<SorobanExpr>,
    },
    AuthorizeAsCurrContract(Box<SorobanExpr>),

    // Events
    PublishEvent {
        event_name: Option<String>,
        topics: Vec<SorobanExpr>,
        data: Box<SorobanExpr>,
    },

    // Cross-contract calls
    InvokeContract {
        address: Box<SorobanExpr>,
        function: Box<SorobanExpr>,
        args: Vec<SorobanExpr>,
        /// Inferred return type for the generic parameter (e.g., "u64").
        /// When `None`, codegen emits `soroban_sdk::Val`.
        return_type: Option<String>,
    },
    TryInvokeContract {
        address: Box<SorobanExpr>,
        function: Box<SorobanExpr>,
        args: Vec<SorobanExpr>,
        /// Inferred return type for the generic parameter.
        return_type: Option<String>,
    },

    // Type construction
    StructConstruct {
        type_name: String,
        fields: Vec<(String, SorobanExpr)>,
    },
    EnumConstruct {
        type_name: String,
        variant: String,
        fields: Vec<SorobanExpr>,
    },
    TupleConstruct(Vec<SorobanExpr>),
    VecConstruct(Vec<SorobanExpr>),
    MapConstruct(Vec<(SorobanExpr, SorobanExpr)>),

    // Type access
    FieldAccess {
        object: Box<SorobanExpr>,
        field: String,
    },
    MethodCall {
        object: Box<SorobanExpr>,
        method: String,
        args: Vec<SorobanExpr>,
    },

    // Error handling
    ContractError {
        error_code: u32,
        error_type: Option<String>,
        variant_name: Option<String>,
    },
    ErrorFromCode(Box<SorobanExpr>),
    /// Represents `panic_with_error!(&env, error)` — a call to fail_with_error host function.
    PanicWithError(Box<SorobanExpr>),
    /// Represents `panic!()` — from a WASM `unreachable`-only function (e.g. `panic!("fail")`).
    Panic,

    // Crypto
    CryptoSha256(Box<SorobanExpr>),
    CryptoKeccak256(Box<SorobanExpr>),
    CryptoEd25519Verify {
        public_key: Box<SorobanExpr>,
        message: Box<SorobanExpr>,
        signature: Box<SorobanExpr>,
    },
    CryptoSecp256k1Recover {
        msg_digest: Box<SorobanExpr>,
        signature: Box<SorobanExpr>,
        recovery_id: Box<SorobanExpr>,
    },

    // Ledger info
    LedgerSequence,
    LedgerTimestamp,
    LedgerNetworkId,
    CurrentContractAddress,
    MaxLiveUntilLedger,

    // PRNG
    PrngReseed(Box<SorobanExpr>),
    PrngBytesNew(Box<SorobanExpr>),
    PrngU64InRange {
        low: Box<SorobanExpr>,
        high: Box<SorobanExpr>,
    },
    PrngVecShuffle(Box<SorobanExpr>),

    // Address operations
    StrkeyToAddress(Box<SorobanExpr>),
    AddressToStrkey(Box<SorobanExpr>),

    // Logging
    Log(Vec<SorobanExpr>),

    // Collection constructors: Vec::new(&env), Map::new(&env)
    CollectionNew(String),

    // Fallback for unrecognized patterns
    RawHostCall {
        module: String,
        function: String,
        args: Vec<SorobanExpr>,
    },

    // Placeholder for unknown/untracked stack values
    UnknownVal,

    // A frame slot whose stored value transitively references itself — a genuine
    // data cycle the lifter cannot resolve to a value. Reported precisely (with
    // the slot identity) instead of collapsing to an anonymous `UnknownVal`.
    CyclicSlot {
        frame_id: u32,
        offset: i32,
    },

    // The symbolic `Result` discriminant of an sret (struct-return) call: a void
    // helper / cross-contract call that wrote its `Result<T, E>` into a frame
    // slot. Produced when a load of that slot feeds a br_table/if, so the
    // dispatch reconstructs as `match <call> { Ok(..) => .., Err(..) => .. }`.
    // Wraps the call expression. If it reaches codegen verbatim it degrades to
    // that inner call.
    SretResult(Box<SorobanExpr>),

    // The 8-bit Soroban Val tag of a value, recovered from a `v & 0xFF` pattern.
    // Renders as `<value>.get_tag()`.
    ValTag(Box<SorobanExpr>),
    // A named Soroban Val tag constant (e.g. `VecObject`), recovered as the
    // right-hand side of a tag comparison. Renders as `Tag::<name>`.
    ValTagName(String),

    // Val type conversion (for patterns we couldn't fully lift)
    ValConvert {
        value: Box<SorobanExpr>,
        target_type: String,
    },

    // Rust `as` cast (e.g., `val as i64`)
    CastAs {
        value: Box<SorobanExpr>,
        target_type: String,
    },

    // Rust `?` operator: `<inner>?`. Used to recover a computed getter's leading
    // fallible storage read as an early-return guard
    // (`get::<_, Val>(&key).ok_or(Error::V)?;`) when the value it produces feeds
    // now-lost downstream arithmetic, so only the missing-key `Err` path is faithful.
    Try(Box<SorobanExpr>),

    // `<vec>.try_iter().fold(<init>, |sum, i| sum + i.unwrap())` — the SDK's
    // overflow-checked sum over a `Vec<i64>`. Recovered from the `vec_len`-seeded
    // iterator loop (udt::add UdtD arm). The closure body is a fixed idiom; only
    // the receiver and the fold init vary.
    VecTryIterFold {
        vec: Box<SorobanExpr>,
        init: Box<SorobanExpr>,
    },
}

impl SorobanExpr {
    /// A `!`-rooted expression: `todo!()`/`panic!()` itself, a method/field
    /// chain hanging off one, or an arithmetic/comparison operator with a `!`
    /// operand. All of these are guaranteed rustc errors (method resolution on
    /// `!` is E0599/E0609; operator traits on `!` fall back to `()` — E0277
    /// "can't compare `()` with `i32`" and friends), and at runtime the `!`
    /// root panics before the rest of the expression evaluates — so rendering
    /// the whole expression as `todo!()` is exact, not lossy.
    ///
    /// A right-operand-only `!` counts ONLY when the left operand is
    /// effect-free: Rust evaluates left-to-right, so collapsing `set(..) - todo!()`
    /// would skip a real side effect, while `x - todo!()` panics identically.
    /// `&&`/`||` are deliberately NOT included: `todo!() && b` type-checks
    /// (plain `bool` coercion, no operator trait), so those renders stand.
    pub(crate) fn is_never_rooted(&self) -> bool {
        match self {
            SorobanExpr::UnknownVal | SorobanExpr::Panic | SorobanExpr::PanicWithError(_) => true,
            SorobanExpr::MethodCall { object, .. } | SorobanExpr::FieldAccess { object, .. } => {
                object.is_never_rooted()
            }
            // Renders bare (no syntactic type pin), so a `!` root shows through.
            // `CastAs` is deliberately NOT here: `todo!() as u128` pins a real
            // type, and methods on it resolve.
            SorobanExpr::ValConvert { value, .. } => value.is_never_rooted(),
            SorobanExpr::Add(a, b)
            | SorobanExpr::Sub(a, b)
            | SorobanExpr::Mul(a, b)
            | SorobanExpr::Div(a, b)
            | SorobanExpr::Rem(a, b)
            | SorobanExpr::Eq(a, b)
            | SorobanExpr::Ne(a, b)
            | SorobanExpr::Lt(a, b)
            | SorobanExpr::Le(a, b)
            | SorobanExpr::Gt(a, b)
            | SorobanExpr::Ge(a, b) => {
                a.is_never_rooted() || (b.is_never_rooted() && a.is_effect_free())
            }
            SorobanExpr::Not(a) => a.is_never_rooted(),
            _ => false,
        }
    }

    /// Conservatively side-effect-free: re-ordering or skipping its evaluation
    /// is unobservable. Literals, variable references, and pure environment
    /// reads only — any host call that writes (or that we are not certain
    /// about) is excluded.
    pub(crate) fn is_effect_free(&self) -> bool {
        match self {
            SorobanExpr::U32Literal(_)
            | SorobanExpr::I32Literal(_)
            | SorobanExpr::U64Literal(_)
            | SorobanExpr::I64Literal(_)
            | SorobanExpr::U128Literal(_)
            | SorobanExpr::I128Literal(_)
            | SorobanExpr::BoolLiteral(_)
            | SorobanExpr::SymbolLiteral(_)
            | SorobanExpr::StringLiteral(_)
            | SorobanExpr::BytesLiteral(_)
            | SorobanExpr::Void
            | SorobanExpr::None
            | SorobanExpr::Param(_)
            | SorobanExpr::Local(_)
            | SorobanExpr::NamedLocal(_)
            | SorobanExpr::Env
            | SorobanExpr::LedgerSequence
            | SorobanExpr::LedgerTimestamp
            | SorobanExpr::CurrentContractAddress => true,
            SorobanExpr::FieldAccess { object, .. } => object.is_effect_free(),
            SorobanExpr::CastAs { value, .. } | SorobanExpr::ValConvert { value, .. } => {
                value.is_effect_free()
            }
            SorobanExpr::Not(a) => a.is_effect_free(),
            // Div/Rem are excluded: divide-by-zero traps, which is an effect.
            SorobanExpr::Add(a, b)
            | SorobanExpr::Sub(a, b)
            | SorobanExpr::Mul(a, b)
            | SorobanExpr::Eq(a, b)
            | SorobanExpr::Ne(a, b)
            | SorobanExpr::Lt(a, b)
            | SorobanExpr::Le(a, b)
            | SorobanExpr::Gt(a, b)
            | SorobanExpr::Ge(a, b) => a.is_effect_free() && b.is_effect_free(),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageType {
    Persistent,
    Temporary,
    Instance,
}

/// A Soroban-aware statement
#[derive(Debug, Clone)]
pub enum SorobanStmt {
    Expr(SorobanExpr),
    Let {
        name: String,
        mutable: bool,
        value: SorobanExpr,
    },
    Assign {
        target: String,
        value: SorobanExpr,
    },
    Return(Option<SorobanExpr>),
    If {
        condition: SorobanExpr,
        then_body: Vec<SorobanStmt>,
        else_body: Vec<SorobanStmt>,
    },
    Match {
        scrutinee: SorobanExpr,
        arms: Vec<MatchArm>,
    },
    Loop {
        body: Vec<SorobanStmt>,
    },
    /// A counted `for var in start..end` loop (with an optional non-unit step,
    /// rendered via `.step_by`). Produced by the optimizer when a recovered
    /// counted loop's induction variable is dead after the loop.
    For {
        var: String,
        start: SorobanExpr,
        end: SorobanExpr,
        step: i64,
        body: Vec<SorobanStmt>,
    },
    Block(Vec<SorobanStmt>),
    Comment(String),
    Break,
    Continue,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: MatchPattern,
    pub body: Vec<SorobanStmt>,
}

#[derive(Debug, Clone)]
pub enum MatchPattern {
    Literal(SorobanExpr),
    EnumVariant {
        type_name: String,
        variant: String,
        bindings: Vec<String>,
    },
    Wildcard,
}
