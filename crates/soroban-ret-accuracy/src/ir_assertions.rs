//! Fluent assertion API for testing decompiler IR properties.
//!
//! Provides `ContractAssertions`, `FnAssertions`, and `TypeAssertions` for
//! expressing rich IR-level test expectations without manual tree walking.
//!
//! # Example
//! ```ignore
//! let ir = decompile_to_ir(wasm).unwrap();
//! let c = ContractAssertions::new(&ir.contract_module, &ir.registry);
//! c.assert_fn("add")
//!     .has_param("a", "u64")
//!     .returns("u64")
//!     .body_contains_expr(|e| matches!(e, SorobanExpr::Add(..)));
//! ```

use soroban_ret::codegen::types::generate_type_ident;
use soroban_ret::ir::high_level_ir::TypeDefKind;
use soroban_ret::ir::{ContractFn, ContractModule, MatchArm, SorobanExpr, SorobanStmt};
use soroban_ret::spec::TypeRegistry;
use stellar_xdr::curr::{ScSpecTypeDef, ScSpecUdtUnionCaseV0};

/// Convert a ScSpecTypeDef to a human-readable type string for assertions.
fn type_to_string(spec: &ScSpecTypeDef) -> String {
    let tokens = generate_type_ident(spec);
    tokens.to_string().replace(' ', "")
}

// ---------------------------------------------------------------------------
// Tree walkers
// ---------------------------------------------------------------------------

/// Recursively walk all expressions in a statement tree.
/// Returns `true` if any expression matches the predicate.
pub fn walk_exprs(stmts: &[SorobanStmt], pred: &dyn Fn(&SorobanExpr) -> bool) -> bool {
    for stmt in stmts {
        if walk_stmt_exprs(stmt, pred) {
            return true;
        }
    }
    false
}

fn walk_stmt_exprs(stmt: &SorobanStmt, pred: &dyn Fn(&SorobanExpr) -> bool) -> bool {
    match stmt {
        SorobanStmt::Expr(e) => walk_expr(e, pred),
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            walk_expr(value, pred)
        }
        SorobanStmt::Return(Some(e)) => walk_expr(e, pred),
        SorobanStmt::Return(None) => false,
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            walk_expr(condition, pred) || walk_exprs(then_body, pred) || walk_exprs(else_body, pred)
        }
        SorobanStmt::Match { scrutinee, arms } => {
            walk_expr(scrutinee, pred) || arms.iter().any(|arm| walk_exprs(&arm.body, pred))
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => walk_exprs(body, pred),
        SorobanStmt::For {
            start, end, body, ..
        } => walk_expr(start, pred) || walk_expr(end, pred) || walk_exprs(body, pred),
        SorobanStmt::Comment(_) | SorobanStmt::Break | SorobanStmt::Continue => false,
    }
}

/// Recursively walk an expression tree.
/// Returns `true` if the expression or any sub-expression matches the predicate.
pub fn walk_expr(expr: &SorobanExpr, pred: &dyn Fn(&SorobanExpr) -> bool) -> bool {
    if pred(expr) {
        return true;
    }
    match expr {
        // Binary operations
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
        | SorobanExpr::Ge(a, b)
        | SorobanExpr::And(a, b)
        | SorobanExpr::Or(a, b) => walk_expr(a, pred) || walk_expr(b, pred),

        // Unary
        SorobanExpr::Not(e)
        | SorobanExpr::RequireAuth(e)
        | SorobanExpr::AuthorizeAsCurrContract(e)
        | SorobanExpr::CryptoSha256(e)
        | SorobanExpr::CryptoKeccak256(e)
        | SorobanExpr::PanicWithError(e)
        | SorobanExpr::PrngReseed(e)
        | SorobanExpr::PrngBytesNew(e)
        | SorobanExpr::PrngVecShuffle(e)
        | SorobanExpr::StrkeyToAddress(e)
        | SorobanExpr::AddressToStrkey(e)
        | SorobanExpr::ErrorFromCode(e) => walk_expr(e, pred),

        // Storage ops
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => walk_expr(key, pred),
        SorobanExpr::StorageSet { key, value, .. } => {
            walk_expr(key, pred) || walk_expr(value, pred)
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => walk_expr(key, pred) || walk_expr(threshold, pred) || walk_expr(extend_to, pred),
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => walk_expr(threshold, pred) || walk_expr(extend_to, pred),

        // Auth
        SorobanExpr::RequireAuthForArgs { address, args } => {
            walk_expr(address, pred) || walk_expr(args, pred)
        }

        // Events
        SorobanExpr::PublishEvent { topics, data, .. } => {
            topics.iter().any(|t| walk_expr(t, pred)) || walk_expr(data, pred)
        }

        // Cross-contract calls
        SorobanExpr::InvokeContract {
            address,
            function,
            args,
            ..
        }
        | SorobanExpr::TryInvokeContract {
            address,
            function,
            args,
            ..
        } => {
            walk_expr(address, pred)
                || walk_expr(function, pred)
                || args.iter().any(|a| walk_expr(a, pred))
        }

        // Type construction
        SorobanExpr::StructConstruct { fields, .. } => {
            fields.iter().any(|(_, v)| walk_expr(v, pred))
        }
        SorobanExpr::EnumConstruct { fields, .. } => fields.iter().any(|v| walk_expr(v, pred)),
        SorobanExpr::TupleConstruct(elems) | SorobanExpr::VecConstruct(elems) => {
            elems.iter().any(|e| walk_expr(e, pred))
        }
        SorobanExpr::MapConstruct(pairs) => pairs
            .iter()
            .any(|(k, v)| walk_expr(k, pred) || walk_expr(v, pred)),

        // Type access
        SorobanExpr::FieldAccess { object, .. } => walk_expr(object, pred),
        SorobanExpr::MethodCall { object, args, .. } => {
            walk_expr(object, pred) || args.iter().any(|a| walk_expr(a, pred))
        }
        SorobanExpr::VecTryIterFold { vec, init } => {
            walk_expr(vec, pred) || walk_expr(init, pred)
        }

        // Crypto (multi-arg)
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => walk_expr(public_key, pred) || walk_expr(message, pred) || walk_expr(signature, pred),
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            walk_expr(msg_digest, pred)
                || walk_expr(signature, pred)
                || walk_expr(recovery_id, pred)
        }

        // PRNG
        SorobanExpr::PrngU64InRange { low, high } => walk_expr(low, pred) || walk_expr(high, pred),

        // Logging
        SorobanExpr::Log(args) => args.iter().any(|a| walk_expr(a, pred)),

        // Host call fallback
        SorobanExpr::RawHostCall { args, .. } => args.iter().any(|a| walk_expr(a, pred)),

        // Val convert / cast / wrappers (single sub-expression)
        SorobanExpr::ValConvert { value, .. }
        | SorobanExpr::CastAs { value, .. }
        | SorobanExpr::SretResult(value)
        | SorobanExpr::Some(value)
        | SorobanExpr::ValTag(value) => walk_expr(value, pred),

        // Leaves (no sub-expressions)
        SorobanExpr::U32Literal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::I64Literal(_)
        | SorobanExpr::U128Literal(_)
        | SorobanExpr::I128Literal(_)
        | SorobanExpr::BoolLiteral(_)
        | SorobanExpr::SymbolLiteral(_)
        | SorobanExpr::StringLiteral(_)
        | SorobanExpr::Void
        | SorobanExpr::None
        | SorobanExpr::Param(_)
        | SorobanExpr::Local(_)
        | SorobanExpr::NamedLocal(_)
        | SorobanExpr::Env
        | SorobanExpr::Panic
        | SorobanExpr::LedgerSequence
        | SorobanExpr::LedgerTimestamp
        | SorobanExpr::LedgerNetworkId
        | SorobanExpr::CurrentContractAddress
        | SorobanExpr::MaxLiveUntilLedger
        | SorobanExpr::CollectionNew(_)
        | SorobanExpr::UnknownVal
        | SorobanExpr::BytesLiteral(_)
        | SorobanExpr::CyclicSlot { .. }
        | SorobanExpr::ValTagName(_)
        | SorobanExpr::ContractError { .. } => false,
    }
}

/// Recursively walk all statements in a statement tree.
/// Returns `true` if any statement matches the predicate.
pub fn walk_stmts(stmts: &[SorobanStmt], pred: &dyn Fn(&SorobanStmt) -> bool) -> bool {
    for stmt in stmts {
        if pred(stmt) {
            return true;
        }
        match stmt {
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } if (walk_stmts(then_body, pred) || walk_stmts(else_body, pred)) => {
                return true;
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms {
                    if walk_stmts(&arm.body, pred) {
                        return true;
                    }
                }
            }
            SorobanStmt::Loop { body }
            | SorobanStmt::Block(body)
            | SorobanStmt::For { body, .. }
                if walk_stmts(body, pred) =>
            {
                return true;
            }
            _ => {}
        }
    }
    false
}

/// Collect all expressions in a statement tree.
pub fn collect_exprs(stmts: &[SorobanStmt]) -> Vec<&SorobanExpr> {
    let mut result = Vec::new();
    walk_exprs(stmts, &|e| {
        // We can't push into result from the predicate due to borrow rules,
        // so we use a different approach
        let _ = e;
        false
    });
    // Use a recursive collector instead
    collect_exprs_recursive(stmts, &mut result);
    result
}

fn collect_exprs_recursive<'a>(stmts: &'a [SorobanStmt], out: &mut Vec<&'a SorobanExpr>) {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Expr(e) => collect_expr_recursive(e, out),
            SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
                collect_expr_recursive(value, out)
            }
            SorobanStmt::Return(Some(e)) => collect_expr_recursive(e, out),
            SorobanStmt::Return(None) => {}
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                collect_expr_recursive(condition, out);
                collect_exprs_recursive(then_body, out);
                collect_exprs_recursive(else_body, out);
            }
            SorobanStmt::Match { scrutinee, arms } => {
                collect_expr_recursive(scrutinee, out);
                for arm in arms {
                    collect_exprs_recursive(&arm.body, out);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                collect_exprs_recursive(body, out)
            }
            SorobanStmt::For {
                start, end, body, ..
            } => {
                collect_expr_recursive(start, out);
                collect_expr_recursive(end, out);
                collect_exprs_recursive(body, out);
            }
            SorobanStmt::Comment(_) | SorobanStmt::Break | SorobanStmt::Continue => {}
        }
    }
}

fn collect_expr_recursive<'a>(expr: &'a SorobanExpr, out: &mut Vec<&'a SorobanExpr>) {
    out.push(expr);
    // Recurse into sub-expressions (simplified — covers main compound variants)
    match expr {
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
        | SorobanExpr::Ge(a, b)
        | SorobanExpr::And(a, b)
        | SorobanExpr::Or(a, b) => {
            collect_expr_recursive(a, out);
            collect_expr_recursive(b, out);
        }
        SorobanExpr::Not(e)
        | SorobanExpr::RequireAuth(e)
        | SorobanExpr::PanicWithError(e)
        | SorobanExpr::ErrorFromCode(e)
        | SorobanExpr::FieldAccess { object: e, .. }
        | SorobanExpr::StorageGet { key: e, .. }
        | SorobanExpr::StorageHas { key: e, .. }
        | SorobanExpr::StorageRemove { key: e, .. } => {
            collect_expr_recursive(e, out);
        }
        SorobanExpr::StorageSet { key, value, .. } => {
            collect_expr_recursive(key, out);
            collect_expr_recursive(value, out);
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            collect_expr_recursive(object, out);
            for a in args {
                collect_expr_recursive(a, out);
            }
        }
        SorobanExpr::InvokeContract {
            address,
            function,
            args,
            ..
        }
        | SorobanExpr::TryInvokeContract {
            address,
            function,
            args,
            ..
        } => {
            collect_expr_recursive(address, out);
            collect_expr_recursive(function, out);
            for a in args {
                collect_expr_recursive(a, out);
            }
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields {
                collect_expr_recursive(v, out);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for v in fields {
                collect_expr_recursive(v, out);
            }
        }
        SorobanExpr::TupleConstruct(elems)
        | SorobanExpr::VecConstruct(elems)
        | SorobanExpr::Log(elems) => {
            for e in elems {
                collect_expr_recursive(e, out);
            }
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics {
                collect_expr_recursive(t, out);
            }
            collect_expr_recursive(data, out);
        }
        _ => {} // Leaves and remaining compound types
    }
}

/// Count how many expressions match a predicate across the entire statement tree.
pub fn count_exprs(stmts: &[SorobanStmt], pred: &dyn Fn(&SorobanExpr) -> bool) -> usize {
    let mut count = 0;
    for expr in collect_exprs(stmts) {
        if pred(expr) {
            count += 1;
        }
    }
    count
}

// ---------------------------------------------------------------------------
// Contract-level assertions
// ---------------------------------------------------------------------------

/// Entry point for fluent IR assertions on a decompiled contract.
pub struct ContractAssertions<'a> {
    pub module: &'a ContractModule,
    pub registry: &'a TypeRegistry,
}

impl<'a> ContractAssertions<'a> {
    pub fn new(module: &'a ContractModule, registry: &'a TypeRegistry) -> Self {
        Self { module, registry }
    }

    /// Assert a function exists and return a builder for further assertions.
    /// Panics if the function is not found.
    pub fn assert_fn(&self, name: &str) -> FnAssertions<'a> {
        let func = self
            .module
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| {
                let available: Vec<&str> = self
                    .module
                    .functions
                    .iter()
                    .map(|f| f.name.as_str())
                    .collect();
                panic!(
                    "function '{}' not found in contract module. Available: {:?}",
                    name, available
                );
            });
        FnAssertions {
            func,
            registry: self.registry,
        }
    }

    /// Assert a type definition exists and return a builder for further assertions.
    /// Searches types, error_enums, and events.
    pub fn assert_type(&self, name: &str) -> TypeAssertions<'a> {
        // Search in types, error_enums, and events
        let type_def = self
            .module
            .types
            .iter()
            .chain(self.module.error_enums.iter())
            .chain(self.module.events.iter())
            .find(|t| t.name == name);

        let type_def = type_def.unwrap_or_else(|| {
            let available: Vec<&str> = self
                .module
                .types
                .iter()
                .chain(self.module.error_enums.iter())
                .chain(self.module.events.iter())
                .map(|t| t.name.as_str())
                .collect();
            panic!(
                "type '{}' not found in contract module. Available: {:?}",
                name, available
            );
        });

        TypeAssertions {
            name: name.to_string(),
            kind: &type_def.kind,
            registry: self.registry,
        }
    }

    /// Assert the contract has a specific number of functions.
    pub fn has_function_count(&self, n: usize) -> &Self {
        assert_eq!(
            self.module.functions.len(),
            n,
            "expected {} functions, found {}",
            n,
            self.module.functions.len()
        );
        self
    }

    /// Assert the contract has a specific number of type definitions.
    pub fn has_type_count(&self, n: usize) -> &Self {
        let total =
            self.module.types.len() + self.module.error_enums.len() + self.module.events.len();
        assert_eq!(total, n, "expected {} types, found {}", n, total);
        self
    }

    /// Assert the contract has a constructor function.
    pub fn has_constructor(&self) -> &Self {
        assert!(
            self.module.functions.iter().any(|f| f.is_constructor),
            "no constructor function found"
        );
        self
    }

    /// Assert the contract detects a standard interface.
    pub fn has_standard_interface(&self, name: &str) -> &Self {
        assert!(
            self.module.standard_interfaces.iter().any(|i| i == name),
            "standard interface '{}' not found. Available: {:?}",
            name,
            self.module.standard_interfaces
        );
        self
    }
}

// ---------------------------------------------------------------------------
// Function-level assertions
// ---------------------------------------------------------------------------

/// Fluent assertions on a single contract function.
pub struct FnAssertions<'a> {
    pub func: &'a ContractFn,
    pub registry: &'a TypeRegistry,
}

impl<'a> FnAssertions<'a> {
    /// Assert a parameter exists with the given name and type string.
    pub fn has_param(&self, name: &str, type_str: &str) -> &Self {
        let param = self.func.params.iter().find(|p| p.name == name);
        let param = param.unwrap_or_else(|| {
            let available: Vec<&str> = self.func.params.iter().map(|p| p.name.as_str()).collect();
            panic!(
                "param '{}' not found in function '{}'. Available: {:?}",
                name, self.func.name, available
            );
        });
        let actual = type_to_string(&param.type_def);
        assert_eq!(
            actual, type_str,
            "param '{}' in function '{}': expected type '{}', got '{}'",
            name, self.func.name, type_str, actual
        );
        self
    }

    /// Assert the function has a specific number of parameters (excluding env).
    pub fn has_param_count(&self, n: usize) -> &Self {
        assert_eq!(
            self.func.params.len(),
            n,
            "function '{}': expected {} params, found {}",
            self.func.name,
            n,
            self.func.params.len()
        );
        self
    }

    /// Assert the return type as a string.
    pub fn returns(&self, type_str: &str) -> &Self {
        let actual_str = self
            .func
            .return_type
            .as_ref()
            .map(type_to_string)
            .unwrap_or_else(|| "()".to_string());
        assert_eq!(
            actual_str, type_str,
            "function '{}': expected return type '{}', got '{}'",
            self.func.name, type_str, actual_str
        );
        self
    }

    /// Assert the function returns void (no return type).
    pub fn returns_void(&self) -> &Self {
        assert!(
            self.func.return_type.is_none(),
            "function '{}': expected void return, got {:?}",
            self.func.name,
            self.func.return_type
        );
        self
    }

    /// Assert the function body contains at least one expression matching the predicate.
    pub fn body_contains_expr(&self, pred: impl Fn(&SorobanExpr) -> bool) -> &Self {
        assert!(
            walk_exprs(&self.func.body, &pred),
            "no expression in function '{}' matches the predicate",
            self.func.name,
        );
        self
    }

    /// Assert the function body does NOT contain any expression matching the predicate.
    pub fn body_lacks_expr(&self, pred: impl Fn(&SorobanExpr) -> bool) -> &Self {
        assert!(
            !walk_exprs(&self.func.body, &pred),
            "unexpected expression found in function '{}'",
            self.func.name,
        );
        self
    }

    /// Assert the function body contains at least one statement matching the predicate.
    pub fn body_contains_stmt(&self, pred: impl Fn(&SorobanStmt) -> bool) -> &Self {
        assert!(
            walk_stmts(&self.func.body, &pred),
            "no statement in function '{}' matches the predicate",
            self.func.name,
        );
        self
    }

    /// Assert the function body does NOT contain any statement matching the predicate.
    pub fn body_lacks_stmt(&self, pred: impl Fn(&SorobanStmt) -> bool) -> &Self {
        assert!(
            !walk_stmts(&self.func.body, &pred),
            "unexpected statement found in function '{}'",
            self.func.name,
        );
        self
    }

    /// Count expressions matching the predicate in the function body.
    pub fn count_expr(&self, pred: impl Fn(&SorobanExpr) -> bool) -> usize {
        count_exprs(&self.func.body, &pred)
    }

    /// Assert exactly N expressions match the predicate.
    pub fn has_expr_count(&self, n: usize, pred: impl Fn(&SorobanExpr) -> bool) -> &Self {
        let count = count_exprs(&self.func.body, &pred);
        assert_eq!(
            count, n,
            "function '{}': expected {} matching expressions, found {}",
            self.func.name, n, count
        );
        self
    }

    /// Assert the function body has a specific number of top-level statements.
    pub fn has_stmt_count(&self, n: usize) -> &Self {
        assert_eq!(
            self.func.body.len(),
            n,
            "function '{}': expected {} top-level statements, found {}",
            self.func.name,
            n,
            self.func.body.len()
        );
        self
    }

    /// Assert the function is a constructor.
    pub fn is_constructor(&self) -> &Self {
        assert!(
            self.func.is_constructor,
            "function '{}' is not a constructor",
            self.func.name
        );
        self
    }

    /// Assert the function takes an env parameter.
    pub fn takes_env(&self) -> &Self {
        assert!(
            self.func.takes_env,
            "function '{}' does not take env",
            self.func.name
        );
        self
    }

    /// Get the function body for manual inspection.
    pub fn body(&self) -> &[SorobanStmt] {
        &self.func.body
    }

    /// Get the function's match arms (first Match statement found).
    pub fn first_match_arms(&self) -> Option<(&SorobanExpr, &[MatchArm])> {
        fn find_match(stmts: &[SorobanStmt]) -> Option<(&SorobanExpr, &[MatchArm])> {
            for stmt in stmts {
                match stmt {
                    SorobanStmt::Match { scrutinee, arms } => return Some((scrutinee, arms)),
                    SorobanStmt::If {
                        then_body,
                        else_body,
                        ..
                    } => {
                        if let Some(r) = find_match(then_body) {
                            return Some(r);
                        }
                        if let Some(r) = find_match(else_body) {
                            return Some(r);
                        }
                    }
                    SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                        if let Some(r) = find_match(body) {
                            return Some(r);
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        find_match(&self.func.body)
    }
}

// ---------------------------------------------------------------------------
// Type-level assertions
// ---------------------------------------------------------------------------

/// Fluent assertions on a type definition.
pub struct TypeAssertions<'a> {
    name: String,
    kind: &'a TypeDefKind,
    registry: &'a TypeRegistry,
}

impl<'a> TypeAssertions<'a> {
    /// Assert the type is a struct.
    pub fn is_struct(&self) -> &Self {
        assert!(
            matches!(self.kind, TypeDefKind::Struct | TypeDefKind::TupleStruct),
            "type '{}' is not a struct (is {:?})",
            self.name,
            self.kind
        );
        self
    }

    /// Assert the type is an enum (simple enum with discriminants).
    pub fn is_enum(&self) -> &Self {
        assert!(
            matches!(self.kind, TypeDefKind::Enum | TypeDefKind::ErrorEnum),
            "type '{}' is not an enum (is {:?})",
            self.name,
            self.kind
        );
        self
    }

    /// Assert the type is a union (complex enum with data-carrying variants).
    pub fn is_union(&self) -> &Self {
        assert!(
            matches!(self.kind, TypeDefKind::Union),
            "type '{}' is not a union (is {:?})",
            self.name,
            self.kind
        );
        self
    }

    /// Assert the type is an event.
    pub fn is_event(&self) -> &Self {
        assert!(
            matches!(self.kind, TypeDefKind::Event),
            "type '{}' is not an event (is {:?})",
            self.name,
            self.kind
        );
        self
    }

    /// Assert a variant exists (for enums and unions).
    pub fn has_variant(&self, variant_name: &str) -> &Self {
        // Check in unions
        if let Some(union_spec) = self.registry.get_union(&self.name) {
            let found = union_spec.cases.iter().any(|c| {
                let name = match c {
                    ScSpecUdtUnionCaseV0::VoidV0(v) => v.name.to_utf8_string().ok(),
                    ScSpecUdtUnionCaseV0::TupleV0(t) => t.name.to_utf8_string().ok(),
                };
                name.as_deref() == Some(variant_name)
            });
            assert!(
                found,
                "variant '{}' not found in union '{}'",
                variant_name, self.name
            );
            return self;
        }
        // Check in enums
        if let Some(enum_spec) = self.registry.get_enum(&self.name) {
            let found = enum_spec
                .cases
                .iter()
                .any(|c| c.name.to_utf8_string().ok().as_deref() == Some(variant_name));
            assert!(
                found,
                "variant '{}' not found in enum '{}'",
                variant_name, self.name
            );
            return self;
        }
        // Check in error enums
        if let Some(err_spec) = self.registry.get_error_enum(&self.name) {
            let found = err_spec
                .cases
                .iter()
                .any(|c| c.name.to_utf8_string().ok().as_deref() == Some(variant_name));
            assert!(
                found,
                "variant '{}' not found in error enum '{}'",
                variant_name, self.name
            );
            return self;
        }
        panic!(
            "type '{}' not found in registry for variant check",
            self.name
        );
    }

    /// Assert a variant carries data (TupleV0 in XDR union).
    pub fn variant_has_data(&self, variant_name: &str) -> &Self {
        if let Some(union_spec) = self.registry.get_union(&self.name) {
            let case = union_spec.cases.iter().find(|c| {
                let name = match c {
                    ScSpecUdtUnionCaseV0::VoidV0(v) => v.name.to_utf8_string().ok(),
                    ScSpecUdtUnionCaseV0::TupleV0(t) => t.name.to_utf8_string().ok(),
                };
                name.as_deref() == Some(variant_name)
            });
            let case = case.unwrap_or_else(|| {
                panic!(
                    "variant '{}' not found in union '{}'",
                    variant_name, self.name
                )
            });
            assert!(
                matches!(case, ScSpecUdtUnionCaseV0::TupleV0(_)),
                "variant '{}' in union '{}' does not carry data (is VoidV0)",
                variant_name,
                self.name
            );
            return self;
        }
        panic!(
            "type '{}' is not a union, can't check variant data",
            self.name
        );
    }

    /// Assert a field exists (for structs).
    pub fn has_field(&self, field_name: &str) -> &Self {
        if let Some(struct_spec) = self.registry.get_struct(&self.name) {
            let found = struct_spec
                .fields
                .iter()
                .any(|f| f.name.to_utf8_string().ok().as_deref() == Some(field_name));
            assert!(
                found,
                "field '{}' not found in struct '{}'",
                field_name, self.name
            );
            return self;
        }
        if let Some(event_spec) = self.registry.get_event(&self.name) {
            let found = event_spec
                .params
                .iter()
                .any(|p| p.name.to_utf8_string().ok().as_deref() == Some(field_name));
            assert!(
                found,
                "field '{}' not found in event '{}'",
                field_name, self.name
            );
            return self;
        }
        panic!("type '{}' not found in registry for field check", self.name);
    }
}
