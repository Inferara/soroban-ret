//! Correctness-guard pass — a final safety net that replaces *provably-broken*
//! IR with honest, compiling output rather than emitting plausible-but-wrong
//! Rust. It encodes the project's prime rule: **a wrong recovery is worse than a
//! `todo!()`**.
//!
//! The mainnet corpus exposed that "restoration %" is correctness-blind — a
//! contract can score 100% yet not compile, because deep loop/control-flow
//! losses leave the lifter emitting constructs that *look* like code but are
//! actually broken (a `break` with no enclosing loop, a field access on an
//! `Error` sentinel, …). This pass turns those into output that at least
//! compiles and does not mislead.
//!
//! It runs **last** — after the optimizer fixpoint and `recover_for_loops` — so
//! it sees the final IR shape. Every detector is deliberately conservative: it
//! fires only on shapes a correctly-lifted body can never contain, so it is a
//! strict no-op on the clean fixtures (guarded by the snapshot + compile-back
//! gates).

use std::collections::HashSet;

use super::soroban_ir::{MatchArm, SorobanExpr, SorobanStmt};

/// Guard a single function body. Order is irrelevant — the detectors target
/// disjoint shapes — but expression husking runs first so a later statement
/// walker never re-inspects a subtree we already neutralised.
pub fn guard_broken_constructs(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let stmts = husk_error_sentinel_access(stmts);
    let stmts = drop_breaks_outside_loops(stmts, false);
    declare_undeclared_assignments(stmts)
}

// ---------------------------------------------------------------------------
// Detector 1: `break` / `continue` with no enclosing loop (rustc E0268).
// ---------------------------------------------------------------------------
//
// Structurization occasionally emits a `Break`/`Continue` outside any loop when
// it fails to reconstruct the loop it belonged to. Such a statement cannot
// compile, so there is no correct runtime behaviour to preserve — dropping it
// strictly helps. Loop nesting is tracked through `Loop`/`For` only (matching
// codegen, where only those introduce a `loop {}` / `for {}` scope); `If`,
// `Match` and `Block` propagate the enclosing loop context unchanged.

fn drop_breaks_outside_loops(stmts: Vec<SorobanStmt>, in_loop: bool) -> Vec<SorobanStmt> {
    stmts
        .into_iter()
        .filter_map(|stmt| match stmt {
            SorobanStmt::Break | SorobanStmt::Continue if !in_loop => None,
            SorobanStmt::Loop { body } => Some(SorobanStmt::Loop {
                body: drop_breaks_outside_loops(body, true),
            }),
            SorobanStmt::For {
                var,
                start,
                end,
                step,
                body,
            } => Some(SorobanStmt::For {
                var,
                start,
                end,
                step,
                body: drop_breaks_outside_loops(body, true),
            }),
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => Some(SorobanStmt::If {
                condition,
                then_body: drop_breaks_outside_loops(then_body, in_loop),
                else_body: drop_breaks_outside_loops(else_body, in_loop),
            }),
            SorobanStmt::Match { scrutinee, arms } => Some(SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|a| MatchArm {
                        pattern: a.pattern,
                        body: drop_breaks_outside_loops(a.body, in_loop),
                    })
                    .collect(),
            }),
            SorobanStmt::Block(body) => {
                Some(SorobanStmt::Block(drop_breaks_outside_loops(body, in_loop)))
            }
            other => Some(other),
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Detector 2: field / method access on an `Error` or `panic!` sentinel.
// ---------------------------------------------------------------------------
//
// `soroban_sdk::Error::from_contract_error(8).request_id` (band-protocol
// `relay`) is the lifter mis-attributing a struct field access to an error
// value: `Error` has no user fields, so it is provably garbage (rustc E0609 /
// E0599). The whole access reduces to an honest `todo!("unknown value")`
// (`UnknownVal`) — the value behind it was lost, and the access was never
// valid.

fn husk_error_sentinel_access(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    map_exprs_in_stmts(stmts, &husk_error_access_expr)
}

/// Post-order rewrite of one expression: recurse into children first (so a
/// nested error access is neutralised before its parent is inspected), then
/// collapse a field/method access *on* an error sentinel to `UnknownVal`.
fn husk_error_access_expr(expr: SorobanExpr) -> SorobanExpr {
    match expr {
        SorobanExpr::FieldAccess { object, field } => {
            let object = husk_error_access_expr(*object);
            if is_error_sentinel(&object) {
                SorobanExpr::UnknownVal
            } else {
                SorobanExpr::FieldAccess {
                    object: Box::new(object),
                    field,
                }
            }
        }
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } => {
            let object = husk_error_access_expr(*object);
            if is_error_sentinel(&object) {
                SorobanExpr::UnknownVal
            } else {
                SorobanExpr::MethodCall {
                    object: Box::new(object),
                    method,
                    args: args.into_iter().map(husk_error_access_expr).collect(),
                }
            }
        }
        other => map_subexprs(other, &husk_error_access_expr),
    }
}

/// An expression that denotes a Soroban `Error` value (or a `panic!` husk) —
/// nothing in user code reads a field or calls a method on one.
fn is_error_sentinel(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::ContractError { .. }
            | SorobanExpr::ErrorFromCode(_)
            | SorobanExpr::PanicWithError(_)
            | SorobanExpr::Panic
    )
}

// ---------------------------------------------------------------------------
// Detector 3: assignment to a never-declared variable (rustc E0425).
// ---------------------------------------------------------------------------
//
// Lost loop/branch dataflow leaves the lifter emitting `var_11 = expr;` with no
// preceding `let` (the declaration lived in a region that failed to lift), so
// the variable is undeclared at its use site. Turn the *first* assignment to
// such a variable into its declaration (`let mut var_11 = expr;`) — the value
// the original initialised it with is what we have, and every later assignment
// to the same name then resolves against this binding.
//
// Conservative on two axes so it is a no-op on correctly-lifted bodies: it only
// touches names that are *never* introduced by any `let` in the whole function
// (so loop-carried `let x; … x = …` accumulators are untouched), and only the
// first textual occurrence (later ones stay `Assign`). Cross-scope cases (first
// assignment nested inside a branch, used outside) are left as-is — best effort,
// never wrong.

fn declare_undeclared_assignments(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut declared = HashSet::new();
    collect_let_names(&stmts, &mut declared);
    let mut seen = HashSet::new();
    declare_first_assign(stmts, &declared, &mut seen)
}

/// Collect every name a binding construct introduces — `let`, the `for` loop
/// variable, and match-arm pattern bindings. A name in this set is in scope by
/// some other means, so an `Assign` to it must stay an `Assign` (promoting it
/// would shadow the real binding and change behaviour).
fn collect_let_names(stmts: &[SorobanStmt], out: &mut HashSet<String>) {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Let { name, .. } => {
                out.insert(name.clone());
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_let_names(then_body, out);
                collect_let_names(else_body, out);
            }
            SorobanStmt::Match { arms, .. } => {
                for a in arms {
                    if let super::soroban_ir::MatchPattern::EnumVariant { bindings, .. } =
                        &a.pattern
                    {
                        out.extend(bindings.iter().cloned());
                    }
                    collect_let_names(&a.body, out);
                }
            }
            SorobanStmt::For { var, body, .. } => {
                out.insert(var.clone());
                collect_let_names(body, out);
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => collect_let_names(body, out),
            _ => {}
        }
    }
}

/// Walk in document order converting the first `Assign` to an undeclared name
/// into `Let { mutable: true }`. `seen` is threaded mutably through *sequential*
/// statements in one list (so only the first occurrence is promoted), but each
/// nested scope — `if`/`else` branches, match arms, loop/block bodies — recurses
/// on a **clone**: those are independent execution paths, and a `let` introduced
/// inside one does not declare the name in a sibling branch or the enclosing
/// scope. Sharing `seen` across them would wrongly suppress promotion of the
/// same undeclared assignment in the `else` branch / next arm (it would stay an
/// `Assign`, i.e. an E0425 error in that path).
fn declare_first_assign(
    stmts: Vec<SorobanStmt>,
    declared: &HashSet<String>,
    seen: &mut HashSet<String>,
) -> Vec<SorobanStmt> {
    stmts
        .into_iter()
        .map(|stmt| match stmt {
            SorobanStmt::Assign { target, value }
                if !declared.contains(&target) && !seen.contains(&target) =>
            {
                seen.insert(target.clone());
                SorobanStmt::Let {
                    name: target,
                    mutable: true,
                    value,
                }
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => SorobanStmt::If {
                condition,
                then_body: declare_first_assign(then_body, declared, &mut seen.clone()),
                else_body: declare_first_assign(else_body, declared, &mut seen.clone()),
            },
            SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|a| MatchArm {
                        pattern: a.pattern,
                        body: declare_first_assign(a.body, declared, &mut seen.clone()),
                    })
                    .collect(),
            },
            SorobanStmt::Loop { body } => SorobanStmt::Loop {
                body: declare_first_assign(body, declared, &mut seen.clone()),
            },
            SorobanStmt::For {
                var,
                start,
                end,
                step,
                body,
            } => SorobanStmt::For {
                var,
                start,
                end,
                step,
                body: declare_first_assign(body, declared, &mut seen.clone()),
            },
            SorobanStmt::Block(body) => {
                SorobanStmt::Block(declare_first_assign(body, declared, &mut seen.clone()))
            }
            other => other,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Minimal generic walkers (the IR has no shared visitor; these stay local).
// ---------------------------------------------------------------------------

/// Apply `f` to every expression that appears directly in `stmts`, recursing
/// into nested statement bodies. `f` is responsible for its own sub-expression
/// recursion (it receives whole expressions).
fn map_exprs_in_stmts(
    stmts: Vec<SorobanStmt>,
    f: &dyn Fn(SorobanExpr) -> SorobanExpr,
) -> Vec<SorobanStmt> {
    stmts
        .into_iter()
        .map(|stmt| match stmt {
            SorobanStmt::Expr(e) => SorobanStmt::Expr(f(e)),
            SorobanStmt::Let {
                name,
                mutable,
                value,
            } => SorobanStmt::Let {
                name,
                mutable,
                value: f(value),
            },
            SorobanStmt::Assign { target, value } => SorobanStmt::Assign {
                target,
                value: f(value),
            },
            SorobanStmt::Return(v) => SorobanStmt::Return(v.map(f)),
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => SorobanStmt::If {
                condition: f(condition),
                then_body: map_exprs_in_stmts(then_body, f),
                else_body: map_exprs_in_stmts(else_body, f),
            },
            SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
                scrutinee: f(scrutinee),
                arms: arms
                    .into_iter()
                    .map(|a| MatchArm {
                        pattern: a.pattern,
                        body: map_exprs_in_stmts(a.body, f),
                    })
                    .collect(),
            },
            SorobanStmt::Loop { body } => SorobanStmt::Loop {
                body: map_exprs_in_stmts(body, f),
            },
            SorobanStmt::For {
                var,
                start,
                end,
                step,
                body,
            } => SorobanStmt::For {
                var,
                start: f(start),
                end: f(end),
                step,
                body: map_exprs_in_stmts(body, f),
            },
            SorobanStmt::Block(body) => SorobanStmt::Block(map_exprs_in_stmts(body, f)),
            other @ (SorobanStmt::Comment(_) | SorobanStmt::Break | SorobanStmt::Continue) => other,
        })
        .collect()
}

/// Apply `f` to the *direct* sub-expressions of `expr`, rebuilding it. Used as
/// the recursion fall-through for expression rewriters that only special-case a
/// few node kinds. Leaf nodes are returned unchanged.
fn map_subexprs(expr: SorobanExpr, f: &dyn Fn(SorobanExpr) -> SorobanExpr) -> SorobanExpr {
    use SorobanExpr as E;
    let b = |e: Box<SorobanExpr>, f: &dyn Fn(SorobanExpr) -> SorobanExpr| Box::new(f(*e));
    match expr {
        E::Add(a, c) => E::Add(b(a, f), b(c, f)),
        E::Sub(a, c) => E::Sub(b(a, f), b(c, f)),
        E::Mul(a, c) => E::Mul(b(a, f), b(c, f)),
        E::Div(a, c) => E::Div(b(a, f), b(c, f)),
        E::Rem(a, c) => E::Rem(b(a, f), b(c, f)),
        E::Eq(a, c) => E::Eq(b(a, f), b(c, f)),
        E::Ne(a, c) => E::Ne(b(a, f), b(c, f)),
        E::Lt(a, c) => E::Lt(b(a, f), b(c, f)),
        E::Le(a, c) => E::Le(b(a, f), b(c, f)),
        E::Gt(a, c) => E::Gt(b(a, f), b(c, f)),
        E::Ge(a, c) => E::Ge(b(a, f), b(c, f)),
        E::And(a, c) => E::And(b(a, f), b(c, f)),
        E::Or(a, c) => E::Or(b(a, f), b(c, f)),
        E::Not(a) => E::Not(b(a, f)),
        E::Some(a) => E::Some(b(a, f)),
        E::StorageGet {
            storage_type,
            key,
            unwrap,
        } => E::StorageGet {
            storage_type,
            key: b(key, f),
            unwrap,
        },
        E::StorageSet {
            storage_type,
            key,
            value,
        } => E::StorageSet {
            storage_type,
            key: b(key, f),
            value: b(value, f),
        },
        E::StorageHas { storage_type, key } => E::StorageHas {
            storage_type,
            key: b(key, f),
        },
        E::StorageRemove { storage_type, key } => E::StorageRemove {
            storage_type,
            key: b(key, f),
        },
        E::StorageExtendTtl {
            storage_type,
            key,
            threshold,
            extend_to,
        } => E::StorageExtendTtl {
            storage_type,
            key: b(key, f),
            threshold: b(threshold, f),
            extend_to: b(extend_to, f),
        },
        E::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => E::ExtendInstanceAndCodeTtl {
            threshold: b(threshold, f),
            extend_to: b(extend_to, f),
        },
        E::RequireAuth(a) => E::RequireAuth(b(a, f)),
        E::RequireAuthForArgs { address, args } => E::RequireAuthForArgs {
            address: b(address, f),
            args: b(args, f),
        },
        E::AuthorizeAsCurrContract(a) => E::AuthorizeAsCurrContract(b(a, f)),
        E::PublishEvent {
            event_name,
            topics,
            data,
        } => E::PublishEvent {
            event_name,
            topics: topics.into_iter().map(f).collect(),
            data: b(data, f),
        },
        E::InvokeContract {
            address,
            function,
            args,
            return_type,
        } => E::InvokeContract {
            address: b(address, f),
            function: b(function, f),
            args: args.into_iter().map(f).collect(),
            return_type,
        },
        E::TryInvokeContract {
            address,
            function,
            args,
            return_type,
        } => E::TryInvokeContract {
            address: b(address, f),
            function: b(function, f),
            args: args.into_iter().map(f).collect(),
            return_type,
        },
        E::StructConstruct { type_name, fields } => E::StructConstruct {
            type_name,
            fields: fields.into_iter().map(|(n, e)| (n, f(e))).collect(),
        },
        E::EnumConstruct {
            type_name,
            variant,
            fields,
        } => E::EnumConstruct {
            type_name,
            variant,
            fields: fields.into_iter().map(f).collect(),
        },
        E::TupleConstruct(items) => E::TupleConstruct(items.into_iter().map(f).collect()),
        E::VecConstruct(items) => E::VecConstruct(items.into_iter().map(f).collect()),
        E::MapConstruct(pairs) => {
            E::MapConstruct(pairs.into_iter().map(|(k, v)| (f(k), f(v))).collect())
        }
        E::FieldAccess { object, field } => E::FieldAccess {
            object: b(object, f),
            field,
        },
        E::MethodCall {
            object,
            method,
            args,
        } => E::MethodCall {
            object: b(object, f),
            method,
            args: args.into_iter().map(f).collect(),
        },
        E::ErrorFromCode(a) => E::ErrorFromCode(b(a, f)),
        E::PanicWithError(a) => E::PanicWithError(b(a, f)),
        E::CryptoSha256(a) => E::CryptoSha256(b(a, f)),
        E::CryptoKeccak256(a) => E::CryptoKeccak256(b(a, f)),
        E::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => E::CryptoEd25519Verify {
            public_key: b(public_key, f),
            message: b(message, f),
            signature: b(signature, f),
        },
        E::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => E::CryptoSecp256k1Recover {
            msg_digest: b(msg_digest, f),
            signature: b(signature, f),
            recovery_id: b(recovery_id, f),
        },
        E::PrngReseed(a) => E::PrngReseed(b(a, f)),
        E::PrngBytesNew(a) => E::PrngBytesNew(b(a, f)),
        E::PrngU64InRange { low, high } => E::PrngU64InRange {
            low: b(low, f),
            high: b(high, f),
        },
        E::PrngVecShuffle(a) => E::PrngVecShuffle(b(a, f)),
        E::StrkeyToAddress(a) => E::StrkeyToAddress(b(a, f)),
        E::AddressToStrkey(a) => E::AddressToStrkey(b(a, f)),
        E::Log(items) => E::Log(items.into_iter().map(f).collect()),
        E::RawHostCall {
            module,
            function,
            args,
        } => E::RawHostCall {
            module,
            function,
            args: args.into_iter().map(f).collect(),
        },
        E::SretResult(a) => E::SretResult(b(a, f)),
        E::ValTag(a) => E::ValTag(b(a, f)),
        E::ValConvert { value, target_type } => E::ValConvert {
            value: b(value, f),
            target_type,
        },
        E::CastAs { value, target_type } => E::CastAs {
            value: b(value, f),
            target_type,
        },
        E::VecTryIterFold { vec, init } => E::VecTryIterFold {
            vec: b(vec, f),
            init: b(init, f),
        },
        // Leaves (literals, vars, ledger/contract constants, tag names, …) and
        // already-terminal nodes have no sub-expressions to rewrite.
        leaf => leaf,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::soroban_ir::StorageType;

    fn remove(key: &str) -> SorobanStmt {
        SorobanStmt::Expr(SorobanExpr::StorageRemove {
            storage_type: StorageType::Persistent,
            key: Box::new(SorobanExpr::Param(key.into())),
        })
    }

    #[test]
    fn drops_break_outside_loop() {
        let out = guard_broken_constructs(vec![remove("a"), SorobanStmt::Break]);
        assert_eq!(out.len(), 1, "stray break should be dropped: {out:?}");
        assert!(matches!(out[0], SorobanStmt::Expr(_)));
    }

    #[test]
    fn keeps_break_inside_loop() {
        let out = guard_broken_constructs(vec![SorobanStmt::Loop {
            body: vec![remove("a"), SorobanStmt::Break],
        }]);
        let SorobanStmt::Loop { body } = &out[0] else {
            panic!("expected loop, got {out:?}");
        };
        assert!(
            matches!(body.last(), Some(SorobanStmt::Break)),
            "in-loop break must be preserved: {body:?}"
        );
    }

    #[test]
    fn drops_break_outside_loop_but_keeps_nested_in_loop() {
        // A break inside `if` inside a loop is in-loop; a break inside `if` at
        // top level is not.
        let in_loop = SorobanStmt::Loop {
            body: vec![SorobanStmt::If {
                condition: SorobanExpr::BoolLiteral(true),
                then_body: vec![SorobanStmt::Break],
                else_body: vec![],
            }],
        };
        let top_if = SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(true),
            then_body: vec![SorobanStmt::Continue],
            else_body: vec![],
        };
        let out = guard_broken_constructs(vec![in_loop, top_if]);
        let SorobanStmt::Loop { body } = &out[0] else {
            panic!("expected loop");
        };
        let SorobanStmt::If { then_body, .. } = &body[0] else {
            panic!("expected if-in-loop");
        };
        assert!(matches!(then_body.as_slice(), [SorobanStmt::Break]));
        let SorobanStmt::If { then_body, .. } = &out[1] else {
            panic!("expected top-level if");
        };
        assert!(then_body.is_empty(), "top-level continue should be dropped");
    }

    #[test]
    fn husks_field_access_on_error() {
        // `from_contract_error(8).request_id < resolve_time` → `todo!() < ...`
        let cond = SorobanExpr::Lt(
            Box::new(SorobanExpr::FieldAccess {
                object: Box::new(SorobanExpr::ContractError {
                    error_code: 8,
                    error_type: None,
                    variant_name: None,
                }),
                field: "request_id".into(),
            }),
            Box::new(SorobanExpr::Param("resolve_time".into())),
        );
        let out = guard_broken_constructs(vec![SorobanStmt::If {
            condition: cond,
            then_body: vec![],
            else_body: vec![],
        }]);
        let SorobanStmt::If { condition, .. } = &out[0] else {
            panic!("expected if");
        };
        let SorobanExpr::Lt(lhs, _) = condition else {
            panic!("expected Lt");
        };
        assert!(
            matches!(**lhs, SorobanExpr::UnknownVal),
            "field access on Error should husk to UnknownVal: {lhs:?}"
        );
    }

    #[test]
    fn leaves_normal_field_access() {
        let access = SorobanExpr::FieldAccess {
            object: Box::new(SorobanExpr::Param("cfg".into())),
            field: "threshold".into(),
        };
        let out = guard_broken_constructs(vec![SorobanStmt::Expr(access.clone())]);
        assert!(matches!(
            &out[0],
            SorobanStmt::Expr(SorobanExpr::FieldAccess { .. })
        ));
    }

    #[test]
    fn promotes_first_undeclared_assignment() {
        // var_11 = 1; var_11 = 2;  →  let mut var_11 = 1; var_11 = 2;
        let out = guard_broken_constructs(vec![
            SorobanStmt::Assign {
                target: "var_11".into(),
                value: SorobanExpr::I64Literal(1),
            },
            SorobanStmt::Assign {
                target: "var_11".into(),
                value: SorobanExpr::I64Literal(2),
            },
        ]);
        assert!(
            matches!(&out[0], SorobanStmt::Let { name, mutable: true, .. } if name == "var_11"),
            "first assignment should become a `let mut`: {out:?}"
        );
        assert!(
            matches!(&out[1], SorobanStmt::Assign { target, .. } if target == "var_11"),
            "later assignment should stay an assignment: {out:?}"
        );
    }

    #[test]
    fn promotes_undeclared_assignment_in_both_branches() {
        // if c { var_9 = 1 } else { var_9 = 2 }  →  each branch declares its own
        // `let mut var_9` (independent paths; the `seen` set must not carry the
        // then-branch promotion into the else branch).
        let assign = |v: i64| SorobanStmt::Assign {
            target: "var_9".into(),
            value: SorobanExpr::I64Literal(v),
        };
        let out = guard_broken_constructs(vec![SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(true),
            then_body: vec![assign(1)],
            else_body: vec![assign(2)],
        }]);
        let SorobanStmt::If {
            then_body,
            else_body,
            ..
        } = &out[0]
        else {
            panic!("expected if");
        };
        assert!(
            matches!(&then_body[0], SorobanStmt::Let { name, .. } if name == "var_9"),
            "then branch should promote: {then_body:?}"
        );
        assert!(
            matches!(&else_body[0], SorobanStmt::Let { name, .. } if name == "var_9"),
            "else branch should promote independently: {else_body:?}"
        );
    }

    #[test]
    fn leaves_assignment_to_declared_var() {
        // let mut x = 0; x = 1;  →  unchanged (x is declared)
        let out = guard_broken_constructs(vec![
            SorobanStmt::Let {
                name: "x".into(),
                mutable: true,
                value: SorobanExpr::I64Literal(0),
            },
            SorobanStmt::Assign {
                target: "x".into(),
                value: SorobanExpr::I64Literal(1),
            },
        ]);
        assert!(matches!(&out[1], SorobanStmt::Assign { target, .. } if target == "x"));
    }

    #[test]
    fn leaves_assignment_to_for_loop_var() {
        // for i in 0..n { i = expr; }  →  the inner `i = …` must stay an Assign
        // (promoting it would shadow the loop variable).
        let out = guard_broken_constructs(vec![SorobanStmt::For {
            var: "i".into(),
            start: SorobanExpr::I64Literal(0),
            end: SorobanExpr::Param("n".into()),
            step: 1,
            body: vec![SorobanStmt::Assign {
                target: "i".into(),
                value: SorobanExpr::I64Literal(5),
            }],
        }]);
        let SorobanStmt::For { body, .. } = &out[0] else {
            panic!("expected for");
        };
        assert!(
            matches!(&body[0], SorobanStmt::Assign { .. }),
            "assignment to the loop variable must not be promoted: {body:?}"
        );
    }

    #[test]
    fn husks_method_call_on_panic_with_error() {
        let expr = SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::Panic),
            method: "foo".into(),
            args: vec![],
        };
        let out = guard_broken_constructs(vec![SorobanStmt::Expr(expr)]);
        assert!(matches!(
            &out[0],
            SorobanStmt::Expr(SorobanExpr::UnknownVal)
        ));
    }
}
