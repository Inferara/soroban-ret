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

use std::collections::{HashMap, HashSet};

use stellar_xdr::curr::ScSpecTypeDef;

use super::high_level_ir::FnParam;
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
// Pass: annotate un-inferable storage gets with an explicit value type.
// ---------------------------------------------------------------------------
//
// `env.storage().<area>().get(&key)` is generic over its value type
// `V: TryFromVal<Env, Val>`. When the result flows into a typed context (a
// typed `let`, a typed return, a typed argument) rustc infers `V`. But the
// corpus leaves many gets whose result is *discarded* (`get(&k).unwrap();`) or
// bound to an *unused* local — there `V` is unconstrained and the code does not
// compile (E0282/E0284, with the `TryFromVal` chain surfacing as E0277).
//
// We supply the type by wrapping the get in `CastAs { .., T }`, which codegen
// lowers to a `get::<_, T>(&key)` turbofish (see `generate_expr`'s
// `CastAs { StorageGet, T }` arm). This is a pure type annotation — it changes
// no runtime value, only makes the (failed) inference explicit. Two cases:
//
//   1. **`Address`** when the get's value is `require_auth()`-ed
//      (`RequireAuth(StorageGet)` — the admin-gate idiom
//      `get(&admin).unwrap().require_auth()`). `require_auth` is an `Address`
//      method, so the value is *provably* an `Address` — `Val` would be wrong
//      (no such method). This is consumer-driven type recovery, not a guess.
//   2. **`Val`** for a get whose result is otherwise unused: the untyped host
//      value is exactly what the lifter could not narrow. Applied to a
//      *discarded* `Expr(StorageGet)` (one not in tail/return position — its
//      value is thrown away) or a `Let { value: StorageGet }` whose binding is
//      *never referenced*. A value-returning tail get, a typed `let`, or any
//      used binding is left to inference (the 38 compile-back fixtures rely on
//      it), so the pass is a no-op on correctly-lifted bodies.

/// Annotate un-inferable storage gets with a concrete value type.
/// `body_supplies_tail` is whether the function's body itself supplies the
/// inferable return value: true only when the function returns a value AND
/// codegen does **not** synthesize the tail (`Ok(())` / `todo!()`). When false,
/// no `Expr(StorageGet)` is ever the return — including a trailing get in a
/// `Result<(), E>` function whose `Ok(())` is codegen-synthesized — so all are
/// discarded and get the `Val` turbofish (see
/// [`crate::codegen::module::codegen_synthesizes_tail`]).
pub fn annotate_uninferable_gets(
    stmts: Vec<SorobanStmt>,
    body_supplies_tail: bool,
) -> Vec<SorobanStmt> {
    // Address-from-require_auth first, so the Val pass below skips a get already
    // wrapped as an auth target (it is no longer a bare `StorageGet`).
    let stmts = annotate_auth_target_gets(stmts);
    let used = collect_referenced_names(&stmts);
    annotate_gets(stmts, body_supplies_tail, &used)
}

/// Case 1: `RequireAuth(StorageGet)` / `RequireAuthForArgs { address:
/// StorageGet, .. }` → annotate the get `Address`. The value has `require_auth`
/// called on it, so it can only be an `Address`.
fn annotate_auth_target_gets(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    map_exprs_in_stmts(stmts, &auth_target_expr)
}

fn auth_target_expr(expr: SorobanExpr) -> SorobanExpr {
    match expr {
        SorobanExpr::RequireAuth(inner) if matches!(*inner, SorobanExpr::StorageGet { .. }) => {
            SorobanExpr::RequireAuth(Box::new(annotate_with(*inner, "Address")))
        }
        SorobanExpr::RequireAuthForArgs { address, args }
            if matches!(*address, SorobanExpr::StorageGet { .. }) =>
        {
            SorobanExpr::RequireAuthForArgs {
                address: Box::new(annotate_with(*address, "Address")),
                args: Box::new(auth_target_expr(*args)),
            }
        }
        other => map_subexprs(other, &auth_target_expr),
    }
}

/// Case 2: annotate discarded / unused bare gets with `Val`. `tail_is_return` is
/// true when the *last* statement of this list is in tail (return) position —
/// only that statement, in a value-returning function, can be the inferable
/// return value; every earlier `Expr(StorageGet)` is discarded. Mirrors
/// codegen's tail handling: `if`/`match`/`block` propagate tail position into
/// their last statement; loop bodies never do.
fn annotate_gets(
    stmts: Vec<SorobanStmt>,
    tail_is_return: bool,
    used: &HashSet<String>,
) -> Vec<SorobanStmt> {
    let last = stmts.len().saturating_sub(1);
    stmts
        .into_iter()
        .enumerate()
        .map(|(i, stmt)| {
            let this_is_tail = tail_is_return && i == last;
            match stmt {
                // Discarded get (not the inferable tail return).
                SorobanStmt::Expr(e)
                    if !this_is_tail && matches!(e, SorobanExpr::StorageGet { .. }) =>
                {
                    SorobanStmt::Expr(annotate_with(e, "Val"))
                }
                // Get bound to a never-referenced local — its `V` is unconstrained.
                SorobanStmt::Let {
                    name,
                    mutable,
                    value,
                } if matches!(value, SorobanExpr::StorageGet { .. }) && !used.contains(&name) => {
                    SorobanStmt::Let {
                        name,
                        mutable,
                        value: annotate_with(value, "Val"),
                    }
                }
                SorobanStmt::If {
                    condition,
                    then_body,
                    else_body,
                } => SorobanStmt::If {
                    condition,
                    then_body: annotate_gets(then_body, this_is_tail, used),
                    else_body: annotate_gets(else_body, this_is_tail, used),
                },
                SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
                    scrutinee,
                    arms: arms
                        .into_iter()
                        .map(|a| MatchArm {
                            pattern: a.pattern,
                            body: annotate_gets(a.body, this_is_tail, used),
                        })
                        .collect(),
                },
                SorobanStmt::Loop { body } => SorobanStmt::Loop {
                    body: annotate_gets(body, false, used),
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
                    body: annotate_gets(body, false, used),
                },
                SorobanStmt::Block(body) => {
                    SorobanStmt::Block(annotate_gets(body, this_is_tail, used))
                }
                other => other,
            }
        })
        .collect()
}

/// Wrap a storage get in `CastAs { .., ty }` — codegen lowers this to the
/// `get::<_, ty>(&key)` turbofish.
fn annotate_with(get: SorobanExpr, ty: &str) -> SorobanExpr {
    SorobanExpr::CastAs {
        value: Box::new(get),
        target_type: ty.to_string(),
    }
}

// ---------------------------------------------------------------------------
// Un-inferable empty collections (`Map::new`/`Vec::new`) → `Map::<_, Val>` etc.
// ---------------------------------------------------------------------------

/// Value-type-agnostic collection methods: calling one tells rustc nothing about
/// the collection's *value* type, so an empty `Map::new`/`Vec::new` reached only
/// through them leaves `V` unconstrained (E0283). `keys`/`contains_key` are
/// Map-only and also pin the *key* type (from the arg / `Vec<K>` result), so the
/// `_` key placeholder still resolves. `get`/`set`/`values`/`iter`/`push_*` all
/// touch the value type and are deliberately excluded — a collection reached
/// through any of them has a constrained `V` and is left to inference.
fn is_value_agnostic_method(method: &str) -> bool {
    matches!(method, "keys" | "contains_key" | "len" | "is_empty")
}

/// An empty `Map::new(&env)` / `Vec::new(&env)` (a [`SorobanExpr::CollectionNew`]
/// of `"Map"`/`"Vec"`) — the only shape whose element types are unconstrained by
/// construction. A `map![..]`/`vec![..]` literal carries its elements' types.
fn is_empty_map_or_vec(expr: &SorobanExpr) -> bool {
    matches!(expr, SorobanExpr::CollectionNew(c) if c == "Map" || c == "Vec")
}

/// The variable name an expression denotes, if it is a bare variable reference.
/// `Local(i)` renders as `var_i` (see codegen), matching a `let` of that name.
fn var_name_of(expr: &SorobanExpr) -> Option<String> {
    match expr {
        SorobanExpr::Param(n) | SorobanExpr::NamedLocal(n) => Some(n.clone()),
        SorobanExpr::Local(i) => Some(format!("var_{i}")),
        _ => None,
    }
}

/// Annotate empty `Map::new`/`Vec::new` collections whose value type the lifter
/// lost and which no usage constrains, so rustc cannot infer `V` (E0283). Pins
/// only the value param to `Val` (`Map::<_, Val>` / `Vec::<Val>`), leaving the
/// key to inference — faithful, since every concrete `Map<K, V>`/`Vec<T>` is a
/// `Map<_, Val>`/`Vec<Val>` at the host level. Fires only when the collection is
/// reached *exclusively* through value-type-agnostic methods
/// ([`is_value_agnostic_method`]); a collection fed a typed value (`set`,
/// `push_back`) or whose `get` result is consumed typed has a constrained `V`
/// and is left untouched, so this can never over-constrain a typed collection
/// (worst case it is a no-op).
///
/// `referenced` / `value_pinned` are **scope-flat** — names accumulate into one
/// function-wide set, not per lexical scope. A same-name binding shadowed across
/// scopes (an outer pinned `m`, an inner agnostic `m`) would therefore leave the
/// inner `let` un-annotated. That direction is safe: it is an *under*-annotation
/// (a fixable `E0283` left honest), never a wrong `Val` pin on a typed
/// collection. The lifter's unique `var_N` local numbering makes such a collision
/// effectively impossible, so this stays a flat scan (matching the shipped
/// `annotate_uninferable_gets` machinery).
pub fn annotate_uninferable_collections(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let referenced = collect_referenced_names(&stmts);
    let mut value_pinned = HashSet::new();
    collect_value_pinning_names(&stmts, &mut value_pinned);
    // 1) Inline receivers — `Map::new(&env).keys()`, `Map::new(&env).contains_key(k)`.
    let stmts = map_exprs_in_stmts(stmts, &annotate_inline_collection);
    // 2) Let-bound collections used only value-agnostically:
    //    `let m = Map::new(&env); … m.contains_key(k)`.
    annotate_let_collections(stmts, &referenced, &value_pinned)
}

/// Wrap the receiver of `Map::new(&env).<agnostic>()` (and `Vec`) in
/// `CastAs { .., "Val" }` so codegen emits the `Map::<_, Val>::new` turbofish.
fn annotate_inline_collection(expr: SorobanExpr) -> SorobanExpr {
    match expr {
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } if is_value_agnostic_method(&method) && is_empty_map_or_vec(&object) => {
            SorobanExpr::MethodCall {
                object: Box::new(annotate_with(*object, "Val")),
                method,
                args: args.into_iter().map(annotate_inline_collection).collect(),
            }
        }
        other => map_subexprs(other, &annotate_inline_collection),
    }
}

/// Annotate `let m = Map::new(&env)` whose binding is referenced but never in a
/// value-pinning position (every use is a value-agnostic method).
fn annotate_let_collections(
    stmts: Vec<SorobanStmt>,
    referenced: &HashSet<String>,
    value_pinned: &HashSet<String>,
) -> Vec<SorobanStmt> {
    stmts
        .into_iter()
        .map(|stmt| match stmt {
            SorobanStmt::Let {
                name,
                mutable,
                value,
            } if is_empty_map_or_vec(&value)
                && referenced.contains(&name)
                && !value_pinned.contains(&name) =>
            {
                SorobanStmt::Let {
                    name,
                    mutable,
                    value: annotate_with(value, "Val"),
                }
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => SorobanStmt::If {
                condition,
                then_body: annotate_let_collections(then_body, referenced, value_pinned),
                else_body: annotate_let_collections(else_body, referenced, value_pinned),
            },
            SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|a| MatchArm {
                        pattern: a.pattern,
                        body: annotate_let_collections(a.body, referenced, value_pinned),
                    })
                    .collect(),
            },
            SorobanStmt::Loop { body } => SorobanStmt::Loop {
                body: annotate_let_collections(body, referenced, value_pinned),
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
                body: annotate_let_collections(body, referenced, value_pinned),
            },
            SorobanStmt::Block(body) => {
                SorobanStmt::Block(annotate_let_collections(body, referenced, value_pinned))
            }
            other => other,
        })
        .collect()
}

/// Collect names whose *value* type a use constrains: every occurrence of a
/// variable except as the receiver of a value-agnostic method
/// ([`is_value_agnostic_method`]). Mirrors [`visit_stmt_names`]'s structure.
fn collect_value_pinning_names(stmts: &[SorobanStmt], out: &mut HashSet<String>) {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Expr(e)
            | SorobanStmt::Let { value: e, .. }
            | SorobanStmt::Assign { value: e, .. }
            | SorobanStmt::Return(Some(e)) => visit_expr_pinning(e, out),
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                visit_expr_pinning(condition, out);
                collect_value_pinning_names(then_body, out);
                collect_value_pinning_names(else_body, out);
            }
            SorobanStmt::Match { scrutinee, arms } => {
                visit_expr_pinning(scrutinee, out);
                for a in arms {
                    collect_value_pinning_names(&a.body, out);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                collect_value_pinning_names(body, out)
            }
            SorobanStmt::For {
                start, end, body, ..
            } => {
                visit_expr_pinning(start, out);
                visit_expr_pinning(end, out);
                collect_value_pinning_names(body, out);
            }
            SorobanStmt::Return(None)
            | SorobanStmt::Comment(_)
            | SorobanStmt::Break
            | SorobanStmt::Continue => {}
        }
    }
}

fn visit_expr_pinning(expr: &SorobanExpr, out: &mut HashSet<String>) {
    // A value-agnostic method call on a bare variable does not pin that
    // variable's value type — skip the receiver, but its args are normal
    // pinning positions.
    if let SorobanExpr::MethodCall {
        object,
        method,
        args,
    } = expr
        && is_value_agnostic_method(method)
        && var_name_of(object).is_some()
    {
        for a in args {
            visit_expr_pinning(a, out);
        }
        return;
    }
    if let Some(n) = var_name_of(expr) {
        out.insert(n);
    }
    for_each_subexpr(expr, &mut |child| visit_expr_pinning(child, out));
}

/// Every variable name referenced anywhere in the body. `Local(i)` renders as
/// `var_i` (see codegen), so it is normalised to that form to match a `let`
/// binding of the same name. A direct read-only walk over the borrowed body —
/// no allocation beyond the result set.
fn collect_referenced_names(stmts: &[SorobanStmt]) -> HashSet<String> {
    let mut names = HashSet::new();
    visit_stmt_names(stmts, &mut names);
    names
}

fn visit_stmt_names(stmts: &[SorobanStmt], out: &mut HashSet<String>) {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Expr(e)
            | SorobanStmt::Let { value: e, .. }
            | SorobanStmt::Assign { value: e, .. }
            | SorobanStmt::Return(Some(e)) => visit_expr_names(e, out),
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                visit_expr_names(condition, out);
                visit_stmt_names(then_body, out);
                visit_stmt_names(else_body, out);
            }
            SorobanStmt::Match { scrutinee, arms } => {
                visit_expr_names(scrutinee, out);
                for a in arms {
                    visit_stmt_names(&a.body, out);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => visit_stmt_names(body, out),
            SorobanStmt::For {
                start, end, body, ..
            } => {
                visit_expr_names(start, out);
                visit_expr_names(end, out);
                visit_stmt_names(body, out);
            }
            SorobanStmt::Return(None)
            | SorobanStmt::Comment(_)
            | SorobanStmt::Break
            | SorobanStmt::Continue => {}
        }
    }
}

fn visit_expr_names(expr: &SorobanExpr, out: &mut HashSet<String>) {
    match expr {
        SorobanExpr::Param(n) | SorobanExpr::NamedLocal(n) => {
            out.insert(n.clone());
        }
        SorobanExpr::Local(i) => {
            out.insert(format!("var_{i}"));
        }
        _ => {}
    }
    for_each_subexpr(expr, &mut |child| visit_expr_names(child, out));
}

/// Borrowed read-only twin of [`map_subexprs`]: invoke `f` on each *direct*
/// sub-expression of `expr`. Kept structurally identical to `map_subexprs` —
/// update both together when a variant gains a sub-expression.
fn for_each_subexpr(expr: &SorobanExpr, f: &mut dyn FnMut(&SorobanExpr)) {
    use SorobanExpr as E;
    match expr {
        E::Add(a, b)
        | E::Sub(a, b)
        | E::Mul(a, b)
        | E::Div(a, b)
        | E::Rem(a, b)
        | E::Eq(a, b)
        | E::Ne(a, b)
        | E::Lt(a, b)
        | E::Le(a, b)
        | E::Gt(a, b)
        | E::Ge(a, b)
        | E::And(a, b)
        | E::Or(a, b) => {
            f(a);
            f(b);
        }
        E::Not(a) | E::Some(a) => f(a),
        E::StorageGet { key, .. } | E::StorageHas { key, .. } | E::StorageRemove { key, .. } => {
            f(key)
        }
        E::StorageSet { key, value, .. } => {
            f(key);
            f(value);
        }
        E::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            f(key);
            f(threshold);
            f(extend_to);
        }
        E::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            f(threshold);
            f(extend_to);
        }
        E::RequireAuth(a) | E::AuthorizeAsCurrContract(a) => f(a),
        E::RequireAuthForArgs { address, args } => {
            f(address);
            f(args);
        }
        E::PublishEvent { topics, data, .. } => {
            topics.iter().for_each(&mut *f);
            f(data);
        }
        E::InvokeContract {
            address,
            function,
            args,
            ..
        }
        | E::TryInvokeContract {
            address,
            function,
            args,
            ..
        } => {
            f(address);
            f(function);
            args.iter().for_each(&mut *f);
        }
        E::StructConstruct { fields, .. } => fields.iter().for_each(|(_, e)| f(e)),
        E::EnumConstruct { fields, .. } => fields.iter().for_each(&mut *f),
        E::TupleConstruct(items) | E::VecConstruct(items) | E::Log(items) => {
            items.iter().for_each(&mut *f)
        }
        E::MapConstruct(pairs) => pairs.iter().for_each(|(k, v)| {
            f(k);
            f(v);
        }),
        E::FieldAccess { object, .. } => f(object),
        E::MethodCall { object, args, .. } => {
            f(object);
            args.iter().for_each(&mut *f);
        }
        E::ErrorFromCode(a)
        | E::PanicWithError(a)
        | E::CryptoSha256(a)
        | E::CryptoKeccak256(a)
        | E::PrngReseed(a)
        | E::PrngBytesNew(a)
        | E::PrngVecShuffle(a)
        | E::StrkeyToAddress(a)
        | E::AddressToStrkey(a)
        | E::SretResult(a)
        | E::ValTag(a)
        | E::ValConvert { value: a, .. }
        | E::CastAs { value: a, .. } => f(a),
        E::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            f(public_key);
            f(message);
            f(signature);
        }
        E::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            f(msg_digest);
            f(signature);
            f(recovery_id);
        }
        E::PrngU64InRange { low, high } => {
            f(low);
            f(high);
        }
        E::RawHostCall { args, .. } => args.iter().for_each(&mut *f),
        E::VecTryIterFold { vec, init } => {
            f(vec);
            f(init);
        }
        // Leaves (literals, vars, ledger/contract constants, tag names, …).
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Clone non-Copy params reused by-value across enum (DataKey) constructions.
// ---------------------------------------------------------------------------

/// Whether a param type is a non-Copy Soroban host handle — moving it by value
/// twice is a use-after-move (E0382), and a `.clone()` is a faithful refcount
/// bump. Copy scalars/`Symbol`/`Val` are excluded (cloning them is redundant
/// churn and they never trigger E0382).
fn is_non_copy_param_type(t: &ScSpecTypeDef) -> bool {
    matches!(
        t,
        ScSpecTypeDef::Address
            | ScSpecTypeDef::Bytes
            | ScSpecTypeDef::BytesN(_)
            | ScSpecTypeDef::String
            | ScSpecTypeDef::Vec(_)
            | ScSpecTypeDef::Map(_)
            | ScSpecTypeDef::Udt(_)
    )
}

/// Insert `.clone()` on a non-Copy param consumed by value in **multiple**
/// `EnumConstruct` payloads — the `DataKey::Variant(addr)` idiom where the same
/// `addr` keys several storage ops (`has`/`get`/`extend_ttl`), each move-ing it
/// (E0382: "use of moved value"). A Soroban host object is a reference-counted
/// handle, so `addr.clone()` is the same value — faithful, behaviour-preserving.
///
/// Fires only when a non-Copy param appears in **≥2** enum-construct fields, so
/// it never touches a single-use or Copy param (a correctly-lifted body cannot
/// contain an un-cloned double-move, so this is a no-op on compiling output).
pub fn clone_reused_move_params(stmts: Vec<SorobanStmt>, params: &[FnParam]) -> Vec<SorobanStmt> {
    let eligible: HashSet<String> = params
        .iter()
        .filter(|p| is_non_copy_param_type(&p.type_def))
        .map(|p| p.name.clone())
        .collect();
    if eligible.is_empty() {
        return stmts;
    }
    let mut counts: HashMap<String, u32> = HashMap::new();
    for_each_expr_in_stmts(&stmts, &mut |e| {
        count_enum_field_params(e, &eligible, &mut counts)
    });
    let to_clone: HashSet<String> = eligible
        .into_iter()
        .filter(|n| counts.get(n).copied().unwrap_or(0) >= 2)
        .collect();
    if to_clone.is_empty() {
        return stmts;
    }
    map_exprs_in_stmts(stmts, &|e| clone_enum_field_params(e, &to_clone))
}

/// Count bare-variable occurrences of `eligible` names in `EnumConstruct` field
/// positions (the by-value move sites), recursing through all sub-expressions.
fn count_enum_field_params(
    expr: &SorobanExpr,
    eligible: &HashSet<String>,
    counts: &mut HashMap<String, u32>,
) {
    if let SorobanExpr::EnumConstruct { fields, .. } = expr {
        for field in fields {
            match var_name_of(field) {
                Some(n) if eligible.contains(&n) => *counts.entry(n).or_insert(0) += 1,
                _ => count_enum_field_params(field, eligible, counts),
            }
        }
        return;
    }
    for_each_subexpr(expr, &mut |c| count_enum_field_params(c, eligible, counts));
}

/// Wrap every bare `to_clone` variable that appears as an `EnumConstruct` field
/// in `.clone()`. Cloning every occurrence (including the last) is harmless — a
/// redundant handle clone still yields the same value and compiles — and avoids
/// threading evaluation-order state through the rewrite.
fn clone_enum_field_params(expr: SorobanExpr, to_clone: &HashSet<String>) -> SorobanExpr {
    match expr {
        SorobanExpr::EnumConstruct {
            type_name,
            variant,
            fields,
        } => SorobanExpr::EnumConstruct {
            type_name,
            variant,
            fields: fields
                .into_iter()
                .map(|field| match var_name_of(&field) {
                    Some(n) if to_clone.contains(&n) => SorobanExpr::MethodCall {
                        object: Box::new(field),
                        method: "clone".to_string(),
                        args: vec![],
                    },
                    _ => clone_enum_field_params(field, to_clone),
                })
                .collect(),
        },
        other => map_subexprs(other, &|e| clone_enum_field_params(e, to_clone)),
    }
}

/// Apply `f` to every expression appearing directly in `stmts`, recursing into
/// nested statement bodies — the borrowed read-only counterpart of
/// [`map_exprs_in_stmts`].
fn for_each_expr_in_stmts(stmts: &[SorobanStmt], f: &mut dyn FnMut(&SorobanExpr)) {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Expr(e)
            | SorobanStmt::Let { value: e, .. }
            | SorobanStmt::Assign { value: e, .. }
            | SorobanStmt::Return(Some(e)) => f(e),
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                f(condition);
                for_each_expr_in_stmts(then_body, f);
                for_each_expr_in_stmts(else_body, f);
            }
            SorobanStmt::Match { scrutinee, arms } => {
                f(scrutinee);
                for a in arms {
                    for_each_expr_in_stmts(&a.body, f);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                for_each_expr_in_stmts(body, f)
            }
            SorobanStmt::For {
                start, end, body, ..
            } => {
                f(start);
                f(end);
                for_each_expr_in_stmts(body, f);
            }
            SorobanStmt::Return(None)
            | SorobanStmt::Comment(_)
            | SorobanStmt::Break
            | SorobanStmt::Continue => {}
        }
    }
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
            on_missing,
        } => E::StorageGet {
            storage_type,
            key: b(key, f),
            unwrap,
            on_missing,
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

// ---------------------------------------------------------------------------
// Lever 2: a fabricated literal in a `Result<T, E>` success value whose type
// contradicts a scalar `T` (rustc E0308).
// ---------------------------------------------------------------------------
//
// When the lifter loses a function's success value it sometimes fabricates a
// stand-in literal — e.g. unknown-oracle's `get_gas_cost_in_native_token`
// returns `Ok(false)` for a `-> Result<u128, E>`. A literal whose scalar class
// can never unify with the declared ok-type is a *guaranteed* compile error, so
// it cannot be the real value: replace it with an honest `todo!()` (`UnknownVal`,
// emitted bare and coercing to the return type). The class comparison collapses
// every integer width to "numeric" because unsuffixed integer literals coerce —
// so a genuinely-recovered constant return such as `Ok(0)` in `-> Result<i128, E>`
// is **never** touched.

/// Husk a type-mismatched literal in the success-value position(s) of a non-unit
/// scalar `Result<T, E>` function. No-op for non-Result / non-scalar / unit
/// ok-types and for any literal whose class unifies with `T`.
pub fn husk_type_mismatched_ok_literal(
    mut stmts: Vec<SorobanStmt>,
    return_type: Option<&ScSpecTypeDef>,
) -> Vec<SorobanStmt> {
    let Some(ScSpecTypeDef::Result(r)) = return_type else {
        return stmts;
    };
    let Some(ok_class) = scalar_ok_class(&r.ok_type) else {
        return stmts;
    };
    // `return Ok(<lit>)` at any depth.
    husk_mismatched_returns(&mut stmts, ok_class);
    // The function-level tail `Ok(<lit>)` is an `Expr(<lit>)` (the `Ok` wrap is
    // synthesized at codegen).
    if let Some(SorobanStmt::Expr(e)) = stmts.last_mut()
        && literal_mismatches(e, ok_class)
    {
        *e = SorobanExpr::UnknownVal;
    }
    stmts
}

fn husk_mismatched_returns(stmts: &mut [SorobanStmt], ok_class: &str) {
    for stmt in stmts.iter_mut() {
        match stmt {
            SorobanStmt::Return(Some(e)) if literal_mismatches(e, ok_class) => {
                *e = SorobanExpr::UnknownVal;
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                husk_mismatched_returns(then_body, ok_class);
                husk_mismatched_returns(else_body, ok_class);
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                husk_mismatched_returns(body, ok_class);
            }
            SorobanStmt::For { body, .. } => husk_mismatched_returns(body, ok_class),
            SorobanStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    husk_mismatched_returns(&mut arm.body, ok_class);
                }
            }
            _ => {}
        }
    }
}

fn literal_mismatches(e: &SorobanExpr, ok_class: &str) -> bool {
    // Look through a `ValConvert` — the lifter wraps a fabricated lost value as
    // `ValConvert { value: <lit>, target_type }` and renders it as the bare inner
    // literal (so `ValConvert { false, "u128" }` surfaces as `false`, the E0308).
    // A real `CastAs` (`false as u128`) is a *valid* cast and is deliberately NOT
    // unwrapped here.
    let inner = match e {
        SorobanExpr::ValConvert { value, .. } => value.as_ref(),
        other => other,
    };
    literal_scalar_class(inner).is_some_and(|c| c != ok_class)
}

/// Scalar class of a `Result` ok-type, but **only** for the primitive scalars
/// where a literal of the wrong class is a guaranteed E0308 (so husking is always
/// safe). Integer widths collapse to `"numeric"` (unsuffixed integer literals
/// coerce between them). Non-scalar ok-types (`Address`/`Vec`/`Map`/`Symbol`/
/// `String`/`Bytes`/UDT/`Option`/`Val`/`U256`/`I256`/…) return `None` → the pass
/// never fires on them.
fn scalar_ok_class(ok: &ScSpecTypeDef) -> Option<&'static str> {
    match ok {
        ScSpecTypeDef::U32
        | ScSpecTypeDef::I32
        | ScSpecTypeDef::U64
        | ScSpecTypeDef::I64
        | ScSpecTypeDef::U128
        | ScSpecTypeDef::I128 => Some("numeric"),
        ScSpecTypeDef::Bool => Some("bool"),
        _ => None,
    }
}

/// Scalar class of a primitive literal expression — mirrors [`scalar_ok_class`].
/// Returns `None` for any non-literal expression (so only literals are huskable).
fn literal_scalar_class(e: &SorobanExpr) -> Option<&'static str> {
    match e {
        SorobanExpr::U32Literal(_)
        | SorobanExpr::I32Literal(_)
        | SorobanExpr::U64Literal(_)
        | SorobanExpr::I64Literal(_)
        | SorobanExpr::U128Literal(_)
        | SorobanExpr::I128Literal(_) => Some("numeric"),
        SorobanExpr::BoolLiteral(_) => Some("bool"),
        SorobanExpr::SymbolLiteral(_) => Some("symbol"),
        SorobanExpr::StringLiteral(_) => Some("string"),
        SorobanExpr::BytesLiteral(_) => Some("bytes"),
        _ => None,
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

    // --- annotate_uninferable_gets ---------------------------------------

    fn get(key: &str) -> SorobanExpr {
        SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key: Box::new(SorobanExpr::Param(key.into())),
            unwrap: true,
            on_missing: None,
        }
    }

    fn is_val_annotated(e: &SorobanExpr) -> bool {
        matches!(
            e,
            SorobanExpr::CastAs { value, target_type }
                if target_type == "Val" && matches!(**value, SorobanExpr::StorageGet { .. })
        )
    }

    #[test]
    fn annotates_discarded_get_in_void_fn() {
        // void fn (returns_value=false): `get(&k);` is discarded → annotate `Val`.
        let out = annotate_uninferable_gets(vec![SorobanStmt::Expr(get("k"))], false);
        assert!(
            matches!(&out[0], SorobanStmt::Expr(e) if is_val_annotated(e)),
            "discarded get in void fn should be Val-annotated: {out:?}"
        );
    }

    #[test]
    fn leaves_tail_get_in_value_fn() {
        // value-returning fn: a trailing `get(&k)` is the inferable return value.
        let out = annotate_uninferable_gets(vec![SorobanStmt::Expr(get("k"))], true);
        assert!(
            matches!(&out[0], SorobanStmt::Expr(SorobanExpr::StorageGet { .. })),
            "tail get in a value fn must stay un-annotated (inferable): {out:?}"
        );
    }

    #[test]
    fn annotates_unused_let_get() {
        // `let x = get(&k);` with `x` never referenced → annotate (any fn).
        let out = annotate_uninferable_gets(
            vec![SorobanStmt::Let {
                name: "x".into(),
                mutable: false,
                value: get("k"),
            }],
            true,
        );
        assert!(
            matches!(&out[0], SorobanStmt::Let { value, .. } if is_val_annotated(value)),
            "unused let-bound get should be Val-annotated: {out:?}"
        );
    }

    #[test]
    fn leaves_used_let_get() {
        // `let x = get(&k); require_auth(x);` — `x` is used, so `V` is constrained.
        let out = annotate_uninferable_gets(
            vec![
                SorobanStmt::Let {
                    name: "x".into(),
                    mutable: false,
                    value: get("k"),
                },
                SorobanStmt::Expr(SorobanExpr::RequireAuth(Box::new(SorobanExpr::Param(
                    "x".into(),
                )))),
            ],
            false,
        );
        assert!(
            matches!(&out[0], SorobanStmt::Let { value, .. } if matches!(value, SorobanExpr::StorageGet { .. })),
            "used let-bound get must stay un-annotated: {out:?}"
        );
    }

    #[test]
    fn annotates_auth_target_get_as_address() {
        // `get(&admin).unwrap().require_auth();` → `get::<_, Address>` (the value
        // has require_auth called on it, so it can only be an Address).
        let stmt = SorobanStmt::Expr(SorobanExpr::RequireAuth(Box::new(get("admin"))));
        let out = annotate_uninferable_gets(vec![stmt], false);
        let SorobanStmt::Expr(SorobanExpr::RequireAuth(inner)) = &out[0] else {
            panic!("expected RequireAuth, got {out:?}");
        };
        assert!(
            matches!(&**inner, SorobanExpr::CastAs { value, target_type }
                if target_type == "Address" && matches!(**value, SorobanExpr::StorageGet { .. })),
            "auth-target get should be Address-annotated: {inner:?}"
        );
    }

    #[test]
    fn annotates_nontail_discarded_get_in_value_fn() {
        // value fn: `get(&k);  ret` — the first (non-tail) get is discarded → Val,
        // the trailing `ret` return value is left to inference.
        let out = annotate_uninferable_gets(
            vec![
                SorobanStmt::Expr(get("k")),
                SorobanStmt::Expr(SorobanExpr::Param("ret".into())),
            ],
            true,
        );
        assert!(
            matches!(&out[0], SorobanStmt::Expr(e) if is_val_annotated(e)),
            "non-tail discarded get in a value fn should be Val-annotated: {out:?}"
        );
        assert!(
            matches!(&out[1], SorobanStmt::Expr(SorobanExpr::Param(_))),
            "tail return value must be untouched: {out:?}"
        );
    }

    // --- annotate_uninferable_collections --------------------------------

    fn map_new() -> SorobanExpr {
        SorobanExpr::CollectionNew("Map".into())
    }

    fn method(obj: SorobanExpr, m: &str, args: Vec<SorobanExpr>) -> SorobanExpr {
        SorobanExpr::MethodCall {
            object: Box::new(obj),
            method: m.into(),
            args,
        }
    }

    fn is_val_collection(e: &SorobanExpr) -> bool {
        matches!(
            e,
            SorobanExpr::CastAs { value, target_type }
                if target_type == "Val" && matches!(**value, SorobanExpr::CollectionNew(_))
        )
    }

    #[test]
    fn annotates_inline_map_keys() {
        // `Map::new(&env).keys()` — `.keys()` is value-agnostic, so `V` is lost →
        // annotate the receiver `Map::<_, Val>`.
        let out = annotate_uninferable_collections(vec![SorobanStmt::Expr(method(
            map_new(),
            "keys",
            vec![],
        ))]);
        let SorobanStmt::Expr(SorobanExpr::MethodCall { object, .. }) = &out[0] else {
            panic!("expected method call, got {out:?}");
        };
        assert!(
            is_val_collection(object),
            "inline agnostic-method receiver should be Val-annotated: {object:?}"
        );
    }

    #[test]
    fn annotates_let_map_used_via_contains_key() {
        // `let m = Map::new(&env); m.contains_key(k)` — contains_key pins the key
        // but not the value → annotate `Map::<_, Val>`.
        let out = annotate_uninferable_collections(vec![
            SorobanStmt::Let {
                name: "m".into(),
                mutable: false,
                value: map_new(),
            },
            SorobanStmt::Expr(method(
                SorobanExpr::Param("m".into()),
                "contains_key",
                vec![SorobanExpr::Param("k".into())],
            )),
        ]);
        assert!(
            matches!(&out[0], SorobanStmt::Let { value, .. } if is_val_collection(value)),
            "let-bound map used only value-agnostically should be Val-annotated: {out:?}"
        );
    }

    #[test]
    fn leaves_let_map_fed_typed_value() {
        // config()-shape: contains_key is agnostic, but `set(k, v)` pins the value
        // type → leave honest (annotating `Val` would mismatch the set arg).
        let out = annotate_uninferable_collections(vec![
            SorobanStmt::Let {
                name: "m".into(),
                mutable: false,
                value: map_new(),
            },
            SorobanStmt::Expr(method(
                SorobanExpr::Param("m".into()),
                "contains_key",
                vec![SorobanExpr::Param("k".into())],
            )),
            SorobanStmt::Expr(method(
                SorobanExpr::Param("m".into()),
                "set",
                vec![SorobanExpr::Param("k".into()), map_new()],
            )),
        ]);
        assert!(
            matches!(
                &out[0],
                SorobanStmt::Let {
                    value: SorobanExpr::CollectionNew(_),
                    ..
                }
            ),
            "map fed a value via set must stay un-annotated: {out:?}"
        );
    }

    #[test]
    fn leaves_unused_let_map() {
        // A never-referenced `let m = Map::new()` has both params unconstrained;
        // pinning only `V` would not help, so leave it (out of scope, no-op).
        let out = annotate_uninferable_collections(vec![SorobanStmt::Let {
            name: "m".into(),
            mutable: false,
            value: map_new(),
        }]);
        assert!(
            matches!(
                &out[0],
                SorobanStmt::Let {
                    value: SorobanExpr::CollectionNew(_),
                    ..
                }
            ),
            "unused let map must stay un-annotated: {out:?}"
        );
    }

    #[test]
    fn leaves_bare_map_new() {
        // `Map::new(&env)` as a bare expr (e.g. a typed tail return) — not a
        // value-agnostic receiver, so inference handles it; leave it alone.
        let out = annotate_uninferable_collections(vec![SorobanStmt::Expr(map_new())]);
        assert!(
            matches!(&out[0], SorobanStmt::Expr(SorobanExpr::CollectionNew(_))),
            "bare Map::new in a typed context must stay un-annotated: {out:?}"
        );
    }

    // --- clone_reused_move_params ----------------------------------------

    fn addr_param(name: &str) -> FnParam {
        FnParam {
            name: name.into(),
            type_def: ScSpecTypeDef::Address,
        }
    }

    fn datakey(field: SorobanExpr) -> SorobanStmt {
        SorobanStmt::Expr(SorobanExpr::EnumConstruct {
            type_name: "DataKey".into(),
            variant: "Balance".into(),
            fields: vec![field],
        })
    }

    fn enum_field_is_clone(stmt: &SorobanStmt) -> bool {
        let SorobanStmt::Expr(SorobanExpr::EnumConstruct { fields, .. }) = stmt else {
            return false;
        };
        matches!(&fields[0], SorobanExpr::MethodCall { method, .. } if method == "clone")
    }

    #[test]
    fn clones_addr_param_reused_in_enum_fields() {
        // `DataKey::Balance(addr)` twice → both moves become `addr.clone()`.
        let out = clone_reused_move_params(
            vec![
                datakey(SorobanExpr::Param("addr".into())),
                datakey(SorobanExpr::Param("addr".into())),
            ],
            &[addr_param("addr")],
        );
        assert!(
            enum_field_is_clone(&out[0]) && enum_field_is_clone(&out[1]),
            "both reused Address moves should be cloned: {out:?}"
        );
    }

    #[test]
    fn leaves_single_use_enum_param() {
        // One use → no move-after-move, so no clone.
        let out = clone_reused_move_params(
            vec![datakey(SorobanExpr::Param("addr".into()))],
            &[addr_param("addr")],
        );
        assert!(
            !enum_field_is_clone(&out[0]),
            "single-use param must not be cloned: {out:?}"
        );
    }

    #[test]
    fn leaves_copy_param_reused_in_enum_fields() {
        // A Copy scalar never triggers E0382, so cloning it would be churn.
        let out = clone_reused_move_params(
            vec![
                datakey(SorobanExpr::Param("idx".into())),
                datakey(SorobanExpr::Param("idx".into())),
            ],
            &[FnParam {
                name: "idx".into(),
                type_def: ScSpecTypeDef::U32,
            }],
        );
        assert!(
            !enum_field_is_clone(&out[0]),
            "Copy param must not be cloned: {out:?}"
        );
    }

    // --- Lever 2: type-mismatched Ok-literal husking ---

    fn result_of(ok: ScSpecTypeDef) -> ScSpecTypeDef {
        use stellar_xdr::curr::ScSpecTypeResult;
        ScSpecTypeDef::Result(Box::new(ScSpecTypeResult {
            ok_type: Box::new(ok),
            error_type: Box::new(ScSpecTypeDef::Error),
        }))
    }

    #[test]
    fn husks_bool_literal_in_u128_result() {
        // `Ok(false)` in `-> Result<u128, E>` — bool can never be u128 → husk to todo!().
        let rt = result_of(ScSpecTypeDef::U128);
        let out = husk_type_mismatched_ok_literal(
            vec![SorobanStmt::Expr(SorobanExpr::BoolLiteral(false))],
            Some(&rt),
        );
        assert!(
            matches!(out.as_slice(), [SorobanStmt::Expr(SorobanExpr::UnknownVal)]),
            "expected the bool tail husked to UnknownVal: {out:?}"
        );
    }

    #[test]
    fn husks_valconvert_bool_in_u128_result() {
        // The real corpus shape: a lost value wrapped as `ValConvert { false, "u128" }`
        // in a `return` — renders as bare `false` (E0308). Look through the wrapper.
        let rt = result_of(ScSpecTypeDef::U128);
        let out = husk_type_mismatched_ok_literal(
            vec![SorobanStmt::Return(Some(SorobanExpr::ValConvert {
                value: Box::new(SorobanExpr::BoolLiteral(false)),
                target_type: "u128".to_string(),
            }))],
            Some(&rt),
        );
        assert!(
            matches!(
                out.as_slice(),
                [SorobanStmt::Return(Some(SorobanExpr::UnknownVal))]
            ),
            "expected the ValConvert-wrapped bool husked to UnknownVal: {out:?}"
        );
    }

    #[test]
    fn keeps_matching_numeric_literal() {
        // A numeric literal in a numeric ok-type coerces (unsuffixed) → never husked,
        // even across integer widths (`u64` literal in `Result<i128, E>`).
        let rt = result_of(ScSpecTypeDef::I128);
        let out = husk_type_mismatched_ok_literal(
            vec![SorobanStmt::Return(Some(SorobanExpr::U64Literal(5)))],
            Some(&rt),
        );
        assert!(
            matches!(
                out.as_slice(),
                [SorobanStmt::Return(Some(SorobanExpr::U64Literal(5)))]
            ),
            "matching numeric literal must be left untouched: {out:?}"
        );
    }

    #[test]
    fn keeps_literal_when_ok_type_nonscalar() {
        // Non-scalar ok-type (Address) is out of scope — a literal there is a
        // different error class; leave it honest rather than guess.
        let rt = result_of(ScSpecTypeDef::Address);
        let out = husk_type_mismatched_ok_literal(
            vec![SorobanStmt::Expr(SorobanExpr::BoolLiteral(false))],
            Some(&rt),
        );
        assert!(
            matches!(
                out.as_slice(),
                [SorobanStmt::Expr(SorobanExpr::BoolLiteral(false))]
            ),
            "non-scalar ok-type must not be touched: {out:?}"
        );
    }

    #[test]
    fn keeps_bool_literal_in_bool_result() {
        // Classes match → no mismatch → no husk.
        let rt = result_of(ScSpecTypeDef::Bool);
        let out = husk_type_mismatched_ok_literal(
            vec![SorobanStmt::Expr(SorobanExpr::BoolLiteral(false))],
            Some(&rt),
        );
        assert!(
            matches!(
                out.as_slice(),
                [SorobanStmt::Expr(SorobanExpr::BoolLiteral(false))]
            ),
            "matching bool literal must be left untouched: {out:?}"
        );
    }
}
