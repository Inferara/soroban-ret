use super::soroban_ir::{MatchArm, MatchPattern, SorobanExpr, SorobanStmt, StorageType};

/// Optimize a list of statements, preserving orphan host calls.
/// Used as a fallback when the standard optimization empties a function body
/// that originally had host calls — produces visible output instead of todo!().
pub fn optimize_stmts_preserve_host_calls(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    optimize_stmts_to_fixpoint(stmts, true)
}

/// Optimize a list of statements
pub fn optimize_stmts(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    optimize_stmts_to_fixpoint(stmts, false)
}

/// Defensive fixed-point wrapper around `optimize_stmts_inner`.
///
/// The inner pipeline contains intentional manual unrolling of several passes
/// (`fold_has_get_pattern` ×2, `collapse_trivial_loops` ×3, `remove_empty_matches`
/// ×2) tuned for the common case. This wrapper re-runs the pipeline if a full
/// pass produced new output, catching cases where adding a future pass exposes
/// fresh work for an earlier pass that the manual unrolling didn't anticipate.
///
/// Cap at 4 iterations: in practice convergence is reached in 1 (the manual
/// unrolling already handles the common case). A debug_assert fires if the
/// cap is hit, surfacing a regression to anyone touching the pass order.
fn optimize_stmts_to_fixpoint(stmts: Vec<SorobanStmt>, preserve_orphans: bool) -> Vec<SorobanStmt> {
    const MAX_ITERATIONS: usize = 4;
    let mut current = optimize_stmts_inner(stmts, preserve_orphans);
    let mut converged = false;
    for iteration in 1..MAX_ITERATIONS {
        let prev_repr = format!("{:?}", &current);
        let next = optimize_stmts_inner(current.clone(), preserve_orphans);
        let next_repr = format!("{:?}", &next);
        current = next;
        if prev_repr == next_repr {
            log::trace!(
                "Optimizer reached fixpoint after {} extra iteration(s)",
                iteration - 1
            );
            converged = true;
            break;
        }
    }
    debug_assert!(
        converged,
        "optimizer did not converge in {MAX_ITERATIONS} iterations — pass ordering may need review",
    );
    // Render recovered counted loops as `for i in start..end` AFTER the fixpoint
    // converges, so every other pass (name propagation, DCE, let-binding) has
    // already processed the loop as a `Loop`. This confines `SorobanStmt::For`
    // to a single late rewrite + codegen, instead of every optimizer walker.
    recover_for_loops(current)
}

fn optimize_stmts_inner(stmts: Vec<SorobanStmt>, preserve_orphans: bool) -> Vec<SorobanStmt> {
    let stmts = hoist_post_break_code(stmts);
    log::trace!(
        "Optimizer pass: hoist_post_break_code ({} stmts)",
        stmts.len()
    );
    let stmts = collapse_trivial_loops(stmts);
    log::trace!(
        "Optimizer pass: collapse_trivial_loops [1] ({} stmts)",
        stmts.len()
    );
    let stmts = fold_constants(stmts);
    log::trace!("Optimizer pass: fold_constants ({} stmts)", stmts.len());
    let stmts = fold_constant_conditions(stmts);
    log::trace!(
        "Optimizer pass: fold_constant_conditions ({} stmts)",
        stmts.len()
    );
    let stmts = collapse_trivial_loops(stmts);
    log::trace!(
        "Optimizer pass: collapse_trivial_loops [2] ({} stmts)",
        stmts.len()
    );
    let stmts = fold_constant_matches(stmts);
    log::trace!(
        "Optimizer pass: fold_constant_matches ({} stmts)",
        stmts.len()
    );
    let stmts = fold_has_get_pattern(stmts);
    log::trace!(
        "Optimizer pass: fold_has_get_pattern [1] ({} stmts)",
        stmts.len()
    );
    let stmts = remove_orphan_has_before_get(stmts);
    log::trace!(
        "Optimizer pass: remove_orphan_has_before_get ({} stmts)",
        stmts.len()
    );
    let stmts = remove_redundant_lets(stmts);
    log::trace!(
        "Optimizer pass: remove_redundant_lets ({} stmts)",
        stmts.len()
    );
    let stmts = fold_has_get_pattern(stmts);
    log::trace!(
        "Optimizer pass: fold_has_get_pattern [2] ({} stmts)",
        stmts.len()
    );
    let stmts = remove_leading_panic(stmts);
    log::trace!(
        "Optimizer pass: remove_leading_panic ({} stmts)",
        stmts.len()
    );
    let stmts = recover_discarded_len_into_consumer(stmts);
    log::trace!(
        "Optimizer pass: recover_discarded_len_into_consumer ({} stmts)",
        stmts.len()
    );
    let stmts = recover_discarded_storage_get_into_consumer(stmts);
    log::trace!(
        "Optimizer pass: recover_discarded_storage_get_into_consumer ({} stmts)",
        stmts.len()
    );
    let stmts = remove_spurious_len(stmts, false);
    log::trace!(
        "Optimizer pass: remove_spurious_len ({} stmts)",
        stmts.len()
    );
    let stmts = remove_spurious_get(stmts, false);
    log::trace!(
        "Optimizer pass: remove_spurious_get ({} stmts)",
        stmts.len()
    );
    let stmts = remove_empty_matches(stmts);
    log::trace!(
        "Optimizer pass: remove_empty_matches [1] ({} stmts)",
        stmts.len()
    );
    let stmts = if preserve_orphans {
        stmts
    } else {
        remove_orphan_host_calls(stmts)
    };
    log::trace!(
        "Optimizer pass: remove_orphan_host_calls ({} stmts)",
        stmts.len()
    );
    let stmts = remove_standalone_collection_new(stmts, false);
    log::trace!(
        "Optimizer pass: remove_standalone_collection_new ({} stmts)",
        stmts.len()
    );
    let stmts = remove_duplicate_exprs(stmts);
    log::trace!(
        "Optimizer pass: remove_duplicate_exprs ({} stmts)",
        stmts.len()
    );
    // Recover the generic return type of a cross-contract `invoke_contract` from
    // the SDK's `Val -> T` type-assertion husk that immediately follows it
    // (`if result.get_tag() != Tag::I128Object { panic!() }`), which the lifter
    // left as `if todo!() != 69 { panic!() }`. Run before `remove_val_tag_guards`
    // strips that husk so the tag is still available to read the type from.
    let stmts = recover_invoke_return_types(stmts);
    log::trace!(
        "Optimizer pass: recover_invoke_return_types ({} stmts)",
        stmts.len()
    );
    let stmts = remove_val_tag_guards(stmts);
    log::trace!(
        "Optimizer pass: remove_val_tag_guards ({} stmts)",
        stmts.len()
    );
    // Removing the argument tag-validation guards can expose a now-leading
    // validation-trap `panic!()` that sat between the guards and the real body.
    // The SDK (v26+) emits this prologue trap for arguments whose tag check
    // does not lift to a recognizable `if .get_tag() != Tag::X { panic }` guard
    // (e.g. the `i128` scalar in `events::failed_transfer`), so it survives
    // guard removal as a bare panic. Left in place it would make
    // `remove_dead_code` (below) discard the entire real body as unreachable.
    // Re-run leading-panic removal here, before dead-code elimination, so the
    // trap is stripped and the body that follows it survives.
    let stmts = remove_leading_panic(stmts);
    log::trace!(
        "Optimizer pass: remove_leading_panic [post-guard] ({} stmts)",
        stmts.len()
    );
    let stmts = invert_guard_clauses(stmts);
    log::trace!(
        "Optimizer pass: invert_guard_clauses ({} stmts)",
        stmts.len()
    );
    // Issue #12: an inlined VOID validation helper leaks its `fail_with_error;
    // unreachable` error exits as stray standalone top-level panics between the
    // validation guard and the real body. Drop them before `remove_dead_code`,
    // which would otherwise treat the first as a terminator and truncate the
    // function's live continuation. Runs after guard inversion (so the panic is
    // genuinely standalone) and before dead-code elimination.
    let stmts = drop_stray_panic_before_continuation(stmts);
    log::trace!(
        "Optimizer pass: drop_stray_panic_before_continuation ({} stmts)",
        stmts.len()
    );
    let stmts = remove_dead_code(stmts);
    log::trace!("Optimizer pass: remove_dead_code ({} stmts)", stmts.len());
    let stmts = collapse_trivial_loops(stmts);
    log::trace!(
        "Optimizer pass: collapse_trivial_loops [3] ({} stmts)",
        stmts.len()
    );
    // Dead mutable var elimination + orphan host call removal + trivial loop
    // collapse can leave matches with all-empty arms. Clean them up.
    let stmts = remove_empty_matches(stmts);
    log::trace!(
        "Optimizer pass: remove_empty_matches [2] ({} stmts)",
        stmts.len()
    );
    // Phase 5b: Resolve self-referential Let bindings like
    // `Let var_5 = TupleConstruct([Local(5)])`. When preceded by a standalone
    // `Expr(something)`, promotes the Expr to `Let var_5 = something` and
    // removes the self-referential Let. This must run before bind_unbound_locals
    // because self-ref Lets mask truly unbound references.
    let stmts = resolve_self_referential_lets(stmts);
    log::trace!(
        "Optimizer pass: resolve_self_referential_lets ({} stmts)",
        stmts.len()
    );
    // Phase 5c: Bind unbound locals — when a Local(N) is referenced but never
    // defined via Let, promote the immediately preceding standalone Expr to a
    // Let binding.
    let stmts = bind_unbound_locals(stmts);
    log::trace!(
        "Optimizer pass: bind_unbound_locals ({} stmts)",
        stmts.len()
    );
    // Phase 6: Improve readability — propagate meaningful names from spec/context
    let stmts = propagate_variable_names(stmts, &[]);
    log::trace!(
        "Optimizer pass: propagate_variable_names ({} stmts)",
        stmts.len()
    );
    // Phase 7: De-shadow variable names (e.g., two `let fp2` → `fp2`, `fp2_2`)
    let stmts = deshadow_variable_names(stmts);
    log::trace!(
        "Optimizer pass: deshadow_variable_names ({} stmts)",
        stmts.len()
    );
    // Phase 8: Remove self-referential assignments created by name propagation
    let stmts = remove_self_assignments(stmts);
    log::trace!(
        "Optimizer pass: remove_self_assignments ({} stmts)",
        stmts.len()
    );
    // Phase 9: Strip trailing `return;` (void returns) which are always redundant
    let stmts = strip_trailing_void_returns(stmts);
    log::trace!(
        "Optimizer pass: strip_trailing_void_returns ({} stmts)",
        stmts.len()
    );
    stmts
}

/// Remove self-referential let bindings like `let var_5 = var_5;` which are
/// invalid Rust. These are created when `propagate_variable_names` maps both
/// sides of a Let to the same name.
pub fn remove_self_assignments(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    stmts
        .into_iter()
        .filter_map(|stmt| {
            // Filter out self-referential lets like `let x = x`.
            // For immutable lets, always safe to remove.
            // For mutable lets, only remove if value is a Param reference —
            // name propagation creates `let mut amount = amount` from
            // `let mut var_3 = Param("amount")` which is always safe to drop.
            if let SorobanStmt::Let {
                ref name,
                mutable,
                ref value,
            } = stmt
                && is_self_referential(name, value)
                && (!mutable || is_param_expr(value))
            {
                return None;
            }
            // Filter out self-referential assigns (e.g., `var_2 = var_2;`)
            if let SorobanStmt::Assign {
                ref target,
                ref value,
            } = stmt
                && is_self_referential(target, value)
            {
                return None;
            }
            // Recurse into nested bodies
            Some(remove_self_assignments_stmt(stmt))
        })
        .collect()
}

fn remove_self_assignments_stmt(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: remove_self_assignments(then_body),
            else_body: remove_self_assignments(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: remove_self_assignments(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: remove_self_assignments(body),
        },
        SorobanStmt::Block(stmts) => SorobanStmt::Block(remove_self_assignments(stmts)),
        other => other,
    }
}

/// Check if `Let var_N = VecConstruct([..., Local(N), ...])` can inline a
/// preceding `Expr(something)` by replacing the self-referential `Local(N)`
/// element with `something`. Returns the new VecConstruct value and name.
fn try_inline_vec_self_ref(
    name: &str,
    value: &SorobanExpr,
    preceding: &SorobanStmt,
) -> Option<(SorobanExpr, String)> {
    let idx = name
        .strip_prefix("var_")
        .and_then(|s| s.parse::<u32>().ok())?;
    let SorobanExpr::VecConstruct(elements) = value else {
        return None;
    };
    // Check that exactly one element is Local(idx)
    let self_ref_count = elements
        .iter()
        .filter(|e| matches!(e, SorobanExpr::Local(i) if *i == idx))
        .count();
    if self_ref_count != 1 {
        return None;
    }
    let SorobanStmt::Expr(expr) = preceding else {
        return None;
    };
    // Replace Local(idx) with the preceding expression
    let new_elements: Vec<SorobanExpr> = elements
        .iter()
        .map(|e| {
            if matches!(e, SorobanExpr::Local(i) if *i == idx) {
                expr.clone()
            } else {
                e.clone()
            }
        })
        .collect();
    Some((SorobanExpr::VecConstruct(new_elements), name.to_string()))
}

/// Check if a let binding value resolves to the same name as the binding itself.
/// Handles direct references (Local, NamedLocal, Param) and single-element
/// TupleConstruct which codegen flattens to the inner expression.
fn is_self_referential(name: &str, value: &SorobanExpr) -> bool {
    match value {
        SorobanExpr::Local(idx) => *name == format!("var_{}", idx),
        SorobanExpr::NamedLocal(n) | SorobanExpr::Param(n) => n == name,
        // TupleConstruct with 1 element is flattened by codegen
        SorobanExpr::TupleConstruct(fields) if fields.len() == 1 => {
            is_self_referential(name, &fields[0])
        }
        // ValConvert is transparent in codegen — unwrap it
        SorobanExpr::ValConvert { value, .. } => is_self_referential(name, value),
        _ => false,
    }
}

/// Check if an expression is a Param reference, unwrapping transparent wrappers.
fn is_param_expr(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::Param(_) => true,
        SorobanExpr::ValConvert { value, .. } => is_param_expr(value),
        _ => false,
    }
}

/// Strip trailing `Return(None)` (void returns) from statement lists.
/// These are always redundant — the function/block ends naturally.
/// Recurses into nested bodies.
fn strip_trailing_void_returns(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut stmts: Vec<SorobanStmt> = stmts
        .into_iter()
        .map(strip_trailing_void_returns_stmt)
        .collect();
    // Remove trailing Return(None) at this level
    if matches!(stmts.last(), Some(SorobanStmt::Return(None))) {
        stmts.pop();
    }
    stmts
}

fn strip_trailing_void_returns_stmt(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: strip_trailing_void_returns(then_body),
            else_body: strip_trailing_void_returns(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    body: strip_trailing_void_returns(arm.body),
                    ..arm
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: strip_trailing_void_returns(body),
        },
        SorobanStmt::Block(stmts) => SorobanStmt::Block(strip_trailing_void_returns(stmts)),
        other => other,
    }
}

/// Remove orphan `.has()` statements that immediately precede a `.get()` on the
/// same storage type and key. The `.has()` return value is discarded and the
/// subsequent `.get()` makes it redundant.
fn remove_orphan_has_before_get(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::with_capacity(stmts.len());
    let mut iter = stmts.into_iter().peekable();
    while let Some(stmt) = iter.next() {
        // Check: current stmt is Expr(StorageHas { .. }) and next stmt contains
        // a matching StorageGet with the same storage_type and key.
        if let SorobanStmt::Expr(SorobanExpr::StorageHas {
            ref storage_type,
            ref key,
        }) = stmt
            && let Some(next) = iter.peek()
            && stmt_contains_matching_get(next, storage_type, key)
        {
            // Skip the orphan .has()
            continue;
        }
        // Recurse into nested bodies
        result.push(remove_orphan_has_before_get_stmt(stmt));
    }
    result
}

fn remove_orphan_has_before_get_stmt(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: remove_orphan_has_before_get(then_body),
            else_body: remove_orphan_has_before_get(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: remove_orphan_has_before_get(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: remove_orphan_has_before_get(body),
        },
        SorobanStmt::Block(stmts) => SorobanStmt::Block(remove_orphan_has_before_get(stmts)),
        other => other,
    }
}

/// Check if a statement (or any expression within it) contains a `StorageGet`
/// with the given storage type and key.
fn stmt_contains_matching_get(
    stmt: &SorobanStmt,
    storage_type: &StorageType,
    key: &SorobanExpr,
) -> bool {
    match stmt {
        SorobanStmt::Let { value, .. } => expr_contains_matching_get(value, storage_type, key),
        SorobanStmt::Assign { value, .. } => expr_contains_matching_get(value, storage_type, key),
        SorobanStmt::Return(Some(expr)) | SorobanStmt::Expr(expr) => {
            expr_contains_matching_get(expr, storage_type, key)
        }
        // Look inside If bodies — `has(k); if has(k) { get(k) }` is common
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            expr_contains_matching_get(condition, storage_type, key)
                || then_body
                    .iter()
                    .any(|s| stmt_contains_matching_get(s, storage_type, key))
                || else_body
                    .iter()
                    .any(|s| stmt_contains_matching_get(s, storage_type, key))
        }
        _ => false,
    }
}

fn expr_contains_matching_get(expr: &SorobanExpr, st: &StorageType, key: &SorobanExpr) -> bool {
    if let SorobanExpr::StorageGet {
        storage_type,
        key: get_key,
        ..
    } = expr
        && storage_type == st
        && get_key.as_ref() == key
    {
        return true;
    }
    // Recurse into sub-expressions
    for child in expr_children(expr) {
        if expr_contains_matching_get(child, st, key) {
            return true;
        }
    }
    false
}

/// Return references to direct child expressions of an expression node.
fn expr_children(expr: &SorobanExpr) -> Vec<&SorobanExpr> {
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
        | SorobanExpr::Or(a, b) => vec![a.as_ref(), b.as_ref()],
        SorobanExpr::Not(a) | SorobanExpr::PanicWithError(a) | SorobanExpr::RequireAuth(a) => {
            vec![a.as_ref()]
        }
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            vec![value.as_ref()]
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            let mut children = vec![object.as_ref()];
            children.extend(args.iter());
            children
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => vec![key.as_ref()],
        SorobanExpr::StorageSet { key, value, .. } => vec![key.as_ref(), value.as_ref()],
        SorobanExpr::FieldAccess { object, .. } => vec![object.as_ref()],
        SorobanExpr::TupleConstruct(fields) | SorobanExpr::VecConstruct(fields) => {
            fields.iter().collect()
        }
        SorobanExpr::StructConstruct { fields, .. } => fields.iter().map(|(_, v)| v).collect(),
        SorobanExpr::RawHostCall { args, .. } => args.iter().collect(),
        _ => vec![],
    }
}

/// Remove a spurious leading `panic!()` when the function body continues with
/// real statements after it.  The lifter emits this from `Unreachable` instructions
/// in WASM preamble blocks that precede the actual function body.
fn remove_leading_panic(mut stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    if stmts.len() >= 2
        && matches!(
            &stmts[0],
            SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_))
        )
    {
        stmts.remove(0);
    }
    stmts
}

// ---------------------------------------------------------------------------
// Remove spurious .len() statements
// ---------------------------------------------------------------------------

/// Remove standalone `.len()` method call statements that are XDR unpacking
/// artifacts from SDK-internal validation leaking through inlining.
/// At the function's top level (`nested == false`), keeps `.len()` in tail
/// position (last statement) since it may be an implicit return.
/// In nested bodies (`nested == true`), removes all standalone `.len()` calls
/// since their return values are never used.
fn remove_spurious_len(stmts: Vec<SorobanStmt>, nested: bool) -> Vec<SorobanStmt> {
    let len = stmts.len();
    let mut result = Vec::new();
    for (i, stmt) in stmts.into_iter().enumerate() {
        match stmt {
            // Remove standalone Expr(.len()) statements
            SorobanStmt::Expr(SorobanExpr::MethodCall {
                ref method,
                ref args,
                ..
            }) if method == "len" && args.is_empty() && (nested || i + 1 < len) => {
                // Skip — spurious .len() artifact
            }
            // Recurse into nested bodies (always nested=true for children)
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => result.push(SorobanStmt::If {
                condition,
                then_body: remove_spurious_len(then_body, true),
                else_body: remove_spurious_len(else_body, true),
            }),
            SorobanStmt::Match { scrutinee, arms } => result.push(SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: remove_spurious_len(arm.body, true),
                    })
                    .collect(),
            }),
            SorobanStmt::Loop { body } => result.push(SorobanStmt::Loop {
                body: remove_spurious_len(body, true),
            }),
            SorobanStmt::Block(body) => {
                result.push(SorobanStmt::Block(remove_spurious_len(body, true)));
            }
            other => result.push(other),
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Recover a discarded pure `.len()` into the next statement's starved consumer
// ---------------------------------------------------------------------------

/// Count `UnknownVal` leaves anywhere within `e`.
fn count_unknown_vals(e: &SorobanExpr) -> usize {
    let here = usize::from(matches!(e, SorobanExpr::UnknownVal));
    here + expr_children(e)
        .iter()
        .map(|c| count_unknown_vals(c))
        .sum::<usize>()
}

/// Replace the (assumed unique) `UnknownVal` leaf in `e` with `repl`, returning
/// `(rebuilt, replaced)`. Only rebuilds the expression shapes that appear in
/// conditions / arithmetic operands (comparisons, logical, arithmetic, `Not`,
/// transparent casts); any other shape yields `replaced == false` so the caller
/// conservatively skips the recovery.
fn replace_sole_unknown(e: SorobanExpr, repl: &SorobanExpr) -> (SorobanExpr, bool) {
    // Try to replace in the first child that contains an UnknownVal; rebuild.
    macro_rules! bin {
        ($a:expr, $b:expr, $ctor:path) => {{
            let a = *$a;
            let b = *$b;
            if count_unknown_vals(&a) > 0 {
                let (na, r) = replace_sole_unknown(a, repl);
                ($ctor(Box::new(na), Box::new(b)), r)
            } else {
                let (nb, r) = replace_sole_unknown(b, repl);
                ($ctor(Box::new(a), Box::new(nb)), r)
            }
        }};
    }
    match e {
        SorobanExpr::UnknownVal => (repl.clone(), true),
        SorobanExpr::Not(a) => {
            let (na, r) = replace_sole_unknown(*a, repl);
            (SorobanExpr::Not(Box::new(na)), r)
        }
        SorobanExpr::Eq(a, b) => bin!(a, b, SorobanExpr::Eq),
        SorobanExpr::Ne(a, b) => bin!(a, b, SorobanExpr::Ne),
        SorobanExpr::Lt(a, b) => bin!(a, b, SorobanExpr::Lt),
        SorobanExpr::Le(a, b) => bin!(a, b, SorobanExpr::Le),
        SorobanExpr::Gt(a, b) => bin!(a, b, SorobanExpr::Gt),
        SorobanExpr::Ge(a, b) => bin!(a, b, SorobanExpr::Ge),
        SorobanExpr::And(a, b) => bin!(a, b, SorobanExpr::And),
        SorobanExpr::Or(a, b) => bin!(a, b, SorobanExpr::Or),
        SorobanExpr::Add(a, b) => bin!(a, b, SorobanExpr::Add),
        SorobanExpr::Sub(a, b) => bin!(a, b, SorobanExpr::Sub),
        SorobanExpr::Mul(a, b) => bin!(a, b, SorobanExpr::Mul),
        SorobanExpr::Div(a, b) => bin!(a, b, SorobanExpr::Div),
        SorobanExpr::Rem(a, b) => bin!(a, b, SorobanExpr::Rem),
        SorobanExpr::ValConvert { value, target_type } => {
            let (nv, r) = replace_sole_unknown(*value, repl);
            (
                SorobanExpr::ValConvert {
                    value: Box::new(nv),
                    target_type,
                },
                r,
            )
        }
        SorobanExpr::CastAs { value, target_type } => {
            let (nv, r) = replace_sole_unknown(*value, repl);
            (
                SorobanExpr::CastAs {
                    value: Box::new(nv),
                    target_type,
                },
                r,
            )
        }
        other => (other, false),
    }
}

/// True for a side-effect-free object a pure `.len()` can be re-evaluated against:
/// a parameter / local / named-local reference, or a field access reaching one.
/// Excludes anything that could carry a side effect (host calls, storage, …).
fn is_pure_len_object(e: &SorobanExpr) -> bool {
    match e {
        SorobanExpr::Param(_) | SorobanExpr::Local(_) | SorobanExpr::NamedLocal(_) => true,
        SorobanExpr::FieldAccess { object, .. } => is_pure_len_object(object),
        _ => false,
    }
}

/// If `stmt` is a discarded pure `.len()` call (`Expr(obj.len())` with a
/// side-effect-free object), return that expression.
///
/// Restricted to `.len()` deliberately. `.len()` returns a count that is compared
/// directly, so substituting it for the lost consumer value is faithful. By
/// contrast `.get(i)` returns an *element* that the SDK frequently tag-extracts or
/// unwraps before comparing — the lost intermediate (e.g. `Ne(UnknownVal, 77)`,
/// where 77 is an ScVal type tag) is a derivation of the element, NOT the element
/// itself, so recovering the raw `.get(i)` fabricates a wrong condition
/// (`tokens.get(1) != 77`). Correctness over count: only `.len()` qualifies.
fn discarded_pure_len(stmt: &SorobanStmt) -> Option<&SorobanExpr> {
    match stmt {
        SorobanStmt::Expr(
            e @ SorobanExpr::MethodCall {
                object,
                method,
                args,
            },
        ) if method == "len" && args.is_empty() && is_pure_len_object(object) => Some(e),
        _ => None,
    }
}

/// The single "consuming position" of a statement — the condition of an `If`, or
/// the value of a `Let`/`Assign`/`Return`/`Expr`. Returns the rebuilt statement
/// with its consuming expression's sole `UnknownVal` replaced by `repl`, or
/// `None` if that position does not contain exactly one `UnknownVal` (or the
/// replace could not be applied to its shape).
fn fill_sole_unknown_in_consumer(stmt: &SorobanStmt, repl: &SorobanExpr) -> Option<SorobanStmt> {
    fn try_fill(target: &SorobanExpr, repl: &SorobanExpr) -> Option<SorobanExpr> {
        if count_unknown_vals(target) != 1 {
            return None;
        }
        let (rebuilt, replaced) = replace_sole_unknown(target.clone(), repl);
        replaced.then_some(rebuilt)
    }
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => Some(SorobanStmt::If {
            condition: try_fill(condition, repl)?,
            then_body: then_body.clone(),
            else_body: else_body.clone(),
        }),
        SorobanStmt::Let {
            name,
            mutable,
            value,
        } => Some(SorobanStmt::Let {
            name: name.clone(),
            mutable: *mutable,
            value: try_fill(value, repl)?,
        }),
        SorobanStmt::Assign { target, value } => Some(SorobanStmt::Assign {
            target: target.clone(),
            value: try_fill(value, repl)?,
        }),
        SorobanStmt::Return(Some(e)) => Some(SorobanStmt::Return(Some(try_fill(e, repl)?))),
        SorobanStmt::Expr(e) => Some(SorobanStmt::Expr(try_fill(e, repl)?)),
        _ => None,
    }
}

/// Recover a discarded pure `.len()` whose value the lifter lost to `UnknownVal`
/// in the immediately-following statement's consuming position.
///
/// The lifter computes `vec.len()` (pushing the result), but a structured
/// control-flow boundary flushes it as a discarded `Expr` statement and the
/// consuming comparison underflows to `UnknownVal`
/// (`Expr(tokens.len()); if UnknownVal != 0 { … }`). When a discarded pure
/// `.len()` is directly followed by a statement whose condition/value contains
/// **exactly one** `UnknownVal`, substitute the len into that slot and drop the
/// now-consumed `Expr`.
///
/// Safe because `.len()` is pure and idempotent (re-evaluating it is
/// side-effect-free), and the WASM adjacency — value computed, then immediately
/// consumed by the next instruction — makes the linkage near-certain. The
/// exactly-one-`UnknownVal` gate keeps the target unambiguous; any other shape is
/// left untouched.
fn recover_discarded_len_into_consumer(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    // Recurse into child bodies first so inner adjacent pairs are handled too.
    let stmts: Vec<SorobanStmt> = stmts
        .into_iter()
        .map(|s| match s {
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => SorobanStmt::If {
                condition,
                then_body: recover_discarded_len_into_consumer(then_body),
                else_body: recover_discarded_len_into_consumer(else_body),
            },
            SorobanStmt::Loop { body } => SorobanStmt::Loop {
                body: recover_discarded_len_into_consumer(body),
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
                body: recover_discarded_len_into_consumer(body),
            },
            SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: recover_discarded_len_into_consumer(arm.body),
                    })
                    .collect(),
            },
            SorobanStmt::Block(body) => {
                SorobanStmt::Block(recover_discarded_len_into_consumer(body))
            }
            other => other,
        })
        .collect();

    // Adjacent-pair pass at this level.
    let mut result: Vec<SorobanStmt> = Vec::with_capacity(stmts.len());
    let mut k = 0;
    while k < stmts.len() {
        if k + 1 < stmts.len()
            && let Some(len_expr) = discarded_pure_len(&stmts[k])
            && let Some(new_next) = fill_sole_unknown_in_consumer(&stmts[k + 1], len_expr)
        {
            cov_mark::hit!(discarded_len_recovered);
            result.push(new_next);
            k += 2;
            continue;
        }
        result.push(stmts[k].clone());
        k += 1;
    }
    result
}

// ---------------------------------------------------------------------------
// Thread a discarded storage load into an immediately-following require_auth
// ---------------------------------------------------------------------------

/// If `stmt` is a discarded storage load (`Expr(StorageGet { unwrap: true })`),
/// return that expression. The SDK's admin/owner gate loads an Address from
/// storage and immediately requires its authorization; a structured-control-flow
/// boundary flushes the load as a value-discarding `Expr` statement, so re-siting
/// it into the adjacent consumer is faithful. Restricted to `unwrap: true` — an
/// unwrapped get yields the stored value itself (the Address), the only shape a
/// `require_auth` target legitimately comes from.
fn discarded_storage_get(stmt: &SorobanStmt) -> Option<&SorobanExpr> {
    match stmt {
        SorobanStmt::Expr(e @ SorobanExpr::StorageGet { unwrap: true, .. }) => Some(e),
        _ => None,
    }
}

/// If `stmt` is `Expr(RequireAuth(UnknownVal))` or
/// `Expr(RequireAuthForArgs { address: UnknownVal, .. })`, return the statement
/// with the lost address replaced by `addr`. Gated on a *bare* `UnknownVal`
/// address so the rewrite is unambiguous — a target that already carries a value
/// is never touched.
fn fill_require_auth_target(stmt: &SorobanStmt, addr: &SorobanExpr) -> Option<SorobanStmt> {
    match stmt {
        SorobanStmt::Expr(SorobanExpr::RequireAuth(target))
            if matches!(**target, SorobanExpr::UnknownVal) =>
        {
            Some(SorobanStmt::Expr(SorobanExpr::RequireAuth(Box::new(
                addr.clone(),
            ))))
        }
        SorobanStmt::Expr(SorobanExpr::RequireAuthForArgs { address, args })
            if matches!(**address, SorobanExpr::UnknownVal) =>
        {
            Some(SorobanStmt::Expr(SorobanExpr::RequireAuthForArgs {
                address: Box::new(addr.clone()),
                args: args.clone(),
            }))
        }
        _ => None,
    }
}

/// Thread a discarded, just-loaded storage value into an immediately-following
/// `require_auth` whose target the lifter lost to `UnknownVal`.
///
/// The admin/owner authorization idiom — `let admin = get(&Admin).unwrap();
/// admin.require_auth();` — lifts as a discarded load followed by a
/// target-less auth (`get(&k).unwrap(); todo!().require_auth();`) because the
/// loaded value is flushed at a control-flow boundary and the auth's operand
/// underflows to `UnknownVal`. When a discarded `StorageGet` is directly followed
/// by a `require_auth` / `require_auth_for_args` whose address is exactly
/// `UnknownVal`, substitute the get for that target and drop the now-consumed
/// `Expr`.
///
/// Safe because the get is a pure read (idempotent; it executes in both the
/// before and after forms) and the WASM adjacency — value loaded, then
/// immediately consumed by the next instruction — makes the linkage near-certain.
/// Restricted to the auth-target position (never a length / arithmetic consumer)
/// and to a bare `UnknownVal` address, so the rewrite is unambiguous.
fn recover_discarded_storage_get_into_consumer(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    // Recurse into child bodies first so inner adjacent pairs are handled too.
    let stmts: Vec<SorobanStmt> = stmts
        .into_iter()
        .map(|s| match s {
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => SorobanStmt::If {
                condition,
                then_body: recover_discarded_storage_get_into_consumer(then_body),
                else_body: recover_discarded_storage_get_into_consumer(else_body),
            },
            SorobanStmt::Loop { body } => SorobanStmt::Loop {
                body: recover_discarded_storage_get_into_consumer(body),
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
                body: recover_discarded_storage_get_into_consumer(body),
            },
            SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: recover_discarded_storage_get_into_consumer(arm.body),
                    })
                    .collect(),
            },
            SorobanStmt::Block(body) => {
                SorobanStmt::Block(recover_discarded_storage_get_into_consumer(body))
            }
            other => other,
        })
        .collect();

    // Adjacent-pair pass at this level.
    let mut result: Vec<SorobanStmt> = Vec::with_capacity(stmts.len());
    let mut k = 0;
    while k < stmts.len() {
        if k + 1 < stmts.len()
            && let Some(get) = discarded_storage_get(&stmts[k])
            && let Some(new_next) = fill_require_auth_target(&stmts[k + 1], get)
        {
            cov_mark::hit!(discarded_get_into_require_auth);
            result.push(new_next);
            k += 2;
            continue;
        }
        result.push(stmts[k].clone());
        k += 1;
    }
    result
}

// ---------------------------------------------------------------------------
// Hoist post-break code from loop bodies
// ---------------------------------------------------------------------------

/// Hoist code trapped after a top-level `break` inside a loop body.
///
/// WASM Stackify creates patterns like:
/// ```text
/// loop { validation; break; actual_body; return }
/// ```
/// The code after `break` is structurally unreachable inside the loop but
/// represents the actual function body. We move it outside the loop:
/// ```text
/// loop { validation; break }; actual_body; return
/// ```
fn hoist_post_break_code(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::new();
    for stmt in stmts {
        match stmt {
            SorobanStmt::Loop { body } => {
                // First, recurse into nested structures within the loop body
                let body = hoist_post_break_code(body);
                // Find the first top-level Break in the loop body
                if let Some(break_pos) = body.iter().position(|s| matches!(s, SorobanStmt::Break)) {
                    let after_break = &body[break_pos + 1..];
                    // Only hoist if the post-break code doesn't contain bare
                    // break/continue — those are loop-specific and would be
                    // invalid outside the loop.
                    if !after_break.is_empty() && !stmts_contain_break_or_continue(after_break) {
                        let hoisted: Vec<_> = after_break.to_vec();
                        let loop_body = body[..=break_pos].to_vec();
                        result.push(SorobanStmt::Loop { body: loop_body });
                        result.extend(hoisted);
                        continue;
                    }
                }
                result.push(SorobanStmt::Loop { body });
            }
            // Recurse into nested structures
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => result.push(SorobanStmt::If {
                condition,
                then_body: hoist_post_break_code(then_body),
                else_body: hoist_post_break_code(else_body),
            }),
            SorobanStmt::Match { scrutinee, arms } => result.push(SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: hoist_post_break_code(arm.body),
                    })
                    .collect(),
            }),
            SorobanStmt::Block(body) => {
                result.push(SorobanStmt::Block(hoist_post_break_code(body)));
            }
            other => result.push(other),
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Collapse trivial loops (SAILR-style deoptimization)
// ---------------------------------------------------------------------------

/// Collapse trivial single-iteration loops that result from SDK Val-validation
/// preambles. After constant-condition folding eliminates dead branches, these
/// loops often become `loop { break }` or `loop { stmts; break }`.
fn collapse_trivial_loops(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::new();
    for stmt in stmts {
        match stmt {
            SorobanStmt::Loop { body } => {
                // First, recursively collapse nested loops within the body
                let body = collapse_trivial_loops(body);
                // Strip trailing `continue` — it's redundant at end of loop body
                let body = if matches!(body.last(), Some(SorobanStmt::Continue)) {
                    let mut body = body;
                    body.pop();
                    body
                } else {
                    body
                };
                // `loop { break }` or `loop { }` (after continue strip) → remove entirely
                if body.is_empty() || matches!(body.as_slice(), [SorobanStmt::Break]) {
                    cov_mark::hit!(trivial_loop_collapsed);
                    continue;
                }
                // `loop { continue; ... }` → remove entirely (infinite empty loop,
                // dead validation artifact from SDK-internal code).
                if matches!(body.first(), Some(SorobanStmt::Continue)) {
                    cov_mark::hit!(trivial_loop_collapsed);
                    continue;
                }
                // `loop { if cond { break; } }` → remove entirely, but only
                // when the condition has no side effects. If the condition
                // triggers a host call (storage read, invoke_contract, etc.)
                // the call itself is observable, and even though Soroban is
                // single-threaded and the condition's *value* can't change
                // between iterations, dropping the loop drops the call. Keep
                // the loop in that case.
                if let [
                    SorobanStmt::If {
                        condition,
                        then_body,
                        else_body,
                    },
                ] = body.as_slice()
                    && matches!(then_body.as_slice(), [SorobanStmt::Break])
                    && else_body.is_empty()
                    && !expr_has_side_effects(condition)
                {
                    cov_mark::hit!(trivial_loop_collapsed);
                    continue;
                }
                // `loop { stmts...; break }` → inline stmts (single iteration)
                if matches!(body.last(), Some(SorobanStmt::Break))
                    && !stmts_contain_continue(&body[..body.len() - 1])
                {
                    cov_mark::hit!(trivial_loop_collapsed);
                    // Inline all statements except the trailing break
                    let count = body.len() - 1;
                    result.extend(body.into_iter().take(count));
                    continue;
                }
                // `loop { stmts...; return }` → inline stmts (single-iteration
                // inlined callee). Return(None) = void return from inlined callee,
                // drop it. Return(Some(val)) = value return, keep it.
                if matches!(body.last(), Some(SorobanStmt::Return(_)))
                    && !stmts_contain_break_or_continue(&body)
                {
                    cov_mark::hit!(trivial_loop_collapsed);
                    match body.last() {
                        Some(SorobanStmt::Return(None)) => {
                            let count = body.len() - 1;
                            result.extend(body.into_iter().take(count));
                        }
                        _ => {
                            result.extend(body);
                        }
                    }
                    continue;
                }
                // `loop { stmts...; panic!() }` → inline stmts (panic never returns,
                // so loop is single-iteration). Same as the return case.
                if matches!(
                    body.last(),
                    Some(SorobanStmt::Expr(
                        SorobanExpr::Panic | SorobanExpr::PanicWithError(_)
                    ))
                ) && !stmts_contain_break_or_continue(&body)
                {
                    cov_mark::hit!(trivial_loop_collapsed);
                    result.extend(body);
                    continue;
                }
                // `loop { stmts... }` whose body has no back-edge (`continue`) and
                // no `break` at this loop's level → inline as straight-line code. A
                // WASM `loop` block only repeats when control explicitly branches
                // back to its label (lifted to `Continue`); without that it runs
                // exactly once and falls through. A genuinely repeating loop keeps
                // its trailing `Continue` (stripped above only when redundant in
                // Rust's auto-repeat sense), or carries a `Break`/`Continue`, so
                // those are preserved by the guard. This recovers function bodies
                // (e.g. SDK v26 wraps `require_auth; invoke` in such a block) that
                // would otherwise render as a spurious `loop { … }`.
                if !stmts_contain_break_or_continue(&body) {
                    cov_mark::hit!(trivial_loop_collapsed);
                    result.extend(body);
                    continue;
                }
                result.push(SorobanStmt::Loop { body });
            }
            // Recurse into nested structures
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => result.push(SorobanStmt::If {
                condition,
                then_body: collapse_trivial_loops(then_body),
                else_body: collapse_trivial_loops(else_body),
            }),
            SorobanStmt::Match { scrutinee, arms } => result.push(SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: collapse_trivial_loops(arm.body),
                    })
                    .collect(),
            }),
            SorobanStmt::Block(body) => {
                result.push(SorobanStmt::Block(collapse_trivial_loops(body)));
            }
            // A `for` is never collapsed (it carries its own bound), but recurse
            // into its body so nested trivial loops are still removed.
            SorobanStmt::For {
                var,
                start,
                end,
                step,
                body,
            } => result.push(SorobanStmt::For {
                var,
                start,
                end,
                step,
                body: collapse_trivial_loops(body),
            }),
            other => result.push(other),
        }
    }
    result
}

/// Rewrite a recovered counted loop into a `for var in start..end` (with
/// Recognize the SDK liquidity-pool-router token-list validation and lift it to a
/// faithful canonical form.
///
/// The validation — inlined into ~27 aquarius accessors (`get_total_*`,
/// `distribute_outstanding_reward`, …) — lifts to a structurally mangled loop:
/// the induction variable and the `tokens.len()` bound degrade to `UnknownVal`
/// and an unconditional mid-loop `break` kills the comparison, leaving ~4
/// `todo!()` per occurrence. Its *intent*, however, is fully recovered: the
/// `obj_cmp(prev, tokens.get(..))` direction plus the near-unique error-code pair
/// `TokensNotSorted` + `DuplicatesNotAllowed` prove it asserts the token vec is
/// strictly ascending (sorted, no duplicates). Replace the mangled statement with
/// the behaviorally equivalent, readable
/// ```text
/// for i in 1..tokens.len() {
///     if tokens.get(i - 1) > tokens.get(i) { panic_with_error!(.., TokensNotSorted) }
///     if tokens.get(i - 1) == tokens.get(i) { panic_with_error!(.., DuplicatesNotAllowed) }
/// }
/// ```
/// (`1..len` naturally no-ops for an empty or single-element vec, so no length
/// guard is needed). The param name and both `ContractError` exprs are taken from
/// the matched subtree, so this is not contract-specific.
///
/// Tightly gated: fires only on a statement whose subtree contains BOTH panic
/// variants AND a `vec.get(..)` over a parameter — a signature unique to this
/// validation. Anything else is left untouched (no fabricated control flow).
pub fn recover_tokens_sorted_validation(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut out = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        if is_token_sort_validation(&stmt)
            && let Some(vec_param) = find_validated_vec_param(&stmt)
            && let Some(sorted_err) = find_panic_error_expr(&stmt, "TokensNotSorted")
            && let Some(dup_err) = find_panic_error_expr(&stmt, "DuplicatesNotAllowed")
        {
            cov_mark::hit!(tokens_sorted_validation_recovered);
            let get = |idx: SorobanExpr| SorobanExpr::MethodCall {
                object: Box::new(SorobanExpr::Param(vec_param.clone())),
                method: "get".to_string(),
                args: vec![idx],
            };
            let prev = || {
                get(SorobanExpr::Sub(
                    Box::new(SorobanExpr::NamedLocal("i".to_string())),
                    Box::new(SorobanExpr::U32Literal(1)),
                ))
            };
            let cur = || get(SorobanExpr::NamedLocal("i".to_string()));
            let panic =
                |e: SorobanExpr| vec![SorobanStmt::Expr(SorobanExpr::PanicWithError(Box::new(e)))];
            out.push(SorobanStmt::For {
                var: "i".to_string(),
                start: SorobanExpr::U32Literal(1),
                end: SorobanExpr::MethodCall {
                    object: Box::new(SorobanExpr::Param(vec_param.clone())),
                    method: "len".to_string(),
                    args: vec![],
                },
                step: 1,
                body: vec![
                    SorobanStmt::If {
                        condition: SorobanExpr::Gt(Box::new(prev()), Box::new(cur())),
                        then_body: panic(sorted_err),
                        else_body: vec![],
                    },
                    SorobanStmt::If {
                        condition: SorobanExpr::Eq(Box::new(prev()), Box::new(cur())),
                        then_body: panic(dup_err),
                        else_body: vec![],
                    },
                ],
            });
            continue;
        }
        out.push(recover_tokens_sorted_in_stmt(stmt));
    }
    out
}

/// Recurse `recover_tokens_sorted_validation` into a statement's nested bodies.
fn recover_tokens_sorted_in_stmt(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: recover_tokens_sorted_validation(then_body),
            else_body: recover_tokens_sorted_validation(else_body),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: recover_tokens_sorted_validation(body),
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
            body: recover_tokens_sorted_validation(body),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(recover_tokens_sorted_validation(body)),
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: recover_tokens_sorted_validation(arm.body),
                })
                .collect(),
        },
        other => other,
    }
}

/// True if `stmt`'s subtree contains BOTH the `TokensNotSorted` and
/// `DuplicatesNotAllowed` panic variants — the unique signature of the router's
/// token-list validation.
fn is_token_sort_validation(stmt: &SorobanStmt) -> bool {
    stmt_subtree_has_error_variant(stmt, "TokensNotSorted")
        && stmt_subtree_has_error_variant(stmt, "DuplicatesNotAllowed")
}

/// Whether `stmt`'s subtree contains a `PanicWithError(ContractError { variant })`.
fn stmt_subtree_has_error_variant(stmt: &SorobanStmt, variant: &str) -> bool {
    find_panic_error_expr(stmt, variant).is_some()
}

/// Find and clone the `ContractError` expr of a `PanicWithError` for `variant`
/// anywhere in `stmt`'s subtree.
fn find_panic_error_expr(stmt: &SorobanStmt, variant: &str) -> Option<SorobanExpr> {
    fn in_stmts(stmts: &[SorobanStmt], variant: &str) -> Option<SorobanExpr> {
        stmts.iter().find_map(|s| find_panic_error_expr(s, variant))
    }
    fn in_expr(e: &SorobanExpr, variant: &str) -> Option<SorobanExpr> {
        if let SorobanExpr::PanicWithError(inner) = e
            && let SorobanExpr::ContractError {
                variant_name: Some(v),
                ..
            } = inner.as_ref()
            && v == variant
        {
            return Some(inner.as_ref().clone());
        }
        None
    }
    match stmt {
        SorobanStmt::Expr(e) => in_expr(e, variant),
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => in_stmts(then_body, variant).or_else(|| in_stmts(else_body, variant)),
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => in_stmts(body, variant),
        SorobanStmt::For { body, .. } => in_stmts(body, variant),
        SorobanStmt::Match { arms, .. } => arms.iter().find_map(|a| in_stmts(&a.body, variant)),
        _ => None,
    }
}

/// Find the parameter name of the vec being validated, from the first
/// `MethodCall { object: Param(p), method: "get", .. }` in `stmt`'s subtree.
fn find_validated_vec_param(stmt: &SorobanStmt) -> Option<String> {
    fn in_stmts(stmts: &[SorobanStmt]) -> Option<String> {
        stmts.iter().find_map(find_validated_vec_param)
    }
    fn in_expr(e: &SorobanExpr) -> Option<String> {
        match e {
            SorobanExpr::MethodCall {
                object,
                method,
                args,
            } => {
                if method == "get"
                    && let SorobanExpr::Param(p) = object.as_ref()
                {
                    return Some(p.clone());
                }
                in_expr(object).or_else(|| args.iter().find_map(in_expr))
            }
            SorobanExpr::Gt(a, b)
            | SorobanExpr::Lt(a, b)
            | SorobanExpr::Ge(a, b)
            | SorobanExpr::Le(a, b)
            | SorobanExpr::Eq(a, b)
            | SorobanExpr::Ne(a, b)
            | SorobanExpr::Sub(a, b)
            | SorobanExpr::Add(a, b) => in_expr(a).or_else(|| in_expr(b)),
            SorobanExpr::Not(a) => in_expr(a),
            SorobanExpr::RawHostCall { args, .. } => args.iter().find_map(in_expr),
            _ => None,
        }
    }
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => in_expr(e),
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => in_expr(value),
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => in_expr(condition)
            .or_else(|| in_stmts(then_body))
            .or_else(|| in_stmts(else_body)),
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => in_stmts(body),
        SorobanStmt::For { body, .. } => in_stmts(body),
        SorobanStmt::Match { arms, .. } => arms.iter().find_map(|a| in_stmts(&a.body)),
        _ => None,
    }
}

/// `.step_by` for non-unit steps) when its induction variable is dead after the
/// loop — `for` scopes the counter, so it must not be read afterward.
///
/// Matches the shape produced by loop-carried recovery in the lifter:
/// ```text
/// let mut var_i = <start>;
/// loop { if var_i == <end> { break; }  <body...>  var_i = var_i + <step>; }
/// ```
/// and rewrites it to `for var_i in start..end { <body without the break-guard
/// and the increment> }`, dropping the now-redundant `let mut`.
fn recover_for_loops(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    // Recurse into nested bodies first so inner loops are handled.
    let mut stmts: Vec<SorobanStmt> = stmts.into_iter().map(recover_for_loops_in_stmt).collect();

    let mut i = 0;
    while i < stmts.len() {
        let SorobanStmt::Loop { body } = &stmts[i] else {
            i += 1;
            continue;
        };
        let Some((counter_idx, step, end_expr)) = counted_for_shape(body) else {
            i += 1;
            continue;
        };
        // Only ascending unit-or-positive steps map cleanly to `start..end`.
        if step <= 0 {
            i += 1;
            continue;
        }
        // The counter must be dead after the loop (the `for` binding is scoped).
        if count_local_in_stmts(&stmts[i + 1..], counter_idx, false).0 != 0 {
            i += 1;
            continue;
        }
        // Find the `let mut var_{idx} = <start>` that initializes the counter.
        let name = format!("var_{counter_idx}");
        let Some(let_pos) = stmts[..i].iter().rposition(
            |s| matches!(s, SorobanStmt::Let { name: n, mutable: true, .. } if *n == name),
        ) else {
            i += 1;
            continue;
        };
        // Between the init and the loop the counter must be untouched (it really
        // is just the loop's induction variable).
        if count_local_in_stmts(&stmts[let_pos + 1..i], counter_idx, false).0 != 0 {
            i += 1;
            continue;
        }
        let SorobanStmt::Let {
            value: start_expr, ..
        } = stmts[let_pos].clone()
        else {
            unreachable!()
        };
        // The range must reach the `== end` exit exactly and ascend: otherwise
        // `(start..end).step_by(step)` would iterate a different number of times
        // than the WASM `i == end` loop (e.g. step 2 over 0..5 stops at 4 while
        // the WASM never hits 5). Bail to the plain `while` form in that case.
        match (expr_as_int(&start_expr), expr_as_int(&end_expr)) {
            (Some(s), Some(e)) if e >= s && (e - s) % step == 0 => {}
            _ => {
                i += 1;
                continue;
            }
        }
        let SorobanStmt::Loop { body } = &stmts[i] else {
            unreachable!()
        };
        let for_body = build_for_body(body, counter_idx);
        stmts[i] = SorobanStmt::For {
            var: name,
            start: start_expr,
            end: end_expr,
            step,
            body: for_body,
        };
        stmts.remove(let_pos);
        // `let_pos < i`, so the new `For` now sits at `i - 1`; `i` already points
        // at the following statement. Continue without advancing.
    }
    stmts
}

fn recover_for_loops_in_stmt(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: recover_for_loops(then_body),
            else_body: recover_for_loops(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: recover_for_loops(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: recover_for_loops(body),
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
            body: recover_for_loops(body),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(recover_for_loops(body)),
        other => other,
    }
}

/// Extract a small integer value from an integer literal expression.
fn expr_as_int(expr: &SorobanExpr) -> Option<i64> {
    match expr {
        SorobanExpr::I32Literal(v) => Some(*v as i64),
        SorobanExpr::I64Literal(v) => Some(*v),
        SorobanExpr::U32Literal(v) => Some(*v as i64),
        SorobanExpr::U64Literal(v) => Some(*v as i64),
        _ => None,
    }
}

/// For a counter-exit test `var_i == <const>`, return `(i, end_const_expr)`.
fn eq_counter_and_end(cond: &SorobanExpr) -> Option<(u32, SorobanExpr)> {
    let SorobanExpr::Eq(a, b) = cond else {
        return None;
    };
    match (a.as_ref(), b.as_ref()) {
        (SorobanExpr::Local(idx), other) if expr_as_int(other).is_some() => {
            Some((*idx, (**b).clone()))
        }
        (other, SorobanExpr::Local(idx)) if expr_as_int(other).is_some() => {
            Some((*idx, (**a).clone()))
        }
        _ => None,
    }
}

/// For a counter step `var_i = var_i + C` / `var_i - C`, return the signed step.
fn increment_step(value: &SorobanExpr, idx: u32) -> Option<i64> {
    match value {
        SorobanExpr::Add(a, b) => match (a.as_ref(), b.as_ref()) {
            (SorobanExpr::Local(i), other) if *i == idx => expr_as_int(other),
            (other, SorobanExpr::Local(i)) if *i == idx => expr_as_int(other),
            _ => None,
        },
        SorobanExpr::Sub(a, b) => match (a.as_ref(), b.as_ref()) {
            (SorobanExpr::Local(i), other) if *i == idx => expr_as_int(other).map(|s| -s),
            _ => None,
        },
        _ => None,
    }
}

/// Recognize the `loop { if i == end { break; } ...; i = i + step }` shape and
/// return `(counter_index, step, end_expr)`. Requires the break-guard as the
/// first statement and exactly one counter-increment assignment.
fn counted_for_shape(body: &[SorobanStmt]) -> Option<(u32, i64, SorobanExpr)> {
    if body.len() < 2 {
        return None;
    }
    let SorobanStmt::If {
        condition,
        then_body,
        else_body,
    } = &body[0]
    else {
        return None;
    };
    if !(else_body.is_empty() && then_body.len() == 1 && matches!(then_body[0], SorobanStmt::Break))
    {
        return None;
    }
    let (counter_idx, end_expr) = eq_counter_and_end(condition)?;

    let name = format!("var_{counter_idx}");
    let mut step = None;
    let mut assign_count = 0u32;
    let mut increment_pos = None;
    for (k, s) in body.iter().enumerate().skip(1) {
        if let SorobanStmt::Assign { target, value } = s
            && *target == name
        {
            assign_count += 1;
            if let Some(st) = increment_step(value, counter_idx) {
                step = Some(st);
                increment_pos = Some(k);
            }
        }
    }
    if assign_count != 1 {
        return None;
    }
    // The increment must be the last meaningful statement (a trailing `continue`
    // is fine and gets stripped). Otherwise a statement after it reads the
    // counter post-increment, but `build_for_body` removes the increment and the
    // `for` range steps the counter — so that statement would see the wrong value.
    let last_meaningful = body
        .iter()
        .rposition(|s| !matches!(s, SorobanStmt::Continue))?;
    if increment_pos? != last_meaningful {
        return None;
    }
    Some((counter_idx, step?, end_expr))
}

/// Build the `for` body: the loop body minus the leading break-guard, the
/// counter increment, and a redundant trailing `continue`.
fn build_for_body(body: &[SorobanStmt], counter_idx: u32) -> Vec<SorobanStmt> {
    let name = format!("var_{counter_idx}");
    let mut out: Vec<SorobanStmt> = body
        .iter()
        .enumerate()
        .filter(|(k, s)| {
            if *k == 0 {
                return false; // the break-guard
            }
            // the counter increment
            !matches!(s, SorobanStmt::Assign { target, value }
                if *target == name && increment_step(value, counter_idx).is_some())
        })
        .map(|(_, s)| s.clone())
        .collect();
    if matches!(out.last(), Some(SorobanStmt::Continue)) {
        out.pop();
    }
    out
}

/// Check if a statement list contains a `Break` or `Continue` (but don't recurse
/// into nested loops — those are scoped to the inner loop).
fn stmts_contain_break_or_continue(stmts: &[SorobanStmt]) -> bool {
    stmts.iter().any(stmt_contains_break_or_continue)
}

fn stmt_contains_break_or_continue(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Break | SorobanStmt::Continue => true,
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            stmts_contain_break_or_continue(then_body) || stmts_contain_break_or_continue(else_body)
        }
        SorobanStmt::Match { arms, .. } => arms
            .iter()
            .any(|arm| stmts_contain_break_or_continue(&arm.body)),
        SorobanStmt::Block(body) => stmts_contain_break_or_continue(body),
        SorobanStmt::Loop { .. } => false,
        _ => false,
    }
}

/// Check if a statement list contains a `Continue` (but don't recurse into nested loops).
fn stmts_contain_continue(stmts: &[SorobanStmt]) -> bool {
    stmts.iter().any(stmt_contains_continue)
}

fn stmt_contains_continue(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Continue => true,
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => stmts_contain_continue(then_body) || stmts_contain_continue(else_body),
        SorobanStmt::Match { arms, .. } => arms.iter().any(|arm| stmts_contain_continue(&arm.body)),
        SorobanStmt::Block(body) => stmts_contain_continue(body),
        // Don't recurse into nested loops — continue there doesn't affect the outer loop
        SorobanStmt::Loop { .. } => false,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Remove spurious .get() statements
// ---------------------------------------------------------------------------

/// Remove standalone `.get(N)` method call statements that are XDR unpacking
/// artifacts from SDK-internal validation leaking through inlining.
/// At the function's top level (`nested == false`), keeps `.get()` in tail
/// position (last statement) since it may be an implicit return.
/// In nested bodies (`nested == true`), removes all standalone `.get()` calls
/// since their return values are never used.
fn remove_spurious_get(stmts: Vec<SorobanStmt>, nested: bool) -> Vec<SorobanStmt> {
    let len = stmts.len();
    let mut result = Vec::new();
    for (i, stmt) in stmts.into_iter().enumerate() {
        match stmt {
            // Remove standalone Expr(.get(N)) statements
            SorobanStmt::Expr(SorobanExpr::MethodCall {
                ref method,
                ref args,
                ..
            }) if method == "get" && args.len() == 1 && (nested || i + 1 < len) => {
                // Skip — spurious .get() artifact
            }
            // Recurse into nested bodies (always nested=true for children)
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => result.push(SorobanStmt::If {
                condition,
                then_body: remove_spurious_get(then_body, true),
                else_body: remove_spurious_get(else_body, true),
            }),
            SorobanStmt::Match { scrutinee, arms } => result.push(SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: remove_spurious_get(arm.body, true),
                    })
                    .collect(),
            }),
            SorobanStmt::Loop { body } => result.push(SorobanStmt::Loop {
                body: remove_spurious_get(body, true),
            }),
            SorobanStmt::Block(body) => {
                result.push(SorobanStmt::Block(remove_spurious_get(body, true)));
            }
            other => result.push(other),
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Remove empty match / if statements
// ---------------------------------------------------------------------------

/// Remove match statements where all arms have empty bodies and if/else
/// where both branches are empty.  These are SDK validation artifacts left
/// behind after spurious `.get()`/`.len()` removal clears arm bodies.
fn remove_empty_matches(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::new();
    for stmt in stmts {
        match stmt {
            SorobanStmt::Match {
                ref scrutinee,
                ref arms,
            } if arms.iter().all(|arm| arm.body.is_empty())
                && !expr_has_side_effects(scrutinee) =>
            {
                cov_mark::hit!(empty_match_removed);
                // Skip — all arms empty and scrutinee is side-effect-free
            }
            SorobanStmt::If {
                ref then_body,
                ref else_body,
                ..
            } if then_body.is_empty() && else_body.is_empty() => {
                cov_mark::hit!(empty_match_removed);
                // Skip — both branches empty, if does nothing
            }
            // Recurse into nested bodies
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => result.push(SorobanStmt::If {
                condition,
                then_body: remove_empty_matches(then_body),
                else_body: remove_empty_matches(else_body),
            }),
            SorobanStmt::Match { scrutinee, arms } => result.push(SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: remove_empty_matches(arm.body),
                    })
                    .collect(),
            }),
            SorobanStmt::Loop { body } => result.push(SorobanStmt::Loop {
                body: remove_empty_matches(body),
            }),
            SorobanStmt::Block(body) => {
                result.push(SorobanStmt::Block(remove_empty_matches(body)));
            }
            other => result.push(other),
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Remove orphan host calls / unknown values
// ---------------------------------------------------------------------------

/// Remove standalone `UnknownVal` and discarded-accessor statements.
///
/// These are intermediate computation results whose return values were lost
/// during lifting. As standalone statements they are artifacts, not real code.
///
/// `RawHostCall` is intentionally **kept** here: the sibling predicate
/// `expr_has_side_effects` classifies raw host calls as side-effectful, and
/// silently dropping them would delete real semantically-meaningful calls the
/// lifter failed to recognise. The two predicates must agree.
fn remove_orphan_host_calls(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::new();
    for stmt in stmts {
        match stmt {
            SorobanStmt::Expr(SorobanExpr::UnknownVal)
            // Standalone has() is a pure existence check with result discarded
            // — artifact from lost if-guard whose structure was removed.
            | SorobanStmt::Expr(SorobanExpr::StorageHas { .. }) => {
                cov_mark::hit!(orphan_host_call_removed);
                // Skip — orphan artifact
            }
            // Standalone .id() / .address() calls — pure accessors whose results
            // were lost during lifting (e.g., MuxedAddress::id()).
            SorobanStmt::Expr(SorobanExpr::MethodCall {
                ref method,
                ref args,
                ..
            }) if (method == "id" || method == "address") && args.is_empty() => {
                // Skip — pure accessor artifact
            }
            // Method call on a discarded temporary collection (e.g.
            // `Vec::new(&env).push_back(todo!(...));` where the Vec is
            // created, mutated, and immediately dropped).
            SorobanStmt::Expr(SorobanExpr::MethodCall { ref object, .. })
                if matches!(object.as_ref(), SorobanExpr::CollectionNew(_)) =>
            {
                // Skip — method call on discarded temporary
            }
            // Standalone linear-memory (de)serialization host calls
            // (`map_unpack_to_linear_memory`, `map_new_from_linear_memory`,
            // `vec_*_linear_memory`, …). These are pure SDK marshalling that the
            // lifter could not fold into a typed construction; codegen renders
            // them as non-public `env.map()…` API, so they neither compile nor
            // carry any contract-observable effect the typed Rust does not
            // already express. Only dropped when the result is discarded (a bare
            // expression statement) — a used result lives inside a Let/expr and
            // is left untouched.
            SorobanStmt::Expr(SorobanExpr::RawHostCall { ref function, .. })
                if function.ends_with("_to_linear_memory")
                    || function.ends_with("_from_linear_memory") =>
            {
                cov_mark::hit!(orphan_linear_memory_marshalling_removed);
                // Skip — linear-memory marshalling artifact
            }
            // Recurse into nested bodies
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => result.push(SorobanStmt::If {
                condition,
                then_body: remove_orphan_host_calls(then_body),
                else_body: remove_orphan_host_calls(else_body),
            }),
            SorobanStmt::Match { scrutinee, arms } => result.push(SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: remove_orphan_host_calls(arm.body),
                    })
                    .collect(),
            }),
            SorobanStmt::Loop { body } => result.push(SorobanStmt::Loop {
                body: remove_orphan_host_calls(body),
            }),
            SorobanStmt::Block(body) => {
                result.push(SorobanStmt::Block(remove_orphan_host_calls(body)));
            }
            other => result.push(other),
        }
    }
    result
}

/// Remove standalone `CollectionNew` expressions (e.g., `Vec::new(&env);`)
/// whose results are discarded. These are WASM lifting artifacts — the
/// original code would have captured the collection in a variable.
/// Skips the last statement in the top-level body to preserve tail expressions.
fn remove_standalone_collection_new(stmts: Vec<SorobanStmt>, nested: bool) -> Vec<SorobanStmt> {
    let len = stmts.len();
    let mut result = Vec::new();
    for (i, stmt) in stmts.into_iter().enumerate() {
        match stmt {
            SorobanStmt::Expr(SorobanExpr::CollectionNew(_)) if nested || i + 1 < len => {
                // Skip — orphan collection construction
            }
            // Recurse into nested bodies
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => result.push(SorobanStmt::If {
                condition,
                then_body: remove_standalone_collection_new(then_body, true),
                else_body: remove_standalone_collection_new(else_body, true),
            }),
            SorobanStmt::Match { scrutinee, arms } => result.push(SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: remove_standalone_collection_new(arm.body, true),
                    })
                    .collect(),
            }),
            SorobanStmt::Loop { body } => result.push(SorobanStmt::Loop {
                body: remove_standalone_collection_new(body, true),
            }),
            SorobanStmt::Block(body) => {
                result.push(SorobanStmt::Block(remove_standalone_collection_new(
                    body, true,
                )));
            }
            other => result.push(other),
        }
    }
    result
}

/// Remove duplicate consecutive expressions: when `Expr(e)` is immediately
/// followed by `Expr(e)` or `Return(Some(e))` with the same expression,
/// the first is a lifter artifact whose result was discarded.
/// Recurses into nested bodies.
fn remove_duplicate_exprs(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result: Vec<SorobanStmt> = Vec::new();
    for stmt in stmts {
        let stmt = remove_duplicate_exprs_nested(stmt);
        // Check if current statement's expression duplicates or subsumes
        // the previous standalone Expr.
        let curr_expr = match &stmt {
            SorobanStmt::Expr(e) => Some(e),
            SorobanStmt::Return(Some(e)) => Some(e),
            SorobanStmt::Let { value: e, .. } => Some(e),
            _ => None,
        };
        if let Some(curr) = curr_expr
            && let Some(SorobanStmt::Expr(prev)) = result.last()
        {
            // Remove previous standalone Expr if:
            // 1. It's identical to current expression, OR
            // 2. It appears as a subexpression within current expression
            //    (lifter artifact: result stored in local, then inlined)
            if expr_contains(curr, prev) {
                cov_mark::hit!(duplicate_expr_removed);
                result.pop();
            }
        }
        result.push(stmt);
    }
    result
}

/// Check if `needle` appears anywhere within `haystack` (including at root).
fn expr_contains(haystack: &SorobanExpr, needle: &SorobanExpr) -> bool {
    if haystack == needle {
        return true;
    }
    let c = |e: &SorobanExpr| expr_contains(e, needle);
    let cv = |v: &[SorobanExpr]| v.iter().any(&c);
    match haystack {
        // Leaf nodes — no children
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
        | SorobanExpr::Panic
        | SorobanExpr::LedgerSequence
        | SorobanExpr::LedgerTimestamp
        | SorobanExpr::LedgerNetworkId
        | SorobanExpr::CurrentContractAddress
        | SorobanExpr::MaxLiveUntilLedger
        | SorobanExpr::CollectionNew(_)
        | SorobanExpr::UnknownVal
        | SorobanExpr::CyclicSlot { .. }
        | SorobanExpr::ValTagName(_)
        | SorobanExpr::ContractError { .. } => false,

        // One child (Box)
        SorobanExpr::Not(e)
        | SorobanExpr::RequireAuth(e)
        | SorobanExpr::AuthorizeAsCurrContract(e)
        | SorobanExpr::ErrorFromCode(e)
        | SorobanExpr::PanicWithError(e)
        | SorobanExpr::CryptoSha256(e)
        | SorobanExpr::CryptoKeccak256(e)
        | SorobanExpr::PrngReseed(e)
        | SorobanExpr::PrngBytesNew(e)
        | SorobanExpr::PrngVecShuffle(e)
        | SorobanExpr::StrkeyToAddress(e)
        | SorobanExpr::AddressToStrkey(e)
        | SorobanExpr::ValTag(e)
        | SorobanExpr::Some(e)
        | SorobanExpr::SretResult(e) => c(e),

        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => c(value),
        SorobanExpr::FieldAccess { object, .. } => c(object),
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => c(key),

        // Two children
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
        | SorobanExpr::Or(a, b) => c(a) || c(b),

        SorobanExpr::StorageSet { key, value, .. } => c(key) || c(value),
        SorobanExpr::RequireAuthForArgs { address, args } => c(address) || c(args),
        SorobanExpr::PrngU64InRange { low, high } => c(low) || c(high),
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => c(threshold) || c(extend_to),

        // Three children
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => c(public_key) || c(message) || c(signature),
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => c(msg_digest) || c(signature) || c(recovery_id),
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => c(key) || c(threshold) || c(extend_to),

        // Object + args
        SorobanExpr::MethodCall { object, args, .. } => c(object) || cv(args),
        SorobanExpr::VecTryIterFold { vec, init } => c(vec) || c(init),
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
        } => c(address) || c(function) || cv(args),

        // Vec children
        SorobanExpr::TupleConstruct(fields)
        | SorobanExpr::VecConstruct(fields)
        | SorobanExpr::Log(fields)
        | SorobanExpr::EnumConstruct { fields, .. } => cv(fields),

        SorobanExpr::RawHostCall { args, .. } => cv(args),
        SorobanExpr::PublishEvent { topics, data, .. } => cv(topics) || c(data),
        SorobanExpr::StructConstruct { fields, .. } => fields.iter().any(|(_, e)| c(e)),
        SorobanExpr::MapConstruct(pairs) => pairs.iter().any(|(k, v)| c(k) || c(v)),
    }
}

fn remove_duplicate_exprs_nested(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: remove_duplicate_exprs(then_body),
            else_body: remove_duplicate_exprs(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: remove_duplicate_exprs(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: remove_duplicate_exprs(body),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(remove_duplicate_exprs(body)),
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Constant condition folding
// ---------------------------------------------------------------------------

fn is_constant_false(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::I32Literal(0) | SorobanExpr::I64Literal(0) | SorobanExpr::BoolLiteral(false)
    )
}

fn is_constant_true(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::I32Literal(v) => *v != 0,
        SorobanExpr::I64Literal(v) => *v != 0,
        SorobanExpr::BoolLiteral(v) => *v,
        _ => false,
    }
}

/// Fold `if` statements with constant conditions: `if 0 { body }` → drop,
/// `if 1 { body }` → inline body. Operates at statement-list level because
/// folding may produce 0 or N statements.
fn fold_constant_conditions(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::new();
    for stmt in stmts {
        match stmt {
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                if is_constant_false(&condition) {
                    cov_mark::hit!(constant_condition_folded);
                    // Dead branch → inline else_body (or drop if empty)
                    result.extend(fold_constant_conditions(else_body));
                } else if is_constant_true(&condition) {
                    cov_mark::hit!(constant_condition_folded);
                    // Always true → inline then_body
                    result.extend(fold_constant_conditions(then_body));
                } else {
                    result.push(SorobanStmt::If {
                        condition,
                        then_body: fold_constant_conditions(then_body),
                        else_body: fold_constant_conditions(else_body),
                    });
                }
            }
            SorobanStmt::Loop { body } => {
                result.push(SorobanStmt::Loop {
                    body: fold_constant_conditions(body),
                });
            }
            SorobanStmt::Match { scrutinee, arms } => {
                result.push(SorobanStmt::Match {
                    scrutinee,
                    arms: arms
                        .into_iter()
                        .map(|arm| MatchArm {
                            pattern: arm.pattern,
                            body: fold_constant_conditions(arm.body),
                        })
                        .collect(),
                });
            }
            SorobanStmt::Block(body) => {
                result.push(SorobanStmt::Block(fold_constant_conditions(body)));
            }
            other => result.push(other),
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Constant-scrutinee match folding
// ---------------------------------------------------------------------------

/// When a `match` scrutinee is a literal constant, find the matching arm and
/// inline its body, discarding all unreachable arms.
///
/// Example: `match 0 { 0 => { useful }, 1 => { dead }, _ => { dead } }`
/// becomes just `useful`.
fn fold_constant_matches(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::new();
    for stmt in stmts {
        match stmt {
            SorobanStmt::Match { scrutinee, arms } => {
                // Guard against the lifter's `I32Literal(0)` sentinel for
                // untracked stack values. If the scrutinee is exactly that
                // sentinel and the match arms include any enum-variant
                // pattern, this is almost certainly an enum dispatch whose
                // scrutinee the lifter failed to compute — folding to a
                // wildcard arm would silently delete the real variant code.
                // Mirror the guard `try_fold_literal_cmp` uses for the same
                // sentinel.
                let scrut_is_sentinel = matches!(&scrutinee, SorobanExpr::I32Literal(0));
                let has_enum_arm = arms
                    .iter()
                    .any(|arm| matches!(arm.pattern, MatchPattern::EnumVariant { .. }));
                if scrut_is_sentinel && has_enum_arm {
                    result.push(SorobanStmt::Match {
                        scrutinee,
                        arms: arms
                            .into_iter()
                            .map(|arm| MatchArm {
                                pattern: arm.pattern,
                                body: fold_constant_matches(arm.body),
                            })
                            .collect(),
                    });
                    continue;
                }
                // Evaluate the scrutinee. For non-enum dispatch (the inlined
                // `br_table` vec-builders in aquarius/blend, whose arms are all
                // `Literal` patterns), fold constant *arithmetic* selectors like
                // `i64(2) - i32(1)` that `fold_expr`'s same-type arms leave intact.
                // For enum dispatch keep the conservative bare-literal evaluation —
                // an enum scrutinee is a runtime discriminant, never a folded const,
                // so never strip its arms on a fabricated constant.
                let scrutinee_eval = if has_enum_arm {
                    as_literal_i128(&scrutinee)
                } else {
                    const_eval_i128(&scrutinee)
                };
                if let Some(scrutinee_val) = scrutinee_eval {
                    // Find the arm whose literal pattern matches the scrutinee
                    let matching_arm = arms.iter().position(|arm| {
                        if let MatchPattern::Literal(ref lit) = arm.pattern {
                            as_literal_i128(lit) == Some(scrutinee_val)
                        } else {
                            false
                        }
                    });
                    if let Some(idx) = matching_arm {
                        // Inline the matching arm's body
                        let body = arms.into_iter().nth(idx).unwrap().body;
                        result.extend(fold_constant_matches(body));
                    } else {
                        // No literal match — try wildcard fallback
                        let wildcard = arms
                            .iter()
                            .position(|arm| matches!(arm.pattern, MatchPattern::Wildcard));
                        if let Some(idx) = wildcard {
                            let body = arms.into_iter().nth(idx).unwrap().body;
                            result.extend(fold_constant_matches(body));
                        } else {
                            // No match at all — keep as-is (shouldn't happen in practice)
                            result.push(SorobanStmt::Match {
                                scrutinee,
                                arms: arms
                                    .into_iter()
                                    .map(|arm| MatchArm {
                                        pattern: arm.pattern,
                                        body: fold_constant_matches(arm.body),
                                    })
                                    .collect(),
                            });
                        }
                    }
                } else {
                    // Non-constant scrutinee — recurse into arm bodies
                    result.push(SorobanStmt::Match {
                        scrutinee,
                        arms: arms
                            .into_iter()
                            .map(|arm| MatchArm {
                                pattern: arm.pattern,
                                body: fold_constant_matches(arm.body),
                            })
                            .collect(),
                    });
                }
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                result.push(SorobanStmt::If {
                    condition,
                    then_body: fold_constant_matches(then_body),
                    else_body: fold_constant_matches(else_body),
                });
            }
            SorobanStmt::Loop { body } => {
                result.push(SorobanStmt::Loop {
                    body: fold_constant_matches(body),
                });
            }
            SorobanStmt::Block(body) => {
                result.push(SorobanStmt::Block(fold_constant_matches(body)));
            }
            other => result.push(other),
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Storage has/get pattern folding
// ---------------------------------------------------------------------------

/// Detect `has(key); if has(key) { get(key).unwrap() }` and simplify to
/// `storage().get(&key)` (without `.unwrap()`), returning `Option<T>`.
///
/// This handles the common SDK pattern where `storage().get()` compiles to:
///   has_contract_data(key, type);
///   if has_contract_data(key, type) { get_contract_data(key, type).unwrap() }
/// The original source was just `storage().get(&key)` returning `Option<T>`.
/// Check whether any statement in the slice contains a `Param(...)` reference,
/// indicating real user code rather than artifact struct reconstructions from
/// `map_unpack_to_linear_memory`.
fn stmts_contain_param_ref(stmts: &[SorobanStmt]) -> bool {
    stmts.iter().any(stmt_contains_param)
}

fn stmt_contains_param(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Expr(e)
        | SorobanStmt::Let { value: e, .. }
        | SorobanStmt::Assign { value: e, .. } => expr_contains_param(e),
        SorobanStmt::Return(Some(e)) => expr_contains_param(e),
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            expr_contains_param(condition)
                || stmts_contain_param_ref(then_body)
                || stmts_contain_param_ref(else_body)
        }
        SorobanStmt::Match { scrutinee, arms } => {
            expr_contains_param(scrutinee)
                || arms.iter().any(|arm| stmts_contain_param_ref(&arm.body))
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => stmts_contain_param_ref(body),
        _ => false,
    }
}

fn expr_contains_param(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::Param(_) => true,
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
        | SorobanExpr::Or(a, b) => expr_contains_param(a) || expr_contains_param(b),
        SorobanExpr::Not(a)
        | SorobanExpr::RequireAuth(a)
        | SorobanExpr::AuthorizeAsCurrContract(a)
        | SorobanExpr::PanicWithError(a)
        | SorobanExpr::PrngReseed(a)
        | SorobanExpr::PrngBytesNew(a)
        | SorobanExpr::PrngVecShuffle(a)
        | SorobanExpr::StrkeyToAddress(a)
        | SorobanExpr::AddressToStrkey(a)
        | SorobanExpr::ErrorFromCode(a)
        | SorobanExpr::CryptoSha256(a)
        | SorobanExpr::CryptoKeccak256(a) => expr_contains_param(a),
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            expr_contains_param(value)
        }
        SorobanExpr::FieldAccess { object, .. } => expr_contains_param(object),
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => expr_contains_param(key),
        SorobanExpr::StorageSet { key, value, .. } => {
            expr_contains_param(key) || expr_contains_param(value)
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            expr_contains_param(key)
                || expr_contains_param(threshold)
                || expr_contains_param(extend_to)
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => expr_contains_param(threshold) || expr_contains_param(extend_to),
        SorobanExpr::RequireAuthForArgs { address, args } => {
            expr_contains_param(address) || expr_contains_param(args)
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            topics.iter().any(expr_contains_param) || expr_contains_param(data)
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
            expr_contains_param(address)
                || expr_contains_param(function)
                || args.iter().any(expr_contains_param)
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            fields.iter().any(|(_, v)| expr_contains_param(v))
        }
        SorobanExpr::EnumConstruct { fields, .. } => fields.iter().any(expr_contains_param),
        SorobanExpr::TupleConstruct(items) | SorobanExpr::VecConstruct(items) => {
            items.iter().any(expr_contains_param)
        }
        SorobanExpr::MapConstruct(pairs) => pairs
            .iter()
            .any(|(k, v)| expr_contains_param(k) || expr_contains_param(v)),
        SorobanExpr::MethodCall { object, args, .. } => {
            expr_contains_param(object) || args.iter().any(expr_contains_param)
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            expr_contains_param(public_key)
                || expr_contains_param(message)
                || expr_contains_param(signature)
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            expr_contains_param(msg_digest)
                || expr_contains_param(signature)
                || expr_contains_param(recovery_id)
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            expr_contains_param(low) || expr_contains_param(high)
        }
        SorobanExpr::Log(args) | SorobanExpr::RawHostCall { args, .. } => {
            args.iter().any(expr_contains_param)
        }
        _ => false,
    }
}

fn fold_has_get_pattern(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::new();
    let mut i = 0;
    while i < stmts.len() {
        if i + 1 < stmts.len()
            && let Some(folded) = try_fold_has_get(&stmts[i], &stmts[i + 1])
        {
            cov_mark::hit!(fold_has_get_merged);
            result.push(SorobanStmt::Expr(folded));
            i += 2;
            continue;
        }
        // Single-statement fold: If { condition: StorageHas, body: [...], else: [] }
        // Handles the common case where the lifter produces has() only as the If
        // condition (no standalone Expr(StorageHas)), so the pair-based fold above
        // doesn't fire.
        // Two sub-patterns:
        //   [StorageGet] or [Let { StorageGet }] → fold to StorageGet (keeping unwrap)
        //   [Panic] → fold to StorageGet { unwrap: true } (inverted unwrap check)
        if let SorobanStmt::If {
            condition:
                SorobanExpr::StorageHas {
                    storage_type,
                    key: has_key,
                },
            then_body,
            else_body,
        } = &stmts[i]
        {
            if else_body.is_empty() && then_body.len() == 1 {
                // Pattern 1: body is [StorageGet] or [Let { StorageGet }]
                let get_expr = match &then_body[0] {
                    SorobanStmt::Expr(e @ SorobanExpr::StorageGet { .. }) => Some(e),
                    SorobanStmt::Let {
                        value: e @ SorobanExpr::StorageGet { .. },
                        ..
                    } => Some(e),
                    _ => Option::None,
                };
                if let Some(SorobanExpr::StorageGet {
                    storage_type: get_st,
                    key: get_key,
                    unwrap,
                }) = get_expr
                    && get_st == storage_type
                    && get_key.as_ref() == has_key.as_ref()
                {
                    cov_mark::hit!(fold_has_get_merged);
                    result.push(SorobanStmt::Expr(SorobanExpr::StorageGet {
                        storage_type: *get_st,
                        key: get_key.clone(),
                        unwrap: *unwrap,
                    }));
                    i += 1;
                    continue;
                }
                // Pattern 2: body is [Panic] — inverted unwrap check.
                // The structurizer put the error path (panic) in the then-body
                // and lost the success path (get). Replace with get().unwrap()
                // which panics if key missing (same semantics).
                if matches!(&then_body[0], SorobanStmt::Expr(SorobanExpr::Panic)) {
                    cov_mark::hit!(fold_has_get_merged);
                    result.push(SorobanStmt::Expr(SorobanExpr::StorageGet {
                        storage_type: *storage_type,
                        key: has_key.clone(),
                        unwrap: true,
                    }));
                    i += 1;
                    continue;
                }
            }
            // Pattern 3: body ends with Panic and contains StorageGet + artifact
            // host calls (map_unpack, etc.). This is the same inverted unwrap pattern
            // but with inlined struct deserialization calls that get stripped later.
            // The real logic was in the success path (lost by structurizer).
            if else_body.is_empty()
                && !then_body.is_empty()
                && matches!(
                    then_body.last(),
                    Some(SorobanStmt::Expr(SorobanExpr::Panic))
                )
            {
                // Check that all non-Panic statements are either StorageGet or
                // RawHostCall artifacts (map_unpack, etc.) — no real user logic.
                let all_artifacts = then_body[..then_body.len() - 1].iter().all(|s| {
                    matches!(
                        s,
                        SorobanStmt::Expr(SorobanExpr::StorageGet { .. })
                            | SorobanStmt::Expr(SorobanExpr::RawHostCall { .. })
                            | SorobanStmt::Let {
                                value: SorobanExpr::StorageGet { .. },
                                ..
                            }
                    )
                });
                if all_artifacts {
                    cov_mark::hit!(fold_has_get_merged);
                    result.push(SorobanStmt::Expr(SorobanExpr::StorageGet {
                        storage_type: *storage_type,
                        key: has_key.clone(),
                        unwrap: true,
                    }));
                    i += 1;
                    // The validation preamble often has a trailing Expr(Panic) as the
                    // else-fallthrough (WASM `unreachable` after the if-else block).
                    // Since the folded get().unwrap() already panics on missing key,
                    // this trailing panic is redundant and would cause remove_dead_code
                    // to truncate the real function body after it.
                    // Only consume the panic when the remaining stmts contain Param
                    // references, indicating real user code follows. When no Param
                    // references exist, the code after the panic is artifact struct
                    // reconstruction from map_unpack_to_linear_memory that should
                    // be blocked by remove_dead_code.
                    if i < stmts.len()
                        && matches!(&stmts[i], SorobanStmt::Expr(SorobanExpr::Panic))
                        && i + 1 < stmts.len()
                        && stmts_contain_param_ref(&stmts[i + 1..])
                    {
                        i += 1;
                    }
                    continue;
                }
            }
        }
        // Recurse into nested structures
        let stmt = match stmts[i].clone() {
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => SorobanStmt::If {
                condition,
                then_body: fold_has_get_pattern(then_body),
                else_body: fold_has_get_pattern(else_body),
            },
            SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: fold_has_get_pattern(arm.body),
                    })
                    .collect(),
            },
            SorobanStmt::Loop { body } => SorobanStmt::Loop {
                body: fold_has_get_pattern(body),
            },
            SorobanStmt::Block(body) => SorobanStmt::Block(fold_has_get_pattern(body)),
            other => other,
        };
        result.push(stmt);
        i += 1;
    }
    result
}

/// Try to fold a `Expr(has(key)); If(has(key), [get(key)], [])` pair into `get(key)`.
fn try_fold_has_get(first: &SorobanStmt, second: &SorobanStmt) -> Option<SorobanExpr> {
    let SorobanStmt::Expr(SorobanExpr::StorageHas {
        storage_type: st1,
        key: key1,
    }) = first
    else {
        return None;
    };
    let SorobanStmt::If {
        condition:
            SorobanExpr::StorageHas {
                storage_type: st2,
                key: key2,
            },
        then_body,
        else_body,
    } = second
    else {
        return None;
    };
    if st1 != st2 || key1 != key2 || !else_body.is_empty() {
        return None;
    }
    extract_storage_get_without_unwrap(then_body, st1, key1)
}

/// Check if a body is `[Expr(StorageGet { same key/type })]` and return a
/// `StorageGet { unwrap: false }` that codegen will emit WITHOUT `.unwrap()`.
fn extract_storage_get_without_unwrap(
    body: &[SorobanStmt],
    expected_st: &StorageType,
    expected_key: &SorobanExpr,
) -> Option<SorobanExpr> {
    if body.len() != 1 {
        return None;
    }
    if let SorobanStmt::Expr(SorobanExpr::StorageGet {
        storage_type, key, ..
    }) = &body[0]
        && storage_type == expected_st
        && key.as_ref() == expected_key
    {
        return Some(SorobanExpr::StorageGet {
            storage_type: *storage_type,
            key: key.clone(),
            unwrap: false,
        });
    }
    None
}

/// Remove unreachable statements after terminators.
/// At the top level, uses an extended check that includes infinite loops as terminators.
/// Nested bodies use the standard check (panic/return only) via remove_dead_code_stmt.
fn remove_dead_code(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::new();
    let total = stmts.len();
    for (i, stmt) in stmts.into_iter().enumerate() {
        let is_terminator = is_strong_terminator_stmt(&stmt);
        result.push(remove_dead_code_stmt(stmt));
        if is_terminator {
            if i + 1 < total {
                cov_mark::hit!(dead_code_removed);
            }
            break;
        }
    }
    result
}

fn truncate_after_terminator(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::new();
    for stmt in stmts {
        let is_terminator = is_terminator_stmt(&stmt);
        result.push(remove_dead_code_stmt(stmt));
        if is_terminator {
            break;
        }
    }
    result
}

/// Basic terminator check for nested bodies: panic/return only (plus if/match
/// where all branches diverge).
/// Note: Break/Continue are NOT included here because the structurizer
/// sometimes places useful code after break in loop bodies (code that
/// would execute after the loop but is structurally inside it).
fn is_terminator_stmt(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_)) => true,
        SorobanStmt::Return(_) => true,
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            !else_body.is_empty()
                && then_body.iter().any(is_terminator_stmt)
                && else_body.iter().any(is_terminator_stmt)
        }
        SorobanStmt::Match { arms, .. } => {
            !arms.is_empty()
                && arms
                    .iter()
                    .all(|arm| arm.body.iter().any(is_terminator_stmt))
        }
        _ => false,
    }
}

/// Extended terminator check for top-level: includes infinite loops (no break),
/// if/else where both branches diverge, and match where all arms diverge.
fn is_strong_terminator_stmt(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_)) => true,
        SorobanStmt::Return(_) => true,
        // Infinite loops (no break) are terminators — code after them is dead
        SorobanStmt::Loop { body } => !stmts_contain_break(body),
        // If/else where both branches always diverge
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            !else_body.is_empty()
                && then_body.iter().any(is_strong_terminator_stmt)
                && else_body.iter().any(is_strong_terminator_stmt)
        }
        // Match where all arms always diverge
        SorobanStmt::Match { arms, .. } => {
            !arms.is_empty()
                && arms
                    .iter()
                    .all(|arm| arm.body.iter().any(is_strong_terminator_stmt))
        }
        _ => false,
    }
}

/// Issue #12 backstop: drop a STRAY standalone top-level panic that is followed
/// by real continuation, so `remove_dead_code` does not discard the live body.
///
/// An inlined VOID validation helper (e.g. aquarius `estimate_swap`'s token-sort
/// check) lifts its `fail_with_error; unreachable` error exits to standalone
/// `Expr(PanicWithError)` / `Expr(Panic)` statements that splice into the
/// caller's top level. They sit *between* the validation guard and the real
/// logic, so `remove_dead_code` treats the first as a strong terminator and
/// drops the rest of the function (the issue-#12 truncation).
///
/// Codegen cannot legally emit code after a `-> !` panic, so such a stray panic
/// is a pure artifact: remove only that statement and keep the continuation.
/// TOP-LEVEL ONLY — a panic nested inside an if/match arm is a real conditional
/// error exit and is left untouched (the truncation is exclusively top-level,
/// since `remove_dead_code` only breaks on top-level strong terminators).
fn drop_stray_panic_before_continuation(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let len = stmts.len();
    if len < 2 {
        return stmts;
    }
    // suffix_has_real[i] = does any stmt at index >= i carry real continuation?
    // The two strays are consecutive, so a stray panic's live continuation can
    // sit *past* the next stray panic — scan the whole tail, not just i+1.
    let mut suffix_has_real = vec![false; len + 1];
    for i in (0..len).rev() {
        suffix_has_real[i] = suffix_has_real[i + 1] || stmt_is_real_continuation(&stmts[i]);
    }
    let mut result = Vec::with_capacity(len);
    for (i, stmt) in stmts.into_iter().enumerate() {
        let is_standalone_panic = matches!(
            &stmt,
            SorobanStmt::Expr(SorobanExpr::Panic | SorobanExpr::PanicWithError(_))
        );
        if is_standalone_panic && suffix_has_real[i + 1] {
            cov_mark::hit!(stray_panic_before_continuation_dropped);
            continue;
        }
        result.push(stmt);
    }
    result
}

/// A statement that represents live work the function must perform. Used by
/// [`drop_stray_panic_before_continuation`] to decide that a preceding standalone
/// top-level panic is a stray inlined-helper artifact rather than a real
/// terminator. Bindings, assignments, returns, and control flow are always live;
/// a bare `Expr` counts only when it has an observable side effect (a host call).
fn stmt_is_real_continuation(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Let { .. }
        | SorobanStmt::Assign { .. }
        | SorobanStmt::Return(_)
        | SorobanStmt::If { .. }
        | SorobanStmt::Match { .. }
        | SorobanStmt::Loop { .. }
        | SorobanStmt::For { .. }
        | SorobanStmt::Block(_) => true,
        SorobanStmt::Expr(e) => expr_has_side_effects(e),
        SorobanStmt::Comment(_) | SorobanStmt::Break | SorobanStmt::Continue => false,
    }
}

/// Check if a statement list contains a `Break` (but don't recurse into nested loops,
/// since a break inside a nested loop doesn't break the outer one).
fn stmts_contain_break(stmts: &[SorobanStmt]) -> bool {
    stmts.iter().any(stmt_contains_break)
}

fn stmt_contains_break(stmt: &SorobanStmt) -> bool {
    match stmt {
        SorobanStmt::Break => true,
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => stmts_contain_break(then_body) || stmts_contain_break(else_body),
        SorobanStmt::Match { arms, .. } => arms.iter().any(|arm| stmts_contain_break(&arm.body)),
        SorobanStmt::Block(body) => stmts_contain_break(body),
        // Don't recurse into nested loops — break there doesn't affect the outer loop
        SorobanStmt::Loop { .. } => false,
        _ => false,
    }
}

fn remove_dead_code_stmt(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: truncate_after_terminator(then_body),
            else_body: truncate_after_terminator(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: truncate_after_terminator(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: truncate_after_terminator(body),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(truncate_after_terminator(body)),
        other => other,
    }
}

/// Guard clause inversion: `if C { return } ; <stmts>` becomes `if !C { <stmts> }`.
///
/// Eliminates early-return guards that obscure the actual conditional logic.
/// This transforms `if a >= b { return }; panic!()` into `if a < b { panic!() }`.
fn invert_guard_clauses(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    // First recurse into nested bodies
    let stmts: Vec<SorobanStmt> = stmts.into_iter().map(invert_guard_clauses_nested).collect();
    // Then apply guard clause inversion at this level
    let mut result = Vec::new();
    let mut i = 0;
    while i < stmts.len() {
        if let SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } = &stmts[i]
        {
            if else_body.is_empty()
                && matches!(then_body.as_slice(), [SorobanStmt::Return(None)])
                && i + 1 < stmts.len()
            {
                cov_mark::hit!(guard_clause_inverted);
                let tail: Vec<SorobanStmt> = stmts[i + 1..].to_vec();
                let negated = fold_expr(SorobanExpr::Not(Box::new(condition.clone())));
                result.push(SorobanStmt::If {
                    condition: negated,
                    then_body: tail,
                    else_body: Vec::new(),
                });
                return result;
            }

            // Panic guard inversion: `if !(cond) { panic!() }` → `if cond { panic!() }`
            // The lifter's BrIf handler creates `if Not(guard) { body }` which the
            // constant folder simplifies to inverted comparisons (Gt → Le, Lt → Ge).
            // When the body is just panic, invert the condition back for readability.
            // Check if body starts with panic — the body may have dead code after
            // the panic that hasn't been truncated yet (remove_dead_code runs later).
            let is_panic_body = matches!(
                then_body.first(),
                Some(SorobanStmt::Expr(
                    SorobanExpr::Panic | SorobanExpr::PanicWithError(_)
                ))
            );
            if else_body.is_empty() && is_panic_body && is_inverted_comparison(condition) {
                let inverted = invert_comparison(condition.clone());
                result.push(SorobanStmt::If {
                    condition: inverted,
                    then_body: then_body.clone(),
                    else_body: Vec::new(),
                });
                i += 1;
                continue;
            }
        }
        result.push(stmts[i].clone());
        i += 1;
    }
    result
}

/// Check if a comparison is the "inverted" form from the BrIf handler's negation.
/// Le/Ge are less natural than Gt/Lt for panic guards (e.g., `len <= 10` vs `len > 10`).
/// Not(Gt/Lt/Ge/Le) is an explicit negation wrapper.
fn is_inverted_comparison(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::Le(_, _) | SorobanExpr::Ge(_, _) => true,
        SorobanExpr::Not(inner) => matches!(
            inner.as_ref(),
            SorobanExpr::Gt(_, _)
                | SorobanExpr::Lt(_, _)
                | SorobanExpr::Ge(_, _)
                | SorobanExpr::Le(_, _)
        ),
        _ => false,
    }
}

/// Invert a comparison: Le ↔ Gt, Ge ↔ Lt, Not(X) → X.
fn invert_comparison(expr: SorobanExpr) -> SorobanExpr {
    match expr {
        SorobanExpr::Le(a, b) => SorobanExpr::Gt(a, b),
        SorobanExpr::Ge(a, b) => SorobanExpr::Lt(a, b),
        SorobanExpr::Not(inner) => *inner,
        other => other,
    }
}

fn invert_guard_clauses_nested(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: invert_guard_clauses(then_body),
            else_body: invert_guard_clauses(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: invert_guard_clauses(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: invert_guard_clauses(body),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(invert_guard_clauses(body)),
        other => other,
    }
}

/// Remove SDK-generated argument tag-validation guards of the shape
/// `if <val>.get_tag() != Tag::<Name> { panic!() }`.
///
/// The Soroban SDK emits these to assert that an incoming `Val` argument carries
/// the expected tag before decoding it into the typed parameter. They are
/// marshalling boilerplate, not contract logic — the typed parameter
/// (`v: Address`, `arg: (u32, i64)`, …) already implies the check. Crucially,
/// `Val::get_tag()` and `Tag` are **not** part of the public `soroban_sdk`
/// surface, so the lifter's `ValTag`/`ValTagName` recovery (issue #4) surfaces
/// code that does not compile. Stripping these guards both restores
/// compilability and matches the canonical SDK source (which never contains
/// them — the SDK re-inserts the marshalling when the typed contract is rebuilt).
fn remove_val_tag_guards(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    stmts
        .into_iter()
        .filter_map(|stmt| match stmt {
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } if else_body.is_empty()
                && is_val_tag_guard_condition(&condition)
                && is_panic_body(&then_body) =>
            {
                None
            }
            // SDK `Val -> T` type-assertion husk whose tag-of operand collapsed to
            // `UnknownVal` (rendered `if todo!() != 69 { panic!() }`): the operand
            // is unrecovered but the constant is a genuine non-boolean `Val` type
            // tag and the body is a bare `panic!()`, so it is unambiguously the
            // inlined type check, not user logic. Drop it.
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } if else_body.is_empty()
                && is_unknown_val_type_tag_assert(&condition)
                && is_bare_panic_body(&then_body) =>
            {
                None
            }
            other => Some(remove_val_tag_guards_nested(other)),
        })
        .collect()
}

/// True when `expr` is an (optionally negated) equality/inequality comparison
/// against a recovered `Val` tag (`ValTag` / `ValTagName`).
fn is_val_tag_guard_condition(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::Not(inner) => is_val_tag_guard_condition(inner),
        SorobanExpr::Eq(a, b) | SorobanExpr::Ne(a, b) => is_val_tag_expr(a) || is_val_tag_expr(b),
        _ => false,
    }
}

fn is_val_tag_expr(expr: &SorobanExpr) -> bool {
    matches!(expr, SorobanExpr::ValTag(_) | SorobanExpr::ValTagName(_))
}

/// True when a guard body begins with a panic (any trailing statements are dead
/// code that later passes truncate).
fn is_panic_body(body: &[SorobanStmt]) -> bool {
    matches!(
        body.first(),
        Some(SorobanStmt::Expr(
            SorobanExpr::Panic | SorobanExpr::PanicWithError(_)
        ))
    )
}

/// True when a guard body is a bare `panic!()` (no error code). The SDK's
/// `Val -> T` runtime type check traps with a plain `panic!()`/`unreachable`;
/// user code raises a `panic_with_error!`, so requiring the bare form keeps the
/// husk recognizer from swallowing genuine error guards.
fn is_bare_panic_body(body: &[SorobanStmt]) -> bool {
    matches!(body.first(), Some(SorobanStmt::Expr(SorobanExpr::Panic)))
}

/// A genuine `Val` *type* tag — the small-value tags (`U32`..`SymbolSmall`) and
/// the object tags (`U64Object`..`MuxedAddressObject`). Excludes the ambiguous
/// `False`/`True`/`Void`/`Error` tags (0..=3), whose small constants routinely
/// appear in real comparisons and must not be mistaken for type checks.
fn is_genuine_val_type_tag(tag: i64) -> bool {
    matches!(tag, 4..=14 | 64..=78)
}

/// The concrete Rust type the SDK decodes a `Val` type tag into, when it is
/// unambiguous from the tag alone. Aggregate/parametric tags (Vec/Map/Bytes,
/// U256/I256, Timepoint/Duration) return `None`: their element type or length is
/// not recoverable from the tag, so the invoke stays `Val`-typed.
fn val_tag_rust_type(tag: i64) -> Option<&'static str> {
    Some(match tag {
        4 => "u32",
        5 => "i32",
        6 | 64 => "u64",
        7 | 65 => "i64",
        10 | 68 => "u128",
        11 | 69 => "i128",
        14 | 74 => "Symbol",
        73 => "String",
        77 => "Address",
        _ => return None,
    })
}

/// True when `expr` compares an unrecovered `UnknownVal` against a genuine `Val`
/// type-tag constant (either operand order, optionally negated) — the shape the
/// SDK's inlined `Val -> T` type assertion lifts to when its tag-of operand was
/// lost. Returns the tag via [`unknown_val_type_tag_assert_tag`] for callers
/// that need the tag itself.
fn is_unknown_val_type_tag_assert(expr: &SorobanExpr) -> bool {
    unknown_val_type_tag_assert_tag(expr).is_some()
}

/// The type tag from an `UnknownVal <cmp> <type-tag>` assertion, or `None`.
fn unknown_val_type_tag_assert_tag(expr: &SorobanExpr) -> Option<i64> {
    let (a, b) = match expr {
        SorobanExpr::Not(inner) => return unknown_val_type_tag_assert_tag(inner),
        SorobanExpr::Eq(a, b) | SorobanExpr::Ne(a, b) => (a.as_ref(), b.as_ref()),
        _ => return None,
    };
    let tag = match (a, b) {
        (SorobanExpr::UnknownVal, other) | (other, SorobanExpr::UnknownVal) => expr_as_int(other)?,
        _ => return None,
    };
    is_genuine_val_type_tag(tag).then_some(tag)
}

/// Recover the generic return type of an `invoke_contract` whose result feeds
/// directly into the SDK's `Val -> T` type-assertion husk on the next statement.
///
/// The lifter leaves the assertion as `if todo!() <cmp> <tag> { panic!() }` with
/// the tag-of operand collapsed to `UnknownVal`, but the constant tag still names
/// the type the SDK decoded the result into. When that type is unambiguous we set
/// it as the invoke's `return_type` (so codegen emits `invoke_contract::<i128>`
/// rather than `::<Val>`); the husk itself is dropped afterwards by
/// `remove_val_tag_guards`. Only fires when the husk is the immediately following
/// statement, matching the SDK's emit order, and never overwrites an already
/// recovered return type.
fn recover_invoke_return_types(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut stmts: Vec<SorobanStmt> = stmts
        .into_iter()
        .map(recover_invoke_return_types_nested)
        .collect();
    for i in 0..stmts.len().saturating_sub(1) {
        let Some(tag) = stmt_as_type_tag_husk(&stmts[i + 1]) else {
            continue;
        };
        let Some(ty) = val_tag_rust_type(tag) else {
            continue;
        };
        if let Some(rt) = stmt_invoke_return_type_mut(&mut stmts[i])
            && rt.is_none()
        {
            *rt = Some(ty.to_string());
        }
    }
    stmts
}

/// The type tag of a bare-`panic!()` `UnknownVal <cmp> <type-tag>` husk statement.
fn stmt_as_type_tag_husk(stmt: &SorobanStmt) -> Option<i64> {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } if else_body.is_empty() && is_bare_panic_body(then_body) => {
            unknown_val_type_tag_assert_tag(condition)
        }
        _ => None,
    }
}

/// A mutable handle to the `return_type` of an `invoke_contract` directly held by
/// a statement (bare expression, `let`, or assignment), or `None`.
fn stmt_invoke_return_type_mut(stmt: &mut SorobanStmt) -> Option<&mut Option<String>> {
    let expr = match stmt {
        SorobanStmt::Expr(e)
        | SorobanStmt::Let { value: e, .. }
        | SorobanStmt::Assign { value: e, .. } => e,
        _ => return None,
    };
    match expr {
        SorobanExpr::InvokeContract { return_type, .. }
        | SorobanExpr::TryInvokeContract { return_type, .. } => Some(return_type),
        _ => None,
    }
}

fn recover_invoke_return_types_nested(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: recover_invoke_return_types(then_body),
            else_body: recover_invoke_return_types(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: recover_invoke_return_types(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: recover_invoke_return_types(body),
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
            body: recover_invoke_return_types(body),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(recover_invoke_return_types(body)),
        other => other,
    }
}

fn remove_val_tag_guards_nested(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: remove_val_tag_guards(then_body),
            else_body: remove_val_tag_guards(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: remove_val_tag_guards(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: remove_val_tag_guards(body),
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
            body: remove_val_tag_guards(body),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(remove_val_tag_guards(body)),
        other => other,
    }
}

/// Drop SDK Val-decode dispatch husks left behind in **void** functions.
///
/// Inlining a non-void decoder (e.g. a `Symbol`→index ladder) into a void caller
/// leaves `if <lost-tag-check> { return <int> }` fragments. In a void function the
/// value-return is invalid, so codegen drops it — the guard renders as
/// `if todo!() == 1114112 {}` (1114112 = `0x110000`, the scval `Symbol` tag). When
/// the condition is itself an `UnknownVal` (the lifter lost the decoded tag, so the
/// branch is unrepresentable — it would `todo!()`-panic if reached) the whole guard
/// is a pure artifact; remove it so it does not surface as a stray `todo!()`.
///
/// The CALLER must gate on void return type (`func.return_type.is_none()`). Within
/// that, this fires only when ALL hold: the `then` body is exactly one value-return
/// (`Return(Some(_))`), there is no `else`, and the condition contains an
/// `UnknownVal`. A legitimate void early-return is `Return(None)`; a real guard has
/// a representable condition — neither matches, so genuine control flow is kept.
pub fn drop_void_unknown_value_return_guards(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    stmts
        .into_iter()
        .filter_map(|stmt| match stmt {
            SorobanStmt::If {
                ref condition,
                ref then_body,
                ref else_body,
            } if else_body.is_empty()
                && matches!(then_body.as_slice(), [SorobanStmt::Return(Some(_))])
                && expr_contains(condition, &SorobanExpr::UnknownVal) =>
            {
                cov_mark::hit!(void_unknown_return_guard_dropped);
                None
            }
            other => Some(drop_void_unknown_value_return_guards_nested(other)),
        })
        .collect()
}

fn drop_void_unknown_value_return_guards_nested(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: drop_void_unknown_value_return_guards(then_body),
            else_body: drop_void_unknown_value_return_guards(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: drop_void_unknown_value_return_guards(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: drop_void_unknown_value_return_guards(body),
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
            body: drop_void_unknown_value_return_guards(body),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(drop_void_unknown_value_return_guards(body)),
        other => other,
    }
}

/// Fold constant expressions
fn fold_constants(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    stmts.into_iter().map(fold_stmt).collect()
}

fn fold_stmt(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::Let {
            name,
            mutable,
            value,
        } => SorobanStmt::Let {
            name,
            mutable,
            value: fold_expr(value),
        },
        SorobanStmt::Return(Some(expr)) => SorobanStmt::Return(Some(fold_expr(expr))),
        SorobanStmt::Expr(expr) => SorobanStmt::Expr(fold_expr(expr)),
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition: fold_expr(condition),
            then_body: fold_constants(then_body),
            else_body: fold_constants(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee: fold_expr(scrutinee),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: fold_constants(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: fold_constants(body),
        },
        SorobanStmt::Block(stmts) => SorobanStmt::Block(fold_constants(stmts)),
        SorobanStmt::Assign { target, value } => SorobanStmt::Assign {
            target,
            value: fold_expr(value),
        },
        other => other,
    }
}

/// True for an integer comparison (`<`, `<=`, `>`, `>=`, `==`, `!=`). When such a
/// bool appears as an operand of integer `+`/`-`, it is a carry/borrow bit from a
/// two-i64-limb i128 add/subtract leaking into the recomposed 128-bit value — the
/// SDK's soft-arith lowering. It can never legitimately be added to an integer.
fn is_carry_borrow_flag(e: &SorobanExpr) -> bool {
    matches!(
        e,
        SorobanExpr::Lt(..)
            | SorobanExpr::Le(..)
            | SorobanExpr::Gt(..)
            | SorobanExpr::Ge(..)
            | SorobanExpr::Eq(..)
            | SorobanExpr::Ne(..)
    )
}

fn fold_expr(expr: SorobanExpr) -> SorobanExpr {
    match expr {
        SorobanExpr::Add(a, b) => {
            let a = fold_expr(*a);
            let b = fold_expr(*b);
            match (&a, &b) {
                (SorobanExpr::U64Literal(x), SorobanExpr::U64Literal(y)) => {
                    SorobanExpr::U64Literal(x.wrapping_add(*y))
                }
                (SorobanExpr::I64Literal(x), SorobanExpr::I64Literal(y)) => {
                    SorobanExpr::I64Literal(x.wrapping_add(*y))
                }
                (SorobanExpr::U32Literal(x), SorobanExpr::U32Literal(y)) => {
                    SorobanExpr::U32Literal(x.wrapping_add(*y))
                }
                (SorobanExpr::I32Literal(x), SorobanExpr::I32Literal(y)) => {
                    SorobanExpr::I32Literal(x.wrapping_add(*y))
                }
                // Algebraic identity: x + 0 → x, 0 + x → x
                _ if is_zero_literal(&b) => a,
                _ if is_zero_literal(&a) => b,
                // Drop a leaked carry flag: `x + (lo < other)` is the carry bit of a
                // two-limb i128 add bleeding into the recomposed value. Adding a bool
                // to an integer never type-checks, so the comparison is always a
                // soft-arith artifact — recover the clean `x`. Require the other
                // operand to be a non-comparison so the `(a > b) - (a < b)` ordering
                // idiom (both operands comparisons) is left for its own recognizer.
                _ if is_carry_borrow_flag(&b) && !is_carry_borrow_flag(&a) => a,
                _ if is_carry_borrow_flag(&a) && !is_carry_borrow_flag(&b) => b,
                _ => SorobanExpr::Add(Box::new(a), Box::new(b)),
            }
        }
        SorobanExpr::Sub(a, b) => {
            let a = fold_expr(*a);
            let b = fold_expr(*b);
            match (&a, &b) {
                (SorobanExpr::U64Literal(x), SorobanExpr::U64Literal(y)) => {
                    SorobanExpr::U64Literal(x.wrapping_sub(*y))
                }
                (SorobanExpr::I64Literal(x), SorobanExpr::I64Literal(y)) => {
                    SorobanExpr::I64Literal(x.wrapping_sub(*y))
                }
                (SorobanExpr::U32Literal(x), SorobanExpr::U32Literal(y)) => {
                    SorobanExpr::U32Literal(x.wrapping_sub(*y))
                }
                (SorobanExpr::I32Literal(x), SorobanExpr::I32Literal(y)) => {
                    SorobanExpr::I32Literal(x.wrapping_sub(*y))
                }
                // Algebraic identity: x - 0 → x
                _ if is_zero_literal(&b) => a,
                // Drop a leaked borrow flag: `x - (lo < other)` is the borrow bit of a
                // two-limb i128 subtraction bleeding into the recomposed value (same
                // rationale as the carry case in `Add`). The non-comparison guard on
                // `a` preserves the `(a > b) - (a < b)` ordering idiom.
                _ if is_carry_borrow_flag(&b) && !is_carry_borrow_flag(&a) => a,
                _ => SorobanExpr::Sub(Box::new(a), Box::new(b)),
            }
        }
        SorobanExpr::Mul(a, b) => {
            let a = fold_expr(*a);
            let b = fold_expr(*b);
            match (&a, &b) {
                (SorobanExpr::U64Literal(x), SorobanExpr::U64Literal(y)) => {
                    SorobanExpr::U64Literal(x.wrapping_mul(*y))
                }
                (SorobanExpr::I64Literal(x), SorobanExpr::I64Literal(y)) => {
                    SorobanExpr::I64Literal(x.wrapping_mul(*y))
                }
                (SorobanExpr::U32Literal(x), SorobanExpr::U32Literal(y)) => {
                    SorobanExpr::U32Literal(x.wrapping_mul(*y))
                }
                (SorobanExpr::I32Literal(x), SorobanExpr::I32Literal(y)) => {
                    SorobanExpr::I32Literal(x.wrapping_mul(*y))
                }
                // Algebraic identities: x * 1 → x, 1 * x → x
                _ if is_one_literal(&b) => a,
                _ if is_one_literal(&a) => b,
                // x * 0 → 0, 0 * x → 0
                _ if is_zero_literal(&b) => b,
                _ if is_zero_literal(&a) => a,
                _ => SorobanExpr::Mul(Box::new(a), Box::new(b)),
            }
        }
        // Div: recurse into sub-expressions and apply algebraic identities
        SorobanExpr::Div(a, b) => {
            let a = fold_expr(*a);
            let b = fold_expr(*b);
            match (&a, &b) {
                (SorobanExpr::U64Literal(x), SorobanExpr::U64Literal(y)) if *y != 0 => {
                    SorobanExpr::U64Literal(x / y)
                }
                (SorobanExpr::I64Literal(x), SorobanExpr::I64Literal(y)) if *y != 0 => {
                    SorobanExpr::I64Literal(x.wrapping_div(*y))
                }
                (SorobanExpr::U32Literal(x), SorobanExpr::U32Literal(y)) if *y != 0 => {
                    SorobanExpr::U32Literal(x / y)
                }
                (SorobanExpr::I32Literal(x), SorobanExpr::I32Literal(y)) if *y != 0 => {
                    SorobanExpr::I32Literal(x.wrapping_div(*y))
                }
                // x / 1 → x
                _ if is_one_literal(&b) => a,
                _ => SorobanExpr::Div(Box::new(a), Box::new(b)),
            }
        }
        // Rem: recurse into sub-expressions and fold constants
        SorobanExpr::Rem(a, b) => {
            let a = fold_expr(*a);
            let b = fold_expr(*b);
            match (&a, &b) {
                (SorobanExpr::U64Literal(x), SorobanExpr::U64Literal(y)) if *y != 0 => {
                    SorobanExpr::U64Literal(x % y)
                }
                (SorobanExpr::I64Literal(x), SorobanExpr::I64Literal(y)) if *y != 0 => {
                    SorobanExpr::I64Literal(x.wrapping_rem(*y))
                }
                (SorobanExpr::U32Literal(x), SorobanExpr::U32Literal(y)) if *y != 0 => {
                    SorobanExpr::U32Literal(x % y)
                }
                (SorobanExpr::I32Literal(x), SorobanExpr::I32Literal(y)) if *y != 0 => {
                    SorobanExpr::I32Literal(x.wrapping_rem(*y))
                }
                // x % 1 → 0 (use divisor's type for the zero)
                _ if is_one_literal(&b) => match &b {
                    SorobanExpr::U64Literal(_) => SorobanExpr::U64Literal(0),
                    SorobanExpr::I64Literal(_) => SorobanExpr::I64Literal(0),
                    SorobanExpr::U32Literal(_) => SorobanExpr::U32Literal(0),
                    SorobanExpr::I32Literal(_) => SorobanExpr::I32Literal(0),
                    _ => unreachable!("is_one_literal matched but no type found"),
                },
                _ => SorobanExpr::Rem(Box::new(a), Box::new(b)),
            }
        }
        // And/Or: recurse and apply short-circuit identities
        SorobanExpr::And(a, b) => {
            let a = fold_expr(*a);
            let b = fold_expr(*b);
            match (&a, &b) {
                // true && x → x, x && true → x
                (SorobanExpr::BoolLiteral(true), _) => b,
                (_, SorobanExpr::BoolLiteral(true)) => a,
                // false && x → false, x && false → false
                (SorobanExpr::BoolLiteral(false), _) | (_, SorobanExpr::BoolLiteral(false)) => {
                    SorobanExpr::BoolLiteral(false)
                }
                _ if a == b => a, // a && a → a
                _ => SorobanExpr::And(Box::new(a), Box::new(b)),
            }
        }
        SorobanExpr::Or(a, b) => {
            let a = fold_expr(*a);
            let b = fold_expr(*b);
            match (&a, &b) {
                // false || x → x, x || false → x
                (SorobanExpr::BoolLiteral(false), _) => b,
                (_, SorobanExpr::BoolLiteral(false)) => a,
                // true || x → true, x || true → true
                (SorobanExpr::BoolLiteral(true), _) | (_, SorobanExpr::BoolLiteral(true)) => {
                    SorobanExpr::BoolLiteral(true)
                }
                _ if a == b => a, // a || a → a
                _ => SorobanExpr::Or(Box::new(a), Box::new(b)),
            }
        }
        // Not(comparison) → negated comparison (boolean identity).
        // Critical for br_if patterns where the condition is the exit guard (NOT the body guard).
        // Re-fold the result since the negated comparison may now be constant-foldable.
        SorobanExpr::Not(inner) => match fold_expr(*inner) {
            SorobanExpr::Not(inner2) => *inner2, // !!x → x
            // !true → false, !false → true.
            // Safe now that collapse_trivial_loops runs first and removes
            // `loop { continue; }` dead validation artifacts.
            SorobanExpr::BoolLiteral(v) => SorobanExpr::BoolLiteral(!v),
            SorobanExpr::Lt(a, b) => fold_expr(SorobanExpr::Ge(a, b)),
            SorobanExpr::Ge(a, b) => fold_expr(SorobanExpr::Lt(a, b)),
            SorobanExpr::Gt(a, b) => fold_expr(SorobanExpr::Le(a, b)),
            SorobanExpr::Le(a, b) => fold_expr(SorobanExpr::Gt(a, b)),
            SorobanExpr::Eq(a, b) => fold_expr(SorobanExpr::Ne(a, b)),
            SorobanExpr::Ne(a, b) => fold_expr(SorobanExpr::Eq(a, b)),
            other => SorobanExpr::Not(Box::new(other)),
        },

        // obj_cmp(a, b) comparison_with_constant → direct comparison a op b.
        // obj_cmp returns: -1 if a < b, 0 if a == b, 1 if a > b.
        SorobanExpr::Eq(lhs, rhs) => {
            let lhs = fold_expr(*lhs);
            let rhs = fold_expr(*rhs);
            if let Some((a, b)) = try_fold_obj_cmp(&lhs, &rhs) {
                return match as_cmp_int(&rhs) {
                    Some(-1) => SorobanExpr::Lt(a, b), // == -1 → a < b
                    Some(0) => SorobanExpr::Eq(a, b),  // == 0  → a == b
                    Some(1) => SorobanExpr::Gt(a, b),  // == 1  → a > b
                    _ => SorobanExpr::Eq(Box::new(lhs), Box::new(rhs)),
                };
            }
            if is_zero_expr(&rhs)
                && let Some((a, b)) = try_fold_signum(&lhs)
            {
                return SorobanExpr::Eq(a, b);
            }
            // bool_expr == 1 → bool_expr;  bool_expr == 0 → !bool_expr
            if is_bool_typed(&lhs) {
                if is_one_expr(&rhs) {
                    return lhs;
                }
                if is_zero_expr(&rhs) {
                    return SorobanExpr::Not(Box::new(lhs));
                }
            }
            // expr == true → expr;  expr == false → !expr
            if matches!(rhs, SorobanExpr::BoolLiteral(true)) {
                return lhs;
            }
            if matches!(rhs, SorobanExpr::BoolLiteral(false)) {
                return fold_expr(SorobanExpr::Not(Box::new(lhs)));
            }
            if matches!(lhs, SorobanExpr::BoolLiteral(true)) {
                return rhs;
            }
            if matches!(lhs, SorobanExpr::BoolLiteral(false)) {
                return fold_expr(SorobanExpr::Not(Box::new(rhs)));
            }
            // x * c == 0 → x == 0 (c is non-zero constant)
            if is_zero_literal(&rhs)
                && let Some(x) = extract_mul_nonzero(&lhs)
            {
                return SorobanExpr::Eq(Box::new(x.clone()), Box::new(rhs));
            }
            if is_zero_literal(&lhs)
                && let Some(x) = extract_mul_nonzero(&rhs)
            {
                return SorobanExpr::Eq(Box::new(lhs), Box::new(x.clone()));
            }
            // Constant comparison: Eq(lit, lit) → BoolLiteral
            if let Some(result) = try_fold_literal_cmp(&lhs, &rhs, |a, b| a == b) {
                return result;
            }
            // Tautology: a == a → true (SorobanExpr derives PartialEq)
            if lhs == rhs {
                return SorobanExpr::BoolLiteral(true);
            }
            // Decode Val-encoded threshold: (N << 32) | 0xFFFFFFFF → U32Literal(N)
            if let Some(n) = try_decode_val_threshold(&rhs) {
                return SorobanExpr::Eq(Box::new(lhs), Box::new(SorobanExpr::U32Literal(n)));
            }
            if let Some(n) = try_decode_val_threshold(&lhs) {
                return SorobanExpr::Eq(Box::new(SorobanExpr::U32Literal(n)), Box::new(rhs));
            }
            SorobanExpr::Eq(Box::new(lhs), Box::new(rhs))
        }
        SorobanExpr::Ne(lhs, rhs) => {
            let lhs = fold_expr(*lhs);
            let rhs = fold_expr(*rhs);
            if let Some((a, b)) = try_fold_obj_cmp(&lhs, &rhs) {
                return match as_cmp_int(&rhs) {
                    Some(-1) => SorobanExpr::Ge(a, b), // != -1 → a >= b
                    Some(0) => SorobanExpr::Ne(a, b),  // != 0  → a != b
                    Some(1) => SorobanExpr::Le(a, b),  // != 1  → a <= b
                    _ => SorobanExpr::Ne(Box::new(lhs), Box::new(rhs)),
                };
            }
            if is_zero_expr(&rhs)
                && let Some((a, b)) = try_fold_signum(&lhs)
            {
                return SorobanExpr::Ne(a, b);
            }
            // bool_expr != 0 → bool_expr;  bool_expr != 1 → !bool_expr
            if is_bool_typed(&lhs) {
                if is_zero_expr(&rhs) {
                    return lhs;
                }
                if is_one_expr(&rhs) {
                    return SorobanExpr::Not(Box::new(lhs));
                }
            }
            // expr != false → expr;  expr != true → !expr
            if matches!(rhs, SorobanExpr::BoolLiteral(false)) {
                return lhs;
            }
            if matches!(rhs, SorobanExpr::BoolLiteral(true)) {
                return fold_expr(SorobanExpr::Not(Box::new(lhs)));
            }
            if matches!(lhs, SorobanExpr::BoolLiteral(false)) {
                return rhs;
            }
            if matches!(lhs, SorobanExpr::BoolLiteral(true)) {
                return fold_expr(SorobanExpr::Not(Box::new(rhs)));
            }
            // x * c != 0 → x != 0 (c is non-zero constant)
            if is_zero_literal(&rhs)
                && let Some(x) = extract_mul_nonzero(&lhs)
            {
                return SorobanExpr::Ne(Box::new(x.clone()), Box::new(rhs));
            }
            if is_zero_literal(&lhs)
                && let Some(x) = extract_mul_nonzero(&rhs)
            {
                return SorobanExpr::Ne(Box::new(lhs), Box::new(x.clone()));
            }
            // Constant comparison: Ne(lit, lit) → BoolLiteral
            if let Some(result) = try_fold_literal_cmp(&lhs, &rhs, |a, b| a != b) {
                return result;
            }
            // Tautology: a != a → false (SorobanExpr derives PartialEq)
            if lhs == rhs {
                return SorobanExpr::BoolLiteral(false);
            }
            // Decode Val-encoded threshold: (N << 32) | 0xFFFFFFFF → U32Literal(N)
            if let Some(n) = try_decode_val_threshold(&rhs) {
                return SorobanExpr::Ne(Box::new(lhs), Box::new(SorobanExpr::U32Literal(n)));
            }
            if let Some(n) = try_decode_val_threshold(&lhs) {
                return SorobanExpr::Ne(Box::new(SorobanExpr::U32Literal(n)), Box::new(rhs));
            }
            SorobanExpr::Ne(Box::new(lhs), Box::new(rhs))
        }
        SorobanExpr::Lt(lhs, rhs) => {
            let lhs = fold_expr(*lhs);
            let rhs = fold_expr(*rhs);
            if let Some((a, b)) = try_fold_obj_cmp(&lhs, &rhs) {
                return match as_cmp_int(&rhs) {
                    Some(0) => SorobanExpr::Lt(a, b), // < 0 → a < b
                    _ => SorobanExpr::Lt(Box::new(lhs), Box::new(rhs)),
                };
            }
            // Signum fold: Sub(Gt(a,b), Lt(a,b)) < 0  →  a < b
            if is_zero_expr(&rhs)
                && let Some((a, b)) = try_fold_signum(&lhs)
            {
                return SorobanExpr::Lt(a, b);
            }
            // Constant comparison: Lt(lit, lit) → BoolLiteral
            if let Some(result) = try_fold_literal_cmp(&lhs, &rhs, |a, b| a < b) {
                return result;
            }
            // Canonicalize: lit < expr → expr > lit
            if is_numeric_literal(&lhs) && !is_numeric_literal(&rhs) {
                return SorobanExpr::Gt(Box::new(rhs), Box::new(lhs));
            }
            // Decode Val-encoded threshold: (N << 32) | 0xFFFFFFFF → U32Literal(N)
            if let Some(n) = try_decode_val_threshold(&rhs) {
                return SorobanExpr::Lt(Box::new(lhs), Box::new(SorobanExpr::U32Literal(n)));
            }
            if let Some(n) = try_decode_val_threshold(&lhs) {
                return SorobanExpr::Lt(Box::new(SorobanExpr::U32Literal(n)), Box::new(rhs));
            }
            SorobanExpr::Lt(Box::new(lhs), Box::new(rhs))
        }
        SorobanExpr::Le(lhs, rhs) => {
            let lhs = fold_expr(*lhs);
            let rhs = fold_expr(*rhs);
            if let Some((a, b)) = try_fold_obj_cmp(&lhs, &rhs) {
                return match as_cmp_int(&rhs) {
                    Some(0) => SorobanExpr::Le(a, b), // <= 0 → a <= b
                    _ => SorobanExpr::Le(Box::new(lhs), Box::new(rhs)),
                };
            }
            if is_zero_expr(&rhs)
                && let Some((a, b)) = try_fold_signum(&lhs)
            {
                return SorobanExpr::Le(a, b);
            }
            // Constant comparison: Le(lit, lit) → BoolLiteral
            if let Some(result) = try_fold_literal_cmp(&lhs, &rhs, |a, b| a <= b) {
                return result;
            }
            // Canonicalize: lit <= expr → expr >= lit
            if is_numeric_literal(&lhs) && !is_numeric_literal(&rhs) {
                return SorobanExpr::Ge(Box::new(rhs), Box::new(lhs));
            }
            // Decode Val-encoded threshold: (N << 32) | 0xFFFFFFFF → U32Literal(N)
            if let Some(n) = try_decode_val_threshold(&rhs) {
                return SorobanExpr::Le(Box::new(lhs), Box::new(SorobanExpr::U32Literal(n)));
            }
            if let Some(n) = try_decode_val_threshold(&lhs) {
                return SorobanExpr::Le(Box::new(SorobanExpr::U32Literal(n)), Box::new(rhs));
            }
            SorobanExpr::Le(Box::new(lhs), Box::new(rhs))
        }
        SorobanExpr::Gt(lhs, rhs) => {
            let lhs = fold_expr(*lhs);
            let rhs = fold_expr(*rhs);
            if let Some((a, b)) = try_fold_obj_cmp(&lhs, &rhs) {
                return match as_cmp_int(&rhs) {
                    Some(0) => SorobanExpr::Gt(a, b), // > 0 → a > b
                    _ => SorobanExpr::Gt(Box::new(lhs), Box::new(rhs)),
                };
            }
            if is_zero_expr(&rhs)
                && let Some((a, b)) = try_fold_signum(&lhs)
            {
                return SorobanExpr::Gt(a, b);
            }
            // Constant comparison: Gt(lit, lit) → BoolLiteral
            if let Some(result) = try_fold_literal_cmp(&lhs, &rhs, |a, b| a > b) {
                return result;
            }
            // Canonicalize: lit > expr → expr < lit
            if is_numeric_literal(&lhs) && !is_numeric_literal(&rhs) {
                return SorobanExpr::Lt(Box::new(rhs), Box::new(lhs));
            }
            // Decode Val-encoded threshold: (N << 32) | 0xFFFFFFFF → U32Literal(N)
            if let Some(n) = try_decode_val_threshold(&rhs) {
                return SorobanExpr::Gt(Box::new(lhs), Box::new(SorobanExpr::U32Literal(n)));
            }
            if let Some(n) = try_decode_val_threshold(&lhs) {
                return SorobanExpr::Gt(Box::new(SorobanExpr::U32Literal(n)), Box::new(rhs));
            }
            SorobanExpr::Gt(Box::new(lhs), Box::new(rhs))
        }
        SorobanExpr::Ge(lhs, rhs) => {
            let lhs = fold_expr(*lhs);
            let rhs = fold_expr(*rhs);
            if let Some((a, b)) = try_fold_obj_cmp(&lhs, &rhs) {
                return match as_cmp_int(&rhs) {
                    Some(0) => SorobanExpr::Ge(a, b), // >= 0 → a >= b
                    _ => SorobanExpr::Ge(Box::new(lhs), Box::new(rhs)),
                };
            }
            if is_zero_expr(&rhs)
                && let Some((a, b)) = try_fold_signum(&lhs)
            {
                return SorobanExpr::Ge(a, b);
            }
            // Constant comparison: Ge(lit, lit) → BoolLiteral
            if let Some(result) = try_fold_literal_cmp(&lhs, &rhs, |a, b| a >= b) {
                return result;
            }
            // Canonicalize: lit >= expr → expr <= lit
            if is_numeric_literal(&lhs) && !is_numeric_literal(&rhs) {
                return SorobanExpr::Le(Box::new(rhs), Box::new(lhs));
            }
            // Decode Val-encoded threshold: (N << 32) | 0xFFFFFFFF → U32Literal(N)
            if let Some(n) = try_decode_val_threshold(&rhs) {
                return SorobanExpr::Ge(Box::new(lhs), Box::new(SorobanExpr::U32Literal(n)));
            }
            if let Some(n) = try_decode_val_threshold(&lhs) {
                return SorobanExpr::Ge(Box::new(SorobanExpr::U32Literal(n)), Box::new(rhs));
            }
            SorobanExpr::Ge(Box::new(lhs), Box::new(rhs))
        }

        // Recurse into MethodCall arguments for constant folding
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } => SorobanExpr::MethodCall {
            object: Box::new(fold_expr(*object)),
            method,
            args: args.into_iter().map(fold_expr).collect(),
        },

        // Recurse into ValConvert for constant folding; strip identity conversions
        // where the inner literal already matches the target type (e.g.,
        // ValConvert { I64Literal(v), "i64" } → I64Literal(v)).
        SorobanExpr::ValConvert { value, target_type } => {
            let inner = fold_expr(*value);
            if is_identity_val_convert(&inner, &target_type) {
                inner
            } else {
                SorobanExpr::ValConvert {
                    value: Box::new(inner),
                    target_type,
                }
            }
        }

        // Recurse into CastAs for constant folding
        SorobanExpr::CastAs { value, target_type } => SorobanExpr::CastAs {
            value: Box::new(fold_expr(*value)),
            target_type,
        },

        // Recurse into composite expressions so sub-expression folding
        // applies inside storage ops, construction, invocations, etc.
        SorobanExpr::StorageGet {
            storage_type,
            key,
            unwrap,
        } => SorobanExpr::StorageGet {
            storage_type,
            key: Box::new(fold_expr(*key)),
            unwrap,
        },
        SorobanExpr::StorageSet {
            storage_type,
            key,
            value,
        } => SorobanExpr::StorageSet {
            storage_type,
            key: Box::new(fold_expr(*key)),
            value: Box::new(fold_expr(*value)),
        },
        SorobanExpr::StorageHas { storage_type, key } => SorobanExpr::StorageHas {
            storage_type,
            key: Box::new(fold_expr(*key)),
        },
        SorobanExpr::StorageRemove { storage_type, key } => SorobanExpr::StorageRemove {
            storage_type,
            key: Box::new(fold_expr(*key)),
        },
        SorobanExpr::StorageExtendTtl {
            storage_type,
            key,
            threshold,
            extend_to,
        } => SorobanExpr::StorageExtendTtl {
            storage_type,
            key: Box::new(fold_expr(*key)),
            threshold: Box::new(fold_expr(*threshold)),
            extend_to: Box::new(fold_expr(*extend_to)),
        },
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold: Box::new(fold_expr(*threshold)),
            extend_to: Box::new(fold_expr(*extend_to)),
        },
        SorobanExpr::StructConstruct { type_name, fields } => SorobanExpr::StructConstruct {
            type_name,
            fields: fields.into_iter().map(|(n, e)| (n, fold_expr(e))).collect(),
        },
        SorobanExpr::EnumConstruct {
            type_name,
            variant,
            fields,
        } => SorobanExpr::EnumConstruct {
            type_name,
            variant,
            fields: fields.into_iter().map(fold_expr).collect(),
        },
        SorobanExpr::TupleConstruct(fields) => {
            SorobanExpr::TupleConstruct(fields.into_iter().map(fold_expr).collect())
        }
        SorobanExpr::VecConstruct(elems) => {
            SorobanExpr::VecConstruct(elems.into_iter().map(fold_expr).collect())
        }
        SorobanExpr::MapConstruct(entries) => SorobanExpr::MapConstruct(
            entries
                .into_iter()
                .map(|(k, v)| (fold_expr(k), fold_expr(v)))
                .collect(),
        ),
        SorobanExpr::InvokeContract {
            address,
            function,
            args,
            return_type,
        } => SorobanExpr::InvokeContract {
            address: Box::new(fold_expr(*address)),
            function: Box::new(fold_expr(*function)),
            args: args.into_iter().map(fold_expr).collect(),
            return_type,
        },
        SorobanExpr::TryInvokeContract {
            address,
            function,
            args,
            return_type,
        } => SorobanExpr::TryInvokeContract {
            address: Box::new(fold_expr(*address)),
            function: Box::new(fold_expr(*function)),
            args: args.into_iter().map(fold_expr).collect(),
            return_type,
        },
        SorobanExpr::FieldAccess { object, field } => SorobanExpr::FieldAccess {
            object: Box::new(fold_expr(*object)),
            field,
        },
        SorobanExpr::PublishEvent {
            event_name,
            topics,
            data,
        } => SorobanExpr::PublishEvent {
            event_name,
            topics: topics.into_iter().map(fold_expr).collect(),
            data: Box::new(fold_expr(*data)),
        },
        SorobanExpr::Log(args) => SorobanExpr::Log(args.into_iter().map(fold_expr).collect()),
        SorobanExpr::PanicWithError(err) => SorobanExpr::PanicWithError(Box::new(fold_expr(*err))),
        SorobanExpr::ErrorFromCode(e) => SorobanExpr::ErrorFromCode(Box::new(fold_expr(*e))),
        SorobanExpr::RequireAuth(addr) => SorobanExpr::RequireAuth(Box::new(fold_expr(*addr))),
        SorobanExpr::RequireAuthForArgs { address, args } => {
            // Auth args are tuples, not Vecs — convert VecConstruct back
            let folded_args = fold_expr(*args);
            let args = match folded_args {
                SorobanExpr::VecConstruct(elems) => SorobanExpr::TupleConstruct(elems),
                other => other,
            };
            SorobanExpr::RequireAuthForArgs {
                address: Box::new(fold_expr(*address)),
                args: Box::new(args),
            }
        }
        SorobanExpr::AuthorizeAsCurrContract(args) => {
            SorobanExpr::AuthorizeAsCurrContract(Box::new(fold_expr(*args)))
        }
        SorobanExpr::CryptoSha256(data) => SorobanExpr::CryptoSha256(Box::new(fold_expr(*data))),
        SorobanExpr::CryptoKeccak256(data) => {
            SorobanExpr::CryptoKeccak256(Box::new(fold_expr(*data)))
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => SorobanExpr::CryptoEd25519Verify {
            public_key: Box::new(fold_expr(*public_key)),
            message: Box::new(fold_expr(*message)),
            signature: Box::new(fold_expr(*signature)),
        },
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => SorobanExpr::CryptoSecp256k1Recover {
            msg_digest: Box::new(fold_expr(*msg_digest)),
            signature: Box::new(fold_expr(*signature)),
            recovery_id: Box::new(fold_expr(*recovery_id)),
        },
        SorobanExpr::PrngReseed(seed) => SorobanExpr::PrngReseed(Box::new(fold_expr(*seed))),
        SorobanExpr::PrngBytesNew(len) => SorobanExpr::PrngBytesNew(Box::new(fold_expr(*len))),
        SorobanExpr::PrngU64InRange { low, high } => SorobanExpr::PrngU64InRange {
            low: Box::new(fold_expr(*low)),
            high: Box::new(fold_expr(*high)),
        },
        SorobanExpr::PrngVecShuffle(vec) => SorobanExpr::PrngVecShuffle(Box::new(fold_expr(*vec))),
        SorobanExpr::StrkeyToAddress(addr) => {
            SorobanExpr::StrkeyToAddress(Box::new(fold_expr(*addr)))
        }
        SorobanExpr::AddressToStrkey(addr) => {
            SorobanExpr::AddressToStrkey(Box::new(fold_expr(*addr)))
        }
        SorobanExpr::RawHostCall {
            module,
            function,
            args,
        } => SorobanExpr::RawHostCall {
            module,
            function,
            args: args.into_iter().map(fold_expr).collect(),
        },

        other => other,
    }
}

/// If `lhs` is `RawHostCall { function: "obj_cmp", args: [a, b] }`, returns `(Box<a>, Box<b>)`.
fn try_fold_obj_cmp(
    lhs: &SorobanExpr,
    _rhs: &SorobanExpr,
) -> Option<(Box<SorobanExpr>, Box<SorobanExpr>)> {
    if let SorobanExpr::RawHostCall { function, args, .. } = lhs
        && function == "obj_cmp"
        && args.len() == 2
    {
        return Some((Box::new(args[0].clone()), Box::new(args[1].clone())));
    }
    None
}

/// Detects Sub(Gt(a,b), Lt(a,b)) -- the WASM signum idiom for obj_cmp results.
/// Returns Some((a, b)) if the pattern matches.
fn try_fold_signum(e: &SorobanExpr) -> Option<(Box<SorobanExpr>, Box<SorobanExpr>)> {
    if let SorobanExpr::Sub(lhs, rhs) = e
        && let (SorobanExpr::Gt(a1, b1), SorobanExpr::Lt(a2, b2)) = (lhs.as_ref(), rhs.as_ref())
        && a1 == a2
        && b1 == b2
    {
        return Some((a1.clone(), b1.clone()));
    }
    None
}

fn is_zero_expr(e: &SorobanExpr) -> bool {
    matches!(e, SorobanExpr::I32Literal(0) | SorobanExpr::I64Literal(0))
}

/// Check if an expression is a numeric literal (any integer type, bool, or Val-like constant).
/// Used for comparison canonicalization: `lit OP expr` → `expr FLIPPED_OP lit`.
fn is_numeric_literal(e: &SorobanExpr) -> bool {
    matches!(
        e,
        SorobanExpr::U64Literal(_)
            | SorobanExpr::I64Literal(_)
            | SorobanExpr::U32Literal(_)
            | SorobanExpr::I32Literal(_)
            | SorobanExpr::BoolLiteral(_)
    )
}

/// Decode a Val-encoded u32 threshold constant.
/// The SDK uses `(N << 32) | 0xFFFFFFFF` as unsigned comparison thresholds
/// to check if a Val-encoded u32's value portion exceeds N.
fn try_decode_val_threshold(expr: &SorobanExpr) -> Option<u32> {
    if let SorobanExpr::I64Literal(v) = expr {
        let uv = *v as u64;
        // Pattern: low 32 bits are all 1s, value > 0xFFFFFFFF (excludes N=0),
        // and high 32 bits < 0xFFFFFFFF (excludes -1 as i64)
        if uv > 0xFFFFFFFF && (uv & 0xFFFFFFFF) == 0xFFFFFFFF {
            let n = (uv >> 32) as u32;
            if n < 0xFFFFFFFF {
                cov_mark::hit!(val_threshold_decoded);
                return Some(n);
            }
        }
    }
    None
}

fn is_one_expr(e: &SorobanExpr) -> bool {
    matches!(e, SorobanExpr::I32Literal(1) | SorobanExpr::I64Literal(1))
}

/// Check if an expression is a zero literal of any integer type.
fn is_zero_literal(e: &SorobanExpr) -> bool {
    matches!(
        e,
        SorobanExpr::I32Literal(0)
            | SorobanExpr::U32Literal(0)
            | SorobanExpr::I64Literal(0)
            | SorobanExpr::U64Literal(0)
    )
}

/// Check if an expression is a one literal of any integer type.
fn is_one_literal(e: &SorobanExpr) -> bool {
    matches!(
        e,
        SorobanExpr::I32Literal(1)
            | SorobanExpr::U32Literal(1)
            | SorobanExpr::I64Literal(1)
            | SorobanExpr::U64Literal(1)
    )
}

/// Check if an expression is a non-zero integer literal.
fn is_nonzero_literal(e: &SorobanExpr) -> bool {
    matches!(
        e,
        SorobanExpr::I32Literal(v) if *v != 0
    ) || matches!(
        e,
        SorobanExpr::U32Literal(v) if *v != 0
    ) || matches!(
        e,
        SorobanExpr::I64Literal(v) if *v != 0
    ) || matches!(
        e,
        SorobanExpr::U64Literal(v) if *v != 0
    )
}

/// Extract the non-constant operand from `Mul(x, c)` or `Mul(c, x)` where c is a non-zero literal.
/// Returns the non-constant operand if the pattern matches.
fn extract_mul_nonzero(e: &SorobanExpr) -> Option<&SorobanExpr> {
    if let SorobanExpr::Mul(a, b) = e {
        if is_nonzero_literal(b) {
            return Some(a);
        }
        if is_nonzero_literal(a) {
            return Some(b);
        }
    }
    None
}

/// Check if a ValConvert is an identity conversion (inner type already matches target).
fn is_identity_val_convert(inner: &SorobanExpr, target_type: &str) -> bool {
    matches!(
        (inner, target_type),
        (SorobanExpr::I32Literal(_), "i32")
            | (SorobanExpr::U32Literal(_), "u32")
            | (SorobanExpr::I64Literal(_), "i64")
            | (SorobanExpr::U64Literal(_), "u64")
            | (SorobanExpr::BoolLiteral(_), "bool")
    )
}

/// Returns true for expressions known to produce a boolean value at the SDK level,
/// even though WASM represents them as integers.
fn is_bool_typed(e: &SorobanExpr) -> bool {
    if matches!(
        e,
        SorobanExpr::StorageHas { .. }
            | SorobanExpr::BoolLiteral(_)
            | SorobanExpr::Lt(_, _)
            | SorobanExpr::Le(_, _)
            | SorobanExpr::Gt(_, _)
            | SorobanExpr::Ge(_, _)
            | SorobanExpr::Eq(_, _)
            | SorobanExpr::Ne(_, _)
            | SorobanExpr::And(_, _)
            | SorobanExpr::Or(_, _)
            | SorobanExpr::Not(_)
    ) {
        return true;
    }
    // Soroban crypto methods that return bool
    if let SorobanExpr::MethodCall { method, .. } = e {
        return matches!(
            method.as_str(),
            "pairing_check" | "g1_is_in_subgroup" | "g2_is_in_subgroup"
        );
    }
    false
}

/// Extract an integer constant from a comparison operand.
/// Handles both I32Literal and I64Literal since the lifter may produce either
/// depending on the WASM instruction width (i32_eq vs i64_gt_s).
fn as_cmp_int(e: &SorobanExpr) -> Option<i64> {
    match e {
        SorobanExpr::I32Literal(v) => Some(*v as i64),
        SorobanExpr::I64Literal(v) => Some(*v),
        _ => None,
    }
}

/// Extract any integer literal as i128 for constant comparison folding.
/// Returns None for non-literal expressions.
fn as_literal_i128(e: &SorobanExpr) -> Option<i128> {
    match e {
        SorobanExpr::BoolLiteral(false) => Some(0),
        SorobanExpr::BoolLiteral(true) => Some(1),
        SorobanExpr::I32Literal(v) => Some(*v as i128),
        SorobanExpr::U32Literal(v) => Some(*v as i128),
        SorobanExpr::I64Literal(v) => Some(*v as i128),
        SorobanExpr::U64Literal(v) => Some(*v as i128),
        SorobanExpr::I128Literal(v) => Some(*v),
        SorobanExpr::U128Literal(v) => {
            // u128 values that fit in i128
            if *v <= i128::MAX as u128 {
                Some(*v as i128)
            } else {
                None
            }
        }
        // Unwrap transparent wrappers around literals — these are lifter artifacts
        // where the br_table index went through Val-encoding/decoding paths
        SorobanExpr::ErrorFromCode(inner)
        | SorobanExpr::ValConvert { value: inner, .. }
        | SorobanExpr::CastAs { value: inner, .. } => as_literal_i128(inner),
        // ContractError with error_code is a constant expression (used as br_table
        // index in enum dispatch, not a real error)
        SorobanExpr::ContractError { error_code, .. } => Some(*error_code as i128),
        _ => None,
    }
}

/// Evaluate a *fully constant* integer expression to its `i128` value.
///
/// Extends [`as_literal_i128`] (which only recognizes leaf literals) by folding
/// constant arithmetic — `2 - 1`, `(3 * 4) + 5`, … — but **only when every leaf
/// is a literal**. Returns `None` the instant a non-literal leaf is reached
/// (`UnknownVal`, a `Param`, a host call, …), so a runtime selector such as
/// `Sub(UnknownVal, 1)` is never mistaken for a constant.
///
/// Used to fold inlined `br_table` dispatches whose discriminant the lifter
/// resolved to a constant of *mixed* literal types (e.g. `i64(2) - i32(1)`),
/// which `fold_expr`'s same-type-only arithmetic arms leave intact. A match on a
/// genuine constant takes exactly one arm, so collapsing to it is faithful.
fn const_eval_i128(e: &SorobanExpr) -> Option<i128> {
    // Leaf literals (and the transparent wrappers `as_literal_i128` peels).
    if let Some(v) = as_literal_i128(e) {
        return Some(v);
    }
    match e {
        SorobanExpr::Add(a, b) => const_eval_i128(a)?.checked_add(const_eval_i128(b)?),
        SorobanExpr::Sub(a, b) => const_eval_i128(a)?.checked_sub(const_eval_i128(b)?),
        SorobanExpr::Mul(a, b) => const_eval_i128(a)?.checked_mul(const_eval_i128(b)?),
        SorobanExpr::Div(a, b) => {
            let d = const_eval_i128(b)?;
            if d == 0 {
                None
            } else {
                const_eval_i128(a)?.checked_div(d)
            }
        }
        SorobanExpr::Rem(a, b) => {
            let d = const_eval_i128(b)?;
            if d == 0 {
                None
            } else {
                const_eval_i128(a)?.checked_rem(d)
            }
        }
        _ => None,
    }
}

/// Try to fold a comparison of two literal values into a BoolLiteral.
/// Only folds to `false` — never to `true` — because `I32Literal(0)` often
/// represents an untracked stack value from the lifter, not a genuine constant.
/// Folding `0 != 16` to `true` would inline `continue` in validation preambles,
/// eliminating the actual function body that follows. Folding to `false` safely
/// removes dead branches without this risk.
fn try_fold_literal_cmp(
    lhs: &SorobanExpr,
    rhs: &SorobanExpr,
    cmp: fn(i128, i128) -> bool,
) -> Option<SorobanExpr> {
    let a = as_literal_i128(lhs)?;
    let b = as_literal_i128(rhs)?;
    let result = cmp(a, b);
    // Only fold to false — conservatively preserves code after always-true guards
    if result {
        None
    } else {
        Some(SorobanExpr::BoolLiteral(false))
    }
}

// ---------------------------------------------------------------------------
// Remove redundant let bindings
// ---------------------------------------------------------------------------

/// Remove let bindings that are unused (dead store) or used exactly once
/// and whose value is side-effect-free (safe to inline).
/// Public entry point for dead-let elimination (used by pipeline post-cleanup).
pub fn remove_redundant_lets_public(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    remove_redundant_lets(stmts)
}

/// Invalidate StorageGet CSE entries when a statement may have mutated
/// observable storage. Conservative: a StorageSet/StorageRemove matching the
/// exact `(storage_type, key)` of an entry invalidates only that entry; any
/// other potential mutation (storage write with non-comparable key,
/// RawHostCall, nested control flow) clears the entire table.
fn invalidate_seen_gets_for_stmt(
    stmt: &SorobanStmt,
    seen_gets: &mut Vec<(StorageType, SorobanExpr, bool, u32, String)>,
) {
    let exprs: Vec<&SorobanExpr> = match stmt {
        SorobanStmt::Expr(e) => vec![e],
        SorobanStmt::Let { value, .. } => vec![value],
        SorobanStmt::Assign { value, .. } => vec![value],
        SorobanStmt::Return(Some(e)) => vec![e],
        // Control flow: we don't track CSE across branches/loops. Just clear.
        SorobanStmt::If { .. }
        | SorobanStmt::Match { .. }
        | SorobanStmt::Loop { .. }
        | SorobanStmt::For { .. }
        | SorobanStmt::Block(_) => {
            seen_gets.clear();
            return;
        }
        SorobanStmt::Return(None)
        | SorobanStmt::Break
        | SorobanStmt::Continue
        | SorobanStmt::Comment(_) => return,
    };

    for e in exprs {
        invalidate_seen_gets_for_expr(e, seen_gets);
        if seen_gets.is_empty() {
            return;
        }
    }
}

fn invalidate_seen_gets_for_expr(
    expr: &SorobanExpr,
    seen_gets: &mut Vec<(StorageType, SorobanExpr, bool, u32, String)>,
) {
    match expr {
        SorobanExpr::StorageSet {
            storage_type, key, ..
        }
        | SorobanExpr::StorageRemove { storage_type, key } => {
            seen_gets.retain(|(st, k, _, _, _)| !(st == storage_type && k == key.as_ref()));
        }
        SorobanExpr::StorageExtendTtl { .. } | SorobanExpr::ExtendInstanceAndCodeTtl { .. } => {
            // TTL extensions do not change observed values; no invalidation.
        }
        SorobanExpr::RawHostCall { .. }
        | SorobanExpr::InvokeContract { .. }
        | SorobanExpr::TryInvokeContract { .. } => {
            // Unknown effects — flush conservatively.
            seen_gets.clear();
        }
        // Recurse into composite expressions to find nested mutations.
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
            invalidate_seen_gets_for_expr(a, seen_gets);
            invalidate_seen_gets_for_expr(b, seen_gets);
        }
        SorobanExpr::Not(inner)
        | SorobanExpr::RequireAuth(inner)
        | SorobanExpr::AuthorizeAsCurrContract(inner)
        | SorobanExpr::PanicWithError(inner)
        | SorobanExpr::CryptoSha256(inner)
        | SorobanExpr::CryptoKeccak256(inner)
        | SorobanExpr::PrngReseed(inner)
        | SorobanExpr::PrngBytesNew(inner)
        | SorobanExpr::PrngVecShuffle(inner)
        | SorobanExpr::StrkeyToAddress(inner)
        | SorobanExpr::AddressToStrkey(inner)
        | SorobanExpr::FieldAccess { object: inner, .. }
        | SorobanExpr::ValConvert { value: inner, .. }
        | SorobanExpr::CastAs { value: inner, .. }
        | SorobanExpr::ValTag(inner)
        | SorobanExpr::Some(inner)
        | SorobanExpr::SretResult(inner)
        | SorobanExpr::ErrorFromCode(inner) => {
            invalidate_seen_gets_for_expr(inner, seen_gets);
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            invalidate_seen_gets_for_expr(object, seen_gets);
            for a in args {
                invalidate_seen_gets_for_expr(a, seen_gets);
            }
        }
        SorobanExpr::VecTryIterFold { vec, init } => {
            invalidate_seen_gets_for_expr(vec, seen_gets);
            invalidate_seen_gets_for_expr(init, seen_gets);
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics {
                invalidate_seen_gets_for_expr(t, seen_gets);
            }
            invalidate_seen_gets_for_expr(data, seen_gets);
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields {
                invalidate_seen_gets_for_expr(v, seen_gets);
            }
        }
        SorobanExpr::EnumConstruct { fields, .. }
        | SorobanExpr::TupleConstruct(fields)
        | SorobanExpr::VecConstruct(fields)
        | SorobanExpr::Log(fields) => {
            for v in fields {
                invalidate_seen_gets_for_expr(v, seen_gets);
            }
        }
        SorobanExpr::MapConstruct(entries) => {
            for (k, v) in entries {
                invalidate_seen_gets_for_expr(k, seen_gets);
                invalidate_seen_gets_for_expr(v, seen_gets);
            }
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            invalidate_seen_gets_for_expr(address, seen_gets);
            invalidate_seen_gets_for_expr(args, seen_gets);
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            invalidate_seen_gets_for_expr(public_key, seen_gets);
            invalidate_seen_gets_for_expr(message, seen_gets);
            invalidate_seen_gets_for_expr(signature, seen_gets);
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            invalidate_seen_gets_for_expr(msg_digest, seen_gets);
            invalidate_seen_gets_for_expr(signature, seen_gets);
            invalidate_seen_gets_for_expr(recovery_id, seen_gets);
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            invalidate_seen_gets_for_expr(low, seen_gets);
            invalidate_seen_gets_for_expr(high, seen_gets);
        }
        // Pure StorageGet and StorageHas are read-only; do not invalidate.
        SorobanExpr::StorageGet { key, .. } | SorobanExpr::StorageHas { key, .. } => {
            invalidate_seen_gets_for_expr(key, seen_gets);
        }
        // Leaves with no side effects.
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
        | SorobanExpr::Panic
        | SorobanExpr::LedgerSequence
        | SorobanExpr::LedgerTimestamp
        | SorobanExpr::LedgerNetworkId
        | SorobanExpr::CurrentContractAddress
        | SorobanExpr::MaxLiveUntilLedger
        | SorobanExpr::CollectionNew(_)
        | SorobanExpr::UnknownVal
        | SorobanExpr::CyclicSlot { .. }
        | SorobanExpr::ValTagName(_)
        | SorobanExpr::ContractError { .. } => {}
    }
}

fn remove_redundant_lets(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    // Recurse into nested scopes first so inner lets are cleaned up.
    let mut stmts: Vec<SorobanStmt> = stmts.into_iter().map(recurse_nested).collect();

    // StorageGet CSE: run FIRST, before dead-store removal. Dead-store removal
    // converts unused `let var_N = StorageGet` to `Expr(StorageGet)` which the
    // CSE can't match. Running CSE first eliminates duplicates while both
    // bindings are still Let statements.
    //
    // Invalidation: a StorageSet of the same (storage_type, key) between two
    // gets makes the second get observe a different value, so we must drop
    // the seen entry. Conservatively, any statement that might mutate storage
    // (a write of an unknown key, or a RawHostCall whose effects we cannot
    // model) flushes the whole table.
    let mut i = 0;
    let mut seen_gets: Vec<(StorageType, SorobanExpr, bool, u32, String)> = Vec::new();
    while i < stmts.len() {
        if let SorobanStmt::Let {
            name,
            mutable: false,
            value:
                SorobanExpr::StorageGet {
                    storage_type,
                    key,
                    unwrap,
                },
        } = &stmts[i]
            && let Some(idx) = let_name_to_local_idx(name)
        {
            if let Some((_, _, _, earlier_idx, _)) = seen_gets
                .iter()
                .find(|(st, k, uw, _, _)| st == storage_type && k == key.as_ref() && uw == unwrap)
            {
                cov_mark::hit!(cse_duplicate_storage_get_eliminated);
                let earlier_idx = *earlier_idx;
                let name_owned = name.clone();
                stmts.remove(i);
                // Only substitute up to the next redefinition of the same var.
                // WASM local reuse means the same var_N can be redefined with
                // a different value later — substitutions must not cross that.
                let redef_limit = find_next_redef(&stmts[i..], &name_owned);
                substitute_local(
                    &mut stmts[i..i + redef_limit],
                    idx,
                    &SorobanExpr::Local(earlier_idx),
                );
                continue;
            }
            seen_gets.push((*storage_type, (**key).clone(), *unwrap, idx, name.clone()));
        } else {
            // For any non-StorageGet-let statement, check whether it might
            // mutate storage and invalidate seen_gets accordingly.
            invalidate_seen_gets_for_stmt(&stmts[i], &mut seen_gets);
        }
        i += 1;
    }

    // Resolve unbound Local(N) in ValConvert args: when Local(N) has no
    // Let binding but there's a Let { var_M = ValConvert { FieldAccess } }
    // with the same target type, replace Local(N) → Local(M). This MUST
    // run before dead-store removal because var_M would otherwise be
    // stripped as unused, losing the FieldAccess reference.
    resolve_valconvert_locals(&mut stmts);

    let mut i = 0;
    while i < stmts.len() {
        if let SorobanStmt::Let {
            name,
            mutable,
            value,
        } = &stmts[i]
            && let Some(idx) = let_name_to_local_idx(name)
        {
            // Only count uses up to the next redefinition of the same var_N.
            // Uses after a redefinition refer to the later binding, not this one.
            let redef_limit = find_next_redef(&stmts[i + 1..], name);
            let (uses, in_loop) = count_local_uses(&stmts[i + 1..i + 1 + redef_limit], idx);
            let side_effect = expr_has_side_effects(value);

            // Dead store: never used and no side effects → drop it.
            if uses == 0 && !side_effect {
                cov_mark::hit!(dead_let_removed);
                if *mutable {
                    // Dead mutable variable: defined and possibly assigned in
                    // match/if arms, but never READ in any expression.
                    // Remove subsequent Assign statements targeting this var.
                    let removed_name = name.clone();
                    stmts.remove(i);
                    remove_dead_assigns(&mut stmts[i..], &removed_name);
                } else {
                    stmts.remove(i);
                }
                continue;
            }

            // Dead store with side effects: never used but the expression
            // might have side effects → keep the expression, drop the binding.
            if uses == 0 && side_effect && !*mutable {
                let SorobanStmt::Let { value, .. } = stmts.remove(i) else {
                    unreachable!()
                };
                stmts.insert(i, SorobanStmt::Expr(value));
                i += 1;
                continue;
            }

            // Immutable single-use, not inside a loop, and side-effect-free → inline.
            if !*mutable && uses == 1 && !in_loop && !side_effect {
                cov_mark::hit!(redundant_let_inlined);
                let SorobanStmt::Let { value, .. } = stmts.remove(i) else {
                    unreachable!()
                };
                substitute_local(&mut stmts[i..], idx, &value);
                // Don't advance i: re-check the (now different) statement at i.
                continue;
            }

            // Immutable single-use with side effects, used in immediately next
            // statement → safe to inline (execution order unchanged).
            if !*mutable && uses == 1 && !in_loop && side_effect && i + 1 < stmts.len() {
                let (next_uses, _) = count_local_uses(&stmts[i + 1..i + 2], idx);
                if next_uses == 1 {
                    let SorobanStmt::Let { value, .. } = stmts.remove(i) else {
                        unreachable!()
                    };
                    substitute_local(&mut stmts[i..i + 1], idx, &value);
                    continue;
                }
            }
        }
        i += 1;
    }

    // CSE pass: eliminate duplicate immutable let bindings with identical
    // side-effect-free values. When two lets in the same scope have the same
    // value expression, replace uses of the later binding with the earlier one.
    let mut i = 0;
    // Map from (value expression) → (local index, binding name)
    let mut seen_values: Vec<(SorobanExpr, u32, String)> = Vec::new();
    while i < stmts.len() {
        if let SorobanStmt::Let {
            name,
            mutable: false,
            value,
        } = &stmts[i]
            && let Some(idx) = let_name_to_local_idx(name)
            && !expr_has_side_effects(value)
        {
            // Check if we've seen an identical value before
            if let Some((_, earlier_idx, _)) = seen_values.iter().find(|(v, _, _)| v == value) {
                cov_mark::hit!(cse_duplicate_let_eliminated);
                let earlier_idx = *earlier_idx;
                // Substitute all references to this binding with the earlier one
                stmts.remove(i);
                substitute_local(&mut stmts[i..], idx, &SorobanExpr::Local(earlier_idx));
                continue; // Don't advance i; re-check statement at i
            }
            // First occurrence — record it
            seen_values.push((value.clone(), idx, name.clone()));
        }
        i += 1;
    }

    stmts
}

/// Recurse `remove_redundant_lets` into nested statement scopes.
/// Resolve unbound Local(N) inside ValConvert expressions by finding a
/// Let binding with matching type and FieldAccess value.
///
/// Pattern: `ValConvert { Local(N), "i128" }` where var_N has no Let binding,
/// but `Let { var_M = ValConvert { FieldAccess { "amount" }, "i128" } }` exists.
/// Replace Local(N) → Local(M) so the FieldAccess is used instead.
fn resolve_valconvert_locals(stmts: &mut [SorobanStmt]) {
    // Collect defined locals and typed FieldAccess bindings
    let mut defined: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut typed_field_bindings: Vec<(u32, String)> = Vec::new(); // (idx, target_type)

    for stmt in stmts.iter() {
        if let SorobanStmt::Let { name, value, .. } = stmt
            && let Some(idx) = let_name_to_local_idx(name)
        {
            defined.insert(idx);
            if let SorobanExpr::ValConvert {
                value: inner,
                target_type,
            } = value
                && matches!(inner.as_ref(), SorobanExpr::FieldAccess { .. })
            {
                typed_field_bindings.push((idx, target_type.clone()));
            }
        }
    }

    if typed_field_bindings.is_empty() {
        return;
    }

    // Walk all expressions and replace unbound Local(N) in ValConvert
    for stmt in stmts.iter_mut() {
        resolve_valconvert_in_stmt(stmt, &defined, &typed_field_bindings);
    }
}

fn resolve_valconvert_in_stmt(
    stmt: &mut SorobanStmt,
    defined: &std::collections::HashSet<u32>,
    bindings: &[(u32, String)],
) {
    match stmt {
        SorobanStmt::Expr(e) | SorobanStmt::Return(Some(e)) => {
            resolve_valconvert_in_expr(e, defined, bindings);
        }
        SorobanStmt::Let { value, .. } | SorobanStmt::Assign { value, .. } => {
            resolve_valconvert_in_expr(value, defined, bindings);
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            resolve_valconvert_in_expr(condition, defined, bindings);
            for s in then_body {
                resolve_valconvert_in_stmt(s, defined, bindings);
            }
            for s in else_body {
                resolve_valconvert_in_stmt(s, defined, bindings);
            }
        }
        SorobanStmt::Match { arms, .. } => {
            for arm in arms {
                for s in &mut arm.body {
                    resolve_valconvert_in_stmt(s, defined, bindings);
                }
            }
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            for s in body {
                resolve_valconvert_in_stmt(s, defined, bindings);
            }
        }
        _ => {}
    }
}

fn resolve_valconvert_in_expr(
    expr: &mut SorobanExpr,
    defined: &std::collections::HashSet<u32>,
    bindings: &[(u32, String)],
) {
    match expr {
        SorobanExpr::ValConvert { value, target_type } => {
            if let SorobanExpr::Local(idx) = value.as_ref()
                && !defined.contains(idx)
                && let Some((binding_idx, _)) = bindings.iter().find(|(_, t)| t == target_type)
            {
                **value = SorobanExpr::Local(*binding_idx);
            }
            resolve_valconvert_in_expr(value, defined, bindings);
        }
        SorobanExpr::InvokeContract { args, address, .. }
        | SorobanExpr::TryInvokeContract { args, address, .. } => {
            resolve_valconvert_in_expr(address, defined, bindings);
            for arg in args {
                resolve_valconvert_in_expr(arg, defined, bindings);
            }
        }
        SorobanExpr::VecConstruct(elems) | SorobanExpr::TupleConstruct(elems) => {
            for e in elems {
                resolve_valconvert_in_expr(e, defined, bindings);
            }
        }
        SorobanExpr::Add(a, b) | SorobanExpr::Sub(a, b) | SorobanExpr::Mul(a, b) => {
            resolve_valconvert_in_expr(a, defined, bindings);
            resolve_valconvert_in_expr(b, defined, bindings);
        }
        _ => {}
    }
}

fn recurse_nested(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: remove_redundant_lets(then_body),
            else_body: remove_redundant_lets(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: remove_redundant_lets(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: remove_redundant_lets(body),
        },
        SorobanStmt::Block(stmts) => SorobanStmt::Block(remove_redundant_lets(stmts)),
        other => other,
    }
}

/// If `name` has the form `var_N`, return `Some(N)`.
/// Named lets (e.g. "key", "result") are never auto-inlined.
fn let_name_to_local_idx(name: &str) -> Option<u32> {
    name.strip_prefix("var_").and_then(|s| s.parse().ok())
}

/// Find the index of the next `Let` statement that redefines the same variable.
/// Returns `stmts.len()` if no redefinition is found.
fn find_next_redef(stmts: &[SorobanStmt], name: &str) -> usize {
    for (j, stmt) in stmts.iter().enumerate() {
        if let SorobanStmt::Let { name: n, .. } = stmt
            && n == name
        {
            return j;
        }
    }
    stmts.len()
}

/// Remove all `Assign { target: name }` statements from a slice of statements,
/// recursing into match/if/loop/block bodies. If the assign's value has side
/// effects, convert to `Expr(value)` instead of dropping entirely.
fn remove_dead_assigns(stmts: &mut [SorobanStmt], name: &str) {
    let limit = find_next_redef(stmts, name);
    for stmt in stmts.iter_mut().take(limit) {
        remove_dead_assigns_stmt(stmt, name);
    }
}

fn remove_dead_assigns_stmt(stmt: &mut SorobanStmt, name: &str) {
    match stmt {
        SorobanStmt::Match { arms, .. } => {
            for arm in arms {
                remove_dead_assigns_from_body(&mut arm.body, name);
            }
        }
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            remove_dead_assigns_from_body(then_body, name);
            remove_dead_assigns_from_body(else_body, name);
        }
        SorobanStmt::Loop { body } => {
            remove_dead_assigns_from_body(body, name);
        }
        SorobanStmt::Block(body) => {
            remove_dead_assigns_from_body(body, name);
        }
        _ => {}
    }
}

fn remove_dead_assigns_from_body(body: &mut Vec<SorobanStmt>, name: &str) {
    body.retain_mut(|stmt| {
        if let SorobanStmt::Assign { target, value } = stmt
            && target == name
        {
            if expr_has_side_effects(value) {
                *stmt = SorobanStmt::Expr(std::mem::replace(value, SorobanExpr::Void));
                return true;
            }
            return false;
        }
        remove_dead_assigns_stmt(stmt, name);
        true
    });
}

/// Count how many times `Local(idx)` appears in `stmts`.
/// Returns `(count, any_use_inside_loop)`.
fn count_local_uses(stmts: &[SorobanStmt], idx: u32) -> (u32, bool) {
    count_local_in_stmts(stmts, idx, false)
}

fn count_local_in_stmts(stmts: &[SorobanStmt], idx: u32, inside_loop: bool) -> (u32, bool) {
    let mut count = 0u32;
    let mut any_loop = false;
    for stmt in stmts {
        let (c, l) = count_local_in_stmt(stmt, idx, inside_loop);
        count += c;
        any_loop |= l;
    }
    (count, any_loop)
}

fn count_local_in_stmt(stmt: &SorobanStmt, idx: u32, inside_loop: bool) -> (u32, bool) {
    match stmt {
        SorobanStmt::Expr(e) => {
            let c = count_local_in_expr(e, idx);
            (c, inside_loop && c > 0)
        }
        SorobanStmt::Let { value, .. } => {
            let c = count_local_in_expr(value, idx);
            (c, inside_loop && c > 0)
        }
        SorobanStmt::Assign { value, .. } => {
            let c = count_local_in_expr(value, idx);
            (c, inside_loop && c > 0)
        }
        SorobanStmt::Return(Some(e)) => {
            let c = count_local_in_expr(e, idx);
            (c, inside_loop && c > 0)
        }
        SorobanStmt::Return(None)
        | SorobanStmt::Comment(_)
        | SorobanStmt::Break
        | SorobanStmt::Continue => (0, false),
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            let cc = count_local_in_expr(condition, idx);
            let (tc, tl) = count_local_in_stmts(then_body, idx, inside_loop);
            let (ec, el) = count_local_in_stmts(else_body, idx, inside_loop);
            (cc + tc + ec, (inside_loop && cc > 0) | tl | el)
        }
        SorobanStmt::Match { scrutinee, arms } => {
            let sc = count_local_in_expr(scrutinee, idx);
            let mut total = sc;
            let mut any_loop = inside_loop && sc > 0;
            for arm in arms {
                let (c, l) = count_local_in_stmts(&arm.body, idx, inside_loop);
                total += c;
                any_loop |= l;
            }
            (total, any_loop)
        }
        SorobanStmt::Loop { body } => {
            // Any use inside a loop body is flagged as in_loop.
            let (c, _) = count_local_in_stmts(body, idx, true);
            (c, c > 0)
        }
        SorobanStmt::For {
            start, end, body, ..
        } => {
            let sc = count_local_in_expr(start, idx);
            let ec = count_local_in_expr(end, idx);
            let (bc, _) = count_local_in_stmts(body, idx, true);
            let total = sc + ec + bc;
            (total, total > 0)
        }
        SorobanStmt::Block(stmts) => count_local_in_stmts(stmts, idx, inside_loop),
    }
}

fn count_local_in_expr(expr: &SorobanExpr, idx: u32) -> u32 {
    match expr {
        SorobanExpr::Local(i) => u32::from(*i == idx),
        // Binary
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
        | SorobanExpr::Or(a, b) => count_local_in_expr(a, idx) + count_local_in_expr(b, idx),
        // Unary
        SorobanExpr::Not(a)
        | SorobanExpr::RequireAuth(a)
        | SorobanExpr::AuthorizeAsCurrContract(a)
        | SorobanExpr::PanicWithError(a)
        | SorobanExpr::PrngReseed(a)
        | SorobanExpr::PrngBytesNew(a)
        | SorobanExpr::PrngVecShuffle(a)
        | SorobanExpr::StrkeyToAddress(a)
        | SorobanExpr::AddressToStrkey(a)
        | SorobanExpr::ErrorFromCode(a)
        | SorobanExpr::CryptoSha256(a)
        | SorobanExpr::CryptoKeccak256(a) => count_local_in_expr(a, idx),
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            count_local_in_expr(value, idx)
        }
        SorobanExpr::FieldAccess { object, .. } => count_local_in_expr(object, idx),
        // Storage
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => count_local_in_expr(key, idx),
        SorobanExpr::StorageSet { key, value, .. } => {
            count_local_in_expr(key, idx) + count_local_in_expr(value, idx)
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            count_local_in_expr(key, idx)
                + count_local_in_expr(threshold, idx)
                + count_local_in_expr(extend_to, idx)
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => count_local_in_expr(threshold, idx) + count_local_in_expr(extend_to, idx),
        SorobanExpr::RequireAuthForArgs { address, args } => {
            count_local_in_expr(address, idx) + count_local_in_expr(args, idx)
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            topics
                .iter()
                .map(|t| count_local_in_expr(t, idx))
                .sum::<u32>()
                + count_local_in_expr(data, idx)
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
            count_local_in_expr(address, idx)
                + count_local_in_expr(function, idx)
                + args
                    .iter()
                    .map(|a| count_local_in_expr(a, idx))
                    .sum::<u32>()
        }
        SorobanExpr::StructConstruct { fields, .. } => fields
            .iter()
            .map(|(_, v)| count_local_in_expr(v, idx))
            .sum(),
        SorobanExpr::EnumConstruct { fields, .. } => {
            fields.iter().map(|f| count_local_in_expr(f, idx)).sum()
        }
        SorobanExpr::TupleConstruct(items) | SorobanExpr::VecConstruct(items) => {
            items.iter().map(|i| count_local_in_expr(i, idx)).sum()
        }
        SorobanExpr::MapConstruct(pairs) => pairs
            .iter()
            .map(|(k, v)| count_local_in_expr(k, idx) + count_local_in_expr(v, idx))
            .sum(),
        SorobanExpr::MethodCall { object, args, .. } => {
            count_local_in_expr(object, idx)
                + args
                    .iter()
                    .map(|a| count_local_in_expr(a, idx))
                    .sum::<u32>()
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            count_local_in_expr(public_key, idx)
                + count_local_in_expr(message, idx)
                + count_local_in_expr(signature, idx)
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            count_local_in_expr(msg_digest, idx)
                + count_local_in_expr(signature, idx)
                + count_local_in_expr(recovery_id, idx)
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            count_local_in_expr(low, idx) + count_local_in_expr(high, idx)
        }
        SorobanExpr::Log(args) | SorobanExpr::RawHostCall { args, .. } => {
            args.iter().map(|a| count_local_in_expr(a, idx)).sum()
        }
        // Leaves: literals, Param, Env, LedgerX, ContractError
        _ => 0,
    }
}

/// Replace the **first** occurrence of `Local(idx)` in `stmts` with `value`.
/// Returns `true` when the substitution was performed.
fn substitute_local(stmts: &mut [SorobanStmt], idx: u32, value: &SorobanExpr) -> bool {
    for stmt in stmts.iter_mut() {
        if substitute_local_in_stmt(stmt, idx, value) {
            return true;
        }
    }
    false
}

fn substitute_local_in_stmt(stmt: &mut SorobanStmt, idx: u32, value: &SorobanExpr) -> bool {
    match stmt {
        SorobanStmt::Expr(e) => substitute_local_in_expr(e, idx, value),
        SorobanStmt::Let { value: v, .. } => substitute_local_in_expr(v, idx, value),
        SorobanStmt::Assign { value: v, .. } => substitute_local_in_expr(v, idx, value),
        SorobanStmt::Return(Some(e)) => substitute_local_in_expr(e, idx, value),
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            substitute_local_in_expr(condition, idx, value)
                || substitute_local(then_body, idx, value)
                || substitute_local(else_body, idx, value)
        }
        SorobanStmt::Match { scrutinee, arms } => {
            if substitute_local_in_expr(scrutinee, idx, value) {
                return true;
            }
            for arm in arms.iter_mut() {
                if substitute_local(&mut arm.body, idx, value) {
                    return true;
                }
            }
            false
        }
        SorobanStmt::Loop { body } => substitute_local(body, idx, value),
        SorobanStmt::Block(stmts) => substitute_local(stmts, idx, value),
        _ => false,
    }
}

fn substitute_local_in_expr(expr: &mut SorobanExpr, idx: u32, value: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::Local(i) if *i == idx => {
            *expr = value.clone();
            true
        }
        // Binary
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
            substitute_local_in_expr(a, idx, value) || substitute_local_in_expr(b, idx, value)
        }
        // Unary
        SorobanExpr::Not(a)
        | SorobanExpr::RequireAuth(a)
        | SorobanExpr::AuthorizeAsCurrContract(a)
        | SorobanExpr::PanicWithError(a)
        | SorobanExpr::PrngReseed(a)
        | SorobanExpr::PrngBytesNew(a)
        | SorobanExpr::PrngVecShuffle(a)
        | SorobanExpr::StrkeyToAddress(a)
        | SorobanExpr::AddressToStrkey(a)
        | SorobanExpr::ErrorFromCode(a)
        | SorobanExpr::CryptoSha256(a)
        | SorobanExpr::CryptoKeccak256(a) => substitute_local_in_expr(a, idx, value),
        SorobanExpr::ValConvert { value: v, .. } | SorobanExpr::CastAs { value: v, .. } => {
            substitute_local_in_expr(v, idx, value)
        }
        SorobanExpr::FieldAccess { object, .. } => substitute_local_in_expr(object, idx, value),
        // Storage
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => substitute_local_in_expr(key, idx, value),
        SorobanExpr::StorageSet {
            key, value: val, ..
        } => substitute_local_in_expr(key, idx, value) || substitute_local_in_expr(val, idx, value),
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            substitute_local_in_expr(key, idx, value)
                || substitute_local_in_expr(threshold, idx, value)
                || substitute_local_in_expr(extend_to, idx, value)
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            substitute_local_in_expr(threshold, idx, value)
                || substitute_local_in_expr(extend_to, idx, value)
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            substitute_local_in_expr(address, idx, value)
                || substitute_local_in_expr(args, idx, value)
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            for t in topics.iter_mut() {
                if substitute_local_in_expr(t, idx, value) {
                    return true;
                }
            }
            substitute_local_in_expr(data, idx, value)
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
            if substitute_local_in_expr(address, idx, value) {
                return true;
            }
            if substitute_local_in_expr(function, idx, value) {
                return true;
            }
            for a in args.iter_mut() {
                if substitute_local_in_expr(a, idx, value) {
                    return true;
                }
            }
            false
        }
        SorobanExpr::StructConstruct { fields, .. } => {
            for (_, v) in fields.iter_mut() {
                if substitute_local_in_expr(v, idx, value) {
                    return true;
                }
            }
            false
        }
        SorobanExpr::EnumConstruct { fields, .. } => {
            for f in fields.iter_mut() {
                if substitute_local_in_expr(f, idx, value) {
                    return true;
                }
            }
            false
        }
        SorobanExpr::TupleConstruct(items) | SorobanExpr::VecConstruct(items) => {
            for item in items.iter_mut() {
                if substitute_local_in_expr(item, idx, value) {
                    return true;
                }
            }
            false
        }
        SorobanExpr::MapConstruct(pairs) => {
            for (k, v) in pairs.iter_mut() {
                if substitute_local_in_expr(k, idx, value) {
                    return true;
                }
                if substitute_local_in_expr(v, idx, value) {
                    return true;
                }
            }
            false
        }
        SorobanExpr::MethodCall { object, args, .. } => {
            if substitute_local_in_expr(object, idx, value) {
                return true;
            }
            for a in args.iter_mut() {
                if substitute_local_in_expr(a, idx, value) {
                    return true;
                }
            }
            false
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            substitute_local_in_expr(public_key, idx, value)
                || substitute_local_in_expr(message, idx, value)
                || substitute_local_in_expr(signature, idx, value)
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            substitute_local_in_expr(msg_digest, idx, value)
                || substitute_local_in_expr(signature, idx, value)
                || substitute_local_in_expr(recovery_id, idx, value)
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            substitute_local_in_expr(low, idx, value) || substitute_local_in_expr(high, idx, value)
        }
        SorobanExpr::Log(args) | SorobanExpr::RawHostCall { args, .. } => {
            for a in args.iter_mut() {
                if substitute_local_in_expr(a, idx, value) {
                    return true;
                }
            }
            false
        }
        // Leaves: literals, Param, Env, LedgerX, ContractError, etc.
        _ => false,
    }
}

/// Returns true for expressions that call out to the host environment or have
/// observable side effects.  Such lets are never inlined (even with one use)
/// because moving the call from a guaranteed-execute position into a
/// conditional branch would change semantics.
fn expr_has_side_effects(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::StorageGet { .. }
            | SorobanExpr::StorageSet { .. }
            | SorobanExpr::StorageHas { .. }
            | SorobanExpr::StorageRemove { .. }
            | SorobanExpr::StorageExtendTtl { .. }
            | SorobanExpr::ExtendInstanceAndCodeTtl { .. }
            | SorobanExpr::RequireAuth(_)
            | SorobanExpr::RequireAuthForArgs { .. }
            | SorobanExpr::AuthorizeAsCurrContract(_)
            | SorobanExpr::PublishEvent { .. }
            | SorobanExpr::InvokeContract { .. }
            | SorobanExpr::TryInvokeContract { .. }
            | SorobanExpr::RawHostCall { .. }
            | SorobanExpr::PrngReseed(_)
            | SorobanExpr::PrngBytesNew(_)
            | SorobanExpr::PrngU64InRange { .. }
            | SorobanExpr::PrngVecShuffle(_)
            | SorobanExpr::Log(_)
    ) || matches!(
        expr,
        SorobanExpr::MethodCall { method, .. } if method != "len" && method != "id" && method != "address"
    )
    // Pure reads: LedgerSequence, LedgerTimestamp, LedgerNetworkId,
    // CurrentContractAddress, MaxLiveUntilLedger, StrkeyToAddress,
    // AddressToStrkey — these don't modify state and can be safely
    // inlined or dropped if unused.
}

// ---------------------------------------------------------------------------
// Recover storage keys from match scrutinees
// ---------------------------------------------------------------------------

/// When a `match param { EnumVariant => storage_op(&todo!("unknown value")) }` pattern
/// is found, replace the unknown storage key with the match scrutinee.
/// Replace `Void` and `UnknownVal` with `None` in struct/event fields that are
/// typed `Option<T>` in the XDR spec. This runs after the main optimizer since
/// it needs access to the `TypeRegistry`.
pub fn replace_void_with_none_in_option_fields(
    stmts: Vec<SorobanStmt>,
    registry: &crate::spec::registry::TypeRegistry,
) -> Vec<SorobanStmt> {
    stmts
        .into_iter()
        .map(|s| void_to_none_stmt(s, registry))
        .collect()
}

fn void_to_none_stmt(
    stmt: SorobanStmt,
    registry: &crate::spec::registry::TypeRegistry,
) -> SorobanStmt {
    match stmt {
        SorobanStmt::Let {
            name,
            mutable,
            value,
        } => SorobanStmt::Let {
            name,
            mutable,
            value: void_to_none_expr(value, registry),
        },
        SorobanStmt::Assign { target, value } => SorobanStmt::Assign {
            target,
            value: void_to_none_expr(value, registry),
        },
        SorobanStmt::Return(Some(expr)) => {
            SorobanStmt::Return(Some(void_to_none_expr(expr, registry)))
        }
        SorobanStmt::Expr(expr) => SorobanStmt::Expr(void_to_none_expr(expr, registry)),
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition: void_to_none_expr(condition, registry),
            then_body: replace_void_with_none_in_option_fields(then_body, registry),
            else_body: replace_void_with_none_in_option_fields(else_body, registry),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee: void_to_none_expr(scrutinee, registry),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: replace_void_with_none_in_option_fields(arm.body, registry),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: replace_void_with_none_in_option_fields(body, registry),
        },
        SorobanStmt::Block(stmts) => {
            SorobanStmt::Block(replace_void_with_none_in_option_fields(stmts, registry))
        }
        other => other,
    }
}

fn void_to_none_expr(
    expr: SorobanExpr,
    registry: &crate::spec::registry::TypeRegistry,
) -> SorobanExpr {
    match expr {
        SorobanExpr::StructConstruct { type_name, fields } => {
            let new_fields = fields
                .into_iter()
                .map(|(name, value)| {
                    let value = void_to_none_expr(value, registry);
                    if is_void_or_unknown(&value) && is_option_field(registry, &type_name, &name) {
                        return (name, SorobanExpr::None);
                    }
                    (name, value)
                })
                .collect();
            SorobanExpr::StructConstruct {
                type_name,
                fields: new_fields,
            }
        }
        SorobanExpr::PublishEvent {
            event_name,
            topics,
            data,
        } => SorobanExpr::PublishEvent {
            event_name,
            topics: topics
                .into_iter()
                .map(|e| void_to_none_expr(e, registry))
                .collect(),
            data: Box::new(void_to_none_expr(*data, registry)),
        },
        // Recurse into method calls to catch structs inside publish() args etc.
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } => SorobanExpr::MethodCall {
            object: Box::new(void_to_none_expr(*object, registry)),
            method,
            args: args
                .into_iter()
                .map(|a| void_to_none_expr(a, registry))
                .collect(),
        },
        SorobanExpr::TupleConstruct(fields) => SorobanExpr::TupleConstruct(
            fields
                .into_iter()
                .map(|f| void_to_none_expr(f, registry))
                .collect(),
        ),
        SorobanExpr::VecConstruct(elements) => SorobanExpr::VecConstruct(
            elements
                .into_iter()
                .map(|e| void_to_none_expr(e, registry))
                .collect(),
        ),
        other => other,
    }
}

/// Check if an expression is Void, UnknownVal, or a ValConvert wrapping one of those.
fn is_void_or_unknown(expr: &SorobanExpr) -> bool {
    match expr {
        SorobanExpr::Void | SorobanExpr::UnknownVal => true,
        SorobanExpr::ValConvert { value, .. } => is_void_or_unknown(value),
        _ => false,
    }
}

/// Check if a field in a struct or event is typed `Option<T>` in the XDR spec.
fn is_option_field(
    registry: &crate::spec::registry::TypeRegistry,
    type_name: &str,
    field_name: &str,
) -> bool {
    use stellar_xdr::curr::ScSpecTypeDef;
    // Check structs
    if let Some(spec) = registry.structs.get(type_name) {
        for field in spec.fields.iter() {
            if let Ok(name) = field.name.to_utf8_string()
                && name == field_name
            {
                return matches!(field.type_, ScSpecTypeDef::Option(_));
            }
        }
    }
    // Check events (params)
    if let Some(spec) = registry.events.get(type_name) {
        for param in spec.params.iter() {
            if let Ok(name) = param.name.to_utf8_string()
                && name == field_name
            {
                return matches!(param.type_, ScSpecTypeDef::Option(_));
            }
        }
    }
    false
}

///
/// This is safe because Soroban SDK match-on-DataKey patterns always pass the
/// matched parameter as the storage key within each arm.
pub fn recover_match_arm_storage_keys(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    stmts.into_iter().map(recover_keys_in_stmt).collect()
}

fn recover_keys_in_stmt(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::Match { scrutinee, arms } => {
            let has_enum_arms = arms
                .iter()
                .any(|arm| matches!(arm.pattern, MatchPattern::EnumVariant { .. }));

            if has_enum_arms && let SorobanExpr::Param(ref param_name) = scrutinee {
                let replacement = SorobanExpr::Param(param_name.clone());
                // Narrow the rewrite: only replace UnknownVal storage keys in
                // arms that have no references to other params. If an arm
                // mentions another param, the lifter most likely lost a key
                // computed from that other param — substituting the scrutinee
                // would silently attribute storage to the wrong key.
                let mut arms: Vec<MatchArm> = arms
                    .into_iter()
                    .map(|arm| {
                        let mentions_other_params =
                            arm_mentions_other_params(&arm.body, param_name);
                        let body = if mentions_other_params {
                            arm.body
                        } else {
                            replace_unknown_storage_keys(arm.body, &replacement)
                        };
                        MatchArm {
                            pattern: arm.pattern,
                            body,
                        }
                    })
                    .collect();
                // A uniform storage-dispatch match (e.g. `constructor::get_data`) may
                // come back with some arms empty because WASM LTO merged the per-tier
                // reads — fill them from the surviving arm.
                fill_empty_storage_dispatch_arms(&mut arms);
                return SorobanStmt::Match { scrutinee, arms };
            }
            // Recurse into arms even if no substitution
            SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: recover_match_arm_storage_keys(arm.body),
                    })
                    .collect(),
            }
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: recover_match_arm_storage_keys(then_body),
            else_body: recover_match_arm_storage_keys(else_body),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: recover_match_arm_storage_keys(body),
        },
        SorobanStmt::Block(stmts) => SorobanStmt::Block(recover_match_arm_storage_keys(stmts)),
        other => other,
    }
}

/// Fill empty arms of a uniform storage-dispatch match.
///
/// `constructor::get_data` lowers to
/// `match key { DataKey::Persistent(_) => env.storage().persistent().get(&key),
///              DataKey::Temp(_)       => env.storage().temporary().get(&key),
///              DataKey::Instance(_)   => env.storage().instance().get(&key) }`,
/// but WASM LTO merges the three per-tier reads into one site, so the lifter recovers a
/// `StorageGet` for only one arm; the others come back empty and codegen renders them
/// `()`, breaking the `Option<i64>` return. When every non-empty arm is a single
/// `StorageGet`, clone that surviving read into each empty arm, picking the tier from the
/// arm's enum-variant name so the faithful `persistent()`/`temporary()`/`instance()` is
/// restored (falling back to the template's tier for an unrecognized name, which still
/// compiles). `unwrap` follows the template; pipeline stage 4e later normalizes it to
/// `false` for `Option`-returning functions.
fn fill_empty_storage_dispatch_arms(arms: &mut [MatchArm]) {
    // Template: an arm whose body is exactly one `Expr(StorageGet { .. })`.
    let template = arms.iter().find_map(|arm| match arm.body.as_slice() {
        [SorobanStmt::Expr(sg @ SorobanExpr::StorageGet { .. })] => Some(sg.clone()),
        _ => None,
    });
    let Some(SorobanExpr::StorageGet {
        storage_type: tmpl_type,
        key,
        unwrap,
    }) = template
    else {
        return;
    };

    // Only act on a uniform storage-dispatch match: at least one empty arm to fill, and
    // every non-empty arm is itself a single `StorageGet`. This keeps the rewrite from
    // touching any match that merely happens to contain a storage read.
    if !arms.iter().any(|arm| arm.body.is_empty()) {
        return;
    }
    let all_nonempty_are_storage_get = arms.iter().filter(|arm| !arm.body.is_empty()).all(|arm| {
        matches!(
            arm.body.as_slice(),
            [SorobanStmt::Expr(SorobanExpr::StorageGet { .. })]
        )
    });
    if !all_nonempty_are_storage_get {
        return;
    }

    for arm in arms.iter_mut() {
        if !arm.body.is_empty() {
            continue;
        }
        let storage_type = match &arm.pattern {
            MatchPattern::EnumVariant { variant, .. } => {
                storage_type_from_variant(variant).unwrap_or(tmpl_type)
            }
            _ => tmpl_type,
        };
        cov_mark::hit!(storage_dispatch_arm_filled);
        arm.body = vec![SorobanStmt::Expr(SorobanExpr::StorageGet {
            storage_type,
            key: key.clone(),
            unwrap,
        })];
    }
}

/// Map a storage-key enum variant name to its storage tier, following the
/// `DataKey::{Persistent,Temp,Instance}` convention.
fn storage_type_from_variant(variant: &str) -> Option<StorageType> {
    let v = variant.to_ascii_lowercase();
    if v.contains("persist") {
        Some(StorageType::Persistent)
    } else if v.contains("temp") {
        Some(StorageType::Temporary)
    } else if v.contains("instance") {
        Some(StorageType::Instance)
    } else {
        None
    }
}

/// Replace `UnknownVal` in storage key positions with `replacement`.
fn replace_unknown_storage_keys(
    stmts: Vec<SorobanStmt>,
    replacement: &SorobanExpr,
) -> Vec<SorobanStmt> {
    stmts
        .into_iter()
        .map(|stmt| replace_unknown_keys_in_stmt(stmt, replacement))
        .collect()
}

fn replace_unknown_keys_in_stmt(stmt: SorobanStmt, replacement: &SorobanExpr) -> SorobanStmt {
    match stmt {
        SorobanStmt::Expr(expr) => {
            SorobanStmt::Expr(replace_unknown_keys_in_expr(expr, replacement))
        }
        SorobanStmt::Let {
            name,
            mutable,
            value,
        } => SorobanStmt::Let {
            name,
            mutable,
            value: replace_unknown_keys_in_expr(value, replacement),
        },
        SorobanStmt::Return(Some(expr)) => {
            SorobanStmt::Return(Some(replace_unknown_keys_in_expr(expr, replacement)))
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: replace_unknown_storage_keys(then_body, replacement),
            else_body: replace_unknown_storage_keys(else_body, replacement),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: replace_unknown_storage_keys(arm.body, replacement),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: replace_unknown_storage_keys(body, replacement),
        },
        SorobanStmt::Block(stmts) => {
            SorobanStmt::Block(replace_unknown_storage_keys(stmts, replacement))
        }
        SorobanStmt::Assign { target, value } => SorobanStmt::Assign {
            target,
            value: replace_unknown_keys_in_expr(value, replacement),
        },
        other => other,
    }
}

/// Return true if any expression in the body references a `SorobanExpr::Param`
/// whose name differs from `excluded`. Used to detect arms whose unknown
/// storage key was likely composed from a different parameter than the
/// matched scrutinee — those arms must NOT have their key rewritten.
fn arm_mentions_other_params(body: &[SorobanStmt], excluded: &str) -> bool {
    body.iter().any(|s| stmt_mentions_other_params(s, excluded))
}

fn stmt_mentions_other_params(stmt: &SorobanStmt, excluded: &str) -> bool {
    match stmt {
        SorobanStmt::Expr(e)
        | SorobanStmt::Let { value: e, .. }
        | SorobanStmt::Assign { value: e, .. } => expr_mentions_other_params(e, excluded),
        SorobanStmt::Return(Some(e)) => expr_mentions_other_params(e, excluded),
        SorobanStmt::Return(None)
        | SorobanStmt::Break
        | SorobanStmt::Continue
        | SorobanStmt::Comment(_) => false,
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            expr_mentions_other_params(condition, excluded)
                || arm_mentions_other_params(then_body, excluded)
                || arm_mentions_other_params(else_body, excluded)
        }
        SorobanStmt::Match { scrutinee, arms } => {
            expr_mentions_other_params(scrutinee, excluded)
                || arms
                    .iter()
                    .any(|a| arm_mentions_other_params(&a.body, excluded))
        }
        SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
            arm_mentions_other_params(body, excluded)
        }
        SorobanStmt::For {
            start, end, body, ..
        } => {
            expr_mentions_other_params(start, excluded)
                || expr_mentions_other_params(end, excluded)
                || arm_mentions_other_params(body, excluded)
        }
    }
}

fn expr_mentions_other_params(expr: &SorobanExpr, excluded: &str) -> bool {
    match expr {
        SorobanExpr::Param(name) => name != excluded,
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
            expr_mentions_other_params(a, excluded) || expr_mentions_other_params(b, excluded)
        }
        SorobanExpr::Not(inner)
        | SorobanExpr::RequireAuth(inner)
        | SorobanExpr::AuthorizeAsCurrContract(inner)
        | SorobanExpr::PanicWithError(inner)
        | SorobanExpr::CryptoSha256(inner)
        | SorobanExpr::CryptoKeccak256(inner)
        | SorobanExpr::PrngReseed(inner)
        | SorobanExpr::PrngBytesNew(inner)
        | SorobanExpr::PrngVecShuffle(inner)
        | SorobanExpr::StrkeyToAddress(inner)
        | SorobanExpr::AddressToStrkey(inner)
        | SorobanExpr::FieldAccess { object: inner, .. }
        | SorobanExpr::ValConvert { value: inner, .. }
        | SorobanExpr::CastAs { value: inner, .. }
        | SorobanExpr::ValTag(inner)
        | SorobanExpr::Some(inner)
        | SorobanExpr::SretResult(inner)
        | SorobanExpr::ErrorFromCode(inner) => expr_mentions_other_params(inner, excluded),
        SorobanExpr::MethodCall { object, args, .. } => {
            expr_mentions_other_params(object, excluded)
                || args.iter().any(|a| expr_mentions_other_params(a, excluded))
        }
        SorobanExpr::VecTryIterFold { vec, init } => {
            expr_mentions_other_params(vec, excluded) || expr_mentions_other_params(init, excluded)
        }
        SorobanExpr::StorageGet { key, .. }
        | SorobanExpr::StorageHas { key, .. }
        | SorobanExpr::StorageRemove { key, .. } => expr_mentions_other_params(key, excluded),
        SorobanExpr::StorageSet { key, value, .. } => {
            expr_mentions_other_params(key, excluded) || expr_mentions_other_params(value, excluded)
        }
        SorobanExpr::StorageExtendTtl {
            key,
            threshold,
            extend_to,
            ..
        } => {
            expr_mentions_other_params(key, excluded)
                || expr_mentions_other_params(threshold, excluded)
                || expr_mentions_other_params(extend_to, excluded)
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            expr_mentions_other_params(threshold, excluded)
                || expr_mentions_other_params(extend_to, excluded)
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            expr_mentions_other_params(address, excluded)
                || expr_mentions_other_params(args, excluded)
        }
        SorobanExpr::PublishEvent { topics, data, .. } => {
            topics
                .iter()
                .any(|t| expr_mentions_other_params(t, excluded))
                || expr_mentions_other_params(data, excluded)
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
            expr_mentions_other_params(address, excluded)
                || expr_mentions_other_params(function, excluded)
                || args.iter().any(|a| expr_mentions_other_params(a, excluded))
        }
        SorobanExpr::StructConstruct { fields, .. } => fields
            .iter()
            .any(|(_, v)| expr_mentions_other_params(v, excluded)),
        SorobanExpr::EnumConstruct { fields, .. }
        | SorobanExpr::TupleConstruct(fields)
        | SorobanExpr::VecConstruct(fields)
        | SorobanExpr::Log(fields)
        | SorobanExpr::RawHostCall { args: fields, .. } => fields
            .iter()
            .any(|v| expr_mentions_other_params(v, excluded)),
        SorobanExpr::MapConstruct(entries) => entries.iter().any(|(k, v)| {
            expr_mentions_other_params(k, excluded) || expr_mentions_other_params(v, excluded)
        }),
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            expr_mentions_other_params(public_key, excluded)
                || expr_mentions_other_params(message, excluded)
                || expr_mentions_other_params(signature, excluded)
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            expr_mentions_other_params(msg_digest, excluded)
                || expr_mentions_other_params(signature, excluded)
                || expr_mentions_other_params(recovery_id, excluded)
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            expr_mentions_other_params(low, excluded) || expr_mentions_other_params(high, excluded)
        }
        // Leaves with no Param children.
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
        | SorobanExpr::CyclicSlot { .. }
        | SorobanExpr::ValTagName(_)
        | SorobanExpr::ContractError { .. } => false,
    }
}

fn is_enum_construct_with_unknown(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::EnumConstruct { fields, .. }
            if fields.contains(&SorobanExpr::UnknownVal)
    )
}

fn replace_unknown_keys_in_expr(expr: SorobanExpr, replacement: &SorobanExpr) -> SorobanExpr {
    match expr {
        SorobanExpr::StorageGet {
            storage_type,
            key,
            unwrap,
        } if *key == SorobanExpr::UnknownVal || is_enum_construct_with_unknown(&key) => {
            SorobanExpr::StorageGet {
                storage_type,
                key: Box::new(replacement.clone()),
                unwrap,
            }
        }
        SorobanExpr::StorageSet {
            storage_type,
            key,
            value,
        } if *key == SorobanExpr::UnknownVal || is_enum_construct_with_unknown(&key) => {
            SorobanExpr::StorageSet {
                storage_type,
                key: Box::new(replacement.clone()),
                value,
            }
        }
        SorobanExpr::StorageHas { storage_type, key }
            if *key == SorobanExpr::UnknownVal || is_enum_construct_with_unknown(&key) =>
        {
            SorobanExpr::StorageHas {
                storage_type,
                key: Box::new(replacement.clone()),
            }
        }
        SorobanExpr::StorageRemove { storage_type, key }
            if *key == SorobanExpr::UnknownVal || is_enum_construct_with_unknown(&key) =>
        {
            SorobanExpr::StorageRemove {
                storage_type,
                key: Box::new(replacement.clone()),
            }
        }
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Variable Name Propagation
// ---------------------------------------------------------------------------

/// Propagate meaningful names to `var_N` bindings based on their value expressions.
///
/// Uses spec-derived parameter names and expression context to replace generic
/// `var_N` names with descriptive alternatives. Also renames all references
/// (Local(N) → Local with new name) throughout the statement tree.
pub fn propagate_variable_names(
    stmts: Vec<SorobanStmt>,
    reserved_names: &[String],
) -> Vec<SorobanStmt> {
    use std::collections::HashMap;

    let mut used_names: std::collections::HashSet<String> = std::collections::HashSet::new();
    // Seed with reserved names (function parameters) to prevent shadowing.
    for name in reserved_names {
        used_names.insert(name.clone());
    }
    collect_used_names(&stmts, &mut used_names);

    // Pre-pass: detect let-match pairs where `let mut var_N = init` is followed
    // by `Match { scrutinee: Param(p), arms all assign to var_N }`. Derive the
    // variable name from the match scrutinee instead of the init value.
    let mut let_match_names: HashMap<String, String> = HashMap::new();
    for w in stmts.windows(2) {
        if let (
            SorobanStmt::Let {
                name,
                mutable: true,
                ..
            },
            SorobanStmt::Match { scrutinee, arms },
        ) = (&w[0], &w[1])
            && name.starts_with("var_")
            && !arms.is_empty() && arms.iter().all(|arm| {
            arm.body.is_empty()
                || (arm.body.len() == 1
                    && matches!(&arm.body[0], SorobanStmt::Assign { target, .. } if target == name))
        }) && let Some(derived) = derive_name_from_expr(scrutinee)
        {
            let_match_names.insert(name.clone(), derived);
        }
    }

    // Streaming approach: process each statement sequentially, accumulating
    // renames as we go. This correctly handles shadowed var_N bindings —
    // each Let gets its own derived name and subsequent references use the
    // latest rename.
    let mut active_renames: HashMap<String, String> = HashMap::new();
    let mut any_rename = false;

    let result: Vec<SorobanStmt> = stmts
        .into_iter()
        .map(|stmt| {
            // Derive a name from the ORIGINAL value (before renames), so the
            // semantic meaning drives naming, not previously renamed variables.
            let new_rename = if let SorobanStmt::Let {
                ref name,
                ref value,
                ..
            } = stmt
            {
                if name.starts_with("var_") {
                    // First try let-match scrutinee name, then fall back to value-based
                    let derived = let_match_names
                        .get(name)
                        .cloned()
                        .or_else(|| derive_name_from_expr(value));
                    derived.and_then(|new_name| {
                        let final_name = if used_names.contains(&new_name) {
                            // For void enum constructs used as storage keys,
                            // use "_key" suffix instead of "_N" for readability.
                            // E.g., DataKey::Admin with param "admin" → "admin_key"
                            let candidate = if matches!(
                                value,
                                SorobanExpr::EnumConstruct { fields, .. } if fields.is_empty()
                            ) {
                                format!("{}_key", new_name)
                            } else {
                                format!("{}_{}", new_name, name.trim_start_matches("var_"))
                            };
                            if used_names.contains(&candidate) {
                                return None; // give up
                            }
                            candidate
                        } else {
                            new_name
                        };
                        if final_name != *name {
                            used_names.insert(final_name.clone());
                            Some((name.clone(), final_name))
                        } else {
                            None
                        }
                    })
                } else {
                    None
                }
            } else {
                None
            };

            // Apply existing renames to this statement
            let stmt = if !active_renames.is_empty() {
                rename_in_stmt(stmt, &active_renames)
            } else {
                stmt
            };

            // Add new rename and override the Let name with the derived name.
            // The Let name may have been changed by rename_in_stmt (from an
            // earlier rename for the same var_N), so we set it explicitly.
            if let Some((old_name, new_name)) = new_rename {
                active_renames.insert(old_name, new_name.clone());
                any_rename = true;
                if let SorobanStmt::Let { mutable, value, .. } = stmt {
                    return SorobanStmt::Let {
                        name: new_name,
                        mutable,
                        value,
                    };
                }
            }

            stmt
        })
        .collect();

    // Recurse into nested statement bodies (If/Match/Loop/Block) to rename
    // var_N bindings that appear inside conditional/loop blocks, not just
    // at the top level.
    result
        .into_iter()
        .map(|stmt| propagate_names_in_nested(stmt, reserved_names))
        .collect()
}

/// Recursively apply `propagate_variable_names` to nested statement bodies.
fn propagate_names_in_nested(stmt: SorobanStmt, reserved_names: &[String]) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: propagate_variable_names(then_body, reserved_names),
            else_body: propagate_variable_names(else_body, reserved_names),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| crate::ir::soroban_ir::MatchArm {
                    body: propagate_variable_names(arm.body, reserved_names),
                    ..arm
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: propagate_variable_names(body, reserved_names),
        },
        SorobanStmt::Block(body) => {
            SorobanStmt::Block(propagate_variable_names(body, reserved_names))
        }
        other => other,
    }
}

/// Convert a CamelCase identifier to snake_case.
fn camel_to_snake(s: &str) -> String {
    let mut result = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() {
            if i > 0 {
                result.push('_');
            }
            result.push(c.to_lowercase().next().unwrap());
        } else {
            result.push(c);
        }
    }
    result
}

/// Derive a meaningful variable name from an expression.
fn derive_name_from_expr(expr: &SorobanExpr) -> Option<String> {
    match expr {
        // Direct parameter reference → use param name
        SorobanExpr::Param(name) => Some(name.clone()),

        // Field access → use field name
        SorobanExpr::FieldAccess { field, .. } => Some(field.clone()),

        // Storage get → derive from key.  CamelCase symbol keys (e.g., "Offer")
        // are lowercased to produce valid Rust variable names ("offer").
        SorobanExpr::StorageGet { key, .. } => match key.as_ref() {
            SorobanExpr::SymbolLiteral(sym) => {
                if sym.chars().next().is_some_and(|c| c.is_uppercase())
                    && sym.chars().any(|c| c.is_lowercase())
                {
                    Some(camel_to_snake(sym))
                } else {
                    Some(sym.clone())
                }
            }
            SorobanExpr::EnumConstruct { variant, .. } => Some(camel_to_snake(variant)),
            SorobanExpr::NamedLocal(name) => Some(name.clone()),
            // VecConstruct key: derive from the first meaningful element.
            // E.g., vec![DataKey::Balance] → "balance"
            SorobanExpr::VecConstruct(elems) => elems.iter().find_map(|e| match e {
                SorobanExpr::EnumConstruct { variant, .. } => Some(camel_to_snake(variant)),
                SorobanExpr::SymbolLiteral(s) => Some(camel_to_snake(s)),
                _ => None,
            }),
            _ => None,
        },

        // ValConvert / CastAs — derive name from inner value
        SorobanExpr::ValConvert { value, .. } | SorobanExpr::CastAs { value, .. } => {
            derive_name_from_expr(value)
        }

        // Method call → derive from method name for specific patterns
        SorobanExpr::MethodCall { method, object, .. } => {
            match method.as_str() {
                "len" => Some("len".to_string()),
                "ledger" => Some("ledger".to_string()),
                "timestamp" => Some("timestamp".to_string()),
                "sequence" => Some("sequence".to_string()),
                // env.crypto() chain → crypto
                "crypto" => Some("crypto".to_string()),
                // object.get(N) → derive from object + index
                "get" => derive_name_from_expr(object).map(|n| format!("{}_elem", n)),
                // address/id on MuxedAddress — use method name
                "address" => Some("address".to_string()),
                "id" => Some("id".to_string()),
                // Crypto: BLS12-381 / BN254 operations
                "g1_mul" | "map_fp_to_g1" => Some("g1".to_string()),
                "g2_mul" | "map_fp2_to_g2" => Some("g2".to_string()),
                "g1_add" => Some("g1_sum".to_string()),
                "g2_add" => Some("g2_sum".to_string()),
                "pairing_check" => Some("pairing_ok".to_string()),
                // Crypto: hashing / signatures
                "sha256" => Some("hash".to_string()),
                "keccak256" => Some("hash".to_string()),
                // unwrap → delegate to inner expression
                "unwrap" => derive_name_from_expr(object),
                _ => None,
            }
        }

        // Crypto expressions (direct variants, not MethodCall)
        SorobanExpr::CryptoSha256(_) | SorobanExpr::CryptoKeccak256(_) => Some("hash".to_string()),
        SorobanExpr::CryptoEd25519Verify { .. } | SorobanExpr::CryptoSecp256k1Recover { .. } => {
            Some("verified".to_string())
        }

        // Ledger / address
        SorobanExpr::CurrentContractAddress => Some("self_addr".to_string()),
        SorobanExpr::LedgerSequence => Some("sequence".to_string()),
        SorobanExpr::LedgerTimestamp => Some("timestamp".to_string()),
        SorobanExpr::LedgerNetworkId => Some("network_id".to_string()),
        SorobanExpr::MaxLiveUntilLedger => Some("max_live_until".to_string()),

        // Cross-contract call → derive from called function name
        SorobanExpr::InvokeContract { function, .. }
        | SorobanExpr::TryInvokeContract { function, .. } => {
            if let SorobanExpr::SymbolLiteral(name) = function.as_ref() {
                Some(name.clone())
            } else {
                None
            }
        }

        // Address operations
        SorobanExpr::AddressToStrkey(_) => Some("strkey".to_string()),
        SorobanExpr::StrkeyToAddress(_) => Some("address".to_string()),

        // PRNG
        SorobanExpr::PrngU64InRange { .. } => Some("random".to_string()),
        SorobanExpr::PrngBytesNew(_) => Some("random_bytes".to_string()),

        // Storage has → "exists"
        SorobanExpr::StorageHas { .. } => Some("exists".to_string()),

        // Type construction → use type/variant name in snake_case
        SorobanExpr::StructConstruct { type_name, .. } => Some(camel_to_snake(type_name)),
        SorobanExpr::EnumConstruct { variant, .. } => Some(camel_to_snake(variant)),

        // Vec construct → derive from single element content, or use "vp" fallback
        SorobanExpr::VecConstruct(elems) => {
            if elems.len() == 1 {
                Some(
                    derive_name_from_expr(&elems[0])
                        .map(|n| format!("{}_vec", n))
                        .unwrap_or_else(|| "vp".to_string()),
                )
            } else {
                None
            }
        }

        // Collection constructors
        SorobanExpr::CollectionNew(ty_name) => match ty_name.as_str() {
            "Vec" => Some("vec".to_string()),
            "Map" => Some("map".to_string()),
            _ => Some(camel_to_snake(ty_name)),
        },

        // Error → "error"
        SorobanExpr::ContractError { .. } | SorobanExpr::ErrorFromCode(_) => {
            Some("error".to_string())
        }

        _ => None,
    }
}

/// Collect all non-var names already used in the statement tree.
fn collect_used_names(stmts: &[SorobanStmt], names: &mut std::collections::HashSet<String>) {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Let { name, .. } => {
                names.insert(name.clone());
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_used_names(then_body, names);
                collect_used_names(else_body, names);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms {
                    collect_used_names(&arm.body, names);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                collect_used_names(body, names);
            }
            _ => {}
        }
    }
}

/// De-shadow variable names: when multiple Let bindings have the same name,
/// rename later ones to `name_2`, `name_3`, etc. and update references.
/// This only processes top-level statements (not nested scopes where shadowing
/// within a nested block is intentional).
fn deshadow_variable_names(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    use std::collections::{HashMap, HashSet};

    // Pre-collect every top-level binding name so a generated `_N` suffix never
    // collides with a name defined *elsewhere* in the body. Without this a
    // lifter-produced `var_2_5_4_3` could collide with a generated
    // `var_2_5_4_3` candidate and get re-suffixed on every fixpoint iteration —
    // a non-idempotency that the issue #12 body recovery exposed.
    let mut used: HashSet<String> = HashSet::new();
    for stmt in &stmts {
        if let SorobanStmt::Let { name, .. } = stmt {
            used.insert(name.clone());
        }
    }

    // Single forward pass: the first binding of a name keeps it; every later
    // shadow gets its own fresh, globally-unique name (each occurrence distinct —
    // the old name→single-rename map collapsed 3+ shadows onto one name, which
    // re-shadowed and oscillated). `active` rewrites downstream references.
    let mut bound_once: HashSet<String> = HashSet::new();
    let mut active: HashMap<String, String> = HashMap::new();
    stmts
        .into_iter()
        .map(|stmt| {
            if let SorobanStmt::Let { ref name, .. } = stmt {
                if bound_once.contains(name) {
                    let base = name.clone();
                    let mut suffix = 2u32;
                    let mut candidate = format!("{}_{}", base, suffix);
                    while used.contains(&candidate) {
                        suffix += 1;
                        candidate = format!("{}_{}", base, suffix);
                    }
                    used.insert(candidate.clone());
                    active.insert(base, candidate);
                    // Applies the new rename to this Let's binding name (and any
                    // earlier active renames to its value).
                    return rename_in_stmt(stmt, &active);
                }
                bound_once.insert(name.clone());
            }
            if active.is_empty() {
                stmt
            } else {
                rename_in_stmt(stmt, &active)
            }
        })
        .collect()
}

/// Rename variable references in a statement.
fn rename_in_stmt(
    stmt: SorobanStmt,
    renames: &std::collections::HashMap<String, String>,
) -> SorobanStmt {
    match stmt {
        SorobanStmt::Let {
            name,
            mutable,
            value,
        } => {
            let new_name = renames.get(&name).cloned().unwrap_or(name);
            SorobanStmt::Let {
                name: new_name,
                mutable,
                value: rename_in_expr(value, renames),
            }
        }
        SorobanStmt::Assign { target, value } => {
            let new_target = renames.get(&target).cloned().unwrap_or(target);
            SorobanStmt::Assign {
                target: new_target,
                value: rename_in_expr(value, renames),
            }
        }
        SorobanStmt::Expr(e) => SorobanStmt::Expr(rename_in_expr(e, renames)),
        SorobanStmt::Return(Some(e)) => SorobanStmt::Return(Some(rename_in_expr(e, renames))),
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition: rename_in_expr(condition, renames),
            then_body: then_body
                .into_iter()
                .map(|s| rename_in_stmt(s, renames))
                .collect(),
            else_body: else_body
                .into_iter()
                .map(|s| rename_in_stmt(s, renames))
                .collect(),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee: rename_in_expr(scrutinee, renames),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: arm
                        .body
                        .into_iter()
                        .map(|s| rename_in_stmt(s, renames))
                        .collect(),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: body
                .into_iter()
                .map(|s| rename_in_stmt(s, renames))
                .collect(),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(
            body.into_iter()
                .map(|s| rename_in_stmt(s, renames))
                .collect(),
        ),
        other => other,
    }
}

/// Rename variable references in an expression.
fn rename_in_expr(
    expr: SorobanExpr,
    renames: &std::collections::HashMap<String, String>,
) -> SorobanExpr {
    let r = |e: SorobanExpr| rename_in_expr(e, renames);
    let rb = |e: Box<SorobanExpr>| Box::new(r(*e));
    let rv = |v: Vec<SorobanExpr>| v.into_iter().map(&r).collect();

    match expr {
        SorobanExpr::Local(idx) => {
            let old_name = format!("var_{}", idx);
            if let Some(new_name) = renames.get(&old_name) {
                SorobanExpr::NamedLocal(new_name.clone())
            } else {
                SorobanExpr::Local(idx)
            }
        }
        SorobanExpr::NamedLocal(ref name) => {
            if let Some(new_name) = renames.get(name) {
                SorobanExpr::NamedLocal(new_name.clone())
            } else {
                expr
            }
        }
        // Binary operators
        SorobanExpr::Add(a, b) => SorobanExpr::Add(rb(a), rb(b)),
        SorobanExpr::Sub(a, b) => SorobanExpr::Sub(rb(a), rb(b)),
        SorobanExpr::Mul(a, b) => SorobanExpr::Mul(rb(a), rb(b)),
        SorobanExpr::Div(a, b) => SorobanExpr::Div(rb(a), rb(b)),
        SorobanExpr::Rem(a, b) => SorobanExpr::Rem(rb(a), rb(b)),
        SorobanExpr::Eq(a, b) => SorobanExpr::Eq(rb(a), rb(b)),
        SorobanExpr::Ne(a, b) => SorobanExpr::Ne(rb(a), rb(b)),
        SorobanExpr::Lt(a, b) => SorobanExpr::Lt(rb(a), rb(b)),
        SorobanExpr::Le(a, b) => SorobanExpr::Le(rb(a), rb(b)),
        SorobanExpr::Gt(a, b) => SorobanExpr::Gt(rb(a), rb(b)),
        SorobanExpr::Ge(a, b) => SorobanExpr::Ge(rb(a), rb(b)),
        SorobanExpr::And(a, b) => SorobanExpr::And(rb(a), rb(b)),
        SorobanExpr::Or(a, b) => SorobanExpr::Or(rb(a), rb(b)),
        // Unary
        SorobanExpr::Not(e) => SorobanExpr::Not(rb(e)),
        // Composite expressions
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } => SorobanExpr::MethodCall {
            object: rb(object),
            method,
            args: rv(args),
        },
        SorobanExpr::FieldAccess { object, field } => SorobanExpr::FieldAccess {
            object: rb(object),
            field,
        },
        SorobanExpr::ValConvert { value, target_type } => SorobanExpr::ValConvert {
            value: rb(value),
            target_type,
        },
        SorobanExpr::CastAs { value, target_type } => SorobanExpr::CastAs {
            value: rb(value),
            target_type,
        },
        // Storage
        SorobanExpr::StorageGet {
            storage_type,
            key,
            unwrap,
        } => SorobanExpr::StorageGet {
            storage_type,
            key: rb(key),
            unwrap,
        },
        SorobanExpr::StorageSet {
            storage_type,
            key,
            value,
        } => SorobanExpr::StorageSet {
            storage_type,
            key: rb(key),
            value: rb(value),
        },
        SorobanExpr::StorageHas { storage_type, key } => SorobanExpr::StorageHas {
            storage_type,
            key: rb(key),
        },
        SorobanExpr::StorageRemove { storage_type, key } => SorobanExpr::StorageRemove {
            storage_type,
            key: rb(key),
        },
        SorobanExpr::StorageExtendTtl {
            storage_type,
            key,
            threshold,
            extend_to,
        } => SorobanExpr::StorageExtendTtl {
            storage_type,
            key: rb(key),
            threshold: rb(threshold),
            extend_to: rb(extend_to),
        },
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold: rb(threshold),
            extend_to: rb(extend_to),
        },
        // Auth
        SorobanExpr::RequireAuth(a) => SorobanExpr::RequireAuth(rb(a)),
        SorobanExpr::RequireAuthForArgs { address, args } => SorobanExpr::RequireAuthForArgs {
            address: rb(address),
            args: rb(args),
        },
        SorobanExpr::AuthorizeAsCurrContract(a) => SorobanExpr::AuthorizeAsCurrContract(rb(a)),
        // Events
        SorobanExpr::PublishEvent {
            event_name,
            topics,
            data,
        } => SorobanExpr::PublishEvent {
            event_name,
            topics: rv(topics),
            data: rb(data),
        },
        // Cross-contract
        SorobanExpr::InvokeContract {
            address,
            function,
            args,
            return_type,
        } => SorobanExpr::InvokeContract {
            address: rb(address),
            function: rb(function),
            args: rv(args),
            return_type,
        },
        SorobanExpr::TryInvokeContract {
            address,
            function,
            args,
            return_type,
        } => SorobanExpr::TryInvokeContract {
            address: rb(address),
            function: rb(function),
            args: rv(args),
            return_type,
        },
        // Type construction
        SorobanExpr::StructConstruct { type_name, fields } => SorobanExpr::StructConstruct {
            type_name,
            fields: fields.into_iter().map(|(n, v)| (n, r(v))).collect(),
        },
        SorobanExpr::EnumConstruct {
            type_name,
            variant,
            fields,
        } => SorobanExpr::EnumConstruct {
            type_name,
            variant,
            fields: rv(fields),
        },
        SorobanExpr::TupleConstruct(items) => SorobanExpr::TupleConstruct(rv(items)),
        SorobanExpr::VecConstruct(items) => SorobanExpr::VecConstruct(rv(items)),
        SorobanExpr::MapConstruct(pairs) => {
            SorobanExpr::MapConstruct(pairs.into_iter().map(|(k, v)| (r(k), r(v))).collect())
        }
        // Crypto
        SorobanExpr::CryptoSha256(a) => SorobanExpr::CryptoSha256(rb(a)),
        SorobanExpr::CryptoKeccak256(a) => SorobanExpr::CryptoKeccak256(rb(a)),
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => SorobanExpr::CryptoEd25519Verify {
            public_key: rb(public_key),
            message: rb(message),
            signature: rb(signature),
        },
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => SorobanExpr::CryptoSecp256k1Recover {
            msg_digest: rb(msg_digest),
            signature: rb(signature),
            recovery_id: rb(recovery_id),
        },
        // PRNG
        SorobanExpr::PrngReseed(a) => SorobanExpr::PrngReseed(rb(a)),
        SorobanExpr::PrngBytesNew(a) => SorobanExpr::PrngBytesNew(rb(a)),
        SorobanExpr::PrngU64InRange { low, high } => SorobanExpr::PrngU64InRange {
            low: rb(low),
            high: rb(high),
        },
        SorobanExpr::PrngVecShuffle(a) => SorobanExpr::PrngVecShuffle(rb(a)),
        // Address
        SorobanExpr::StrkeyToAddress(a) => SorobanExpr::StrkeyToAddress(rb(a)),
        SorobanExpr::AddressToStrkey(a) => SorobanExpr::AddressToStrkey(rb(a)),
        SorobanExpr::ErrorFromCode(a) => SorobanExpr::ErrorFromCode(rb(a)),
        SorobanExpr::PanicWithError(a) => SorobanExpr::PanicWithError(rb(a)),
        SorobanExpr::Log(args) => SorobanExpr::Log(rv(args)),
        SorobanExpr::RawHostCall {
            module,
            function,
            args,
        } => SorobanExpr::RawHostCall {
            module,
            function,
            args: rv(args),
        },
        // Leaves: literals, Param, Env, NamedLocal, etc.
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Bind unbound locals
// ---------------------------------------------------------------------------

/// Detect `Local(N)` references that have no corresponding `Let var_N = ...`
/// definition and promote a preceding standalone `Expr(...)` to a `Let`
/// binding. This recovers host-call return values that were lost during
/// lifting (e.g., BLS g2_mul result stored to a WASM local but emitted as a
/// standalone expression).
///
/// Resolve self-referential Let bindings: `Let var_N = TupleConstruct([Local(N)])`.
/// When a standalone `Expr(something)` immediately precedes such a Let, promotes
/// the Expr to `Let var_N = something` and removes the self-ref Let.
/// This happens when the lifter loses a host-call return value (emits it as
/// standalone Expr) and then constructs a self-referential binding from the
/// untracked local.
fn resolve_self_referential_lets(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    let mut result = Vec::with_capacity(stmts.len());
    let mut iter = stmts.into_iter().peekable();

    while let Some(stmt) = iter.next() {
        // Check: current is Expr, next is self-referential Let
        if matches!(&stmt, SorobanStmt::Expr(_))
            && let Some(SorobanStmt::Let {
                name,
                mutable: false,
                value,
            }) = iter.peek()
        {
            if is_self_referential(name, value) {
                let name = name.clone();
                // Extract the Expr value
                let SorobanStmt::Expr(expr) = stmt else {
                    unreachable!()
                };
                // Skip the self-referential Let
                iter.next();
                // Emit Let binding with the Expr's value
                result.push(SorobanStmt::Let {
                    name,
                    mutable: false,
                    value: expr,
                });
                continue;
            }

            // Check: Expr(something) + Let var_N = VecConstruct([..., Local(N), ...])
            // Inline the Expr value into the VecConstruct, replacing the
            // self-referential Local(N) element.
            if let Some((replaced_value, replaced_name)) =
                try_inline_vec_self_ref(name, value, &stmt)
            {
                iter.next();
                result.push(SorobanStmt::Let {
                    name: replaced_name,
                    mutable: false,
                    value: replaced_value,
                });
                continue;
            }
        }

        result.push(resolve_self_referential_lets_stmt(stmt));
    }

    result
}

fn resolve_self_referential_lets_stmt(stmt: SorobanStmt) -> SorobanStmt {
    match stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => SorobanStmt::If {
            condition,
            then_body: resolve_self_referential_lets(then_body),
            else_body: resolve_self_referential_lets(else_body),
        },
        SorobanStmt::Match { scrutinee, arms } => SorobanStmt::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: resolve_self_referential_lets(arm.body),
                })
                .collect(),
        },
        SorobanStmt::Loop { body } => SorobanStmt::Loop {
            body: resolve_self_referential_lets(body),
        },
        SorobanStmt::Block(body) => SorobanStmt::Block(resolve_self_referential_lets(body)),
        other => other,
    }
}

/// Conservative heuristic: only fires when the standalone `Expr` is
/// immediately before the statement containing the unbound reference, and
/// each unbound local is matched to exactly one standalone `Expr` (working
/// backwards from the reference point).
fn bind_unbound_locals(stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
    use std::collections::HashSet;

    // 1. Collect all var_N indices defined by Let bindings
    let mut defined: HashSet<u32> = HashSet::new();
    collect_let_indices(&stmts, &mut defined);

    // 2. Collect all Local(N) indices referenced in expressions
    let mut referenced: HashSet<u32> = HashSet::new();
    collect_local_refs_stmts(&stmts, &mut referenced);

    // 3. Find unbound: referenced but not defined
    let unbound: Vec<u32> = referenced.difference(&defined).copied().collect();
    if unbound.is_empty() {
        return stmts;
    }

    // 4. For each unbound local, scan backwards from the statement that
    //    references it to find a standalone Expr to bind.
    let mut stmts = stmts;
    let mut bound: HashSet<u32> = HashSet::new();

    for &idx in &unbound {
        // Find the first statement that references Local(idx)
        let ref_pos = stmts.iter().position(|s| stmt_refs_local(s, idx));
        let Some(ref_pos) = ref_pos else {
            continue;
        };

        // Walk backwards from ref_pos to find a standalone Expr to bind
        let mut expr_pos = None;
        for i in (0..ref_pos).rev() {
            if let SorobanStmt::Expr(expr) = &stmts[i] {
                // Skip expressions that are obviously not host-call results
                if matches!(expr, SorobanExpr::Panic | SorobanExpr::PanicWithError(_)) {
                    continue;
                }
                expr_pos = Some(i);
                break;
            }
            // Stop searching if we hit a non-Expr statement (Let, If, Match, etc.)
            // to avoid binding expressions from unrelated code sections
            break;
        }

        if let Some(pos) = expr_pos
            && !bound.contains(&idx)
        {
            // Replace the standalone Expr with a Let binding
            let expr = match std::mem::replace(&mut stmts[pos], SorobanStmt::Break) {
                SorobanStmt::Expr(e) => e,
                _ => unreachable!(),
            };
            stmts[pos] = SorobanStmt::Let {
                name: format!("var_{}", idx),
                mutable: false,
                value: expr,
            };
            bound.insert(idx);
        }
    }

    stmts
}

/// Collect all u32 indices from `Let { name: "var_N" }` bindings.
fn collect_let_indices(stmts: &[SorobanStmt], defined: &mut std::collections::HashSet<u32>) {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Let { name, .. } => {
                if let Some(idx) = name
                    .strip_prefix("var_")
                    .and_then(|s| s.parse::<u32>().ok())
                {
                    defined.insert(idx);
                }
            }
            SorobanStmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_let_indices(then_body, defined);
                collect_let_indices(else_body, defined);
            }
            SorobanStmt::Match { arms, .. } => {
                for arm in arms {
                    collect_let_indices(&arm.body, defined);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                collect_let_indices(body, defined);
            }
            _ => {}
        }
    }
}

/// Collect all `Local(N)` indices referenced in expressions.
fn collect_local_refs_stmts(stmts: &[SorobanStmt], refs: &mut std::collections::HashSet<u32>) {
    for stmt in stmts {
        match stmt {
            SorobanStmt::Expr(e) | SorobanStmt::Let { value: e, .. } => {
                collect_local_refs_expr(e, refs);
            }
            SorobanStmt::Assign { value, .. } => collect_local_refs_expr(value, refs),
            SorobanStmt::Return(Some(e)) => collect_local_refs_expr(e, refs),
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                collect_local_refs_expr(condition, refs);
                collect_local_refs_stmts(then_body, refs);
                collect_local_refs_stmts(else_body, refs);
            }
            SorobanStmt::Match { scrutinee, arms } => {
                collect_local_refs_expr(scrutinee, refs);
                for arm in arms {
                    collect_local_refs_stmts(&arm.body, refs);
                }
            }
            SorobanStmt::Loop { body } | SorobanStmt::Block(body) => {
                collect_local_refs_stmts(body, refs);
            }
            _ => {}
        }
    }
}

/// Collect Local(N) indices from an expression tree.
fn collect_local_refs_expr(expr: &SorobanExpr, refs: &mut std::collections::HashSet<u32>) {
    match expr {
        SorobanExpr::Local(idx) => {
            refs.insert(*idx);
        }
        _ => {
            // Use the existing child-walking infrastructure
            for child in expr_children(expr) {
                collect_local_refs_expr(child, refs);
            }
        }
    }
}

/// Check if a statement references Local(idx) in any of its expressions.
fn stmt_refs_local(stmt: &SorobanStmt, idx: u32) -> bool {
    count_local_in_stmt(stmt, idx, false).0 > 0
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::soroban_ir::StorageType;

    #[test]
    fn fold_drops_leaked_borrow_and_carry_flags() {
        // `total_shares - (a < b)` is a two-limb i128 borrow bit leaking into the
        // recomposed value; recover the clean `total_shares`.
        let borrow = SorobanExpr::Sub(
            Box::new(SorobanExpr::Param("total_shares".into())),
            Box::new(SorobanExpr::Lt(
                Box::new(SorobanExpr::Param("a".into())),
                Box::new(SorobanExpr::Param("b".into())),
            )),
        );
        assert_eq!(fold_expr(borrow), SorobanExpr::Param("total_shares".into()));
        // `x + (lo != 0)` — the carry case.
        let carry = SorobanExpr::Add(
            Box::new(SorobanExpr::Param("x".into())),
            Box::new(SorobanExpr::Ne(
                Box::new(SorobanExpr::Param("lo".into())),
                Box::new(SorobanExpr::I64Literal(0)),
            )),
        );
        assert_eq!(fold_expr(carry), SorobanExpr::Param("x".into()));
    }

    #[test]
    fn fold_preserves_comparison_minus_comparison_ordering_idiom() {
        // `(a > b) - (a < b)` is the `cmp` ordering idiom, NOT a borrow leak — both
        // operands are comparisons, so neither may be dropped (a later pass folds it
        // to `a < b`). Dropping one here regressed `test_fuzz` to `(a > b) < 0`.
        let cmp = SorobanExpr::Sub(
            Box::new(SorobanExpr::Gt(
                Box::new(SorobanExpr::Param("a".into())),
                Box::new(SorobanExpr::Param("b".into())),
            )),
            Box::new(SorobanExpr::Lt(
                Box::new(SorobanExpr::Param("a".into())),
                Box::new(SorobanExpr::Param("b".into())),
            )),
        );
        assert_eq!(
            fold_expr(cmp.clone()),
            cmp,
            "ordering idiom must be preserved"
        );
    }

    fn param(name: &str) -> SorobanExpr {
        SorobanExpr::Param(name.to_string())
    }
    fn local(idx: u32) -> SorobanExpr {
        SorobanExpr::Local(idx)
    }
    fn u64_lit(v: u64) -> SorobanExpr {
        SorobanExpr::U64Literal(v)
    }
    fn i64_lit(v: i64) -> SorobanExpr {
        SorobanExpr::I64Literal(v)
    }
    fn let_var(idx: u32, value: SorobanExpr) -> SorobanStmt {
        SorobanStmt::Let {
            name: format!("var_{}", idx),
            mutable: false,
            value,
        }
    }
    fn ret(e: SorobanExpr) -> SorobanStmt {
        SorobanStmt::Return(Some(e))
    }

    // ----- Constant folding -----

    #[test]
    fn fold_add_u64() {
        let stmts = vec![ret(SorobanExpr::Add(
            Box::new(u64_lit(3)),
            Box::new(u64_lit(4)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            out[0],
            SorobanStmt::Return(Some(SorobanExpr::U64Literal(7)))
        ));
    }

    #[test]
    fn fold_sub_u64() {
        let stmts = vec![ret(SorobanExpr::Sub(
            Box::new(u64_lit(10)),
            Box::new(u64_lit(3)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            out[0],
            SorobanStmt::Return(Some(SorobanExpr::U64Literal(7)))
        ));
    }

    #[test]
    fn fold_mul_i64() {
        let stmts = vec![ret(SorobanExpr::Mul(
            Box::new(i64_lit(6)),
            Box::new(i64_lit(7)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            out[0],
            SorobanStmt::Return(Some(SorobanExpr::I64Literal(42)))
        ));
    }

    // ----- Let inlining -----

    #[test]
    fn single_use_inline() {
        // let var_0 = a; return var_0;  →  return a;
        let stmts = vec![let_var(0, param("a")), ret(local(0))];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0], SorobanStmt::Return(Some(SorobanExpr::Param(n))) if n == "a"));
    }

    #[test]
    fn multi_use_preserved() {
        // let var_0 = a; expr(var_0); return var_0;
        // After name propagation: let a = a; expr(a); return a;
        // Self-assignment removed → expr(a); return a;
        // Duplicate expr removal → return a;
        let stmts = vec![
            let_var(0, param("a")),
            SorobanStmt::Expr(local(0)),
            ret(local(0)),
        ];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1, "out = {:#?}", out);
    }

    #[test]
    fn dead_store_removed() {
        // let var_0 = a;  (never used)  return b;  →  return b;
        let stmts = vec![let_var(0, param("a")), ret(param("b"))];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0], SorobanStmt::Return(Some(SorobanExpr::Param(n))) if n == "b"));
    }

    #[test]
    fn named_let_not_inlined() {
        // let key = a;  (no var_ prefix)  return key (as Local(0));
        // Named lets are kept as-is — let_name_to_local_idx returns None for "key".
        let stmts = vec![
            SorobanStmt::Let {
                name: "key".to_string(),
                mutable: false,
                value: param("k"),
            },
            ret(local(0)),
        ];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 2);
    }

    #[test]
    fn side_effect_inlined_when_immediately_used() {
        // let var_3 = storage_get; return var_3;  → return storage_get (inlined)
        // Side-effectful let is safe to inline when the sole use is in the next stmt.
        let stmts = vec![
            let_var(
                3,
                SorobanExpr::StorageGet {
                    storage_type: StorageType::Persistent,
                    key: Box::new(param("key")),
                    unwrap: true,
                },
            ),
            ret(local(3)),
        ];
        let out = optimize_stmts(stmts);
        // Inlined: `return storage_get`
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0], SorobanStmt::Return(Some(_))));
    }

    #[test]
    fn backedge_free_loop_inlined_with_name_propagation() {
        // let var_0 = x;  loop { expr(var_0) }
        // The `loop` has no back-edge (`continue`) and no `break`, so it is a WASM
        // `loop` block that runs exactly once and is inlined to straight-line code.
        // Name propagation still applies: the self-assignment `let x = x` is removed
        // and the inlined body references `x` directly (no dangling `var_0`).
        let stmts = vec![
            let_var(0, param("x")),
            SorobanStmt::Loop {
                body: vec![SorobanStmt::Expr(local(0))],
            },
        ];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1);
        assert!(
            matches!(&out[0], SorobanStmt::Expr(_)),
            "back-edge-free loop should inline to its body expression; got: {out:?}"
        );
        assert!(
            !matches!(&out[0], SorobanStmt::Loop { .. }),
            "loop wrapper should be gone: {out:?}"
        );
    }

    #[test]
    fn loop_with_breaking_condition_preserved() {
        // A loop that exits via a `break` carries a real back-edge and must be
        // preserved (only back-edge-free loops inline). The break is inside an
        // `if` whose condition has a side effect, so the loop is not a trivial
        // pure-condition loop either.
        let stmts = vec![SorobanStmt::Loop {
            body: vec![
                SorobanStmt::Expr(SorobanExpr::RequireAuth(Box::new(param("a")))),
                SorobanStmt::If {
                    condition: SorobanExpr::Param("cond".to_string()),
                    then_body: vec![SorobanStmt::Break],
                    else_body: vec![],
                },
            ],
        }];
        let out = optimize_stmts(stmts);
        assert!(
            matches!(&out[0], SorobanStmt::Loop { .. }),
            "loop containing a break must be preserved; got: {out:?}"
        );
    }

    #[test]
    fn chained_inline() {
        // let var_0 = a + b; let var_1 = var_0; return var_1;
        // → return a + b;
        let stmts = vec![
            let_var(
                0,
                SorobanExpr::Add(Box::new(param("a")), Box::new(param("b"))),
            ),
            let_var(1, local(0)),
            ret(local(1)),
        ];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1);
        assert!(
            matches!(&out[0], SorobanStmt::Return(Some(SorobanExpr::Add(_, _)))),
            "Expected Return(Add(...))"
        );
    }

    // ----- Constant condition folding -----

    #[test]
    fn fold_constant_false_if() {
        // if 0i32 { break; }  →  (nothing)
        let stmts = vec![SorobanStmt::If {
            condition: SorobanExpr::I32Literal(0),
            then_body: vec![SorobanStmt::Break],
            else_body: vec![],
        }];
        let out = optimize_stmts(stmts);
        assert!(out.is_empty(), "Expected empty, got {:?}", out);
    }

    #[test]
    fn fold_constant_true_if() {
        // if 1i32 { continue; }  →  continue;
        let stmts = vec![SorobanStmt::If {
            condition: SorobanExpr::I32Literal(1),
            then_body: vec![SorobanStmt::Continue],
            else_body: vec![],
        }];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1);
        assert!(matches!(out[0], SorobanStmt::Continue));
    }

    #[test]
    fn fold_constant_false_if_else() {
        // if 0i64 { break; } else { continue; }  →  continue;
        let stmts = vec![SorobanStmt::If {
            condition: SorobanExpr::I64Literal(0),
            then_body: vec![SorobanStmt::Break],
            else_body: vec![SorobanStmt::Continue],
        }];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1);
        assert!(matches!(out[0], SorobanStmt::Continue));
    }

    // ----- Leading panic removal -----

    #[test]
    fn remove_leading_panic_with_tail() {
        // panic!(); storage_remove(key);  →  storage_remove(key);
        let stmts = vec![
            SorobanStmt::Expr(SorobanExpr::Panic),
            SorobanStmt::Expr(SorobanExpr::StorageRemove {
                storage_type: StorageType::Persistent,
                key: Box::new(param("key")),
            }),
        ];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1);
        assert!(matches!(
            &out[0],
            SorobanStmt::Expr(SorobanExpr::StorageRemove { .. })
        ));
    }

    #[test]
    fn preserve_lone_panic() {
        // panic!();  →  panic!();  (no tail → keep it)
        let stmts = vec![SorobanStmt::Expr(SorobanExpr::Panic)];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0], SorobanStmt::Expr(SorobanExpr::Panic)));
    }

    // ----- Stray leaked panic removal (issue #12) -----

    #[test]
    fn drop_stray_panic_keeps_host_call_continuation() {
        // var_0 = seed; panic!(); storage_remove(key);  →  drop the mid-body
        // stray panic, keep the continuation. (Non-leading, so this exercises the
        // issue #12 backstop rather than remove_leading_panic.)
        let stmts = vec![
            let_var(0, param("seed")),
            SorobanStmt::Expr(SorobanExpr::Panic),
            SorobanStmt::Expr(SorobanExpr::StorageRemove {
                storage_type: StorageType::Persistent,
                key: Box::new(param("key")),
            }),
        ];
        let out = drop_stray_panic_before_continuation(stmts);
        assert_eq!(out.len(), 2);
        assert!(matches!(&out[0], SorobanStmt::Let { .. }));
        assert!(matches!(
            &out[1],
            SorobanStmt::Expr(SorobanExpr::StorageRemove { .. })
        ));
    }

    #[test]
    fn drop_stray_panic_two_consecutive_before_real_body() {
        // The estimate_swap shape: [Panic, PanicWithError, Let, Return]. The
        // first stray's live continuation sits *past* the second stray, so the
        // whole tail must be scanned — both panics are dropped.
        let stmts = vec![
            SorobanStmt::Expr(SorobanExpr::Panic),
            SorobanStmt::Expr(SorobanExpr::PanicWithError(Box::new(
                SorobanExpr::I64Literal(2002),
            ))),
            let_var(2, param("x")),
            ret(local(2)),
        ];
        let out = drop_stray_panic_before_continuation(stmts);
        assert_eq!(out.len(), 2, "both stray panics dropped");
        assert!(matches!(&out[0], SorobanStmt::Let { .. }));
        assert!(matches!(&out[1], SorobanStmt::Return(_)));
    }

    #[test]
    fn drop_stray_panic_preserves_lone_terminal_panic() {
        let stmts = vec![SorobanStmt::Expr(SorobanExpr::Panic)];
        let out = drop_stray_panic_before_continuation(stmts);
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0], SorobanStmt::Expr(SorobanExpr::Panic)));
    }

    #[test]
    fn drop_stray_panic_ignores_nested_panic() {
        // `if c { panic!() }` is a real conditional error exit — top-level-only
        // scope must leave it untouched even when real work follows.
        let stmts = vec![
            SorobanStmt::If {
                condition: param("c"),
                then_body: vec![SorobanStmt::Expr(SorobanExpr::Panic)],
                else_body: vec![],
            },
            let_var(0, param("x")),
        ];
        let out = drop_stray_panic_before_continuation(stmts);
        assert_eq!(out.len(), 2);
        if let SorobanStmt::If { then_body, .. } = &out[0] {
            assert_eq!(then_body.len(), 1);
            assert!(matches!(
                &then_body[0],
                SorobanStmt::Expr(SorobanExpr::Panic)
            ));
        } else {
            panic!("Expected If preserved");
        }
    }

    #[test]
    fn drop_stray_panic_preserves_terminal_panic_after_real_work() {
        // publish(&env); panic!()  — the `failed_transfer` shape: the panic is
        // terminal (nothing after) so it is the function's genuine divergence.
        let stmts = vec![
            SorobanStmt::Expr(SorobanExpr::PublishEvent {
                event_name: None,
                topics: vec![],
                data: Box::new(SorobanExpr::Void),
            }),
            SorobanStmt::Expr(SorobanExpr::Panic),
        ];
        let out = drop_stray_panic_before_continuation(stmts);
        assert_eq!(out.len(), 2);
        assert!(matches!(&out[1], SorobanStmt::Expr(SorobanExpr::Panic)));
    }

    #[test]
    fn drop_stray_panic_preserves_when_tail_has_no_real_continuation() {
        // panic!(); <pure expr>; continue;  — the tail carries no real work, so
        // the panic is a genuine terminator and is preserved.
        let stmts = vec![
            SorobanStmt::Expr(SorobanExpr::Panic),
            SorobanStmt::Expr(param("pure")),
            SorobanStmt::Continue,
        ];
        let out = drop_stray_panic_before_continuation(stmts);
        assert_eq!(out.len(), 3);
        assert!(matches!(&out[0], SorobanStmt::Expr(SorobanExpr::Panic)));
    }

    #[test]
    fn pipeline_recovers_body_after_stray_panic() {
        // End-to-end: a stray panic between real work must not truncate the body.
        let stmts = vec![
            SorobanStmt::Expr(SorobanExpr::RequireAuth(Box::new(param("user")))),
            SorobanStmt::Expr(SorobanExpr::Panic),
            SorobanStmt::Expr(SorobanExpr::StorageRemove {
                storage_type: StorageType::Persistent,
                key: Box::new(param("key")),
            }),
        ];
        let out = optimize_stmts(stmts);
        assert!(
            out.iter()
                .any(|s| matches!(s, SorobanStmt::Expr(SorobanExpr::StorageRemove { .. }))),
            "real continuation dropped"
        );
        assert!(
            !out.iter()
                .any(|s| matches!(s, SorobanStmt::Expr(SorobanExpr::Panic))),
            "stray panic not removed"
        );
    }

    // ----- Bool comparison folding -----

    #[test]
    fn fold_bool_eq_one() {
        // has(key) == 1  →  has(key)
        let stmts = vec![ret(SorobanExpr::Eq(
            Box::new(SorobanExpr::StorageHas {
                storage_type: StorageType::Persistent,
                key: Box::new(param("key")),
            }),
            Box::new(SorobanExpr::I32Literal(1)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::StorageHas { .. }))
        ));
    }

    #[test]
    fn fold_bool_eq_zero() {
        // has(key) == 0  →  !has(key)
        let stmts = vec![ret(SorobanExpr::Eq(
            Box::new(SorobanExpr::StorageHas {
                storage_type: StorageType::Persistent,
                key: Box::new(param("key")),
            }),
            Box::new(SorobanExpr::I32Literal(0)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::Not(_)))
        ));
    }

    #[test]
    fn fold_double_not() {
        // !!a  →  a
        let stmts = vec![ret(SorobanExpr::Not(Box::new(SorobanExpr::Not(Box::new(
            param("a"),
        )))))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::Param(n))) if n == "a"
        ));
    }

    // ----- Guard clause inversion -----

    #[test]
    fn invert_guard_clause() {
        // if a >= b { return; } ; panic!()  →  if a < b { panic!() }
        let stmts = vec![
            SorobanStmt::If {
                condition: SorobanExpr::Ge(Box::new(param("a")), Box::new(param("b"))),
                then_body: vec![SorobanStmt::Return(None)],
                else_body: vec![],
            },
            SorobanStmt::Expr(SorobanExpr::Panic),
        ];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1);
        if let SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } = &out[0]
        {
            assert!(matches!(condition, SorobanExpr::Lt(_, _)));
            assert_eq!(then_body.len(), 1);
            assert!(else_body.is_empty());
        } else {
            panic!("Expected If statement");
        }
    }

    // ----- Dead code removal -----

    #[test]
    fn remove_dead_code_after_panic_in_if() {
        // if c { panic!(); unreachable_stmt; }  →  if c { panic!(); }
        let stmts = vec![SorobanStmt::If {
            condition: param("c"),
            then_body: vec![
                SorobanStmt::Expr(SorobanExpr::Panic),
                SorobanStmt::Expr(param("unreachable")),
            ],
            else_body: vec![],
        }];
        let out = optimize_stmts(stmts);
        if let SorobanStmt::If { then_body, .. } = &out[0] {
            assert_eq!(then_body.len(), 1, "dead code not removed");
        } else {
            panic!("Expected If statement");
        }
    }

    #[test]
    fn remove_dead_code_after_return_in_match() {
        // match x { _ => { return a; unreachable; } }
        let stmts = vec![SorobanStmt::Match {
            scrutinee: param("x"),
            arms: vec![MatchArm {
                pattern: crate::ir::soroban_ir::MatchPattern::Wildcard,
                body: vec![
                    SorobanStmt::Return(Some(param("a"))),
                    SorobanStmt::Expr(param("dead")),
                ],
            }],
        }];
        let out = optimize_stmts(stmts);
        if let SorobanStmt::Match { arms, .. } = &out[0] {
            assert_eq!(arms[0].body.len(), 1, "dead code not removed in match arm");
        } else {
            panic!("Expected Match statement");
        }
    }

    // ----- Constant comparison folding -----

    #[test]
    fn fold_le_false_comparison() {
        // if 10 <= 9 { break; }  →  (nothing, since 10 <= 9 is false)
        let stmts = vec![SorobanStmt::If {
            condition: SorobanExpr::Le(
                Box::new(SorobanExpr::I32Literal(10)),
                Box::new(SorobanExpr::I32Literal(9)),
            ),
            then_body: vec![SorobanStmt::Break],
            else_body: vec![],
        }];
        let out = optimize_stmts(stmts);
        assert!(
            out.is_empty(),
            "Expected dead branch eliminated, got {:?}",
            out
        );
    }

    #[test]
    fn preserve_ne_true_comparison() {
        // if 0 != 16 { continue; }  → preserved (not folded to true)
        let stmts = vec![SorobanStmt::If {
            condition: SorobanExpr::Ne(
                Box::new(SorobanExpr::I32Literal(0)),
                Box::new(SorobanExpr::I32Literal(16)),
            ),
            then_body: vec![SorobanStmt::Continue],
            else_body: vec![],
        }];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1, "true-constant if should be preserved");
        assert!(matches!(&out[0], SorobanStmt::If { .. }));
    }

    #[test]
    fn fold_eq_false_comparison() {
        // if 0 == 1 { panic!(); }  →  (nothing, since 0 == 1 is false)
        let stmts = vec![SorobanStmt::If {
            condition: SorobanExpr::Eq(
                Box::new(SorobanExpr::I32Literal(0)),
                Box::new(SorobanExpr::I32Literal(1)),
            ),
            then_body: vec![SorobanStmt::Expr(SorobanExpr::Panic)],
            else_body: vec![],
        }];
        let out = optimize_stmts(stmts);
        assert!(
            out.is_empty(),
            "Expected dead branch eliminated, got {:?}",
            out
        );
    }

    // ----- Dead code after break/continue -----

    #[test]
    fn hoist_code_after_break_in_loop() {
        // loop { break; expr(a); }  → expr(a) (hoisted out, loop collapsed)
        let stmts = vec![SorobanStmt::Loop {
            body: vec![SorobanStmt::Break, SorobanStmt::Expr(param("useful"))],
        }];
        let out = optimize_stmts(stmts);
        // Code after break is hoisted outside the loop, then loop { break } collapses
        assert_eq!(out.len(), 1, "should be just the hoisted statement");
        assert!(matches!(&out[0], SorobanStmt::Expr(SorobanExpr::Param(s)) if s == "useful"));
    }

    // ----- Loop collapse -----

    #[test]
    fn collapse_loop_break() {
        // loop { break; }  →  (nothing)
        let stmts = vec![SorobanStmt::Loop {
            body: vec![SorobanStmt::Break],
        }];
        let out = optimize_stmts(stmts);
        assert!(out.is_empty(), "Expected loop {{ break }} collapsed");
    }

    #[test]
    fn collapse_single_iteration_loop() {
        // loop { expr(a); break; }  →  expr(a);
        let stmts = vec![SorobanStmt::Loop {
            body: vec![SorobanStmt::Expr(param("a")), SorobanStmt::Break],
        }];
        let out = optimize_stmts(stmts);
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0], SorobanStmt::Expr(SorobanExpr::Param(n)) if n == "a"));
    }

    // ----- Algebraic identities -----

    #[test]
    fn fold_add_zero() {
        // x + 0 → x
        let stmts = vec![ret(SorobanExpr::Add(
            Box::new(param("x")),
            Box::new(SorobanExpr::I32Literal(0)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::Param(n))) if n == "x"
        ));
    }

    #[test]
    fn fold_mul_one() {
        // x * 1 → x
        let stmts = vec![ret(SorobanExpr::Mul(
            Box::new(param("x")),
            Box::new(SorobanExpr::U64Literal(1)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::Param(n))) if n == "x"
        ));
    }

    #[test]
    fn fold_mul_zero() {
        // x * 0u64 → 0u64
        let stmts = vec![ret(SorobanExpr::Mul(
            Box::new(param("x")),
            Box::new(SorobanExpr::U64Literal(0)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::U64Literal(0)))
        ));
    }

    #[test]
    fn fold_div_constants() {
        // 42i64 / 7i64 → 6i64
        let stmts = vec![ret(SorobanExpr::Div(
            Box::new(SorobanExpr::I64Literal(42)),
            Box::new(SorobanExpr::I64Literal(7)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::I64Literal(6)))
        ));
    }

    #[test]
    fn fold_rem_constants() {
        // 10u32 % 3u32 → 1u32
        let stmts = vec![ret(SorobanExpr::Rem(
            Box::new(SorobanExpr::U32Literal(10)),
            Box::new(SorobanExpr::U32Literal(3)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::U32Literal(1)))
        ));
    }

    #[test]
    fn fold_div_by_zero_not_folded() {
        // x / 0 is NOT folded (division by zero)
        let stmts = vec![ret(SorobanExpr::Div(
            Box::new(SorobanExpr::I64Literal(42)),
            Box::new(SorobanExpr::I64Literal(0)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::Div(..)))
        ));
    }

    #[test]
    fn strip_identity_val_convert() {
        // ValConvert { I64Literal(42), "i64" } → I64Literal(42)
        let stmts = vec![ret(SorobanExpr::ValConvert {
            value: Box::new(SorobanExpr::I64Literal(42)),
            target_type: "i64".to_string(),
        })];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::I64Literal(42)))
        ));
    }

    #[test]
    fn strip_identity_val_convert_enables_folding() {
        // ValConvert { I64Literal(10), "i64" } * I64Literal(5) → I64Literal(50)
        let stmts = vec![ret(SorobanExpr::Mul(
            Box::new(SorobanExpr::ValConvert {
                value: Box::new(SorobanExpr::I64Literal(10)),
                target_type: "i64".to_string(),
            }),
            Box::new(SorobanExpr::I64Literal(5)),
        ))];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::I64Literal(50)))
        ));
    }

    #[test]
    fn non_identity_val_convert_preserved() {
        // ValConvert { I32Literal(42), "i64" } is NOT stripped (type mismatch)
        let stmts = vec![ret(SorobanExpr::ValConvert {
            value: Box::new(SorobanExpr::I32Literal(42)),
            target_type: "i64".to_string(),
        })];
        let out = optimize_stmts(stmts);
        assert!(matches!(
            &out[0],
            SorobanStmt::Return(Some(SorobanExpr::ValConvert { .. }))
        ));
    }

    #[test]
    fn fold_method_call_args_i64() {
        // v.get(1i64 + 1i64) → v.get(2i64)
        let stmts = vec![SorobanStmt::Expr(SorobanExpr::MethodCall {
            object: Box::new(param("a")),
            method: "get".to_string(),
            args: vec![SorobanExpr::Add(Box::new(i64_lit(1)), Box::new(i64_lit(1)))],
        })];
        let out = optimize_stmts(stmts);
        match &out[0] {
            SorobanStmt::Expr(SorobanExpr::MethodCall { args, .. }) => {
                assert_eq!(
                    args[0],
                    i64_lit(2),
                    "Expected I64Literal(2), got {:?}",
                    args[0]
                );
            }
            other => panic!("expected Expr(MethodCall), got {:?}", other),
        }
    }

    #[test]
    fn fold_method_call_args_i32() {
        // v.get(1i32 + 1i32) → v.get(2i32)
        let stmts = vec![SorobanStmt::Expr(SorobanExpr::MethodCall {
            object: Box::new(param("a")),
            method: "get".to_string(),
            args: vec![SorobanExpr::Add(
                Box::new(SorobanExpr::I32Literal(1)),
                Box::new(SorobanExpr::I32Literal(1)),
            )],
        })];
        let out = optimize_stmts(stmts);
        match &out[0] {
            SorobanStmt::Expr(SorobanExpr::MethodCall { args, .. }) => {
                assert_eq!(
                    args[0],
                    SorobanExpr::I32Literal(2),
                    "Expected I32Literal(2), got {:?}",
                    args[0]
                );
            }
            other => panic!("expected Expr(MethodCall), got {:?}", other),
        }
    }

    #[test]
    fn collapse_trivial_loops_keeps_loop_if_cond_has_side_effects() {
        // `loop { if storage_get { break } }` must NOT be collapsed — the
        // storage read is observable and the collapse would drop it.
        let stmts = vec![SorobanStmt::Loop {
            body: vec![SorobanStmt::If {
                condition: SorobanExpr::StorageHas {
                    storage_type: StorageType::Persistent,
                    key: Box::new(SorobanExpr::SymbolLiteral("k".into())),
                },
                then_body: vec![SorobanStmt::Break],
                else_body: Vec::new(),
            }],
        }];
        let out = optimize_stmts(stmts);
        assert!(
            matches!(&out[0], SorobanStmt::Loop { .. }),
            "expected loop to survive; got: {out:?}"
        );
    }

    #[test]
    fn collapse_trivial_loops_still_collapses_pure_cond() {
        // Regression-protect happy path: pure condition still gets collapsed.
        let stmts = vec![SorobanStmt::Loop {
            body: vec![SorobanStmt::If {
                condition: SorobanExpr::BoolLiteral(true),
                then_body: vec![SorobanStmt::Break],
                else_body: Vec::new(),
            }],
        }];
        let out = optimize_stmts(stmts);
        assert!(
            out.is_empty(),
            "expected pure-condition trivial loop to collapse; got: {out:?}"
        );
    }

    #[test]
    fn fold_constant_matches_preserves_enum_dispatch_with_sentinel_scrutinee() {
        // The lifter emits `I32Literal(0)` as a placeholder for untracked
        // stack values. If a match scrutinee comes through as that sentinel
        // and the arms are enum dispatch, the old folder would pick the
        // wildcard arm and silently delete the variant code.
        let arms = vec![
            MatchArm {
                pattern: MatchPattern::EnumVariant {
                    type_name: "DataKey".into(),
                    variant: "Persistent".into(),
                    bindings: vec!["_".into()],
                },
                body: vec![ret(SorobanExpr::U32Literal(1))],
            },
            MatchArm {
                pattern: MatchPattern::EnumVariant {
                    type_name: "DataKey".into(),
                    variant: "Temp".into(),
                    bindings: vec!["_".into()],
                },
                body: vec![ret(SorobanExpr::U32Literal(2))],
            },
            MatchArm {
                pattern: MatchPattern::Wildcard,
                body: vec![ret(SorobanExpr::U32Literal(99))],
            },
        ];
        let stmts = vec![SorobanStmt::Match {
            scrutinee: SorobanExpr::I32Literal(0),
            arms,
        }];
        let out = optimize_stmts(stmts);
        // Match must survive with all three arms intact.
        match &out[0] {
            SorobanStmt::Match { arms, .. } => {
                assert_eq!(
                    arms.len(),
                    3,
                    "expected match to survive intact; got: {arms:?}"
                );
            }
            other => panic!("expected match to survive; got: {other:?}"),
        }
    }

    #[test]
    fn fold_constant_matches_still_folds_real_literal_dispatch() {
        // Regression-protect the happy path: `match 1 { 0 => .., 1 => ok, _ => .. }`
        // should still fold to `ok`. Use literal patterns only (no enum arms)
        // so the sentinel guard doesn't trigger.
        let arms = vec![
            MatchArm {
                pattern: MatchPattern::Literal(SorobanExpr::I32Literal(0)),
                body: vec![ret(SorobanExpr::U32Literal(999))],
            },
            MatchArm {
                pattern: MatchPattern::Literal(SorobanExpr::I32Literal(1)),
                body: vec![ret(SorobanExpr::U32Literal(7))],
            },
        ];
        let stmts = vec![SorobanStmt::Match {
            scrutinee: SorobanExpr::I32Literal(1),
            arms,
        }];
        let out = optimize_stmts(stmts);
        // The match should have been inlined to just the return-7 body.
        assert!(
            matches!(
                &out[0],
                SorobanStmt::Return(Some(SorobanExpr::U32Literal(7)))
            ),
            "expected literal-1 arm to fold; got: {out:?}"
        );
    }

    #[test]
    fn fold_constant_matches_folds_mixed_type_arithmetic_scrutinee() {
        // The aquarius/blend inlined `br_table` key-builders arrive with a
        // *constant* discriminant of mixed literal types, e.g. `i64(2) - i32(1)`,
        // which `fold_expr`'s same-type-only arithmetic arms leave intact as
        // `match 2 - 1 { ... }`. `const_eval_i128` evaluates the selector so the
        // dispatch collapses to its single live arm — discarding the dozens of
        // dead `vec![&env, todo!()]` arms that dominated the todo count.
        let arms = vec![
            MatchArm {
                pattern: MatchPattern::Literal(SorobanExpr::U32Literal(0)),
                body: vec![ret(SorobanExpr::U32Literal(999))],
            },
            MatchArm {
                pattern: MatchPattern::Literal(SorobanExpr::U32Literal(1)),
                body: vec![ret(SorobanExpr::U32Literal(7))],
            },
            MatchArm {
                pattern: MatchPattern::Literal(SorobanExpr::U32Literal(2)),
                body: vec![ret(SorobanExpr::U32Literal(8))],
            },
        ];
        let stmts = vec![SorobanStmt::Match {
            scrutinee: SorobanExpr::Sub(
                Box::new(SorobanExpr::I64Literal(2)),
                Box::new(SorobanExpr::I32Literal(1)),
            ),
            arms,
        }];
        let out = optimize_stmts(stmts);
        assert!(
            matches!(
                &out[0],
                SorobanStmt::Return(Some(SorobanExpr::U32Literal(7)))
            ),
            "expected `2 - 1` to select arm 1; got: {out:?}"
        );
    }

    #[test]
    fn fold_constant_matches_keeps_runtime_unknown_scrutinee() {
        // A genuine runtime selector — `UnknownVal - 1`, the lifter's marker for a
        // discriminant it could not track — must NEVER be folded: picking an
        // arbitrary arm would fabricate wrong code. `const_eval_i128` returns
        // `None` the instant it hits a non-literal leaf, so the match survives.
        let arms = vec![
            MatchArm {
                pattern: MatchPattern::Literal(SorobanExpr::U32Literal(0)),
                body: vec![ret(SorobanExpr::U32Literal(999))],
            },
            MatchArm {
                pattern: MatchPattern::Literal(SorobanExpr::U32Literal(1)),
                body: vec![ret(SorobanExpr::U32Literal(7))],
            },
        ];
        let stmts = vec![SorobanStmt::Match {
            scrutinee: SorobanExpr::Sub(
                Box::new(SorobanExpr::UnknownVal),
                Box::new(SorobanExpr::I32Literal(1)),
            ),
            arms,
        }];
        let out = optimize_stmts(stmts);
        assert!(
            matches!(&out[0], SorobanStmt::Match { arms, .. } if arms.len() == 2),
            "expected runtime-unknown match to survive intact; got: {out:?}"
        );
    }

    #[test]
    fn void_guard_drops_unknown_value_return_husk() {
        // `if todo!() == 1114112 { return 0 }` in a void fn: an inlined Symbol→index
        // decoder husk. The value-return is dropped by codegen and the condition is
        // an `UnknownVal` (unrepresentable), so the whole guard is a pure artifact.
        let stmts = vec![SorobanStmt::If {
            condition: SorobanExpr::Eq(
                Box::new(SorobanExpr::UnknownVal),
                Box::new(SorobanExpr::I32Literal(1114112)),
            ),
            then_body: vec![SorobanStmt::Return(Some(SorobanExpr::I32Literal(0)))],
            else_body: Vec::new(),
        }];
        let out = drop_void_unknown_value_return_guards(stmts);
        assert!(
            out.is_empty(),
            "expected void decode husk to be dropped; got: {out:?}"
        );
    }

    #[test]
    fn void_guard_keeps_real_guards_and_void_early_returns() {
        // Must NOT fire on: (a) a representable condition (real control flow), or
        // (b) a bare `return;` (`Return(None)` — a legitimate void early-return).
        let real_guard = SorobanStmt::If {
            condition: SorobanExpr::Gt(
                Box::new(SorobanExpr::Param("x".into())),
                Box::new(SorobanExpr::U32Literal(5)),
            ),
            then_body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(0)))],
            else_body: Vec::new(),
        };
        let void_early_return = SorobanStmt::If {
            condition: SorobanExpr::Eq(
                Box::new(SorobanExpr::UnknownVal),
                Box::new(SorobanExpr::I32Literal(1114112)),
            ),
            then_body: vec![SorobanStmt::Return(None)],
            else_body: Vec::new(),
        };
        let stmts = vec![real_guard, void_early_return];
        let out = drop_void_unknown_value_return_guards(stmts.clone());
        assert_eq!(
            format!("{out:?}"),
            format!("{stmts:?}"),
            "real guard / bare early-return must be preserved"
        );
    }

    #[test]
    fn recover_discarded_len_fills_next_condition() {
        // `Expr(tokens.len()); if UnknownVal != 0 { .. }` — the lifter lost the
        // len result across a block boundary. Recover it into the lone UnknownVal
        // → `if tokens.len() != 0 { .. }`, dropping the now-consumed Expr.
        let len_call = SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::Param("tokens".into())),
            method: "len".into(),
            args: vec![],
        };
        let stmts = vec![
            SorobanStmt::Expr(len_call.clone()),
            SorobanStmt::If {
                condition: SorobanExpr::Ne(
                    Box::new(SorobanExpr::UnknownVal),
                    Box::new(SorobanExpr::I32Literal(0)),
                ),
                then_body: vec![SorobanStmt::Break],
                else_body: vec![],
            },
        ];
        let out = recover_discarded_len_into_consumer(stmts);
        assert_eq!(out.len(), 1, "the discarded Expr(len) should be consumed");
        match &out[0] {
            SorobanStmt::If { condition, .. } => assert_eq!(
                condition,
                &SorobanExpr::Ne(Box::new(len_call), Box::new(SorobanExpr::I32Literal(0))),
                "len should fill the lone UnknownVal"
            ),
            other => panic!("expected If; got {other:?}"),
        }
    }

    #[test]
    fn recover_discarded_get_threads_into_require_auth() {
        cov_mark::check!(discarded_get_into_require_auth);
        // `get(&k).unwrap(); todo!().require_auth();` — the admin/owner gate. The
        // loaded Address was flushed as a discarded Expr and the auth's target
        // underflowed to UnknownVal. Thread the get into the auth target and drop
        // the now-consumed Expr.
        let get = SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key: Box::new(SorobanExpr::UnknownVal),
            unwrap: true,
        };
        let stmts = vec![
            SorobanStmt::Expr(get.clone()),
            SorobanStmt::Expr(SorobanExpr::RequireAuth(Box::new(SorobanExpr::UnknownVal))),
        ];
        let out = recover_discarded_storage_get_into_consumer(stmts);
        assert_eq!(out.len(), 1, "the discarded Expr(get) should be consumed");
        match &out[0] {
            SorobanStmt::Expr(SorobanExpr::RequireAuth(target)) => assert_eq!(
                **target, get,
                "the loaded storage value should become the require_auth target"
            ),
            other => panic!("expected Expr(RequireAuth(..)); got {other:?}"),
        }
    }

    #[test]
    fn recover_discarded_get_skips_non_auth_and_valued_target() {
        // (a) Consumer is not a require_auth → never threaded (a discarded get
        // before an arbitrary statement is left intact; only the auth-target
        // position is recovered).
        let get = SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key: Box::new(SorobanExpr::UnknownVal),
            unwrap: true,
        };
        let non_auth = vec![
            SorobanStmt::Expr(get.clone()),
            SorobanStmt::If {
                condition: SorobanExpr::Ne(
                    Box::new(SorobanExpr::UnknownVal),
                    Box::new(SorobanExpr::I32Literal(0)),
                ),
                then_body: vec![SorobanStmt::Break],
                else_body: vec![],
            },
        ];
        assert_eq!(
            recover_discarded_storage_get_into_consumer(non_auth).len(),
            2,
            "a discarded get before a non-auth consumer must be left intact"
        );

        // (b) The auth target already carries a value → never overwritten.
        let valued = vec![
            SorobanStmt::Expr(get),
            SorobanStmt::Expr(SorobanExpr::RequireAuth(Box::new(SorobanExpr::Param(
                "admin".into(),
            )))),
        ];
        assert_eq!(
            recover_discarded_storage_get_into_consumer(valued).len(),
            2,
            "a require_auth whose target is already a value must not be touched"
        );
    }

    #[test]
    fn recover_discarded_len_skips_ambiguous_and_impure() {
        // (a) Two UnknownVals in the consumer → ambiguous → no recovery.
        let len_call = SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::Param("tokens".into())),
            method: "len".into(),
            args: vec![],
        };
        let two_unknowns = vec![
            SorobanStmt::Expr(len_call.clone()),
            SorobanStmt::If {
                condition: SorobanExpr::Lt(
                    Box::new(SorobanExpr::UnknownVal),
                    Box::new(SorobanExpr::UnknownVal),
                ),
                then_body: vec![SorobanStmt::Break],
                else_body: vec![],
            },
        ];
        assert_eq!(
            recover_discarded_len_into_consumer(two_unknowns.clone()).len(),
            2,
            "ambiguous (2 UnknownVals) consumer must be left intact"
        );

        // (b) Impure len object (a host call) → never moved.
        let impure = vec![
            SorobanStmt::Expr(SorobanExpr::MethodCall {
                object: Box::new(SorobanExpr::RawHostCall {
                    module: "x".into(),
                    function: "y".into(),
                    args: vec![],
                }),
                method: "len".into(),
                args: vec![],
            }),
            SorobanStmt::If {
                condition: SorobanExpr::Ne(
                    Box::new(SorobanExpr::UnknownVal),
                    Box::new(SorobanExpr::I32Literal(0)),
                ),
                then_body: vec![SorobanStmt::Break],
                else_body: vec![],
            },
        ];
        assert_eq!(
            recover_discarded_len_into_consumer(impure).len(),
            2,
            "impure .len() object must not be moved into the consumer"
        );
    }

    #[test]
    fn cse_storage_get_invalidates_after_storage_set_same_key() {
        // `let a = get(k); set(k, v); let b = get(k);` must NOT fold the
        // second get to `a` — the StorageSet between them invalidates the
        // cached value.
        let key = || SorobanExpr::SymbolLiteral("k".into());
        let stmts = vec![
            SorobanStmt::Let {
                name: "var_0".into(),
                mutable: false,
                value: SorobanExpr::StorageGet {
                    storage_type: StorageType::Persistent,
                    key: Box::new(key()),
                    unwrap: true,
                },
            },
            SorobanStmt::Expr(SorobanExpr::StorageSet {
                storage_type: StorageType::Persistent,
                key: Box::new(key()),
                value: Box::new(SorobanExpr::U64Literal(42)),
            }),
            SorobanStmt::Let {
                name: "var_1".into(),
                mutable: false,
                value: SorobanExpr::StorageGet {
                    storage_type: StorageType::Persistent,
                    key: Box::new(key()),
                    unwrap: true,
                },
            },
        ];
        let out = optimize_stmts(stmts);
        // Both gets must survive (CSE must not collapse them).
        let get_count = out
            .iter()
            .filter(|s| {
                matches!(
                    s,
                    SorobanStmt::Let {
                        value: SorobanExpr::StorageGet { .. },
                        ..
                    } | SorobanStmt::Expr(SorobanExpr::StorageGet { .. })
                )
            })
            .count();
        assert_eq!(
            get_count, 2,
            "expected both gets to survive CSE around an intervening set; got: {out:?}"
        );
    }

    #[test]
    fn cse_storage_get_still_folds_without_intervening_set() {
        // Regression-protect the happy path: two reads of the same key with
        // no intervening write should still be CSE'd.
        let key = || SorobanExpr::SymbolLiteral("k".into());
        let stmts = vec![
            SorobanStmt::Let {
                name: "var_0".into(),
                mutable: false,
                value: SorobanExpr::StorageGet {
                    storage_type: StorageType::Persistent,
                    key: Box::new(key()),
                    unwrap: true,
                },
            },
            SorobanStmt::Let {
                name: "var_1".into(),
                mutable: false,
                value: SorobanExpr::StorageGet {
                    storage_type: StorageType::Persistent,
                    key: Box::new(key()),
                    unwrap: true,
                },
            },
            // Use both so dead-store removal doesn't strip them.
            SorobanStmt::Return(Some(SorobanExpr::Add(
                Box::new(SorobanExpr::Local(0)),
                Box::new(SorobanExpr::Local(1)),
            ))),
        ];
        let out = optimize_stmts(stmts);
        let get_count = out
            .iter()
            .filter(|s| {
                matches!(
                    s,
                    SorobanStmt::Let {
                        value: SorobanExpr::StorageGet { .. },
                        ..
                    }
                )
            })
            .count();
        assert_eq!(
            get_count, 1,
            "expected CSE to fold duplicate gets; got: {out:?}"
        );
    }

    #[test]
    fn remove_orphan_host_calls_keeps_raw_host_call() {
        // RawHostCall has side effects per `expr_has_side_effects`; the orphan
        // remover must agree and keep it, otherwise host calls the lifter
        // failed to recognize would be silently deleted.
        let stmts = vec![SorobanStmt::Expr(SorobanExpr::RawHostCall {
            module: "x".to_string(),
            function: "unknown_op".to_string(),
            args: Vec::new(),
        })];
        let out = optimize_stmts(stmts);
        let kept_a_raw_host_call = out.iter().any(|s| {
            matches!(
                s,
                SorobanStmt::Expr(SorobanExpr::RawHostCall { function, .. })
                    if function == "unknown_op"
            )
        });
        assert!(
            kept_a_raw_host_call,
            "orphan RawHostCall must survive DCE; got: {out:?}"
        );
    }

    // ----- Val tag expression walkers (issue #4) ----------------------

    #[test]
    fn expr_contains_recurses_into_val_tag() {
        let needle = SorobanExpr::Param("x".to_string());
        let tag = SorobanExpr::ValTag(Box::new(SorobanExpr::Param("x".to_string())));
        assert!(expr_contains(&tag, &needle));
        // ValTagName is a leaf and never contains another expr.
        assert!(!expr_contains(
            &SorobanExpr::ValTagName("VecObject".to_string()),
            &needle
        ));
    }

    #[test]
    fn invalidate_seen_gets_for_expr_walks_val_tag() {
        let mut seen = Vec::new();
        // Both variants must be handled without panicking.
        invalidate_seen_gets_for_expr(
            &SorobanExpr::ValTag(Box::new(SorobanExpr::Param("v".to_string()))),
            &mut seen,
        );
        invalidate_seen_gets_for_expr(&SorobanExpr::ValTagName("Void".to_string()), &mut seen);
        assert!(seen.is_empty());
    }

    #[test]
    fn expr_mentions_other_params_sees_through_val_tag() {
        // ValTag wraps another param → mentions it.
        let tag = SorobanExpr::ValTag(Box::new(SorobanExpr::Param("other".to_string())));
        assert!(expr_mentions_other_params(&tag, "self"));
        // ValTagName is a leaf with no params.
        assert!(!expr_mentions_other_params(
            &SorobanExpr::ValTagName("VecObject".to_string()),
            "self"
        ));
    }

    // ----- for-loop recovery (issue #6, Step 2) -----------------------

    fn contract_err(variant: &str, code: u32) -> SorobanExpr {
        SorobanExpr::PanicWithError(Box::new(SorobanExpr::ContractError {
            error_code: code,
            error_type: Some("RouterError".into()),
            variant_name: Some(variant.into()),
        }))
    }

    fn vec_get(p: &str, idx: SorobanExpr) -> SorobanExpr {
        SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::Param(p.into())),
            method: "get".into(),
            args: vec![idx],
        }
    }

    /// A mangled validation block carrying BOTH `TokensNotSorted` and
    /// `DuplicatesNotAllowed` over `tokens.get(..)` lifts to a clean
    /// `for i in 1..tokens.len()` with no `todo!`.
    #[test]
    fn recover_tokens_sorted_validation_fires_on_both_error_codes() {
        cov_mark::check!(tokens_sorted_validation_recovered);
        let mangled = SorobanStmt::If {
            condition: SorobanExpr::Ne(
                Box::new(SorobanExpr::UnknownVal),
                Box::new(SorobanExpr::I32Literal(0)),
            ),
            then_body: vec![
                SorobanStmt::Loop {
                    body: vec![
                        SorobanStmt::Expr(vec_get("tokens", SorobanExpr::U32Literal(1))),
                        SorobanStmt::If {
                            condition: SorobanExpr::Gt(
                                Box::new(SorobanExpr::Local(3)),
                                Box::new(vec_get("tokens", SorobanExpr::U32Literal(1))),
                            ),
                            then_body: vec![SorobanStmt::Expr(contract_err(
                                "TokensNotSorted",
                                2002,
                            ))],
                            else_body: vec![],
                        },
                    ],
                },
                SorobanStmt::Expr(contract_err("DuplicatesNotAllowed", 315)),
            ],
            else_body: vec![],
        };
        let out = recover_tokens_sorted_validation(vec![mangled]);
        assert!(
            matches!(out.first(), Some(SorobanStmt::For { var, .. }) if var == "i"),
            "expected a recovered for-loop, got {out:?}"
        );
        if let Some(SorobanStmt::For { start, end, .. }) = out.first() {
            assert!(matches!(start, SorobanExpr::U32Literal(1)));
            assert!(matches!(end, SorobanExpr::MethodCall { method, .. } if method == "len"));
        }
    }

    /// Gating: a loop with only ONE of the two error codes is NOT a token-sort
    /// validation and must be left untouched (never fabricate a sorted+unique check).
    #[test]
    fn recover_tokens_sorted_validation_skips_single_error_code() {
        let only_sorted = SorobanStmt::Loop {
            body: vec![
                SorobanStmt::Expr(vec_get("tokens", SorobanExpr::U32Literal(0))),
                SorobanStmt::Expr(contract_err("TokensNotSorted", 2002)),
            ],
        };
        let out = recover_tokens_sorted_validation(vec![only_sorted.clone()]);
        assert!(
            matches!(out.first(), Some(SorobanStmt::Loop { .. })),
            "must not rewrite a loop missing DuplicatesNotAllowed, got {out:?}"
        );
    }

    /// `let mut var_0 = 0; loop { if var_0 == 5 { break } acc; var_0 += 1 }`
    /// with the counter dead afterward becomes `for var_0 in 0..5 { acc }`,
    /// dropping the counter's `let` and its increment.
    #[test]
    fn recover_for_loops_rewrites_dead_counter() {
        let stmts = vec![
            SorobanStmt::Let {
                name: "var_0".into(),
                mutable: true,
                value: SorobanExpr::I64Literal(0),
            },
            SorobanStmt::Loop {
                body: vec![
                    SorobanStmt::If {
                        condition: SorobanExpr::Eq(
                            Box::new(SorobanExpr::Local(0)),
                            Box::new(SorobanExpr::I64Literal(5)),
                        ),
                        then_body: vec![SorobanStmt::Break],
                        else_body: Vec::new(),
                    },
                    SorobanStmt::Assign {
                        target: "var_2".into(),
                        value: SorobanExpr::Add(
                            Box::new(SorobanExpr::Local(2)),
                            Box::new(SorobanExpr::Local(0)),
                        ),
                    },
                    SorobanStmt::Assign {
                        target: "var_0".into(),
                        value: SorobanExpr::Add(
                            Box::new(SorobanExpr::Local(0)),
                            Box::new(SorobanExpr::I64Literal(1)),
                        ),
                    },
                ],
            },
            SorobanStmt::Return(Some(SorobanExpr::Local(2))), // counter unused here
        ];
        let out = recover_for_loops(stmts);
        // The `let mut var_0` is gone; the loop is a `for` with a single-stmt body.
        assert_eq!(out.len(), 2, "expected For + Return; got: {out:?}");
        match &out[0] {
            SorobanStmt::For {
                var, step, body, ..
            } => {
                assert_eq!(var, "var_0");
                assert_eq!(*step, 1);
                assert_eq!(body.len(), 1, "increment/guard not stripped: {body:?}");
                assert!(matches!(
                    &body[0],
                    SorobanStmt::Assign { target, .. } if target == "var_2"
                ));
            }
            other => panic!("expected For; got: {other:?}"),
        }
    }

    /// When the counter is read after the loop, `for` (which scopes the counter)
    /// is unsafe, so the loop must stay a `Loop`.
    #[test]
    fn recover_for_loops_keeps_loop_when_counter_live_out() {
        let stmts = vec![
            SorobanStmt::Let {
                name: "var_0".into(),
                mutable: true,
                value: SorobanExpr::I64Literal(0),
            },
            SorobanStmt::Loop {
                body: vec![
                    SorobanStmt::If {
                        condition: SorobanExpr::Eq(
                            Box::new(SorobanExpr::Local(0)),
                            Box::new(SorobanExpr::I64Literal(5)),
                        ),
                        then_body: vec![SorobanStmt::Break],
                        else_body: Vec::new(),
                    },
                    SorobanStmt::Assign {
                        target: "var_0".into(),
                        value: SorobanExpr::Add(
                            Box::new(SorobanExpr::Local(0)),
                            Box::new(SorobanExpr::I64Literal(1)),
                        ),
                    },
                ],
            },
            SorobanStmt::Return(Some(SorobanExpr::Local(0))), // counter live-out
        ];
        let out = recover_for_loops(stmts);
        assert!(
            matches!(&out[0], SorobanStmt::Let { .. })
                && matches!(&out[1], SorobanStmt::Loop { .. }),
            "loop with live-out counter must not become a `for`; got: {out:?}"
        );
    }

    // ----- ValTag argument-guard removal (compile-fidelity) -----

    #[test]
    fn val_tag_guard_stripped() {
        // `if v.get_tag() != Tag::AddressObject { panic!() } return v;`
        // The SDK arg-validation guard must be removed (it renders as non-public
        // `Val::get_tag()`/`Tag` API), leaving the real body intact.
        let guard = SorobanStmt::If {
            condition: SorobanExpr::Ne(
                Box::new(SorobanExpr::ValTag(Box::new(param("v")))),
                Box::new(SorobanExpr::ValTagName("AddressObject".to_string())),
            ),
            then_body: vec![SorobanStmt::Expr(SorobanExpr::Panic)],
            else_body: vec![],
        };
        let out = remove_val_tag_guards(vec![guard, ret(param("v"))]);
        assert_eq!(out.len(), 1, "guard not removed: {out:?}");
        assert!(matches!(&out[0], SorobanStmt::Return(Some(SorobanExpr::Param(n))) if n == "v"));
    }

    #[test]
    fn val_tag_guard_kept_when_body_is_real_logic() {
        // A ValTag comparison whose body is NOT a panic is left untouched —
        // only the panic-guard marshalling shape is stripped.
        let cond = SorobanExpr::Ne(
            Box::new(SorobanExpr::ValTag(Box::new(param("v")))),
            Box::new(SorobanExpr::ValTagName("U32Val".to_string())),
        );
        let stmt = SorobanStmt::If {
            condition: cond,
            then_body: vec![ret(u64_lit(1))],
            else_body: vec![],
        };
        let out = remove_val_tag_guards(vec![stmt]);
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0], SorobanStmt::If { .. }));
    }

    // ----- Orphan linear-memory marshalling removal (compile-fidelity) -----

    #[test]
    fn orphan_linear_memory_marshalling_stripped() {
        // A standalone `map_unpack_to_linear_memory(..)` host call (result
        // discarded) renders as non-public `env.map()…` API and must be dropped.
        let marshalling = SorobanStmt::Expr(SorobanExpr::RawHostCall {
            module: "m".to_string(),
            function: "map_unpack_to_linear_memory".to_string(),
            args: vec![param("proof"), u64_lit(1048588)],
        });
        let out = remove_orphan_host_calls(vec![marshalling, ret(param("proof"))]);
        assert_eq!(out.len(), 1, "marshalling not removed: {out:?}");
        assert!(
            matches!(&out[0], SorobanStmt::Return(Some(SorobanExpr::Param(n))) if n == "proof")
        );
    }

    // ----- Storage-dispatch empty-arm recovery (compile-fidelity, constructor #16) -----

    #[test]
    fn empty_storage_dispatch_arms_filled() {
        // `get_data` shape: WASM LTO merged the three per-tier reads so the lifter only
        // recovered the `Temp` arm; `Persistent`/`Instance` came back empty.
        fn get(st: StorageType) -> SorobanStmt {
            SorobanStmt::Expr(SorobanExpr::StorageGet {
                storage_type: st,
                key: Box::new(param("key")),
                unwrap: false,
            })
        }
        fn arm(variant: &str, body: Vec<SorobanStmt>) -> MatchArm {
            MatchArm {
                pattern: MatchPattern::EnumVariant {
                    type_name: "DataKey".to_string(),
                    variant: variant.to_string(),
                    bindings: vec!["_".to_string()],
                },
                body,
            }
        }
        let stmts = vec![SorobanStmt::Match {
            scrutinee: param("key"),
            arms: vec![
                arm("Persistent", vec![]),
                arm("Temp", vec![get(StorageType::Temporary)]),
                arm("Instance", vec![]),
            ],
        }];

        let out = recover_match_arm_storage_keys(stmts);
        let SorobanStmt::Match { arms, .. } = &out[0] else {
            panic!("expected match, got {out:?}");
        };
        // Every arm now reads storage at its own tier, derived from the variant name.
        let tier = |a: &MatchArm| match a.body.as_slice() {
            [SorobanStmt::Expr(SorobanExpr::StorageGet { storage_type, .. })] => *storage_type,
            other => panic!("arm body is not a single StorageGet: {other:?}"),
        };
        assert_eq!(tier(&arms[0]), StorageType::Persistent);
        assert_eq!(tier(&arms[1]), StorageType::Temporary);
        assert_eq!(tier(&arms[2]), StorageType::Instance);
    }

    #[test]
    fn storage_dispatch_fill_skips_non_storage_match() {
        // A match whose non-empty arms aren't single StorageGets must be left alone.
        let stmts = vec![SorobanStmt::Match {
            scrutinee: param("key"),
            arms: vec![
                MatchArm {
                    pattern: MatchPattern::EnumVariant {
                        type_name: "E".to_string(),
                        variant: "A".to_string(),
                        bindings: vec!["_".to_string()],
                    },
                    body: vec![],
                },
                MatchArm {
                    pattern: MatchPattern::EnumVariant {
                        type_name: "E".to_string(),
                        variant: "B".to_string(),
                        bindings: vec!["_".to_string()],
                    },
                    body: vec![ret(i64_lit(7))],
                },
            ],
        }];
        let out = recover_match_arm_storage_keys(stmts);
        let SorobanStmt::Match { arms, .. } = &out[0] else {
            panic!("expected match");
        };
        assert!(arms[0].body.is_empty(), "empty arm should stay empty");
    }

    // ----- Invoke return-type recovery + Val type-tag assertion husk drop -----

    fn unknown_tag_husk(op_eq: bool, tag: u32, error: bool) -> SorobanStmt {
        let cond = Box::new(SorobanExpr::UnknownVal);
        let lit = Box::new(SorobanExpr::U32Literal(tag));
        let condition = if op_eq {
            SorobanExpr::Eq(cond, lit)
        } else {
            SorobanExpr::Ne(cond, lit)
        };
        let panic = if error {
            SorobanExpr::PanicWithError(Box::new(SorobanExpr::U32Literal(7)))
        } else {
            SorobanExpr::Panic
        };
        SorobanStmt::If {
            condition,
            then_body: vec![SorobanStmt::Expr(panic)],
            else_body: vec![],
        }
    }

    fn bare_invoke() -> SorobanExpr {
        SorobanExpr::InvokeContract {
            address: Box::new(SorobanExpr::UnknownVal),
            function: Box::new(SorobanExpr::SymbolLiteral("get_x".to_string())),
            args: vec![],
            return_type: None,
        }
    }

    #[test]
    fn invoke_return_type_recovered_from_i128_tag_husk() {
        // `invoke(...); if todo!() != 69 { panic!() }` → `invoke::<i128>(...)`,
        // and the type-assertion husk is then stripped.
        let stmts = vec![
            SorobanStmt::Expr(bare_invoke()),
            unknown_tag_husk(false, 69, false),
        ];
        let typed = recover_invoke_return_types(stmts);
        match &typed[0] {
            SorobanStmt::Expr(SorobanExpr::InvokeContract { return_type, .. }) => {
                assert_eq!(return_type.as_deref(), Some("i128"));
            }
            other => panic!("expected typed invoke, got {other:?}"),
        }
        let dropped = remove_val_tag_guards(typed);
        assert_eq!(
            dropped.len(),
            1,
            "type-assert husk not dropped: {dropped:?}"
        );
    }

    #[test]
    fn invoke_return_type_recovered_through_let_binding() {
        let stmts = vec![
            SorobanStmt::Let {
                name: "balance".to_string(),
                mutable: true,
                value: bare_invoke(),
            },
            unknown_tag_husk(false, 6, false),
        ];
        let typed = recover_invoke_return_types(stmts);
        match &typed[0] {
            SorobanStmt::Let {
                value: SorobanExpr::InvokeContract { return_type, .. },
                ..
            } => assert_eq!(return_type.as_deref(), Some("u64")),
            other => panic!("expected typed let-invoke, got {other:?}"),
        }
    }

    #[test]
    fn aggregate_tag_drops_husk_but_leaves_invoke_untyped() {
        // VecObject (75) has no recoverable element type: drop the husk but keep
        // the invoke `Val`-typed rather than guess.
        let stmts = vec![
            SorobanStmt::Expr(bare_invoke()),
            unknown_tag_husk(false, 75, false),
        ];
        let typed = recover_invoke_return_types(stmts);
        match &typed[0] {
            SorobanStmt::Expr(SorobanExpr::InvokeContract { return_type, .. }) => {
                assert!(return_type.is_none(), "aggregate tag must not set a type");
            }
            other => panic!("expected invoke, got {other:?}"),
        }
        let dropped = remove_val_tag_guards(typed);
        assert_eq!(
            dropped.len(),
            1,
            "aggregate-tag husk not dropped: {dropped:?}"
        );
    }

    #[test]
    fn type_tag_husk_dropped_without_preceding_invoke() {
        // The husk is droppable on its own (e.g. after `ledger().timestamp()`).
        let out = remove_val_tag_guards(vec![unknown_tag_husk(false, 69, false)]);
        assert!(
            out.is_empty(),
            "standalone type-tag husk not dropped: {out:?}"
        );
    }

    #[test]
    fn ambiguous_and_nontag_husks_are_kept() {
        // Tag::True (1), Tag::Void (2), Tag::False (0) and non-tag 24 are NOT
        // dropped — dropping them would be a wrong recovery, not noise removal.
        for (op_eq, tag) in [(true, 1u32), (false, 2), (true, 0), (true, 24)] {
            let out = remove_val_tag_guards(vec![unknown_tag_husk(op_eq, tag, false)]);
            assert_eq!(out.len(), 1, "husk for tag {tag} was wrongly dropped");
        }
    }

    #[test]
    fn type_tag_guard_with_error_body_is_kept() {
        // A `panic_with_error!` body is user logic, never the SDK type check —
        // keep it even though the constant is a genuine type tag.
        let out = remove_val_tag_guards(vec![unknown_tag_husk(false, 69, true)]);
        assert_eq!(out.len(), 1, "error guard must not be dropped: {out:?}");
    }
}
