use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use stellar_xdr::curr::ScSpecTypeDef;

use super::functions::{
    generate_stmt, generate_stmt_result_wrapped, generate_stmts_with_tail,
    generate_stmts_with_tail_result_wrapped, safe_ident,
};
use super::imports::{compute_extra_imports, compute_imports};
use crate::ir::high_level_ir::{ContractFn, ContractModule, CryptoUsage};
use crate::ir::soroban_ir::{SorobanExpr, SorobanStmt};
use crate::spec::registry::TypeRegistry;
use crate::wasm::WasmType;

/// Assemble a complete Rust source file from a ContractModule
pub fn assemble_module(module: &ContractModule, registry: &TypeRegistry) -> TokenStream {
    let imports = compute_imports(module, registry);
    let extra_imports = compute_extra_imports(module);

    // Type definitions
    let type_tokens: Vec<_> = module
        .types
        .iter()
        .filter_map(|t| t.generated_tokens.clone())
        .collect();

    // Error enum definitions
    let error_tokens: Vec<_> = module
        .error_enums
        .iter()
        .filter_map(|t| t.generated_tokens.clone())
        .collect();

    // Event definitions
    let event_tokens: Vec<_> = module
        .events
        .iter()
        .filter_map(|t| t.generated_tokens.clone())
        .collect();

    // Contract struct
    let contract_name = safe_ident(&module.contract_struct);

    // Determine contract's error enum name for Result return types
    let error_enum_name: Option<String> = if module.error_enums.len() == 1 {
        Some(module.error_enums[0].name.clone())
    } else {
        None
    };

    // Contract functions
    let fn_tokens: Vec<_> = module
        .functions
        .iter()
        .map(|f| generate_contract_fn(f, &error_enum_name, &module.crypto_usage))
        .collect();

    quote! {
        #![no_std]
        #imports
        #extra_imports

        #(#type_tokens)*
        #(#error_tokens)*
        #(#event_tokens)*

        #[contract]
        pub struct #contract_name;

        #[contractimpl]
        impl #contract_name {
            #(#fn_tokens)*
        }
    }
}

/// Assemble a Rust source file from a generic (non-Soroban) WASM module.
/// Emits plain `pub fn` functions without Soroban annotations.
pub fn assemble_generic_module(module: &ContractModule) -> TokenStream {
    let fn_tokens: Vec<_> = module.functions.iter().map(generate_generic_fn).collect();

    quote! {
        #(#fn_tokens)*
    }
}

fn wasm_type_token(wt: &WasmType) -> TokenStream {
    match wt {
        WasmType::I32 => quote! { i32 },
        WasmType::I64 => quote! { i64 },
        WasmType::F32 => quote! { f32 },
        WasmType::F64 => quote! { f64 },
    }
}

fn generic_wasm_return_type(results: &[WasmType]) -> Option<TokenStream> {
    match results {
        [] => None,
        [wt] => {
            let ty = wasm_type_token(wt);
            Some(quote! { -> #ty })
        }
        multi => {
            let tys: Vec<_> = multi.iter().map(wasm_type_token).collect();
            Some(quote! { -> (#(#tys),*) })
        }
    }
}

fn generate_generic_fn(func: &ContractFn) -> TokenStream {
    let fn_name = safe_ident(&func.name);

    // Build parameter list from wasm_signature if available
    let mut params = Vec::new();
    if let Some(ref sig) = func.wasm_signature {
        for (i, wt) in sig.params.iter().enumerate() {
            let p_name = if let Some(p) = func.params.get(i) {
                safe_ident(&p.name)
            } else {
                format_ident!("arg{}", i)
            };
            let p_type = wasm_type_token(wt);
            params.push(quote! { #p_name: #p_type });
        }
    } else {
        for param in &func.params {
            let p_name = safe_ident(&param.name);
            let p_type = super::types::generate_type_ident(&param.type_def);
            params.push(quote! { #p_name: #p_type });
        }
    }

    // Return type
    let return_type = if let Some(ref sig) = func.wasm_signature {
        generic_wasm_return_type(&sig.results)
    } else {
        func.return_type.as_ref().and_then(|rt| {
            if matches!(rt, ScSpecTypeDef::Void) {
                None
            } else {
                let rt_tokens = super::types::generate_type_ident(rt);
                Some(quote! { -> #rt_tokens })
            }
        })
    };

    let has_return_type = return_type.is_some();
    let body_stmts: Vec<_> = if has_return_type && !func.body.is_empty() {
        generate_stmts_with_tail(&func.body)
    } else {
        func.body.iter().map(generate_stmt).collect()
    };

    let body = if body_stmts.is_empty() && has_return_type {
        quote! { todo!("decompiled function body") }
    } else {
        quote! { #(#body_stmts)* }
    };

    quote! {
        pub fn #fn_name(#(#params),*) #return_type {
            #body
        }
    }
}

fn generate_contract_fn(
    func: &ContractFn,
    error_enum_name: &Option<String>,
    crypto: &CryptoUsage,
) -> TokenStream {
    let fn_name = if func.is_constructor {
        format_ident!("__constructor")
    } else if func.is_check_auth {
        format_ident!("__check_auth")
    } else {
        safe_ident(&func.name)
    };

    // Build parameter list
    let mut params = Vec::new();
    if func.takes_env {
        params.push(quote! { env: Env });
    }
    for param in &func.params {
        // If a user param is literally named `env` and we also inject the
        // `env: Env` host parameter, the user param shadows the injected one
        // and breaks hard-coded `&env` / `env.storage()` call sites in the
        // body. Rename the colliding user param to `env_`.
        let resolved_name: &str = if func.takes_env && param.name == "env" {
            "env_"
        } else {
            &param.name
        };
        let p_name = safe_ident(resolved_name);
        let p_type = if crypto.has_any() {
            super::types::generate_type_ident_crypto(&param.type_def, crypto, Some(&param.name))
        } else {
            super::types::generate_type_ident(&param.type_def)
        };
        params.push(quote! { #p_name: #p_type });
    }

    // Return type — substitute contract error enum in Result<T, Error>
    let gen_type = |spec: &ScSpecTypeDef| {
        if crypto.has_any() {
            super::types::generate_type_ident_crypto(spec, crypto, None)
        } else {
            super::types::generate_type_ident(spec)
        }
    };
    let return_type = func.return_type.as_ref().and_then(|rt| {
        // Suppress explicit `-> ()` — Rust convention is to omit void return type
        if matches!(rt, ScSpecTypeDef::Void) {
            return None;
        }
        Some(if let ScSpecTypeDef::Result(r) = rt {
            let ok = gen_type(&r.ok_type);
            if matches!(&*r.error_type, ScSpecTypeDef::Error)
                && let Some(ename) = error_enum_name
            {
                let err = safe_ident(ename);
                return Some(quote! { -> Result<#ok, #err> });
            }
            let err = gen_type(&r.error_type);
            quote! { -> Result<#ok, #err> }
        } else {
            let rt_tokens = gen_type(rt);
            quote! { -> #rt_tokens }
        })
    });

    // Body — use result-wrapped generator for Result<T,E>-returning functions so that
    // bare `return error_val` is emitted as `return Err(error_val)` and other returns
    // are emitted as `return Ok(val)`.
    let is_result_return = func
        .return_type
        .as_ref()
        .is_some_and(|rt| matches!(rt, ScSpecTypeDef::Result { .. }));
    let has_return_type = func
        .return_type
        .as_ref()
        .is_some_and(|rt| !matches!(rt, ScSpecTypeDef::Void));
    let needs_ok_tail = is_result_return && needs_ok_unit_tail(func);
    // Non-unit-returning fn whose body lost its success value (ends in a `()`-typed,
    // non-diverging tail) → append an honest `todo!()` tail. The non-unit analog of
    // `needs_ok_tail`. Disjoint from it by the unit-ok-type exclusion + the
    // `!needs_ok_tail` belt.
    let needs_todo_tail = !needs_ok_tail && needs_todo_value_tail(func);
    let body_stmts: Vec<_> = if is_result_return && !needs_ok_tail && !needs_todo_tail {
        // Use tail form only when the function's own body provides the final return
        generate_stmts_with_tail_result_wrapped(&func.body)
    } else if is_result_return {
        // When Ok(()) or a todo!() tail will be appended, use normal (non-tail) form
        func.body.iter().map(generate_stmt_result_wrapped).collect()
    } else if has_return_type && !func.body.is_empty() && !needs_todo_tail {
        // Strip the trailing semicolon from the last expression to make it a tail expression
        generate_stmts_with_tail(&func.body)
    } else {
        func.body.iter().map(generate_stmt).collect()
    };

    // If needs_ok_tail, append Ok(()) — even for empty bodies (e.g., Result<(), E>
    // functions whose body was all XDR unpacking artifacts that got stripped).
    // If needs_todo_tail, append todo!() — a non-unit return whose value was lost
    // (`todo!()` is `!` and coerces to the return type; honest hole, not a fabrication).
    // Otherwise, empty body + return type → todo!() placeholder.
    // Void-returning functions with empty bodies are valid — they just need `{}`.
    let body = if needs_ok_tail {
        quote! { #(#body_stmts)* Ok(()) }
    } else if needs_todo_tail {
        quote! { #(#body_stmts)* todo!("decompiled return value") }
    } else if body_stmts.is_empty()
        && func
            .return_type
            .as_ref()
            .is_some_and(|t| !matches!(t, stellar_xdr::curr::ScSpecTypeDef::Void))
    {
        quote! { todo!("decompiled function body") }
    } else {
        quote! { #(#body_stmts)* }
    };

    quote! {
        pub fn #fn_name(#(#params),*) #return_type {
            #body
        }
    }
}

/// Check if a Result-returning function needs an `Ok(())` tail expression.
/// This is the case when the Result ok_type is Void and the body doesn't end
/// with an explicit Return statement.
fn needs_ok_unit_tail(func: &ContractFn) -> bool {
    needs_ok_unit_tail_for(&func.return_type, &func.body)
}

/// `needs_ok_unit_tail` parameterized on `(return_type, body)` so non-codegen
/// passes (the get-annotator) can ask the same question without a `ContractFn`.
pub(crate) fn needs_ok_unit_tail_for(
    return_type: &Option<ScSpecTypeDef>,
    body: &[SorobanStmt],
) -> bool {
    let Some(ScSpecTypeDef::Result(r)) = return_type else {
        return false;
    };
    // The unit ok-type renders as `()` either as `Void` or as an empty tuple
    // `()` — the SDK's spec for `Result<(), E>` uses the latter. Both mean the
    // only success value is `Ok(())`, which is faithful to append; a non-unit
    // ok-type (`Result<u128, E>` etc.) is a *lost value* and must stay honest.
    if !is_unit_ok_type(&r.ok_type) {
        return false;
    }
    // If the body's last statement is already a Return, no tail needed
    !matches!(body.last(), Some(SorobanStmt::Return(_)))
}

/// True when codegen will SYNTHESIZE the function's tail expression (`Ok(())` or
/// a `todo!()` value tail) instead of the body supplying it. In that case the
/// body's last statement is NOT the inferable return value, so a trailing
/// discarded `StorageGet` there must be type-annotated rather than left to
/// inference (it was previously mistaken for the return → E0284). Mirrors the two
/// tail-synthesis conditions in `generate_contract_fn`.
pub(crate) fn codegen_synthesizes_tail(
    return_type: &Option<ScSpecTypeDef>,
    body: &[SorobanStmt],
) -> bool {
    needs_ok_unit_tail_for(return_type, body) || needs_todo_value_tail_for(return_type, body)
}

/// Whether a Result ok-type is the unit type `()` — modeled either as `Void` or
/// (as the SDK emits for `Result<(), E>`) an empty tuple.
fn is_unit_ok_type(ok_type: &ScSpecTypeDef) -> bool {
    match ok_type {
        ScSpecTypeDef::Void => true,
        ScSpecTypeDef::Tuple(t) => t.value_types.is_empty(),
        _ => false,
    }
}

/// Whether a **non-unit**-returning function lost its success value — its body
/// ends in a non-diverging `()`-typed tail (the lifter recovered the side effects
/// but not the returned value, so the tail mismatches the declared return type).
/// The faithful completion is a `todo!()` tail: the value is unrecoverable, so an
/// honest hole is correct (a wrong recovery is worse than a `todo!()`). This is
/// the non-unit analog of [`needs_ok_unit_tail`] — they are mutually exclusive by
/// the unit-ok-type exclusion below.
fn needs_todo_value_tail(func: &ContractFn) -> bool {
    needs_todo_value_tail_for(&func.return_type, &func.body)
}

/// `needs_todo_value_tail` parameterized on `(return_type, body)` (see
/// [`needs_ok_unit_tail_for`]).
pub(crate) fn needs_todo_value_tail_for(
    return_type: &Option<ScSpecTypeDef>,
    body: &[SorobanStmt],
) -> bool {
    let Some(rt) = return_type else {
        return false;
    };
    // Non-unit returns only. `Void` has no value to lose; `Result<(), E>` (and a
    // `Void` ok-type) are Lever B's `Ok(())` territory — never steal them.
    match rt {
        ScSpecTypeDef::Void => return false,
        ScSpecTypeDef::Result(r) if is_unit_ok_type(&r.ok_type) => return false,
        _ => {}
    }
    // An empty body is already handled by the `todo!("decompiled function body")`
    // path; only fire when there is a concrete `()`-typed, non-diverging tail.
    match body.last() {
        Some(stmt) => tail_is_unit(stmt),
        None => false,
    }
}

/// Whether a statement in function-tail position evaluates to a non-diverging
/// `()`. Conservative on purpose — only shapes that are *provably* `()` count, so
/// a real recovered value tail is never mistaken for a lost one.
fn tail_is_unit(stmt: &SorobanStmt) -> bool {
    match stmt {
        // `if cond { .. }` with no else is `()` in Rust regardless of the then
        // branch — the strongest, unconditional signal (and the dominant case).
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => {
            if else_body.is_empty() {
                true
            } else {
                stmts_tail_is_unit(then_body) && stmts_tail_is_unit(else_body)
            }
        }
        SorobanStmt::Loop { .. } | SorobanStmt::For { .. } => true,
        SorobanStmt::Block(body) => stmts_tail_is_unit(body),
        SorobanStmt::Expr(e) => expr_is_unit_typed(e),
        // Return / Match / Comment / Break / Continue / Assign / Let → not a
        // non-diverging unit tail (a `Return`/value already produces a value; a
        // diverging panic/todo tail already type-checks). Leave untouched.
        _ => false,
    }
}

/// `()`-ness of a statement block's tail (an empty block is `()`).
fn stmts_tail_is_unit(body: &[SorobanStmt]) -> bool {
    match body.last() {
        Some(stmt) => tail_is_unit(stmt),
        None => true,
    }
}

/// Whether a `SorobanExpr` used as a statement tail is statically `()`-typed.
/// Restricted to the host operations the SDK types as `()`; an arbitrary
/// `MethodCall`/value expr is **not** assumed unit (it may legitimately be the
/// value). Never-typed exprs (`Panic`/`PanicWithError`/`UnknownVal`) are excluded
/// — they already type-check as the tail, so we must not append a dead `todo!()`.
fn expr_is_unit_typed(e: &SorobanExpr) -> bool {
    matches!(
        e,
        SorobanExpr::StorageSet { .. }
            | SorobanExpr::StorageRemove { .. }
            | SorobanExpr::StorageExtendTtl { .. }
            | SorobanExpr::ExtendInstanceAndCodeTtl { .. }
            | SorobanExpr::RequireAuth(_)
            | SorobanExpr::RequireAuthForArgs { .. }
            | SorobanExpr::AuthorizeAsCurrContract(_)
            | SorobanExpr::PublishEvent { .. }
            | SorobanExpr::Log(_)
            | SorobanExpr::PrngReseed(_)
            // A `?` in tail position renders as the `()`-typed statement `expr?;`,
            // so a `todo!()` value tail is appended after it (the computed-getter
            // early-return guard). Never a recovered value itself.
            | SorobanExpr::Try(_)
    )
}

/// Format a token stream into a pretty-printed Rust string
pub fn format_source(tokens: &TokenStream) -> Result<String, syn::Error> {
    let mut file = syn::parse2(tokens.clone())?;
    // Strip explicit Paren nodes from the AST. Our codegen wraps all binary
    // expressions in parens for safety, but prettyplease will re-add parens
    // only where truly needed for precedence/associativity.
    strip_unnecessary_parens(&mut file);
    // Strip `(topics = [...])` from `#[contractevent(...)]` attributes —
    // the Soroban SDK derives the event name from the struct name. Done at
    // the AST level so the rewrite cannot mangle string literals or comments.
    strip_contractevent_topics_ast(&mut file);
    let source = prettyplease::unparse(&file);
    // prettyplease inserts a space between `&` and `env` inside macro
    // invocations (e.g. `panic_with_error!(& env, ...)`) because they are
    // separate tokens. Collapse `& env` back to `&env`, but only outside
    // string literals so contents like `"& env, foo"` are preserved.
    let source = replace_outside_strings(&source, "& env,", "&env,");
    let source = replace_outside_strings(&source, "& env)", "&env)");
    // Collapse single-type turbofish that prettyplease splits across lines, e.g.:
    //   invoke_contract::<\n            u64,\n        >(  →  invoke_contract::<u64>(
    let mut source = collapse_single_turbofish(&source);
    // Ensure trailing newline (Rust convention, matches rustfmt)
    if !source.ends_with('\n') {
        source.push('\n');
    }
    // Try rustfmt post-processing for canonical formatting. Falls back to
    // prettyplease output if rustfmt is unavailable or fails.
    source = try_rustfmt(&source).unwrap_or(source);
    Ok(source)
}

/// Walk an `&str` and apply a `find → replace` substitution, but only when
/// the match site lies outside a Rust string or character literal. Used by
/// post-format passes that would otherwise risk corrupting contract code
/// containing the same substring inside a literal.
fn replace_outside_strings(source: &str, find: &str, replace_with: &str) -> String {
    if find.is_empty() {
        return source.to_string();
    }
    let bytes = source.as_bytes();
    let mut out = String::with_capacity(source.len());
    let mut i = 0;
    // States: Normal, InString, InChar, InRawString { hashes }, LineComment, BlockComment { depth }
    enum St {
        Normal,
        String,
        Char,
        Raw(usize),
        LineComment,
        BlockComment(u32),
    }
    let mut st = St::Normal;
    while i < bytes.len() {
        match st {
            St::Normal => {
                // Detect start of literal/comment context.
                let b = bytes[i];
                // Raw string: r"...", r#"..."#, r##"..."##
                if b == b'r'
                    && (i + 1 < bytes.len() && (bytes[i + 1] == b'"' || bytes[i + 1] == b'#'))
                {
                    let mut j = i + 1;
                    let mut hashes = 0;
                    while j < bytes.len() && bytes[j] == b'#' {
                        hashes += 1;
                        j += 1;
                    }
                    if j < bytes.len() && bytes[j] == b'"' {
                        out.push_str(&source[i..=j]);
                        i = j + 1;
                        st = St::Raw(hashes);
                        continue;
                    }
                }
                if b == b'"' {
                    out.push('"');
                    i += 1;
                    st = St::String;
                    continue;
                }
                if b == b'\'' {
                    out.push('\'');
                    i += 1;
                    st = St::Char;
                    continue;
                }
                if b == b'/' && i + 1 < bytes.len() {
                    if bytes[i + 1] == b'/' {
                        out.push_str("//");
                        i += 2;
                        st = St::LineComment;
                        continue;
                    }
                    if bytes[i + 1] == b'*' {
                        out.push_str("/*");
                        i += 2;
                        st = St::BlockComment(1);
                        continue;
                    }
                }
                if source[i..].starts_with(find) {
                    out.push_str(replace_with);
                    i += find.len();
                    continue;
                }
                out.push(b as char);
                i += 1;
            }
            St::String => {
                let b = bytes[i];
                out.push(b as char);
                i += 1;
                if b == b'\\' && i < bytes.len() {
                    out.push(bytes[i] as char);
                    i += 1;
                } else if b == b'"' {
                    st = St::Normal;
                }
            }
            St::Char => {
                let b = bytes[i];
                out.push(b as char);
                i += 1;
                if b == b'\\' && i < bytes.len() {
                    out.push(bytes[i] as char);
                    i += 1;
                } else if b == b'\'' {
                    st = St::Normal;
                }
            }
            St::Raw(hashes) => {
                if bytes[i] == b'"' {
                    let needed = hashes;
                    let mut ok = true;
                    for k in 1..=needed {
                        if i + k >= bytes.len() || bytes[i + k] != b'#' {
                            ok = false;
                            break;
                        }
                    }
                    if ok {
                        out.push_str(&source[i..=i + needed]);
                        i += needed + 1;
                        st = St::Normal;
                        continue;
                    }
                }
                out.push(bytes[i] as char);
                i += 1;
            }
            St::LineComment => {
                let b = bytes[i];
                out.push(b as char);
                i += 1;
                if b == b'\n' {
                    st = St::Normal;
                }
            }
            St::BlockComment(depth) => {
                if i + 1 < bytes.len() && bytes[i] == b'*' && bytes[i + 1] == b'/' {
                    out.push_str("*/");
                    i += 2;
                    st = if depth == 1 {
                        St::Normal
                    } else {
                        St::BlockComment(depth - 1)
                    };
                    continue;
                }
                if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
                    out.push_str("/*");
                    i += 2;
                    st = St::BlockComment(depth + 1);
                    continue;
                }
                out.push(bytes[i] as char);
                i += 1;
            }
        }
    }
    out
}

/// Strip the `topics = [...]` parameter from `#[contractevent(...)]`
/// attributes at the AST level — the Soroban SDK derives the event name
/// from the struct name, so the explicit topics list emitted by
/// `soroban-spec-rust` is redundant. Operating on the parsed `syn::File`
/// avoids any risk of corrupting string literals or comments that happen
/// to contain the same substring.
fn strip_contractevent_topics_ast(file: &mut syn::File) {
    use syn::visit_mut::VisitMut;
    struct V;
    impl VisitMut for V {
        fn visit_attribute_mut(&mut self, attr: &mut syn::Attribute) {
            if attr.path().is_ident("contractevent")
                && let syn::Meta::List(list) = &attr.meta
            {
                // Collapse `#[contractevent(topics = [...])]` to bare
                // `#[contractevent]`. We do this only when the attribute
                // contains *only* a `topics = ...` clause; if other future
                // parameters appear we preserve them.
                let only_has_topics = syn::parse2::<TopicsOnly>(list.tokens.clone()).is_ok();
                if only_has_topics {
                    let path = list.path.clone();
                    attr.meta = syn::Meta::Path(path);
                }
            }
            syn::visit_mut::visit_attribute_mut(self, attr);
        }
    }

    // Helper parse target: matches `topics = [...]` exactly.
    struct TopicsOnly;
    impl syn::parse::Parse for TopicsOnly {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let ident: syn::Ident = input.parse()?;
            if ident != "topics" {
                return Err(input.error("expected `topics`"));
            }
            let _: syn::Token![=] = input.parse()?;
            let _: syn::ExprArray = input.parse()?;
            if !input.is_empty() {
                return Err(input.error("unexpected trailing tokens"));
            }
            Ok(TopicsOnly)
        }
    }

    V.visit_file_mut(file);
}

/// Try to format source code with rustfmt. Returns None if rustfmt is
/// unavailable or the formatting fails.
fn try_rustfmt(source: &str) -> Option<String> {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new("rustfmt")
        .arg("--edition=2021")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.take()?.write_all(source.as_bytes()).ok()?;
    let output = child.wait_with_output().ok()?;
    if output.status.success() {
        String::from_utf8(output.stdout).ok()
    } else {
        None
    }
}

/// Remove all explicit `ExprParen` wrapper nodes from the AST.
/// prettyplease handles precedence-based parenthesization itself, so explicit
/// Paren nodes from our codegen just add unnecessary visual noise.
fn strip_unnecessary_parens(file: &mut syn::File) {
    for item in &mut file.items {
        strip_parens_item(item);
    }
}

fn strip_parens_item(item: &mut syn::Item) {
    if let syn::Item::Impl(imp) = item {
        for item in &mut imp.items {
            if let syn::ImplItem::Fn(f) = item {
                for stmt in &mut f.block.stmts {
                    strip_parens_stmt(stmt);
                }
            }
        }
    }
}

fn strip_parens_stmt(stmt: &mut syn::Stmt) {
    match stmt {
        syn::Stmt::Local(local) => {
            if let Some(init) = &mut local.init {
                strip_parens_expr(&mut init.expr);
            }
        }
        syn::Stmt::Expr(expr, _) => strip_parens_expr(expr),
        _ => {}
    }
}

fn strip_parens_expr(expr: &mut syn::Expr) {
    // First recurse into sub-expressions
    match expr {
        syn::Expr::Binary(b) => {
            strip_parens_expr(&mut b.left);
            strip_parens_expr(&mut b.right);
        }
        syn::Expr::Unary(u) => strip_parens_expr(&mut u.expr),
        syn::Expr::Reference(r) => strip_parens_expr(&mut r.expr),
        syn::Expr::Return(r) => {
            if let Some(e) = &mut r.expr {
                strip_parens_expr(e);
            }
        }
        syn::Expr::Call(c) => {
            strip_parens_expr(&mut c.func);
            for arg in &mut c.args {
                strip_parens_expr(arg);
            }
        }
        syn::Expr::MethodCall(m) => {
            strip_parens_expr(&mut m.receiver);
            for arg in &mut m.args {
                strip_parens_expr(arg);
            }
        }
        syn::Expr::Block(b) => {
            for stmt in &mut b.block.stmts {
                strip_parens_stmt(stmt);
            }
        }
        syn::Expr::If(i) => {
            strip_parens_expr(&mut i.cond);
            for stmt in &mut i.then_branch.stmts {
                strip_parens_stmt(stmt);
            }
            if let Some((_, else_branch)) = &mut i.else_branch {
                strip_parens_expr(else_branch);
            }
        }
        syn::Expr::Match(m) => {
            strip_parens_expr(&mut m.expr);
            for arm in &mut m.arms {
                strip_parens_expr(&mut arm.body);
            }
        }
        syn::Expr::Tuple(t) => {
            for elem in &mut t.elems {
                strip_parens_expr(elem);
            }
        }
        syn::Expr::Struct(s) => {
            for field in &mut s.fields {
                strip_parens_expr(&mut field.expr);
            }
        }
        syn::Expr::Assign(a) => {
            strip_parens_expr(&mut a.left);
            strip_parens_expr(&mut a.right);
        }
        syn::Expr::Field(f) => strip_parens_expr(&mut f.base),
        syn::Expr::Range(r) => {
            if let Some(start) = &mut r.start {
                strip_parens_expr(start);
            }
            if let Some(end) = &mut r.end {
                strip_parens_expr(end);
            }
        }
        syn::Expr::Loop(l) => {
            for stmt in &mut l.body.stmts {
                strip_parens_stmt(stmt);
            }
        }
        syn::Expr::While(w) => {
            strip_parens_expr(&mut w.cond);
            for stmt in &mut w.body.stmts {
                strip_parens_stmt(stmt);
            }
        }
        _ => {}
    }
    // Then unwrap Paren at this level
    if let syn::Expr::Paren(paren) = expr {
        *expr = *paren.expr.clone();
    }
}

/// Collapse single-type turbofish that `prettyplease` splits across 3 lines:
/// ```text
///   invoke_contract::<
///           u64,
///       >(
/// ```
/// into the compact `invoke_contract::<u64>(` form.
fn collapse_single_turbofish(source: &str) -> String {
    let lines: Vec<&str> = source.lines().collect();
    let mut result = Vec::with_capacity(lines.len());
    let mut i = 0;
    while i < lines.len() {
        if i + 2 < lines.len() && lines[i].trim_end().ends_with("::<") {
            let type_line = lines[i + 1].trim();
            let close_line = lines[i + 2].trim();
            // Match: TYPE, (single word/path with comma) followed by >( ...
            if type_line.ends_with(',') && close_line.starts_with(">(") {
                let ty = type_line.trim_end_matches(',').trim();
                // Only collapse simple types (identifiers and paths)
                if !ty.is_empty()
                    && ty
                        .chars()
                        .all(|c| c.is_alphanumeric() || c == '_' || c == ':')
                {
                    let line = lines[i].trim_end();
                    let prefix = &line[..line.len() - 3]; // strip "::<"
                    let suffix = close_line.trim_start_matches('>');
                    result.push(format!("{prefix}::<{ty}>{suffix}"));
                    i += 3;
                    continue;
                }
            }
        }
        result.push(lines[i].to_string());
        i += 1;
    }
    result.join("\n")
}

#[cfg(test)]
mod tests {
    use super::{assemble_generic_module, codegen_synthesizes_tail, format_source};
    use crate::ir::high_level_ir::{ContractFn, ContractModule, WasmFnSignature};
    use crate::ir::soroban_ir::{SorobanExpr, SorobanStmt};
    use crate::wasm::WasmType;

    #[test]
    fn generic_codegen_preserves_multivalue_wasm_returns() {
        let mut module = ContractModule::new("test".to_string());
        module.is_soroban = false;
        module.functions.push(ContractFn {
            name: "pair".to_string(),
            params: Vec::new(),
            return_type: None,
            body: vec![SorobanStmt::Return(Some(SorobanExpr::TupleConstruct(
                vec![SorobanExpr::I32Literal(1), SorobanExpr::I64Literal(2)],
            )))],
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: Some(WasmFnSignature {
                params: Vec::new(),
                results: vec![WasmType::I32, WasmType::I64],
            }),
        });

        let tokens = assemble_generic_module(&module);
        let formatted = format_source(&tokens).expect("generic module should format");

        assert!(formatted.contains("pub fn pair() -> (i32, i64)"));
        assert!(formatted.contains("(1, 2)"));
    }

    use super::assemble_module;
    use crate::spec::registry::TypeRegistry;
    use quote::quote;
    use std::collections::BTreeMap;

    fn empty_registry() -> TypeRegistry {
        TypeRegistry {
            functions: BTreeMap::new(),
            structs: BTreeMap::new(),
            unions: BTreeMap::new(),
            enums: BTreeMap::new(),
            error_enums: BTreeMap::new(),
            events: BTreeMap::new(),
            meta: Vec::new(),
            spec_entries: Vec::new(),
        }
    }

    fn empty_fn(name: &str) -> ContractFn {
        ContractFn {
            name: name.to_string(),
            params: Vec::new(),
            return_type: None,
            body: Vec::new(),
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: None,
        }
    }

    #[test]
    fn assemble_module_minimal_emits_no_std_and_contract_attr() {
        let mut module = ContractModule::new("Contract".to_string());
        module.functions.push(empty_fn("noop"));
        let registry = empty_registry();
        let tokens = assemble_module(&module, &registry);
        let formatted = format_source(&tokens).expect("must format");
        assert!(formatted.contains("#![no_std]"));
        assert!(formatted.contains("#[contract]"));
        assert!(formatted.contains("#[contractimpl]"));
        assert!(formatted.contains("pub fn noop"));
    }

    #[test]
    fn assemble_module_uses_constructor_block() {
        let mut module = ContractModule::new("Contract".to_string());
        let mut ctor = empty_fn("__constructor");
        ctor.is_constructor = true;
        ctor.takes_env = true;
        module.has_constructor = true;
        module.functions.push(ctor);
        let registry = empty_registry();
        let formatted = format_source(&assemble_module(&module, &registry)).expect("must format");
        assert!(formatted.contains("__constructor"));
    }

    #[test]
    fn assemble_module_with_check_auth_imports_context() {
        let mut module = ContractModule::new("Contract".to_string());
        let mut auth = empty_fn("__check_auth");
        auth.is_check_auth = true;
        module.functions.push(auth);
        let registry = empty_registry();
        let formatted = format_source(&assemble_module(&module, &registry)).expect("must format");
        assert!(
            formatted.contains("use soroban_sdk::auth::Context"),
            "missing Context import: {formatted}"
        );
    }

    #[test]
    fn assemble_module_with_bn254_imports_crypto_aliases() {
        let mut module = ContractModule::new("Contract".to_string());
        module.crypto_usage.uses_bn254 = true;
        module.functions.push(empty_fn("noop"));
        let registry = empty_registry();
        let formatted = format_source(&assemble_module(&module, &registry)).expect("must format");
        assert!(
            formatted.contains("Bn254G1Affine") && formatted.contains("Bn254G2Affine"),
            "missing bn254 crypto import block: {formatted}"
        );
    }

    #[test]
    fn assemble_module_with_bls12_381_imports_crypto_aliases() {
        let mut module = ContractModule::new("Contract".to_string());
        module.crypto_usage.uses_bls12_381 = true;
        module.functions.push(empty_fn("noop"));
        let registry = empty_registry();
        let formatted = format_source(&assemble_module(&module, &registry)).expect("must format");
        assert!(
            formatted.contains("Bls12381Fp") && formatted.contains("Bls12381G2Affine"),
            "missing bls12_381 crypto import block: {formatted}"
        );
    }

    #[test]
    fn format_source_propagates_syn_error_on_invalid_tokens() {
        // `: ;` is not a valid Rust file; format_source should surface a syn::Error
        // rather than panicking.
        let bad: proc_macro2::TokenStream = quote! { : ; };
        let result = format_source(&bad);
        assert!(result.is_err(), "expected error from format_source");
    }

    #[test]
    fn replace_outside_strings_skips_string_literal_contents() {
        // The naive replace would corrupt this string literal; the literal-aware
        // version must leave it untouched.
        let src = r#"fn x() { let _ = "& env, foo"; let y = &env, bar; }"#;
        let out = super::replace_outside_strings(src, "& env,", "&env,");
        // The literal must contain `& env,` verbatim still.
        assert!(out.contains(r#""& env, foo""#), "got: {out}");
        // The non-string occurrence (`= &env, bar`) was already &env-spaced
        // in the source; no replacement was needed there. Verify the literal
        // wasn't merged, by checking the count of the literal-text substring.
        assert_eq!(out.matches("& env,").count(), 1, "got: {out}");
    }

    #[test]
    fn replace_outside_strings_handles_raw_strings_and_comments() {
        let src = r##"// comment with & env,
        fn x() {
            let _ = r#"raw & env, raw"#;
            let _ = r"plain & env, plain";
            // & env, in line comment
            /* & env, in block comment */
        }
        macro_invocation!(& env, body);
        "##;
        let out = super::replace_outside_strings(src, "& env,", "&env,");
        // Line + block comments and raw strings preserve `& env,`.
        assert!(out.contains("// comment with & env,"), "got: {out}");
        assert!(out.contains(r#""raw & env, raw""#), "got: {out}");
        assert!(out.contains(r#""plain & env, plain""#), "got: {out}");
        assert!(out.contains("// & env, in line comment"), "got: {out}");
        assert!(out.contains("/* & env, in block comment */"), "got: {out}");
        // The macro_invocation match is in normal code, so it gets replaced.
        assert!(out.contains("macro_invocation!(&env, body)"), "got: {out}");
    }

    #[test]
    fn strip_contractevent_topics_ast_collapses_to_bare_attr() {
        // Synthesize a minimal file with a #[contractevent(topics = ["transfer"])]
        // attribute and verify the AST pass collapses it to #[contractevent].
        let src: proc_macro2::TokenStream = quote! {
            #[contractevent(topics = ["transfer"])]
            pub struct Transfer { pub amount: i128 }
        };
        let mut file: syn::File = syn::parse2(quote! { #src }).unwrap();
        super::strip_contractevent_topics_ast(&mut file);
        let out = prettyplease::unparse(&file);
        assert!(out.contains("#[contractevent]"), "got: {out}");
        assert!(!out.contains("topics"), "got: {out}");
    }

    #[test]
    fn assemble_generic_module_with_typed_signature() {
        let mut module = ContractModule::new("g".to_string());
        module.is_soroban = false;
        module.functions.push(ContractFn {
            name: "add".to_string(),
            params: Vec::new(),
            return_type: None,
            body: vec![SorobanStmt::Return(Some(SorobanExpr::I32Literal(42)))],
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: Some(WasmFnSignature {
                params: vec![WasmType::I32, WasmType::I32],
                results: vec![WasmType::I32],
            }),
        });
        let formatted =
            format_source(&assemble_generic_module(&module)).expect("must format generic module");
        assert!(formatted.contains("pub fn add"));
        assert!(formatted.contains("-> i32"));
    }

    use crate::ir::high_level_ir::FnParam;
    use stellar_xdr::curr::{ScSpecTypeBytesN, ScSpecTypeDef, ScSpecTypeResult};

    #[test]
    fn assemble_generic_module_uses_spec_when_no_wasm_signature() {
        // No wasm_signature → params/return come from ScSpecTypeDef.
        let mut module = ContractModule::new("g".to_string());
        module.is_soroban = false;
        module.functions.push(ContractFn {
            name: "spec_only".to_string(),
            params: vec![FnParam {
                name: "addr".to_string(),
                type_def: ScSpecTypeDef::Address,
            }],
            return_type: Some(ScSpecTypeDef::U64),
            body: vec![SorobanStmt::Return(Some(SorobanExpr::U64Literal(7)))],
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: None,
        });
        let formatted =
            format_source(&assemble_generic_module(&module)).expect("must format generic module");
        assert!(
            formatted.contains("pub fn spec_only(addr"),
            "got: {formatted}"
        );
        assert!(formatted.contains("-> u64"), "got: {formatted}");
    }

    #[test]
    fn assemble_generic_module_void_return_has_no_arrow() {
        let mut module = ContractModule::new("g".to_string());
        module.is_soroban = false;
        module.functions.push(ContractFn {
            name: "voidfn".to_string(),
            params: vec![],
            return_type: Some(ScSpecTypeDef::Void),
            body: vec![],
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: None,
        });
        let formatted =
            format_source(&assemble_generic_module(&module)).expect("must format generic module");
        assert!(formatted.contains("pub fn voidfn()"), "got: {formatted}");
        assert!(
            !formatted.contains(" -> "),
            "void should omit arrow: {formatted}"
        );
    }

    fn fn_with_result_return(error_type: ScSpecTypeDef) -> ContractFn {
        ContractFn {
            name: "f".to_string(),
            params: vec![],
            return_type: Some(ScSpecTypeDef::Result(Box::new(ScSpecTypeResult {
                ok_type: Box::new(ScSpecTypeDef::U64),
                error_type: Box::new(error_type),
            }))),
            body: vec![SorobanStmt::Return(Some(SorobanExpr::U64Literal(1)))],
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: None,
        }
    }

    #[test]
    fn assemble_module_result_with_named_error_enum() {
        // Result<T, Error> + exactly one error enum named "Error" → substitutes the
        // enum name into the return type.
        let mut module = ContractModule::new("Contract".to_string());
        module.error_enums.push(crate::ir::high_level_ir::TypeDef {
            kind: crate::ir::high_level_ir::TypeDefKind::ErrorEnum,
            name: "MyError".to_string(),
            generated_tokens: Some(quote! { pub enum MyError { Bad = 1 } }),
        });
        module
            .functions
            .push(fn_with_result_return(ScSpecTypeDef::Error));
        let formatted =
            format_source(&assemble_module(&module, &empty_registry())).expect("must format");
        assert!(
            formatted.contains("Result<u64, MyError>"),
            "expected Result<u64, MyError>: {formatted}"
        );
    }

    #[test]
    fn assemble_module_result_with_non_error_error_type() {
        // Error type is not `Error` (it's a UDT or other type) → just renders verbatim.
        let mut module = ContractModule::new("Contract".to_string());
        // Use U64 as a stand-in "error type" (the codegen path doesn't care semantically).
        module
            .functions
            .push(fn_with_result_return(ScSpecTypeDef::U64));
        let formatted =
            format_source(&assemble_module(&module, &empty_registry())).expect("must format");
        assert!(formatted.contains("Result<u64, u64>"), "got: {formatted}");
    }

    #[test]
    fn assemble_module_with_crypto_substitutes_params() {
        // BLS12-381 active + a fn with BytesN<48> param → param type becomes Bls12381Fp.
        let mut module = ContractModule::new("Contract".to_string());
        module.crypto_usage.uses_bls12_381 = true;
        module.functions.push(ContractFn {
            name: "doit".to_string(),
            params: vec![FnParam {
                name: "x".to_string(),
                type_def: ScSpecTypeDef::BytesN(ScSpecTypeBytesN { n: 48 }),
            }],
            return_type: None,
            body: vec![],
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: None,
        });
        let formatted =
            format_source(&assemble_module(&module, &empty_registry())).expect("must format");
        assert!(formatted.contains("Bls12381Fp"), "got: {formatted}");
    }

    #[test]
    fn assemble_module_result_unit_ok_appends_ok_unit_tail() {
        // Result<(), Error> with no explicit return in body → codegen appends Ok(()).
        let mut module = ContractModule::new("Contract".to_string());
        module.error_enums.push(crate::ir::high_level_ir::TypeDef {
            kind: crate::ir::high_level_ir::TypeDefKind::ErrorEnum,
            name: "MyError".to_string(),
            generated_tokens: Some(quote! { pub enum MyError { Bad = 1 } }),
        });
        module.functions.push(ContractFn {
            name: "do_or_fail".to_string(),
            params: vec![],
            return_type: Some(ScSpecTypeDef::Result(Box::new(ScSpecTypeResult {
                ok_type: Box::new(ScSpecTypeDef::Void),
                error_type: Box::new(ScSpecTypeDef::Error),
            }))),
            // Empty body → expects Ok(()) to be appended.
            body: vec![],
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: None,
        });
        let formatted =
            format_source(&assemble_module(&module, &empty_registry())).expect("must format");
        assert!(
            formatted.contains("Ok(())"),
            "missing Ok(()) tail: {formatted}"
        );
        assert!(
            formatted.contains("Result<(), MyError>"),
            "got: {formatted}"
        );
    }

    #[test]
    fn assemble_module_result_empty_tuple_ok_appends_ok_unit_tail() {
        // The SDK encodes `Result<(), E>`'s ok-type as an *empty tuple*, not
        // `Void`. Both render as `()`, and both must get an `Ok(())` tail — a
        // non-unit ok-type (a lost value) must not.
        use stellar_xdr::curr::ScSpecTypeTuple;
        let mut module = ContractModule::new("Contract".to_string());
        module.error_enums.push(crate::ir::high_level_ir::TypeDef {
            kind: crate::ir::high_level_ir::TypeDefKind::ErrorEnum,
            name: "MyError".to_string(),
            generated_tokens: Some(quote! { pub enum MyError { Bad = 1 } }),
        });
        module.functions.push(ContractFn {
            name: "touch".to_string(),
            params: vec![],
            return_type: Some(ScSpecTypeDef::Result(Box::new(ScSpecTypeResult {
                ok_type: Box::new(ScSpecTypeDef::Tuple(Box::new(ScSpecTypeTuple {
                    value_types: Default::default(),
                }))),
                error_type: Box::new(ScSpecTypeDef::Error),
            }))),
            // Non-Return tail (a discarded expr) → must gain an Ok(()) tail.
            body: vec![SorobanStmt::Expr(SorobanExpr::UnknownVal)],
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: None,
        });
        let formatted =
            format_source(&assemble_module(&module, &empty_registry())).expect("must format");
        assert!(
            formatted.contains("Ok(())"),
            "empty-tuple ok-type must append Ok(()): {formatted}"
        );
    }

    // --- Lever 1: non-unit return with a lost `()` tail → `todo!()` tail ---

    fn fn_with(return_type: Option<ScSpecTypeDef>, body: Vec<SorobanStmt>) -> ContractFn {
        ContractFn {
            name: "f".to_string(),
            params: vec![],
            return_type,
            body,
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: None,
        }
    }

    fn result_ty(ok: ScSpecTypeDef) -> ScSpecTypeDef {
        ScSpecTypeDef::Result(Box::new(ScSpecTypeResult {
            ok_type: Box::new(ok),
            error_type: Box::new(ScSpecTypeDef::Error),
        }))
    }

    fn render_fn(func: ContractFn) -> String {
        let mut module = ContractModule::new("Contract".to_string());
        module.functions.push(func);
        format_source(&assemble_module(&module, &empty_registry())).expect("must format")
    }

    #[test]
    fn result_nonunit_if_without_else_tail_appends_todo() {
        // `Result<u64, E>` whose body ends in `if cond { .. }` (no else → `()`): the
        // success value was lost, so a faithful `todo!()` tail is appended (no `Ok`).
        let body = vec![SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(true),
            then_body: vec![SorobanStmt::Expr(SorobanExpr::StorageExtendTtl {
                storage_type: crate::ir::soroban_ir::StorageType::Instance,
                key: Box::new(SorobanExpr::SymbolLiteral("k".to_string())),
                threshold: Box::new(SorobanExpr::U32Literal(1)),
                extend_to: Box::new(SorobanExpr::U32Literal(2)),
            })],
            else_body: vec![],
        }];
        let out = render_fn(fn_with(Some(result_ty(ScSpecTypeDef::U64)), body));
        assert!(out.contains("todo!"), "missing todo!() tail: {out}");
        assert!(!out.contains("Ok("), "must not Ok-wrap a lost value: {out}");
    }

    #[test]
    fn result_nonunit_explicit_return_not_touched() {
        // A real recovered value tail must be left alone (Ok-wrapped, no todo!()).
        let body = vec![SorobanStmt::Return(Some(SorobanExpr::U64Literal(7)))];
        let out = render_fn(fn_with(Some(result_ty(ScSpecTypeDef::U64)), body));
        assert!(out.contains("Ok(7)"), "expected Ok(7): {out}");
        assert!(!out.contains("todo!"), "must not append a tail: {out}");
    }

    #[test]
    fn result_unit_still_gets_ok_unit_not_todo() {
        // `Result<(), E>` with an if-tail is Lever B's `Ok(())` territory — Lever 1
        // must not steal it.
        let body = vec![SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(true),
            then_body: vec![],
            else_body: vec![],
        }];
        let out = render_fn(fn_with(Some(result_ty(ScSpecTypeDef::Void)), body));
        assert!(out.contains("Ok(())"), "expected Ok(()) tail: {out}");
        assert!(!out.contains("todo!"), "must not append todo!(): {out}");
    }

    #[test]
    fn plain_value_fn_unit_tail_appends_todo() {
        // A plain `-> u64` (non-Result) value fn ending in a unit-typed effect →
        // todo!() tail (exercises the `expr_is_unit_typed` path, not the if path).
        let body = vec![SorobanStmt::Expr(SorobanExpr::StorageExtendTtl {
            storage_type: crate::ir::soroban_ir::StorageType::Instance,
            key: Box::new(SorobanExpr::SymbolLiteral("k".to_string())),
            threshold: Box::new(SorobanExpr::U32Literal(1)),
            extend_to: Box::new(SorobanExpr::U32Literal(2)),
        })];
        let out = render_fn(fn_with(Some(ScSpecTypeDef::U64), body));
        assert!(out.contains("todo!"), "missing todo!() tail: {out}");
    }

    #[test]
    fn result_nonunit_diverging_panic_tail_not_touched() {
        // A diverging `panic_with_error!` tail already type-checks (`!`) — appending
        // a `todo!()` would be dead code AND a false "lost value" (Session-3 trap).
        let body = vec![SorobanStmt::Expr(SorobanExpr::PanicWithError(Box::new(
            SorobanExpr::U32Literal(1),
        )))];
        let out = render_fn(fn_with(Some(result_ty(ScSpecTypeDef::U64)), body));
        assert!(
            !out.contains("decompiled return value"),
            "must not append a todo!() tail after a diverging panic: {out}"
        );
    }

    #[test]
    fn codegen_synthesizes_tail_distinguishes_discarded_from_value_get() {
        // The get-annotator consults this to tell a discarded trailing get (codegen
        // synthesizes the tail) from a value-returning one (body supplies the tail).
        let get = || {
            SorobanStmt::Expr(SorobanExpr::StorageGet {
                storage_type: crate::ir::soroban_ir::StorageType::Instance,
                key: Box::new(SorobanExpr::SymbolLiteral("k".to_string())),
                unwrap: true,
                on_missing: None,
            })
        };
        // `Result<(), E>` ending in a get: `Ok(())` is synthesized → the get is
        // discarded (the bug: it was previously mistaken for the return → E0284).
        assert!(codegen_synthesizes_tail(
            &Some(result_ty(ScSpecTypeDef::Void)),
            &[get()]
        ));
        // `Result<u128, E>` ending in a get: the get IS the return value → not synth.
        assert!(!codegen_synthesizes_tail(
            &Some(result_ty(ScSpecTypeDef::U128)),
            &[get()]
        ));
        // Plain `-> Address` ending in a get: the get is the return value.
        assert!(!codegen_synthesizes_tail(&Some(ScSpecTypeDef::Address), &[get()]));
        // `Result<u128, E>` ending in an if-without-else (lost `()` tail): a
        // `todo!()` value tail is synthesized → the body does not supply the tail.
        let if_unit = SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(true),
            then_body: vec![],
            else_body: vec![],
        };
        assert!(codegen_synthesizes_tail(
            &Some(result_ty(ScSpecTypeDef::U128)),
            std::slice::from_ref(&if_unit)
        ));
        // `Void` / explicit `Return` → nothing synthesized.
        assert!(!codegen_synthesizes_tail(&Some(ScSpecTypeDef::Void), &[get()]));
        assert!(!codegen_synthesizes_tail(
            &Some(result_ty(ScSpecTypeDef::Void)),
            &[SorobanStmt::Return(None)]
        ));
    }

    #[test]
    fn assemble_module_empty_body_with_return_type_emits_todo() {
        // Non-Result return + empty body → todo!() placeholder.
        let mut module = ContractModule::new("Contract".to_string());
        module.functions.push(ContractFn {
            name: "stub".to_string(),
            params: vec![],
            return_type: Some(ScSpecTypeDef::U64),
            body: vec![],
            takes_env: false,
            is_constructor: false,
            is_check_auth: false,
            wrapper_panics: false,
            had_host_calls: false,
            wasm_param_base: 0,
            wasm_signature: None,
        });
        let formatted =
            format_source(&assemble_module(&module, &empty_registry())).expect("must format");
        assert!(
            formatted.contains("todo!(\"decompiled function body\")"),
            "got: {formatted}"
        );
    }
}
