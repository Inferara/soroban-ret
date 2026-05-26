use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use stellar_xdr::curr::ScSpecTypeDef;

use super::functions::{
    generate_stmt, generate_stmt_result_wrapped, generate_stmts_with_tail,
    generate_stmts_with_tail_result_wrapped,
};
use super::imports::{compute_extra_imports, compute_imports};
use crate::ir::high_level_ir::{ContractFn, ContractModule, CryptoUsage};
use crate::ir::soroban_ir::SorobanStmt;
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
    let contract_name = format_ident!("{}", module.contract_struct);

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
    let fn_name = format_ident!("{}", func.name);

    // Build parameter list from wasm_signature if available
    let mut params = Vec::new();
    if let Some(ref sig) = func.wasm_signature {
        for (i, wt) in sig.params.iter().enumerate() {
            let p_name = if let Some(p) = func.params.get(i) {
                format_ident!("{}", p.name)
            } else {
                format_ident!("arg{}", i)
            };
            let p_type = wasm_type_token(wt);
            params.push(quote! { #p_name: #p_type });
        }
    } else {
        for param in &func.params {
            let p_name = format_ident!("{}", param.name);
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
        format_ident!("{}", func.name)
    };

    // Build parameter list
    let mut params = Vec::new();
    if func.takes_env {
        params.push(quote! { env: Env });
    }
    for param in &func.params {
        let p_name = format_ident!("{}", param.name);
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
                && let Some(ename) = error_enum_name {
                    let err = format_ident!("{}", ename);
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
    let body_stmts: Vec<_> = if is_result_return && !needs_ok_tail {
        // Use tail form only when the function's own body provides the final return
        generate_stmts_with_tail_result_wrapped(&func.body)
    } else if is_result_return {
        // When Ok(()) will be appended, use normal (non-tail) form for all statements
        func.body.iter().map(generate_stmt_result_wrapped).collect()
    } else if has_return_type && !func.body.is_empty() {
        // Strip the trailing semicolon from the last expression to make it a tail expression
        generate_stmts_with_tail(&func.body)
    } else {
        func.body.iter().map(generate_stmt).collect()
    };

    // If needs_ok_tail, append Ok(()) — even for empty bodies (e.g., Result<(), E>
    // functions whose body was all XDR unpacking artifacts that got stripped).
    // Otherwise, empty body + return type → todo!() placeholder.
    // Void-returning functions with empty bodies are valid — they just need `{}`.
    let body = if needs_ok_tail {
        quote! { #(#body_stmts)* Ok(()) }
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
    let Some(ScSpecTypeDef::Result(r)) = &func.return_type else {
        return false;
    };
    if !matches!(*r.ok_type, ScSpecTypeDef::Void) {
        return false;
    }
    // If the body's last statement is already a Return, no tail needed
    !matches!(func.body.last(), Some(SorobanStmt::Return(_)))
}

/// Format a token stream into a pretty-printed Rust string
pub fn format_source(tokens: &TokenStream) -> Result<String, syn::Error> {
    let mut file = syn::parse2(tokens.clone())?;
    // Strip explicit Paren nodes from the AST. Our codegen wraps all binary
    // expressions in parens for safety, but prettyplease will re-add parens
    // only where truly needed for precedence/associativity.
    strip_unnecessary_parens(&mut file);
    let source = prettyplease::unparse(&file);
    // prettyplease inserts a space between `&` and `env` inside macro invocations
    // (e.g. `panic_with_error!(& env, ...)`) because they are separate tokens.
    // Fix this by collapsing `& env` back to `&env`.
    let source = source.replace("& env,", "&env,").replace("& env)", "&env)");
    // Strip contractevent topics parameter — Soroban SDK derives event name from struct name,
    // so `#[contractevent(topics = ["transfer"])]` is redundant; emit `#[contractevent]`.
    let source = strip_contractevent_topics(&source);
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

/// Strip `(topics = [...])` from `#[contractevent(...)]` attributes.
/// The Soroban SDK derives the event name from the struct name, so the
/// explicit topics parameter from soroban-spec-rust is redundant.
fn strip_contractevent_topics(source: &str) -> String {
    let pattern = "contractevent(topics = [";
    let mut result = source.to_string();
    while let Some(start) = result.find(pattern) {
        let search_from = start + pattern.len();
        if let Some(close_rel) = result[search_from..].find("])") {
            let end = search_from + close_rel + 2; // skip past `])`
            result = format!("{}contractevent{}", &result[..start], &result[end..]);
        } else {
            break;
        }
    }
    result
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
    use super::{assemble_generic_module, format_source};
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
}
