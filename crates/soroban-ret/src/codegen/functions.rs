use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::soroban_ir::{MatchArm, MatchPattern, SorobanExpr, SorobanStmt, StorageType};

/// Build a `proc_macro2::Ident` from a possibly-untrusted name without panicking.
///
/// Lifter-recovered names occasionally come from data-section bytes, frame-slot
/// derivation, or symbol decoding. These paths can yield strings that are not
/// valid Rust identifiers (empty, leading digit, embedded punctuation), and
/// `format_ident!` panics inside `proc_macro2` on such input. This helper
/// sanitises the input: any non-`[A-Za-z0-9_]` character becomes `_`, a leading
/// digit gains a `_` prefix, and an empty string falls back to `_unknown`.
fn safe_ident(name: &str) -> proc_macro2::Ident {
    let mut sanitised: String = name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if sanitised.is_empty() {
        sanitised.push_str("_unknown");
    } else if sanitised.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        sanitised.insert(0, '_');
    }
    format_ident!("{}", sanitised)
}

// Operator precedence levels (Rust standard, higher = tighter binding).
const PREC_OR: u8 = 1;
const PREC_AND: u8 = 2;
const PREC_CMP: u8 = 3;
const PREC_ADD: u8 = 4;
const PREC_MUL: u8 = 5;
const PREC_NOT: u8 = 6;

/// Check if an expression is a zero literal (any integer type).
fn is_zero_literal_expr(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::U64Literal(0)
            | SorobanExpr::I64Literal(0)
            | SorobanExpr::U32Literal(0)
            | SorobanExpr::I32Literal(0)
    )
}

/// Return the precedence of a binary/unary operator expression, or `None` for atoms.
fn expr_precedence(expr: &SorobanExpr) -> Option<u8> {
    match expr {
        SorobanExpr::Or(..) => Some(PREC_OR),
        SorobanExpr::And(..) => Some(PREC_AND),
        SorobanExpr::Eq(..)
        | SorobanExpr::Ne(..)
        | SorobanExpr::Lt(..)
        | SorobanExpr::Le(..)
        | SorobanExpr::Gt(..)
        | SorobanExpr::Ge(..) => Some(PREC_CMP),
        SorobanExpr::Add(..) | SorobanExpr::Sub(..) => Some(PREC_ADD),
        SorobanExpr::Mul(..) | SorobanExpr::Div(..) | SorobanExpr::Rem(..) => Some(PREC_MUL),
        SorobanExpr::Not(..) => Some(PREC_NOT),
        _ => None,
    }
}

/// Generate the type parameter for invoke_contract/try_invoke_contract.
/// Uses the inferred return type if available, otherwise falls back to `soroban_sdk::Val`.
fn invoke_type_param(return_type: &Option<String>) -> TokenStream {
    if let Some(ty) = return_type {
        let ty_ident: TokenStream = ty.parse().unwrap_or_else(|_| quote! { soroban_sdk::Val });
        ty_ident
    } else {
        quote! { soroban_sdk::Val }
    }
}

/// Rust comparisons are non-associative (`a == b == c` is a compile error).
fn is_comparison(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::Eq(..)
            | SorobanExpr::Ne(..)
            | SorobanExpr::Lt(..)
            | SorobanExpr::Le(..)
            | SorobanExpr::Gt(..)
            | SorobanExpr::Ge(..)
    )
}

/// Whether a binary expression needs parentheses given the parent context.
fn needs_parens(own_prec: u8, parent_prec: u8, is_right: bool, is_cmp: bool) -> bool {
    if own_prec < parent_prec {
        true
    } else if own_prec == parent_prec {
        is_right || is_cmp
    } else {
        false
    }
}

/// Generate a binary/unary expression with precedence-aware parenthesization.
///
/// `parent_prec` is the precedence of the enclosing operator (0 = top-level/tail).
/// `is_right` is true when this is the right operand of a left-associative operator.
/// Non-operator expressions delegate to `generate_expr_base`.
fn generate_expr_prec(expr: &SorobanExpr, parent_prec: u8, is_right: bool) -> TokenStream {
    let Some(own_prec) = expr_precedence(expr) else {
        return generate_expr_base(expr);
    };

    // Not is unary prefix — handle separately (no wrapping logic for Not itself)
    if let SorobanExpr::Not(a) = expr {
        let inner = generate_expr_prec(a, PREC_NOT, false);
        return quote! { !#inner };
    }

    let wrap = needs_parens(own_prec, parent_prec, is_right, is_comparison(expr));

    let (a, b) = match expr {
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
        | SorobanExpr::Or(a, b) => (a, b),
        _ => unreachable!(),
    };

    let left = generate_expr_prec(a, own_prec, false);
    let right = generate_expr_prec(b, own_prec, true);

    let inner = match expr {
        SorobanExpr::Add(..) => quote! { #left + #right },
        SorobanExpr::Sub(..) => {
            // Emit `0 - x` as `-x` for cleaner negation
            if is_zero_literal_expr(a) {
                quote! { -#right }
            } else {
                quote! { #left - #right }
            }
        }
        SorobanExpr::Mul(..) => quote! { #left * #right },
        SorobanExpr::Div(..) => quote! { #left / #right },
        SorobanExpr::Rem(..) => quote! { #left % #right },
        SorobanExpr::Eq(..) => quote! { #left == #right },
        SorobanExpr::Ne(..) => quote! { #left != #right },
        SorobanExpr::Lt(..) => quote! { #left < #right },
        SorobanExpr::Le(..) => quote! { #left <= #right },
        SorobanExpr::Gt(..) => quote! { #left > #right },
        SorobanExpr::Ge(..) => quote! { #left >= #right },
        SorobanExpr::And(..) => quote! { #left && #right },
        SorobanExpr::Or(..) => quote! { #left || #right },
        _ => unreachable!(),
    };

    if wrap {
        quote! { (#inner) }
    } else {
        inner
    }
}

/// Generate a token stream for a Soroban expression.
///
/// Operators get outer parentheses (safe for any context: function args, `&expr`, etc.).
/// Inner sub-expressions use precedence-aware parenthesization to avoid redundant nesting.
pub fn generate_expr(expr: &SorobanExpr) -> TokenStream {
    generate_expr_prec(expr, u8::MAX, false)
}

/// Generate a token stream for non-operator Soroban expressions.
///
/// Operator variants delegate back to `generate_expr` (which wraps via `generate_expr_prec`).
fn generate_expr_base(expr: &SorobanExpr) -> TokenStream {
    match expr {
        // Literals
        SorobanExpr::U32Literal(v) => {
            let lit = proc_macro2::Literal::u32_unsuffixed(*v);
            quote! { #lit }
        }
        SorobanExpr::I32Literal(v) => {
            let lit = proc_macro2::Literal::i32_unsuffixed(*v);
            quote! { #lit }
        }
        SorobanExpr::U64Literal(v) => {
            let lit = proc_macro2::Literal::u64_unsuffixed(*v);
            quote! { #lit }
        }
        SorobanExpr::I64Literal(v) => {
            let lit = proc_macro2::Literal::i64_unsuffixed(*v);
            quote! { #lit }
        }
        SorobanExpr::U128Literal(v) => {
            let lit = proc_macro2::Literal::u128_unsuffixed(*v);
            quote! { #lit }
        }
        SorobanExpr::I128Literal(v) => {
            let lit = proc_macro2::Literal::i128_unsuffixed(*v);
            quote! { #lit }
        }
        SorobanExpr::BoolLiteral(v) => quote! { #v },
        SorobanExpr::SymbolLiteral(s) => {
            if s.len() <= 9 {
                let sym = proc_macro2::Literal::string(s);
                quote! { symbol_short!(#sym) }
            } else {
                let sym = proc_macro2::Literal::string(s);
                quote! { Symbol::new(&env, #sym) }
            }
        }
        SorobanExpr::StringLiteral(s) => {
            let lit = proc_macro2::Literal::string(s);
            quote! { String::from_str(&env, #lit) }
        }
        SorobanExpr::Void => quote! { () },
        SorobanExpr::None => quote! { None },

        // Variables
        SorobanExpr::Param(name) => {
            let ident = safe_ident(name);
            quote! { #ident }
        }
        SorobanExpr::Local(idx) => {
            let ident = format_ident!("var_{}", idx);
            quote! { #ident }
        }
        SorobanExpr::NamedLocal(name) => {
            let ident = safe_ident(name);
            quote! { #ident }
        }
        SorobanExpr::Env => quote! { env },

        // Operators — handled by generate_expr_prec via generate_expr
        SorobanExpr::Add(..)
        | SorobanExpr::Sub(..)
        | SorobanExpr::Mul(..)
        | SorobanExpr::Div(..)
        | SorobanExpr::Rem(..)
        | SorobanExpr::Eq(..)
        | SorobanExpr::Ne(..)
        | SorobanExpr::Lt(..)
        | SorobanExpr::Le(..)
        | SorobanExpr::Gt(..)
        | SorobanExpr::Ge(..)
        | SorobanExpr::And(..)
        | SorobanExpr::Or(..)
        | SorobanExpr::Not(..) => generate_expr(expr),

        // Storage
        SorobanExpr::StorageGet {
            storage_type,
            key,
            unwrap,
        } => {
            let key = generate_expr(key);
            let storage = storage_method(*storage_type);
            if *unwrap {
                quote! { env.storage().#storage().get(&#key).unwrap() }
            } else {
                quote! { env.storage().#storage().get(&#key) }
            }
        }
        SorobanExpr::StorageSet {
            storage_type,
            key,
            value,
        } => {
            let key = generate_expr(key);
            let value = generate_expr(value);
            let storage = storage_method(*storage_type);
            quote! { env.storage().#storage().set(&#key, &#value) }
        }
        SorobanExpr::StorageHas { storage_type, key } => {
            let key = generate_expr(key);
            let storage = storage_method(*storage_type);
            quote! { env.storage().#storage().has(&#key) }
        }
        SorobanExpr::StorageRemove { storage_type, key } => {
            let key = generate_expr(key);
            let storage = storage_method(*storage_type);
            quote! { env.storage().#storage().remove(&#key) }
        }
        SorobanExpr::StorageExtendTtl {
            storage_type,
            key,
            threshold,
            extend_to,
        } => {
            let key = generate_expr(key);
            let threshold = generate_expr(threshold);
            let extend_to = generate_expr(extend_to);
            let storage = storage_method(*storage_type);
            quote! { env.storage().#storage().extend_ttl(&#key, #threshold, #extend_to) }
        }
        SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold,
            extend_to,
        } => {
            let threshold = generate_expr(threshold);
            let extend_to = generate_expr(extend_to);
            quote! { env.storage().instance().extend_ttl(#threshold, #extend_to) }
        }

        // Auth
        SorobanExpr::RequireAuth(addr) => {
            let addr = generate_expr(addr);
            quote! { #addr.require_auth() }
        }
        SorobanExpr::RequireAuthForArgs { address, args } => {
            let addr = generate_expr(address);
            let args = generate_expr(args);
            quote! { #addr.require_auth_for_args(#args.into_val(&env)) }
        }
        SorobanExpr::AuthorizeAsCurrContract(args) => {
            let args = generate_expr(args);
            quote! { env.authorize_as_current_contract(#args) }
        }

        // Events
        SorobanExpr::PublishEvent {
            event_name,
            topics,
            data,
        } => {
            if event_name.is_some() {
                // High-level event: data is a complete StructConstruct with all fields
                let data_expr = generate_expr(data);
                quote! { #data_expr.publish(&env) }
            } else {
                let data = generate_expr(data);
                // Flatten: if topics is a single TupleConstruct, use its inner fields
                let topic_list: Vec<&SorobanExpr> = if topics.len() == 1 {
                    if let SorobanExpr::TupleConstruct(inner) = &topics[0] {
                        inner.iter().collect()
                    } else {
                        topics.iter().collect()
                    }
                } else {
                    topics.iter().collect()
                };
                let topic_exprs: Vec<_> = topic_list.iter().map(|t| generate_expr(t)).collect();
                quote! { env.events().publish((#(#topic_exprs),*), #data) }
            }
        }

        // Cross-contract calls
        SorobanExpr::InvokeContract {
            address,
            function,
            args,
            return_type,
        } => {
            let addr = generate_expr(address);
            let func = generate_expr(function);
            let arg_exprs: Vec<_> = args
                .iter()
                .map(|a| {
                    let e = generate_expr(a);
                    quote! { #e.into_val(&env) }
                })
                .collect();
            let type_param = invoke_type_param(return_type);
            quote! { env.invoke_contract::<#type_param>(&#addr, &#func, vec![&env, #(#arg_exprs),*]) }
        }
        SorobanExpr::TryInvokeContract {
            address,
            function,
            args,
            return_type,
        } => {
            let addr = generate_expr(address);
            let func = generate_expr(function);
            let arg_exprs: Vec<_> = args
                .iter()
                .map(|a| {
                    let e = generate_expr(a);
                    quote! { #e.into_val(&env) }
                })
                .collect();
            let type_param = invoke_type_param(return_type);
            quote! { env.try_invoke_contract::<#type_param>(&#addr, &#func, vec![&env, #(#arg_exprs),*]) }
        }

        // Type construction
        SorobanExpr::StructConstruct { type_name, fields } => {
            let ty = safe_ident(type_name);
            let field_assigns: Vec<_> = fields
                .iter()
                .map(|(name, expr)| {
                    let field_name = safe_ident(name);
                    // Use field init shorthand when the value is a Param/NamedLocal
                    // with the same name as the field (e.g., `amount` instead of `amount: amount`)
                    if is_ident_expr(expr, name) {
                        quote! { #field_name }
                    } else {
                        let value = generate_expr(expr);
                        quote! { #field_name: #value }
                    }
                })
                .collect();
            quote! { #ty { #(#field_assigns),* } }
        }
        SorobanExpr::EnumConstruct {
            type_name,
            variant,
            fields,
        } => {
            let ty = safe_ident(type_name);
            let var = safe_ident(variant);
            if fields.is_empty() {
                quote! { #ty::#var }
            } else {
                let field_exprs: Vec<_> = fields.iter().map(generate_expr).collect();
                quote! { #ty::#var(#(#field_exprs),*) }
            }
        }
        SorobanExpr::TupleConstruct(fields) => {
            if fields.len() == 1 {
                generate_expr(&fields[0])
            } else {
                let field_exprs: Vec<_> = fields.iter().map(generate_expr).collect();
                quote! { (#(#field_exprs),*) }
            }
        }
        SorobanExpr::VecConstruct(elements) => {
            let elem_exprs: Vec<_> = elements.iter().map(generate_expr).collect();
            quote! { vec![&env, #(#elem_exprs),*] }
        }
        SorobanExpr::MapConstruct(entries) => {
            let entry_exprs: Vec<_> = entries
                .iter()
                .map(|(k, v)| {
                    let key = generate_expr(k);
                    let val = generate_expr(v);
                    quote! { (#key, #val) }
                })
                .collect();
            quote! { map![&env, #(#entry_exprs),*] }
        }

        // Collection constructors: Vec::new(&env), Map::new(&env)
        SorobanExpr::CollectionNew(ty_name) => {
            let ty_ident = safe_ident(ty_name);
            quote! { #ty_ident::new(&env) }
        }

        // Field access
        SorobanExpr::FieldAccess { object, field } => {
            let obj = generate_expr(object);
            if let Ok(idx) = field.parse::<usize>() {
                let index = syn::Index::from(idx);
                quote! { #obj.#index }
            } else {
                let field_ident = safe_ident(field);
                quote! { #obj.#field_ident }
            }
        }
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } => {
            let obj = generate_expr(object);
            let method_ident = safe_ident(method);
            // BLS12-381 methods take references for most args
            if is_bls_method_chain(object) && is_bls_ref_method(method) {
                let arg_exprs: Vec<_> = args
                    .iter()
                    .enumerate()
                    .map(|(i, a)| {
                        let e = generate_expr(a);
                        // fr_pow: second arg (exp) is u64, not a reference
                        if method == "fr_pow" && i == 1 {
                            e
                        } else {
                            quote! { &#e }
                        }
                    })
                    .collect();
                quote! { #obj.#method_ident(#(#arg_exprs),*) }
            } else {
                let arg_exprs: Vec<_> = args.iter().map(generate_expr).collect();
                quote! { #obj.#method_ident(#(#arg_exprs),*) }
            }
        }

        // Error handling
        SorobanExpr::ContractError {
            error_code,
            error_type,
            variant_name,
        } => {
            if let (Some(ename), Some(vname)) = (error_type, variant_name) {
                let ename_ident = safe_ident(ename);
                let vname_ident = safe_ident(vname);
                quote! { #ename_ident::#vname_ident }
            } else if let Some(ty) = error_type {
                let ty_ident = safe_ident(ty);
                let code = proc_macro2::Literal::u32_unsuffixed(*error_code);
                quote! { #ty_ident::from(#code) }
            } else {
                let code = proc_macro2::Literal::u32_unsuffixed(*error_code);
                quote! { soroban_sdk::Error::from_contract_error(#code) }
            }
        }
        SorobanExpr::ErrorFromCode(expr) => {
            let e = generate_expr(expr);
            quote! { soroban_sdk::Error::from_contract_error(#e) }
        }
        SorobanExpr::PanicWithError(err) => {
            let e = generate_expr(err);
            quote! { panic_with_error!(&env, #e) }
        }
        SorobanExpr::Panic => {
            quote! { panic!() }
        }

        // Crypto
        SorobanExpr::CryptoSha256(data) => {
            let data = generate_expr(data);
            quote! { env.crypto().sha256(&#data) }
        }
        SorobanExpr::CryptoKeccak256(data) => {
            let data = generate_expr(data);
            quote! { env.crypto().keccak256(&#data) }
        }
        SorobanExpr::CryptoEd25519Verify {
            public_key,
            message,
            signature,
        } => {
            let pk = generate_expr(public_key);
            let msg = generate_expr(message);
            let sig = generate_expr(signature);
            quote! { env.crypto().ed25519_verify(&#pk, &#msg, &#sig) }
        }
        SorobanExpr::CryptoSecp256k1Recover {
            msg_digest,
            signature,
            recovery_id,
        } => {
            let md = generate_expr(msg_digest);
            let sig = generate_expr(signature);
            let rid = generate_expr(recovery_id);
            quote! { env.crypto().secp256k1_recover(&#md, &#sig, #rid) }
        }

        // Ledger info
        SorobanExpr::LedgerSequence => quote! { env.ledger().sequence() },
        SorobanExpr::LedgerTimestamp => quote! { env.ledger().timestamp() },
        SorobanExpr::LedgerNetworkId => quote! { env.ledger().network_id() },
        SorobanExpr::CurrentContractAddress => quote! { env.current_contract_address() },
        SorobanExpr::MaxLiveUntilLedger => quote! { env.ledger().max_live_until_ledger() },

        // PRNG
        SorobanExpr::PrngReseed(seed) => {
            let seed = generate_expr(seed);
            quote! { env.prng().reseed(&#seed) }
        }
        SorobanExpr::PrngBytesNew(len) => {
            let len = generate_expr(len);
            quote! { env.prng().gen_len(#len) }
        }
        SorobanExpr::PrngU64InRange { low, high } => {
            let low = generate_expr(low);
            let high = generate_expr(high);
            quote! { env.prng().gen_range(#low..=#high) }
        }
        SorobanExpr::PrngVecShuffle(vec) => {
            let vec = generate_expr(vec);
            quote! { env.prng().shuffle(#vec) }
        }

        // Address operations
        SorobanExpr::StrkeyToAddress(strkey) => {
            let sk = generate_expr(strkey);
            quote! { Address::from_string(&#sk) }
        }
        SorobanExpr::AddressToStrkey(addr) => {
            let a = generate_expr(addr);
            quote! { #a.to_string() }
        }

        // Logging
        SorobanExpr::Log(args) => {
            let arg_exprs: Vec<_> = args.iter().map(generate_expr).collect();
            quote! { log!(&env, #(#arg_exprs),*) }
        }

        // Fallback
        SorobanExpr::RawHostCall {
            module,
            function,
            args,
        } => {
            // Validate that module and function are valid Rust identifiers before
            // using format_ident! (raw WASM import names like "0" would panic).
            let is_valid_ident = |s: &str| {
                !s.is_empty()
                    && s.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
                    && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            };
            if is_valid_ident(&module.to_lowercase()) && is_valid_ident(function) {
                let arg_exprs: Vec<_> = args.iter().map(generate_expr).collect();
                let mod_ident = format_ident!("{}", module.to_lowercase());
                let fn_ident = format_ident!("{}", function);
                if arg_exprs.is_empty() {
                    quote! { env.#mod_ident().#fn_ident() }
                } else {
                    quote! { env.#mod_ident().#fn_ident(#(#arg_exprs),*) }
                }
            } else {
                let msg = format!("host call: {}.{}", module, function);
                quote! { todo!(#msg) }
            }
        }

        SorobanExpr::UnknownVal => {
            quote! { todo!("unknown value") }
        }

        SorobanExpr::ValConvert {
            value,
            target_type: _,
        } => {
            let val = generate_expr(value);
            quote! { #val }
        }

        SorobanExpr::CastAs { value, target_type } => {
            let val = generate_expr(value);
            // `target_type` originates from spec/IR strings and is not guaranteed
            // to parse as a Rust type. Fall back to an identifier so codegen never
            // panics on an unexpected type name.
            match syn::parse_str::<syn::Type>(target_type) {
                Ok(ty) => quote! { #val as #ty },
                Err(_) => {
                    let ty_ident = safe_ident(target_type);
                    quote! { #val as #ty_ident }
                }
            }
        }
    }
}

/// Generate a Soroban expression used as an `if` condition (no outer parentheses).
fn generate_cond_expr(expr: &SorobanExpr) -> TokenStream {
    generate_expr_prec(expr, 0, false)
}

/// Generate a Soroban expression in tail position (no outer parentheses on operators).
fn generate_tail_expr(expr: &SorobanExpr) -> TokenStream {
    generate_expr_prec(expr, 0, false)
}

/// Generate a token stream for a Soroban statement
pub fn generate_stmt(stmt: &SorobanStmt) -> TokenStream {
    match stmt {
        SorobanStmt::Expr(expr) => {
            let e = generate_expr(expr);
            quote! { #e; }
        }
        SorobanStmt::Let {
            name,
            mutable,
            value,
        } => {
            let ident = safe_ident(name);
            let value = generate_expr(value);
            if *mutable {
                quote! { let mut #ident = #value; }
            } else {
                quote! { let #ident = #value; }
            }
        }
        SorobanStmt::Assign { target, value } => {
            let ident = safe_ident(target);
            let value = generate_expr(value);
            quote! { #ident = #value; }
        }
        SorobanStmt::Return(Some(expr)) => {
            let e = generate_expr(expr);
            quote! { return #e; }
        }
        SorobanStmt::Return(None) => {
            quote! { return; }
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            let cond = generate_cond_expr(condition);
            let then_stmts = generate_stmt_list_with(then_body, generate_stmt);
            if else_body.is_empty() {
                quote! { if #cond { #(#then_stmts)* } }
            } else {
                let else_stmts = generate_stmt_list_with(else_body, generate_stmt);
                quote! { if #cond { #(#then_stmts)* } else { #(#else_stmts)* } }
            }
        }
        SorobanStmt::Match { scrutinee, arms } => {
            // When all patterns are unit enum variants (no bindings) or wildcard,
            // emit as if/else if chain for more natural code.
            let all_unit = arms.iter().all(|arm| match &arm.pattern {
                MatchPattern::EnumVariant { bindings, .. } => bindings.is_empty(),
                MatchPattern::Wildcard => true,
                MatchPattern::Literal(_) => false,
            });
            if all_unit && !arms.is_empty() {
                generate_if_else_chain(scrutinee, arms)
            } else {
                let scrut = generate_expr(scrutinee);
                let arm_tokens: Vec<_> = arms
                    .iter()
                    .map(|arm| {
                        let pat = generate_pattern(&arm.pattern);
                        let body_stmts = generate_stmt_list_with(&arm.body, generate_stmt);
                        quote! { #pat => { #(#body_stmts)* } }
                    })
                    .collect();
                quote! { match #scrut { #(#arm_tokens)* } }
            }
        }
        SorobanStmt::Loop { body } => {
            if let Some(while_loop) = try_generate_while(body, generate_stmt) {
                while_loop
            } else {
                let body_stmts = generate_stmt_list_with(body, generate_stmt);
                quote! { loop { #(#body_stmts)* } }
            }
        }
        SorobanStmt::Block(stmts) => {
            let body_stmts = generate_stmt_list_with(stmts, generate_stmt);
            quote! { { #(#body_stmts)* } }
        }
        SorobanStmt::Comment(text) => {
            let comment = format!("// {}", text);
            comment.parse().unwrap_or_default()
        }
        SorobanStmt::Break => {
            quote! { break; }
        }
        SorobanStmt::Continue => {
            quote! { continue; }
        }
    }
}

/// Like `generate_stmt` but generates the last `Expr(e)` or `Return(e)` without a
/// trailing semicolon / `return` keyword, producing a Rust tail expression. Recurses
/// into If/Match/Block so that all branches have their final expression treated as a
/// tail. Does NOT recurse into Loop — `return` inside a loop must stay explicit.
pub fn generate_stmt_tail(stmt: &SorobanStmt) -> TokenStream {
    match stmt {
        SorobanStmt::Expr(expr) => {
            let e = generate_tail_expr(expr);
            // No semicolon — this is a tail expression
            quote! { #e }
        }
        // Tail return: strip the `return` keyword, emit bare expression
        SorobanStmt::Return(Some(expr)) => {
            let e = generate_tail_expr(expr);
            quote! { #e }
        }
        SorobanStmt::Return(None) => {
            quote! {}
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            let cond = generate_cond_expr(condition);
            let then_stmts = generate_stmts_with_tail(then_body);
            if else_body.is_empty() {
                quote! { if #cond { #(#then_stmts)* } }
            } else {
                let else_stmts = generate_stmts_with_tail(else_body);
                quote! { if #cond { #(#then_stmts)* } else { #(#else_stmts)* } }
            }
        }
        SorobanStmt::Match { scrutinee, arms } => {
            let all_unit = arms.iter().all(|arm| match &arm.pattern {
                MatchPattern::EnumVariant { bindings, .. } => bindings.is_empty(),
                MatchPattern::Wildcard => true,
                MatchPattern::Literal(_) => false,
            });
            if all_unit && !arms.is_empty() {
                generate_if_else_chain_tail(scrutinee, arms)
            } else {
                let scrut = generate_expr(scrutinee);
                let arm_tokens: Vec<_> = arms
                    .iter()
                    .map(|arm| {
                        let pat = generate_pattern(&arm.pattern);
                        let body_stmts = generate_stmts_with_tail(&arm.body);
                        quote! { #pat => { #(#body_stmts)* } }
                    })
                    .collect();
                quote! { match #scrut { #(#arm_tokens)* } }
            }
        }
        // Do NOT use tail form inside loops — `return` inside a loop body must stay
        // explicit because it exits the function, not just the loop iteration.
        SorobanStmt::Loop { body } => {
            if let Some(while_loop) = try_generate_while(body, generate_stmt) {
                while_loop
            } else {
                let body_stmts = generate_stmt_list_with(body, generate_stmt);
                quote! { loop { #(#body_stmts)* } }
            }
        }
        SorobanStmt::Block(stmts) => {
            let body_stmts = generate_stmts_with_tail(stmts);
            quote! { { #(#body_stmts)* } }
        }
        // All other statements: delegate to normal generator
        other => generate_stmt(other),
    }
}

/// Generate a statement list where the last statement uses tail-expression form.
pub fn generate_stmts_with_tail(stmts: &[SorobanStmt]) -> Vec<TokenStream> {
    if stmts.is_empty() {
        return vec![];
    }
    let last_idx = stmts.len() - 1;
    let mut result = generate_stmt_list_with(&stmts[..last_idx], generate_stmt);
    result.push(generate_stmt_tail(&stmts[last_idx]));
    result
}

fn is_error_like_expr(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::ContractError { .. } | SorobanExpr::ErrorFromCode(_)
    )
}

/// Stricter check: true only for ContractError with a known contracterror enum type.
/// Used for PanicWithError → Err conversion: raw error codes (ErrorFromCode) and
/// unresolved errors should stay as panic_with_error!, not be converted to Err.
fn is_typed_contract_error(expr: &SorobanExpr) -> bool {
    matches!(
        expr,
        SorobanExpr::ContractError {
            error_type: Some(_),
            variant_name: Some(_),
            ..
        }
    )
}

/// Like `generate_stmt` but wraps `Return` values in `Ok()`/`Err()` for `Result`-returning
/// functions. Also recurses into `if`/`match`/`loop`/`block` bodies so that early returns
/// nested inside control flow are also wrapped correctly.
pub fn generate_stmt_result_wrapped(stmt: &SorobanStmt) -> TokenStream {
    match stmt {
        SorobanStmt::Return(Some(expr)) => {
            let e = generate_expr(expr);
            if is_error_like_expr(expr) {
                quote! { return Err(#e); }
            } else if matches!(
                expr,
                SorobanExpr::Void | SorobanExpr::UnknownVal | SorobanExpr::Panic
            ) {
                quote! { return #e; }
            } else {
                quote! { return Ok(#e); }
            }
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            let cond = generate_cond_expr(condition);
            let then_stmts = generate_stmt_list_with(then_body, generate_stmt_result_wrapped);
            if else_body.is_empty() {
                quote! { if #cond { #(#then_stmts)* } }
            } else {
                let else_stmts = generate_stmt_list_with(else_body, generate_stmt_result_wrapped);
                quote! { if #cond { #(#then_stmts)* } else { #(#else_stmts)* } }
            }
        }
        SorobanStmt::Match { scrutinee, arms } => {
            let all_unit = arms.iter().all(|arm| match &arm.pattern {
                MatchPattern::EnumVariant { bindings, .. } => bindings.is_empty(),
                MatchPattern::Wildcard => true,
                MatchPattern::Literal(_) => false,
            });
            if all_unit && !arms.is_empty() {
                generate_if_else_chain_with(scrutinee, arms, |stmts| {
                    generate_stmt_list_with(stmts, generate_stmt_result_wrapped)
                })
            } else {
                let scrut = generate_expr(scrutinee);
                let arm_tokens: Vec<_> = arms
                    .iter()
                    .map(|arm| {
                        let pat = generate_pattern(&arm.pattern);
                        let body_stmts =
                            generate_stmt_list_with(&arm.body, generate_stmt_result_wrapped);
                        quote! { #pat => { #(#body_stmts)* } }
                    })
                    .collect();
                quote! { match #scrut { #(#arm_tokens)* } }
            }
        }
        SorobanStmt::Loop { body } => {
            if let Some(while_loop) = try_generate_while(body, generate_stmt_result_wrapped) {
                while_loop
            } else {
                let body_stmts = generate_stmt_list_with(body, generate_stmt_result_wrapped);
                quote! { loop { #(#body_stmts)* } }
            }
        }
        SorobanStmt::Block(stmts) => {
            let body_stmts = generate_stmt_list_with(stmts, generate_stmt_result_wrapped);
            quote! { { #(#body_stmts)* } }
        }
        // PanicWithError(ContractError) in a Result-returning function is the
        // compiled form of `Err(variant)` — the SDK macro expands Err returns to
        // fail_with_error host calls. Convert back to idiomatic Err returns.
        SorobanStmt::Expr(SorobanExpr::PanicWithError(err)) if is_typed_contract_error(err) => {
            let e = generate_expr(err);
            quote! { return Err(#e); }
        }
        // All other statement types (Expr, Let, Assign, Comment, Break, Continue)
        // do not contain return statements, so delegate to the plain generator.
        other => generate_stmt(other),
    }
}

/// Like `generate_stmt_result_wrapped` but for the last statement in a function body:
/// strips the `return` keyword while still wrapping in `Ok()`/`Err()`.
/// Does NOT recurse into Loop — `return` inside a loop body must stay explicit.
fn generate_stmt_tail_result_wrapped(stmt: &SorobanStmt) -> TokenStream {
    match stmt {
        SorobanStmt::Return(Some(expr)) => {
            // Ok()/Err() wrapping: the expression is nested inside Ok()/Err(),
            // so use generate_expr (parens needed for correct precedence).
            // Only bare tail expressions (Void/UnknownVal/Panic) use generate_tail_expr.
            let e = generate_expr(expr);
            if is_error_like_expr(expr) {
                quote! { Err(#e) }
            } else if matches!(
                expr,
                SorobanExpr::Void | SorobanExpr::UnknownVal | SorobanExpr::Panic
            ) {
                let e = generate_tail_expr(expr);
                quote! { #e }
            } else {
                quote! { Ok(#e) }
            }
        }
        SorobanStmt::Return(None) => {
            quote! {}
        }
        // PanicWithError(ContractError) → Err(variant) in tail position
        SorobanStmt::Expr(SorobanExpr::PanicWithError(err)) if is_typed_contract_error(err) => {
            let e = generate_expr(err);
            quote! { Err(#e) }
        }
        SorobanStmt::Expr(expr) => {
            let e = generate_tail_expr(expr);
            // No semicolon — tail expression
            quote! { #e }
        }
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => {
            let cond = generate_cond_expr(condition);
            let then_stmts = generate_stmts_with_tail_result_wrapped(then_body);
            if else_body.is_empty() {
                quote! { if #cond { #(#then_stmts)* } }
            } else {
                let else_stmts = generate_stmts_with_tail_result_wrapped(else_body);
                quote! { if #cond { #(#then_stmts)* } else { #(#else_stmts)* } }
            }
        }
        SorobanStmt::Match { scrutinee, arms } => {
            let all_unit = arms.iter().all(|arm| match &arm.pattern {
                MatchPattern::EnumVariant { bindings, .. } => bindings.is_empty(),
                MatchPattern::Wildcard => true,
                MatchPattern::Literal(_) => false,
            });
            if all_unit && !arms.is_empty() {
                generate_if_else_chain_with(
                    scrutinee,
                    arms,
                    generate_stmts_with_tail_result_wrapped,
                )
            } else {
                let scrut = generate_expr(scrutinee);
                let arm_tokens: Vec<_> = arms
                    .iter()
                    .map(|arm| {
                        let pat = generate_pattern(&arm.pattern);
                        let body_stmts = generate_stmts_with_tail_result_wrapped(&arm.body);
                        quote! { #pat => { #(#body_stmts)* } }
                    })
                    .collect();
                quote! { match #scrut { #(#arm_tokens)* } }
            }
        }
        SorobanStmt::Loop { body } => {
            if let Some(while_loop) = try_generate_while(body, generate_stmt_result_wrapped) {
                while_loop
            } else {
                let body_stmts = generate_stmt_list_with(body, generate_stmt_result_wrapped);
                quote! { loop { #(#body_stmts)* } }
            }
        }
        SorobanStmt::Block(stmts) => {
            let body_stmts = generate_stmts_with_tail_result_wrapped(stmts);
            quote! { { #(#body_stmts)* } }
        }
        other => generate_stmt_result_wrapped(other),
    }
}

/// Generate a statement list for Result-returning functions where the last statement
/// uses tail-expression form (no `return` keyword, but still wraps in `Ok()`/`Err()`).
pub fn generate_stmts_with_tail_result_wrapped(stmts: &[SorobanStmt]) -> Vec<TokenStream> {
    if stmts.is_empty() {
        return vec![];
    }
    let last_idx = stmts.len() - 1;
    let mut result = generate_stmt_list_with(&stmts[..last_idx], generate_stmt_result_wrapped);
    result.push(generate_stmt_tail_result_wrapped(&stmts[last_idx]));
    result
}

// ---------------------------------------------------------------------------
// Let-Match Expression Optimization
// ---------------------------------------------------------------------------

/// Check if a variable name is assigned anywhere in a statement list (recursively).
fn has_assign_to_in(stmts: &[SorobanStmt], name: &str) -> bool {
    stmts.iter().any(|s| stmt_has_assign_to(s, name))
}

fn stmt_has_assign_to(stmt: &SorobanStmt, name: &str) -> bool {
    match stmt {
        SorobanStmt::Assign { target, .. } => target == name,
        SorobanStmt::If {
            then_body,
            else_body,
            ..
        } => has_assign_to_in(then_body, name) || has_assign_to_in(else_body, name),
        SorobanStmt::Match { arms, .. } => arms.iter().any(|arm| has_assign_to_in(&arm.body, name)),
        SorobanStmt::Loop { body } => has_assign_to_in(body, name),
        SorobanStmt::Block(stmts) => has_assign_to_in(stmts, name),
        _ => false,
    }
}

/// Try to combine `let mut x = init; match { arms all assign x }` into
/// `let x = match scrutinee { pattern => value, empty_pattern => init }`.
///
/// `remaining` is the statements after the match — used to verify the variable
/// is not re-assigned later (so it's safe to make it immutable).
fn try_combine_let_match(
    let_stmt: &SorobanStmt,
    match_stmt: &SorobanStmt,
    remaining: &[SorobanStmt],
) -> Option<TokenStream> {
    let (name, init) = match let_stmt {
        SorobanStmt::Let {
            name,
            mutable: true,
            value,
        } => (name, value),
        _ => return None,
    };
    let (scrutinee, arms) = match match_stmt {
        SorobanStmt::Match { scrutinee, arms } if !arms.is_empty() => (scrutinee, arms),
        _ => return None,
    };
    // Every arm must be either empty (keeps init) or a single Assign to `name`.
    let mut arm_values: Vec<(&MatchPattern, &SorobanExpr)> = Vec::new();
    for arm in arms {
        if arm.body.is_empty() {
            arm_values.push((&arm.pattern, init));
        } else if arm.body.len() == 1 {
            if let SorobanStmt::Assign { target, value } = &arm.body[0] {
                if target == name {
                    arm_values.push((&arm.pattern, value));
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
    // Verify the variable is not re-assigned after the match.
    if has_assign_to_in(remaining, name) {
        return None;
    }

    let ident = safe_ident(name);
    let scrut = generate_expr(scrutinee);
    let arm_tokens: Vec<_> = arm_values
        .iter()
        .map(|(pattern, value)| {
            let pat = generate_pattern(pattern);
            let val = generate_expr(value);
            quote! { #pat => #val, }
        })
        .collect();
    Some(quote! { let #ident = match #scrut { #(#arm_tokens)* }; })
}

/// Try to combine `let mut x = init; if cond { x = val; }` into
/// `let x = if cond { val } else { init };`.
///
/// Also handles the case where both branches assign: `if cond { x = a; } else { x = b; }`.
fn try_combine_let_if(
    let_stmt: &SorobanStmt,
    if_stmt: &SorobanStmt,
    remaining: &[SorobanStmt],
) -> Option<TokenStream> {
    let (name, init) = match let_stmt {
        SorobanStmt::Let {
            name,
            mutable: true,
            value,
        } => (name, value),
        _ => return None,
    };
    let (condition, then_body, else_body) = match if_stmt {
        SorobanStmt::If {
            condition,
            then_body,
            else_body,
        } => (condition, then_body, else_body),
        _ => return None,
    };
    // then_body must be a single Assign to `name`.
    let then_value = match then_body.as_slice() {
        [SorobanStmt::Assign { target, value }] if target == name => value,
        _ => return None,
    };
    // else_body: empty → use init, single Assign → use assigned value.
    let else_value = if else_body.is_empty() {
        init
    } else {
        match else_body.as_slice() {
            [SorobanStmt::Assign { target, value }] if target == name => value,
            _ => return None,
        }
    };
    // Don't combine if the variable is re-assigned later.
    if has_assign_to_in(remaining, name) {
        return None;
    }

    let ident = safe_ident(name);
    let cond = generate_cond_expr(condition);
    let then_val = generate_expr(then_value);
    let else_val = generate_expr(else_value);
    Some(quote! { let #ident = if #cond { #then_val } else { #else_val }; })
}

/// Generate a list of statements, combining `let mut + match/if` patterns into
/// expression forms when possible.
fn generate_stmt_list_with(
    stmts: &[SorobanStmt],
    gen_stmt: fn(&SorobanStmt) -> TokenStream,
) -> Vec<TokenStream> {
    let mut result = Vec::new();
    let mut i = 0;
    while i < stmts.len() {
        if i + 1 < stmts.len() {
            let remaining = if i + 2 < stmts.len() {
                &stmts[i + 2..]
            } else {
                &[]
            };
            if let Some(combined) = try_combine_let_match(&stmts[i], &stmts[i + 1], remaining) {
                result.push(combined);
                i += 2;
                continue;
            }
            if let Some(combined) = try_combine_let_if(&stmts[i], &stmts[i + 1], remaining) {
                result.push(combined);
                i += 2;
                continue;
            }
        }
        result.push(gen_stmt(&stmts[i]));
        i += 1;
    }
    result
}

/// Detect `loop { if cond { break; } body... }` → emit as `while !cond { body }`.
/// Returns None if the pattern doesn't match.
fn try_generate_while(
    body: &[SorobanStmt],
    gen_stmt: fn(&SorobanStmt) -> TokenStream,
) -> Option<TokenStream> {
    if body.len() < 2 {
        return None;
    }
    // First statement must be `if cond { break; }` with no else
    if let SorobanStmt::If {
        condition,
        then_body,
        else_body,
    } = &body[0]
        && else_body.is_empty()
        && then_body.len() == 1
        && matches!(then_body[0], SorobanStmt::Break)
    {
        // Negate the condition cleanly: flip comparisons directly instead of wrapping in !()
        let neg_cond = negate_condition(condition);
        let rest: Vec<_> = body[1..].iter().map(gen_stmt).collect();
        return Some(quote! { while #neg_cond { #(#rest)* } });
    }
    None
}

/// Negate a condition for while-loop emission, producing clean output.
/// Flips comparisons directly (Eq→Ne, Lt→Ge, etc.) instead of wrapping in !().
fn negate_condition(cond: &SorobanExpr) -> TokenStream {
    match cond {
        SorobanExpr::Eq(a, b) => {
            let la = generate_expr(a);
            let lb = generate_expr(b);
            quote! { #la != #lb }
        }
        SorobanExpr::Ne(a, b) => {
            let la = generate_expr(a);
            let lb = generate_expr(b);
            quote! { #la == #lb }
        }
        SorobanExpr::Lt(a, b) => {
            let la = generate_expr(a);
            let lb = generate_expr(b);
            quote! { #la >= #lb }
        }
        SorobanExpr::Ge(a, b) => {
            let la = generate_expr(a);
            let lb = generate_expr(b);
            quote! { #la < #lb }
        }
        SorobanExpr::Gt(a, b) => {
            let la = generate_expr(a);
            let lb = generate_expr(b);
            quote! { #la <= #lb }
        }
        SorobanExpr::Le(a, b) => {
            let la = generate_expr(a);
            let lb = generate_expr(b);
            quote! { #la > #lb }
        }
        SorobanExpr::Not(inner) => generate_expr(inner),
        SorobanExpr::BoolLiteral(v) => {
            let neg = !v;
            quote! { #neg }
        }
        _ => {
            let c = generate_expr(cond);
            quote! { !#c }
        }
    }
}

/// Emit a match on unit enum variants as an if/else if chain.
/// Uses `generate_stmt` for each arm body.
fn generate_if_else_chain(scrutinee: &SorobanExpr, arms: &[MatchArm]) -> TokenStream {
    generate_if_else_chain_with(scrutinee, arms, |stmts| {
        generate_stmt_list_with(stmts, generate_stmt)
    })
}

/// Emit a match on unit enum variants as an if/else if chain, using tail-expression
/// form for the last statement in each arm body.
fn generate_if_else_chain_tail(scrutinee: &SorobanExpr, arms: &[MatchArm]) -> TokenStream {
    generate_if_else_chain_with(scrutinee, arms, generate_stmts_with_tail)
}

/// Emit a match on unit enum variants as an if/else if chain with a custom
/// body generator for arm bodies.
fn generate_if_else_chain_with(
    scrutinee: &SorobanExpr,
    arms: &[MatchArm],
    body_gen: impl Fn(&[SorobanStmt]) -> Vec<TokenStream>,
) -> TokenStream {
    let scrut = generate_expr(scrutinee);
    let mut result = TokenStream::new();

    for (i, arm) in arms.iter().enumerate() {
        let body_stmts = body_gen(&arm.body);

        if matches!(arm.pattern, MatchPattern::Wildcard) {
            // Wildcard becomes the final `else` block (skip empty else)
            if i == 0 {
                // Only a wildcard arm — just emit the body directly
                result.extend(quote! { { #(#body_stmts)* } });
            } else if !arm.body.is_empty() {
                result.extend(quote! { else { #(#body_stmts)* } });
            }
        } else {
            let pat = generate_pattern(&arm.pattern);
            if i == 0 {
                result.extend(quote! { if #scrut == #pat { #(#body_stmts)* } });
            } else {
                result.extend(quote! { else if #scrut == #pat { #(#body_stmts)* } });
            }
        }
    }

    result
}

fn generate_pattern(pattern: &MatchPattern) -> TokenStream {
    match pattern {
        MatchPattern::Literal(expr) => generate_expr(expr),
        MatchPattern::EnumVariant {
            type_name,
            variant,
            bindings,
        } => {
            let ty = safe_ident(type_name);
            let var = safe_ident(variant);
            if bindings.is_empty() {
                quote! { #ty::#var }
            } else {
                let binding_idents: Vec<_> = bindings.iter().map(|b| safe_ident(b)).collect();
                quote! { #ty::#var(#(#binding_idents),*) }
            }
        }
        MatchPattern::Wildcard => quote! { _ },
    }
}

/// Check if a MethodCall's object chain includes `.bls12_381()`.
fn is_bls_method_chain(object: &SorobanExpr) -> bool {
    match object {
        SorobanExpr::MethodCall { method, object, .. } => {
            if method == "bls12_381" {
                return true;
            }
            is_bls_method_chain(object)
        }
        _ => false,
    }
}

/// BLS12-381 methods that take their arguments by reference.
/// Excluded: g1_msm, g2_msm, pairing_check (take Vec by value).
fn is_bls_ref_method(method: &str) -> bool {
    matches!(
        method,
        "g1_add"
            | "g1_mul"
            | "g2_add"
            | "g2_mul"
            | "g1_is_in_subgroup"
            | "g2_is_in_subgroup"
            | "map_fp_to_g1"
            | "map_fp2_to_g2"
            | "hash_to_g1"
            | "hash_to_g2"
            | "fr_add"
            | "fr_sub"
            | "fr_mul"
            | "fr_pow"
            | "fr_inv"
    )
}

fn storage_method(storage_type: StorageType) -> TokenStream {
    match storage_type {
        StorageType::Persistent => quote! { persistent },
        StorageType::Temporary => quote! { temporary },
        StorageType::Instance => quote! { instance },
    }
}

/// Check if an expression is a simple identifier reference (Param or NamedLocal)
/// whose name matches the given field name — enabling field init shorthand.
/// Unwraps ValConvert wrappers which are transparent in codegen.
fn is_ident_expr(expr: &SorobanExpr, name: &str) -> bool {
    match expr {
        SorobanExpr::Param(n) | SorobanExpr::NamedLocal(n) => n == name,
        SorobanExpr::ValConvert { value, .. } => is_ident_expr(value, name),
        _ => false,
    }
}

#[cfg(test)]
mod safe_ident_tests {
    use super::safe_ident;

    #[test]
    fn rejects_leading_digit() {
        assert_eq!(safe_ident("0").to_string(), "_0");
        assert_eq!(safe_ident("123abc").to_string(), "_123abc");
    }

    #[test]
    fn replaces_punctuation() {
        assert_eq!(safe_ident("foo-bar").to_string(), "foo_bar");
        assert_eq!(safe_ident("foo.bar").to_string(), "foo_bar");
        assert_eq!(safe_ident("foo bar").to_string(), "foo_bar");
    }

    #[test]
    fn empty_name_falls_back() {
        assert_eq!(safe_ident("").to_string(), "_unknown");
    }

    #[test]
    fn passes_through_valid_idents() {
        assert_eq!(safe_ident("foo").to_string(), "foo");
        assert_eq!(safe_ident("_x").to_string(), "_x");
        assert_eq!(safe_ident("snake_case_42").to_string(), "snake_case_42");
    }
}
