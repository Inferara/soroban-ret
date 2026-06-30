use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};

use crate::ir::soroban_ir::{MatchArm, MatchPattern, SorobanExpr, SorobanStmt, StorageType};

/// Names that cannot be escaped via `r#` (Rust 2024).
/// `proc_macro2::Ident::new_raw` panics on these.
const RAW_FORBIDDEN: &[&str] = &["self", "Self", "crate", "super"];

/// Build a `proc_macro2::Ident` from a possibly-untrusted name without panicking
/// and without colliding with Rust keywords.
///
/// Lifter-recovered names come from data-section bytes, frame-slot derivation,
/// or symbol decoding. These paths can yield strings that are not valid Rust
/// identifiers (empty, leading digit, embedded punctuation), and `format_ident!`
/// panics inside `proc_macro2` on such input. Furthermore, a spec param literally
/// named `type`, `match`, `move`, `fn`, etc. would emit unparseable Rust.
///
/// Sanitisation: any non-`[A-Za-z0-9_]` character becomes `_`, a leading digit
/// gains a `_` prefix, empty falls back to `_unknown`. After sanitisation, if
/// the result is a Rust keyword, it is raw-escaped (`r#name`); for the four
/// keywords (`self`, `Self`, `crate`, `super`) that cannot be raw-escaped, a
/// trailing underscore is appended.
pub(crate) fn safe_ident(name: &str) -> proc_macro2::Ident {
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

    // `_` is the wildcard token. `syn::parse_str::<Ident>("_")` rejects it
    // and `Ident::new_raw("_")` panics, but `format_ident!("_")` works and
    // is exactly the right output in pattern-binding contexts (the only
    // callers that pass a bare `_`).
    if sanitised == "_" {
        return format_ident!("_");
    }

    // `syn::parse_str::<syn::Ident>` rejects all Rust keywords; if parsing
    // fails the sanitised string is a keyword and must be escaped.
    if syn::parse_str::<syn::Ident>(&sanitised).is_ok() {
        format_ident!("{}", sanitised)
    } else if RAW_FORBIDDEN.contains(&sanitised.as_str()) {
        sanitised.push('_');
        format_ident!("{}", sanitised)
    } else {
        proc_macro2::Ident::new_raw(&sanitised, Span::call_site())
    }
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
        SorobanExpr::BytesLiteral(bytes) => {
            let byte_lits = bytes
                .iter()
                .map(|b| proc_macro2::Literal::u8_unsuffixed(*b));
            quote! { Bytes::from_slice(&env, &[#(#byte_lits),*]) }
        }
        SorobanExpr::Void => quote! { () },
        SorobanExpr::None => quote! { None },
        SorobanExpr::Some(inner) => {
            let inner = generate_expr(inner);
            quote! { Some(#inner) }
        }

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
            on_missing,
        } => {
            let key = generate_expr(key);
            let storage = storage_method(*storage_type);
            if let Some(err) = on_missing {
                let err = generate_expr(err);
                quote! { env.storage().#storage().get(&#key).ok_or(#err) }
            } else if *unwrap {
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
                    // A lost arg renders as a bare `todo!()` (`!`), which already
                    // coerces to the element type; `.into_val()` on `!` does not
                    // type-check (`Val: TryFromVal<Env, !>`, E0277). Keep it bare.
                    if matches!(a, SorobanExpr::UnknownVal) {
                        e
                    } else {
                        quote! { #e.into_val(&env) }
                    }
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
                    // A lost arg renders as a bare `todo!()` (`!`), which already
                    // coerces to the element type; `.into_val()` on `!` does not
                    // type-check (`Val: TryFromVal<Env, !>`, E0277). Keep it bare.
                    if matches!(a, SorobanExpr::UnknownVal) {
                        e
                    } else {
                        quote! { #e.into_val(&env) }
                    }
                })
                .collect();
            let type_param = invoke_type_param(return_type);
            // v26 `try_invoke_contract::<T, E>` returns
            // `Result<Result<T, T::Error>, Result<E, InvokeError>>`; flatten it to the
            // function's declared `Result<T, E>`. `E` is left to inference so it matches
            // whatever error type the signature declares (contract enum or `soroban_sdk::Error`).
            quote! {
                env.try_invoke_contract::<#type_param, _>(&#addr, &#func, vec![&env, #(#arg_exprs),*])
                    .map(|r| r.unwrap())
                    .map_err(|e| e.unwrap())
            }
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
            if is_heterogeneous_val_vec(elements) {
                // Mixed element types can't form a homogeneous `Vec<T>` (E0308) —
                // the lost-`DataKey` shape `vec![&env, 14, addr]`, a raw
                // discriminant beside a variable payload. Convert each element to
                // `Val` so the literal types as `Vec<Val>`. Faithful: `into_val`
                // yields the identical per-element ScVal, and `Vec<Val>` is the
                // only type a heterogeneous key vec can have.
                let elem_exprs: Vec<_> = elements.iter().map(generate_val_elem).collect();
                quote! { vec![&env, #(#elem_exprs),*] }
            } else {
                let elem_exprs: Vec<_> = elements.iter().map(generate_expr).collect();
                quote! { vec![&env, #(#elem_exprs),*] }
            }
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

        SorobanExpr::CyclicSlot { frame_id, offset } => {
            let msg = format!("cyclic frame slot ({frame_id}, {offset})");
            quote! { todo!(#msg) }
        }

        // A bare sret discriminant that wasn't consumed by a match: render the
        // underlying call so the value is at least surfaced.
        SorobanExpr::SretResult(inner) => generate_expr(inner),

        SorobanExpr::ValTag(inner) => {
            let val = generate_expr(inner);
            quote! { #val.get_tag() }
        }
        SorobanExpr::ValTagName(name) => {
            let ident = safe_ident(name);
            quote! { Tag::#ident }
        }

        SorobanExpr::ValConvert {
            value,
            target_type: _,
        } => {
            let val = generate_expr(value);
            quote! { #val }
        }

        // A storage get typed for i128/u128 arithmetic: emit a `get::<_, T>`
        // turbofish rather than an `as` cast — the get's generic value type cannot
        // be `as`-cast and Rust will not infer it from the surrounding arithmetic.
        SorobanExpr::CastAs { value, target_type }
            if matches!(value.as_ref(), SorobanExpr::StorageGet { .. })
                && syn::parse_str::<syn::Type>(target_type).is_ok() =>
        {
            if let SorobanExpr::StorageGet {
                storage_type,
                key,
                unwrap,
                on_missing,
            } = value.as_ref()
            {
                let key = generate_expr(key);
                let storage = storage_method(*storage_type);
                let ty: syn::Type = syn::parse_str(target_type).expect("checked by guard");
                if let Some(err) = on_missing {
                    // Recovered fallible get: the turbofish pins the value type the
                    // `.ok_or(..)` return can't infer on its own (Address/UDT).
                    let err = generate_expr(err);
                    quote! { env.storage().#storage().get::<_, #ty>(&#key).ok_or(#err) }
                } else if *unwrap {
                    quote! { env.storage().#storage().get::<_, #ty>(&#key).unwrap() }
                } else {
                    quote! { env.storage().#storage().get::<_, #ty>(&#key) }
                }
            } else {
                unreachable!("guarded by matches! on StorageGet")
            }
        }

        // An un-inferable empty collection (`Map::new`/`Vec::new`) whose value
        // type the lifter lost: emit a `Map::<_, T>::new` / `Vec::<T>::new`
        // turbofish pinning only the value param (the key stays inferred). A
        // plain `as` cast (the fallback arm below) cannot annotate a generic
        // constructor, so this must precede it.
        SorobanExpr::CastAs { value, target_type }
            if matches!(value.as_ref(), SorobanExpr::CollectionNew(_))
                && syn::parse_str::<syn::Type>(target_type).is_ok() =>
        {
            let SorobanExpr::CollectionNew(coll) = value.as_ref() else {
                unreachable!("guarded by matches! on CollectionNew")
            };
            let coll_ident = safe_ident(coll);
            let ty: syn::Type = syn::parse_str(target_type).expect("checked by guard");
            if coll == "Map" {
                quote! { #coll_ident::<_, #ty>::new(&env) }
            } else {
                quote! { #coll_ident::<#ty>::new(&env) }
            }
        }

        SorobanExpr::CastAs { value, target_type } => {
            let val = generate_expr(value);
            // `target_type` originates from spec/IR strings and is not guaranteed
            // to parse as a Rust type. Earlier code silently coerced it to a
            // sanitised ident (e.g. `Vec_u32_`), producing valid syntax with
            // the wrong type. Instead, emit a `compile_error!` so the failure
            // surfaces at compile time of the decompiled code rather than as a
            // silent miscast.
            match syn::parse_str::<syn::Type>(target_type) {
                Ok(ty) => quote! { #val as #ty },
                Err(_) => {
                    let msg = format!("decompiler: unsupported cast target `{target_type}`");
                    let msg_lit = proc_macro2::Literal::string(&msg);
                    quote! { { compile_error!(#msg_lit); #val } }
                }
            }
        }

        SorobanExpr::Try(inner) => {
            let inner = generate_expr(inner);
            quote! { #inner? }
        }

        SorobanExpr::VecTryIterFold { vec, init } => {
            let v = generate_expr(vec);
            // Emit the fold init as a suffixed `0i64` to match the SDK source
            // (the closure's accumulator type is i64). Only this call site is
            // suffixed; global `I64Literal` rendering stays unsuffixed.
            let i = match init.as_ref() {
                SorobanExpr::I64Literal(n) => {
                    let lit = proc_macro2::Literal::i64_suffixed(*n);
                    quote! { #lit }
                }
                other => generate_expr(other),
            };
            quote! { #v.try_iter().fold(#i, |sum, i| sum + i.unwrap()) }
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

/// True when a `vec![&env, ...]` literal mixes element types and so cannot type
/// as a homogeneous `Vec<T>` — the lost-`DataKey` shape `vec![&env, 14, addr]`
/// (a raw discriminant beside a variable payload). Conservative: fires only when
/// there are ≥2 *distinct* known scalar types, or a known numeric literal sits
/// beside an element whose type can't be told (`Address`/`Param`/method call/…).
/// A uniform vec, or one whose element types are indistinguishable, is untouched.
///
/// `!`-typed elements (`todo!()`/`panic!()`) are skipped: they coerce to any
/// element type and so never force a heterogeneous vec — forcing `.into_val()`
/// on one would instead *break* a vec that previously compiled via coercion.
pub(crate) fn is_heterogeneous_val_vec(elems: &[SorobanExpr]) -> bool {
    if elems.len() < 2 {
        return false;
    }
    let mut known: std::collections::BTreeSet<&'static str> = std::collections::BTreeSet::new();
    let mut has_unknown = false;
    let mut has_numeric = false;
    for e in elems {
        if is_never_typed(e) {
            continue;
        }
        match scalar_class(e) {
            Some(c) => {
                known.insert(c);
                if is_numeric_class(c) {
                    has_numeric = true;
                }
            }
            None => has_unknown = true,
        }
    }
    known.len() >= 2 || (has_numeric && has_unknown)
}

/// A `!`-typed expression (`todo!()`, `panic!()`, `panic_with_error!()`) — it
/// coerces to any type, so it never participates in a type mismatch.
fn is_never_typed(e: &SorobanExpr) -> bool {
    matches!(
        e,
        SorobanExpr::UnknownVal | SorobanExpr::Panic | SorobanExpr::PanicWithError(_)
    )
}

/// The concrete Rust scalar type of an element, when statically known. `None`
/// for elements whose type can't be determined from the IR node alone (variables,
/// addresses, method results) — those are treated as the unknown class.
fn scalar_class(e: &SorobanExpr) -> Option<&'static str> {
    use SorobanExpr as E;
    match e {
        E::U32Literal(_) => Some("u32"),
        E::I32Literal(_) => Some("i32"),
        E::U64Literal(_) => Some("u64"),
        E::I64Literal(_) => Some("i64"),
        E::U128Literal(_) => Some("u128"),
        E::I128Literal(_) => Some("i128"),
        E::BoolLiteral(_) => Some("bool"),
        E::SymbolLiteral(_) => Some("symbol"),
        E::StringLiteral(_) => Some("string"),
        _ => None,
    }
}

fn is_numeric_class(c: &str) -> bool {
    matches!(c, "u32" | "i32" | "u64" | "i64" | "u128" | "i128")
}

/// Render one heterogeneous-vec element as a `Val` via fully-qualified
/// `IntoVal::<_, Val>::into_val(&elem, &env)`. The explicit `Val` target is
/// required: a bare `elem.into_val(&env)` leaves the conversion target ambiguous
/// inside a `vec!` whose element type isn't otherwise pinned (E0283). Integer
/// literals carry a width suffix so the source type is unambiguous too.
fn generate_val_elem(e: &SorobanExpr) -> TokenStream {
    let inner = generate_suffixed_scalar(e);
    quote! { IntoVal::<_, Val>::into_val(&(#inner), &env) }
}

fn generate_suffixed_scalar(e: &SorobanExpr) -> TokenStream {
    use SorobanExpr as E;
    match e {
        E::U32Literal(v) => {
            let l = proc_macro2::Literal::u32_suffixed(*v);
            quote! { #l }
        }
        E::I32Literal(v) => {
            let l = proc_macro2::Literal::i32_suffixed(*v);
            quote! { #l }
        }
        E::U64Literal(v) => {
            let l = proc_macro2::Literal::u64_suffixed(*v);
            quote! { #l }
        }
        E::I64Literal(v) => {
            let l = proc_macro2::Literal::i64_suffixed(*v);
            quote! { #l }
        }
        E::U128Literal(v) => {
            let l = proc_macro2::Literal::u128_suffixed(*v);
            quote! { #l }
        }
        E::I128Literal(v) => {
            let l = proc_macro2::Literal::i128_suffixed(*v);
            quote! { #l }
        }
        _ => generate_expr(e),
    }
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
        SorobanStmt::For {
            var,
            start,
            end,
            step,
            body,
        } => {
            let ident = safe_ident(var);
            let start_e = generate_expr(start);
            let end_e = generate_expr(end);
            let body_stmts = generate_stmt_list_with(body, generate_stmt);
            if *step == 1 {
                quote! { for #ident in #start_e..#end_e { #(#body_stmts)* } }
            } else {
                let step_lit = proc_macro2::Literal::usize_unsuffixed(*step as usize);
                quote! { for #ident in (#start_e..#end_e).step_by(#step_lit) { #(#body_stmts)* } }
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
                SorobanExpr::Void
                    | SorobanExpr::UnknownVal
                    | SorobanExpr::CyclicSlot { .. }
                    | SorobanExpr::Panic
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
                SorobanExpr::Void
                    | SorobanExpr::UnknownVal
                    | SorobanExpr::CyclicSlot { .. }
                    | SorobanExpr::Panic
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
        SorobanStmt::For { body, .. } => has_assign_to_in(body, name),
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

    #[test]
    fn raw_escapes_strict_and_reserved_keywords() {
        // Strict keywords get the r# prefix and parse cleanly. The exact set
        // depends on the syn version's keyword recognition; we test only
        // keywords syn already treats as non-Ident, so the test tracks the
        // implementation precisely.
        for kw in [
            "fn", "if", "else", "let", "match", "move", "type", "loop", "while", "for", "return",
            "break", "continue", "mut", "ref", "use", "where", "impl", "trait", "pub", "mod",
            "struct", "enum", "true", "false", "as", "in", "const", "static", "async", "await",
            "dyn", "unsafe", "extern", "yield", "abstract", "become", "box", "do", "final",
            "macro", "override", "priv", "typeof", "unsized", "virtual", "try",
        ] {
            if syn::parse_str::<syn::Ident>(kw).is_ok() {
                // This syn version does not classify `kw` as a keyword — skip.
                continue;
            }
            let id = safe_ident(kw);
            assert_eq!(
                id.to_string(),
                format!("r#{kw}"),
                "keyword {kw} did not round-trip to r#{kw}"
            );
            // Round-trips through syn — the produced ident is parseable.
            let parsed = syn::parse_str::<syn::Ident>(&id.to_string());
            assert!(parsed.is_ok(), "r#{kw} did not parse as syn::Ident");
        }
    }

    #[test]
    fn appends_underscore_to_forbidden_raw_keywords() {
        // self/Self/crate/super cannot be raw-escaped: panic in Ident::new_raw.
        // Fall back to underscore suffix.
        assert_eq!(safe_ident("self").to_string(), "self_");
        assert_eq!(safe_ident("Self").to_string(), "Self_");
        assert_eq!(safe_ident("crate").to_string(), "crate_");
        assert_eq!(safe_ident("super").to_string(), "super_");
    }

    #[test]
    fn underscore_passes_through_as_wildcard() {
        // `_` is the wildcard token and is the right output in match-arm
        // binding positions (the only place a bare `_` reaches safe_ident).
        assert_eq!(safe_ident("_").to_string(), "_");
    }
}

#[cfg(test)]
mod generate_expr_tests {
    use super::*;

    fn s(t: TokenStream) -> String {
        t.to_string()
    }
    fn collapse(s: &str) -> String {
        s.split_whitespace().collect::<Vec<_>>().join(" ")
    }
    fn boxed(e: SorobanExpr) -> Box<SorobanExpr> {
        Box::new(e)
    }

    // ----- Heterogeneous key vecs -> Vec<Val> -----

    #[test]
    fn heterogeneous_vec_detection() {
        use SorobanExpr as E;
        let addr = || E::Param("address".into());
        // numeric literal beside a variable payload (the lost-DataKey shape)
        assert!(is_heterogeneous_val_vec(&[E::I64Literal(14), addr()]));
        // two distinct known scalar types
        assert!(is_heterogeneous_val_vec(&[
            E::I32Literal(1),
            E::U64Literal(2)
        ]));
        // uniform: same int type / same symbol kind / single element
        assert!(!is_heterogeneous_val_vec(&[
            E::I32Literal(1),
            E::I32Literal(2)
        ]));
        assert!(!is_heterogeneous_val_vec(&[
            E::SymbolLiteral("a".into()),
            E::SymbolLiteral("b".into())
        ]));
        assert!(!is_heterogeneous_val_vec(&[E::I64Literal(14)]));
        // `!`-typed (todo!()/panic!()) elements coerce — they do not force a wrap
        assert!(!is_heterogeneous_val_vec(&[
            E::I64Literal(14),
            E::UnknownVal
        ]));
        assert!(!is_heterogeneous_val_vec(&[
            E::U32Literal(1),
            E::UnknownVal,
            E::UnknownVal
        ]));
        // …but a real concrete unknown beside a numeric still wraps, todo ignored
        assert!(is_heterogeneous_val_vec(&[
            E::I64Literal(14),
            E::UnknownVal,
            addr()
        ]));
    }

    #[test]
    fn heterogeneous_vec_renders_into_val() {
        use SorobanExpr as E;
        let v = E::VecConstruct(vec![E::I64Literal(14), E::Param("address".into())]);
        let out = collapse(&s(generate_expr(&v)));
        assert!(
            out.contains("IntoVal :: < _ , Val > :: into_val (& (14i64)"),
            "numeric element should be suffixed + Val-pinned: {out}"
        );
        assert!(
            out.contains("into_val (& (address) , & env)"),
            "variable element should be Val-pinned: {out}"
        );
    }

    #[test]
    fn homogeneous_vec_unchanged() {
        use SorobanExpr as E;
        let v = E::VecConstruct(vec![E::I32Literal(1), E::I32Literal(2)]);
        let out = collapse(&s(generate_expr(&v)));
        assert_eq!(out, "vec ! [& env , 1 , 2]", "got: {out}");
    }

    // ----- Literals & basic atoms -----

    #[test]
    fn literals_emit_unsuffixed() {
        assert_eq!(s(generate_expr(&SorobanExpr::U32Literal(7))), "7");
        assert_eq!(s(generate_expr(&SorobanExpr::I32Literal(-3))), "- 3");
        assert_eq!(s(generate_expr(&SorobanExpr::U64Literal(42))), "42");
        assert_eq!(s(generate_expr(&SorobanExpr::I64Literal(-1))), "- 1");
        assert_eq!(s(generate_expr(&SorobanExpr::U128Literal(1))), "1");
        assert_eq!(s(generate_expr(&SorobanExpr::I128Literal(-1))), "- 1");
        assert_eq!(s(generate_expr(&SorobanExpr::BoolLiteral(true))), "true");
        assert_eq!(s(generate_expr(&SorobanExpr::BoolLiteral(false))), "false");
        assert_eq!(s(generate_expr(&SorobanExpr::Void)), "()");
        assert_eq!(s(generate_expr(&SorobanExpr::None)), "None");
    }

    #[test]
    fn short_symbol_uses_symbol_short_macro() {
        let out = collapse(&s(generate_expr(&SorobanExpr::SymbolLiteral("foo".into()))));
        assert_eq!(out, "symbol_short ! (\"foo\")");
    }

    #[test]
    fn long_symbol_uses_symbol_new() {
        // 10+ chars uses Symbol::new(&env, ...)
        let out = collapse(&s(generate_expr(&SorobanExpr::SymbolLiteral(
            "very_long_symbol".into(),
        ))));
        assert!(out.contains("Symbol :: new (& env"), "got: {out}");
        assert!(out.contains("\"very_long_symbol\""), "got: {out}");
    }

    #[test]
    fn string_literal_emits_from_str() {
        let out = collapse(&s(generate_expr(&SorobanExpr::StringLiteral(
            "hello".into(),
        ))));
        assert_eq!(out, "String :: from_str (& env , \"hello\")");
    }

    #[test]
    fn variables_emit_safe_idents() {
        assert_eq!(s(generate_expr(&SorobanExpr::Param("a".into()))), "a");
        assert_eq!(s(generate_expr(&SorobanExpr::Local(3))), "var_3");
        assert_eq!(
            s(generate_expr(&SorobanExpr::NamedLocal("foo_bar".into()))),
            "foo_bar"
        );
        assert_eq!(s(generate_expr(&SorobanExpr::Env)), "env");
        // Untrusted name gets sanitised.
        assert_eq!(
            s(generate_expr(&SorobanExpr::Param("123-bad".into()))),
            "_123_bad"
        );
    }

    // ----- Arithmetic & precedence -----

    #[test]
    fn add_two_literals() {
        // Top-level operators always get outer parens for safety in any context.
        let e = SorobanExpr::Add(
            boxed(SorobanExpr::U32Literal(1)),
            boxed(SorobanExpr::U32Literal(2)),
        );
        assert_eq!(collapse(&s(generate_expr(&e))), "(1 + 2)");
    }

    #[test]
    fn precedence_mul_binds_tighter_than_add() {
        // `a + b * c` — inner mul does NOT get parens (higher precedence).
        let mul = SorobanExpr::Mul(
            boxed(SorobanExpr::Param("b".into())),
            boxed(SorobanExpr::Param("c".into())),
        );
        let add = SorobanExpr::Add(boxed(SorobanExpr::Param("a".into())), boxed(mul));
        assert_eq!(collapse(&s(generate_expr(&add))), "(a + b * c)");
    }

    #[test]
    fn precedence_add_inside_mul_gets_parens() {
        // (a + b) * c — inner lower-precedence add requires explicit parens.
        let add = SorobanExpr::Add(
            boxed(SorobanExpr::Param("a".into())),
            boxed(SorobanExpr::Param("b".into())),
        );
        let mul = SorobanExpr::Mul(boxed(add), boxed(SorobanExpr::Param("c".into())));
        let out = collapse(&s(generate_expr(&mul)));
        assert!(out.contains("(a + b) * c"), "got: {out}");
    }

    #[test]
    fn left_associative_add_no_inner_parens() {
        // (a + b) + c — left associative same precedence, inner no parens.
        let inner = SorobanExpr::Add(
            boxed(SorobanExpr::Param("a".into())),
            boxed(SorobanExpr::Param("b".into())),
        );
        let outer = SorobanExpr::Add(boxed(inner), boxed(SorobanExpr::Param("c".into())));
        // Outer wrap is unconditional; inner pair is on the left so no parens needed.
        assert_eq!(collapse(&s(generate_expr(&outer))), "(a + b + c)");
    }

    #[test]
    fn right_associative_sub_gets_parens() {
        // a - (b - c) — right side of same-precedence binop needs parens.
        let inner = SorobanExpr::Sub(
            boxed(SorobanExpr::Param("b".into())),
            boxed(SorobanExpr::Param("c".into())),
        );
        let outer = SorobanExpr::Sub(boxed(SorobanExpr::Param("a".into())), boxed(inner));
        let out = collapse(&s(generate_expr(&outer)));
        assert!(out.contains("a - (b - c)"), "got: {out}");
    }

    #[test]
    fn sub_div_rem_codegen() {
        for (op, sym) in [
            (
                SorobanExpr::Sub(
                    boxed(SorobanExpr::Param("a".into())),
                    boxed(SorobanExpr::Param("b".into())),
                ),
                "-",
            ),
            (
                SorobanExpr::Div(
                    boxed(SorobanExpr::Param("a".into())),
                    boxed(SorobanExpr::Param("b".into())),
                ),
                "/",
            ),
            (
                SorobanExpr::Rem(
                    boxed(SorobanExpr::Param("a".into())),
                    boxed(SorobanExpr::Param("b".into())),
                ),
                "%",
            ),
        ] {
            assert_eq!(collapse(&s(generate_expr(&op))), format!("(a {sym} b)"));
        }
    }

    #[test]
    fn comparison_operators() {
        for (op, sym) in [
            (
                SorobanExpr::Eq(
                    boxed(SorobanExpr::Param("a".into())),
                    boxed(SorobanExpr::Param("b".into())),
                ),
                "==",
            ),
            (
                SorobanExpr::Ne(
                    boxed(SorobanExpr::Param("a".into())),
                    boxed(SorobanExpr::Param("b".into())),
                ),
                "!=",
            ),
            (
                SorobanExpr::Lt(
                    boxed(SorobanExpr::Param("a".into())),
                    boxed(SorobanExpr::Param("b".into())),
                ),
                "<",
            ),
            (
                SorobanExpr::Le(
                    boxed(SorobanExpr::Param("a".into())),
                    boxed(SorobanExpr::Param("b".into())),
                ),
                "<=",
            ),
            (
                SorobanExpr::Gt(
                    boxed(SorobanExpr::Param("a".into())),
                    boxed(SorobanExpr::Param("b".into())),
                ),
                ">",
            ),
            (
                SorobanExpr::Ge(
                    boxed(SorobanExpr::Param("a".into())),
                    boxed(SorobanExpr::Param("b".into())),
                ),
                ">=",
            ),
        ] {
            assert_eq!(collapse(&s(generate_expr(&op))), format!("(a {sym} b)"));
        }
    }

    #[test]
    fn logical_and_or_not() {
        let a = SorobanExpr::Param("a".into());
        let b = SorobanExpr::Param("b".into());
        let and = SorobanExpr::And(boxed(a.clone()), boxed(b.clone()));
        let or = SorobanExpr::Or(boxed(a.clone()), boxed(b));
        let not = SorobanExpr::Not(boxed(a));
        assert_eq!(collapse(&s(generate_expr(&and))), "(a && b)");
        assert_eq!(collapse(&s(generate_expr(&or))), "(a || b)");
        // Unary `!` is highest precedence; codegen emits it without outer parens.
        assert_eq!(collapse(&s(generate_expr(&not))), "! a");
    }

    // ----- Storage operations -----

    #[test]
    fn storage_get_with_and_without_unwrap() {
        let key = SorobanExpr::SymbolLiteral("k".into());
        let g = SorobanExpr::StorageGet {
            storage_type: StorageType::Persistent,
            key: boxed(key.clone()),
            unwrap: true,
            on_missing: None,
        };
        let out = collapse(&s(generate_expr(&g)));
        assert!(out.contains(". persistent ()"), "got: {out}");
        assert!(out.contains(". get (&"), "got: {out}");
        assert!(out.ends_with(". unwrap ()"), "got: {out}");

        let g = SorobanExpr::StorageGet {
            storage_type: StorageType::Temporary,
            key: boxed(key),
            unwrap: false,
            on_missing: None,
        };
        let out = collapse(&s(generate_expr(&g)));
        assert!(out.contains(". temporary ()"), "got: {out}");
        assert!(!out.contains("unwrap"), "got: {out}");
    }

    #[test]
    fn storage_set_has_remove() {
        let k = SorobanExpr::SymbolLiteral("k".into());
        let v = SorobanExpr::U64Literal(7);
        let set = SorobanExpr::StorageSet {
            storage_type: StorageType::Instance,
            key: boxed(k.clone()),
            value: boxed(v),
        };
        let out = collapse(&s(generate_expr(&set)));
        assert!(out.contains(". instance ()"), "got: {out}");
        assert!(out.contains(". set (&"), "got: {out}");

        let has = SorobanExpr::StorageHas {
            storage_type: StorageType::Persistent,
            key: boxed(k.clone()),
        };
        assert!(collapse(&s(generate_expr(&has))).contains(". has (&"));

        let rm = SorobanExpr::StorageRemove {
            storage_type: StorageType::Persistent,
            key: boxed(k),
        };
        assert!(collapse(&s(generate_expr(&rm))).contains(". remove (&"));
    }

    #[test]
    fn storage_extend_ttl() {
        let e = SorobanExpr::StorageExtendTtl {
            storage_type: StorageType::Persistent,
            key: boxed(SorobanExpr::SymbolLiteral("k".into())),
            threshold: boxed(SorobanExpr::U32Literal(100)),
            extend_to: boxed(SorobanExpr::U32Literal(1000)),
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains(". extend_ttl (&"), "got: {out}");
        assert!(out.contains("100"));
        assert!(out.contains("1000"));
    }

    #[test]
    fn extend_instance_and_code_ttl() {
        let e = SorobanExpr::ExtendInstanceAndCodeTtl {
            threshold: boxed(SorobanExpr::U32Literal(50)),
            extend_to: boxed(SorobanExpr::U32Literal(500)),
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("env . storage () . instance () . extend_ttl"));
        assert!(out.contains("50") && out.contains("500"));
    }

    // ----- Auth -----

    #[test]
    fn auth_require_and_for_args() {
        let r = SorobanExpr::RequireAuth(boxed(SorobanExpr::Param("a".into())));
        assert_eq!(collapse(&s(generate_expr(&r))), "a . require_auth ()");

        let f = SorobanExpr::RequireAuthForArgs {
            address: boxed(SorobanExpr::Param("a".into())),
            args: boxed(SorobanExpr::TupleConstruct(vec![
                SorobanExpr::U32Literal(1),
                SorobanExpr::U32Literal(2),
            ])),
        };
        let out = collapse(&s(generate_expr(&f)));
        assert!(out.contains("require_auth_for_args"));
        assert!(out.contains("(1 , 2) . into_val (& env)"));
    }

    #[test]
    fn authorize_as_curr_contract() {
        let e = SorobanExpr::AuthorizeAsCurrContract(boxed(SorobanExpr::VecConstruct(vec![])));
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("env . authorize_as_current_contract"));
    }

    // ----- Events -----

    #[test]
    fn publish_event_high_level_uses_struct_publish() {
        let e = SorobanExpr::PublishEvent {
            event_name: Some("Transfer".into()),
            topics: vec![],
            data: boxed(SorobanExpr::StructConstruct {
                type_name: "Transfer".into(),
                fields: vec![("amount".into(), SorobanExpr::U64Literal(1))],
            }),
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("Transfer { amount : 1 } . publish (& env)"));
    }

    #[test]
    fn publish_event_low_level_uses_env_events_publish() {
        let e = SorobanExpr::PublishEvent {
            event_name: None,
            topics: vec![SorobanExpr::SymbolLiteral("t".into())],
            data: boxed(SorobanExpr::U64Literal(7)),
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("env . events () . publish"));
        assert!(out.contains("symbol_short ! (\"t\")"));
    }

    #[test]
    fn publish_event_flattens_tuple_topics() {
        // Single TupleConstruct topic gets unwrapped into the publish tuple.
        let e = SorobanExpr::PublishEvent {
            event_name: None,
            topics: vec![SorobanExpr::TupleConstruct(vec![
                SorobanExpr::SymbolLiteral("a".into()),
                SorobanExpr::SymbolLiteral("b".into()),
            ])],
            data: boxed(SorobanExpr::U64Literal(7)),
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("env . events () . publish"));
        assert!(out.contains("symbol_short ! (\"a\")"));
        assert!(out.contains("symbol_short ! (\"b\")"));
    }

    // ----- Cross-contract calls -----

    #[test]
    fn invoke_contract_with_typed_return() {
        let e = SorobanExpr::InvokeContract {
            address: boxed(SorobanExpr::Param("addr".into())),
            function: boxed(SorobanExpr::SymbolLiteral("add".into())),
            args: vec![SorobanExpr::Param("x".into())],
            return_type: Some("u64".into()),
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("env . invoke_contract :: < u64 >"));
        assert!(out.contains("symbol_short ! (\"add\")"));
        assert!(out.contains("x . into_val (& env)"));
    }

    #[test]
    fn invoke_contract_lost_arg_stays_bare_todo() {
        // A lost invoke arg (`UnknownVal`) renders as a bare `todo!()` (`!`), which
        // coerces to the element type; `.into_val()` on `!` is E0277, so it must NOT
        // be appended. A real arg still gets `.into_val(&env)`.
        let e = SorobanExpr::InvokeContract {
            address: boxed(SorobanExpr::Param("addr".into())),
            function: boxed(SorobanExpr::SymbolLiteral("f".into())),
            args: vec![SorobanExpr::UnknownVal, SorobanExpr::Param("x".into())],
            return_type: None,
        };
        let out = collapse(&s(generate_expr(&e)));
        assert_eq!(
            out.matches("into_val").count(),
            1,
            "only the real arg should get .into_val(): {out}"
        );
        assert!(
            out.contains("todo !"),
            "lost arg should stay a bare todo!(): {out}"
        );
    }

    #[test]
    fn invoke_contract_untyped_falls_back_to_val() {
        let e = SorobanExpr::InvokeContract {
            address: boxed(SorobanExpr::Param("addr".into())),
            function: boxed(SorobanExpr::SymbolLiteral("f".into())),
            args: vec![],
            return_type: None,
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("env . invoke_contract :: < soroban_sdk :: Val >"));
    }

    #[test]
    fn try_invoke_contract_emits_try_variant() {
        let e = SorobanExpr::TryInvokeContract {
            address: boxed(SorobanExpr::Param("addr".into())),
            function: boxed(SorobanExpr::SymbolLiteral("f".into())),
            args: vec![],
            return_type: Some("i32".into()),
        };
        let out = collapse(&s(generate_expr(&e)));
        // v26: two generic params (`E` inferred) + flatten of the nested Result.
        assert!(
            out.contains("env . try_invoke_contract :: < i32 , _ >"),
            "got: {out}"
        );
        assert!(
            out.contains(". map_err"),
            "expected nested-Result flatten: {out}"
        );
    }

    // ----- Type constructors -----

    #[test]
    fn struct_construct_uses_shorthand_when_field_eq_param() {
        let e = SorobanExpr::StructConstruct {
            type_name: "Transfer".into(),
            fields: vec![
                ("from".into(), SorobanExpr::Param("from".into())),
                ("amount".into(), SorobanExpr::U64Literal(1)),
            ],
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("Transfer { from , amount : 1 }"), "got: {out}");
    }

    #[test]
    fn enum_construct_unit_and_tuple_variants() {
        let unit = SorobanExpr::EnumConstruct {
            type_name: "Flag".into(),
            variant: "A".into(),
            fields: vec![],
        };
        assert_eq!(collapse(&s(generate_expr(&unit))), "Flag :: A");

        let tup = SorobanExpr::EnumConstruct {
            type_name: "DataKey".into(),
            variant: "Persistent".into(),
            fields: vec![SorobanExpr::U32Literal(7)],
        };
        assert_eq!(
            collapse(&s(generate_expr(&tup))),
            "DataKey :: Persistent (7)"
        );
    }

    #[test]
    fn tuple_construct_single_unwraps_paren() {
        // 1-element TupleConstruct should not emit `(x,)` — it unwraps.
        let e = SorobanExpr::TupleConstruct(vec![SorobanExpr::U32Literal(5)]);
        assert_eq!(collapse(&s(generate_expr(&e))), "5");

        let multi = SorobanExpr::TupleConstruct(vec![
            SorobanExpr::U32Literal(1),
            SorobanExpr::U32Literal(2),
        ]);
        assert_eq!(collapse(&s(generate_expr(&multi))), "(1 , 2)");
    }

    #[test]
    fn vec_and_map_construct() {
        let v =
            SorobanExpr::VecConstruct(vec![SorobanExpr::U32Literal(1), SorobanExpr::U32Literal(2)]);
        let out = collapse(&s(generate_expr(&v)));
        assert!(out.contains("vec ! [& env , 1 , 2]"));

        let m = SorobanExpr::MapConstruct(vec![(
            SorobanExpr::SymbolLiteral("k".into()),
            SorobanExpr::U32Literal(1),
        )]);
        let out = collapse(&s(generate_expr(&m)));
        assert!(out.contains("map ! [& env ,"));
    }

    #[test]
    fn collection_new() {
        let v = SorobanExpr::CollectionNew("Vec".into());
        assert_eq!(collapse(&s(generate_expr(&v))), "Vec :: new (& env)");
    }

    #[test]
    fn cast_collection_emits_value_turbofish() {
        // Map pins only the value param, leaving the key inferred.
        let m = SorobanExpr::CastAs {
            value: boxed(SorobanExpr::CollectionNew("Map".into())),
            target_type: "Val".into(),
        };
        let out = collapse(&s(generate_expr(&m)));
        assert!(out.contains("Map :: < _ , Val > :: new"), "got: {out}");
        // Vec has a single element param.
        let v = SorobanExpr::CastAs {
            value: boxed(SorobanExpr::CollectionNew("Vec".into())),
            target_type: "Val".into(),
        };
        let out = collapse(&s(generate_expr(&v)));
        assert!(out.contains("Vec :: < Val > :: new"), "got: {out}");
    }

    #[test]
    fn field_access_named_and_indexed() {
        let named = SorobanExpr::FieldAccess {
            object: boxed(SorobanExpr::Param("s".into())),
            field: "amount".into(),
        };
        assert_eq!(collapse(&s(generate_expr(&named))), "s . amount");

        // Numeric field becomes tuple index.
        let idx = SorobanExpr::FieldAccess {
            object: boxed(SorobanExpr::Param("t".into())),
            field: "0".into(),
        };
        assert_eq!(collapse(&s(generate_expr(&idx))), "t . 0");
    }

    #[test]
    fn method_call_simple() {
        let e = SorobanExpr::MethodCall {
            object: boxed(SorobanExpr::Param("a".into())),
            method: "to_string".into(),
            args: vec![],
        };
        assert_eq!(collapse(&s(generate_expr(&e))), "a . to_string ()");
    }

    // ----- Error handling -----

    #[test]
    fn contract_error_with_enum_variant() {
        let e = SorobanExpr::ContractError {
            error_code: 1,
            error_type: Some("Error".into()),
            variant_name: Some("AnError".into()),
        };
        assert_eq!(collapse(&s(generate_expr(&e))), "Error :: AnError");
    }

    #[test]
    fn contract_error_with_type_only_uses_from() {
        let e = SorobanExpr::ContractError {
            error_code: 9,
            error_type: Some("Error".into()),
            variant_name: None,
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("Error :: from (9)"), "got: {out}");
    }

    #[test]
    fn contract_error_raw_code() {
        let e = SorobanExpr::ContractError {
            error_code: 9,
            error_type: None,
            variant_name: None,
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(
            out.contains("soroban_sdk :: Error :: from_contract_error (9)"),
            "got: {out}"
        );
    }

    #[test]
    fn error_from_code_panic_with_error_and_panic() {
        let efc = SorobanExpr::ErrorFromCode(boxed(SorobanExpr::U32Literal(5)));
        let out = collapse(&s(generate_expr(&efc)));
        assert!(out.contains("Error :: from_contract_error (5)"));

        let pwe = SorobanExpr::PanicWithError(boxed(SorobanExpr::ContractError {
            error_code: 0,
            error_type: Some("Error".into()),
            variant_name: Some("Bad".into()),
        }));
        let out = collapse(&s(generate_expr(&pwe)));
        assert!(out.contains("panic_with_error ! (& env , Error :: Bad)"));

        assert_eq!(
            collapse(&s(generate_expr(&SorobanExpr::Panic))),
            "panic ! ()"
        );
    }

    // ----- Crypto -----

    #[test]
    fn crypto_sha256_keccak256() {
        let data = SorobanExpr::Param("d".into());
        let sha = SorobanExpr::CryptoSha256(boxed(data.clone()));
        let kec = SorobanExpr::CryptoKeccak256(boxed(data));
        assert!(collapse(&s(generate_expr(&sha))).contains("env . crypto () . sha256 (& d)"));
        assert!(collapse(&s(generate_expr(&kec))).contains("env . crypto () . keccak256 (& d)"));
    }

    #[test]
    fn crypto_ed25519_verify() {
        let e = SorobanExpr::CryptoEd25519Verify {
            public_key: boxed(SorobanExpr::Param("pk".into())),
            message: boxed(SorobanExpr::Param("m".into())),
            signature: boxed(SorobanExpr::Param("sig".into())),
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("env . crypto () . ed25519_verify (& pk , & m , & sig)"));
    }

    #[test]
    fn crypto_secp256k1_recover() {
        let e = SorobanExpr::CryptoSecp256k1Recover {
            msg_digest: boxed(SorobanExpr::Param("md".into())),
            signature: boxed(SorobanExpr::Param("sig".into())),
            recovery_id: boxed(SorobanExpr::U32Literal(0)),
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("env . crypto () . secp256k1_recover (& md , & sig , 0)"));
    }

    // ----- Ledger info -----

    #[test]
    fn ledger_atoms() {
        for (e, want) in [
            (SorobanExpr::LedgerSequence, "env . ledger () . sequence ()"),
            (
                SorobanExpr::LedgerTimestamp,
                "env . ledger () . timestamp ()",
            ),
            (
                SorobanExpr::LedgerNetworkId,
                "env . ledger () . network_id ()",
            ),
            (
                SorobanExpr::CurrentContractAddress,
                "env . current_contract_address ()",
            ),
            (
                SorobanExpr::MaxLiveUntilLedger,
                "env . ledger () . max_live_until_ledger ()",
            ),
        ] {
            assert_eq!(collapse(&s(generate_expr(&e))), want);
        }
    }

    // ----- PRNG -----

    #[test]
    fn prng_variants() {
        let r = SorobanExpr::PrngReseed(boxed(SorobanExpr::Param("seed".into())));
        assert!(collapse(&s(generate_expr(&r))).contains("env . prng () . reseed (& seed)"));

        let b = SorobanExpr::PrngBytesNew(boxed(SorobanExpr::U32Literal(32)));
        assert!(collapse(&s(generate_expr(&b))).contains("env . prng () . gen_len (32)"));

        let u = SorobanExpr::PrngU64InRange {
            low: boxed(SorobanExpr::U64Literal(1)),
            high: boxed(SorobanExpr::U64Literal(10)),
        };
        assert!(collapse(&s(generate_expr(&u))).contains("env . prng () . gen_range (1 ..= 10)"));

        let sh = SorobanExpr::PrngVecShuffle(boxed(SorobanExpr::Param("v".into())));
        assert!(collapse(&s(generate_expr(&sh))).contains("env . prng () . shuffle (v)"));
    }

    // ----- Address & log -----

    #[test]
    fn strkey_address_and_log() {
        let sk = SorobanExpr::StrkeyToAddress(boxed(SorobanExpr::Param("s".into())));
        assert!(collapse(&s(generate_expr(&sk))).contains("Address :: from_string (& s)"));

        let to = SorobanExpr::AddressToStrkey(boxed(SorobanExpr::Param("a".into())));
        assert_eq!(collapse(&s(generate_expr(&to))), "a . to_string ()");

        let l = SorobanExpr::Log(vec![
            SorobanExpr::StringLiteral("x".into()),
            SorobanExpr::Param("n".into()),
        ]);
        let out = collapse(&s(generate_expr(&l)));
        assert!(out.starts_with("log ! (& env ,"), "got: {out}");
    }

    // ----- Fallbacks -----

    #[test]
    fn raw_host_call_valid_idents_emits_method() {
        let e = SorobanExpr::RawHostCall {
            module: "Ctx".into(),
            function: "do_thing".into(),
            args: vec![SorobanExpr::U32Literal(7)],
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("env . ctx () . do_thing (7)"));
    }

    #[test]
    fn raw_host_call_invalid_falls_back_to_todo() {
        let e = SorobanExpr::RawHostCall {
            module: "0bad".into(),
            function: "f".into(),
            args: vec![],
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("todo ! ("), "got: {out}");
    }

    #[test]
    fn unknown_val_emits_todo() {
        let out = collapse(&s(generate_expr(&SorobanExpr::UnknownVal)));
        assert!(out.contains("todo ! (\"unknown value\")"));
    }

    #[test]
    fn val_convert_pass_through() {
        let e = SorobanExpr::ValConvert {
            value: boxed(SorobanExpr::U64Literal(7)),
            target_type: "u64".into(),
        };
        assert_eq!(collapse(&s(generate_expr(&e))), "7");
    }

    #[test]
    fn cast_as_valid_type() {
        let e = SorobanExpr::CastAs {
            value: boxed(SorobanExpr::Param("n".into())),
            target_type: "i64".into(),
        };
        assert_eq!(collapse(&s(generate_expr(&e))), "n as i64");
    }

    #[test]
    fn cast_as_invalid_type_emits_compile_error() {
        let e = SorobanExpr::CastAs {
            value: boxed(SorobanExpr::Param("n".into())),
            target_type: "not a type".into(),
        };
        let out = collapse(&s(generate_expr(&e)));
        // The emitted Rust must contain a compile_error! so the failure is
        // visible at compile time of the decompiled output rather than as a
        // silent miscast to a sanitised identifier.
        assert!(
            out.contains("compile_error !"),
            "expected compile_error fallback, got: {out}"
        );
        assert!(
            out.contains("not a type"),
            "expected target_type in error message, got: {out}"
        );
    }
}

#[cfg(test)]
mod generate_stmt_tests {
    use super::*;

    fn s(t: TokenStream) -> String {
        t.to_string()
    }
    fn collapse(s: &str) -> String {
        s.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    #[test]
    fn expr_stmt_has_semicolon() {
        let stmt = SorobanStmt::Expr(SorobanExpr::U32Literal(7));
        assert_eq!(collapse(&s(generate_stmt(&stmt))), "7 ;");
    }

    #[test]
    fn let_immutable_and_mutable() {
        let im = SorobanStmt::Let {
            name: "x".into(),
            mutable: false,
            value: SorobanExpr::U32Literal(1),
        };
        assert_eq!(collapse(&s(generate_stmt(&im))), "let x = 1 ;");

        let mu = SorobanStmt::Let {
            name: "y".into(),
            mutable: true,
            value: SorobanExpr::U32Literal(2),
        };
        assert_eq!(collapse(&s(generate_stmt(&mu))), "let mut y = 2 ;");
    }

    #[test]
    fn assign_stmt() {
        let stmt = SorobanStmt::Assign {
            target: "x".into(),
            value: SorobanExpr::U32Literal(3),
        };
        assert_eq!(collapse(&s(generate_stmt(&stmt))), "x = 3 ;");
    }

    #[test]
    fn return_with_and_without_value() {
        let r = SorobanStmt::Return(Some(SorobanExpr::U32Literal(7)));
        assert_eq!(collapse(&s(generate_stmt(&r))), "return 7 ;");
        let r = SorobanStmt::Return(None);
        assert_eq!(collapse(&s(generate_stmt(&r))), "return ;");
    }

    #[test]
    fn if_with_and_without_else() {
        let no_else = SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(true),
            then_body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(1))],
            else_body: vec![],
        };
        let out = collapse(&s(generate_stmt(&no_else)));
        assert_eq!(out, "if true { 1 ; }");

        let with_else = SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(false),
            then_body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(1))],
            else_body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(2))],
        };
        let out = collapse(&s(generate_stmt(&with_else)));
        assert_eq!(out, "if false { 1 ; } else { 2 ; }");
    }

    #[test]
    fn match_with_literal_arms_uses_match() {
        let stmt = SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("n".into()),
            arms: vec![
                MatchArm {
                    pattern: MatchPattern::Literal(SorobanExpr::U32Literal(0)),
                    body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(10))],
                },
                MatchArm {
                    pattern: MatchPattern::Wildcard,
                    body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(20))],
                },
            ],
        };
        let out = collapse(&s(generate_stmt(&stmt)));
        assert!(out.starts_with("match n {"), "got: {out}");
        assert!(out.contains("0 => { 10 ; }"));
        assert!(out.contains("_ => { 20 ; }"));
    }

    #[test]
    fn match_with_only_unit_enum_variants_uses_if_else_chain() {
        let stmt = SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("k".into()),
            arms: vec![
                MatchArm {
                    pattern: MatchPattern::EnumVariant {
                        type_name: "DK".into(),
                        variant: "A".into(),
                        bindings: vec![],
                    },
                    body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(1))],
                },
                MatchArm {
                    pattern: MatchPattern::EnumVariant {
                        type_name: "DK".into(),
                        variant: "B".into(),
                        bindings: vec![],
                    },
                    body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(2))],
                },
            ],
        };
        let out = collapse(&s(generate_stmt(&stmt)));
        // Unit-only arms are collapsed into an if/else if chain.
        assert!(out.contains("if k == DK :: A"), "got: {out}");
        assert!(out.contains("else if k == DK :: B"), "got: {out}");
    }

    #[test]
    fn loop_block_break_continue_comment() {
        let loop_stmt = SorobanStmt::Loop {
            body: vec![SorobanStmt::Break],
        };
        let out = collapse(&s(generate_stmt(&loop_stmt)));
        assert!(out.contains("loop { break ; }"), "got: {out}");

        let block = SorobanStmt::Block(vec![SorobanStmt::Continue]);
        assert!(collapse(&s(generate_stmt(&block))).contains("continue ;"));

        assert_eq!(collapse(&s(generate_stmt(&SorobanStmt::Break))), "break ;");
        assert_eq!(
            collapse(&s(generate_stmt(&SorobanStmt::Continue))),
            "continue ;"
        );

        // Comments don't survive TokenStream parsing (proc_macro2 strips them);
        // codegen falls back to empty. Asserts the no-panic contract.
        let c = SorobanStmt::Comment("hi".into());
        assert_eq!(collapse(&s(generate_stmt(&c))), "");
    }

    // ----- Tail variants -----

    #[test]
    fn stmt_tail_strips_trailing_semicolon() {
        let e = SorobanStmt::Expr(SorobanExpr::U32Literal(7));
        let out = collapse(&s(generate_stmt_tail(&e)));
        assert_eq!(out, "7");
    }

    #[test]
    fn stmt_tail_return_drops_keyword() {
        let r = SorobanStmt::Return(Some(SorobanExpr::U32Literal(7)));
        let out = collapse(&s(generate_stmt_tail(&r)));
        assert_eq!(out, "7");
        let r = SorobanStmt::Return(None);
        assert_eq!(collapse(&s(generate_stmt_tail(&r))), "");
    }

    #[test]
    fn stmts_with_tail_keeps_only_last_as_tail() {
        let stmts = vec![
            SorobanStmt::Let {
                name: "x".into(),
                mutable: false,
                value: SorobanExpr::U32Literal(1),
            },
            SorobanStmt::Expr(SorobanExpr::Add(
                Box::new(SorobanExpr::NamedLocal("x".into())),
                Box::new(SorobanExpr::U32Literal(2)),
            )),
        ];
        let tokens = generate_stmts_with_tail(&stmts);
        let joined: String = tokens.iter().map(|t| t.to_string()).collect();
        let out = joined.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(out.contains("let x = 1 ;"), "got: {out}");
        assert!(out.ends_with("x + 2"), "got: {out}");
    }

    #[test]
    fn stmts_with_tail_empty_returns_empty() {
        let tokens = generate_stmts_with_tail(&[]);
        assert!(tokens.is_empty());
    }

    #[test]
    fn stmt_result_wrapped_wraps_naked_return() {
        // Naked Return(Expr) gets wrapped as Ok(Expr) in result-returning fns.
        let stmt = SorobanStmt::Return(Some(SorobanExpr::U32Literal(7)));
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        assert!(out.contains("return Ok (7) ;"), "got: {out}");
    }

    #[test]
    fn stmt_result_wrapped_typed_error_becomes_err() {
        let stmt = SorobanStmt::Return(Some(SorobanExpr::ContractError {
            error_code: 1,
            error_type: Some("Error".into()),
            variant_name: Some("Bad".into()),
        }));
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        assert!(out.contains("return Err (Error :: Bad) ;"), "got: {out}");
    }

    // -------- generate_stmt_tail with control flow --------

    #[test]
    fn stmt_tail_if_recurses_with_tail_form() {
        let stmt = SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(true),
            then_body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(1))],
            else_body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(2))],
        };
        let out = collapse(&s(generate_stmt_tail(&stmt)));
        // No trailing `;` on the tail expressions.
        assert_eq!(out, "if true { 1 } else { 2 }");
    }

    #[test]
    fn stmt_tail_if_no_else() {
        let stmt = SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(true),
            then_body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(7))],
            else_body: vec![],
        };
        let out = collapse(&s(generate_stmt_tail(&stmt)));
        assert_eq!(out, "if true { 7 }");
    }

    #[test]
    fn stmt_tail_match_literal_keeps_match_form() {
        let stmt = SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("n".into()),
            arms: vec![
                MatchArm {
                    pattern: MatchPattern::Literal(SorobanExpr::U32Literal(0)),
                    body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(10))],
                },
                MatchArm {
                    pattern: MatchPattern::Wildcard,
                    body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(20))],
                },
            ],
        };
        let out = collapse(&s(generate_stmt_tail(&stmt)));
        // Tail form: no `;` on the inner expressions.
        assert!(out.starts_with("match n {"), "got: {out}");
        assert!(out.contains("0 => { 10 }"));
        assert!(out.contains("_ => { 20 }"));
    }

    #[test]
    fn stmt_tail_match_unit_enum_collapses_to_if_else_chain() {
        let stmt = SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("k".into()),
            arms: vec![
                MatchArm {
                    pattern: MatchPattern::EnumVariant {
                        type_name: "DK".into(),
                        variant: "A".into(),
                        bindings: vec![],
                    },
                    body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(1))],
                },
                MatchArm {
                    pattern: MatchPattern::EnumVariant {
                        type_name: "DK".into(),
                        variant: "B".into(),
                        bindings: vec![],
                    },
                    body: vec![SorobanStmt::Expr(SorobanExpr::U32Literal(2))],
                },
            ],
        };
        let out = collapse(&s(generate_stmt_tail(&stmt)));
        assert!(out.contains("if k == DK :: A"));
        assert!(out.contains("else if k == DK :: B"));
    }

    #[test]
    fn stmt_tail_loop_uses_standard_stmt_form() {
        let stmt = SorobanStmt::Loop {
            body: vec![SorobanStmt::Break],
        };
        let out = collapse(&s(generate_stmt_tail(&stmt)));
        assert!(out.contains("loop { break ; }"));
    }

    #[test]
    fn stmt_tail_block_recurses_with_tail() {
        let stmt = SorobanStmt::Block(vec![
            SorobanStmt::Let {
                name: "x".into(),
                mutable: false,
                value: SorobanExpr::U32Literal(1),
            },
            SorobanStmt::Expr(SorobanExpr::NamedLocal("x".into())),
        ]);
        let out = collapse(&s(generate_stmt_tail(&stmt)));
        // Block's last stmt is tail (no `;`).
        assert!(out.contains("let x = 1 ;"));
        assert!(out.ends_with("x }"), "got: {out}");
    }

    #[test]
    fn stmt_tail_other_delegates_to_generate_stmt() {
        // A Comment is delegated to generate_stmt (which emits the parsed comment text or empty).
        let stmt = SorobanStmt::Comment("hi".into());
        assert_eq!(collapse(&s(generate_stmt_tail(&stmt))), "");
    }

    // -------- generate_stmt_result_wrapped with control flow --------

    #[test]
    fn stmt_result_wrapped_void_return_passes_through() {
        let stmt = SorobanStmt::Return(Some(SorobanExpr::Void));
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        // Void/UnknownVal/Panic skip Ok() wrapping.
        assert_eq!(out, "return () ;");
    }

    #[test]
    fn stmt_result_wrapped_panic_passes_through() {
        let stmt = SorobanStmt::Return(Some(SorobanExpr::Panic));
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        assert_eq!(out, "return panic ! () ;");
    }

    #[test]
    fn stmt_result_wrapped_if_propagates_wrapping_into_branches() {
        let stmt = SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(true),
            then_body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(1)))],
            else_body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(2)))],
        };
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        // Both arms wrap their returns in Ok().
        assert!(out.contains("return Ok (1) ;"), "got: {out}");
        assert!(out.contains("return Ok (2) ;"), "got: {out}");
    }

    #[test]
    fn stmt_result_wrapped_if_no_else() {
        let stmt = SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(false),
            then_body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(1)))],
            else_body: vec![],
        };
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        assert!(out.contains("return Ok (1) ;"));
        assert!(!out.contains("else"), "stray else: {out}");
    }

    #[test]
    fn stmt_result_wrapped_match_unit_enum_collapses_to_chain() {
        let stmt = SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("k".into()),
            arms: vec![
                MatchArm {
                    pattern: MatchPattern::EnumVariant {
                        type_name: "K".into(),
                        variant: "A".into(),
                        bindings: vec![],
                    },
                    body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(1)))],
                },
                MatchArm {
                    pattern: MatchPattern::Wildcard,
                    body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(2)))],
                },
            ],
        };
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        assert!(out.contains("if k == K :: A"), "got: {out}");
        assert!(out.contains("Ok (1)"));
        assert!(out.contains("Ok (2)"));
    }

    #[test]
    fn stmt_result_wrapped_match_with_literal_keeps_match_form() {
        let stmt = SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("n".into()),
            arms: vec![MatchArm {
                pattern: MatchPattern::Literal(SorobanExpr::U32Literal(0)),
                body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(99)))],
            }],
        };
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        assert!(out.contains("match n {"), "got: {out}");
        assert!(out.contains("Ok (99)"));
    }

    #[test]
    fn stmt_result_wrapped_loop_body_returns_get_wrapped() {
        let stmt = SorobanStmt::Loop {
            body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(7)))],
        };
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        assert!(out.contains("loop {"), "got: {out}");
        assert!(out.contains("return Ok (7) ;"), "got: {out}");
    }

    #[test]
    fn stmt_result_wrapped_block_recurses() {
        let stmt = SorobanStmt::Block(vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(5)))]);
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        assert!(out.contains("{ return Ok (5) ; }"), "got: {out}");
    }

    #[test]
    fn stmt_result_wrapped_panic_with_error_becomes_err() {
        // PanicWithError(ContractError with type+variant) in a Result-returning fn
        // converts back to `return Err(variant);`.
        let stmt = SorobanStmt::Expr(SorobanExpr::PanicWithError(Box::new(
            SorobanExpr::ContractError {
                error_code: 1,
                error_type: Some("E".into()),
                variant_name: Some("Bad".into()),
            },
        )));
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        assert_eq!(out, "return Err (E :: Bad) ;");
    }

    #[test]
    fn stmt_result_wrapped_panic_with_error_untyped_stays_as_call() {
        // Untyped (raw code) PanicWithError stays as a statement, not Err.
        let stmt = SorobanStmt::Expr(SorobanExpr::PanicWithError(Box::new(
            SorobanExpr::ErrorFromCode(Box::new(SorobanExpr::U32Literal(5))),
        )));
        let out = collapse(&s(generate_stmt_result_wrapped(&stmt)));
        assert!(out.contains("panic_with_error !"), "got: {out}");
        assert!(
            !out.contains("return Err"),
            "should not wrap raw codes: {out}"
        );
    }

    // -------- generate_stmts_with_tail_result_wrapped --------

    fn render_stmts_with_tail_result_wrapped(stmts: &[SorobanStmt]) -> String {
        let toks = generate_stmts_with_tail_result_wrapped(stmts);
        let joined: String = toks.iter().map(|t| t.to_string()).collect();
        joined.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    #[test]
    fn stmts_with_tail_result_wrapped_empty_returns_empty() {
        assert!(generate_stmts_with_tail_result_wrapped(&[]).is_empty());
    }

    #[test]
    fn stmts_with_tail_result_wrapped_wraps_only_last_return() {
        let stmts = vec![
            SorobanStmt::Let {
                name: "x".into(),
                mutable: false,
                value: SorobanExpr::U32Literal(1),
            },
            SorobanStmt::Return(Some(SorobanExpr::NamedLocal("x".into()))),
        ];
        let out = render_stmts_with_tail_result_wrapped(&stmts);
        assert!(out.contains("let x = 1 ;"));
        assert!(out.ends_with("Ok (x)"), "got: {out}");
    }

    #[test]
    fn stmts_with_tail_result_wrapped_typed_error_tail() {
        let stmts = vec![SorobanStmt::Return(Some(SorobanExpr::ContractError {
            error_code: 1,
            error_type: Some("E".into()),
            variant_name: Some("X".into()),
        }))];
        let out = render_stmts_with_tail_result_wrapped(&stmts);
        assert_eq!(out, "Err (E :: X)");
    }

    #[test]
    fn stmts_with_tail_result_wrapped_void_return_empty() {
        let stmts = vec![SorobanStmt::Return(None)];
        let out = render_stmts_with_tail_result_wrapped(&stmts);
        assert_eq!(out, "");
    }

    #[test]
    fn stmts_with_tail_result_wrapped_panic_with_error_tail() {
        // tail-position PanicWithError(typed) → Err(...) without trailing semicolon.
        let stmts = vec![SorobanStmt::Expr(SorobanExpr::PanicWithError(Box::new(
            SorobanExpr::ContractError {
                error_code: 1,
                error_type: Some("E".into()),
                variant_name: Some("X".into()),
            },
        )))];
        let out = render_stmts_with_tail_result_wrapped(&stmts);
        assert_eq!(out, "Err (E :: X)");
    }

    #[test]
    fn stmts_with_tail_result_wrapped_if_propagates_into_branches() {
        let stmts = vec![SorobanStmt::If {
            condition: SorobanExpr::BoolLiteral(true),
            then_body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(1)))],
            else_body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(2)))],
        }];
        let out = render_stmts_with_tail_result_wrapped(&stmts);
        // Tail context: both branches wrap returns as tail expressions.
        assert!(out.contains("Ok (1)"));
        assert!(out.contains("Ok (2)"));
        assert!(out.contains("if true"));
    }

    #[test]
    fn stmts_with_tail_result_wrapped_match_literal_keeps_match() {
        let stmts = vec![SorobanStmt::Match {
            scrutinee: SorobanExpr::Param("n".into()),
            arms: vec![MatchArm {
                pattern: MatchPattern::Literal(SorobanExpr::U32Literal(0)),
                body: vec![SorobanStmt::Return(Some(SorobanExpr::U32Literal(7)))],
            }],
        }];
        let out = render_stmts_with_tail_result_wrapped(&stmts);
        assert!(out.starts_with("match n {"));
        assert!(out.contains("Ok (7)"));
    }

    #[test]
    fn stmts_with_tail_result_wrapped_loop_uses_standard_form() {
        let stmts = vec![SorobanStmt::Loop {
            body: vec![SorobanStmt::Break],
        }];
        let out = render_stmts_with_tail_result_wrapped(&stmts);
        assert!(out.contains("loop { break ; }"));
    }

    #[test]
    fn stmts_with_tail_result_wrapped_block_recurses() {
        let stmts = vec![SorobanStmt::Block(vec![SorobanStmt::Return(Some(
            SorobanExpr::U32Literal(7),
        ))])];
        let out = render_stmts_with_tail_result_wrapped(&stmts);
        // Block in tail position recurses; inner Return tail-wraps as Ok(7).
        assert!(out.contains("Ok (7)"), "got: {out}");
    }

    // -------- Misc smaller branches in generate_expr_base --------

    #[test]
    fn invoke_contract_multi_args_each_into_val() {
        let e = SorobanExpr::InvokeContract {
            address: Box::new(SorobanExpr::Param("a".into())),
            function: Box::new(SorobanExpr::SymbolLiteral("f".into())),
            args: vec![
                SorobanExpr::Param("x".into()),
                SorobanExpr::Param("y".into()),
            ],
            return_type: Some("u64".into()),
        };
        let out = collapse(&s(generate_expr(&e)));
        // Both args go through .into_val(&env).
        assert!(
            out.contains("x . into_val (& env)") && out.contains("y . into_val (& env)"),
            "got: {out}"
        );
    }

    #[test]
    fn raw_host_call_no_args_emits_no_paren_arg_list() {
        let e = SorobanExpr::RawHostCall {
            module: "Ctx".into(),
            function: "f".into(),
            args: vec![],
        };
        let out = collapse(&s(generate_expr(&e)));
        // Should be `env.ctx().f()` without an arg list.
        assert_eq!(out, "env . ctx () . f ()");
    }

    #[test]
    fn publish_event_multiple_topics_emits_tuple() {
        let e = SorobanExpr::PublishEvent {
            event_name: None,
            topics: vec![
                SorobanExpr::SymbolLiteral("a".into()),
                SorobanExpr::SymbolLiteral("b".into()),
            ],
            data: Box::new(SorobanExpr::U64Literal(7)),
        };
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("env . events () . publish"));
        assert!(out.contains("symbol_short ! (\"a\")"));
        assert!(out.contains("symbol_short ! (\"b\")"));
    }

    #[test]
    fn val_tag_check_renders_get_tag_and_named_tag() {
        // `arg.get_tag() != Tag::VecObject` — a recovered tag guard (issue #4).
        let e = SorobanExpr::Ne(
            Box::new(SorobanExpr::ValTag(Box::new(SorobanExpr::Param(
                "arg".into(),
            )))),
            Box::new(SorobanExpr::ValTagName("VecObject".into())),
        );
        let out = collapse(&s(generate_expr(&e)));
        assert!(out.contains("arg . get_tag ()"), "got: {out}");
        assert!(out.contains("Tag :: VecObject"), "got: {out}");
        assert!(out.contains("!="), "got: {out}");
        assert!(!out.contains("todo !"), "got: {out}");
    }
}
