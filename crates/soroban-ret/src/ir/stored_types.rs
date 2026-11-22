//! The type of the value a contract stores under each storage key, from the
//! evidence the bytecode gives (campaign stage 3b).
//!
//! `env.storage().<kind>().get(&key)` is generic over its value type. When the
//! lifter cannot see a typed use of the result, rustc cannot infer it
//! (E0282/E0283/E0284), and when the result flows into a context of another
//! type, rustc infers the WRONG type and the recompiled contract decodes the
//! stored value as something it is not. This module collects, per contract,
//! what each key is proven to hold, and annotates every read of that key with
//! it (`get::<_, T>(&key)`, through the `CastAs { StorageGet, T }` vehicle).
//!
//! Evidence, per (storage kind, key shape):
//!
//! - **Typed writes** (required). `set(&key, &v)` where `v` is a parameter
//!   of a spec type, or a struct / enum literal. Every value the contract
//!   stores under the key is then a `T`, so reading it as `T` succeeds and
//!   fails on the same states as the original's read.
//! - **The decode of a read** (confirms or conflicts). The SDK decodes a
//!   stored struct with `map_unpack_to_linear_memory` over the struct's
//!   field-name array; the lifter records the struct named by that exact
//!   field list when exactly one spec struct has it ([`StoredTypeEvidence`],
//!   collected in `pattern::lifter`). The type is what the original reads,
//!   but the KEY attached to the read is the lifter's recovery, which inside
//!   inlined helpers can name the wrong variant (blend pools: a temporary
//!   auction read keyed `ResConfig`). So a decode never creates an entry on
//!   its own: it only adds its type, which turns a disagreement into a
//!   conflict.
//! - **Typed consumers already proven** (confirm or conflict, same reason):
//!   a read that is `require_auth()`-ed (an `Address`), and reads already
//!   annotated with a concrete type (the storage try-get lowering, the
//!   fallible-getter rebuild).
//!
//! A key whose evidence names two types gets no entry. `Val` is never
//! evidence. A write whose key shape is unknown could have written anything
//! of its storage kind, so it cancels every entry of that kind not also
//! confirmed by a decode.
//!
//! The key shape ignores the payload of an enum variant (`Balance(addr)` is
//! `Balance`): the evidence is pooled over every payload the contract uses,
//! and a variant stored with two types gets no entry.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use stellar_xdr::curr::ScSpecTypeDef;

use super::correctness::{
    for_each_expr_in_stmts, for_each_subexpr, map_exprs_in_stmts, map_subexprs,
};
use super::high_level_ir::FnParam;
use super::soroban_ir::{SorobanExpr, SorobanStmt, StorageType};
use crate::spec::registry::TypeRegistry;

/// What a storage key looks like, independent of the optimizer's rendering:
/// `DataKey::Admin` and `vec![Symbol("Admin")]` are the same key.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KeyShape {
    /// An enum variant key (`vec![Symbol(name), payload..]`), payload ignored.
    Variant(String),
    /// A bare symbol key (`symbol_short!("name")`).
    Symbol(String),
}

/// One stored-type observation made by the lifter at a decode site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoredTypeEvidence {
    pub storage_type: StorageType,
    pub key: KeyShape,
    pub type_name: String,
}

fn kind_index(st: StorageType) -> u8 {
    match st {
        StorageType::Persistent => 0,
        StorageType::Temporary => 1,
        StorageType::Instance => 2,
    }
}

/// Immutable single-binding `let`s of a body, for resolving a key or value
/// that is reached through a variable. A name bound twice, or assigned, is
/// left out (it does not denote one value).
pub fn single_lets(stmts: &[SorobanStmt]) -> HashMap<String, SorobanExpr> {
    fn walk(stmts: &[SorobanStmt], seen: &mut HashMap<String, Option<SorobanExpr>>) {
        for s in stmts {
            match s {
                SorobanStmt::Let { name, value, .. } => {
                    seen.entry(name.clone())
                        .and_modify(|v| *v = None)
                        .or_insert_with(|| Some(value.clone()));
                }
                SorobanStmt::Assign { target, .. } => {
                    seen.insert(target.clone(), None);
                }
                SorobanStmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    walk(then_body, seen);
                    walk(else_body, seen);
                }
                SorobanStmt::Match { arms, .. } => {
                    for a in arms {
                        walk(&a.body, seen);
                    }
                }
                SorobanStmt::Loop { body }
                | SorobanStmt::Block(body)
                | SorobanStmt::For { body, .. } => walk(body, seen),
                _ => {}
            }
        }
    }
    let mut seen = HashMap::new();
    walk(stmts, &mut seen);
    seen.into_iter()
        .filter_map(|(k, v)| v.map(|v| (k, v)))
        .collect()
}

fn var_name(e: &SorobanExpr) -> Option<String> {
    match e {
        SorobanExpr::Local(i) => Some(format!("var_{i}")),
        SorobanExpr::NamedLocal(n) => Some(n.clone()),
        _ => None,
    }
}

/// The shape of a storage key expression, following variables and `.clone()`.
pub fn key_shape(key: &SorobanExpr, lets: &HashMap<String, SorobanExpr>) -> Option<KeyShape> {
    key_shape_depth(key, lets, 0)
}

fn key_shape_depth(
    key: &SorobanExpr,
    lets: &HashMap<String, SorobanExpr>,
    depth: u8,
) -> Option<KeyShape> {
    if depth > 8 {
        return None;
    }
    match key {
        SorobanExpr::EnumConstruct { variant, .. } => Some(KeyShape::Variant(variant.clone())),
        SorobanExpr::VecConstruct(items) => match items.first() {
            Some(SorobanExpr::SymbolLiteral(s)) => Some(KeyShape::Variant(s.clone())),
            _ => None,
        },
        SorobanExpr::SymbolLiteral(s) => Some(KeyShape::Symbol(s.clone())),
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } if method == "clone" && args.is_empty() => key_shape_depth(object, lets, depth + 1),
        e => {
            let name = var_name(e)?;
            key_shape_depth(lets.get(&name)?, lets, depth + 1)
        }
    }
}

/// The Rust type of a written value, when the IR proves it.
fn written_type(
    value: &SorobanExpr,
    params: &[FnParam],
    lets: &HashMap<String, SorobanExpr>,
    registry: &TypeRegistry,
    depth: u8,
) -> Option<String> {
    if depth > 8 {
        return None;
    }
    match value {
        SorobanExpr::Param(p) => {
            let param = params.iter().find(|fp| fp.name == *p)?;
            if matches!(param.type_def, ScSpecTypeDef::Val) {
                return None;
            }
            crate::pipeline::spec_type_to_string(&param.type_def)
        }
        SorobanExpr::StructConstruct { type_name, .. }
            if registry.structs.contains_key(type_name) =>
        {
            Some(type_name.clone())
        }
        SorobanExpr::EnumConstruct { type_name, .. }
            if registry.unions.contains_key(type_name)
                || registry.enums.contains_key(type_name) =>
        {
            Some(type_name.clone())
        }
        SorobanExpr::MethodCall {
            object,
            method,
            args,
        } if method == "clone" && args.is_empty() => {
            written_type(object, params, lets, registry, depth + 1)
        }
        e => {
            let name = var_name(e)?;
            written_type(lets.get(&name)?, params, lets, registry, depth + 1)
        }
    }
}

/// A concrete annotation type (not `Val` or a type built over it).
fn is_concrete(ty: &str) -> bool {
    !ty.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .any(|t| t == "Val")
}

#[derive(Default)]
struct Entry {
    types: BTreeSet<String>,
    decoded: bool,
    written: bool,
}

/// The per-contract table of proven stored-value types.
#[derive(Default)]
pub struct StoredTypes {
    entries: BTreeMap<(u8, KeyShape), Entry>,
    /// Storage kinds that a write with an unknown key may have written to.
    blind_writes: BTreeSet<u8>,
}

impl StoredTypes {
    /// Collect evidence from the lifter's decode observations and from every
    /// function body.
    pub fn collect<'a>(
        decoded: &[StoredTypeEvidence],
        functions: impl IntoIterator<Item = (&'a [SorobanStmt], &'a [FnParam])>,
        registry: &TypeRegistry,
    ) -> Self {
        let mut table = StoredTypes::default();
        for ev in decoded {
            let entry = table
                .entries
                .entry((kind_index(ev.storage_type), ev.key.clone()))
                .or_default();
            entry.types.insert(ev.type_name.clone());
            entry.decoded = true;
        }
        for (body, params) in functions {
            let lets = single_lets(body);
            let mut visit = |e: &SorobanExpr| table.observe(e, params, &lets, registry);
            for_each_expr_in_stmts(body, &mut visit);
        }
        table
    }

    fn add(&mut self, st: StorageType, key: KeyShape, ty: String) {
        if is_concrete(&ty) {
            self.entries
                .entry((kind_index(st), key))
                .or_default()
                .types
                .insert(ty);
        }
    }

    fn observe(
        &mut self,
        e: &SorobanExpr,
        params: &[FnParam],
        lets: &HashMap<String, SorobanExpr>,
        registry: &TypeRegistry,
    ) {
        match e {
            SorobanExpr::StorageSet {
                storage_type,
                key,
                value,
            } => match key_shape(key, lets) {
                Some(shape) => {
                    if let Some(ty) = written_type(value, params, lets, registry, 0) {
                        let concrete = is_concrete(&ty);
                        self.add(*storage_type, shape.clone(), ty);
                        if concrete {
                            self.entries
                                .entry((kind_index(*storage_type), shape))
                                .or_default()
                                .written = true;
                        }
                    }
                }
                None => {
                    self.blind_writes.insert(kind_index(*storage_type));
                }
            },
            SorobanExpr::RequireAuth(inner) => {
                if let SorobanExpr::StorageGet {
                    storage_type, key, ..
                } = inner.as_ref()
                    && let Some(shape) = key_shape(key, lets)
                {
                    self.add(*storage_type, shape, "Address".to_string());
                }
            }
            SorobanExpr::CastAs { value, target_type } => {
                if let SorobanExpr::StorageGet {
                    storage_type, key, ..
                } = value.as_ref()
                    && let Some(shape) = key_shape(key, lets)
                {
                    self.add(*storage_type, shape, target_type.clone());
                }
            }
            _ => {}
        }
        for_each_subexpr(e, &mut |sub| self.observe(sub, params, lets, registry));
    }

    /// The proven type of the value stored under `key`, if exactly one.
    pub fn type_of(&self, st: StorageType, key: &KeyShape) -> Option<&str> {
        let k = kind_index(st);
        let entry = self.entries.get(&(k, key.clone()))?;
        if entry.types.len() != 1 {
            return None;
        }
        if !entry.written {
            return None;
        }
        if !entry.decoded && self.blind_writes.contains(&k) {
            return None;
        }
        entry.types.iter().next().map(String::as_str)
    }

    /// Annotate every bare read of a key with a proven type.
    pub fn annotate(&self, stmts: Vec<SorobanStmt>) -> Vec<SorobanStmt> {
        let lets = single_lets(&stmts);
        map_exprs_in_stmts(stmts, &|e| self.annotate_expr(e, &lets))
    }

    fn annotate_expr(&self, e: SorobanExpr, lets: &HashMap<String, SorobanExpr>) -> SorobanExpr {
        match e {
            // Already typed: only its key may hold a read to annotate.
            SorobanExpr::CastAs { value, target_type }
                if matches!(*value, SorobanExpr::StorageGet { .. }) =>
            {
                SorobanExpr::CastAs {
                    value: Box::new(map_subexprs(*value, &|x| self.annotate_expr(x, lets))),
                    target_type,
                }
            }
            SorobanExpr::StorageGet { .. } => {
                let get = map_subexprs(e, &|x| self.annotate_expr(x, lets));
                let SorobanExpr::StorageGet {
                    storage_type, key, ..
                } = &get
                else {
                    unreachable!()
                };
                match key_shape(key, lets).and_then(|shape| self.type_of(*storage_type, &shape)) {
                    Some(ty) => {
                        cov_mark::hit!(stored_type_read_annotated);
                        SorobanExpr::CastAs {
                            value: Box::new(get),
                            target_type: ty.to_string(),
                        }
                    }
                    None => get,
                }
            }
            other => map_subexprs(other, &|x| self.annotate_expr(x, lets)),
        }
    }
}

/// The Rust type a storage read evaluates to, once annotated: `T` for
/// `get::<_, T>(..).unwrap()`, `Option<T>` for a bare `get::<_, T>(..)`.
/// `None` for anything else (including the defaulting and fallible forms,
/// whose rendering depends on the `on_missing` value).
fn read_value_type(e: &SorobanExpr) -> Option<String> {
    let SorobanExpr::CastAs { value, target_type } = e else {
        return None;
    };
    let SorobanExpr::StorageGet {
        unwrap, on_missing, ..
    } = value.as_ref()
    else {
        return None;
    };
    match (unwrap, on_missing) {
        (true, None) => Some(target_type.clone()),
        (false, None) => Some(format!("Option<{target_type}>")),
        _ => None,
    }
}

/// A function that returns a storage read whose proven type is not its
/// declared return type returns a value it never had: fxdao-oracle
/// `resolution() -> u32` returned `get::<_, CoreData>(..).unwrap()`, where the
/// bytecode returns the `tick` field the lifter lost. Keep the read (it runs,
/// and traps when the key is missing) as a statement and return an honest
/// `todo!()` instead. Applies to the body's tail and to every `return`.
pub fn hole_reads_returned_as_another_type(
    stmts: Vec<SorobanStmt>,
    return_type: Option<&ScSpecTypeDef>,
) -> Vec<SorobanStmt> {
    let want = match return_type {
        Some(ScSpecTypeDef::Result(r)) => crate::pipeline::spec_type_to_string(&r.ok_type),
        Some(t) => crate::pipeline::spec_type_to_string(t),
        None => None,
    };
    let Some(want) = want.filter(|w| is_concrete(w)) else {
        return stmts;
    };
    hole_in_stmts(stmts, &want, true)
}

fn mismatched(e: &SorobanExpr, want: &str) -> bool {
    read_value_type(e).is_some_and(|have| have != want)
}

fn hole_in_stmts(stmts: Vec<SorobanStmt>, want: &str, is_tail: bool) -> Vec<SorobanStmt> {
    let last = stmts.len().saturating_sub(1);
    let mut out = Vec::with_capacity(stmts.len());
    for (i, stmt) in stmts.into_iter().enumerate() {
        let tail = is_tail && i == last;
        match stmt {
            SorobanStmt::Return(Some(e)) if mismatched(&e, want) => {
                cov_mark::hit!(read_returned_as_another_type_holed);
                out.push(SorobanStmt::Expr(e));
                out.push(SorobanStmt::Return(Some(SorobanExpr::UnknownVal)));
            }
            SorobanStmt::Expr(e) if tail && mismatched(&e, want) => {
                cov_mark::hit!(read_returned_as_another_type_holed);
                out.push(SorobanStmt::Expr(e));
                out.push(SorobanStmt::Expr(SorobanExpr::UnknownVal));
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => out.push(SorobanStmt::If {
                condition,
                then_body: hole_in_stmts(then_body, want, tail),
                else_body: hole_in_stmts(else_body, want, tail),
            }),
            SorobanStmt::Match { scrutinee, arms } => out.push(SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|a| super::soroban_ir::MatchArm {
                        pattern: a.pattern,
                        body: hole_in_stmts(a.body, want, tail),
                    })
                    .collect(),
            }),
            SorobanStmt::Block(body) => {
                out.push(SorobanStmt::Block(hole_in_stmts(body, want, tail)))
            }
            SorobanStmt::Loop { body } => out.push(SorobanStmt::Loop {
                body: hole_in_stmts(body, want, false),
            }),
            SorobanStmt::For {
                var,
                start,
                end,
                step,
                body,
            } => out.push(SorobanStmt::For {
                var,
                start,
                end,
                step,
                body: hole_in_stmts(body, want, false),
            }),
            other => out.push(other),
        }
    }
    out
}

/// A typed read of a contract struct or union followed by `.get(i)`: the
/// lifter's view of the SDK decoding the value's vec encoding (a union is
/// `vec![Symbol(variant), payload..]`), not anything the source wrote. The
/// type has no `get` method, so the fragment cannot be a value of the
/// original; it becomes an honest `todo!()`. The read itself stays as a
/// statement (it traps when the key is missing). Statement-level only:
/// `let x = read.get(i)`, `x = read.get(i)`, `read.get(i);`.
pub fn hole_decode_fragments(stmts: Vec<SorobanStmt>, registry: &TypeRegistry) -> Vec<SorobanStmt> {
    let fragment = |e: &SorobanExpr| -> Option<SorobanExpr> {
        let SorobanExpr::MethodCall {
            object,
            method,
            args,
        } = e
        else {
            return None;
        };
        if method != "get" || args.len() != 1 {
            return None;
        }
        let SorobanExpr::CastAs { value, target_type } = object.as_ref() else {
            return None;
        };
        let SorobanExpr::StorageGet {
            unwrap: true,
            on_missing: None,
            ..
        } = value.as_ref()
        else {
            return None;
        };
        (registry.unions.contains_key(target_type) || registry.structs.contains_key(target_type))
            .then(|| (**object).clone())
    };
    let mut out = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        match stmt {
            SorobanStmt::Let {
                name,
                mutable,
                value,
            } if fragment(&value).is_some() => {
                cov_mark::hit!(decode_fragment_holed);
                out.push(SorobanStmt::Expr(fragment(&value).unwrap()));
                out.push(SorobanStmt::Let {
                    name,
                    mutable,
                    value: SorobanExpr::UnknownVal,
                });
            }
            SorobanStmt::Assign { target, value } if fragment(&value).is_some() => {
                cov_mark::hit!(decode_fragment_holed);
                out.push(SorobanStmt::Expr(fragment(&value).unwrap()));
                out.push(SorobanStmt::Assign {
                    target,
                    value: SorobanExpr::UnknownVal,
                });
            }
            SorobanStmt::Expr(e) if fragment(&e).is_some() => {
                cov_mark::hit!(decode_fragment_holed);
                out.push(SorobanStmt::Expr(fragment(&e).unwrap()));
            }
            SorobanStmt::If {
                condition,
                then_body,
                else_body,
            } => out.push(SorobanStmt::If {
                condition,
                then_body: hole_decode_fragments(then_body, registry),
                else_body: hole_decode_fragments(else_body, registry),
            }),
            SorobanStmt::Match { scrutinee, arms } => out.push(SorobanStmt::Match {
                scrutinee,
                arms: arms
                    .into_iter()
                    .map(|a| super::soroban_ir::MatchArm {
                        pattern: a.pattern,
                        body: hole_decode_fragments(a.body, registry),
                    })
                    .collect(),
            }),
            SorobanStmt::Loop { body } => out.push(SorobanStmt::Loop {
                body: hole_decode_fragments(body, registry),
            }),
            SorobanStmt::Block(body) => {
                out.push(SorobanStmt::Block(hole_decode_fragments(body, registry)))
            }
            SorobanStmt::For {
                var,
                start,
                end,
                step,
                body,
            } => out.push(SorobanStmt::For {
                var,
                start,
                end,
                step,
                body: hole_decode_fragments(body, registry),
            }),
            other => out.push(other),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use stellar_xdr::curr::{ScSpecUdtStructFieldV0, ScSpecUdtStructV0, StringM, VecM};

    fn registry() -> TypeRegistry {
        let field = |name: &str| ScSpecUdtStructFieldV0 {
            doc: StringM::default(),
            name: name.try_into().unwrap(),
            type_: ScSpecTypeDef::U32,
        };
        let mut registry = TypeRegistry {
            functions: Default::default(),
            structs: Default::default(),
            unions: Default::default(),
            enums: Default::default(),
            error_enums: Default::default(),
            events: Default::default(),
            meta: Vec::new(),
            spec_entries: Vec::new(),
        };
        for name in ["Config", "Other"] {
            registry.structs.insert(
                name.into(),
                ScSpecUdtStructV0 {
                    doc: StringM::default(),
                    lib: StringM::default(),
                    name: name.try_into().unwrap(),
                    fields: VecM::try_from(vec![field("a")]).unwrap(),
                },
            );
        }
        registry
    }

    fn key(variant: &str) -> SorobanExpr {
        SorobanExpr::EnumConstruct {
            type_name: "DataKey".into(),
            variant: variant.into(),
            fields: vec![],
        }
    }

    fn get(variant: &str) -> SorobanExpr {
        SorobanExpr::StorageGet {
            storage_type: StorageType::Instance,
            key: Box::new(key(variant)),
            unwrap: true,
            on_missing: None,
        }
    }

    fn set(variant: &str, value: SorobanExpr) -> SorobanStmt {
        SorobanStmt::Expr(SorobanExpr::StorageSet {
            storage_type: StorageType::Instance,
            key: Box::new(key(variant)),
            value: Box::new(value),
        })
    }

    fn param(name: &str, ty: ScSpecTypeDef) -> FnParam {
        FnParam {
            name: name.into(),
            type_def: ty,
        }
    }

    fn table(
        decoded: &[StoredTypeEvidence],
        body: &[SorobanStmt],
        params: &[FnParam],
    ) -> StoredTypes {
        StoredTypes::collect(decoded, [(body, params)], &registry())
    }

    fn decoded(variant: &str, ty: &str) -> StoredTypeEvidence {
        StoredTypeEvidence {
            storage_type: StorageType::Instance,
            key: KeyShape::Variant(variant.into()),
            type_name: ty.into(),
        }
    }

    fn annotated(t: &StoredTypes, variant: &str) -> Option<String> {
        match t.annotate(vec![SorobanStmt::Expr(get(variant))]).pop() {
            Some(SorobanStmt::Expr(SorobanExpr::CastAs { target_type, .. })) => Some(target_type),
            _ => None,
        }
    }

    #[test]
    fn a_typed_write_types_every_read_of_its_key() {
        cov_mark::check!(stored_type_read_annotated);
        let params = [param("admin", ScSpecTypeDef::Address)];
        let t = table(
            &[],
            &[set("Admin", SorobanExpr::Param("admin".into()))],
            &params,
        );
        assert_eq!(annotated(&t, "Admin").as_deref(), Some("Address"));
        assert_eq!(annotated(&t, "Other"), None, "another key is left alone");
    }

    #[test]
    fn a_struct_literal_write_types_its_key() {
        let lit = SorobanExpr::StructConstruct {
            type_name: "Config".into(),
            fields: vec![("a".into(), SorobanExpr::U32Literal(1))],
        };
        let t = table(&[], &[set("Cfg", lit)], &[]);
        assert_eq!(annotated(&t, "Cfg").as_deref(), Some("Config"));
    }

    #[test]
    fn a_decode_alone_types_nothing() {
        // The type is what the original reads, but the key on the read is
        // the lifter's recovery and can be wrong.
        let t = table(&[decoded("Cfg", "Config")], &[], &[]);
        assert_eq!(annotated(&t, "Cfg"), None);
    }

    #[test]
    fn a_decode_of_another_type_cancels_the_write() {
        let params = [param(
            "c",
            ScSpecTypeDef::Udt(stellar_xdr::curr::ScSpecTypeUdt {
                name: "Config".try_into().unwrap(),
            }),
        )];
        let body = [set("Cfg", SorobanExpr::Param("c".into()))];
        assert_eq!(
            annotated(&table(&[decoded("Cfg", "Config")], &body, &params), "Cfg").as_deref(),
            Some("Config"),
            "an agreeing decode keeps the entry"
        );
        assert_eq!(
            annotated(&table(&[decoded("Cfg", "Other")], &body, &params), "Cfg"),
            None,
            "a disagreeing decode cancels it"
        );
    }

    #[test]
    fn two_written_types_give_no_entry() {
        let params = [
            param("a", ScSpecTypeDef::Address),
            param("n", ScSpecTypeDef::U32),
        ];
        let body = [
            set("K", SorobanExpr::Param("a".into())),
            set("K", SorobanExpr::Param("n".into())),
        ];
        assert_eq!(annotated(&table(&[], &body, &params), "K"), None);
    }

    #[test]
    fn a_write_to_an_unknown_key_cancels_unconfirmed_entries() {
        let params = [param("a", ScSpecTypeDef::Address)];
        let blind = SorobanStmt::Expr(SorobanExpr::StorageSet {
            storage_type: StorageType::Instance,
            key: Box::new(SorobanExpr::UnknownVal),
            value: Box::new(SorobanExpr::UnknownVal),
        });
        let body = [set("Admin", SorobanExpr::Param("a".into())), blind];
        assert_eq!(annotated(&table(&[], &body, &params), "Admin"), None);
        assert_eq!(
            annotated(
                &table(&[decoded("Admin", "Address")], &body, &params),
                "Admin"
            )
            .as_deref(),
            Some("Address"),
            "a decode of the same type confirms it"
        );
    }

    #[test]
    fn val_is_never_evidence() {
        let params = [param("v", ScSpecTypeDef::Val)];
        let t = table(&[], &[set("K", SorobanExpr::Param("v".into()))], &params);
        assert_eq!(annotated(&t, "K"), None);
    }

    #[test]
    fn a_key_bound_to_a_variable_has_the_same_shape() {
        let lets: HashMap<String, SorobanExpr> =
            [("vp".to_string(), key("Admin"))].into_iter().collect();
        assert_eq!(
            key_shape(&SorobanExpr::NamedLocal("vp".into()), &lets),
            Some(KeyShape::Variant("Admin".into()))
        );
        assert_eq!(
            key_shape(
                &SorobanExpr::VecConstruct(vec![SorobanExpr::SymbolLiteral("Admin".into())]),
                &lets
            ),
            Some(KeyShape::Variant("Admin".into())),
            "`vec![Symbol]` is the encoding of the unit variant"
        );
        assert_eq!(
            key_shape(&SorobanExpr::SymbolLiteral("Admin".into()), &lets),
            Some(KeyShape::Symbol("Admin".into())),
            "a bare symbol is a different key"
        );
    }

    #[test]
    fn a_read_returned_as_another_type_becomes_a_hole() {
        cov_mark::check!(read_returned_as_another_type_holed);
        let read = SorobanExpr::CastAs {
            value: Box::new(get("Cfg")),
            target_type: "Config".into(),
        };
        let out = hole_reads_returned_as_another_type(
            vec![SorobanStmt::Expr(read.clone())],
            Some(&ScSpecTypeDef::U32),
        );
        assert!(
            matches!(
                out.as_slice(),
                [SorobanStmt::Expr(r), SorobanStmt::Expr(SorobanExpr::UnknownVal)] if *r == read
            ),
            "the read stays, the value is a hole: {out:?}"
        );
    }

    #[test]
    fn a_read_returned_as_its_own_type_stays() {
        let read = SorobanExpr::CastAs {
            value: Box::new(get("Cfg")),
            target_type: "u32".into(),
        };
        let body = vec![SorobanStmt::Expr(read)];
        let out = hole_reads_returned_as_another_type(body.clone(), Some(&ScSpecTypeDef::U32));
        assert_eq!(format!("{out:?}"), format!("{body:?}"));
    }

    #[test]
    fn a_get_on_a_typed_struct_read_is_a_decode_fragment() {
        cov_mark::check!(decode_fragment_holed);
        let read = SorobanExpr::CastAs {
            value: Box::new(get("Cfg")),
            target_type: "Config".into(),
        };
        let out = hole_decode_fragments(
            vec![SorobanStmt::Assign {
                target: "vp".into(),
                value: SorobanExpr::MethodCall {
                    object: Box::new(read.clone()),
                    method: "get".into(),
                    args: vec![SorobanExpr::U32Literal(0)],
                },
            }],
            &registry(),
        );
        assert!(
            matches!(
                out.as_slice(),
                [
                    SorobanStmt::Expr(r),
                    SorobanStmt::Assign { value: SorobanExpr::UnknownVal, .. }
                ] if *r == read
            ),
            "{out:?}"
        );
    }
}
