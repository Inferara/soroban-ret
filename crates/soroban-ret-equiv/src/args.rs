//! Argument generation for the equivalence harness.
//!
//! [`Generator::values`] turns a spec type into a short list of candidate
//! [`ScVal`]s: boundary values plus a seeded one for scalars, and a few
//! shapes (empty / one / several) for aggregates. User-defined types are built
//! from the contract's own spec ([`TypeRegistry`]), so a struct argument has
//! exactly the fields the original contract declares.
//!
//! Everything is deterministic: the only randomness is an LCG seeded from the
//! function name, so a divergence reproduces on every run.

use soroban_ret::TypeRegistry;
use stellar_xdr::curr::{
    AccountId, ContractId, Duration, Hash, Int128Parts, Int256Parts, MuxedEd25519Account,
    PublicKey, ScAddress, ScBytes, ScError, ScMap, ScMapEntry, ScSpecTypeDef, ScSpecUdtUnionCaseV0,
    ScString, ScSymbol, ScVal, ScVec, TimePoint, UInt128Parts, UInt256Parts, Uint256,
};

/// Contract id both sides are registered at, so "the contract's own address"
/// is a valid argument and identical for the original and the recompiled side.
pub(crate) const SELF_CONTRACT_ID: [u8; 32] = [0xC0; 32];

/// Contract id of the first `Address` candidate. The harness registers a
/// callee contract there, so a cross-contract call has something to reach.
pub(crate) const CALLEE_CONTRACT_ID: [u8; 32] = [0xA1; 32];

/// Key of the account `Address` candidate.
pub(crate) const ACCOUNT_KEY: [u8; 32] = [0x11; 32];

/// User types nest at most this deep before the generator picks the smallest
/// terminating shape (`None`, an empty collection, a unit case).
const SHALLOW_DEPTH: usize = 2;
/// Hard stop: a type that still has not terminated here cannot be built.
const MAX_DEPTH: usize = 6;

/// Tiny deterministic LCG so fuzz inputs are reproducible without `rand`.
pub(crate) fn lcg(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    // The low bits of an LCG are weak; fold the high half in.
    *state ^ (*state >> 33)
}

pub(crate) fn u128_scval(v: u128) -> ScVal {
    ScVal::U128(UInt128Parts {
        hi: (v >> 64) as u64,
        lo: v as u64,
    })
}

pub(crate) fn i128_scval(v: i128) -> ScVal {
    ScVal::I128(Int128Parts {
        hi: (v >> 64) as i64,
        lo: v as u64,
    })
}

fn contract_address(id: [u8; 32]) -> ScVal {
    ScVal::Address(ScAddress::Contract(ContractId(Hash(id))))
}

fn account_address(key: [u8; 32]) -> ScVal {
    ScVal::Address(ScAddress::Account(AccountId(
        PublicKey::PublicKeyTypeEd25519(Uint256(key)),
    )))
}

fn symbol(s: &str) -> ScVal {
    ScVal::Symbol(ScSymbol(s.try_into().expect("symbol fits")))
}

fn sc_vec(items: Vec<ScVal>) -> ScVal {
    ScVal::Vec(Some(ScVec(items.try_into().expect("vec fits"))))
}

/// A map value with unique keys in ascending order, as the host requires.
fn sc_map(mut entries: Vec<(ScVal, ScVal)>) -> ScVal {
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    entries.dedup_by(|a, b| a.0 == b.0);
    let entries: Vec<ScMapEntry> = entries
        .into_iter()
        .map(|(key, val)| ScMapEntry { key, val })
        .collect();
    ScVal::Map(Some(ScMap(entries.try_into().expect("map fits"))))
}

/// Values that earlier calls stored, by type label. Offered first for later
/// parameters of the same type, so a getter is asked about a key that exists.
pub(crate) type Preferred = std::collections::BTreeMap<String, Vec<ScVal>>;

/// At most this many remembered values per type (keeps the case count flat).
const MAX_PREFERRED: usize = 3;

/// Record `value` (of spec type `td`) and the values nested in it: a stored
/// `Vec<String>` makes each of its strings a candidate for a later `String`
/// parameter.
pub(crate) fn remember(preferred: &mut Preferred, td: &ScSpecTypeDef, value: &ScVal) {
    use ScSpecTypeDef as T;
    let slot = preferred.entry(crate::type_label(td)).or_default();
    if slot.len() < MAX_PREFERRED && !slot.contains(value) {
        slot.push(value.clone());
    }
    match (td, value) {
        (T::Vec(v), ScVal::Vec(Some(items))) => {
            for item in items.iter() {
                remember(preferred, &v.element_type, item);
            }
        }
        (T::Tuple(t), ScVal::Vec(Some(items))) => {
            for (ty, item) in t.value_types.iter().zip(items.iter()) {
                remember(preferred, ty, item);
            }
        }
        (T::Map(m), ScVal::Map(Some(entries))) => {
            for e in entries.iter() {
                remember(preferred, &m.key_type, &e.key);
                remember(preferred, &m.value_type, &e.val);
            }
        }
        (T::Option(o), v) if *v != ScVal::Void => remember(preferred, &o.value_type, v),
        _ => {}
    }
}

/// Candidate values for spec types, seeded per function.
pub(crate) struct Generator<'a> {
    reg: &'a TypeRegistry,
    seed: u64,
    preferred: Preferred,
    extra_addresses: Vec<ScVal>,
}

impl<'a> Generator<'a> {
    pub(crate) fn new(reg: &'a TypeRegistry, seed: u64) -> Self {
        Generator {
            reg,
            seed,
            preferred: Preferred::new(),
            extra_addresses: Vec::new(),
        }
    }

    /// Offer `preferred` values first, and `extra_addresses` as additional
    /// `Address` candidates (contracts registered next to the one under test).
    pub(crate) fn with_context(mut self, preferred: &Preferred, extra_addresses: &[ScVal]) -> Self {
        self.preferred = preferred.clone();
        self.extra_addresses = extra_addresses.to_vec();
        self
    }

    fn next(&mut self) -> u64 {
        lcg(&mut self.seed)
    }

    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }

    /// Candidate values for one parameter of type `td`, or `None` when the
    /// type cannot be built (an unknown user type, a `Result`, a user type
    /// with no finite value).
    pub(crate) fn values(&mut self, td: &ScSpecTypeDef) -> Option<Vec<ScVal>> {
        let generated = self.values_at(td, 0)?;
        let Some(first) = self.preferred.get(&crate::type_label(td)) else {
            return Some(generated);
        };
        let mut out = first.clone();
        for v in generated {
            if !out.contains(&v) {
                out.push(v);
            }
        }
        Some(out)
    }

    fn values_at(&mut self, td: &ScSpecTypeDef, depth: usize) -> Option<Vec<ScVal>> {
        use ScSpecTypeDef as T;
        if depth > MAX_DEPTH {
            return None;
        }
        let shallow = depth >= SHALLOW_DEPTH;
        Some(match td {
            T::Bool => vec![ScVal::Bool(false), ScVal::Bool(true)],
            T::Void => vec![ScVal::Void],
            T::U32 => {
                let mut v = vec![0u32, 1, 2, u32::MAX];
                v.push(self.next() as u32);
                v.into_iter().map(ScVal::U32).collect()
            }
            T::I32 => {
                let mut v = vec![i32::MIN, -1, 0, 1, i32::MAX];
                v.push(self.next() as i32);
                v.into_iter().map(ScVal::I32).collect()
            }
            T::U64 => {
                let mut v = vec![0u64, 1, 2, u64::MAX];
                v.push(self.next());
                v.into_iter().map(ScVal::U64).collect()
            }
            T::I64 => {
                let mut v = vec![i64::MIN, -1, 0, 1, i64::MAX];
                v.push(self.next() as i64);
                v.into_iter().map(ScVal::I64).collect()
            }
            T::Timepoint => {
                let mut v = vec![0u64, 1, u64::MAX];
                v.push(self.next());
                v.into_iter()
                    .map(|t| ScVal::Timepoint(TimePoint(t)))
                    .collect()
            }
            T::Duration => {
                let mut v = vec![0u64, 1, u64::MAX];
                v.push(self.next());
                v.into_iter()
                    .map(|t| ScVal::Duration(Duration(t)))
                    .collect()
            }
            T::U128 => {
                let mut v = vec![0u128, 1, u128::MAX];
                v.push(((self.next() as u128) << 64) | self.next() as u128);
                v.into_iter().map(u128_scval).collect()
            }
            T::I128 => {
                let mut v = vec![i128::MIN, -1, 0, 1, i128::MAX];
                v.push((((self.next() as u128) << 64) | self.next() as u128) as i128);
                v.into_iter().map(i128_scval).collect()
            }
            T::U256 => {
                let u = |hi_hi, hi_lo, lo_hi, lo_lo| {
                    ScVal::U256(UInt256Parts {
                        hi_hi,
                        hi_lo,
                        lo_hi,
                        lo_lo,
                    })
                };
                vec![
                    u(0, 0, 0, 0),
                    u(0, 0, 0, 1),
                    u(u64::MAX, u64::MAX, u64::MAX, u64::MAX),
                    u(self.next(), self.next(), self.next(), self.next()),
                ]
            }
            T::I256 => {
                let i = |hi_hi, hi_lo, lo_hi, lo_lo| {
                    ScVal::I256(Int256Parts {
                        hi_hi,
                        hi_lo,
                        lo_hi,
                        lo_lo,
                    })
                };
                vec![
                    i(i64::MIN, 0, 0, 0),
                    i(-1, u64::MAX, u64::MAX, u64::MAX),
                    i(0, 0, 0, 0),
                    i(0, 0, 0, 1),
                    i(i64::MAX, u64::MAX, u64::MAX, u64::MAX),
                    i(self.next() as i64, self.next(), self.next(), self.next()),
                ]
            }
            T::Address => {
                // The account comes first: it is the candidate most likely to
                // end up as a stored admin, and mocked auth works for it. (A
                // contract address with code behind it cannot authorize.)
                let mut v = vec![
                    account_address(ACCOUNT_KEY),
                    contract_address(CALLEE_CONTRACT_ID),
                    contract_address([0xB2; 32]),
                    contract_address(SELF_CONTRACT_ID),
                ];
                v.extend(self.extra_addresses.iter().cloned());
                v
            }
            T::MuxedAddress => vec![
                account_address([0x11; 32]),
                ScVal::Address(ScAddress::MuxedAccount(MuxedEd25519Account {
                    id: 7,
                    ed25519: Uint256([0x22; 32]),
                })),
            ],
            T::Bytes => {
                let short = self.bytes(5);
                let long = self.bytes(40);
                [vec![], vec![0u8], short, long]
                    .into_iter()
                    .map(|b| ScVal::Bytes(ScBytes(b.try_into().expect("bytes fit"))))
                    .collect()
            }
            T::BytesN(b) => {
                let n = b.n as usize;
                let seeded = self.bytes(n);
                [vec![0u8; n], vec![0xff; n], seeded]
                    .into_iter()
                    .map(|b| ScVal::Bytes(ScBytes(b.try_into().expect("bytes fit"))))
                    .collect()
            }
            T::String => {
                let tag = self.next() % 1000;
                [
                    String::new(),
                    "a".to_string(),
                    format!("str{tag}"),
                    "a string that is longer than thirty-two bytes".to_string(),
                ]
                .into_iter()
                .map(|s| ScVal::String(ScString(s.as_str().try_into().expect("string fits"))))
                .collect()
            }
            T::Symbol => {
                let tag = self.next() % 1000;
                vec![
                    symbol(""),
                    symbol(&format!("sym{tag}")),
                    symbol("a_symbol_longer_than_nine_chars"),
                ]
            }
            T::Val => vec![ScVal::U32(7), ScVal::Void, symbol("val")],
            T::Error => vec![ScVal::Error(ScError::Contract(1))],
            T::Result(_) => return None,
            T::Option(o) => {
                let mut v = vec![ScVal::Void];
                if !shallow {
                    v.extend(self.values_at(&o.value_type, depth + 1)?);
                }
                v
            }
            T::Vec(v) => {
                let mut out = vec![sc_vec(vec![])];
                if !shallow {
                    let elems = self.values_at(&v.element_type, depth + 1)?;
                    if let Some(first) = elems.first() {
                        out.push(sc_vec(vec![first.clone()]));
                        let pick = self.next() as usize % elems.len();
                        out.push(sc_vec(vec![
                            first.clone(),
                            elems[elems.len() - 1].clone(),
                            elems[pick].clone(),
                        ]));
                    }
                }
                out
            }
            T::Map(m) => {
                let mut out = vec![sc_map(vec![])];
                if !shallow {
                    let keys = self.values_at(&m.key_type, depth + 1)?;
                    let vals = self.values_at(&m.value_type, depth + 1)?;
                    if let (Some(k0), Some(v0)) = (keys.first(), vals.first()) {
                        out.push(sc_map(vec![(k0.clone(), v0.clone())]));
                        let entries: Vec<(ScVal, ScVal)> = keys
                            .iter()
                            .take(3)
                            .enumerate()
                            .map(|(i, k)| (k.clone(), vals[(i + 1) % vals.len()].clone()))
                            .collect();
                        out.push(sc_map(entries));
                    }
                }
                out
            }
            T::Tuple(t) => {
                let per_elem: Vec<Vec<ScVal>> = t
                    .value_types
                    .iter()
                    .map(|e| self.values_at(e, depth + 1))
                    .collect::<Option<_>>()?;
                self.combine(&per_elem).into_iter().map(sc_vec).collect()
            }
            T::Udt(u) => {
                let name = u.name.to_utf8_string().ok()?;
                return self.udt_values(&name, depth);
            }
        })
    }

    /// A few rows over per-slot candidates: all first, all last, one seeded.
    /// An empty slot list gives the single empty row.
    fn combine(&mut self, per_slot: &[Vec<ScVal>]) -> Vec<Vec<ScVal>> {
        if per_slot.iter().any(|c| c.is_empty()) {
            return Vec::new();
        }
        let mut rows: Vec<Vec<ScVal>> = Vec::new();
        let first: Vec<ScVal> = per_slot.iter().map(|c| c[0].clone()).collect();
        let last: Vec<ScVal> = per_slot.iter().map(|c| c[c.len() - 1].clone()).collect();
        let seeded: Vec<ScVal> = per_slot
            .iter()
            .map(|c| c[self.next() as usize % c.len()].clone())
            .collect();
        for row in [first, last, seeded] {
            if !rows.contains(&row) {
                rows.push(row);
            }
        }
        rows
    }

    fn udt_values(&mut self, name: &str, depth: usize) -> Option<Vec<ScVal>> {
        let reg = self.reg;
        if let Some(s) = reg.structs.get(name) {
            let names: Vec<String> = s
                .fields
                .iter()
                .map(|f| f.name.to_utf8_string())
                .collect::<Result<_, _>>()
                .ok()?;
            let per_field: Vec<Vec<ScVal>> = s
                .fields
                .iter()
                .map(|f| self.values_at(&f.type_, depth + 1))
                .collect::<Option<_>>()?;
            // A tuple struct (`struct S(A, B)`) names its fields "0", "1", …
            // and is encoded as a vector; a named struct is a symbol-keyed map.
            let tuple_struct = !names.is_empty() && names.iter().all(|n| n.parse::<u32>().is_ok());
            let rows = self.combine(&per_field);
            return Some(
                rows.into_iter()
                    .map(|row| {
                        if tuple_struct {
                            sc_vec(row)
                        } else {
                            sc_map(names.iter().map(|n| symbol(n)).zip(row).collect())
                        }
                    })
                    .collect(),
            );
        }
        if let Some(u) = reg.unions.get(name) {
            let mut out = Vec::new();
            for case in u.cases.iter() {
                match case {
                    ScSpecUdtUnionCaseV0::VoidV0(c) => {
                        out.push(sc_vec(vec![symbol(&c.name.to_utf8_string().ok()?)]));
                    }
                    ScSpecUdtUnionCaseV0::TupleV0(c) => {
                        let tag = symbol(&c.name.to_utf8_string().ok()?);
                        // A payload that cannot be built (recursion ran out)
                        // drops this case, not the whole type.
                        let Some(per_elem) = c
                            .type_
                            .iter()
                            .map(|e| self.values_at(e, depth + 1))
                            .collect::<Option<Vec<_>>>()
                        else {
                            continue;
                        };
                        // Two payloads per case keeps unions small.
                        for row in self.combine(&per_elem).into_iter().take(2) {
                            let mut items = vec![tag.clone()];
                            items.extend(row);
                            out.push(sc_vec(items));
                        }
                    }
                }
            }
            return if out.is_empty() { None } else { Some(out) };
        }
        if let Some(e) = reg.enums.get(name) {
            let declared: Vec<u32> = e.cases.iter().map(|c| c.value).collect();
            let mut out: Vec<ScVal> = declared.iter().take(4).map(|v| ScVal::U32(*v)).collect();
            // One value the type does not declare: rejecting it is behaviour,
            // and a wrongly recovered definition shows up here.
            if let Some(bad) = (0..=u32::MAX).rev().find(|v| !declared.contains(v)) {
                out.push(ScVal::U32(bad));
            }
            return Some(out);
        }
        if let Some(e) = reg.error_enums.get(name) {
            let out: Vec<ScVal> = e
                .cases
                .iter()
                .take(4)
                .map(|c| ScVal::Error(ScError::Contract(c.value)))
                .collect();
            return if out.is_empty() { None } else { Some(out) };
        }
        None
    }
}

/// Input vectors for one function: the full product of the per-parameter
/// candidates when it fits in `cap`; otherwise a covering pass (every
/// candidate of every parameter appears at least once) topped up with seeded
/// rows. `seed` makes the selection stable per function.
pub(crate) fn select_cases(
    per_param: &[Vec<ScVal>],
    cap: usize,
    seed: &mut u64,
) -> Vec<Vec<ScVal>> {
    if per_param.iter().any(|c| c.is_empty()) || cap == 0 {
        return Vec::new();
    }
    let product = per_param
        .iter()
        .try_fold(1usize, |acc, c| acc.checked_mul(c.len()));
    if let Some(total) = product
        && total <= cap
    {
        let mut out: Vec<Vec<ScVal>> = vec![vec![]];
        for cand in per_param {
            out = out
                .iter()
                .flat_map(|prefix| {
                    cand.iter().map(move |v| {
                        let mut p = prefix.clone();
                        p.push(v.clone());
                        p
                    })
                })
                .collect();
        }
        return out;
    }

    let mut out: Vec<Vec<ScVal>> = Vec::new();
    let widest = per_param.iter().map(Vec::len).max().unwrap_or(0);
    // Covering pass: row `i` takes candidate `i` (wrapping) of every parameter.
    for i in 0..widest.min(cap) {
        out.push(per_param.iter().map(|c| c[i % c.len()].clone()).collect());
    }
    // Seeded rows; a bounded number of attempts so duplicates cannot spin.
    let mut attempts = cap * 8;
    while out.len() < cap && attempts > 0 {
        attempts -= 1;
        let row: Vec<ScVal> = per_param
            .iter()
            .map(|c| c[lcg(seed) as usize % c.len()].clone())
            .collect();
        if !out.contains(&row) {
            out.push(row);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use soroban_sdk::{Env, TryFromVal, Val};
    use std::path::PathBuf;

    fn fixture_and_corpus_wasms() -> Vec<PathBuf> {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../");
        let mut out = Vec::new();
        for dir in ["tests/fixtures", "benchmark-data/mainnet"] {
            let Ok(entries) = std::fs::read_dir(root.join(dir)) else {
                continue;
            };
            for e in entries.flatten() {
                if e.path().extension().is_some_and(|x| x == "wasm") {
                    out.push(e.path());
                }
            }
        }
        out.sort();
        out
    }

    /// The registry of a contract that declares no user types.
    fn plain_registry() -> TypeRegistry {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/test_add_u64.wasm");
        TypeRegistry::from_wasm(&std::fs::read(path).unwrap()).unwrap()
    }

    /// Every candidate the generator produces for every parameter of every
    /// function in the fixtures and the corpus is a value the host accepts
    /// (sorted maps, symbols within length, well-formed addresses).
    #[test]
    fn every_generated_value_converts_in_a_real_env() {
        let env = Env::default();
        let mut params = 0usize;
        let mut unbuildable: Vec<String> = Vec::new();
        for path in fixture_and_corpus_wasms() {
            let wasm = std::fs::read(&path).unwrap();
            let Ok(registry) = TypeRegistry::from_wasm(&wasm) else {
                continue;
            };
            for (name, f) in &registry.functions {
                let mut g = Generator::new(&registry, 1);
                for input in f.inputs.iter() {
                    params += 1;
                    let Some(values) = g.values(&input.type_) else {
                        // `__check_auth` takes SDK types the contract's spec
                        // does not define; it is not directly callable anyway.
                        if name.starts_with("__") {
                            continue;
                        }
                        unbuildable.push(format!(
                            "{}::{name}: {}",
                            path.file_stem().unwrap().to_string_lossy(),
                            crate::type_label(&input.type_)
                        ));
                        continue;
                    };
                    assert!(!values.is_empty(), "{name}: empty candidate list");
                    for v in &values {
                        assert!(
                            Val::try_from_val(&env, v).is_ok(),
                            "{}::{name}: host rejects generated {} value {v:?}",
                            path.display(),
                            crate::type_label(&input.type_)
                        );
                    }
                }
            }
        }
        assert!(
            params > 500,
            "fixtures and corpus not found ({params} params)"
        );
        assert!(
            unbuildable.is_empty(),
            "parameter types with no generated value: {unbuildable:#?}"
        );
    }

    /// A remembered value, and the values nested in it, come first for a
    /// later parameter of the same type.
    #[test]
    fn remembered_values_are_offered_first() {
        let reg = plain_registry();
        let strings = ScSpecTypeDef::Vec(Box::new(stellar_xdr::curr::ScSpecTypeVec {
            element_type: Box::new(ScSpecTypeDef::String),
        }));
        let stored = ScVal::String(ScString("stored-repo".try_into().unwrap()));
        let mut preferred = Preferred::new();
        remember(&mut preferred, &strings, &sc_vec(vec![stored.clone()]));
        let values = Generator::new(&reg, 1)
            .with_context(&preferred, &[])
            .values(&ScSpecTypeDef::String)
            .expect("strings generate");
        assert_eq!(values[0], stored);
        assert_eq!(
            values.iter().filter(|v| **v == stored).count(),
            1,
            "offered once"
        );
    }

    #[test]
    fn generation_is_deterministic_per_seed() {
        let reg = plain_registry();
        let td = ScSpecTypeDef::Vec(Box::new(stellar_xdr::curr::ScSpecTypeVec {
            element_type: Box::new(ScSpecTypeDef::U256),
        }));
        let a = Generator::new(&reg, 42).values(&td);
        let b = Generator::new(&reg, 42).values(&td);
        let c = Generator::new(&reg, 43).values(&td);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn unknown_user_type_and_result_are_not_generated() {
        let reg = plain_registry();
        let udt = ScSpecTypeDef::Udt(stellar_xdr::curr::ScSpecTypeUdt {
            name: "Missing".try_into().unwrap(),
        });
        assert_eq!(Generator::new(&reg, 1).values(&udt), None);
        // An aggregate of an unbuildable type is unbuildable too.
        let vec_of = ScSpecTypeDef::Vec(Box::new(stellar_xdr::curr::ScSpecTypeVec {
            element_type: Box::new(udt),
        }));
        assert_eq!(Generator::new(&reg, 1).values(&vec_of), None);
    }

    #[test]
    fn maps_are_sorted_with_unique_keys() {
        let v = sc_map(vec![
            (ScVal::U32(3), ScVal::Void),
            (ScVal::U32(1), ScVal::Void),
            (ScVal::U32(3), ScVal::Bool(true)),
        ]);
        let ScVal::Map(Some(m)) = v else { panic!() };
        let keys: Vec<ScVal> = m.iter().map(|e| e.key.clone()).collect();
        assert_eq!(keys, vec![ScVal::U32(1), ScVal::U32(3)]);
    }

    fn u32s(n: u32) -> Vec<ScVal> {
        (0..n).map(ScVal::U32).collect()
    }

    #[test]
    fn small_products_are_enumerated_in_full() {
        let mut seed = 7;
        let cases = select_cases(&[u32s(3), u32s(4)], 48, &mut seed);
        assert_eq!(cases.len(), 12);
        let mut unique = cases.clone();
        unique.sort();
        unique.dedup();
        assert_eq!(unique.len(), 12);
        // No parameters: exactly one empty input vector.
        assert_eq!(select_cases(&[], 48, &mut seed), vec![Vec::<ScVal>::new()]);
    }

    #[test]
    fn large_products_cover_every_candidate_within_the_cap() {
        let per_param = vec![u32s(6), u32s(5), u32s(6), u32s(4)];
        let mut seed = 7;
        let cases = select_cases(&per_param, 48, &mut seed);
        assert_eq!(cases.len(), 48);
        for (i, cands) in per_param.iter().enumerate() {
            for c in cands {
                assert!(
                    cases.iter().any(|row| &row[i] == c),
                    "candidate {c:?} of parameter {i} never used"
                );
            }
        }
        let mut seed2 = 7;
        assert_eq!(cases, select_cases(&per_param, 48, &mut seed2));
    }
}
