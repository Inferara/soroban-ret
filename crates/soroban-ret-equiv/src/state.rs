//! Ledger states for the equivalence harness.
//!
//! A call on a freshly registered contract mostly compares "not initialised".
//! To compare real behaviour the harness needs the contract in a state it
//! actually reaches, on **both** sides, and identical on both sides.
//!
//! The state is always built by the *original* contract. Its ledger is then
//! snapshotted and, for the recompiled side, the contract instance is
//! repointed at the recompiled code ([`World::with_code`]). Both sides are
//! registered at the same address, so every storage key is the same. The
//! consequences:
//!
//! - a hole or a bug in a recompiled *setter* cannot stop its *getters* from
//!   being compared against real data;
//! - a recompiled contract that decodes stored data differently from the
//!   original is a visible divergence.

use soroban_sdk::testutils::{EnvTestConfig, Snapshot};
use soroban_sdk::xdr::{
    ContractEvent, ContractEventType, ContractExecutable, ContractId, Hash, LedgerEntry,
    LedgerEntryData, LedgerKey, ScAddress, ScVal, SorobanAuthorizedInvocation,
};
use soroban_sdk::{Address, Env, Symbol, TryFromVal, Val, Vec as SVec};

use crate::args::SELF_CONTRACT_ID;
use crate::{AuthMode, Outcome};

/// A test [`Env`] that does NOT write a snapshot JSON on drop (the harness
/// creates many envs; the default would litter `test_snapshots/`).
pub(crate) fn fresh_env() -> Env {
    Env::new_with_config(EnvTestConfig {
        capture_snapshot_at_drop: false,
    })
}

fn address(env: &Env, id: [u8; 32]) -> Address {
    let sc = ScVal::Address(ScAddress::Contract(ContractId(Hash(id))));
    Address::try_from_val(env, &sc).expect("fixed contract address converts")
}

/// A contract registered next to the one under test, so that an `Address`
/// argument can point at something callable.
pub(crate) struct Callee<'a> {
    pub id: [u8; 32],
    pub wasm: &'a [u8],
}

/// A ledger with the contract under test registered at [`SELF_CONTRACT_ID`].
#[derive(Clone)]
pub(crate) struct World {
    snapshot: Snapshot,
}

/// One ledger entry as an effect: key, entry, and the ledger its lifetime
/// runs to.
type Entry = (LedgerKey, LedgerEntry, Option<u32>);

/// Everything a call that returned did besides returning: what the two sides
/// must agree on for a case to match.
#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct Effects {
    /// Contract events published by the call and its sub-calls, in order.
    pub events: Vec<ContractEvent>,
    /// The ledger after the call (see [`World::ledger`]), sorted by key.
    pub ledger: Vec<Entry>,
    /// Who authorized what (recorded under mocked auth; empty otherwise).
    pub auths: Vec<(ScAddress, SorobanAuthorizedInvocation)>,
    /// The call added, removed or changed a ledger entry.
    pub wrote: bool,
    /// The call changed the lifetime of an entry it did not otherwise change.
    pub extended: bool,
}

/// Which part of two [`Effects`] differs, with the first differing item
/// from each side.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct EffectDifference {
    /// `events`, `storage`, `lifetime` or `auth`.
    pub part: &'static str,
    pub left: String,
    pub right: String,
}

fn shown<T: std::fmt::Debug>(item: Option<&T>) -> String {
    match item {
        Some(v) => format!("{v:?}"),
        None => "nothing".to_string(),
    }
}

/// First position where two lists differ, shown from both sides.
fn first_difference<T: PartialEq + std::fmt::Debug>(a: &[T], b: &[T]) -> Option<(String, String)> {
    let n = a.len().max(b.len());
    (0..n)
        .find(|&i| a.get(i) != b.get(i))
        .map(|i| (shown(a.get(i)), shown(b.get(i))))
}

impl Effects {
    /// `None` when the two calls did the same thing.
    pub(crate) fn difference(&self, other: &Effects) -> Option<EffectDifference> {
        if let Some((left, right)) = first_difference(&self.events, &other.events) {
            return Some(EffectDifference {
                part: "events",
                left,
                right,
            });
        }
        // Contents first: a wrong value is reported as `storage` even when
        // its lifetime differs too.
        let contents = |e: &[Entry]| -> Vec<(LedgerKey, LedgerEntry)> {
            e.iter().map(|(k, v, _)| (k.clone(), v.clone())).collect()
        };
        if let Some((left, right)) =
            first_difference(&contents(&self.ledger), &contents(&other.ledger))
        {
            return Some(EffectDifference {
                part: "storage",
                left,
                right,
            });
        }
        let lifetimes = |e: &[Entry]| -> Vec<(LedgerKey, Option<u32>)> {
            e.iter().map(|(k, _, l)| (k.clone(), *l)).collect()
        };
        if let Some((left, right)) =
            first_difference(&lifetimes(&self.ledger), &lifetimes(&other.ledger))
        {
            return Some(EffectDifference {
                part: "lifetime",
                left,
                right,
            });
        }
        first_difference(&self.auths, &other.auths).map(|(left, right)| EffectDifference {
            part: "auth",
            left,
            right,
        })
    }
}

/// The result of [`World::run`].
pub(crate) struct Run {
    pub outcome: Outcome,
    /// What the call did, when it returned a value. A failed call is rolled
    /// back by the host, so it has no effects to compare.
    pub effects: Option<Effects>,
    /// The world after the call, when it returned a value.
    pub after: Option<World>,
}

impl Run {
    fn failed(outcome: Outcome) -> Run {
        Run {
            outcome,
            effects: None,
            after: None,
        }
    }
}

impl World {
    /// Register `wasm` (with `ctor_args`) and the `callees` in an empty
    /// ledger. `None` when registration fails: a constructor that rejects the
    /// arguments, or one that needs arguments that were not given.
    pub(crate) fn new(wasm: &[u8], ctor_args: &[ScVal], callees: &[Callee<'_>]) -> Option<World> {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let env = fresh_env();
            for c in callees {
                env.register_at(&address(&env, c.id), c.wasm, ());
            }
            let mut args: SVec<Val> = SVec::new(&env);
            for sc in ctor_args {
                args.push_back(Val::try_from_val(&env, sc).ok()?);
            }
            env.register_at(&address(&env, SELF_CONTRACT_ID), wasm, args);
            Some(World {
                snapshot: env.to_snapshot(),
            })
        }))
        .ok()
        .flatten()
    }

    fn env(&self) -> Env {
        let mut env = Env::from_snapshot(self.snapshot.clone());
        env.set_config(EnvTestConfig {
            capture_snapshot_at_drop: false,
        });
        env
    }

    /// The same ledger with the contract under test running `wasm` instead:
    /// its instance entry (and therefore its instance storage) is kept, only
    /// the executable is replaced. `None` if `wasm` cannot be installed.
    pub(crate) fn with_code(&self, wasm: &[u8]) -> Option<World> {
        // Install `wasm` in a scratch ledger to get its code entry.
        let scratch = World::new_unconstructed(wasm)?;
        let (code_key, code_entry) = scratch
            .snapshot
            .ledger
            .ledger_entries
            .iter()
            .find(|(k, _)| matches!(**k, LedgerKey::ContractCode(_)))
            .cloned()?;
        let LedgerKey::ContractCode(code) = &*code_key else {
            return None;
        };
        let new_hash = code.hash.clone();

        let mut out = self.clone();
        let entries = &mut out.snapshot.ledger.ledger_entries;
        let mut repointed = false;
        for (key, (entry, _)) in entries.iter_mut() {
            if !is_self_instance_key(key) {
                continue;
            }
            if let LedgerEntryData::ContractData(data) = &mut entry.data
                && let ScVal::ContractInstance(instance) = &mut data.val
            {
                instance.executable = ContractExecutable::Wasm(new_hash.clone());
                repointed = true;
            }
        }
        if !repointed {
            return None;
        }
        if !entries.iter().any(|(k, _)| **k == *code_key) {
            entries.push((code_key, code_entry));
        }
        Some(out)
    }

    /// `wasm` uploaded and instantiated WITHOUT running its constructor, only
    /// to obtain its code entry.
    fn new_unconstructed(wasm: &[u8]) -> Option<World> {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let env = fresh_env();
            env.deployer().upload_contract_wasm(wasm);
            World {
                snapshot: env.to_snapshot(),
            }
        }))
        .ok()
    }

    /// [`World::run`] without the effects: the outcome and, when the call
    /// returned normally, the world after it.
    pub(crate) fn call(
        &self,
        func: &str,
        inputs: &[ScVal],
        auth: AuthMode,
    ) -> (Outcome, Option<World>) {
        let run = self.run(func, inputs, auth);
        (run.outcome, run.after)
    }

    /// Invoke `func` in this world.
    ///
    /// Everything runs inside one `catch_unwind`, env drop included, so a
    /// host panic (budget exceeded, trap escalation) becomes
    /// [`Outcome::Panic`] instead of aborting the run.
    pub(crate) fn run(&self, func: &str, inputs: &[ScVal], auth: AuthMode) -> Run {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let env = self.env();
            let addr = address(&env, SELF_CONTRACT_ID);
            if auth == AuthMode::Mocked {
                env.mock_all_auths_allowing_non_root_auth();
            }
            let mut args = SVec::new(&env);
            for sc in inputs {
                match Val::try_from_val(&env, sc) {
                    Ok(v) => args.push_back(v),
                    Err(_) => return Run::failed(Outcome::Unconvertible),
                }
            }
            let sym = Symbol::new(&env, func);
            // `try_invoke_contract::<Val, _>` returns
            // `Result<Result<Val, _>, Result<Error, InvokeError>>`. The OUTER
            // result discriminates "the returned `Val` was an error" (`Err`)
            // from "was a normal value" (`Ok`): a contract-returned Soroban
            // error is `Err(Ok(e))`, NOT `Ok(Err(..))`.
            match env.try_invoke_contract::<Val, soroban_sdk::Error>(&addr, &sym, args) {
                Ok(Ok(v)) => match ScVal::try_from_val(&env, &v) {
                    Ok(sc) => {
                        let mut snapshot = env.to_snapshot();
                        // Consumed auth nonces are per-invocation bookkeeping,
                        // not contract state. Every env restarts the same
                        // nonce sequence, so a kept nonce would make the next
                        // authorized call in this world fail as a replay.
                        snapshot.ledger.ledger_entries.retain(|(key, _)| {
                            !matches!(&**key, LedgerKey::ContractData(d)
                                if matches!(d.key, ScVal::LedgerKeyNonce(_)))
                        });
                        let events = snapshot
                            .events
                            .0
                            .iter()
                            .filter(|e| {
                                !e.failed_call && e.event.type_ == ContractEventType::Contract
                            })
                            .map(|e| e.event.clone())
                            .collect();
                        let auths = snapshot.auth.0.last().cloned().unwrap_or_default();
                        // The next call in this world starts its own record.
                        snapshot.events.0.clear();
                        snapshot.auth.0.clear();
                        let after = World { snapshot };
                        let code = self.code();
                        let before = self.ledger(code.as_ref());
                        let ledger = after.ledger(code.as_ref());
                        let contents = |e: &[Entry]| -> Vec<(LedgerKey, LedgerEntry)> {
                            e.iter().map(|(k, v, _)| (k.clone(), v.clone())).collect()
                        };
                        let wrote = contents(&before) != contents(&ledger);
                        let extended = !wrote && before != ledger;
                        Run {
                            outcome: Outcome::Value(sc),
                            effects: Some(Effects {
                                events,
                                ledger,
                                auths,
                                wrote,
                                extended,
                            }),
                            after: Some(after),
                        }
                    }
                    Err(_) => Run::failed(Outcome::Unconvertible),
                },
                // Unreachable for `T = Val` (the conversion is infallible);
                // kept for exhaustiveness. NOT a contract-error path.
                Ok(Err(_conv)) => Run::failed(Outcome::Unconvertible),
                // The error value is kept in the string, so two *different*
                // contract errors compare unequal.
                Err(Ok(e)) => Run::failed(Outcome::ContractError(format!("{e:?}"))),
                Err(Err(ie)) => Run::failed(Outcome::InvokeError(format!("{ie:?}"))),
            }
        }))
        .unwrap_or_else(|_| Run::failed(Outcome::Panic))
    }

    /// The code the contract under test runs in this world.
    fn code(&self) -> Option<Hash> {
        self.snapshot
            .ledger
            .ledger_entries
            .iter()
            .find(|(k, _)| is_self_instance_key(k))
            .and_then(|(_, (entry, _))| match &entry.data {
                LedgerEntryData::ContractData(data) => match &data.val {
                    ScVal::ContractInstance(instance) => match &instance.executable {
                        ContractExecutable::Wasm(hash) => Some(hash.clone()),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            })
    }

    /// The ledger as an effect, lifetimes included, in a form that is equal
    /// for two worlds that differ only in which code is under test: code
    /// entries are left out, and where the contract under test still runs
    /// `code` its executable is replaced by a fixed marker. Anything the
    /// contract itself changed, its own executable included, is kept.
    fn ledger(&self, code: Option<&Hash>) -> Vec<Entry> {
        let mut v: Vec<Entry> = self
            .snapshot
            .ledger
            .ledger_entries
            .iter()
            .filter(|(k, _)| !matches!(**k, LedgerKey::ContractCode(_)))
            .map(|(k, (e, live_until))| {
                let mut entry = (**e).clone();
                if is_self_instance_key(k)
                    && let LedgerEntryData::ContractData(data) = &mut entry.data
                    && let ScVal::ContractInstance(instance) = &mut data.val
                    && let ContractExecutable::Wasm(hash) = &instance.executable
                    && Some(hash) == code
                {
                    instance.executable = ContractExecutable::Wasm(Hash([0; 32]));
                }
                ((**k).clone(), entry, *live_until)
            })
            .collect();
        v.sort();
        v
    }

    /// The ledger entries, for telling whether a call changed anything.
    /// Lifetimes (`live_until`) are left out: a read that only bumps a TTL
    /// has not built new state.
    pub(crate) fn entries(&self) -> Vec<(LedgerKey, LedgerEntry)> {
        let mut v: Vec<(LedgerKey, LedgerEntry)> = self
            .snapshot
            .ledger
            .ledger_entries
            .iter()
            .map(|(k, (e, _))| ((**k).clone(), (**e).clone()))
            .collect();
        v.sort();
        v
    }

    /// How many ledger entries differ between `self` and `other` (added,
    /// removed or changed).
    pub(crate) fn entries_changed(&self, other: &World) -> usize {
        let a = self.entries();
        let b = other.entries();
        let only_a = a.iter().filter(|e| !b.contains(e)).count();
        let only_b = b.iter().filter(|e| !a.contains(e)).count();
        only_a.max(only_b)
    }
}

fn is_self_instance_key(key: &LedgerKey) -> bool {
    matches!(
        key,
        LedgerKey::ContractData(d)
            if d.contract == ScAddress::Contract(ContractId(Hash(SELF_CONTRACT_ID)))
                && d.key == ScVal::LedgerKeyContractInstance
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use soroban_sdk::xdr::ScSymbol;

    fn fixture(name: &str) -> Vec<u8> {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures")
            .join(name);
        std::fs::read(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
    }

    fn sym(s: &str) -> ScVal {
        ScVal::Symbol(ScSymbol(s.try_into().unwrap()))
    }

    /// State written by one copy of a contract is read by another copy put in
    /// its place: the transplant the whole harness relies on.
    #[test]
    fn state_survives_a_code_swap() {
        let wasm = fixture("test_contract_data.wasm");
        let empty = World::new(&wasm, &[], &[]).expect("registers");
        let (out, after) = empty.call("put", &[sym("k"), sym("v")], AuthMode::Enforced);
        assert_eq!(out, Outcome::Value(ScVal::Void));
        let after = after.expect("put returns");
        assert!(empty.entries_changed(&after) >= 1, "put stores an entry");

        // Swap in different code (another contract entirely): the state stays,
        // the behaviour is the new code's.
        let other = fixture("test_add_u64.wasm");
        let swapped = after.with_code(&other).expect("repoints");
        let (out, _) = swapped.call("add", &[ScVal::U64(2), ScVal::U64(3)], AuthMode::Enforced);
        assert_eq!(out, Outcome::Value(ScVal::U64(5)));

        // Swap the original code back in: it reads what it wrote.
        let back = swapped.with_code(&wasm).expect("repoints back");
        let (out, _) = back.call("get", &[sym("k")], AuthMode::Enforced);
        assert_eq!(out, Outcome::Value(sym("v")));
        // The empty world still has nothing under that key.
        let (out, _) = empty.call("get", &[sym("k")], AuthMode::Enforced);
        assert_eq!(out, Outcome::Value(ScVal::Void));
    }

    /// A second authorized call in a world built by an authorized call must
    /// not fail as a nonce replay.
    #[test]
    fn authorized_calls_chain_across_worlds() {
        let wasm = std::fs::read(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../benchmark-data/mainnet/digicus-CCZLARB4.wasm"),
        )
        .expect("read digicus");
        let admin = ScVal::Address(ScAddress::Account(soroban_sdk::xdr::AccountId(
            soroban_sdk::xdr::PublicKey::PublicKeyTypeEd25519(soroban_sdk::xdr::Uint256(
                crate::args::ACCOUNT_KEY,
            )),
        )));
        let config = ScVal::Map(Some(soroban_sdk::xdr::ScMap(
            vec![
                soroban_sdk::xdr::ScMapEntry {
                    key: sym("admin"),
                    val: admin,
                },
                soroban_sdk::xdr::ScMapEntry {
                    key: sym("repos"),
                    val: ScVal::Vec(Some(soroban_sdk::xdr::ScVec(vec![].try_into().unwrap()))),
                },
            ]
            .try_into()
            .unwrap(),
        )));
        let empty = World::new(&wasm, &[], &[]).expect("registers");
        let (out, configured) = empty.call("config", &[config], AuthMode::Mocked);
        assert_eq!(out, Outcome::Value(ScVal::Void));
        let (out, _) =
            configured
                .expect("config returns")
                .call("clear_repos", &[], AuthMode::Mocked);
        assert_eq!(
            out,
            Outcome::Value(ScVal::Void),
            "admin auth is mocked again"
        );
    }

    fn account() -> ScVal {
        ScVal::Address(ScAddress::Account(soroban_sdk::xdr::AccountId(
            soroban_sdk::xdr::PublicKey::PublicKeyTypeEd25519(soroban_sdk::xdr::Uint256(
                crate::args::ACCOUNT_KEY,
            )),
        )))
    }

    fn effects(world: &World, func: &str, inputs: &[ScVal], auth: AuthMode) -> Effects {
        let run = world.run(func, inputs, auth);
        assert!(
            matches!(run.outcome, Outcome::Value(_)),
            "{func} returns: {:?}",
            run.outcome
        );
        run.effects.expect("a returning call has effects")
    }

    /// A write is an effect, a different written value is a `storage`
    /// difference, and a read has no effect.
    #[test]
    fn a_write_is_an_effect_and_a_read_is_not() {
        let wasm = fixture("test_contract_data.wasm");
        let empty = World::new(&wasm, &[], &[]).expect("registers");
        let v1 = effects(&empty, "put", &[sym("k"), sym("v")], AuthMode::Enforced);
        let v2 = effects(&empty, "put", &[sym("k"), sym("w")], AuthMode::Enforced);
        assert!(v1.wrote && !v1.extended);
        assert_eq!(v1.difference(&v1.clone()), None);
        let diff = v1.difference(&v2).expect("different values differ");
        assert_eq!(diff.part, "storage");
        assert!(
            diff.left.contains("StringM(v)") && diff.right.contains("StringM(w)"),
            "{diff:?}"
        );

        let read = effects(&empty, "get", &[sym("k")], AuthMode::Enforced);
        assert!(!read.wrote && !read.extended);
        assert!(read.events.is_empty() && read.auths.is_empty());
        // A missing write is a difference too.
        assert_eq!(v1.difference(&read).expect("differs").part, "storage");
    }

    /// Putting a second copy of the same code in place changes nothing a
    /// comparison can see: the normalisation hides the swap and only that.
    #[test]
    fn a_code_swap_is_not_an_effect() {
        let wasm = fixture("test_contract_data.wasm");
        let other = fixture("test_add_u64.wasm");
        let empty = World::new(&wasm, &[], &[]).expect("registers");
        // Through another contract's code and back: the ledger now carries an
        // extra code entry, as the recompiled side's does.
        let swapped = empty
            .with_code(&other)
            .and_then(|w| w.with_code(&wasm))
            .expect("repoints");
        for (func, inputs) in [("put", vec![sym("k"), sym("v")]), ("get", vec![sym("k")])] {
            let a = effects(&empty, func, &inputs, AuthMode::Enforced);
            let b = effects(&swapped, func, &inputs, AuthMode::Enforced);
            assert_eq!(a.difference(&b), None, "{func}");
            assert_eq!(a.wrote, b.wrote, "{func}");
        }
    }

    #[test]
    fn a_published_event_is_an_effect() {
        let wasm = fixture("test_events.wasm");
        let world = World::new(&wasm, &[], &[]).expect("registers");
        let transfer = |amount: i128| {
            let amount = ScVal::I128(soroban_sdk::xdr::Int128Parts {
                hi: 0,
                lo: amount as u64,
            });
            effects(
                &world,
                "transfer",
                &[account(), account(), amount],
                AuthMode::Enforced,
            )
        };
        let a = transfer(5);
        assert_eq!(a.events.len(), 1, "{:?}", a.events);
        assert!(!a.wrote);
        assert_eq!(a.difference(&transfer(5)), None, "deterministic");
        assert_eq!(a.difference(&transfer(6)).expect("differs").part, "events");
    }

    #[test]
    fn a_recorded_authorization_is_an_effect() {
        let wasm = fixture("test_auth.wasm");
        let world = World::new(&wasm, &[], &[]).expect("registers");
        let a = effects(&world, "fn1", &[account()], AuthMode::Mocked);
        assert_eq!(a.auths.len(), 1, "{:?}", a.auths);
        assert_eq!(ScVal::Address(a.auths[0].0.clone()), account());
        assert!(!a.wrote, "a consumed nonce is not a write");
        let again = effects(&world, "fn1", &[account()], AuthMode::Mocked);
        assert_eq!(a.difference(&again), None, "deterministic");

        let mut other = again;
        other.auths.clear();
        assert_eq!(a.difference(&other).expect("differs").part, "auth");
    }

    /// The same contents with a different lifetime are a `lifetime`
    /// difference, not a `storage` one.
    #[test]
    fn a_lifetime_is_compared_separately_from_contents() {
        let wasm = fixture("test_contract_data.wasm");
        let empty = World::new(&wasm, &[], &[]).expect("registers");
        let a = effects(&empty, "put", &[sym("k"), sym("v")], AuthMode::Enforced);
        let mut b = a.clone();
        let entry = b
            .ledger
            .iter_mut()
            .find(|(_, _, live_until)| live_until.is_some())
            .expect("an entry with a lifetime");
        entry.2 = entry.2.map(|l| l + 1);
        assert_eq!(a.difference(&b).expect("differs").part, "lifetime");
    }

    #[test]
    fn a_read_does_not_change_the_state() {
        let wasm = fixture("test_contract_data.wasm");
        let empty = World::new(&wasm, &[], &[]).expect("registers");
        let (_, after) = empty.call("get", &[sym("k")], AuthMode::Enforced);
        assert_eq!(empty.entries_changed(&after.expect("get returns")), 0);
    }

    #[test]
    fn a_constructor_that_needs_arguments_fails_without_them() {
        let wasm = fixture("test_constructor.wasm");
        assert!(World::new(&wasm, &[], &[]).is_none());
        let with_args = World::new(&wasm, &[ScVal::U32(7), ScVal::I64(-3)], &[]);
        assert!(with_args.is_some(), "registers with constructor arguments");
    }
}
