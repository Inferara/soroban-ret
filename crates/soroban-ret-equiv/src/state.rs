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
    ContractExecutable, ContractId, Hash, LedgerEntry, LedgerEntryData, LedgerKey, ScAddress, ScVal,
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

    /// Invoke `func` in this world. Returns the outcome and, when the call
    /// returned normally, the world after it.
    ///
    /// Everything runs inside one `catch_unwind`, env drop included, so a
    /// host panic (budget exceeded, trap escalation) becomes
    /// [`Outcome::Panic`] instead of aborting the run.
    pub(crate) fn call(
        &self,
        func: &str,
        inputs: &[ScVal],
        auth: AuthMode,
    ) -> (Outcome, Option<World>) {
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
                    Err(_) => return (Outcome::Unconvertible, None),
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
                        (Outcome::Value(sc), Some(World { snapshot }))
                    }
                    Err(_) => (Outcome::Unconvertible, None),
                },
                // Unreachable for `T = Val` (the conversion is infallible);
                // kept for exhaustiveness. NOT a contract-error path.
                Ok(Err(_conv)) => (Outcome::Unconvertible, None),
                // The error value is kept in the string, so two *different*
                // contract errors compare unequal.
                Err(Ok(e)) => (Outcome::ContractError(format!("{e:?}")), None),
                Err(Err(ie)) => (Outcome::InvokeError(format!("{ie:?}")), None),
            }
        }))
        .unwrap_or((Outcome::Panic, None))
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
