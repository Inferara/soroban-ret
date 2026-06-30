/// Host function call resolution.
///
/// Maps import calls in WASM instructions to Soroban SDK operations,
/// producing SorobanExpr nodes.
use crate::ir::soroban_ir::{SorobanExpr, StorageType};
use crate::wasm::imports::{HostFunction, HostModule};

/// Lift a host function call into a SorobanExpr.
///
/// Given a resolved host function and its arguments (as already-lifted expressions),
/// produce the equivalent Soroban SDK expression.
pub fn lift_host_call(func: &HostFunction, args: Vec<SorobanExpr>) -> SorobanExpr {
    match func.module {
        HostModule::Ledger => lift_ledger_call(&func.name, args),
        HostModule::Address => lift_address_call(&func.name, args),
        HostModule::Context => lift_context_call(&func.name, args),
        HostModule::Crypto => lift_crypto_call(&func.name, args),
        HostModule::Call => lift_contract_call(&func.name, args),
        HostModule::Int => lift_int_call(&func.name, args),
        HostModule::Prng => lift_prng_call(&func.name, args),
        HostModule::Map => lift_map_call(&func.name, args),
        HostModule::Vec => lift_vec_call(&func.name, args),
        HostModule::Buf => lift_buf_call(&func.name, args),
        _ => SorobanExpr::RawHostCall {
            module: format!("{:?}", func.module),
            function: func.name.clone(),
            args,
        },
    }
}

fn lift_ledger_call(name: &str, mut args: Vec<SorobanExpr>) -> SorobanExpr {
    match name {
        "put_contract_data" => {
            // put_contract_data(key, val, storage_type)
            let storage_type = extract_storage_type(args.pop());
            let value = args.pop().unwrap_or(SorobanExpr::Void);
            let key = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::StorageSet {
                storage_type,
                key: Box::new(key),
                value: Box::new(value),
            }
        }
        "get_contract_data" => {
            let storage_type = extract_storage_type(args.pop());
            let key = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::StorageGet {
                storage_type,
                key: Box::new(key),
                unwrap: true,
                on_missing: None,
            }
        }
        "has_contract_data" => {
            let storage_type = extract_storage_type(args.pop());
            let key = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::StorageHas {
                storage_type,
                key: Box::new(key),
            }
        }
        "del_contract_data" => {
            let storage_type = extract_storage_type(args.pop());
            let key = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::StorageRemove {
                storage_type,
                key: Box::new(key),
            }
        }
        "extend_contract_data_ttl" => {
            let extend_to = args.pop().unwrap_or(SorobanExpr::Void);
            let threshold = args.pop().unwrap_or(SorobanExpr::Void);
            let storage_type = extract_storage_type(args.pop());
            let key = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::StorageExtendTtl {
                storage_type,
                key: Box::new(key),
                threshold: Box::new(threshold),
                extend_to: Box::new(extend_to),
            }
        }
        "extend_current_contract_instance_and_code_ttl" => {
            let extend_to = args.pop().unwrap_or(SorobanExpr::Void);
            let threshold = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::ExtendInstanceAndCodeTtl {
                threshold: Box::new(threshold),
                extend_to: Box::new(extend_to),
            }
        }
        // The host's `update_current_contract_wasm` is exposed publicly on the
        // `Deployer`, not the `Ledger` — `env.deployer().update_current_contract_wasm(hash)`
        // (soroban-sdk `deploy.rs`). Without this it fell through to the RawHostCall
        // fallback and rendered `env.ledger().update_current_contract_wasm(..)`,
        // which has no such method (E0599).
        "update_current_contract_wasm" => {
            let hash = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(SorobanExpr::MethodCall {
                    object: Box::new(SorobanExpr::Env),
                    method: "deployer".to_string(),
                    args: vec![],
                }),
                method: "update_current_contract_wasm".to_string(),
                args: vec![hash],
            }
        }
        _ => SorobanExpr::RawHostCall {
            module: "Ledger".to_string(),
            function: name.to_string(),
            args,
        },
    }
}

fn lift_address_call(name: &str, mut args: Vec<SorobanExpr>) -> SorobanExpr {
    match name {
        "require_auth" => {
            let addr = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::RequireAuth(Box::new(addr))
        }
        "require_auth_for_args" => {
            let auth_args = args.pop().unwrap_or(SorobanExpr::Void);
            let addr = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::RequireAuthForArgs {
                address: Box::new(addr),
                args: Box::new(auth_args),
            }
        }
        "authorize_as_curr_contract" => {
            let auth_args = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::AuthorizeAsCurrContract(Box::new(auth_args))
        }
        "get_address_from_muxed_address" => {
            let muxed = args.into_iter().next().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(muxed),
                method: "address".to_string(),
                args: vec![],
            }
        }
        "get_id_from_muxed_address" => {
            let muxed = args.into_iter().next().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(muxed),
                method: "id".to_string(),
                args: vec![],
            }
        }
        // `address_to_strkey`/`strkey_to_address` are the public `Address::to_string`
        // / `Address::from_string` (soroban-sdk `address.rs`), rendered by the
        // existing `AddressToStrkey`/`StrkeyToAddress` IR variants. Without these
        // they fell through to RawHostCall → `env.address().address_to_strkey(..)`,
        // which has no such method (E0599).
        "address_to_strkey" => {
            let addr = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::AddressToStrkey(Box::new(addr))
        }
        "strkey_to_address" => {
            let strkey = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::StrkeyToAddress(Box::new(strkey))
        }
        _ => SorobanExpr::RawHostCall {
            module: "Address".to_string(),
            function: name.to_string(),
            args,
        },
    }
}

fn lift_context_call(name: &str, args: Vec<SorobanExpr>) -> SorobanExpr {
    match name {
        "get_ledger_sequence" => SorobanExpr::LedgerSequence,
        "get_ledger_timestamp" => SorobanExpr::LedgerTimestamp,
        "get_ledger_network_id" => SorobanExpr::LedgerNetworkId,
        "get_current_contract_address" => SorobanExpr::CurrentContractAddress,
        "get_max_live_until_ledger" => SorobanExpr::MaxLiveUntilLedger,
        "contract_event" => {
            let mut a = args;
            let data = a.pop().unwrap_or(SorobanExpr::Void);
            let topics = a.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::PublishEvent {
                event_name: None,
                topics: vec![topics],
                data: Box::new(data),
            }
        }
        "log_from_linear_memory" => SorobanExpr::Log(args),
        "fail_with_error" => {
            let err = args.into_iter().next().unwrap_or(SorobanExpr::Void);
            SorobanExpr::PanicWithError(Box::new(err))
        }
        _ => SorobanExpr::RawHostCall {
            module: "Context".to_string(),
            function: name.to_string(),
            args,
        },
    }
}

fn lift_crypto_call(name: &str, mut args: Vec<SorobanExpr>) -> SorobanExpr {
    match name {
        "compute_hash_sha256" => {
            let data = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::CryptoSha256(Box::new(data))
        }
        "compute_hash_keccak256" => {
            let data = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::CryptoKeccak256(Box::new(data))
        }
        "verify_sig_ed25519" => {
            let sig = args.pop().unwrap_or(SorobanExpr::Void);
            let msg = args.pop().unwrap_or(SorobanExpr::Void);
            let pk = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::CryptoEd25519Verify {
                public_key: Box::new(pk),
                message: Box::new(msg),
                signature: Box::new(sig),
            }
        }
        // BN254 operations — emit operators (Bn254G1Affine impls Add/Mul via crypto type aliases)
        "bn254_g1_add" => {
            let b = args.pop().unwrap_or(SorobanExpr::Void);
            let a = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::Add(Box::new(a), Box::new(b))
        }
        "bn254_g1_mul" => {
            let s = args.pop().unwrap_or(SorobanExpr::Void);
            let p = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::Mul(Box::new(p), Box::new(s))
        }
        "bn254_multi_pairing_check" => {
            let vq = args.pop().unwrap_or(SorobanExpr::Void);
            let vp = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bn254", "pairing_check", vec![vp, vq])
        }
        // BLS12-381 operations
        "bls12_381_g1_add" => {
            let b = args.pop().unwrap_or(SorobanExpr::Void);
            let a = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "g1_add", vec![a, b])
        }
        "bls12_381_g1_mul" => {
            let s = args.pop().unwrap_or(SorobanExpr::Void);
            let p = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "g1_mul", vec![p, s])
        }
        "bls12_381_g1_msm" => {
            let ss = args.pop().unwrap_or(SorobanExpr::Void);
            let ps = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "g1_msm", vec![ps, ss])
        }
        "bls12_381_g2_add" => {
            let b = args.pop().unwrap_or(SorobanExpr::Void);
            let a = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "g2_add", vec![a, b])
        }
        "bls12_381_g2_mul" => {
            let s = args.pop().unwrap_or(SorobanExpr::Void);
            let p = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "g2_mul", vec![p, s])
        }
        "bls12_381_g2_msm" => {
            let ss = args.pop().unwrap_or(SorobanExpr::Void);
            let ps = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "g2_msm", vec![ps, ss])
        }
        "bls12_381_multi_pairing_check" => {
            let vq = args.pop().unwrap_or(SorobanExpr::Void);
            let vp = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "pairing_check", vec![vp, vq])
        }
        "bls12_381_check_g1_is_in_subgroup" => {
            let p = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "g1_is_in_subgroup", vec![p])
        }
        "bls12_381_check_g2_is_in_subgroup" => {
            let p = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "g2_is_in_subgroup", vec![p])
        }
        "bls12_381_map_fp_to_g1" => {
            let fp = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "map_fp_to_g1", vec![fp])
        }
        "bls12_381_map_fp2_to_g2" => {
            let fp2 = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "map_fp2_to_g2", vec![fp2])
        }
        "bls12_381_hash_to_g1" => {
            let msg = args.pop().unwrap_or(SorobanExpr::Void);
            let dst = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "hash_to_g1", vec![dst, msg])
        }
        "bls12_381_hash_to_g2" => {
            let msg = args.pop().unwrap_or(SorobanExpr::Void);
            let dst = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "hash_to_g2", vec![dst, msg])
        }
        "bls12_381_fr_add" => {
            let b = args.pop().unwrap_or(SorobanExpr::Void);
            let a = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "fr_add", vec![a, b])
        }
        "bls12_381_fr_sub" => {
            let b = args.pop().unwrap_or(SorobanExpr::Void);
            let a = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "fr_sub", vec![a, b])
        }
        "bls12_381_fr_mul" => {
            let b = args.pop().unwrap_or(SorobanExpr::Void);
            let a = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "fr_mul", vec![a, b])
        }
        "bls12_381_fr_pow" => {
            let exp = args.pop().unwrap_or(SorobanExpr::Void);
            let base = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "fr_pow", vec![base, exp])
        }
        "bls12_381_fr_inv" => {
            let a = args.pop().unwrap_or(SorobanExpr::Void);
            crypto_method_call("bls12_381", "fr_inv", vec![a])
        }
        // ECDSA operations
        "recover_key_ecdsa_secp256k1" => {
            let rid = args.pop().unwrap_or(SorobanExpr::Void);
            let sig = args.pop().unwrap_or(SorobanExpr::Void);
            let md = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::CryptoSecp256k1Recover {
                msg_digest: Box::new(md),
                signature: Box::new(sig),
                recovery_id: Box::new(rid),
            }
        }
        _ => SorobanExpr::RawHostCall {
            module: "Crypto".to_string(),
            function: name.to_string(),
            args,
        },
    }
}

/// Build `env.crypto().{submodule}().{method}(args)` as nested MethodCall nodes.
fn crypto_method_call(submodule: &str, method: &str, args: Vec<SorobanExpr>) -> SorobanExpr {
    SorobanExpr::MethodCall {
        object: Box::new(SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::MethodCall {
                object: Box::new(SorobanExpr::Env),
                method: "crypto".to_string(),
                args: vec![],
            }),
            method: submodule.to_string(),
            args: vec![],
        }),
        method: method.to_string(),
        args,
    }
}

fn lift_contract_call(name: &str, mut args: Vec<SorobanExpr>) -> SorobanExpr {
    match name {
        "call" => {
            let _call_args = args.split_off(3.min(args.len()));
            let args_vec = args.pop().unwrap_or(SorobanExpr::Void);
            let func = args.pop().unwrap_or(SorobanExpr::Void);
            let addr = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::InvokeContract {
                address: Box::new(addr),
                function: Box::new(func),
                args: unwrap_invoke_args(args_vec),
                return_type: None,
            }
        }
        "try_call" => {
            let args_vec = args.pop().unwrap_or(SorobanExpr::Void);
            let func = args.pop().unwrap_or(SorobanExpr::Void);
            let addr = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::TryInvokeContract {
                address: Box::new(addr),
                function: Box::new(func),
                args: unwrap_invoke_args(args_vec),
                return_type: None,
            }
        }
        _ => SorobanExpr::RawHostCall {
            module: "Call".to_string(),
            function: name.to_string(),
            args,
        },
    }
}

/// Unwrap invoke_contract/try_invoke_contract args: the third host-call
/// argument is a Vec<Val>. When the lifter resolves it to a VecConstruct
/// or TupleConstruct, extract the individual elements so codegen emits
/// `vec![&env, x, y]` instead of `vec![&env, (x, y)]`.
fn unwrap_invoke_args(args_vec: SorobanExpr) -> Vec<SorobanExpr> {
    match args_vec {
        SorobanExpr::VecConstruct(elems) => elems,
        SorobanExpr::TupleConstruct(elems) if elems.len() != 1 => elems,
        other => vec![other],
    }
}

fn lift_int_call(name: &str, mut args: Vec<SorobanExpr>) -> SorobanExpr {
    match name {
        // Single-arg conversions
        "obj_from_u64" | "obj_to_u64" => {
            let value = args.into_iter().next().unwrap_or(SorobanExpr::Void);
            SorobanExpr::ValConvert {
                value: Box::new(value),
                target_type: "u64".to_string(),
            }
        }
        "obj_from_i64" | "obj_to_i64" => {
            let value = args.into_iter().next().unwrap_or(SorobanExpr::Void);
            SorobanExpr::ValConvert {
                value: Box::new(value),
                target_type: "i64".to_string(),
            }
        }
        // Extraction operations — pass through the value
        "obj_to_u128_lo64" | "obj_to_u128_hi64" => {
            let value = args.into_iter().next().unwrap_or(SorobanExpr::Void);
            SorobanExpr::ValConvert {
                value: Box::new(value),
                target_type: "u128".to_string(),
            }
        }
        "obj_to_i128_lo64" | "obj_to_i128_hi64" => {
            let value = args.into_iter().next().unwrap_or(SorobanExpr::Void);
            SorobanExpr::ValConvert {
                value: Box::new(value),
                target_type: "i128".to_string(),
            }
        }
        // Two-arg piece constructors — consume both args to keep the stack clean
        "obj_from_u128_pieces" => {
            let _lo = args.pop().unwrap_or(SorobanExpr::Void);
            let hi = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::ValConvert {
                value: Box::new(hi),
                target_type: "u128".to_string(),
            }
        }
        "obj_from_i128_pieces" => {
            let _lo = args.pop().unwrap_or(SorobanExpr::Void);
            let hi = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::ValConvert {
                value: Box::new(hi),
                target_type: "i128".to_string(),
            }
        }
        // Timepoint/Duration
        "timepoint_obj_from_u64" | "timepoint_obj_to_u64" => {
            let value = args.into_iter().next().unwrap_or(SorobanExpr::Void);
            SorobanExpr::ValConvert {
                value: Box::new(value),
                target_type: "u64".to_string(),
            }
        }
        "duration_obj_from_u64" | "duration_obj_to_u64" => {
            let value = args.into_iter().next().unwrap_or(SorobanExpr::Void);
            SorobanExpr::ValConvert {
                value: Box::new(value),
                target_type: "u64".to_string(),
            }
        }
        // U256/I256 four-piece constructors — consume all 4 args
        "obj_from_u256_pieces" | "obj_from_i256_pieces" => {
            let _d = args.pop();
            let _c = args.pop();
            let _b = args.pop();
            let hi = args.pop().unwrap_or(SorobanExpr::Void);
            let target = if name.contains("u256") {
                "U256"
            } else {
                "I256"
            };
            SorobanExpr::ValConvert {
                value: Box::new(hi),
                target_type: target.to_string(),
            }
        }
        // Fallback for any other Int module functions
        _ => {
            let value = args.into_iter().next().unwrap_or(SorobanExpr::Void);
            SorobanExpr::ValConvert {
                value: Box::new(value),
                target_type: name.to_string(),
            }
        }
    }
}

fn lift_prng_call(name: &str, mut args: Vec<SorobanExpr>) -> SorobanExpr {
    match name {
        "prng_reseed" => {
            let seed = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::PrngReseed(Box::new(seed))
        }
        "prng_bytes_new" => {
            let len = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::PrngBytesNew(Box::new(len))
        }
        "prng_u64_in_inclusive_range" => {
            let high = args.pop().unwrap_or(SorobanExpr::Void);
            let low = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::PrngU64InRange {
                low: Box::new(low),
                high: Box::new(high),
            }
        }
        "prng_vec_shuffle" => {
            let vec = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::PrngVecShuffle(Box::new(vec))
        }
        _ => SorobanExpr::RawHostCall {
            module: "Prng".to_string(),
            function: name.to_string(),
            args,
        },
    }
}

fn lift_map_call(name: &str, mut args: Vec<SorobanExpr>) -> SorobanExpr {
    match name {
        "map_new" => SorobanExpr::CollectionNew("Map".to_string()),
        "map_put" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            let key = args.pop().unwrap_or(SorobanExpr::Void);
            let map = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(map),
                method: "set".to_string(),
                args: vec![key, val],
            }
        }
        "map_get" => {
            let key = args.pop().unwrap_or(SorobanExpr::Void);
            let map = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(map),
                method: "get".to_string(),
                args: vec![key],
            }
        }
        "map_del" => {
            let key = args.pop().unwrap_or(SorobanExpr::Void);
            let map = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(map),
                method: "remove".to_string(),
                args: vec![key],
            }
        }
        "map_len" => {
            let map = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(map),
                method: "len".to_string(),
                args: vec![],
            }
        }
        "map_has" => {
            let key = args.pop().unwrap_or(SorobanExpr::Void);
            let map = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(map),
                method: "contains_key".to_string(),
                args: vec![key],
            }
        }
        "map_keys" => {
            let map = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(map),
                method: "keys".to_string(),
                args: vec![],
            }
        }
        "map_values" => {
            let map = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(map),
                method: "values".to_string(),
                args: vec![],
            }
        }
        // Linear memory variants fall through - handled by the lifter directly
        "map_new_from_linear_memory" | "map_unpack_to_linear_memory" => SorobanExpr::RawHostCall {
            module: "Map".to_string(),
            function: name.to_string(),
            args,
        },
        _ => SorobanExpr::RawHostCall {
            module: "Map".to_string(),
            function: name.to_string(),
            args,
        },
    }
}

fn lift_vec_call(name: &str, mut args: Vec<SorobanExpr>) -> SorobanExpr {
    match name {
        "vec_new" => SorobanExpr::CollectionNew("Vec".to_string()),
        "vec_put" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            let idx = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "set".to_string(),
                args: vec![idx, val],
            }
        }
        "vec_get" => {
            let idx = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "get".to_string(),
                args: vec![idx],
            }
        }
        "vec_del" => {
            let idx = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "remove".to_string(),
                args: vec![idx],
            }
        }
        "vec_len" => {
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "len".to_string(),
                args: vec![],
            }
        }
        "vec_push_front" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "push_front".to_string(),
                args: vec![val],
            }
        }
        "vec_pop_front" => {
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "pop_front".to_string(),
                args: vec![],
            }
        }
        "vec_push_back" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "push_back".to_string(),
                args: vec![val],
            }
        }
        "vec_pop_back" => {
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "pop_back".to_string(),
                args: vec![],
            }
        }
        "vec_front" => {
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "first".to_string(),
                args: vec![],
            }
        }
        "vec_back" => {
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "last".to_string(),
                args: vec![],
            }
        }
        "vec_insert" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            let idx = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "insert".to_string(),
                args: vec![idx, val],
            }
        }
        "vec_append" => {
            let other = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "append".to_string(),
                args: vec![other],
            }
        }
        "vec_slice" => {
            let end = args.pop().unwrap_or(SorobanExpr::Void);
            let start = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "slice".to_string(),
                args: vec![start, end],
            }
        }
        "vec_first_index_of" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "first_index_of".to_string(),
                args: vec![val],
            }
        }
        "vec_last_index_of" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "last_index_of".to_string(),
                args: vec![val],
            }
        }
        "vec_binary_search" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            let vec_obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(vec_obj),
                method: "binary_search".to_string(),
                args: vec![val],
            }
        }
        // Linear memory variants fall through - handled by the lifter directly
        "vec_new_from_linear_memory" | "vec_unpack_to_linear_memory" => SorobanExpr::RawHostCall {
            module: "Vec".to_string(),
            function: name.to_string(),
            args,
        },
        _ => SorobanExpr::RawHostCall {
            module: "Vec".to_string(),
            function: name.to_string(),
            args,
        },
    }
}

fn lift_buf_call(name: &str, mut args: Vec<SorobanExpr>) -> SorobanExpr {
    match name {
        "serialize_to_bytes" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(SorobanExpr::Env),
                method: "to_xdr".to_string(),
                args: vec![val],
            }
        }
        "deserialize_from_bytes" => {
            let bytes = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(SorobanExpr::Env),
                method: "from_xdr".to_string(),
                args: vec![bytes],
            }
        }
        "bytes_len" | "string_len" | "symbol_len" => {
            let obj = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(obj),
                method: "len".to_string(),
                args: vec![],
            }
        }
        // The host `bytes_new` constructs an empty bytes object — the public
        // `Bytes::new(&env)` (soroban-sdk `bytes.rs`), via the `CollectionNew`
        // codegen (`Bytes::new(&env)`). Was `env.bytes_new()`, no such method (E0599).
        "bytes_new" => SorobanExpr::CollectionNew("Bytes".to_string()),
        "bytes_push" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            let bytes = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(bytes),
                method: "push".to_string(),
                args: vec![val],
            }
        }
        "bytes_append" => {
            let other = args.pop().unwrap_or(SorobanExpr::Void);
            let bytes = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(bytes),
                method: "append".to_string(),
                args: vec![other],
            }
        }
        "bytes_slice" => {
            let end = args.pop().unwrap_or(SorobanExpr::Void);
            let start = args.pop().unwrap_or(SorobanExpr::Void);
            let bytes = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(bytes),
                method: "slice".to_string(),
                args: vec![start, end],
            }
        }
        "bytes_get" => {
            let idx = args.pop().unwrap_or(SorobanExpr::Void);
            let bytes = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(bytes),
                method: "get".to_string(),
                args: vec![idx],
            }
        }
        "bytes_put" => {
            let val = args.pop().unwrap_or(SorobanExpr::Void);
            let idx = args.pop().unwrap_or(SorobanExpr::Void);
            let bytes = args.pop().unwrap_or(SorobanExpr::Void);
            SorobanExpr::MethodCall {
                object: Box::new(bytes),
                method: "set".to_string(),
                args: vec![idx, val],
            }
        }
        _ => SorobanExpr::RawHostCall {
            module: "Buf".to_string(),
            function: name.to_string(),
            args,
        },
    }
}

/// Extract storage type from a Val discriminant.
fn extract_storage_type(expr: Option<SorobanExpr>) -> StorageType {
    match expr {
        Some(SorobanExpr::I64Literal(0))
        | Some(SorobanExpr::I32Literal(0))
        | Some(SorobanExpr::U32Literal(0))
        | Some(SorobanExpr::BoolLiteral(false)) => StorageType::Temporary,
        Some(SorobanExpr::I64Literal(2))
        | Some(SorobanExpr::I32Literal(2))
        | Some(SorobanExpr::U32Literal(2))
        | Some(SorobanExpr::Void) => StorageType::Instance,
        _ => StorageType::Persistent, // Default to persistent
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hf(module: HostModule, name: &str) -> HostFunction {
        HostFunction {
            module,
            name: name.to_string(),
            import_index: 0,
            type_index: 0,
        }
    }

    fn key() -> SorobanExpr {
        SorobanExpr::SymbolLiteral("k".to_string())
    }
    fn val() -> SorobanExpr {
        SorobanExpr::U64Literal(7)
    }
    fn storage_persistent() -> SorobanExpr {
        SorobanExpr::I64Literal(1)
    }
    fn storage_temp() -> SorobanExpr {
        SorobanExpr::I64Literal(0)
    }
    fn storage_instance() -> SorobanExpr {
        SorobanExpr::I64Literal(2)
    }

    fn obj() -> SorobanExpr {
        SorobanExpr::Param("o".to_string())
    }

    // ----- Top-level dispatch -----

    #[test]
    fn unknown_module_returns_raw_host_call() {
        let f = hf(HostModule::Unknown, "do_thing");
        let out = lift_host_call(&f, vec![]);
        match out {
            SorobanExpr::RawHostCall {
                module, function, ..
            } => {
                assert_eq!(module, "Unknown");
                assert_eq!(function, "do_thing");
            }
            other => panic!("expected RawHostCall, got {other:?}"),
        }
    }

    #[test]
    fn test_module_returns_raw_host_call() {
        let f = hf(HostModule::Test, "dummy0");
        let out = lift_host_call(&f, vec![]);
        assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
    }

    // ----- Ledger storage -----

    #[test]
    fn ledger_put_get_has_del_storage_type_disambiguation() {
        // put_contract_data(key, val, storage_type=Persistent)
        let out = lift_host_call(
            &hf(HostModule::Ledger, "put_contract_data"),
            vec![key(), val(), storage_persistent()],
        );
        assert!(matches!(
            out,
            SorobanExpr::StorageSet {
                storage_type: StorageType::Persistent,
                ..
            }
        ));

        // get_contract_data with storage_type=Temporary
        let out = lift_host_call(
            &hf(HostModule::Ledger, "get_contract_data"),
            vec![key(), storage_temp()],
        );
        assert!(matches!(
            out,
            SorobanExpr::StorageGet {
                storage_type: StorageType::Temporary,
                unwrap: true,
                ..
            }
        ));

        // has_contract_data with storage_type=Instance
        let out = lift_host_call(
            &hf(HostModule::Ledger, "has_contract_data"),
            vec![key(), storage_instance()],
        );
        assert!(matches!(
            out,
            SorobanExpr::StorageHas {
                storage_type: StorageType::Instance,
                ..
            }
        ));

        // del_contract_data
        let out = lift_host_call(
            &hf(HostModule::Ledger, "del_contract_data"),
            vec![key(), storage_persistent()],
        );
        assert!(matches!(out, SorobanExpr::StorageRemove { .. }));
    }

    #[test]
    fn ledger_extend_ttl_variants() {
        let out = lift_host_call(
            &hf(HostModule::Ledger, "extend_contract_data_ttl"),
            vec![
                key(),
                storage_persistent(),
                SorobanExpr::U32Literal(100),
                SorobanExpr::U32Literal(1000),
            ],
        );
        assert!(matches!(out, SorobanExpr::StorageExtendTtl { .. }));

        let out = lift_host_call(
            &hf(
                HostModule::Ledger,
                "extend_current_contract_instance_and_code_ttl",
            ),
            vec![SorobanExpr::U32Literal(10), SorobanExpr::U32Literal(20)],
        );
        assert!(matches!(out, SorobanExpr::ExtendInstanceAndCodeTtl { .. }));
    }

    #[test]
    fn ledger_unknown_falls_back_to_raw() {
        let out = lift_host_call(&hf(HostModule::Ledger, "unknown_op"), vec![]);
        assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
    }

    #[test]
    fn ledger_update_wasm_lowers_to_deployer() {
        // Faithful public API is `env.deployer().update_current_contract_wasm(hash)`,
        // NOT the RawHostCall `env.ledger().update_current_contract_wasm(..)` (E0599).
        let out = lift_host_call(
            &hf(HostModule::Ledger, "update_current_contract_wasm"),
            vec![SorobanExpr::Param("hash".into())],
        );
        match out {
            SorobanExpr::MethodCall {
                object,
                method,
                args,
            } => {
                assert_eq!(method, "update_current_contract_wasm");
                assert!(matches!(args.as_slice(), [SorobanExpr::Param(p)] if p == "hash"));
                assert!(matches!(
                    *object,
                    SorobanExpr::MethodCall { ref method, .. } if method == "deployer"
                ));
            }
            other => panic!("expected deployer().update_current_contract_wasm, got {other:?}"),
        }
    }

    // ----- Address -----

    #[test]
    fn address_auth_variants() {
        let out = lift_host_call(
            &hf(HostModule::Address, "require_auth"),
            vec![SorobanExpr::Param("a".into())],
        );
        assert!(matches!(out, SorobanExpr::RequireAuth(_)));

        let out = lift_host_call(
            &hf(HostModule::Address, "require_auth_for_args"),
            vec![
                SorobanExpr::Param("a".into()),
                SorobanExpr::TupleConstruct(vec![]),
            ],
        );
        assert!(matches!(out, SorobanExpr::RequireAuthForArgs { .. }));

        let out = lift_host_call(
            &hf(HostModule::Address, "authorize_as_curr_contract"),
            vec![SorobanExpr::VecConstruct(vec![])],
        );
        assert!(matches!(out, SorobanExpr::AuthorizeAsCurrContract(_)));
    }

    #[test]
    fn address_strkey_conversions_lower_to_public_api() {
        // `address_to_strkey` → `addr.to_string()`; `strkey_to_address` →
        // `Address::from_string(&sk)` (the existing AddressToStrkey/StrkeyToAddress
        // IR variants), NOT the RawHostCall `env.address().address_to_strkey(..)`.
        let out = lift_host_call(
            &hf(HostModule::Address, "address_to_strkey"),
            vec![SorobanExpr::Param("a".into())],
        );
        assert!(matches!(out, SorobanExpr::AddressToStrkey(b) if matches!(*b, SorobanExpr::Param(ref p) if p == "a")));

        let out = lift_host_call(
            &hf(HostModule::Address, "strkey_to_address"),
            vec![SorobanExpr::Param("sk".into())],
        );
        assert!(matches!(out, SorobanExpr::StrkeyToAddress(b) if matches!(*b, SorobanExpr::Param(ref p) if p == "sk")));
    }

    #[test]
    fn address_muxed_extraction_methods() {
        let out = lift_host_call(
            &hf(HostModule::Address, "get_address_from_muxed_address"),
            vec![SorobanExpr::Param("mux".into())],
        );
        match out {
            SorobanExpr::MethodCall { method, .. } => assert_eq!(method, "address"),
            other => panic!("expected MethodCall, got {other:?}"),
        }

        let out = lift_host_call(
            &hf(HostModule::Address, "get_id_from_muxed_address"),
            vec![SorobanExpr::Param("mux".into())],
        );
        match out {
            SorobanExpr::MethodCall { method, .. } => assert_eq!(method, "id"),
            other => panic!("expected MethodCall, got {other:?}"),
        }
    }

    #[test]
    fn address_unknown_falls_back_to_raw() {
        let out = lift_host_call(&hf(HostModule::Address, "unknown"), vec![]);
        assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
    }

    // ----- Context -----

    #[test]
    fn context_ledger_atoms() {
        for (name, expected) in [
            ("get_ledger_sequence", SorobanExpr::LedgerSequence),
            ("get_ledger_timestamp", SorobanExpr::LedgerTimestamp),
            ("get_ledger_network_id", SorobanExpr::LedgerNetworkId),
            (
                "get_current_contract_address",
                SorobanExpr::CurrentContractAddress,
            ),
            ("get_max_live_until_ledger", SorobanExpr::MaxLiveUntilLedger),
        ] {
            let out = lift_host_call(&hf(HostModule::Context, name), vec![]);
            assert_eq!(out, expected);
        }
    }

    #[test]
    fn context_contract_event_log_fail() {
        let out = lift_host_call(
            &hf(HostModule::Context, "contract_event"),
            vec![SorobanExpr::SymbolLiteral("t".into()), val()],
        );
        assert!(matches!(
            out,
            SorobanExpr::PublishEvent {
                event_name: None,
                ..
            }
        ));

        let out = lift_host_call(
            &hf(HostModule::Context, "log_from_linear_memory"),
            vec![val()],
        );
        assert!(matches!(out, SorobanExpr::Log(_)));

        let out = lift_host_call(
            &hf(HostModule::Context, "fail_with_error"),
            vec![SorobanExpr::U32Literal(1)],
        );
        assert!(matches!(out, SorobanExpr::PanicWithError(_)));
    }

    #[test]
    fn context_unknown_falls_back_to_raw() {
        let out = lift_host_call(&hf(HostModule::Context, "unknown"), vec![]);
        assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
    }

    // ----- Crypto -----

    #[test]
    fn crypto_hash_variants() {
        let out = lift_host_call(
            &hf(HostModule::Crypto, "compute_hash_sha256"),
            vec![SorobanExpr::Param("d".into())],
        );
        assert!(matches!(out, SorobanExpr::CryptoSha256(_)));

        let out = lift_host_call(
            &hf(HostModule::Crypto, "compute_hash_keccak256"),
            vec![SorobanExpr::Param("d".into())],
        );
        assert!(matches!(out, SorobanExpr::CryptoKeccak256(_)));
    }

    #[test]
    fn crypto_ed25519_verify() {
        let out = lift_host_call(
            &hf(HostModule::Crypto, "verify_sig_ed25519"),
            vec![
                SorobanExpr::Param("pk".into()),
                SorobanExpr::Param("m".into()),
                SorobanExpr::Param("sig".into()),
            ],
        );
        assert!(matches!(out, SorobanExpr::CryptoEd25519Verify { .. }));
    }

    #[test]
    fn crypto_secp256k1_recover() {
        let out = lift_host_call(
            &hf(HostModule::Crypto, "recover_key_ecdsa_secp256k1"),
            vec![
                SorobanExpr::Param("md".into()),
                SorobanExpr::Param("sig".into()),
                SorobanExpr::U32Literal(0),
            ],
        );
        assert!(matches!(out, SorobanExpr::CryptoSecp256k1Recover { .. }));
    }

    #[test]
    fn crypto_bn254_arithmetic() {
        let out = lift_host_call(
            &hf(HostModule::Crypto, "bn254_g1_add"),
            vec![
                SorobanExpr::Param("a".into()),
                SorobanExpr::Param("b".into()),
            ],
        );
        assert!(matches!(out, SorobanExpr::Add(_, _)));

        let out = lift_host_call(
            &hf(HostModule::Crypto, "bn254_g1_mul"),
            vec![
                SorobanExpr::Param("p".into()),
                SorobanExpr::Param("s".into()),
            ],
        );
        assert!(matches!(out, SorobanExpr::Mul(_, _)));

        let out = lift_host_call(
            &hf(HostModule::Crypto, "bn254_multi_pairing_check"),
            vec![
                SorobanExpr::Param("p".into()),
                SorobanExpr::Param("q".into()),
            ],
        );
        match out {
            SorobanExpr::MethodCall { method, .. } => assert_eq!(method, "pairing_check"),
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn crypto_bls12_381_full_surface() {
        let methods = [
            ("bls12_381_g1_add", "g1_add", 2),
            ("bls12_381_g1_mul", "g1_mul", 2),
            ("bls12_381_g1_msm", "g1_msm", 2),
            ("bls12_381_g2_add", "g2_add", 2),
            ("bls12_381_g2_mul", "g2_mul", 2),
            ("bls12_381_g2_msm", "g2_msm", 2),
            ("bls12_381_multi_pairing_check", "pairing_check", 2),
            ("bls12_381_check_g1_is_in_subgroup", "g1_is_in_subgroup", 1),
            ("bls12_381_check_g2_is_in_subgroup", "g2_is_in_subgroup", 1),
            ("bls12_381_map_fp_to_g1", "map_fp_to_g1", 1),
            ("bls12_381_map_fp2_to_g2", "map_fp2_to_g2", 1),
            ("bls12_381_hash_to_g1", "hash_to_g1", 2),
            ("bls12_381_hash_to_g2", "hash_to_g2", 2),
            ("bls12_381_fr_add", "fr_add", 2),
            ("bls12_381_fr_sub", "fr_sub", 2),
            ("bls12_381_fr_mul", "fr_mul", 2),
            ("bls12_381_fr_pow", "fr_pow", 2),
            ("bls12_381_fr_inv", "fr_inv", 1),
        ];
        for (host_name, sdk_method, arg_count) in methods {
            let args: Vec<_> = (0..arg_count)
                .map(|i| SorobanExpr::Param(format!("arg{i}")))
                .collect();
            let out = lift_host_call(&hf(HostModule::Crypto, host_name), args);
            match out {
                SorobanExpr::MethodCall { method, .. } => assert_eq!(
                    method, sdk_method,
                    "host {host_name} should map to .{sdk_method}()"
                ),
                other => panic!("{host_name}: expected MethodCall, got {other:?}"),
            }
        }
    }

    #[test]
    fn crypto_unknown_falls_back_to_raw() {
        let out = lift_host_call(&hf(HostModule::Crypto, "unknown"), vec![]);
        assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
    }

    // ----- Call / contract invocation -----

    #[test]
    fn contract_call_and_try_call() {
        let out = lift_host_call(
            &hf(HostModule::Call, "call"),
            vec![
                SorobanExpr::Param("addr".into()),
                SorobanExpr::SymbolLiteral("fn".into()),
                SorobanExpr::VecConstruct(vec![SorobanExpr::U32Literal(1)]),
            ],
        );
        match out {
            SorobanExpr::InvokeContract { args, .. } => assert_eq!(args.len(), 1),
            other => panic!("got {other:?}"),
        }

        let out = lift_host_call(
            &hf(HostModule::Call, "try_call"),
            vec![
                SorobanExpr::Param("addr".into()),
                SorobanExpr::SymbolLiteral("fn".into()),
                SorobanExpr::VecConstruct(vec![]),
            ],
        );
        assert!(matches!(out, SorobanExpr::TryInvokeContract { .. }));
    }

    #[test]
    fn contract_call_unwraps_tuple_args_with_multi_elements() {
        // TupleConstruct with multiple elements gets unwrapped.
        let out = lift_host_call(
            &hf(HostModule::Call, "call"),
            vec![
                SorobanExpr::Param("addr".into()),
                SorobanExpr::SymbolLiteral("fn".into()),
                SorobanExpr::TupleConstruct(vec![
                    SorobanExpr::U32Literal(1),
                    SorobanExpr::U32Literal(2),
                ]),
            ],
        );
        match out {
            SorobanExpr::InvokeContract { args, .. } => assert_eq!(args.len(), 2),
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn contract_call_keeps_single_tuple_as_single_arg() {
        // Single-element TupleConstruct stays as 1 arg (not unwrapped).
        let out = lift_host_call(
            &hf(HostModule::Call, "call"),
            vec![
                SorobanExpr::Param("addr".into()),
                SorobanExpr::SymbolLiteral("fn".into()),
                SorobanExpr::TupleConstruct(vec![SorobanExpr::U32Literal(1)]),
            ],
        );
        match out {
            SorobanExpr::InvokeContract { args, .. } => assert_eq!(args.len(), 1),
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn contract_call_unknown_falls_back() {
        let out = lift_host_call(&hf(HostModule::Call, "unknown"), vec![]);
        assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
    }

    // ----- Int -----

    #[test]
    fn int_conversions_64_bit() {
        for name in ["obj_from_u64", "obj_to_u64"] {
            let out = lift_host_call(&hf(HostModule::Int, name), vec![val()]);
            match out {
                SorobanExpr::ValConvert { target_type, .. } => assert_eq!(target_type, "u64"),
                other => panic!("got {other:?}"),
            }
        }
        for name in ["obj_from_i64", "obj_to_i64"] {
            let out = lift_host_call(&hf(HostModule::Int, name), vec![val()]);
            match out {
                SorobanExpr::ValConvert { target_type, .. } => assert_eq!(target_type, "i64"),
                other => panic!("got {other:?}"),
            }
        }
    }

    #[test]
    fn int_extraction_128_bit() {
        for name in ["obj_to_u128_lo64", "obj_to_u128_hi64"] {
            let out = lift_host_call(&hf(HostModule::Int, name), vec![val()]);
            match out {
                SorobanExpr::ValConvert { target_type, .. } => assert_eq!(target_type, "u128"),
                other => panic!("got {other:?}"),
            }
        }
        for name in ["obj_to_i128_lo64", "obj_to_i128_hi64"] {
            let out = lift_host_call(&hf(HostModule::Int, name), vec![val()]);
            match out {
                SorobanExpr::ValConvert { target_type, .. } => assert_eq!(target_type, "i128"),
                other => panic!("got {other:?}"),
            }
        }
    }

    #[test]
    fn int_piece_constructors_128_and_256() {
        let out = lift_host_call(
            &hf(HostModule::Int, "obj_from_u128_pieces"),
            vec![SorobanExpr::U64Literal(0), SorobanExpr::U64Literal(1)],
        );
        match out {
            SorobanExpr::ValConvert { target_type, .. } => assert_eq!(target_type, "u128"),
            other => panic!("got {other:?}"),
        }

        let out = lift_host_call(
            &hf(HostModule::Int, "obj_from_i128_pieces"),
            vec![SorobanExpr::U64Literal(0), SorobanExpr::U64Literal(1)],
        );
        match out {
            SorobanExpr::ValConvert { target_type, .. } => assert_eq!(target_type, "i128"),
            other => panic!("got {other:?}"),
        }

        let out = lift_host_call(
            &hf(HostModule::Int, "obj_from_u256_pieces"),
            vec![
                SorobanExpr::U64Literal(0),
                SorobanExpr::U64Literal(1),
                SorobanExpr::U64Literal(2),
                SorobanExpr::U64Literal(3),
            ],
        );
        match out {
            SorobanExpr::ValConvert { target_type, .. } => assert_eq!(target_type, "U256"),
            other => panic!("got {other:?}"),
        }

        let out = lift_host_call(
            &hf(HostModule::Int, "obj_from_i256_pieces"),
            vec![
                SorobanExpr::U64Literal(0),
                SorobanExpr::U64Literal(1),
                SorobanExpr::U64Literal(2),
                SorobanExpr::U64Literal(3),
            ],
        );
        match out {
            SorobanExpr::ValConvert { target_type, .. } => assert_eq!(target_type, "I256"),
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn int_timepoint_duration() {
        for name in ["timepoint_obj_from_u64", "timepoint_obj_to_u64"] {
            let out = lift_host_call(&hf(HostModule::Int, name), vec![val()]);
            assert!(matches!(out, SorobanExpr::ValConvert { .. }));
        }
        for name in ["duration_obj_from_u64", "duration_obj_to_u64"] {
            let out = lift_host_call(&hf(HostModule::Int, name), vec![val()]);
            assert!(matches!(out, SorobanExpr::ValConvert { .. }));
        }
    }

    #[test]
    fn int_unknown_uses_name_as_target_type() {
        let out = lift_host_call(&hf(HostModule::Int, "mystery_conversion"), vec![val()]);
        match out {
            SorobanExpr::ValConvert { target_type, .. } => {
                assert_eq!(target_type, "mystery_conversion")
            }
            other => panic!("got {other:?}"),
        }
    }

    // ----- PRNG -----

    #[test]
    fn prng_all_variants() {
        let out = lift_host_call(
            &hf(HostModule::Prng, "prng_reseed"),
            vec![SorobanExpr::Param("s".into())],
        );
        assert!(matches!(out, SorobanExpr::PrngReseed(_)));

        let out = lift_host_call(
            &hf(HostModule::Prng, "prng_bytes_new"),
            vec![SorobanExpr::U32Literal(32)],
        );
        assert!(matches!(out, SorobanExpr::PrngBytesNew(_)));

        let out = lift_host_call(
            &hf(HostModule::Prng, "prng_u64_in_inclusive_range"),
            vec![SorobanExpr::U64Literal(1), SorobanExpr::U64Literal(10)],
        );
        assert!(matches!(out, SorobanExpr::PrngU64InRange { .. }));

        let out = lift_host_call(
            &hf(HostModule::Prng, "prng_vec_shuffle"),
            vec![SorobanExpr::Param("v".into())],
        );
        assert!(matches!(out, SorobanExpr::PrngVecShuffle(_)));

        let out = lift_host_call(&hf(HostModule::Prng, "unknown"), vec![]);
        assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
    }

    // ----- Map -----

    #[test]
    fn map_full_surface() {
        assert!(matches!(
            lift_host_call(&hf(HostModule::Map, "map_new"), vec![]),
            SorobanExpr::CollectionNew(_)
        ));
        for (name, sdk_method) in [
            ("map_put", "set"),
            ("map_get", "get"),
            ("map_del", "remove"),
            ("map_has", "contains_key"),
        ] {
            let arg_count = if name == "map_put" { 3 } else { 2 };
            let args: Vec<_> = (0..arg_count).map(|_| obj()).collect();
            let out = lift_host_call(&hf(HostModule::Map, name), args);
            match out {
                SorobanExpr::MethodCall { method, .. } => assert_eq!(method, sdk_method),
                other => panic!("{name}: got {other:?}"),
            }
        }
        for (name, sdk_method) in [
            ("map_len", "len"),
            ("map_keys", "keys"),
            ("map_values", "values"),
        ] {
            let out = lift_host_call(&hf(HostModule::Map, name), vec![obj()]);
            match out {
                SorobanExpr::MethodCall { method, .. } => assert_eq!(method, sdk_method),
                other => panic!("{name}: got {other:?}"),
            }
        }
    }

    #[test]
    fn map_linear_memory_variants_pass_through_raw() {
        for name in ["map_new_from_linear_memory", "map_unpack_to_linear_memory"] {
            let out = lift_host_call(&hf(HostModule::Map, name), vec![]);
            assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
        }
    }

    #[test]
    fn map_unknown_falls_back_to_raw() {
        let out = lift_host_call(&hf(HostModule::Map, "unknown"), vec![]);
        assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
    }

    // ----- Vec -----

    #[test]
    fn vec_full_surface() {
        assert!(matches!(
            lift_host_call(&hf(HostModule::Vec, "vec_new"), vec![]),
            SorobanExpr::CollectionNew(_)
        ));
        // 2-arg ops yielding MethodCall
        for (name, sdk_method) in [
            ("vec_get", "get"),
            ("vec_del", "remove"),
            ("vec_push_front", "push_front"),
            ("vec_push_back", "push_back"),
            ("vec_append", "append"),
            ("vec_first_index_of", "first_index_of"),
            ("vec_last_index_of", "last_index_of"),
            ("vec_binary_search", "binary_search"),
        ] {
            let out = lift_host_call(&hf(HostModule::Vec, name), vec![obj(), obj()]);
            match out {
                SorobanExpr::MethodCall { method, .. } => assert_eq!(method, sdk_method),
                other => panic!("{name}: got {other:?}"),
            }
        }
        // 1-arg ops
        for (name, sdk_method) in [
            ("vec_len", "len"),
            ("vec_pop_front", "pop_front"),
            ("vec_pop_back", "pop_back"),
            ("vec_front", "first"),
            ("vec_back", "last"),
        ] {
            let out = lift_host_call(&hf(HostModule::Vec, name), vec![obj()]);
            match out {
                SorobanExpr::MethodCall { method, .. } => assert_eq!(method, sdk_method),
                other => panic!("{name}: got {other:?}"),
            }
        }
        // 3-arg ops
        for (name, sdk_method) in [
            ("vec_put", "set"),
            ("vec_insert", "insert"),
            ("vec_slice", "slice"),
        ] {
            let out = lift_host_call(&hf(HostModule::Vec, name), vec![obj(), obj(), obj()]);
            match out {
                SorobanExpr::MethodCall { method, .. } => assert_eq!(method, sdk_method),
                other => panic!("{name}: got {other:?}"),
            }
        }
    }

    #[test]
    fn vec_linear_memory_and_unknown_fall_back() {
        for name in [
            "vec_new_from_linear_memory",
            "vec_unpack_to_linear_memory",
            "unknown",
        ] {
            let out = lift_host_call(&hf(HostModule::Vec, name), vec![]);
            assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
        }
    }

    // ----- Buf -----

    #[test]
    fn buf_serialize_and_deserialize() {
        let out = lift_host_call(
            &hf(HostModule::Buf, "serialize_to_bytes"),
            vec![SorobanExpr::Param("v".into())],
        );
        match out {
            SorobanExpr::MethodCall { method, .. } => assert_eq!(method, "to_xdr"),
            other => panic!("got {other:?}"),
        }
        let out = lift_host_call(
            &hf(HostModule::Buf, "deserialize_from_bytes"),
            vec![SorobanExpr::Param("b".into())],
        );
        match out {
            SorobanExpr::MethodCall { method, .. } => assert_eq!(method, "from_xdr"),
            other => panic!("got {other:?}"),
        }
    }

    #[test]
    fn buf_len_variants() {
        for name in ["bytes_len", "string_len", "symbol_len"] {
            let out = lift_host_call(&hf(HostModule::Buf, name), vec![obj()]);
            match out {
                SorobanExpr::MethodCall { method, .. } => assert_eq!(method, "len"),
                other => panic!("{name}: got {other:?}"),
            }
        }
    }

    #[test]
    fn buf_bytes_ops() {
        let cases = [
            ("bytes_push", 2, "push"),
            ("bytes_append", 2, "append"),
            ("bytes_slice", 3, "slice"),
            ("bytes_get", 2, "get"),
            ("bytes_put", 3, "set"),
        ];
        for (name, arg_count, sdk_method) in cases {
            let args: Vec<_> = (0..arg_count).map(|_| obj()).collect();
            let out = lift_host_call(&hf(HostModule::Buf, name), args);
            match out {
                SorobanExpr::MethodCall { method, .. } => assert_eq!(method, sdk_method),
                other => panic!("{name}: got {other:?}"),
            }
        }
    }

    #[test]
    fn buf_bytes_new_lowers_to_bytes_collection() {
        // `bytes_new` → `Bytes::new(&env)` (the public empty-Bytes constructor),
        // via `CollectionNew("Bytes")`, NOT the nonexistent `env.bytes_new()` (E0599).
        let out = lift_host_call(&hf(HostModule::Buf, "bytes_new"), vec![]);
        assert!(
            matches!(out, SorobanExpr::CollectionNew(ref c) if c == "Bytes"),
            "got {out:?}"
        );
    }

    #[test]
    fn buf_unknown_falls_back_to_raw() {
        let out = lift_host_call(&hf(HostModule::Buf, "unknown"), vec![]);
        assert!(matches!(out, SorobanExpr::RawHostCall { .. }));
    }

    // ----- extract_storage_type direct tests -----

    #[test]
    fn extract_storage_type_dispatch() {
        assert_eq!(extract_storage_type(None), StorageType::Persistent);
        assert_eq!(
            extract_storage_type(Some(SorobanExpr::I64Literal(0))),
            StorageType::Temporary
        );
        assert_eq!(
            extract_storage_type(Some(SorobanExpr::I32Literal(0))),
            StorageType::Temporary
        );
        assert_eq!(
            extract_storage_type(Some(SorobanExpr::U32Literal(0))),
            StorageType::Temporary
        );
        assert_eq!(
            extract_storage_type(Some(SorobanExpr::BoolLiteral(false))),
            StorageType::Temporary
        );
        assert_eq!(
            extract_storage_type(Some(SorobanExpr::I64Literal(2))),
            StorageType::Instance
        );
        assert_eq!(
            extract_storage_type(Some(SorobanExpr::I32Literal(2))),
            StorageType::Instance
        );
        assert_eq!(
            extract_storage_type(Some(SorobanExpr::U32Literal(2))),
            StorageType::Instance
        );
        assert_eq!(
            extract_storage_type(Some(SorobanExpr::Void)),
            StorageType::Instance
        );
        // Other values default to Persistent.
        assert_eq!(
            extract_storage_type(Some(SorobanExpr::I64Literal(1))),
            StorageType::Persistent
        );
        assert_eq!(
            extract_storage_type(Some(SorobanExpr::Param("p".into()))),
            StorageType::Persistent
        );
    }
}
