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
        "bytes_new" => SorobanExpr::MethodCall {
            object: Box::new(SorobanExpr::Env),
            method: "bytes_new".to_string(),
            args: vec![],
        },
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
