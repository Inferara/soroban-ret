/// Host function import table analyzer.
///
/// CRITICAL: Soroban WASM uses single-letter module codes and short function codes,
/// NOT full names like "put_contract_data". The import section contains entries like
/// (module="l", name="_") which maps to (Ledger, put_contract_data).

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HostModule {
    Context,
    Int,
    Map,
    Vec,
    Ledger,
    Call,
    Buf,
    Crypto,
    Address,
    Prng,
    Test,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostFunction {
    pub module: HostModule,
    pub name: String,
    pub import_index: u32,
    pub type_index: u32,
}

#[derive(Debug, Default)]
pub struct ImportTable {
    pub functions: Vec<HostFunction>,
}

impl ImportTable {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
        }
    }

    pub fn add(&mut self, module_name: &str, fn_name: &str, type_index: u32) {
        let import_index = self.functions.len() as u32;
        let (module, resolved_name) =
            resolve_host_function(module_name, fn_name).unwrap_or((HostModule::Unknown, fn_name));
        self.functions.push(HostFunction {
            module,
            name: resolved_name.to_string(),
            import_index,
            type_index,
        });
    }

    pub fn resolve(&self, import_index: u32) -> Option<&HostFunction> {
        self.functions
            .iter()
            .find(|f| f.import_index == import_index)
    }

    pub fn get_by_index(&self, func_index: u32) -> Option<&HostFunction> {
        self.functions.get(func_index as usize)
    }

    pub fn len(&self) -> usize {
        self.functions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }
}

/// Resolve a (module_letter, fn_code) pair to (HostModule, full_function_name).
pub fn resolve_host_function(
    module_letter: &str,
    fn_code: &str,
) -> Option<(HostModule, &'static str)> {
    match module_letter {
        "x" => resolve_context(fn_code),
        "i" => resolve_int(fn_code),
        "m" => resolve_map(fn_code),
        "v" => resolve_vec(fn_code),
        "l" => resolve_ledger(fn_code),
        "d" => resolve_call(fn_code),
        "b" => resolve_buf(fn_code),
        "c" => resolve_crypto(fn_code),
        "a" => resolve_address(fn_code),
        "p" => resolve_prng(fn_code),
        "t" => resolve_test(fn_code),
        _ => None,
    }
}

fn resolve_context(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "log_from_linear_memory",
        "0" => "obj_cmp",
        "1" => "contract_event",
        "2" => "get_ledger_version",
        "3" => "get_ledger_sequence",
        "4" => "get_ledger_timestamp",
        "5" => "fail_with_error",
        "6" => "get_ledger_network_id",
        "7" => "get_current_contract_address",
        "8" => "get_max_live_until_ledger",
        _ => return None,
    };
    Some((HostModule::Context, name))
}

fn resolve_int(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "obj_from_u64",
        "0" => "obj_to_u64",
        "1" => "obj_from_i64",
        "2" => "obj_to_i64",
        "3" => "obj_from_u128_pieces",
        "4" => "obj_to_u128_lo64",
        "5" => "obj_to_u128_hi64",
        "6" => "obj_from_i128_pieces",
        "7" => "obj_to_i128_lo64",
        "8" => "obj_to_i128_hi64",
        "9" => "obj_from_u256_pieces",
        "a" => "u256_val_from_be_bytes",
        "b" => "u256_val_to_be_bytes",
        "c" => "obj_to_u256_hi_hi",
        "d" => "obj_to_u256_hi_lo",
        "e" => "obj_to_u256_lo_hi",
        "f" => "obj_to_u256_lo_lo",
        "g" => "obj_from_i256_pieces",
        "h" => "i256_val_from_be_bytes",
        "i" => "i256_val_to_be_bytes",
        "j" => "obj_to_i256_hi_hi",
        "k" => "obj_to_i256_hi_lo",
        "l" => "obj_to_i256_lo_hi",
        "m" => "obj_to_i256_lo_lo",
        "n" => "u256_add",
        "o" => "u256_sub",
        "p" => "u256_mul",
        "q" => "u256_div",
        "r" => "u256_rem_euclid",
        "s" => "u256_pow",
        "t" => "u256_shl",
        "u" => "u256_shr",
        "v" => "i256_add",
        "w" => "i256_sub",
        "x" => "i256_mul",
        "y" => "i256_div",
        "z" => "i256_rem_euclid",
        "A" => "i256_pow",
        "B" => "i256_shl",
        "C" => "i256_shr",
        "D" => "timepoint_obj_from_u64",
        "E" => "timepoint_obj_to_u64",
        "F" => "duration_obj_from_u64",
        "G" => "duration_obj_to_u64",
        _ => return None,
    };
    Some((HostModule::Int, name))
}

fn resolve_map(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "map_new",
        "0" => "map_put",
        "1" => "map_get",
        "2" => "map_del",
        "3" => "map_len",
        "4" => "map_has",
        "5" => "map_key_by_pos",
        "6" => "map_val_by_pos",
        "7" => "map_keys",
        "8" => "map_values",
        "9" => "map_new_from_linear_memory",
        "a" => "map_unpack_to_linear_memory",
        _ => return None,
    };
    Some((HostModule::Map, name))
}

fn resolve_vec(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "vec_new",
        "0" => "vec_put",
        "1" => "vec_get",
        "2" => "vec_del",
        "3" => "vec_len",
        "4" => "vec_push_front",
        "5" => "vec_pop_front",
        "6" => "vec_push_back",
        "7" => "vec_pop_back",
        "8" => "vec_front",
        "9" => "vec_back",
        "a" => "vec_insert",
        "b" => "vec_append",
        "c" => "vec_slice",
        "d" => "vec_first_index_of",
        "e" => "vec_last_index_of",
        "f" => "vec_binary_search",
        "g" => "vec_new_from_linear_memory",
        "h" => "vec_unpack_to_linear_memory",
        _ => return None,
    };
    Some((HostModule::Vec, name))
}

fn resolve_ledger(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "put_contract_data",
        "0" => "has_contract_data",
        "1" => "get_contract_data",
        "2" => "del_contract_data",
        "3" => "create_contract",
        "4" => "create_asset_contract",
        "5" => "upload_wasm",
        "6" => "update_current_contract_wasm",
        "7" => "extend_contract_data_ttl",
        "8" => "extend_current_contract_instance_and_code_ttl",
        "9" => "extend_contract_instance_and_code_ttl",
        "a" => "get_contract_id",
        "b" => "get_asset_contract_id",
        "c" => "extend_contract_instance_ttl",
        "d" => "extend_contract_code_ttl",
        "e" => "create_contract_with_constructor",
        _ => return None,
    };
    Some((HostModule::Ledger, name))
}

fn resolve_call(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "call",
        "0" => "try_call",
        _ => return None,
    };
    Some((HostModule::Call, name))
}

fn resolve_buf(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "serialize_to_bytes",
        "0" => "deserialize_from_bytes",
        "1" => "bytes_copy_to_linear_memory",
        "2" => "bytes_copy_from_linear_memory",
        "3" => "bytes_new_from_linear_memory",
        "4" => "bytes_new",
        "5" => "bytes_put",
        "6" => "bytes_get",
        "7" => "bytes_del",
        "8" => "bytes_len",
        "9" => "bytes_push",
        "a" => "bytes_pop",
        "b" => "bytes_front",
        "c" => "bytes_back",
        "d" => "bytes_insert",
        "e" => "bytes_append",
        "f" => "bytes_slice",
        "g" => "string_copy_to_linear_memory",
        "h" => "symbol_copy_to_linear_memory",
        "i" => "string_new_from_linear_memory",
        "j" => "symbol_new_from_linear_memory",
        "k" => "string_len",
        "l" => "symbol_len",
        "m" => "symbol_index_in_linear_memory",
        "n" => "string_to_bytes",
        "o" => "bytes_to_string",
        _ => return None,
    };
    Some((HostModule::Buf, name))
}

fn resolve_crypto(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "compute_hash_sha256",
        "0" => "verify_sig_ed25519",
        "1" => "compute_hash_keccak256",
        "2" => "recover_key_ecdsa_secp256k1",
        "3" => "verify_sig_ecdsa_secp256r1",
        "4" => "bls12_381_check_g1_is_in_subgroup",
        "5" => "bls12_381_g1_add",
        "6" => "bls12_381_g1_mul",
        "7" => "bls12_381_g1_msm",
        "8" => "bls12_381_map_fp_to_g1",
        "9" => "bls12_381_hash_to_g1",
        "a" => "bls12_381_check_g2_is_in_subgroup",
        "b" => "bls12_381_g2_add",
        "c" => "bls12_381_g2_mul",
        "d" => "bls12_381_g2_msm",
        "e" => "bls12_381_map_fp2_to_g2",
        "f" => "bls12_381_hash_to_g2",
        "g" => "bls12_381_multi_pairing_check",
        "h" => "bls12_381_fr_add",
        "i" => "bls12_381_fr_sub",
        "j" => "bls12_381_fr_mul",
        "k" => "bls12_381_fr_pow",
        "l" => "bls12_381_fr_inv",
        "m" => "bn254_g1_add",
        "n" => "bn254_g1_mul",
        "o" => "bn254_multi_pairing_check",
        _ => return None,
    };
    Some((HostModule::Crypto, name))
}

fn resolve_address(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "require_auth_for_args",
        "0" => "require_auth",
        "1" => "strkey_to_address",
        "2" => "address_to_strkey",
        "3" => "authorize_as_curr_contract",
        "4" => "get_address_from_muxed_address",
        "5" => "get_id_from_muxed_address",
        "6" => "get_address_executable",
        _ => return None,
    };
    Some((HostModule::Address, name))
}

fn resolve_prng(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "prng_reseed",
        "0" => "prng_bytes_new",
        "1" => "prng_u64_in_inclusive_range",
        "2" => "prng_vec_shuffle",
        _ => return None,
    };
    Some((HostModule::Prng, name))
}

fn resolve_test(code: &str) -> Option<(HostModule, &'static str)> {
    let name = match code {
        "_" => "dummy0",
        "0" => "protocol_gated_dummy",
        _ => return None,
    };
    Some((HostModule::Test, name))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resolve_ledger_functions() {
        assert_eq!(
            resolve_host_function("l", "_"),
            Some((HostModule::Ledger, "put_contract_data"))
        );
        assert_eq!(
            resolve_host_function("l", "1"),
            Some((HostModule::Ledger, "get_contract_data"))
        );
    }

    #[test]
    fn test_resolve_address_functions() {
        assert_eq!(
            resolve_host_function("a", "0"),
            Some((HostModule::Address, "require_auth"))
        );
    }

    #[test]
    fn test_resolve_context_functions() {
        assert_eq!(
            resolve_host_function("x", "1"),
            Some((HostModule::Context, "contract_event"))
        );
        assert_eq!(
            resolve_host_function("x", "7"),
            Some((HostModule::Context, "get_current_contract_address"))
        );
    }

    #[test]
    fn test_resolve_unknown() {
        assert_eq!(resolve_host_function("z", "0"), None);
    }

    #[test]
    fn test_import_table() {
        let mut table = ImportTable::new();
        table.add("l", "_", 0);
        table.add("l", "1", 1);
        table.add("a", "0", 2);

        assert_eq!(table.len(), 3);
        assert_eq!(table.get_by_index(0).unwrap().name, "put_contract_data");
        assert_eq!(table.get_by_index(1).unwrap().name, "get_contract_data");
        assert_eq!(table.get_by_index(2).unwrap().name, "require_auth");
    }

    #[test]
    fn empty_table_helpers() {
        let table = ImportTable::new();
        assert!(table.is_empty());
        assert_eq!(table.len(), 0);
        assert!(table.resolve(0).is_none());
        assert!(table.get_by_index(0).is_none());

        let default_table = ImportTable::default();
        assert!(default_table.is_empty());
    }

    #[test]
    fn unknown_module_letter_falls_back_to_unknown_module() {
        let mut t = ImportTable::new();
        t.add("z", "9", 7);
        let entry = t.get_by_index(0).unwrap();
        assert_eq!(entry.module, HostModule::Unknown);
        assert_eq!(entry.name, "9"); // raw fn_code preserved
        assert_eq!(entry.type_index, 7);
        assert_eq!(entry.import_index, 0);
    }

    #[test]
    fn resolve_host_function_returns_none_for_unknown_module_letter() {
        assert!(resolve_host_function("Z", "_").is_none());
        assert!(resolve_host_function("", "_").is_none());
        assert!(resolve_host_function("foo", "_").is_none());
    }

    fn module_codes() -> &'static [(&'static str, HostModule)] {
        &[
            ("x", HostModule::Context),
            ("i", HostModule::Int),
            ("m", HostModule::Map),
            ("v", HostModule::Vec),
            ("l", HostModule::Ledger),
            ("d", HostModule::Call),
            ("b", HostModule::Buf),
            ("c", HostModule::Crypto),
            ("a", HostModule::Address),
            ("p", HostModule::Prng),
            ("t", HostModule::Test),
        ]
    }

    #[test]
    fn unknown_fn_code_within_known_module_returns_none() {
        // "~" is not a valid fn_code in any host module — every module should
        // refuse to resolve it.
        for (letter, _) in module_codes() {
            assert!(
                resolve_host_function(letter, "~").is_none(),
                "expected None for module {letter} fn ~"
            );
        }
    }

    /// Exhaustive table of every (module, fn_code, expected_name) pair Soroban
    /// emits. This drives every match arm in `resolve_*` to be hit at least
    /// once for coverage.
    fn full_dispatch_table() -> Vec<(&'static str, &'static str, HostModule, &'static str)> {
        use HostModule::*;
        vec![
            // Context
            ("x", "_", Context, "log_from_linear_memory"),
            ("x", "0", Context, "obj_cmp"),
            ("x", "1", Context, "contract_event"),
            ("x", "2", Context, "get_ledger_version"),
            ("x", "3", Context, "get_ledger_sequence"),
            ("x", "4", Context, "get_ledger_timestamp"),
            ("x", "5", Context, "fail_with_error"),
            ("x", "6", Context, "get_ledger_network_id"),
            ("x", "7", Context, "get_current_contract_address"),
            ("x", "8", Context, "get_max_live_until_ledger"),
            // Int
            ("i", "_", Int, "obj_from_u64"),
            ("i", "0", Int, "obj_to_u64"),
            ("i", "1", Int, "obj_from_i64"),
            ("i", "2", Int, "obj_to_i64"),
            ("i", "3", Int, "obj_from_u128_pieces"),
            ("i", "4", Int, "obj_to_u128_lo64"),
            ("i", "5", Int, "obj_to_u128_hi64"),
            ("i", "6", Int, "obj_from_i128_pieces"),
            ("i", "7", Int, "obj_to_i128_lo64"),
            ("i", "8", Int, "obj_to_i128_hi64"),
            ("i", "9", Int, "obj_from_u256_pieces"),
            ("i", "a", Int, "u256_val_from_be_bytes"),
            ("i", "b", Int, "u256_val_to_be_bytes"),
            ("i", "c", Int, "obj_to_u256_hi_hi"),
            ("i", "d", Int, "obj_to_u256_hi_lo"),
            ("i", "e", Int, "obj_to_u256_lo_hi"),
            ("i", "f", Int, "obj_to_u256_lo_lo"),
            ("i", "g", Int, "obj_from_i256_pieces"),
            ("i", "h", Int, "i256_val_from_be_bytes"),
            ("i", "i", Int, "i256_val_to_be_bytes"),
            ("i", "j", Int, "obj_to_i256_hi_hi"),
            ("i", "k", Int, "obj_to_i256_hi_lo"),
            ("i", "l", Int, "obj_to_i256_lo_hi"),
            ("i", "m", Int, "obj_to_i256_lo_lo"),
            ("i", "n", Int, "u256_add"),
            ("i", "o", Int, "u256_sub"),
            ("i", "p", Int, "u256_mul"),
            ("i", "q", Int, "u256_div"),
            ("i", "r", Int, "u256_rem_euclid"),
            ("i", "s", Int, "u256_pow"),
            ("i", "t", Int, "u256_shl"),
            ("i", "u", Int, "u256_shr"),
            ("i", "v", Int, "i256_add"),
            ("i", "w", Int, "i256_sub"),
            ("i", "x", Int, "i256_mul"),
            ("i", "y", Int, "i256_div"),
            ("i", "z", Int, "i256_rem_euclid"),
            ("i", "A", Int, "i256_pow"),
            ("i", "B", Int, "i256_shl"),
            ("i", "C", Int, "i256_shr"),
            ("i", "D", Int, "timepoint_obj_from_u64"),
            ("i", "E", Int, "timepoint_obj_to_u64"),
            ("i", "F", Int, "duration_obj_from_u64"),
            ("i", "G", Int, "duration_obj_to_u64"),
            // Map
            ("m", "_", Map, "map_new"),
            ("m", "0", Map, "map_put"),
            ("m", "1", Map, "map_get"),
            ("m", "2", Map, "map_del"),
            ("m", "3", Map, "map_len"),
            ("m", "4", Map, "map_has"),
            ("m", "5", Map, "map_key_by_pos"),
            ("m", "6", Map, "map_val_by_pos"),
            ("m", "7", Map, "map_keys"),
            ("m", "8", Map, "map_values"),
            ("m", "9", Map, "map_new_from_linear_memory"),
            ("m", "a", Map, "map_unpack_to_linear_memory"),
            // Vec
            ("v", "_", Vec, "vec_new"),
            ("v", "0", Vec, "vec_put"),
            ("v", "1", Vec, "vec_get"),
            ("v", "2", Vec, "vec_del"),
            ("v", "3", Vec, "vec_len"),
            ("v", "4", Vec, "vec_push_front"),
            ("v", "5", Vec, "vec_pop_front"),
            ("v", "6", Vec, "vec_push_back"),
            ("v", "7", Vec, "vec_pop_back"),
            ("v", "8", Vec, "vec_front"),
            ("v", "9", Vec, "vec_back"),
            ("v", "a", Vec, "vec_insert"),
            ("v", "b", Vec, "vec_append"),
            ("v", "c", Vec, "vec_slice"),
            ("v", "d", Vec, "vec_first_index_of"),
            ("v", "e", Vec, "vec_last_index_of"),
            ("v", "f", Vec, "vec_binary_search"),
            ("v", "g", Vec, "vec_new_from_linear_memory"),
            ("v", "h", Vec, "vec_unpack_to_linear_memory"),
            // Ledger
            ("l", "_", Ledger, "put_contract_data"),
            ("l", "0", Ledger, "has_contract_data"),
            ("l", "1", Ledger, "get_contract_data"),
            ("l", "2", Ledger, "del_contract_data"),
            ("l", "3", Ledger, "create_contract"),
            ("l", "4", Ledger, "create_asset_contract"),
            ("l", "5", Ledger, "upload_wasm"),
            ("l", "6", Ledger, "update_current_contract_wasm"),
            ("l", "7", Ledger, "extend_contract_data_ttl"),
            (
                "l",
                "8",
                Ledger,
                "extend_current_contract_instance_and_code_ttl",
            ),
            ("l", "9", Ledger, "extend_contract_instance_and_code_ttl"),
            ("l", "a", Ledger, "get_contract_id"),
            ("l", "b", Ledger, "get_asset_contract_id"),
            ("l", "c", Ledger, "extend_contract_instance_ttl"),
            ("l", "d", Ledger, "extend_contract_code_ttl"),
            ("l", "e", Ledger, "create_contract_with_constructor"),
            // Call
            ("d", "_", Call, "call"),
            ("d", "0", Call, "try_call"),
            // Buf
            ("b", "_", Buf, "serialize_to_bytes"),
            ("b", "0", Buf, "deserialize_from_bytes"),
            ("b", "1", Buf, "bytes_copy_to_linear_memory"),
            ("b", "2", Buf, "bytes_copy_from_linear_memory"),
            ("b", "3", Buf, "bytes_new_from_linear_memory"),
            ("b", "4", Buf, "bytes_new"),
            ("b", "5", Buf, "bytes_put"),
            ("b", "6", Buf, "bytes_get"),
            ("b", "7", Buf, "bytes_del"),
            ("b", "8", Buf, "bytes_len"),
            ("b", "9", Buf, "bytes_push"),
            ("b", "a", Buf, "bytes_pop"),
            ("b", "b", Buf, "bytes_front"),
            ("b", "c", Buf, "bytes_back"),
            ("b", "d", Buf, "bytes_insert"),
            ("b", "e", Buf, "bytes_append"),
            ("b", "f", Buf, "bytes_slice"),
            ("b", "g", Buf, "string_copy_to_linear_memory"),
            ("b", "h", Buf, "symbol_copy_to_linear_memory"),
            ("b", "i", Buf, "string_new_from_linear_memory"),
            ("b", "j", Buf, "symbol_new_from_linear_memory"),
            ("b", "k", Buf, "string_len"),
            ("b", "l", Buf, "symbol_len"),
            ("b", "m", Buf, "symbol_index_in_linear_memory"),
            ("b", "n", Buf, "string_to_bytes"),
            ("b", "o", Buf, "bytes_to_string"),
            // Crypto
            ("c", "_", Crypto, "compute_hash_sha256"),
            ("c", "0", Crypto, "verify_sig_ed25519"),
            ("c", "1", Crypto, "compute_hash_keccak256"),
            ("c", "2", Crypto, "recover_key_ecdsa_secp256k1"),
            ("c", "3", Crypto, "verify_sig_ecdsa_secp256r1"),
            ("c", "4", Crypto, "bls12_381_check_g1_is_in_subgroup"),
            ("c", "5", Crypto, "bls12_381_g1_add"),
            ("c", "6", Crypto, "bls12_381_g1_mul"),
            ("c", "7", Crypto, "bls12_381_g1_msm"),
            ("c", "8", Crypto, "bls12_381_map_fp_to_g1"),
            ("c", "9", Crypto, "bls12_381_hash_to_g1"),
            ("c", "a", Crypto, "bls12_381_check_g2_is_in_subgroup"),
            ("c", "b", Crypto, "bls12_381_g2_add"),
            ("c", "c", Crypto, "bls12_381_g2_mul"),
            ("c", "d", Crypto, "bls12_381_g2_msm"),
            ("c", "e", Crypto, "bls12_381_map_fp2_to_g2"),
            ("c", "f", Crypto, "bls12_381_hash_to_g2"),
            ("c", "g", Crypto, "bls12_381_multi_pairing_check"),
            ("c", "h", Crypto, "bls12_381_fr_add"),
            ("c", "i", Crypto, "bls12_381_fr_sub"),
            ("c", "j", Crypto, "bls12_381_fr_mul"),
            ("c", "k", Crypto, "bls12_381_fr_pow"),
            ("c", "l", Crypto, "bls12_381_fr_inv"),
            ("c", "m", Crypto, "bn254_g1_add"),
            ("c", "n", Crypto, "bn254_g1_mul"),
            ("c", "o", Crypto, "bn254_multi_pairing_check"),
            // Address
            ("a", "_", Address, "require_auth_for_args"),
            ("a", "0", Address, "require_auth"),
            ("a", "1", Address, "strkey_to_address"),
            ("a", "2", Address, "address_to_strkey"),
            ("a", "3", Address, "authorize_as_curr_contract"),
            ("a", "4", Address, "get_address_from_muxed_address"),
            ("a", "5", Address, "get_id_from_muxed_address"),
            ("a", "6", Address, "get_address_executable"),
            // Prng
            ("p", "_", Prng, "prng_reseed"),
            ("p", "0", Prng, "prng_bytes_new"),
            ("p", "1", Prng, "prng_u64_in_inclusive_range"),
            ("p", "2", Prng, "prng_vec_shuffle"),
            // Test
            ("t", "_", Test, "dummy0"),
            ("t", "0", Test, "protocol_gated_dummy"),
        ]
    }

    #[test]
    fn full_dispatch_table_resolves_every_known_pair() {
        for (letter, code, expected_module, expected_name) in full_dispatch_table() {
            let resolved = resolve_host_function(letter, code)
                .unwrap_or_else(|| panic!("no resolution for ({letter}, {code})"));
            assert_eq!(resolved.0, expected_module, "module for ({letter}, {code})");
            assert_eq!(resolved.1, expected_name, "name for ({letter}, {code})");
        }
    }

    #[test]
    fn import_table_resolve_finds_entry_by_index() {
        let mut t = ImportTable::new();
        t.add("c", "_", 5);
        t.add("c", "0", 6);
        let entry = t.resolve(1).expect("entry at import_index 1");
        assert_eq!(entry.name, "verify_sig_ed25519");
        assert_eq!(entry.type_index, 6);
        assert!(t.resolve(99).is_none());
    }
}
