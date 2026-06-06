#!/usr/bin/env python3
#
# Fetch the curated Stellar *mainnet* smart-contract corpus used for
# decompiler testing/benchmarking, straight from the public ledger.
#
# Source: the Stellar Lab "contract-list" (mainnet), a hand-picked set of the
# most notable live protocols (Band/Reflector oracles, Soroswap/Phoenix/Aqua
# AMMs, the full Blend lending suite, FxDAO, Soroban Domains, SACs, ...).
#
# Pipeline (all via public Soroban RPC -- no Cloudflare-fronted scraping):
#   1. strkey-decode each `C...` contract id  -> 32-byte contract address
#   2. getLedgerEntries(ContractData / instance) -> ContractExecutable
#         * CONTRACT_EXECUTABLE_WASM         -> 32-byte code hash
#         * CONTRACT_EXECUTABLE_STELLAR_ASSET-> built-in SAC, no uploaded wasm
#   3. getLedgerEntries(ContractCode hash)   -> raw wasm bytes
#   4. integrity check: sha256(wasm) == code hash   (the hash *is* the sha256)
#
# Output: one `.wasm` per code-bearing contract + manifest.json in
#         benchmark-data/mainnet/ .
#
# Usage:  python3 scripts/fetch_benchmark_wasm.py
import base64, struct, hashlib, json, subprocess, sys, os, time, datetime, re

OUT_DIR = os.path.join(os.path.dirname(__file__), "..", "benchmark-data", "mainnet")
OUT_DIR = os.path.abspath(OUT_DIR)

# Public mainnet Soroban RPC endpoints, tried in order with failover.
RPCS = [
    "https://mainnet.sorobanrpc.com",
    "https://soroban-rpc.mainnet.stellar.gateway.fm",
    "https://rpc.ankr.com/stellar_soroban",
]

# Curated mainnet contract list (entity name, contract id) -- from Stellar Lab.
CONTRACTS = [
    ("Band Protocol",                 "CCQXWMZVM3KRTXTUPTN53YHL272QGKF32L7XEDNZ2S6OSUFK3NFBGG5M"),
    ("Lightecho",                     "CDOR3QD27WAAF4TK4MO33TGQXR6RPNANNVLOY277W2XVV6ZVJ6X6X42T"),
    ("Reflector",                     "CAFJZQWSED6YAWZU3GWRTOCNPPCGBN32L7QV43XX5LZLFTK6JLN34DLN"),
    ("Reflector",                     "CALI2BYU2JE6WVRUFYTS6MSBNEHGJ35P4AVCZYF3B6QOE3QKOB2PLE6M"),
    ("Soroban Domains",               "CATRNPHYKNXAPNLHEYH55REB6YSAJLGCPA4YM6L3WUKSZOPI77M2UMKI"),
    ("Soroswap",                      "CA4HEQTL2WPEUYKYKCDOHCDNIV4QHNJ7EL4J4NQ6VADP7SYHVRYZ7AW2"),
    ("Soroswap",                      "CAG5LRYQ5JVEUI5TEID72EYOVX44TTUJT5BQR2J6J77FH65PCCFAJDDH"),
    ("XycLoans",                      "CBV4OSTRMD2IJJYX3XRNIIVCNA5B2ZLHQMUEUJSKLAH45ONANQ2QV7QN"),
    ("Comet BLND-USDC AMM",           "CAS3FL6TLZKDGGSISDBWGGPXT3NRR4DYTZD7YOD3HMYO6LTJUVGRVEAM"),
    ("BLND Token",                    "CD25MNVTZDL4Y3XBCPCJXGXATV5WUHHOWMYFF4YBEGU5FCPGMYTVG5JY"),
    ("Blend Emitter",                 "CCOQM6S7ICIUWA225O5PSJWUBEMXGFSSW2PQFO6FP4DQEKMS5DASRGRR"),
    ("Blend Backstop",                "CAQQR5SWBXKIGZKPBZDH3KM5GQ5GUTPKB7JAFCINLZBC5WXPJKRG3IM7"),
    ("Blend Pool Factory",            "CDSYOAVXFY7SM5S64IZPPPYB4GVGGLMQVFREPSQQEZVIWXX5R23G4QSU"),
    ("Blend Fixed Pool",              "CAJJZSGMMM3PD7N33TAPHGBUGTB43OC73HVIK2L2G6BNGGGYOSSYBXBD"),
    ("Blend Yieldblox Pool",          "CCCCIQSDILITHMM7PBSLVDT5MISSY7R26MNZXCX4H7J5JQ5FPIYOGYFS"),
    ("Aqua AMM",                      "CBQDHNBFBZYE4MKPWBSJOPIYLW4SFSXAXUTSXJN76GNKYVYPCKWC6QUK"),
    ("FxDAO Liquidity locking pool",  "CDCART6WRSM2K4CKOAOB5YKUVBSJ6KLOVS7ZEJHA4OAQ2FXX7JOHLXIP"),
    ("FxDAO Vault",                   "CCUN4RXU5VNDHSF4S4RKV4ZJYMX2YWKOH6L4AKEKVNVDQ7HY5QIAO4UB"),
    ("FxDAO Oracle",                  "CB5OTV4GV24T5USEZHFVYGC3F4A4MPUQ3LN56E76UK2IT7MJ6QXW4TFS"),
    ("Unknown Oracle",                "CAWGFKEL4XSE7JHVZLFIXSDVK7HNI57VFU4OPVRV7NHECRXCZ3ZNDNTR"),
    ("Digicus",                       "CCZLARB46ZUHADIKNVOXFZUY4TO2J2USTA4ZGR3L3CAG45VYYXAUOTUB"),
    ("XLM SAC",                       "CAS3J7GYLGXMF6TDJBBYYSE3HQ6BBSMLNUQ34T6TZMYMW2EVH34XOWMA"),
    ("YBX Claim Contract",            "CBBM3WOKTRG7VRDZKDDZOSCQDPKFFTUIQWX5WD6UZ66XV7UFH2OSU2LM"),
    ("PHO SAC",                       "CBZ7M5B3Y4WWBZ5XK5UZCAFOEZ23KSSZXYECYX3IXM6E2JOLQC52DK32"),
    ("USDC SAC",                      "CCW67TSZV3SSS2HXMBQ5JFGCKJNXKZM7UQUWUZPUTHXSTZLEO7SJMI75"),
    ("Phoenix AMM",                   "CCLZRD4E72T7JCZCN3P7KNPYNXFYKQCL64ECLX7WP5GNVYPYJGU2IO2G"),
    ("Aqua Rewards",                  "CCY2PXGMKNQHO7WNYXEWX76L2C5BH3JUW3RCATGUYKY7QQTRILBZIFWV"),
    ("ARB Bot Contract",              "CCBVCCNPIFMCXW7S3GBM6IOQBD5TEUCSQ6WWJGB5VIXZCRVJJQHQQE23"),
]

# ---- XDR helpers -----------------------------------------------------------

def strkey_decode_contract(s):
    """`C...` strkey -> 32-byte contract address (validates version + CRC16)."""
    raw = base64.b32decode(s)                       # ver(1) + payload(32) + crc(2)
    if raw[0] != (2 << 3):                           # version byte 'C' (contract)
        raise ValueError(f"{s}: not a contract strkey (ver {raw[0]:#x})")
    payload, crc = raw[:-2], raw[-2:]
    if _crc16(payload) != crc:
        raise ValueError(f"{s}: bad checksum")
    return raw[1:33]

def _crc16(data):
    crc = 0
    for b in data:
        crc ^= b << 8
        for _ in range(8):
            crc = ((crc << 1) ^ 0x1021) & 0xFFFF if crc & 0x8000 else (crc << 1) & 0xFFFF
    return bytes([crc & 0xFF, (crc >> 8) & 0xFF])

def instance_key_b64(contract32):
    """LedgerKey for a contract's instance (ContractData / LedgerKeyContractInstance)."""
    x  = struct.pack(">I", 6)                        # CONTRACT_DATA
    x += struct.pack(">I", 1) + contract32          # SCAddress: SC_ADDRESS_TYPE_CONTRACT
    x += struct.pack(">I", 20)                       # SCVal: SCV_LEDGER_KEY_CONTRACT_INSTANCE
    x += struct.pack(">I", 1)                        # ContractDataDurability: PERSISTENT
    return base64.b64encode(x).decode()

def code_key_b64(hash_hex):
    """LedgerKey for ContractCode(hash)."""
    return base64.b64encode(struct.pack(">I", 7) + bytes.fromhex(hash_hex)).decode()

def parse_executable(xdr_b64):
    """Parse a ContractData instance entry -> ('wasm', hexhash) | ('stellar_asset', None)."""
    d = base64.b64decode(xdr_b64); o = [0]
    def u32():
        v = struct.unpack(">I", d[o[0]:o[0]+4])[0]; o[0] += 4; return v
    if u32() != 6:    raise ValueError("not CONTRACT_DATA")
    u32()                                            # ExtensionPoint (v0)
    u32(); o[0] += 32                                # SCAddress (type + 32-byte payload)
    if u32() != 20:   raise ValueError("key != LedgerKeyContractInstance")
    u32()                                            # durability
    if u32() != 19:   raise ValueError("val != ScContractInstance")
    edisc = u32()                                    # ContractExecutable
    if edisc == 0:    return ("wasm", d[o[0]:o[0]+32].hex())
    if edisc == 1:    return ("stellar_asset", None)
    raise ValueError(f"unknown executable discriminant {edisc}")

def extract_wasm(code_xdr_b64):
    """ContractCode entry XDR -> raw wasm bytes (opaque `code<>` field)."""
    d = base64.b64decode(code_xdr_b64)
    i = d.find(b"\x00asm")
    if i < 4: raise ValueError("wasm magic not found")
    length = struct.unpack(">I", d[i-4:i])[0]       # opaque length prefix precedes the magic
    return d[i:i+length]

# ---- RPC -------------------------------------------------------------------

def rpc_get_entries(keys, retries=4):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "getLedgerEntries",
                       "params": {"keys": keys}})
    last = None
    for attempt in range(retries):
        rpc = RPCS[attempt % len(RPCS)]
        try:
            p = subprocess.run(["curl", "-sS", "--max-time", "40",
                                "-H", "content-type: application/json", "-d", body, rpc],
                               capture_output=True, text=True)
            j = json.loads(p.stdout)
            if "result" in j:
                return j["result"].get("entries", [])
            last = j.get("error", p.stdout[:200])
        except Exception as e:
            last = str(e)
        time.sleep(1.5 * (attempt + 1))
    raise RuntimeError(f"RPC failed after {retries} tries: {last}")

# ---- main ------------------------------------------------------------------

def kebab(s):
    return re.sub(r"-+", "-", re.sub(r"[^a-z0-9]+", "-", s.lower())).strip("-")

def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    records = [{"entity": e, "contract_id": c, "contract32": strkey_decode_contract(c)}
               for e, c in CONTRACTS]

    # 1) batch-resolve every instance -> executable
    keymap = {instance_key_b64(r["contract32"]): r for r in records}
    print(f"Resolving {len(records)} contract instances via RPC ...")
    for ent in rpc_get_entries(list(keymap)):
        rec = keymap.get(ent["key"])
        if rec is not None:
            rec["kind"], rec["wasm_hash"] = parse_executable(ent["xdr"])
    for r in records:
        if "kind" not in r:
            r["kind"], r["wasm_hash"] = "missing", None   # archived / not found

    # 2) download unique wasm, verify, then write one file per code-bearing contract
    cache = {}                                            # hash -> wasm bytes
    for r in records:
        if r["kind"] != "wasm":
            r["wasm_file"], r["wasm_size"], r["verified"] = None, None, None
            continue
        h = r["wasm_hash"]
        if h not in cache:
            wasm = extract_wasm(rpc_get_entries([code_key_b64(h)])[0]["xdr"])
            ok = hashlib.sha256(wasm).hexdigest() == h
            if not ok:
                raise RuntimeError(f"sha256 mismatch for {h}")
            cache[h] = wasm
        wasm = cache[h]
        fname = f"{kebab(r['entity'])}-{r['contract_id'][:8]}.wasm"
        with open(os.path.join(OUT_DIR, fname), "wb") as fh:
            fh.write(wasm)
        r["wasm_file"], r["wasm_size"], r["verified"] = fname, len(wasm), True

    # 3) manifest
    by_hash = {}
    for r in records:
        if r["kind"] == "wasm":
            by_hash.setdefault(r["wasm_hash"], []).append(r["contract_id"])
    manifest = {
        "source": "Stellar Lab mainnet contract-list (curated)",
        "network": "public",
        "fetched_utc": datetime.datetime.utcnow().isoformat() + "Z",
        "rpc": RPCS[0],
        "method": "getLedgerEntries",
        "summary": {
            "total": len(records),
            "wasm_contracts": sum(1 for r in records if r["kind"] == "wasm"),
            "stellar_asset": sum(1 for r in records if r["kind"] == "stellar_asset"),
            "missing": sum(1 for r in records if r["kind"] == "missing"),
            "unique_wasm": len(by_hash),
        },
        "shared_wasm": {h: ids for h, ids in by_hash.items() if len(ids) > 1},
        "contracts": [
            {"entity": r["entity"], "contract_id": r["contract_id"], "executable": r["kind"],
             "wasm_hash": r["wasm_hash"], "wasm_file": r["wasm_file"],
             "wasm_size": r["wasm_size"], "sha256_verified": r["verified"]}
            for r in records
        ],
    }
    with open(os.path.join(OUT_DIR, "manifest.json"), "w") as fh:
        json.dump(manifest, fh, indent=2)

    # 4) report
    print(f"\nOutput dir: {OUT_DIR}")
    for r in records:
        if r["kind"] == "wasm":
            print(f"  OK    {r['wasm_size']:>8} B  {r['wasm_file']:<42} {r['entity']}")
        elif r["kind"] == "stellar_asset":
            print(f"  SAC   {'-':>8}    (built-in Stellar Asset Contract) {r['entity']}")
        else:
            print(f"  MISS  {'-':>8}    (instance not found / archived)   {r['entity']}")
    s = manifest["summary"]
    print(f"\n{s['wasm_contracts']} wasm  /  {s['unique_wasm']} unique  /  "
          f"{s['stellar_asset']} SAC  /  {s['missing']} missing  (of {s['total']})")

if __name__ == "__main__":
    main()
