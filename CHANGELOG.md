# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Fixed — a validation guard no longer disappears from a small contract (issue #80)

A user-written `panic_with_error!` guard vanished from the decompiled output,
leaving no `todo!()` marker — the output simply did not have the check:

```rust
// source                              // decompiled, before
pub fn check(env: Env, decimals: u32)   pub fn check(decimals: u32) -> u32 {
    -> u32 {                                7
    if decimals != 7 {                  }
        panic_with_error!(
            &env, Error::BadDecimals);
    }
    decimals
}
```

`check(8)` fails in the original and returns `7` in the recompiled output, so
this is a silent-wrong of the worst kind: the guard is user logic, not SDK
marshalling the host re-inserts.

The cause is not the guard classifiers but the two recognizers that decide
whether a branch target is a contract-error tail. Both were written against the
shape a LARGE contract emits, where the SDK's error path is inlined flat. A
small contract has nothing to inline into, so the same `panic_with_error!`
lowers to a longer chain:

- `Env::fail_with_error` survives as a two-level wrapper
  (`Env::fail_with_error` -> `Guest::fail_with_error` -> the import), and both
  recognizers tested only ONE level with `function_calls_host`.
- It takes `&self`, so the receiver operand is frame-pointer arithmetic
  (`local.get <fp>; i32.const <off>; i32.add`), and its `Val` return is
  `drop`ped — making the tail seven nodes of shapes neither allowlist admitted.

Fixed in both (`pattern::lifter`): follow the wrapper chain
(`function_calls_host_in_chain`, new `FAIL_WRAPPER_CHAIN_DEPTH`), accept
`i32.add`/`i32.sub` over the operand leaves, accept the `drop` after the call,
and raise each `MAX_TAIL_LEN` from 6 to 8. All of it is still gated on reaching
`fail_with_error`, which remains the load-bearing test.

- **The guarded value reads as a number, not a raw `Val`.** With the guard back,
  `if decimals != 7` would have printed as `if decimals != 30064771072` (`7 <<
  32`): the `I64And` arm dropped the proven tag-clearing mask for a parameter,
  so the compare arm could no longer decode it. A spec-declared `u32` parameter
  now keeps that mask exactly as a `.len()` result does, and
  `decode_masked_len_compare` decodes it. A wrong value is as unfaithful as a
  dropped guard.
- **A multi-guard constructor recovers too.** Several guards before a storage
  write, each a `br_if` to a different block depth, had collapsed into two
  panics with mismatched errors and no write. All the guards, their correct
  errors, and the write are now restored. Fixing the tail recognizers exposed
  two further defects that the mangling had hidden; both are fixed here.
- **A panic guard keeps the contract's own polarity.** `invert_guard_clauses`
  used to "restore" a guard whose condition read `Le`/`Ge`, on the theory that
  the lifter had emitted `if Not(Gt) { panic }` and the constant folder had
  degraded it. It had not: `Not(Gt)` IS `Le`, so the fold was exact and
  flipping it back negated the guard — `if name.len() <= 0 { panic }` rendered
  as `if name.len() > 0 { panic }`, firing on the complement of the contract's
  own check. Stripping an explicit `Not` wrapper was wrong for the same reason.
  The panic-guard inversion is gone; the sound early-return inversion stays.
- **An inlined error tail no longer survives as an unconditional panic.**
  Layer B inlines a tail at each branch site and leaves the original in place
  for downstream passes, which only drop a stray panic that still has live work
  after it. A tail at the END of a level therefore survived and rendered as a
  `panic_with_error!` after the recovered body, making the function always
  fail. New `pattern::lifter::drop_unreachable_fail_tails` removes it as the
  dead code it is: the tail is reachable only by a branch to the block's exit
  depth (`branch_targets_depth` scans for any surviving `br`/`br_if`/`br_table`
  with WASM depth bookkeeping) or by falling out of the block's end
  (`diverges_at_end` requires `return` or a dead end). With both ruled out the
  tail is unreachable in the original wasm too.
- **New fixtures** `tests/fixtures/test_guard_panic.wasm`
  (`tests/fixtures-src/guard_panic`), covering the guarded value both returned
  and unused, and `tests/fixtures/test_guard_multi.wasm`
  (`tests/fixtures-src/guard_multi`), covering guards at different branch
  depths followed by a storage write. Kept as separate contracts so both stay
  small enough that the SDK has nothing to inline the error paths into.

Still open for this contract shape: an `i128` `<= 0` sign test lifts as
`== 0`, losing the negative case. Unrelated to the guard recovery and tracked
under issue #80.

Gates: compile-back 37/38 non-skipped (97%, `test_liquidity_pool` as on main),
corpus ratchet 358 unchanged, equivalence 0 divergences, 714 lib + 78
integration tests, no snapshot drift.


### Fixed — every value of a reused wasm local gets its own name (campaign stage 3c)

A wasm local is a slot, not a variable: it carries several values over a
function's life, and the lifter emits a binding for each of them under the
slot's own name. Two of them in nested scopes were rendered under one name, so
the inner `let` shadowed the outer binding:

```rust
let mut vp = CoreDataKeys::CoreData;              // slot 3: the storage key
if env.storage().instance().has(&CoreDataKeys::CoreData) {
    let vp = env.storage().instance()
        .get::<_, CoreData>(&CoreDataKeys::CoreData).unwrap();   // slot 3: the struct
    vp = vp.adm;                                  // slot 3: the admin
}
```

The write hit the immutable inner binding (E0384) across types (E0308), and
later reads of the slot took the wrong value. 19 sites in four contracts.

- **Each binding gets its own name** (`ir::optimizer::split_shadowed_bindings`,
  a new pass before name propagation). The reads inside a shadow's region point
  at the shadow; a write keeps going to the slot's **home** binding — the one an
  enclosing scope declared, and so the one a reader after the block sees. The
  example above becomes `let core_data = get::<_, CoreData>(..).unwrap(); ..;
  vp = core_data.adm;`.
- **Two guards keep it to what it can prove.** A `Loop`/`For` in the region that
  assigns the slot reads the previous iteration's value, which lives in the home
  binding, so that slot is left alone. So is a region that writes the slot from
  inside a block and then reads it again: that read wants the merge of two
  incoming values, the shadow's and the written one, and only one mutable
  variable models it (soroswap's `create_pair` builds the `PairWasmHash` key in
  the slot, writes an error sentinel over it when the key is absent, then reads
  the slot as its own read's key). The merge guard is lifted only when **both**
  incoming values are holes, because a read that follows the write lands on the
  home binding, which offers the home's value in place of the shadow's: exact
  when both are holes, a fabricated value when the home holds a vec, a literal
  or a field read. 37 of the corpus's 45 merge-guarded shadows have a hole on
  both sides and split; the other 8 keep today's rendering.
- **blend-emitter's swap functions read the right fields now.**
  `queue_swap_backstop`, `cancel_swap_backstop` and `swap_backstop` published
  `Swap { new_backstop, new_backstop_token: new_backstop.new_backstop_token,
  unlock_time: new_backstop.new_backstop }` — the fields read off the `Address`
  field that had taken the struct's name (issue #80, class B).
- **A key-adopted default is holed through a bound read.** Stage 4m6 accepted
  only a read assigned straight to the local; it now follows the read through a
  binding of its own and a field projection, so `let mut vp =
  CoreDataKeys::CoreData` is the honest `todo!()` it already was for the direct
  form. The key itself loses nothing — every use of it renders inline.
- **A literal written into a typed local is a hole.** soroban-domains reads the
  oracle address and then writes `oracle = 10` on a branch whose real value the
  lifter lost. An `Address` holds no integer, so the write was fabricated and a
  guaranteed error at once; it is now `todo!()`
  (`ir::correctness::husk_type_mismatched_assignments`, one corpus site).
- **A rename now reaches into every expression.** `rename_in_expr` ended in a
  catch-all `other => other`, so it returned `Shl`, `Some`, `Try`, `SretResult`,
  `ValTag` and `VecTryIterFold` unvisited: a rename reached the binding but not
  a read inside one of those, which left the read on the old name. The match is
  exhaustive now, so the compiler names the next variant that is added. It also
  recovers four values that were holes, among them blend-backstop's second
  `try_invoke_contract` target inside a `.get_tag()` (`todo!()` → `&emitter`).

Corpus hard errors 371 → 358: soroban-domains 63→56, blend-emitter 16→11,
fxdao-vault 5→3, and one rise — soroswap-CA4HEQTL 8→9, where refusing the
merge-guarded shadow restores the `E0308` that names the slot's two types, the
honest diagnosis of the live-range split below. `x = x.field` 19 → 1, the one
left being the merge the guard protects. Clean contracts still 2 of 24.
Equivalence:
147 functions, 3724 cases, **0 divergences**, hole cases 918 in 12 functions
(unchanged). Compile-back 97 %, only `test_liquidity_pool` failing, as on main
(#74). Restoration 89.6 → 89.4: the split brings back statements the merged
name had made dead (soroban-domains' `key.get(i)` parameter reads, 223 → 253
artifacts) and replaces adopted keys with holes, while soroswap (44 → 36
artifacts) and arb-bot (97.4 → 97.8 %, an invoke function symbol recovered)
improve. fxdao-vault's one clean function was clean only because its lost
default arm was rendered as the storage key: it is now a hole, and the function
is graded partial. Part of soroban-domains' artifact count is bookkeeping, not
recovery: once a read resolves to its binding, a hole that had been inlined at
each use is one named hole (`SubRecord(todo!())` → `SubRecord(var_3_4)`, where
`var_3_4` holds a hole), and 15 empty `if todo!() { } else { }` husks drop out.
Baseline refreshed.

Not addressed: a `let` may still shadow a function **parameter**
(`let min_duration = core_data.min_duration;` in soroban-domains' `init`). The
collision is minted by name propagation, whose first run deliberately passes no
reserved names so that parameter spills collapse onto the parameter; reserving
them there breaks that. One slot reused for values of different types in one
scope (soroban-domains' `node = caller` followed by `snapshot: node`) needs a
live-range split, not a rename.

### Fixed — storage reads get the type the contract writes (campaign stage 3b)

`env.storage().<kind>().get(&key)` is generic over the value type. Where the
lifter saw no typed use of the result, rustc could not infer it (E0282 /
E0283 / E0284); where the result flowed into a context of another type,
rustc inferred that type, and the recompiled contract decoded the stored
value as something it is not.

- **Reads are annotated `get::<_, T>(&key)`** when every typed write to the
  key in the contract (a parameter of a spec type, a struct or enum literal)
  stores the same `T`, and no decode of a read or typed consumer of the key
  disagrees. Keys compare by shape: an enum variant regardless of payload,
  or a bare symbol. A write whose key is unknown cancels the entries of its
  storage kind unless a decode confirms them. A write to the key whose value
  type is not proven (a lost value, a literal, a `Val`) cancels the key's
  entry outright: it may have stored anything. A decode of a read alone never
  types a key: the struct it names is what the original reads, but inside
  inlined helpers the lifter can attach the wrong key to the read (blend
  pools decode an auction under a key rendered `ResConfig`, blend-backstop a
  user balance under `PoolBalance`). New module `ir::stored_types`.
- **Wrong values this exposed are holes.** fxdao-oracle `resolution()` and
  `decimals()` returned the whole stored `CoreData` as their `u32`, and
  `base() -> Asset` / `assets() -> Vec<Asset>` the whole `AssetsData` (the
  bytecode returns one field, which the lifter lost): the read stays, the
  returned value is `todo!()`. All four were graded fully recovered. A read of a union followed by
  `.get(i)` is the SDK decoding the union's vec encoding, not a value
  (soroban-domains, 34 sites): the read stays, the value is `todo!()`. blend
  pools `accept_admin` started the admin from the storage key
  `symbol_short!("PropAdmin")`; that default is now a hole, as it already
  was for enum keys.
- **Moved values.** Struct-literal fields count as moves for the existing
  clone repair (comet's allowance key builds `AllowanceDataKey { from,
  spender }` twice).
- An annotation imports every type it names (`Vec<Address>`, `Symbol`, ..),
  not only its head.

Corpus hard errors 379 → 371: fxdao-oracle 12→5, phoenix 8→5, comet 19→17,
band 12→11, blend-fixed-pool and yieldblox 16→15 each. soroban-domains rose
56→63: its untyped reads had stopped type checking in those functions, and
typing them unmasked 10 `vp = vp.adm` (a second value reusing a binding, the
next step) and assignments that were already wrong (`oracle = 10` to an
`Address`). Equivalence: 0 divergences, unchanged. Still 2 of 24 contracts
compile. Restoration 90.0 → 89.6 (fxdao-oracle 98.4 → 91.4: the four
getters above; soroban-domains 88.5 → 87.2: the union decode fragments);
baseline refreshed.

### Fixed — wrong values that only showed up as compile errors (campaign stage 3a)

Each of these failed to type-check, so the corpus soundness gate counted it
as a compile error. Once the errors around them were fixed they would have
compiled and been silently wrong.

- **A storage key called as a contract.** The SDK's `storage.get` helper,
  monomorphised as `(sret, key)` writing `{present, value}`, is now lowered
  at the call to the call it is: `let b_token = get::<_, Address>(&key);`,
  with the flag read as `b_token.is_some()` and the value as
  `b_token.clone().unwrap()`. The typed read keeps the helper's stored-type
  check even where a caller only looks at the flag. Inlining it lost the
  stored value where the "absent" and "present" paths join and kept the key
  in the value slot, so blend-emitter rendered
  `invoke_contract(&symbol_short!("BToken"), ..)`, and the blend pools did
  the same with `BLNDTkn`. They now call the address stored under that key,
  read once. Three blend-backstop guards that were `if todo!() { panic!() }`
  are now `if !u_s_d_c_tkn.is_some() { panic!() }` on the typed read.
- **The contract's own address compared with an integer.**
  `if env.current_contract_address() != 0 { panic!() }` (15 sites in each
  blend pool) is a Val tag check whose operand was lost. The condition is
  now a hole and the panic is kept, as was already done for an `Address`
  parameter.
- **A literal returned where no literal can type.** `return 0` in
  `-> Address` and symbol literals returned from a `-> Map<..>` function
  (inlined helper returns, aqua-amm and aqua-rewards) are now holes. This
  extends the existing rule for scalar `Result` ok-types to `Address`,
  collections, user types, `Symbol`, `String` and `Bytes`.
- **A Val-encoded constant in a TTL argument.** fxdao-vault builds
  `extend_to` in Val space; it rendered as `sequence() + 2078076976496644`
  and is now `sequence() + 483840`.
- Corpus hard errors 433 → 379, no contract's count rose (blend-emitter
  28 → 16, blend-fixed-pool and yieldblox 30 → 16 each, aqua-amm 73 → 62,
  aqua-rewards 31 → 28). Mean restoration 90.1 % → 90.0 %: the fabricated
  values are now counted holes.

### Changed — the recovery report stops calling incomplete functions recovered (#81)

No decompiler output changes; only how it is graded and counted.

- **`todo!("decompiled return value")` is counted.** `ArtifactCounts` has a
  new `return_value` field, included in `total` and in `--report` under
  `holes`. The corpus has 89 of these markers, uncounted until now.
- **A function ending in that marker is not recovered.** The grader uses the
  same condition codegen uses to append it, so the two cannot drift. The lost
  value counts as one unknown node. If the function also writes, authorizes,
  publishes, calls and returns nothing, it is `LogicLost`: it does nothing
  and then traps.
- **Two signs of a truncated body with no marker at all** make a function
  `Partial`, each counted as one unknown node: a parameter that is never read
  (names starting with `_` are exempt), and a `Result<T, E>` whose every exit
  is an error.
- **The report says why.** `FnRecovery::incomplete` (and `incomplete` per
  function in `--report`) lists the signs in plain words, for example
  ``"parameter `amount` is never read"``.
- **Effect on the corpus numbers** (24 contracts, 481 functions):

  | | Before | After |
  |---|---:|---:|
  | Functions graded fully recovered | 189 | 151 |
  | Functions graded logic lost | 0 | 18 |
  | Holes counted | 1994 | 2083 |
  | Mean restoration | 92.7 % | 90.1 % |

  Of the 38 functions no longer graded fully recovered, 19 never read a
  parameter, 12 end in the lost-return-value marker, 6 show both, and 1
  (`phoenix-amm::accept_admin`) can only return an error. 8 of them are now
  `LogicLost`, as are 10 functions that were already `Partial`. The largest
  per-contract moves are unknown-oracle (6 → 1 fully recovered), lightecho
  (18 → 12) and blend-backstop (9 → 4). `benchmark-data/baseline.json` is
  refreshed; the lower number is the accurate one.
- A new test checks, on every corpus contract and fixture, that no function
  graded fully recovered has a `todo!` in its emitted body.

### Changed — the equivalence gate compares what a call does, not only what it returns

- **Effects.** A case now matches only if the return outcome and the call's
  effects are equal: the contract events published, the ledger afterwards
  (every entry of every contract), the lifetime of every entry, and under
  mocked auth the recorded authorizations. Effects are compared when both
  sides return a value; a failed call is rolled back by the host. A
  divergence names the part that differs (`events`, `storage`, `lifetime`,
  `auth`) and shows the first differing item from each side.
  Code entries count too: the lifetime of the code under test is compared
  under a name that does not depend on which code is installed, and a callee
  that is a copy of the contract under test gets its own code entry, so that
  extending one contract's code cannot extend the other's on one side only.
- **What the comparison covered** is reported and floored, so "effects are
  compared" cannot quietly mean "two empty lists were equal": a ledger write
  in 9 functions (85 matching cases), an authorization in 8 (30 cases). No
  matching case publishes an event or changes only a lifetime; see below.
- **What it found** (100 diverging cases in 3 functions, every one of which
  matched on its return value):
  - *A stored `true` / `false` was written as the integer `1` / `0`.*
    `test_errors::hello` stored an `i32` where the original stores a `bool`.
    A pipeline pass turned every stored bool constant into an integer; that
    is only right where the constant reaches the write through a wrapper
    that takes the value before encoding it (one fixture). A constant handed
    to `put_contract_data` is a `Val`, where 0 and 1 are `false` and `true`
    and nothing else. Fixed; six corpus outputs now store the bool the
    original stores (aqua-rewards kill switches, blend `Backfill` and
    `IsInit`, phoenix `MULTIHOP`, ybx `Final`).
  - *`transfer` published `to_muxed_id: None` for a muxed address.* The
    original publishes `to.id()`. In `test_events` the SDK's two-way
    argument switch (plain or muxed address) was walked as straight-line
    code and the plain-address result kept; in `test_events_ref` the value
    was simply unknown, and an unknown value in an `Option` field was
    rendered as `None`. Both are now an honest `todo!()`. Along the way an
    unknown event field is no longer filled with a parameter that already
    fills another field (`to_muxed_id: amount`).
- **Numbers.** 147 of 149 functions, 3724 cases, 0 divergences. Matching
  cases 3094 → 2806, on a returned value 1490 → 1298; functions matching on a
  value 129 → 127. Cases reaching a hole 630 → 918, in 12 functions (was 9):
  the two `transfer`s, and `test_events_ref::failed_transfer`, whose correct
  `None` came from the same guess. Both events fixtures leave the list of
  fixtures without a `todo!()`.
- **Open.** Recovering the muxed id (a value assigned under one arm of a
  switch) would bring the event comparison back onto matching cases.

### Changed — the equivalence gate runs functions against real state

- **States.** Every function now also runs in up to three states the original
  contract reaches, not only on a freshly registered instance. A state is
  found by calling the original: a call that returns a value and changes the
  ledger builds the next one (digicus: `config` → `add_repos` → `add_issues`).
  The recompiled contract is then put in the original's place in that same
  ledger, so a hole in a recompiled setter does not stop its getters from
  being compared against real data. Values stored by those calls are offered
  first as later arguments.
- **Callees and constructors.** A contract is registered behind the first
  `Address` candidate (a second copy of the original, or the fixture named
  in the gate's `CALLEES` table), so cross-contract calls complete. A
  constructor that needs arguments gets generated ones (`test_constructor`
  is executed for the first time).
- **Numbers.** 147 of 149 functions, 3724 cases, 0 divergences. Functions
  that match on a returned value: 118 → 129; 15 of them in a built state.
  Cases reaching a hole: 262 → 630 (the same functions, now in every state)
  in 9 functions (was 6). New limits: at most 9 functions may reach a hole,
  and at least 15 must match on a value in a built state.
- **What it found** (17 diverging cases in 3 functions, all fixed or holed):
  - *A guard whose error path is skipped by a branch was dropped.* digicus
    `config` accepted a second initialisation; the original fails with
    `AlreadyInitialized`. Fixed in the lifter. The same fix restores guards
    in eleven other outputs, where the panic was unconditional or missing
    (for example aqua `if em_pause_admins.first_index_of(admin).is_none()
    { panic_with_error!(Unauthorized) }`, reflector `AlreadyInitialized`).
  - *A getter returning one field of a stored struct was rebuilt as a read
    of that field's type.* unknown-oracle `get_price` and `get_admin` failed
    on every stored value. They keep the missing-key error; the value is an
    honest hole.
- Corpus errors stay at 433 (no per-contract change). Mean restoration
  92.8 % → 92.7 %: recovered guards whose condition is not recovered add
  `todo!()` conditions.
- Not done: comparing events and resulting storage (stage 1d); a token
  contract behind an address (no contract in the gate takes one yet).

### Changed — the equivalence gate executes every function, and what it found

- **Gate.** The equivalence harness generates arguments of every spec type
  (addresses, wide integers, bytes, strings, symbols, collections, tuples,
  options, and the contract's own structs and enums built from its spec) and
  runs each case with authorization enforced and mocked. Functions executed:
  74 → 146 of the 149 in contracts that recompile. Case selection now covers
  every candidate of every parameter instead of truncating the product.
- **Holes are visible at run time.** A `todo!()` in the recompiled contract
  fails with a reserved error code, so a case that reaches a hole is counted
  as unverified ("reached a hole": 262 cases in 6 functions), neither a match
  nor a divergence. The gate also reports how many matches returned a value
  (1287) as opposed to failing identically.
  Both numbers are gated: at most 262 cases may reach a hole, and at least
  118 functions must match on a returned value, so a change that replaces
  working bodies with holes fails the gate.
- **Getters keep their lifetime extension.** A rebuilt fallible getter
  dropped the `extend_ttl` the original performs on a successful read. The
  extension now goes in front of the rebuilt read
  (`if has(&key) { extend_ttl(..) }`), and a value-returning rebuild that
  cannot account for every extension in the body is declined.
- **What it found.** The first run had 404 diverging cases in 11 functions
  the integer-only gate had reported as matching. Divergences are back to 0,
  by fixing the cause or leaving an honest hole:
  - A `br_table` arm that leaves the switch was dropped when the default
    target was a case body, sending its discriminant to the default's code
    (`errors::hello`; role checks in the aqua contracts were unconditional
    panics).
  - An inlined helper's `return` was read as the caller returning, deleting
    whatever followed the call. It is now removed when state-changing code
    follows it.
  - A value block with two exits kept one exit's constant, folding real
    conditions away. That constant is now an unknown.
  - The whole-body fallible-getter rebuild also fired on setters; it is now
    limited to functions that only read.
  - A `try_invoke_contract` result used as a value is a hole instead of a
    fixed `.unwrap()` mapping, which panicked where the original returned an
    error. `import_contract` therefore carries two holes.
  - Unlowered `*_linear_memory` host calls and `require_auth` on a
    non-address render as holes; tuple structs are constructed positionally.
- **Honest numbers.** Corpus hard errors 303 → 433 and clean contracts 4 → 2:
  `fxdao-oracle` and `soroswap-CA4HEQTL` compiled cleanly only because their
  bodies had been truncated. The deleted code is back, partly unrecovered.
  `unknown-oracle` stays clean with holes in its four admin-gated setters
  where it used to return `Ok(())`.

### Changed — gate tooling and CI housekeeping

- The equivalence gate prints every skipped function with its reason, naming
  the parameter types that blocked it, and a count of functions blocked per
  type; `SOROBAN_RET_EQUIV_REPORT=<path>` writes the run as JSON. No change to
  what is executed (74 of 175 functions in the contracts that recompile).
- `SOROBAN_RET_ERRORS_DIR=<dir>` makes the corpus-soundness and compile-back
  scripts save each contract's generated source and compiler errors.
- CI: the macOS job moves to `macos-15` (the `macos-14` label is no longer
  accepted and the job never started); the job that pushed a refreshed
  baseline to protected `main` is replaced by a check that fails a PR whose
  committed `benchmark-data/baseline.json` is stale. The PR benchmark table
  now compares against the base commit's baseline, so a PR that refreshes the
  file still shows what it changed.
- Baseline refreshed: soroban-domains restoration 91.5 → 91.7 %, left behind
  by the #87 review fixes.

### Fixed — equivalence gate at zero divergences (#69)

- SDK `for x in vec.iter()` loops are rebuilt as `for i in 0..v.len()` from
  the proven iterator protocol. Each exit goes where the bytecode puts it: a
  failure inside the loop stays inside it, and the code on the exhaustion
  path (for example a size-limit check) runs once after it. The generic loop
  lift mapped every exit to `break`, which made in-loop failures
  unconditional.
- Loop-carried collections become `let mut` bindings updated in place
  (`m.set(k, v)`, `m.remove(k)`); a functional update stored directly is
  hoisted to the mutator followed by the store.
- The defaulting collection getter (`get(&KEY).unwrap_or(Map::new(&env))`) is
  enabled, typed from the contract's own signature where an export returns it.
- A guard whose body is only `return <value>` keeps its guard.
- `Map` accessors clone a by-value key that is used again.
- digicus: all four mutation loops recovered with no holes; equivalence
  divergences **2 → 0**. Corpus hard errors unchanged at 303.
- Review hardening: the loop is not rebuilt when anything but the frame
  pointer names the iterator's frame; carried locals are written as one
  parallel assignment (a swap stays a swap); a stored update is hoisted in
  place only when the binding has no other reader, else applied to a clone,
  and never when the storage key reads the collection. The optimizer no
  longer inlines a binding past a reassignment of a variable it reads (two
  corpus contracts keep such reads in their original order).

### Added — iterator-protocol proofs, stage 1 of loop recovery (#69)

- The evaluator can summarize a helper with all parameters symbolic (loads
  and stores through pointer parameters included). Two summaries are
  classified: the SDK `Vec` iterator `next` and the `Option` unwrap adapter
  that follows it. No decompiled output changes yet; this is the proof layer
  the `for`-loop recovery will consume.
- `DBG_ITER=1` lists the proven helpers and their in-loop call sites.

### Fixed — two of the four digicus divergences (#69)

- A zero-parameter export that is a pure computation over static data
  (digicus `version()` parses a version string in nested loops) is executed
  and rendered as its constant.
- Getter recovery by execution now covers `String::from_str` storage keys and
  the auth guard `get::<_, Address>(&KEY).unwrap_or_else(|| panic_with_error!(..))
  .require_auth()`. digicus `clear_repos` keeps its `Unauthorized` error and
  the storage write that was being dropped; fxdao-liquidity's `NotStarted`
  manager guards are recovered (15 → 10 errors).
- An empty `Map`/`Vec` stored directly pins its element types to `Val`.
- Equivalence divergences **4 → 2** (99.6 % match); corpus hard errors
  **304 → 303**. The remaining two (`get_repos`, `get_repos_and_issues`) need
  the proven empty-map default, which is withheld until the loops that mutate
  that map lift correctly.

### Fixed — soroswap factory compiles and matches the original (#80)

- `Result`-returning exports keep their error path. The SDK lowers
  `if ok { Ok(v) } else { Err(E) }` three ways (a tail value-`if`, an error
  preset in a local, an error carried out of a block by `br_if`); each now
  renders an explicit `Err(E)` return instead of silently falling through to
  the success path. Where the success value is path-dependent and unproven it
  is an explicit hole, never a guessed constant.
- Descriptor-pointer storage keys are resolved by executing the key
  constructor. The body-order string shortcut picked the wrong variant when the
  constructor's arms are not in discriminant order: soroswap factory read
  `TotalPairs` as `PairAddressesNIndexed`, and fxdao-oracle's `AssetsData`
  keys rendered as `AssetRecord`.
- A `.len()` compared against a raw `U32Val` constant decodes to the u32
  length (`len() != 32`, was `!= 137438953472`); 30 sites corpus-wide.
- `publish` with a lost (`todo!()`) topic or data pins the type rustc was
  falling back to, which a deny-by-default lint rejected.
- The `u32` getter that defaults on a missing key recovers as
  `get::<_, u32>(&KEY).unwrap_or(d)` (was `.unwrap()` or a hole).
- Clean-compiling corpus contracts **3 → 4**; the factory runs under the
  equivalence gate with 11 cases at 100 % match. Divergences stay at 4.

### Added — plain `.unwrap()` storage getters recovered by execution (#66)

- The getter classifier from #67 also accepts the protocol whose absent-key
  path is a bare trap, and renders it as one bound, typed
  `get::<_, T>(&KEY).unwrap()`. Soroswap factory's setter guard is now
  `get::<_, Address>(&DataKey::FeeToSetter).unwrap().require_auth()` (was
  `DataKey::PairWasmHash.require_auth()`, #80); blend-emitter, comet, ybx-claim
  and xycloans getters recover their values the same way.
- Corpus soundness ratchet **318 → 304** hard errors.

### Added — fallible storage getters recovered by execution (#67)

- The micro-evaluator has a protocol mode: storage `has`/`get` results are
  symbolic, `fail_with_error` and `unreachable` are path terminals, and every
  path of a helper is enumerated. A helper call is rewritten to
  `get::<_, T>(&KEY).unwrap_or_else(|| panic_with_error!(&env, E))` only when
  its complete path set is exactly that protocol. This recovers the aquarius
  `StorageError::ValueNotInitialized` getters in the shapes the window
  detector missed (selector- and descriptor-keyed `Address` getters, the `u32`
  fee getter): the lost `if todo!("unknown value") { panic_with_error!(..) }`
  guard and the lost value both come back as one typed, bound read.
- `DBG_PROTO=1` prints the path set of every constant-argument helper call
  that reads storage, as a census tool for the remaining guard classes (#66).

### Fixed — storage key rendered in place of the stored value (#67, #80)

- The key-constructor folds also claimed storage *getters*, so a call to the
  getter was replaced by its own key (`vec![&env, Symbol::new(&env,
  "RewardToken")]` where the stored `Address` belongs) with no `todo!()`. They
  now refuse any target that does more than build a value.
- A trapping getter read wrapped in a type annotation was treated as pure, so
  an unused one was deleted together with its panic-on-missing.
- Corpus soundness ratchet **326 → 318** hard errors (aqua-amm 55 → 46;
  aqua-rewards 24 → 25 is an audited unmask of a pre-existing render gap).
  Soroswap factory's four key-as-value sites are now honest holes: its getter
  uses plain `.unwrap()` and is not yet recovered.

### Added — per-contract recovery signals

- New public `soroban_ret::recovery` module: per-function recovery verdicts
  (`FnStatus::{Clean, Partial, LogicLost, Trivial, Missing}`) and
  unresolved-hole counts by category, computed from the contract in front of
  you with no corpus baseline involved. Surfaced on `DecompileResult::recovery`
  and `DecompileIR::recovery` (both `#[non_exhaustive]`, so this is additive),
  and as JSON via the new `soroban-ret --report` CLI flag. Intended for UIs that
  display decompiled source and need an honest per-contract confidence signal:
  the project's corpus-wide figures are corpus means and do not describe an
  individual contract.
- `soroban_ret::VERSION`, and an optional `serde` feature deriving
  `Serialize`/`Deserialize` on the recovery types.
- The report is `None` under `DecompileOptions::spec_only`, which skips body
  lifting: grading those empty bodies would report a fully-recovered contract
  as mostly "logic lost". `--report` rejects `--spec-only` for the same reason.
  An unmeasured result must not be mistakable for a measured one.
- The library now owns the canonical artifact counter. `soroban-ret-bench` and
  `soroban-ret-accuracy` each kept their own copy; both now delegate.

### Fixed — deceptively-clean function grading

- `FnStatus::Trivial` no longer covers a function whose empty body must still
  return a value. Codegen renders such a body as
  `todo!("decompiled function body")`, which traps at runtime, so grading it
  "fully recovered" was the deceptively-clean bug class. Two corpus functions
  were affected — `aqua-rewards::get_pools_plane` and `digicus::version`, the
  latter independently recorded by the equivalence harness as diverging
  (original returns `U32(0)`, recompiled traps). Both are now `LogicLost`.
  Corpus mean restoration moves **92.8 % → 92.4 %** with **no change to any
  decompiled output** (`artifacts_total` is identical for all 24 contracts);
  `benchmark-data/baseline.json` refreshed accordingly.

### Documentation

- `README.md` and `docs/pattern-coverage.md` re-measured against `main`: the
  compile-back gate is **38/39 = 97 %**, not the previously documented 38/38 =
  100 % (`test_liquidity_pool` regressed to 3 hard errors); the 4 equivalence
  divergences are `digicus`, not `test_alloc::num_list` (closed in #64). Added
  the corpus-soundness gate, refreshed every stale count, and replaced rotted
  line-number code references with greppable symbol names.

## [0.0.4] - 2026-07-26

The correctness-first release: two multi-tranche programs — memory-SSA-style
value recovery (#34, 16 tranches) and loop-structure recovery (#38, 7
tranches) — landed end to end, driving the mainnet-corpus hard-error ratchet
**1042 → 326** (−68%) and closing the behavioral-equivalence story to **4
divergences / 99.2% match**, every one an honest `todo!()` panic, none a
silently wrong value.

### Fixed — fabrication classes eliminated

- Lost `Map`/`Vec` values are no longer fabricated as empty collections;
  unrecoverable collections surface as honest holes (#36, #39).
- Symbol-builder loops no longer fabricate tag-only `SymbolSmall` keys: the
  DkEval const-loop evaluator recovers the **real** encoded symbols
  (`Symbol::new(&env, "AssetRecord")`, real invoke symbols) at lift time
  (#61, #62).
- `blend-backstop`'s `user_balance` recovered from a bare `panic!()` collapse
  to its real storage protocol (#33).
- Never-type (`!`) rooted values render so the panic semantics are exact and
  the output compiles — operators, reference args, and generic storage ops
  no longer produce guaranteed type errors (#54).
- Compiler-internal size arithmetic renders wrapping-exact (`count << 2`
  instead of `count * 4`) and dead vestigial counters are eliminated, so
  recompiled output no longer traps on overflow inputs where the original
  wrapped (#64).

### Added — recovery capabilities

- Storage-getter recovery classes: defaulting u128 getters, fallible struct
  getters with proven multi-field layouts and TTL protocols, value-returning
  getters (`.unwrap_or_else(|| panic_with_error!(..))`), and defaulting
  `Map`/`Vec` getters (#41–#47).
- Keyed `DataKey` recovery through frame-built descriptors: DkEval executes
  the real constructor bytecode against provenance-checked frame state, so
  wrong bare unit keys become true keyed variants
  (`Positions(user)`, `ResConfig(asset.clone())`) (#50, #51).
- Fallible storage-decode discriminants modeled (`OptionDecodeDisc`), folding
  re-encoded `.unwrap()` None-arms instead of leaving opaque scrutinees (#40).
- Loop-structure program (#57–#60, #62–#64): carried-seed admissibility,
  helper statement adoption, functional vec-accumulator recovery
  (`let mut vec = Vec::new(&env); … vec.push_back(x)`), const-loop
  evaluation, and the populate→push value relay — `test_alloc`'s `num_list`
  now decompiles **hole-free** and behaviorally matches the original on
  every generated input, including overflow cases.
- Reaching-definition groundwork: append-only slot-def journal with
  unique-def fill, if-result value joins, sound-join read poisoning backed by
  a corpus-measured taint census (#41, #48, #49).

### Changed

- Corpus soundness ratchet (hard compile errors across the 24-contract
  mainnet corpus): **1042 → 326**, with every intermediate rise an audited,
  documented honesty unmask. Three contracts now decompile to cleanly
  compiling Rust (digicus, fxdao-oracle, unknown-oracle).
- Codegen soundness sweep: registry-typed construct-field admissibility,
  adopted defaults, construct arity, semantic recoveries
  (`first_index_of(x) == 2` → `.is_none()`, `Bytes` append chains) (#52–#56).
- The functional-equivalence gate itemizes every divergence with inputs and
  both outcomes; ceiling ratcheted 8 → 6 → 4 across the loop program.

## [0.0.3] - 2026-07-02

The verification-infrastructure release: every later correctness claim is
backed by gates introduced here.

### Added

- `soroban-ret-equiv`: functional-equivalence gate — decompile → recompile →
  run both contracts in `soroban-env-host` → diff outcomes per input (#28).
- Mainnet corpus (24 deployed contracts) with restoration benchmark,
  structural-plausibility ratchet, and corpus soundness (hard-compile-error)
  ratchet (#22, #23, #25).
- Accuracy framework for IR-level assertions (#18).
- Checked-arithmetic recovery: `a.checked_add(b).ok_or(err)` restored from
  the overflow-unsafe `Ok(a + b)` collapse (behavioral match 82.3% → 87.3%)
  (#29).
- Fallible storage-getter recovery:
  `env.storage().<dur>().get::<_, T>(&key).ok_or(Error::V)` rebuilt from
  helper bytecode, error codes included (match 87.3% → 99.2%) (#30).
- Big-contract recovery batch: enum variants, i128 soft-arithmetic
  reconstruction, `Symbol`-from-linear-memory builders, router token-list
  validation, cross-contract invoke return types (aquarius −85% todos).

### Changed

- Correctness-first corpus compilation: host-call lowering, lost-value tail
  completion, correctness-guard husk passes (ratchet 1318 → 1042)
  (#26, #27, #31).

## [0.0.2] - 2026-05-29

### Added

- WASM-level CFG analysis distinguishing compiler safety-net `unreachable`
  traps from real panics (#13).
- Linear-memory points-to modeling of the shadow stack (#9).
- Iterative fixpoint dataflow over loops (#6).
- Guard-chain shadowing recovery (#10) and broader `Val` type support (#4).
- Base decompilation pipeline hardening and expanded test coverage (#3, #5).

## [0.0.1] - 2026-04-30

### Added

- Initial release: WASM parsing, Soroban spec/type recovery, base
  decompilation pipeline, CI workflows, and the publish process.

[0.0.4]: https://github.com/Inferara/soroban-ret/compare/v0.0.3...v0.0.4
[0.0.3]: https://github.com/Inferara/soroban-ret/compare/v0.0.2...v0.0.3
[0.0.2]: https://github.com/Inferara/soroban-ret/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/Inferara/soroban-ret/releases/tag/v0.0.1
