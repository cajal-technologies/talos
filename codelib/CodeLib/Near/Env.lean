import CodeLib.Near.State

/-!
# NEAR host-function registry (`nearEnv`)

A `HostEnv NearState` modelling the NEAR Protocol host functions a Wasm
contract imports from module `"env"`. Semantics transcribed from nearcore
(`runtime/near-vm-runner/src/logic/{logic,vmstate}.rs`).

`HostEnv.funcs` is **positional**: index `i` resolves `call i` for
`i < imports.length`. So the env and a module's `imports` must agree on
order. `nearHostFns : List (ImportDecl × HostFn NearState)` is the source
of truth. Hand-built examples can use `nearImports`/`nearEnv` directly;
real compiled modules should call `resolveEnv?` so their declared subset
of imports is resolved by name/signature into the right positional order.

## Incremental strategy

Implemented tiers have real semantics; un-modelled crypto/promise entries
are **trapping stubs** (`unsupported`). A contract that calls an
un-modelled host function therefore *fails to verify loudly* (a trap the
proof can't discharge) rather than silently misbehaving — implement a tier
when a real contract needs it.

Gas is intentionally unmodelled: functional correctness ignores it, and
the interpreter's `fuel` already gives termination. Promises are deferred.
-/

namespace Wasm
namespace Near

/-- Byte capacity of `st`'s linear memory. -/
@[inline] def memBytes (st : Store NearState) : Nat := st.mem.pages * 65536

/-- Little-endian byte encoding of a NEAR `u128` value. Values above
`2^128 - 1` are truncated modulo `2^128`, matching fixed-width writes. -/
def leU128Bytes (n : Nat) : List UInt8 :=
  (List.range 16).map (fun i => UInt8.ofNat (n / 2 ^ (8 * i) % 256))

/-- Write bytes into guest memory, trapping when the range is out of bounds. -/
def writeMemBytes (name : String) (st : Store NearState) (ptr : UInt64)
    (data : List UInt8) : HostResult NearState :=
  if ptr.toNat + data.length > memBytes st then
    .Trap st s!"{name}: out of bounds"
  else
    .Return [] { st with mem := st.mem.writeBytes ptr.toNat data }

/-- Write a `u128` into guest memory as 16 little-endian bytes. -/
def writeU128 (name : String) (st : Store NearState) (ptr : UInt64)
    (n : Nat) : HostResult NearState :=
  writeMemBytes name st ptr (leU128Bytes n)

def contextRegisterFn (name : String) (select : NearContext → List UInt8) : HostFn NearState :=
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId] =>
        .Return [] { st with host := st.host.setRegisterIf regId (select st.host.context) }
      | _ => .Trap st s!"{name}: bad args" }

def contextU64Fn (name : String) (select : NearContext → UInt64) : HostFn NearState :=
  { params := [], results := [.i64]
    invoke := fun st args => match args with
      | [] => .Return [.i64 (select st.host.context)] st
      | _  => .Trap st s!"{name}: bad args" }

def contextU128MemFn (name : String) (select : NearContext → Nat) : HostFn NearState :=
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 ptr] => writeU128 name st ptr (select st.host.context)
      | _          => .Trap st s!"{name}: bad args" }

/-! ## Trapping stub for un-modelled host functions -/

/-- A host function that is declared (so import resolution succeeds) but
not yet modelled: every call traps. Keeps un-modelled functionality from
silently passing verification. -/
def unsupported (name : String) (params results : List ValueType) : HostFn NearState :=
  { params, results, invoke := fun st _ => .Trap st s!"unsupported NEAR host function: {name}" }

/-! ## Tier 0 — registers and I/O -/

/-- `input(register_id)`: write the raw call input into `register_id`. -/
def inputFn : HostFn NearState :=
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId] =>
        .Return [] { st with host := st.host.setRegisterIf regId st.host.context.input }
      | _ => .Trap st "input: bad args" }

/-- `read_register(register_id, ptr)`: copy the whole register into linear
memory at `ptr`. Traps if the register is unset or the write is OOB. -/
def readRegisterFn : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId, .i64 ptr] =>
        match st.host.registers regId.toNat with
        | none => .Trap st "read_register: invalid register"
        | some data =>
          if ptr.toNat + data.length > memBytes st then
            .Trap st "read_register: out of bounds"
          else
            .Return [] { st with mem := st.mem.writeBytes ptr.toNat data }
      | _ => .Trap st "read_register: bad args" }

/-- `register_len(register_id) -> u64`: byte length of the register, or
`u64Max` if the register is unset. -/
def registerLenFn : HostFn NearState :=
  { params := [.i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 regId] =>
        match st.host.registers regId.toNat with
        | none      => .Return [.i64 u64Max] st
        | some data => .Return [.i64 (UInt64.ofNat data.length)] st
      | _ => .Trap st "register_len: bad args" }

/-- `write_register(register_id, data_len, data_ptr)`: store
`data_len` bytes of linear memory into `register_id`. Reads memory
directly (no `u64Max` sentinel here). -/
def writeRegisterFn : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId, .i64 dataLen, .i64 dataPtr] =>
        if dataPtr.toNat + dataLen.toNat > memBytes st then
          .Trap st "write_register: out of bounds"
        else
          let data := st.mem.readBytes dataPtr.toNat dataLen.toNat
          .Return [] { st with host := st.host.setRegisterIf regId data }
      | _ => .Trap st "write_register: bad args" }

/-- `value_return(value_len, value_ptr)`: set the call's return data, read
through the memory-or-register convention. -/
def valueReturnFn : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 valLen, .i64 valPtr] =>
        match getMemOrReg st valPtr valLen with
        | none   => .Trap st "value_return: invalid register"
        | some v => .Return [] { st with host := { st.host with returnData := some v } }
      | _ => .Trap st "value_return: bad args" }

/-! ## Context and economics -/

def currentAccountIdFn : HostFn NearState :=
  contextRegisterFn "current_account_id" (·.currentAccountId)

def predecessorAccountIdFn : HostFn NearState :=
  contextRegisterFn "predecessor_account_id" (·.predecessorAccountId)

def signerAccountIdFn : HostFn NearState :=
  contextRegisterFn "signer_account_id" (·.signerAccountId)

def signerAccountPkFn : HostFn NearState :=
  contextRegisterFn "signer_account_pk" (·.signerAccountPk)

def blockIndexFn : HostFn NearState :=
  contextU64Fn "block_index" (·.blockIndex)

def blockTimestampFn : HostFn NearState :=
  contextU64Fn "block_timestamp" (·.blockTimestamp)

def epochHeightFn : HostFn NearState :=
  contextU64Fn "epoch_height" (·.epochHeight)

def storageUsageFn : HostFn NearState :=
  contextU64Fn "storage_usage" (·.storageUsage)

def accountBalanceFn : HostFn NearState :=
  contextU128MemFn "account_balance" (·.accountBalance)

def accountLockedBalanceFn : HostFn NearState :=
  contextU128MemFn "account_locked_balance" (·.accountLockedBalance)

def attachedDepositFn : HostFn NearState :=
  contextU128MemFn "attached_deposit" (·.attachedDeposit)

def prepaidGasFn : HostFn NearState :=
  contextU64Fn "prepaid_gas" (·.prepaidGas)

def usedGasFn : HostFn NearState :=
  contextU64Fn "used_gas" (·.usedGas)

def validatorStakeFn : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 accountIdLen, .i64 accountIdPtr, .i64 stakePtr] =>
        match getMemOrReg st accountIdPtr accountIdLen with
        | none => .Trap st "validator_stake: invalid account id"
        | some accountId =>
          writeU128 "validator_stake" st stakePtr (st.host.context.validatorStake accountId)
      | _ => .Trap st "validator_stake: bad args" }

def validatorTotalStakeFn : HostFn NearState :=
  contextU128MemFn "validator_total_stake" (·.validatorTotalStake)

/-! ## Crypto and math, modelled as pure host-state hooks -/

def digestFn (name : String) (hash : NearState → List UInt8 → List UInt8) : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 valueLen, .i64 valuePtr, .i64 regId] =>
        match getMemOrReg st valuePtr valueLen with
        | none => .Trap st s!"{name}: invalid input"
        | some value =>
          .Return [] { st with host := st.host.setRegisterIf regId (hash st.host value) }
      | _ => .Trap st s!"{name}: bad args" }

def sha256Fn : HostFn NearState :=
  digestFn "sha256" (·.sha256)

def keccak256Fn : HostFn NearState :=
  digestFn "keccak256" (·.keccak256)

def keccak512Fn : HostFn NearState :=
  digestFn "keccak512" (·.keccak512)

def ripemd160Fn : HostFn NearState :=
  digestFn "ripemd160" (·.ripemd160)

def randomSeedFn : HostFn NearState :=
  { params := [.i64], results := []
    invoke := fun st args => match args with
      | [.i64 regId] =>
        .Return [] { st with host := st.host.setRegisterIf regId st.host.randomSeed }
      | _ => .Trap st "random_seed: bad args" }

def ecrecoverFn : HostFn NearState :=
  { params := [.i64, .i64, .i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 hashLen, .i64 hashPtr, .i64 sigLen, .i64 sigPtr, .i64 v, .i64 malleabilityFlag] =>
        match getMemOrReg st hashPtr hashLen, getMemOrReg st sigPtr sigLen with
        | some hash, some sig =>
          match st.host.ecrecover hash sig v (malleabilityFlag != 0) with
          | some pk =>
            .Return [.i64 1] { st with host := st.host.setRegisterIf 0 pk }
          | none => .Return [.i64 0] st
        | _, _ => .Trap st "ecrecover: invalid input"
      | _ => .Trap st "ecrecover: bad args" }

def ed25519VerifyFn : HostFn NearState :=
  { params := [.i64, .i64, .i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 sigLen, .i64 sigPtr, .i64 msgLen, .i64 msgPtr, .i64 pkLen, .i64 pkPtr] =>
        match getMemOrReg st sigPtr sigLen, getMemOrReg st msgPtr msgLen, getMemOrReg st pkPtr pkLen with
        | some sig, some msg, some pk =>
          .Return [.i64 (if st.host.ed25519Verify sig msg pk then 1 else 0)] st
        | _, _, _ => .Trap st "ed25519_verify: invalid input"
      | _ => .Trap st "ed25519_verify: bad args" }

/-! ## Tier 1 — storage

Return convention (uniform): `0` = key was absent, `1` = key was present.
On the present case the previous/read value is written to `register_id`
unless `register_id = u64Max`, which discards the output. -/

/-- `storage_write(key_len, key_ptr, value_len, value_ptr, register_id) -> u64`.
Inserts `key ↦ value`. If a value existed it is evicted into
`register_id` and `1` is returned; otherwise `0`. -/
def storageWriteFn : HostFn NearState :=
  { params := [.i64, .i64, .i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 keyLen, .i64 keyPtr, .i64 valLen, .i64 valPtr, .i64 regId] =>
        match getMemOrReg st keyPtr keyLen, getMemOrReg st valPtr valLen with
        | some key, some val =>
          match st.host.storage key with
          | some old =>
            .Return [.i64 1]
              { st with host := (st.host.setRegisterIf regId old).setStorage key val }
          | none =>
            .Return [.i64 0] { st with host := st.host.setStorage key val }
        | _, _ => .Trap st "storage_write: invalid register"
      | _ => .Trap st "storage_write: bad args" }

/-- `storage_read(key_len, key_ptr, register_id) -> u64`. On hit, copies the
value into `register_id` and returns `1`; on miss returns `0` and leaves
the register untouched. -/
def storageReadFn : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 keyLen, .i64 keyPtr, .i64 regId] =>
        match getMemOrReg st keyPtr keyLen with
        | none => .Trap st "storage_read: invalid register"
        | some key =>
          match st.host.storage key with
          | some v => .Return [.i64 1] { st with host := st.host.setRegisterIf regId v }
          | none   => .Return [.i64 0] st
      | _ => .Trap st "storage_read: bad args" }

/-- `storage_remove(key_len, key_ptr, register_id) -> u64`. On hit, copies
the removed value into `register_id`, removes the key and returns `1`; on
miss returns `0`. -/
def storageRemoveFn : HostFn NearState :=
  { params := [.i64, .i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 keyLen, .i64 keyPtr, .i64 regId] =>
        match getMemOrReg st keyPtr keyLen with
        | none => .Trap st "storage_remove: invalid register"
        | some key =>
          match st.host.storage key with
          | some v =>
            .Return [.i64 1]
              { st with host := (st.host.setRegisterIf regId v).removeStorage key }
          | none => .Return [.i64 0] st
      | _ => .Trap st "storage_remove: bad args" }

/-- `storage_has_key(key_len, key_ptr) -> u64`: `1` if present, else `0`. -/
def storageHasKeyFn : HostFn NearState :=
  { params := [.i64, .i64], results := [.i64]
    invoke := fun st args => match args with
      | [.i64 keyLen, .i64 keyPtr] =>
        match getMemOrReg st keyPtr keyLen with
        | none => .Trap st "storage_has_key: invalid register"
        | some key => .Return [.i64 (if (st.host.storage key).isSome then 1 else 0)] st
      | _ => .Trap st "storage_has_key: bad args" }

/-- `panic()`: always traps. -/
def panicFn : HostFn NearState :=
  { invoke := fun st _ => .Trap st "explicit guest panic" }

/-- `panic_utf8(len, ptr)`: always traps (message content not modelled). -/
def panicUtf8Fn : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st _ => .Trap st "guest panic (utf8)" }

def logUtf8Fn : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 len, .i64 ptr] =>
        match getMemOrReg st ptr len with
        | none => .Trap st "log_utf8: invalid memory"
        | some msg => .Return [] { st with host := { st.host with logs := st.host.logs ++ [msg] } }
      | _ => .Trap st "log_utf8: bad args" }

def logUtf16Fn : HostFn NearState :=
  { params := [.i64, .i64], results := []
    invoke := fun st args => match args with
      | [.i64 len, .i64 ptr] =>
        match getMemOrReg st ptr len with
        | none => .Trap st "log_utf16: invalid memory"
        | some msg => .Return [] { st with host := { st.host with logs := st.host.logs ++ [msg] } }
      | _ => .Trap st "log_utf16: bad args" }

def abortFn : HostFn NearState :=
  { params := [.i32, .i32, .i32, .i32], results := []
    invoke := fun st _ => .Trap st "guest abort" }

/-! ## The registry — single source of truth -/

private def imp (name : String) (params results : List ValueType) : ImportDecl :=
  { «module» := "env", name, params, results }

/-- Canonical ordered list of NEAR host functions, paired with their import
declarations. Index in this list is the unified function index used by
`call`. Real entries come first; trapping stubs fill out the common
remainder so contracts importing them resolve (and then fail loudly). -/
def nearHostFns : List (ImportDecl × HostFn NearState) :=
  [ (imp "input"                [.i64] [],                          inputFn)          -- 0
  , (imp "read_register"        [.i64, .i64] [],                    readRegisterFn)   -- 1
  , (imp "register_len"         [.i64] [.i64],                      registerLenFn)    -- 2
  , (imp "write_register"       [.i64, .i64, .i64] [],              writeRegisterFn)  -- 3
  , (imp "value_return"         [.i64, .i64] [],                    valueReturnFn)    -- 4
  , (imp "storage_write"        [.i64, .i64, .i64, .i64, .i64] [.i64], storageWriteFn)-- 5
  , (imp "storage_read"         [.i64, .i64, .i64] [.i64],          storageReadFn)    -- 6
  , (imp "storage_remove"       [.i64, .i64, .i64] [.i64],          storageRemoveFn)  -- 7
  , (imp "storage_has_key"      [.i64, .i64] [.i64],                storageHasKeyFn)  -- 8
  , (imp "panic"                [] [],                              panicFn)          -- 9
  , (imp "panic_utf8"           [.i64, .i64] [],                    panicUtf8Fn)      -- 10
  , (imp "current_account_id"     [.i64] [],     currentAccountIdFn)                  -- 11
  , (imp "predecessor_account_id" [.i64] [],     predecessorAccountIdFn)              -- 12
  , (imp "signer_account_id"      [.i64] [],     signerAccountIdFn)                   -- 13
  , (imp "attached_deposit"       [.i64] [],     attachedDepositFn)                   -- 14
  , (imp "log_utf8"               [.i64, .i64] [], logUtf8Fn)                         -- 15
  , (imp "sha256"           [.i64, .i64, .i64] [], sha256Fn)                                     -- 16
  , (imp "keccak256"        [.i64, .i64, .i64] [], keccak256Fn)                                  -- 17
  , (imp "signer_account_pk"      [.i64] [],     signerAccountPkFn)
  , (imp "block_index"            [] [.i64],     blockIndexFn)
  , (imp "block_height"           [] [.i64],     blockIndexFn)
  , (imp "block_timestamp"        [] [.i64],     blockTimestampFn)
  , (imp "epoch_height"           [] [.i64],     epochHeightFn)
  , (imp "storage_usage"          [] [.i64],     storageUsageFn)
  , (imp "account_balance"        [.i64] [],     accountBalanceFn)
  , (imp "account_locked_balance" [.i64] [],     accountLockedBalanceFn)
  , (imp "prepaid_gas"            [] [.i64],     prepaidGasFn)
  , (imp "used_gas"               [] [.i64],     usedGasFn)
  , (imp "validator_stake"        [.i64, .i64, .i64] [], validatorStakeFn)
  , (imp "validator_total_stake"  [.i64] [],     validatorTotalStakeFn)
  , (imp "log_utf16"              [.i64, .i64] [], logUtf16Fn)
  , (imp "abort"                  [.i32, .i32, .i32, .i32] [], abortFn)
    -- Remaining trapping stubs (un-modelled tier): promises.
  , (imp "keccak512"        [.i64, .i64, .i64] [], keccak512Fn)
  , (imp "ripemd160"        [.i64, .i64, .i64] [], ripemd160Fn)
  , (imp "ecrecover"        [.i64, .i64, .i64, .i64, .i64, .i64] [.i64], ecrecoverFn)
  , (imp "ed25519_verify"   [.i64, .i64, .i64, .i64, .i64, .i64] [.i64], ed25519VerifyFn)
  , (imp "random_seed"      [.i64] [], randomSeedFn)
  , (imp "promise_results_count" [] [.i64], unsupported "promise_results_count" [] [.i64])
  , (imp "promise_result" [.i64, .i64] [.i64], unsupported "promise_result" [.i64, .i64] [.i64])
  , (imp "promise_return" [.i64] [], unsupported "promise_return" [.i64] []) ]

/-- Import declarations, in canonical order. A NEAR contract module sets
`imports := nearImports`. -/
def nearImports : List ImportDecl := nearHostFns.map Prod.fst

/-- The NEAR host environment. `funcs` aligns positionally with
`nearImports`. -/
def nearEnv : HostEnv NearState := { funcs := nearHostFns.map Prod.snd }

/-- Import declarations match by module, name, params, and results. -/
def importMatches (a b : ImportDecl) : Bool :=
  a.«module» == b.«module» && a.name == b.name &&
    a.params == b.params && a.results == b.results

/-- Resolve one declared import to its NEAR host function. -/
def resolveImport? (decl : ImportDecl) : Option (HostFn NearState) :=
  (nearHostFns.find? (fun p => importMatches p.fst decl)).map Prod.snd

/-- Resolve the exact subset/order of imports declared by a real module into
a positional `HostEnv`. Returns `none` when an import is not a known NEAR
function with the declared signature. -/
def resolveImports? : List ImportDecl → Option (HostEnv NearState)
  | [] => some { funcs := [] }
  | decl :: rest =>
    match resolveImport? decl, resolveImports? rest with
    | some hf, some env => some { funcs := hf :: env.funcs }
    | _, _ => none

/-- Resolve a module's imports into a positional NEAR host environment. -/
def resolveEnv? (m : Module) : Option (HostEnv NearState) :=
  resolveImports? m.imports

/-- Number of host imports; a contract's own functions start at this
unified index. -/
def importCount : Nat := nearImports.length

end Near
end Wasm
