import CodeLib.Near.State

/-!
# NEAR host-function registry (`nearEnv`)

A `HostEnv NearState` modelling the NEAR Protocol host functions a Wasm
contract imports from module `"env"`. Semantics transcribed from nearcore
(`runtime/near-vm-runner/src/logic/{logic,vmstate}.rs`).

`HostEnv.funcs` is **positional**: index `i` resolves `call i` for
`i < imports.length`. So the env and a module's `imports` must agree on
order. To keep them in lockstep there is a single source of truth,
`nearHostFns : List (ImportDecl × HostFn NearState)`, from which both
`nearImports` and `nearEnv` are projected. A hand-built contract sets
`imports := nearImports` and calls host functions by their canonical index
(`input = 0`, `read_register = 1`, …, `storage_write = 5`, …).

## Incremental strategy

Every NEAR host function appears in the registry. The ones needed so far
(Tier 0 I/O + storage) have real semantics; everything else is a
**trapping stub** (`unsupported`). A contract that calls an un-modelled
host function therefore *fails to verify loudly* (a trap the proof can't
discharge) rather than silently misbehaving — implement a tier when a real
contract needs it.

Gas is intentionally unmodelled: functional correctness ignores it, and
the interpreter's `fuel` already gives termination. Promises are deferred.
-/

namespace Wasm
namespace Near

/-- Byte capacity of `st`'s linear memory. -/
@[inline] def memBytes (st : Store NearState) : Nat := st.mem.pages * 65536

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
        .Return [] { st with host := st.host.setRegister regId.toNat st.host.context.input }
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
          .Return [] { st with host := st.host.setRegister regId.toNat data }
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

/-! ## Tier 1 — storage

Return convention (uniform): `0` = key was absent, `1` = key was present.
On the present case the previous/read value is written to `register_id`
(unconditionally — no sentinel on the output register). -/

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
              { st with host := (st.host.setRegister regId.toNat old).setStorage key val }
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
          | some v => .Return [.i64 1] { st with host := st.host.setRegister regId.toNat v }
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
              { st with host := (st.host.setRegister regId.toNat v).removeStorage key }
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
    -- Trapping stubs (un-modelled tiers): context, logging, crypto.
  , (imp "current_account_id"     [.i64] [],     unsupported "current_account_id" [.i64] [])      -- 11
  , (imp "predecessor_account_id" [.i64] [],     unsupported "predecessor_account_id" [.i64] [])  -- 12
  , (imp "signer_account_id"      [.i64] [],     unsupported "signer_account_id" [.i64] [])       -- 13
  , (imp "attached_deposit"       [.i64] [],     unsupported "attached_deposit" [.i64] [])        -- 14
  , (imp "log_utf8"               [.i64, .i64] [], unsupported "log_utf8" [.i64, .i64] [])        -- 15
  , (imp "sha256"           [.i64, .i64, .i64] [], unsupported "sha256" [.i64, .i64, .i64] [])    -- 16
  , (imp "keccak256"        [.i64, .i64, .i64] [], unsupported "keccak256" [.i64, .i64, .i64] []) ]-- 17

/-- Import declarations, in canonical order. A NEAR contract module sets
`imports := nearImports`. -/
def nearImports : List ImportDecl := nearHostFns.map Prod.fst

/-- The NEAR host environment. `funcs` aligns positionally with
`nearImports`. -/
def nearEnv : HostEnv NearState := { funcs := nearHostFns.map Prod.snd }

/-- Number of host imports; a contract's own functions start at this
unified index. -/
def importCount : Nat := nearImports.length

end Near
end Wasm
