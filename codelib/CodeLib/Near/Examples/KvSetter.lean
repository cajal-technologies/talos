import CodeLib.Near.Env

/-!
# Example: a NEAR key-value setter

A hand-built NEAR contract with one method, `set`. It follows the real
NEAR ABI end to end:

1. `input(0)` — deposit the raw call input into register 0.
2. `read_register(0, 0)` — copy that input into linear memory at offset 0.
3. parse a **length-prefixed** `(key, value)` out of memory, where the
   encoding is `le32(key.len) ++ key ++ le32(val.len) ++ val`.
4. `storage_write(key_len, key_ptr, value_len, value_ptr, 1)` — store it.

The interesting property (`SetSpec`) is a *before/after projection* of the
NEAR storage trie plus a *frame condition*: after the call the chosen key
maps to the value, and every other key is unchanged. The `∀ k` in the
frame is the "iterate over all keys" reasoning the storage-as-a-function
model makes free — no Wasm enumeration needed.

Following the repo convention (cf. `XorSum/Spec.lean`), `SetSpec` is stated
as a `def … : Prop`; its general proof rests on linear-memory framing
lemmas (`read32`/`readBytes` through `writeBytes`) and is the next
milestone. The `native_decide` theorems below prove the *whole pipeline*
— registers, the memory-or-register sentinel, length-prefix parsing, and
`storage_write` semantics — executes correctly on concrete inputs.
-/

namespace Wasm
namespace Near
namespace KvSetter

open Wasm

/-! ## The contract -/

/-- Body of `set`. Operand pushes are arranged so each host call receives
its arguments first-declared-first under the wasm calling convention. -/
def setBody : Program :=
  [ -- input(0): register 0 ← call input
    .constI64 0, .call 0,
    -- read_register(0, 0): memory[0..] ← register 0
    .constI64 0, .constI64 0, .call 1,
    -- storage_write(keyLen, keyPtr, valLen, valPtr, 1):
    -- arg1 keyLen = (u64) mem.read32(0)
    .const 0, .load32 0, .extendUI32,
    -- arg2 keyPtr = 4
    .constI64 4,
    -- arg3 valLen = (u64) mem.read32(keyLen + 4)
    .const 0, .load32 0, .load32 4, .extendUI32,
    -- arg4 valPtr = keyLen + 8
    .const 0, .load32 0, .extendUI32, .constI64 8, .addI64,
    -- arg5 register_id = 1
    .constI64 1,
    -- call storage_write (canonical index 5), discard the u64 result
    .call 5, .drop ]

/-- The contract module. Imports the full canonical NEAR host set, so the
contract's own `set` sits at unified index `importCount`. -/
def «module» : Module :=
  { imports := nearImports
    funcs   := [{ params := [], locals := [], body := setBody, results := [] }]
    memory  := some { pagesMin := 1 }
    exports := [{ name := "set", funcIdx := importCount }] }

/-- Unified function index of the exported `set`. -/
def setIdx : Nat := importCount

/-! ## Length-prefix encoding -/

/-- Little-endian 4-byte encoding of a length. -/
def le32 (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256),
    UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 16777216 % 256) ]

/-- The contract's input wire format: `le32(|key|) ++ key ++ le32(|val|) ++ val`. -/
def encodeKV (key val : List UInt8) : List UInt8 :=
  le32 key.length ++ key ++ le32 val.length ++ val

/-! ## Specification (stated; general proof is the next milestone) -/

/-- **Spec for `set`.** For any incoming NEAR state whose `input` is the
length-prefixed encoding of `(key, val)` (with sizes that fit a u32 and the
single memory page), the call terminates and:

* *projection after the call:* `storage[key] = val`;
* *frame condition:* every other key is unchanged from the incoming state.

The store is pinned to the module's `initialStore` (memory + globals set up
by instantiation) with the NEAR projection injected as `host := ns`, per
the repo convention for memory-touching specs. -/
def SetSpec : Prop :=
  ∀ (ns : NearState) (key val : List UInt8),
    key.length < 4294967296 → val.length < 4294967296 →
    (encodeKV key val).length ≤ 65536 →
    ns.context.input = encodeKV key val →
    TerminatesWith nearEnv «module» setIdx
      { («module».initialStore : Store NearState) with host := ns } []
      (fun st _ =>
        st.host.storage key = some val ∧
        (∀ k, k ≠ key → st.host.storage k = ns.storage k))

/-! ## Concrete end-to-end validation

These run the contract through the interpreter on a concrete input and
check the resulting storage projection, exercising the entire host
pipeline. They are full proofs (`native_decide`), not statements. -/

/-- Run `set` from the module's initial store with NEAR projection `ns`. -/
def runFrom (ns : NearState) : Result NearState :=
  run 100 «module» setIdx { («module».initialStore : Store NearState) with host := ns } [] nearEnv

/-- Storage projection of `key` after running `set` (or `none` if the run
did not succeed). -/
def storedAt (ns : NearState) (key : List UInt8) : Option (List UInt8) :=
  match runFrom ns with
  | .Success _ st => st.host.storage key
  | _             => none

/-- Did the run succeed with no return values? -/
def ranOk (ns : NearState) : Bool :=
  match runFrom ns with
  | .Success [] _ => true
  | _             => false

/-- A concrete incoming state: input encodes key `[1,2]` ↦ value `[7,8,9]`. -/
def demoNs : NearState := { context := { input := encodeKV [1, 2] [7, 8, 9] } }

/-- The call succeeds and returns nothing. -/
theorem demo_ranOk : ranOk demoNs = true := by native_decide

/-- After the call, the parsed key holds the parsed value. -/
theorem demo_stored : storedAt demoNs [1, 2] = some [7, 8, 9] := by native_decide

/-- Frame: a key that was not written stays absent. -/
theorem demo_frame_absent : storedAt demoNs [9, 9] = none := by native_decide

/-- Frame against a non-empty incoming store: a pre-existing unrelated key
survives the write untouched. -/
def demoNs2 : NearState :=
  { storage := fun k => if k = [42] then some [100] else none
    context := { input := encodeKV [1, 2] [7, 8, 9] } }

theorem demo2_stored : storedAt demoNs2 [1, 2] = some [7, 8, 9] := by native_decide

theorem demo2_frame_other : storedAt demoNs2 [42] = some [100] := by native_decide

/-! ## Host semantic regression checks -/

def initialWith (ns : NearState) : Store NearState :=
  { («module».initialStore : Store NearState) with host := ns }

/-- Guest-memory inputs must trap when the requested range exceeds memory. -/
def valueReturnOobTraps : Bool :=
  match valueReturnFn.invoke (initialWith {}) [.i64 1, .i64 (UInt64.ofNat 65536)] with
  | .Trap _ _ => true
  | _         => false

theorem value_return_oob_traps : valueReturnOobTraps = true := by native_decide

/-- Output `register_id = u64::MAX` discards the output instead of writing
to an actual register with that numeric id. -/
def inputMaxDiscards : Bool :=
  match inputFn.invoke (initialWith { context := { input := [1, 2, 3] } }) [.i64 u64Max] with
  | .Return [] st => (st.host.registers u64Max.toNat).isNone
  | _             => false

theorem input_max_discards : inputMaxDiscards = true := by native_decide

def storageReadMaxDiscards : Bool :=
  let ns : NearState :=
    { storage := fun k => if k = [1] then some [2] else none
      registers := fun i => if i = 0 then some [1] else none }
  match storageReadFn.invoke (initialWith ns) [.i64 u64Max, .i64 0, .i64 u64Max] with
  | .Return [.i64 1] st => (st.host.registers u64Max.toNat).isNone
  | _                   => false

theorem storage_read_max_discards : storageReadMaxDiscards = true := by native_decide

def resolvesImportSubset : Bool :=
  match resolveImports?
      [ { «module» := "env", name := "current_account_id", params := [.i64], results := [] }
      , { «module» := "env", name := "storage_write",
          params := [.i64, .i64, .i64, .i64, .i64], results := [.i64] } ] with
  | some env => env.funcs.length == 2
  | none     => false

theorem resolve_import_subset : resolvesImportSubset = true := by native_decide

def rejectsBadImportSignature : Bool :=
  match resolveImports?
      [ { «module» := "env", name := "storage_write",
          params := [.i64, .i64], results := [.i64] } ] with
  | none   => true
  | some _ => false

theorem reject_bad_import_signature : rejectsBadImportSignature = true := by native_decide

def currentAccountWritesRegister : Bool :=
  let ns : NearState := { context := { currentAccountId := [99, 100] } }
  match currentAccountIdFn.invoke (initialWith ns) [.i64 7] with
  | .Return [] st => st.host.registers 7 == some [99, 100]
  | _             => false

theorem current_account_writes_register : currentAccountWritesRegister = true := by native_decide

def accountBalanceWritesU128 : Bool :=
  let ns : NearState := { context := { accountBalance := 258 } }
  match accountBalanceFn.invoke (initialWith ns) [.i64 0] with
  | .Return [] st => st.mem.readBytes 0 16 == leU128Bytes 258
  | _             => false

theorem account_balance_writes_u128 : accountBalanceWritesU128 = true := by native_decide

def sha256HookWritesRegister : Bool :=
  let ns : NearState := { sha256 := fun bs => bs ++ [9] }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match sha256Fn.invoke st [.i64 2, .i64 0, .i64 5] with
  | .Return [] st' => st'.host.registers 5 == some [1, 2, 9]
  | _              => false

theorem sha256_hook_writes_register : sha256HookWritesRegister = true := by native_decide

def randomSeedWritesRegister : Bool :=
  let ns : NearState := { randomSeed := [4, 5, 6] }
  match randomSeedFn.invoke (initialWith ns) [.i64 3] with
  | .Return [] st => st.host.registers 3 == some [4, 5, 6]
  | _             => false

theorem random_seed_writes_register : randomSeedWritesRegister = true := by native_decide

end KvSetter
end Near
end Wasm
