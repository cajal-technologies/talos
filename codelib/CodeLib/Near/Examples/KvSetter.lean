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

end KvSetter
end Near
end Wasm
