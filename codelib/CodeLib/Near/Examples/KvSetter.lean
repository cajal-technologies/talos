import CodeLib.Near.SmallStep

/-!
# Example: a NEAR key-value setter

A hand-built NEAR contract with one method, `set`. It follows the real
NEAR ABI end to end:

1. `input(0)` — deposit the raw call input into register 0.
2. `read_register(0, 0)` — copy that input into linear memory at offset 0.
3. parse a **length-prefixed** `(key, value)` out of memory, where the
   encoding is `le32(key.len) ++ key ++ le32(val.len) ++ val`.
4. `storage_write(key_len, key_ptr, value_len, value_ptr, 1)` — store it.

The interesting property is a *before/after projection* of the
NEAR storage trie plus a *frame condition*: after the call the chosen key
maps to the value, and every other key is unchanged. The `∀ k` in the
frame is the "iterate over all keys" reasoning the storage-as-a-function
model makes free — no Wasm enumeration needed.

The property is proved against the small-step machine through the Iris
total-WP layer, starting from `setConfig` — the entry frame of
`«module».funcs[0]` (the exported `set`, unified index `setIdx`; it has no
params or locals) over the module's initial store with NEAR state `nearSt`.
`set_terminatesWith` gives total correctness (`SmallStep.TerminatesWith`) and
`set_partiallyMeets` the partial-correctness corollary; neither mentions fuel.
The kernel-checked regression theorems below additionally validate the *whole pipeline*
— registers, the memory-or-register sentinel, length-prefix parsing, and
`storage_write` semantics — executes correctly on concrete inputs.
-/

namespace Wasm
namespace Near
namespace KvSetter

open Wasm SepLogic SmallStep
open Iris Iris.BI Iris.ProgramLogic OFE COFE Iris.Algebra Language.Notation Std

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

/-- The hand-built example imports the canonical NEAR host set, so the
reference environment satisfies the canonical proof-facing spec. -/
theorem near_env_satisfies : nearEnv.Satisfies «module» nearSpec :=
  nearEnv_satisfies_canonical «module» rfl

/-! ## Length-prefix encoding -/

/-- Little-endian 4-byte encoding of a length. -/
def le32 (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256),
    UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 16777216 % 256) ]

/-- Little-endian 8-byte encoding of a `u64`-sized natural. -/
def le64 (n : Nat) : List UInt8 :=
  (List.range 8).map (fun i => UInt8.ofNat (n / 2 ^ (8 * i) % 256))

/-- The contract's input wire format: `le32(|key|) ++ key ++ le32(|val|) ++ val`. -/
def encodeKV (key val : List UInt8) : List UInt8 :=
  le32 key.length ++ (key ++ (le32 val.length ++ val))

theorem le32_parts_or (n : Nat) :
    n % 256 ||| ((n / 256 % 256) <<< 8) ||| ((n / 65536 % 256) <<< 16) |||
      ((n / 16777216 % 256) <<< 24) = n % 4294967296 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hm0 : (n % 256).testBit i = (decide (i < 8) && n.testBit i) := by
    simpa using (Nat.testBit_mod_two_pow n 8 i)
  have hm1 : (n / 256 % 256).testBit (i - 8) =
      (decide (i - 8 < 8) && n.testBit (i - 8 + 8)) := by
    rw [show 256 = 2 ^ 8 by norm_num]
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have hm2 : (n / 65536 % 256).testBit (i - 16) =
      (decide (i - 16 < 8) && n.testBit (i - 16 + 16)) := by
    rw [show 65536 = 2 ^ 16 by norm_num, show 256 = 2 ^ 8 by norm_num]
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have hm3 : (n / 16777216 % 256).testBit (i - 24) =
      (decide (i - 24 < 8) && n.testBit (i - 24 + 24)) := by
    rw [show 16777216 = 2 ^ 24 by norm_num, show 256 = 2 ^ 8 by norm_num]
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have hm4 : (n % 4294967296).testBit i = (decide (i < 32) && n.testBit i) := by
    rw [show 4294967296 = 2 ^ 32 by norm_num]
    rw [Nat.testBit_mod_two_pow]
  simp [Nat.testBit_or, Nat.testBit_shiftLeft, hm0, hm1, hm2, hm3, hm4]
  by_cases h0 : i < 8
  · have hi32 : i < 32 := by omega
    have hn8 : ¬ 8 ≤ i := by omega
    have hn16 : ¬ 16 ≤ i := by omega
    have hn24 : ¬ 24 ≤ i := by omega
    by_cases hb : n.testBit i <;> simp [h0, hi32, hn8, hn16, hn24, hb]
  by_cases h1 : i < 16
  · have hi8 : 8 ≤ i := by omega
    have hi32 : i < 32 := by omega
    have hi1 : i - 8 < 8 := by omega
    have hsum : i - 8 + 8 = i := by omega
    have hn16 : ¬ 16 ≤ i := by omega
    have hn24 : ¬ 24 ≤ i := by omega
    by_cases hb : n.testBit i <;> simp [h0, hi8, hi32, hi1, hsum, hn16, hn24, hb]
  by_cases h2 : i < 24
  · have hi8 : 8 ≤ i := by omega
    have hi16 : 16 ≤ i := by omega
    have hi32 : i < 32 := by omega
    have hi1 : ¬ i - 8 < 8 := by omega
    have hi2 : i - 16 < 8 := by omega
    have hsum : i - 16 + 16 = i := by omega
    have hn24 : ¬ 24 ≤ i := by omega
    by_cases hb : n.testBit i <;> simp [h0, hi8, hi16, hi32, hi1, hi2, hsum, hn24, hb]
  by_cases h3 : i < 32
  · have hi8 : 8 ≤ i := by omega
    have hi16 : 16 ≤ i := by omega
    have hi24 : 24 ≤ i := by omega
    have hi1 : ¬ i - 8 < 8 := by omega
    have hi2 : ¬ i - 16 < 8 := by omega
    have hi3 : i - 24 < 8 := by omega
    have hsum : i - 24 + 24 = i := by omega
    by_cases hb : n.testBit i <;> simp [h0, h3, hi8, hi16, hi24, hi1, hi2, hi3, hsum, hb]
  · have hi8 : 8 ≤ i := by omega
    have hi16 : 16 ≤ i := by omega
    have hi24 : 24 ≤ i := by omega
    have hi1 : ¬ i - 8 < 8 := by omega
    have hi2 : ¬ i - 16 < 8 := by omega
    have hi3 : ¬ i - 24 < 8 := by omega
    by_cases hb : n.testBit i <;> simp [h0, h3, hi8, hi16, hi24, hi1, hi2, hi3, hb]

@[simp] theorem read32_writeBytes_le32 (m : Mem) (n : Nat) :
    (m.writeBytes 0 (le32 n)).read32 0 = UInt32.ofNat n := by
  apply UInt32.toNat.inj
  simp [le32, Mem.read32, Mem.writeBytes, UInt8.toNat_toUInt32, UInt32.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]
    have : n / 256 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    omega : ((n / 256 % 256) <<< 8) < 4294967296)]
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]
    have : n / 65536 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    omega : ((n / 65536 % 256) <<< 16) < 4294967296)]
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]
    have : n / 16777216 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    omega : ((n / 16777216 % 256) <<< 24) < 4294967296)]
  exact le32_parts_or n

@[simp] theorem read32_writeBytes_encode_keyLen (m : Mem) (key val : List UInt8) :
    (m.writeBytes 0 (encodeKV key val)).read32 0 = UInt32.ofNat key.length := by
  apply UInt32.toNat.inj
  simp [encodeKV, le32, Mem.read32, Mem.writeBytes, UInt8.toNat_toUInt32, UInt32.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]
    have : key.length / 256 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    omega : ((key.length / 256 % 256) <<< 8) < 4294967296)]
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]
    have : key.length / 65536 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    omega : ((key.length / 65536 % 256) <<< 16) < 4294967296)]
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]
    have : key.length / 16777216 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    omega : ((key.length / 16777216 % 256) <<< 24) < 4294967296)]
  exact le32_parts_or key.length

@[simp] theorem read32_writeBytes_encode_valLen (m : Mem) (key val : List UInt8)
    (hKeyAddr : key.length + 4 < 4294967296) :
    (m.writeBytes 0 (encodeKV key val)).read32 (UInt32.ofNat key.length + 4) =
      UInt32.ofNat val.length := by
  apply UInt32.toNat.inj
  have hAddr : (UInt32.ofNat key.length + 4).toNat = key.length + 4 := by
    rw [UInt32.toNat_add, UInt32.toNat_ofNat]
    change (key.length % 4294967296 + 4) % 4294967296 = key.length + 4
    have hKey : key.length < 4294967296 := by omega
    rw [Nat.mod_eq_of_lt hKey]; exact Nat.mod_eq_of_lt hKeyAddr
  simp [encodeKV, le32, Mem.read32, Mem.writeBytes, hAddr, UInt8.toNat_toUInt32,
    UInt32.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]
    have : val.length / 256 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    omega : ((val.length / 256 % 256) <<< 8) < 4294967296)]
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]
    have : val.length / 65536 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    omega : ((val.length / 65536 % 256) <<< 16) < 4294967296)]
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]
    have : val.length / 16777216 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    omega : ((val.length / 16777216 % 256) <<< 24) < 4294967296)]
  exact le32_parts_or val.length

@[simp] theorem readBytes_writeBytes_encode_key (m : Mem) (key val : List UInt8) :
    (m.writeBytes 0 (encodeKV key val)).readBytes 4 key.length = key := by
  rw [show 4 = 0 + 4 by norm_num]
  rw [readBytes_writeBytes_slice]
  · simp [encodeKV, le32]
  · simp [encodeKV, le32]; omega

@[simp] theorem readBytes_writeBytes_encode_val (m : Mem) (key val : List UInt8) :
    (m.writeBytes 0 (encodeKV key val)).readBytes (key.length + 8) val.length = val := by
  rw [show key.length + 8 = 0 + (key.length + 8) by omega]
  rw [readBytes_writeBytes_slice]
  · simp [encodeKV, le32]
  · simp [encodeKV, le32]; omega

theorem u64_toNat_of_u32_len (n : Nat) (h : n < 4294967296) :
    (UInt64.ofNat n).toNat = n := by
  change (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem u64_ofNat_ne_u64Max_of_u32_len (n : Nat) (h : n < 4294967296) :
    UInt64.ofNat n ≠ u64Max := by
  intro heq
  have ht := congrArg UInt64.toNat heq
  change (BitVec.ofNat 64 n).toNat = (18446744073709551615#64).toNat at ht
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  norm_num at ht; omega

theorem u64_key_add8_toNat (key : List UInt8) (hKey : key.length < 4294967296) :
    (UInt64.ofNat key.length + 8).toNat = key.length + 8 := by
  rw [UInt64.toNat_add]
  change ((UInt64.ofNat key.length).toNat + (8#64).toNat) %
      18446744073709551616 = key.length + 8
  rw [u64_toNat_of_u32_len key.length hKey]
  norm_num; omega

theorem getMemOrReg_writeBytes_encode_key (st : Store NearState) (key val : List UInt8)
    (hKey : key.length < 4294967296)
    (hMem : (encodeKV key val).length ≤ memBytes st) :
    getMemOrReg { st with mem := st.mem.writeBytes 0 (encodeKV key val) }
      (4 : UInt64) (UInt64.ofNat key.length) = some key := by
  rw [getMemOrReg_mem]
  · simp [u64_toNat_of_u32_len key.length hKey]
  · exact u64_ofNat_ne_u64Max_of_u32_len key.length hKey
  · simp [u64_toNat_of_u32_len key.length hKey, memBytes, encodeKV, le32] at hMem ⊢; omega

theorem getMemOrReg_writeBytes_encode_val (st : Store NearState) (key val : List UInt8)
    (hKey : key.length < 4294967296) (hVal : val.length < 4294967296)
    (hMem : (encodeKV key val).length ≤ memBytes st) :
    getMemOrReg { st with mem := st.mem.writeBytes 0 (encodeKV key val) }
      (UInt64.ofNat key.length + 8) (UInt64.ofNat val.length) = some val := by
  rw [getMemOrReg_mem]
  · simp [u64_key_add8_toNat key hKey, u64_toNat_of_u32_len val.length hVal]
  · exact u64_ofNat_ne_u64Max_of_u32_len val.length hVal
  · simp [u64_key_add8_toNat key hKey, u64_toNat_of_u32_len val.length hVal,
      memBytes, encodeKV, le32, Nat.add_comm, Nat.add_left_comm] at hMem ⊢
    omega

/-! ## Specification -/

def afterInputStore (ns : NearState) (key val : List UInt8) : Store NearState :=
  { («module».initialStore : Store NearState) with
    host := ns.setRegister 0 (encodeKV key val) }

def storageCallStore (ns : NearState) (key val : List UInt8) : Store NearState :=
  { afterInputStore ns key val with
    mem := (afterInputStore ns key val).mem.writeBytes 0 (encodeKV key val) }

theorem storageWrite_invoke_encode_present (ns : NearState) (key val old : List UInt8)
    (hView : ns.context.isView = false)
    (hKey : key.length < 4294967296) (hVal : val.length < 4294967296)
    (hLen : (encodeKV key val).length ≤ 65536)
    (hKeyLim : withinLimit ns.config.maxStorageKeyLen key.length = true)
    (hValLim : withinLimit ns.config.maxStorageValueLen val.length = true)
    (hOld : ns.storage key = some old)
    (hOldLim : withinLimit ns.config.maxRegisterLen old.length = true) :
    storageWriteFn.invoke (storageCallStore ns key val)
      [.i64 (UInt64.ofNat key.length), .i64 4, .i64 (UInt64.ofNat val.length),
        .i64 (UInt64.ofNat key.length + 8), .i64 1] =
      .Return [.i64 1]
        { storageCallStore ns key val with
          host := (((ns.setRegister 0 (encodeKV key val)).setRegister 1 old).setStorage key val).invalidateIterators } := by
  refine storageWriteFn_invoke_present
    (st := storageCallStore ns key val) (key := key) (val := val) (old := old)
    (keyLen := UInt64.ofNat key.length) (keyPtr := 4)
    (valLen := UInt64.ofNat val.length) (valPtr := UInt64.ofNat key.length + 8)
    (regId := 1)
    (stReg :=
      { storageCallStore ns key val with
        host := (ns.setRegister 0 (encodeKV key val)).setRegister 1 old }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hView
  · apply getMemOrReg_writeBytes_encode_key
    · exact hKey
    · simpa [afterInputStore, memBytes, «module», Module.initialStore, Mem.empty] using hLen
  · apply getMemOrReg_writeBytes_encode_val
    · exact hKey
    · exact hVal
    · simpa [afterInputStore, memBytes, «module», Module.initialStore, Mem.empty] using hLen
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hKeyLim
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hValLim
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hOld
  · simp [storageCallStore, afterInputStore, checkedSetRegister?, hOldLim, NearState.setRegister, u64Max]

theorem storageWrite_invoke_encode_absent (ns : NearState) (key val : List UInt8)
    (hView : ns.context.isView = false)
    (hKey : key.length < 4294967296) (hVal : val.length < 4294967296)
    (hLen : (encodeKV key val).length ≤ 65536)
    (hKeyLim : withinLimit ns.config.maxStorageKeyLen key.length = true)
    (hValLim : withinLimit ns.config.maxStorageValueLen val.length = true)
    (hOld : ns.storage key = none) :
    storageWriteFn.invoke (storageCallStore ns key val)
      [.i64 (UInt64.ofNat key.length), .i64 4, .i64 (UInt64.ofNat val.length),
        .i64 (UInt64.ofNat key.length + 8), .i64 1] =
      .Return [.i64 0]
        { storageCallStore ns key val with
          host := ((ns.setRegister 0 (encodeKV key val)).setStorage key val).invalidateIterators } := by
  apply storageWriteFn_invoke_absent
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hView
  · apply getMemOrReg_writeBytes_encode_key
    · exact hKey
    · simpa [afterInputStore, memBytes, «module», Module.initialStore, Mem.empty] using hLen
  · apply getMemOrReg_writeBytes_encode_val
    · exact hKey
    · exact hVal
    · simpa [afterInputStore, memBytes, «module», Module.initialStore, Mem.empty] using hLen
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hKeyLim
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hValLim
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hOld

/-- Initial machine configuration for the `set` entry: the body of
`«module».funcs[0]` (exported as `set`, unified index `setIdx`) running in an
empty frame — `set` has no params or locals — over the module's initial
store with NEAR host state `nearSt`. -/
def setConfig (nearSt : NearState) : Config NearState :=
  { expr := .running
      { locals := {}
        code := setBody
        resultArity := 0
        callerRemainder := [] }
    store :=
      { runtime := nearRuntime «module»
        wasm := { («module».initialStore : Store NearState) with host := nearSt } } }

private def setHeap (key val : List UInt8) : WasmHeapMap (Option UInt8) :=
  insertFreshBytes ∅ 0 (physicalBytes (Mem.empty 1) 0 (key.length + val.length + 8))

private theorem le32_eq_u32Bytes (n : Nat) (hn : n < UInt32.size) :
    le32 n = [u32Byte (UInt32.ofNat n) 0, u32Byte (UInt32.ofNat n) 1,
              u32Byte (UInt32.ofNat n) 2, u32Byte (UInt32.ofNat n) 3] := by
  have hmod : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by simpa [UInt32.size] using hn)
  simp only [le32, u32Byte]
  have h0 : UInt8.ofNat (n % 256) = (UInt32.ofNat n).toUInt8 := by
    apply UInt8.toNat.inj
    simp only [UInt32.toNat_toUInt8]; simp
  have h1 : UInt8.ofNat (n / 256 % 256) = ((UInt32.ofNat n) >>> 8).toUInt8 := by
    apply UInt8.toNat.inj
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
               UInt32.toNat_ofNat, Nat.shiftRight_eq_div_pow,
               show 8 % 32 = 8 from rfl]; simp; omega
  have h2 : UInt8.ofNat (n / 65536 % 256) = ((UInt32.ofNat n) >>> 16).toUInt8 := by
    apply UInt8.toNat.inj
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
               UInt32.toNat_ofNat, Nat.shiftRight_eq_div_pow,
               show 16 % 32 = 16 from rfl]; simp; omega
  have h3 : UInt8.ofNat (n / 16777216 % 256) = ((UInt32.ofNat n) >>> 24).toUInt8 := by
    apply UInt8.toNat.inj
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
               UInt32.toNat_ofNat, Nat.shiftRight_eq_div_pow,
               show 24 % 32 = 24 from rfl]; simp; omega
  simp [h0, h1, h2, h3]

private theorem setHeap_facts (nearSt : NearState) (key val : List UInt8)
    (hLen : key.length + val.length + 8 ≤ 65536) :
    heapAgreesWithMem (setHeap key val) (storeResolve (setConfig nearSt).store) ∧
    heapAddressesInBounds (setHeap key val) (storeResolve (setConfig nearSt).store) := by
  have hresolve : storeResolve (setConfig nearSt).store 0 = some (Mem.empty 1) := by
    simp [storeResolve, setConfig]; rfl
  refine ⟨?_, ?_⟩
  · exact (insertFreshPhysicalBytes_facts ∅ (storeResolve (setConfig nearSt).store)
        (Mem.empty 1) 0 (key.length + val.length + 8)
        hresolve (heapAgreesWithMem_empty _) (heapAddressesInBounds_empty _)
        (by simp [Mem.empty]; omega)
        (by simp [UInt32.size]; omega)).1
  · exact (insertFreshPhysicalBytes_facts ∅ (storeResolve (setConfig nearSt).store)
        (Mem.empty 1) 0 (key.length + val.length + 8)
        hresolve (heapAgreesWithMem_empty _) (heapAddressesInBounds_empty _)
        (by simp [Mem.empty]; omega)
        (by simp [UInt32.size]; omega)).2

/-- `storageWriteFn` always returns (never traps or throws) when the view,
key/value limits, and register-size preconditions are met. Factors out the
identical `none`/`some` case split in the TRAP and THROW callbacks. -/
private theorem storageWriteFn_isReturn
    (st : Store NearState) (key val : List UInt8) (klen_u32 : UInt32)
    (ns1 : NearState)
    (heq : st.host = ns1)
    (hView' : st.host.context.isView = false)
    (hKeyLim' : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hValLim' : withinLimit st.host.config.maxStorageValueLen val.length = true)
    (hkeyGet : getMemOrReg st 4 (UInt64.ofNat klen_u32.toNat) = some key)
    (hvalGet : getMemOrReg st (UInt64.ofNat klen_u32.toNat + 8)
        (UInt64.ofNat (UInt32.ofNat val.length).toNat) = some val)
    (hMaxReg : ∀ old, ns1.storage key = some old →
        withinLimit ns1.config.maxRegisterLen old.length = true) :
    ∃ results postWasm, storageWriteFn.invoke st
        [.i64 (UInt64.ofNat klen_u32.toNat), .i64 4,
         .i64 (UInt64.ofNat (UInt32.ofNat val.length).toNat),
         .i64 (UInt64.ofNat klen_u32.toNat + 8), .i64 1] =
        .Return results postWasm := by
  cases hOld : ns1.storage key with
  | none =>
    exact ⟨_, _, storageWriteFn_invoke_absent st key val
        (UInt64.ofNat klen_u32.toNat) 4
        (UInt64.ofNat (UInt32.ofNat val.length).toNat)
        (UInt64.ofNat klen_u32.toNat + 8) 1
        hView' hkeyGet hvalGet hKeyLim' hValLim'
        (by rw [heq]; exact hOld)⟩
  | some old =>
    have hLim_host : withinLimit st.host.config.maxRegisterLen old.length = true := by
      rw [heq]; exact hMaxReg old hOld
    obtain ⟨stReg, hChecked⟩ : ∃ stReg, checkedSetRegister? st 1 old = some stReg := by
      simp only [checkedSetRegister?, show ¬ (1 : UInt64) = u64Max from by decide,
                 ite_false, ite_eq_left hLim_host]
      exact ⟨_, rfl⟩
    exact ⟨_, _, storageWriteFn_invoke_present st key val old
        (UInt64.ofNat klen_u32.toNat) 4
        (UInt64.ofNat (UInt32.ofNat val.length).toNat)
        (UInt64.ofNat klen_u32.toNat + 8) 1 stReg
        hView' hkeyGet hvalGet hKeyLim' hValLim'
        (by rw [heq]; exact hOld) hChecked⟩

theorem set_terminatesWith (nearSt : NearState) (key val : List UInt8)
    (hView : nearSt.context.isView = false)
    (hKey : key.length < 4294967296) (hVal : val.length < 4294967296)
    (hLen : key.length + val.length + 8 ≤ 65536)
    (hReg : withinLimit nearSt.config.maxRegisterLen (encodeKV key val).length)
    (hKeyLim : withinLimit nearSt.config.maxStorageKeyLen key.length)
    (hValLim : withinLimit nearSt.config.maxStorageValueLen val.length)
    (hMaxReg : ∀ old, nearSt.storage key = some old →
        withinLimit nearSt.config.maxRegisterLen old.length)
    (hInput : nearSt.context.input = encodeKV key val) :
    SmallStep.TerminatesWith (setConfig nearSt)
      (fun _ store => store.wasm.host.storage key = some val ∧
        ∀ k, k ≠ key → store.wasm.host.storage k = nearSt.storage k) := by
  apply wasm_smallStep_heap_globals_runtime_host_store_terminates
      (setConfig nearSt) (setHeap key val) (∅ : WasmGlobalMap Value)
  · exact (setHeap_facts nearSt key val hLen).1
  · exact (setHeap_facts nearSt key val hLen).2
  · exact globalHeapAgrees_empty _
  · simp [setConfig, nearRuntime]
  · intro hlc inst _
    set N := key.length + val.length + 8
    have hNnowrap : (0 : UInt32).toNat + (physicalBytes (Mem.empty 1) 0 N).length < UInt32.size := by
      simp [UInt32.size]; omega
    have hNbelow : HeapBelow (∅ : WasmHeapMap (Option UInt8)) 0 :=
      fun _ _ h _ => by simp [LawfulPartialMap.get?_empty] at h
    simp only [BI.BigSepM.bigSepM_empty.to_eq, BI.emp_sep.to_eq,
               setConfig, nearRuntime, setHeap, setBody,
               RuntimeEnv.currentModule_mk1, RuntimeEnv.currentHost_mk1]
    iintro ⟨Hheap, Hruntime, Henv, Hhost⟩
    ihave ⟨Hbytes0, _Hemp⟩ :=
      insertFreshBytes_bigSep_pointsToBytes ∅ (0 : UInt32)
        (physicalBytes (Mem.empty 1) 0 N) hNbelow hNnowrap $$ Hheap
    -- input(0)
    wasm_twp_pures [twp_constI64]
    set ns0 := nearSt
    set ns1 := nearSt.setRegister 0 (encodeKV key val)
    ihave ⟨Henv_pass1, Henv1⟩ := persistent_sep_dup_mp $$ Henv
    iapply twp_callHost «module» 0
        { «module» := "env", name := "input", params := [.i64], results := [] }
        inputFn
        (by decide) rfl nearEnv (by rfl)
        (iprop(hostStateOwn ns0 ∗ pointsToBytes 0 (0 : UInt32) (physicalBytes (Mem.empty 1) 0 N) ∗ hostEnvOwn 0 nearEnv))
        (fun _ => iprop(hostStateOwn ns1 ∗ pointsToBytes 0 (0 : UInt32) (physicalBytes (Mem.empty 1) 0 N) ∗ hostEnvOwn 0 nearEnv))
        (iprop(False)) (iprop(False)) ⟨0⟩
        (fun store ns obs nt hModule results postWasm hinvoke => by
          iintro ⟨⟨HP, HbytesSuc, HenvK⟩, Hσ⟩
          have heqNs1 : ns0.setRegister 0 ns0.context.input = ns1 := by
            simp [ns0, ns1, hInput]
          rw [← heqNs1]
          have hxfer := @twp_near_input hlc inst ns0 «module» store ns obs nt hModule results postWasm hinvoke
          imod hxfer $$ [$HP $Hσ] with ⟨HP1, Hσ1⟩
          imodintro
          isplitl [HP1 HbytesSuc HenvK]; iframe; iexact Hσ1)
        (fun store ns obs nt _ postWasm msg hinvoke => by
          iintro ⟨⟨HP, _, _⟩, Hσ⟩
          ihave %heq : ⌜store.wasm.host = ns0⌝ $$ [Hσ HP]
          · iapply (stateInterp_host_agree store ns obs nt ns0); iframe Hσ HP
          simp [inputFn, writeRegisterResult, checkedSetRegister?, u64Max, hReg, heq, hInput] at hinvoke)
        (fun store ns obs nt _ postWasm tag xs hinvoke => by
          iintro ⟨⟨HP, _, _⟩, Hσ⟩
          ihave %heq : ⌜store.wasm.host = ns0⌝ $$ [Hσ HP]
          · iapply (stateInterp_host_agree store ns obs nt ns0); iframe Hσ HP
          simp [inputFn, writeRegisterResult, checkedSetRegister?, u64Max, hReg, heq, hInput] at hinvoke)
        $$ [$Hhost $Hbytes0 $Henv1] Hruntime Henv_pass1
    · iintro %_pre %_results %_post %_hinvoke ⟨⟨Hhost1, Hbytes0, Henv1_back⟩, Hruntime1⟩
      -- read_register(0, 0)
      wasm_twp_pures [twp_constI64 twp_constI64]
      have hReg0 : ns1.registers 0 = some (encodeKV key val) := by
        simp [ns1, NearState.setRegister]
      have hEncLen : (encodeKV key val).length = N := by
        simp [encodeKV, le32, N]; ring
      have hNowrapRR : (encodeKV key val).length < UInt32.size := by
        simp only [UInt32.size]; omega
      ihave ⟨Henv_pass2, Henv2⟩ := persistent_sep_dup_mp $$ Henv1_back
      iapply twp_callHost «module» 1
          { «module» := "env", name := "read_register", params := [.i64, .i64], results := [] }
          readRegisterFn
          (by decide) rfl nearEnv (by rfl)
          (iprop(hostStateOwn ns1 ∗ pointsToBytes 0 (0 : UInt32)
            (physicalBytes (Mem.empty 1) 0 N) ∗ hostEnvOwn 0 nearEnv))
          (fun _ => iprop(hostStateOwn ns1 ∗ pointsToBytes 0 (0 : UInt32) (encodeKV key val) ∗ hostEnvOwn 0 nearEnv))
          (iprop(False)) (iprop(False)) ⟨0⟩
          (fun store ns obs nt hModule results postWasm hinvoke => by
            iintro ⟨⟨HP1, Hbytes0', HenvRR⟩, Hσ⟩
            have hLenEq : (physicalBytes (Mem.empty 1) 0 N).length =
                (encodeKV key val).length := by
              rw [physicalBytes_length]; exact hEncLen.symm
            have hxfer := @twp_near_readRegister hlc inst ns1 (encodeKV key val)
                (physicalBytes (Mem.empty 1) 0 N) «module»
                hReg0 hLenEq hNowrapRR store ns obs nt hModule
                results postWasm hinvoke
            imod hxfer $$ [$HP1 $Hbytes0' $Hσ] with ⟨⟨HP2, Hbytes1⟩, Hσ2⟩
            imodintro
            isplitl [HP2 Hbytes1 HenvRR]
            iframe
            iexact Hσ2)
          (fun store ns obs nt _ postWasm msg hinvoke => by
            iintro ⟨⟨HP1, HbytesTrap, _⟩, Hσ⟩
            wasm_points_to_bytes_agree hbfactsTrap, (0 : UInt32), (physicalBytes (Mem.empty 1) 0 N), obs $$ [Hσ HbytesTrap]
            have hboundTrap : (encodeKV key val).length ≤ store.wasm.mem.pages * 65536 := by
              have hpos : 0 < (physicalBytes (Mem.empty 1) 0 N).length := by
                simp [physicalBytes_length]; omega
              have hb := pointsToBytes_facts_bound hbfactsTrap hpos hNnowrap
              simp only [UInt32.toNat_zero, Nat.zero_add, physicalBytes_length] at hb
              omega
            ihave %heq : ⌜store.wasm.host = ns1⌝ $$ [Hσ HP1]
            · iapply (stateInterp_host_agree store ns obs nt ns1); iframe Hσ HP1
            have hreg0 : store.wasm.host.registers 0 =
                some (encodeKV key val) := by simp [heq, ns1, NearState.setRegister]
            have hNOOB : ¬ (memBytes store.wasm < (encodeKV key val).length) := by
              simp only [memBytes]; omega
            simp [readRegisterFn, hreg0, hNOOB] at hinvoke)
          (fun store ns obs nt _ postWasm tag xs hinvoke => by
            iintro ⟨⟨HP1, _, _⟩, Hσ⟩
            ihave %heq : ⌜store.wasm.host = ns1⌝ $$ [Hσ HP1]
            · iapply (stateInterp_host_agree store ns obs nt ns1); iframe Hσ HP1
            have hreg0 : store.wasm.host.registers 0 =
                some (encodeKV key val) := by simp [heq, ns1, NearState.setRegister]
            simp [readRegisterFn, hreg0] at hinvoke
            split_ifs at hinvoke)
          $$ [$Hhost1 $Hbytes0 $Henv2] Hruntime1 Henv_pass2
      · iintro %_pre %_results %_post %_hinvoke ⟨⟨Hhost2, Hbytes1, Henv2_back⟩, Hruntime2⟩
        -- Convert Hbytes1 from encodeKV form to explicit concat for IntoWand
        have hEncConv : pointsToBytes 0 (0 : UInt32) (encodeKV key val) ⊢
            pointsToBytes 0 (0 : UInt32) (le32 key.length ++ (key ++ (le32 val.length ++ val))) :=
          BI.entails_refl
        ihave Hbytes1_exp := hEncConv $$ Hbytes1
        -- Split: klen | rest
        ihave ⟨Hklen_raw, Hrest1_raw⟩ :=
          (pointsToBytes_append 0 (0 : UInt32)
            (le32 key.length) (key ++ (le32 val.length ++ val))).mp $$ Hbytes1_exp
        -- Bridge offset: 0 + UInt32.ofNat (le32 key.length).length → 4
        have h4Eq : (0 : UInt32) + UInt32.ofNat (le32 key.length).length = 4 := by
          simp [le32]
        have hRest1Conv : pointsToBytes 0 ((0 : UInt32) + UInt32.ofNat (le32 key.length).length)
            (key ++ (le32 val.length ++ val)) ⊢
            pointsToBytes 0 (4 : UInt32) (key ++ (le32 val.length ++ val)) :=
          h4Eq ▸ BI.entails_refl
        ihave Hrest1 := hRest1Conv $$ Hrest1_raw
        have hklenEq : le32 key.length =
            [u32Byte (UInt32.ofNat key.length) 0, u32Byte (UInt32.ofNat key.length) 1,
             u32Byte (UInt32.ofNat key.length) 2, u32Byte (UInt32.ofNat key.length) 3] :=
          le32_eq_u32Bytes key.length (by simpa [UInt32.size] using hKey)
        have hKlenConv : pointsToBytes 0 (0 : UInt32) (le32 key.length) ⊢
            pointsTo_u32 0 (0 : UInt32) (UInt32.ofNat key.length) :=
          hklenEq ▸ (pointsTo_u32_as_bytes 0 (0 : UInt32) (UInt32.ofNat key.length)).mpr
        ihave Hklen := hKlenConv $$ Hklen_raw
        ihave ⟨Hkey_raw, Hrest2⟩ :=
          (pointsToBytes_append 0 (4 : UInt32) key (le32 val.length ++ val)).mp $$
            Hrest1
        set klen_u32 := UInt32.ofNat key.length
        ihave ⟨Hvlen_raw, Hval_raw⟩ :=
          (pointsToBytes_append 0 (4 + klen_u32)
            (le32 val.length) val).mp $$ Hrest2
        have hvlenEq : le32 val.length =
            [u32Byte (UInt32.ofNat val.length) 0, u32Byte (UInt32.ofNat val.length) 1,
             u32Byte (UInt32.ofNat val.length) 2, u32Byte (UInt32.ofNat val.length) 3] :=
          le32_eq_u32Bytes val.length (by simpa [UInt32.size] using hVal)
        have hVlenConv : pointsToBytes 0 (4 + klen_u32) (le32 val.length) ⊢
            pointsTo_u32 0 (4 + klen_u32) (UInt32.ofNat val.length) :=
          hvlenEq ▸ (pointsTo_u32_as_bytes 0 (4 + klen_u32) (UInt32.ofNat val.length)).mpr
        ihave Hvlen := hVlenConv $$ Hvlen_raw
        -- Bridge Hval_raw offset from (4+klen_u32)+len(le32 vlen) to 4+klen_u32+4
        have h4valLen : (4 + klen_u32) + UInt32.ofNat (le32 val.length).length =
            4 + klen_u32 + 4 := by simp [le32]
        have hValRawConv : pointsToBytes 0
            ((4 + klen_u32) + UInt32.ofNat (le32 val.length).length) val ⊢
            pointsToBytes 0 (4 + klen_u32 + 4) val :=
          h4valLen ▸ BI.entails_refl
        ihave Hval_raw := hValRawConv $$ Hval_raw
        -- Arithmetic helpers
        have hklen_toNat : klen_u32.toNat = key.length := by
          simp [klen_u32, Nat.mod_eq_of_lt hKey]
        have h0add1 : ((0 : UInt32) + 1).toNat = 1 := by decide
        have h0add2 : ((0 : UInt32) + 2).toNat = 2 := by decide
        have h0add3 : ((0 : UInt32) + 3).toNat = 3 := by decide
        have hk4nowrap : (klen_u32 + 4 : UInt32).toNat = key.length + 4 := by
          rw [UInt32.toNat_add, hklen_toNat]
          simp; omega
        have hk4add1 : (klen_u32 + 4 + 1 : UInt32).toNat = key.length + 5 := by
          rw [UInt32.toNat_add]; simp [hk4nowrap]; omega
        have hk4add2 : (klen_u32 + 4 + 2 : UInt32).toNat = key.length + 6 := by
          rw [UInt32.toNat_add]; simp [hk4nowrap]; omega
        have hk4add3 : (klen_u32 + 4 + 3 : UInt32).toNat = key.length + 7 := by
          rw [UInt32.toNat_add]; simp [hk4nowrap]; omega
        -- Convert Hvlen to klen_u32+4 form for twp_load32 address matching
        have hComm4k : (4 : UInt32) + klen_u32 = klen_u32 + 4 := by exact UInt32.add_comm 4 klen_u32
        have hHvlenComm : pointsTo_u32 0 (4 + klen_u32) (UInt32.ofNat val.length) ⊢
            pointsTo_u32 0 (klen_u32 + 4) (UInt32.ofNat val.length) :=
          hComm4k ▸ BI.entails_refl
        ihave Hvlen_k4 := hHvlenComm $$ Hvlen
        -- Pure arithmetic steps up to storage_write
        wasm_twp_pures [twp_const]
        wasm_twp_rebind (twp_load32_addr (UInt32.ofNat key.length)
            h0add1 h0add2 h0add3) with Hklen
        wasm_twp_pures [twp_extendUI32 twp_constI64 twp_const]
        wasm_twp_rebind (twp_load32_addr (UInt32.ofNat key.length)
            h0add1 h0add2 h0add3) with Hklen
        wasm_twp_rebind (twp_load32 (UInt32.ofNat val.length)
            (by simp only [show UInt32.toNat (4 : UInt32) = 4 from rfl, hk4nowrap]; omega)
            (by simp only [hk4add1]; omega)
            (by simp only [hk4add2]; omega)
            (by simp only [hk4add3]; omega)) with Hvlen_k4
        -- Restore Hvlen to 4+klen_u32 form for storage_write pre-condition
        have hHvlenCommBack : pointsTo_u32 0 (klen_u32 + 4) (UInt32.ofNat val.length) ⊢
            pointsTo_u32 0 (4 + klen_u32) (UInt32.ofNat val.length) :=
          hComm4k.symm ▸ BI.entails_refl
        ihave Hvlen := hHvlenCommBack $$ Hvlen_k4
        wasm_twp_pures [twp_extendUI32 twp_const]
        wasm_twp_rebind (twp_load32_addr (UInt32.ofNat key.length)
            h0add1 h0add2 h0add3) with Hklen
        wasm_twp_pures [twp_extendUI32 twp_constI64 twp_addI64 twp_constI64]
        -- storage_write(keyLen, keyPtr, valLen, valPtr, regId)
        iapply twp_callHost «module» 5
            { «module» := "env", name := "storage_write",
              params := [.i64, .i64, .i64, .i64, .i64], results := [.i64] }
            storageWriteFn
            (by decide) rfl nearEnv (by rfl)
            (iprop(hostStateOwn ns1 ∗ pointsToBytes 0 4 key ∗
              pointsToBytes 0 (4 + klen_u32 + 4) val ∗
              pointsTo_u32 0 (0 : UInt32) klen_u32 ∗
              pointsTo_u32 0 (4 + klen_u32) (UInt32.ofNat val.length)))
            (fun results5 => iprop(
              ⌜results5 = [.i64 0] ∨ results5 = [.i64 1]⌝ ∗
              (∃ ns_final : NearState, hostStateOwn ns_final ∗
                ⌜ns_final.storage key = some val ∧
                  ∀ k, k ≠ key → ns_final.storage k = nearSt.storage k⌝) ∗
              pointsToBytes 0 4 key ∗
              pointsToBytes 0 (4 + klen_u32 + 4) val ∗
              pointsTo_u32 0 (0 : UInt32) klen_u32 ∗
              pointsTo_u32 0 (4 + klen_u32) (UInt32.ofNat val.length)))
            (iprop(False)) (iprop(False)) ⟨0⟩
            (fun store ns obs nt hModule results5 postWasm hinvoke => by
              iintro ⟨⟨HP2, Hkey_raw2, Hval_raw2, Hklen2, Hvlen2⟩, Hσ⟩
              ihave %heq : ⌜store.wasm.host = ns1⌝ $$ [Hσ HP2]
              · iapply (stateInterp_host_agree store ns obs nt ns1); iframe Hσ HP2
              have hView' : ns1.context.isView = false := by
                simp only [ns1, NearState.setRegister]; exact hView
              have hKeyLim' : withinLimit ns1.config.maxStorageKeyLen key.length = true := by
                simp only [ns1, NearState.setRegister]; exact hKeyLim
              have hValLim' : withinLimit ns1.config.maxStorageValueLen val.length = true := by
                simp only [ns1, NearState.setRegister]; exact hValLim
              have hMaxReg' : ∀ old, ns1.storage key = some old →
                  withinLimit ns1.config.maxRegisterLen old.length = true := by
                intro old hold
                simp only [ns1, NearState.setRegister] at hold
                exact hMaxReg old hold
              wasm_points_to_bytes_agree hkeyFacts, (4 : UInt32), key, obs $$
                [Hσ Hkey_raw2]
              wasm_points_to_bytes_agree hvalFacts, (4 + klen_u32 + 4), val, obs $$
                [Hσ Hval_raw2]
              ihave Hklen2_bytes := (pointsTo_u32_as_bytes 0 (0 : UInt32) klen_u32).mp $$ Hklen2
              wasm_points_to_bytes_agree hklenFacts, (0 : UInt32),
                [u32Byte klen_u32 0, u32Byte klen_u32 1, u32Byte klen_u32 2, u32Byte klen_u32 3],
                obs $$ [Hσ Hklen2_bytes]
              ihave Hklen2 := (pointsTo_u32_as_bytes 0 (0 : UInt32) klen_u32).mpr $$ Hklen2_bytes
              have hNbound : key.length + val.length + 8 ≤ 65536 := hLen
              have hmem3 : 3 < store.wasm.mem.pages * 65536 := by
                have h := (hklenFacts 3 (u32Byte klen_u32 3) (by simp)).2
                simpa using h
              have hkeyRead : store.wasm.mem.readBytes 4 key.length = key :=
                pointsToBytes_facts_readBytes
                  (fun i b hi => (hkeyFacts i b hi).1)
                  (by simp only [show UInt32.toNat (4 : UInt32) = 4 from rfl]; omega)
              have hvalRead : store.wasm.mem.readBytes
                  (key.length + 8) val.length = val := by
                have := pointsToBytes_facts_readBytes
                  (fun i b hi => (hvalFacts i b hi).1)
                  (by have h44 : (4 + klen_u32 + 4 : UInt32).toNat = key.length + 8 := by
                          rw [show (4 + klen_u32 + 4 : UInt32) = klen_u32 + 4 + 4 from by
                            rw [hComm4k]]
                          rw [UInt32.toNat_add, hk4nowrap]
                          simp only [show UInt32.toNat (4 : UInt32) = 4 from rfl]
                          omega
                      simp only [h44, UInt32.size]; omega)
                convert this using 2
                simp [klen_u32, hklen_toNat]; omega
              have hkeyGet : getMemOrReg store.wasm 4
                  (UInt64.ofNat klen_u32.toNat) = some key := by
                rw [show UInt64.ofNat klen_u32.toNat = UInt64.ofNat key.length from
                    by simp [hklen_toNat], getMemOrReg_mem]
                · simp [u64_toNat_of_u32_len key.length hKey]; exact hkeyRead
                · exact u64_ofNat_ne_u64Max_of_u32_len key.length hKey
                · simp only [u64_toNat_of_u32_len key.length hKey, memBytes]
                  rcases Nat.eq_zero_or_pos key.length with hz | hpos
                  · simp only [show UInt64.toNat (4 : UInt64) = 4 from rfl]; omega
                  · exact pointsToBytes_facts_bound hkeyFacts hpos
                      (by simp only [show UInt32.toNat (4 : UInt32) = 4 from rfl];
                          omega)
              have hvalGet : getMemOrReg store.wasm
                  (UInt64.ofNat klen_u32.toNat + 8)
                  (UInt64.ofNat (UInt32.ofNat val.length).toNat) = some val := by
                rw [show UInt64.ofNat klen_u32.toNat = UInt64.ofNat key.length from
                    by simp [hklen_toNat],
                    show UInt64.ofNat (UInt32.ofNat val.length).toNat =
                        UInt64.ofNat val.length from by
                      simp [Nat.mod_eq_of_lt hVal],
                    getMemOrReg_mem]
                · simp [u64_key_add8_toNat key hKey, u64_toNat_of_u32_len val.length hVal]
                  exact hvalRead
                · exact u64_ofNat_ne_u64Max_of_u32_len val.length hVal
                · simp only [u64_key_add8_toNat key hKey, u64_toNat_of_u32_len val.length hVal,
                              memBytes]
                  rcases Nat.eq_zero_or_pos val.length with hz | hpos
                  · omega
                  · have := pointsToBytes_facts_bound hvalFacts hpos
                        (by simp [klen_u32, hklen_toNat]; omega)
                    simp [klen_u32, hklen_toNat] at this; omega
              have hxfer := @twp_near_storageWrite
                  (P := iprop(pointsToBytes 0 4 key ∗
                    pointsToBytes 0 (4 + klen_u32 + 4) val ∗
                    pointsTo_u32 0 (0 : UInt32) klen_u32 ∗
                    pointsTo_u32 0 (4 + klen_u32) (UInt32.ofNat val.length)))
                  hlc inst ns1 key val «module»
                  (UInt64.ofNat klen_u32.toNat) 4
                  (UInt64.ofNat (UInt32.ofNat val.length).toNat)
                  (UInt64.ofNat klen_u32.toNat + 8) 1
                  store ns obs nt
                  hView' hkeyGet hvalGet hKeyLim' hValLim' hMaxReg'
                  hModule results5 postWasm hinvoke
              imod hxfer $$ [$HP2 $Hkey_raw2 $Hval_raw2 $Hklen2 $Hvlen2 $Hσ] with
                ⟨⟨⟨%ns_final, Hhost_final, %hStorageFacts⟩, HcP⟩, Hσ2⟩
              have hresults5 : results5 = [.i64 0] ∨ results5 = [.i64 1] := by
                have hView_host : store.wasm.host.context.isView = false := heq ▸ hView'
                have hKeyLim_host : withinLimit store.wasm.host.config.maxStorageKeyLen key.length = true :=
                  heq ▸ hKeyLim'
                have hValLim_host : withinLimit store.wasm.host.config.maxStorageValueLen val.length = true :=
                  heq ▸ hValLim'
                cases hOld : ns1.storage key with
                | none =>
                  have hStorage' : store.wasm.host.storage key = none := by
                    rw [heq]; exact hOld
                  have := storageWriteFn_invoke_absent store.wasm key val
                      (UInt64.ofNat klen_u32.toNat) 4
                      (UInt64.ofNat (UInt32.ofNat val.length).toNat)
                      (UInt64.ofNat klen_u32.toNat + 8) 1
                      hView_host hkeyGet hvalGet hKeyLim_host hValLim_host hStorage'
                  have hinvoke_flat : storageWriteFn.invoke store.wasm
                      [.i64 (UInt64.ofNat klen_u32.toNat), .i64 4,
                       .i64 (UInt64.ofNat (UInt32.ofNat val.length).toNat),
                       .i64 (UInt64.ofNat klen_u32.toNat + 8), .i64 1] =
                      .Return results5 postWasm := hinvoke
                  rw [this] at hinvoke_flat; simp at hinvoke_flat
                  exact Or.inl hinvoke_flat.1.symm
                | some old =>
                  have hStorage' : store.wasm.host.storage key = some old := by
                    rw [heq]; exact hOld
                  have hLim : withinLimit ns1.config.maxRegisterLen old.length = true := by
                    simp only [ns1, NearState.setRegister]
                    exact hMaxReg old (by simp [ns1, NearState.setRegister] at hOld; exact hOld)
                  have hLim_host : withinLimit store.wasm.host.config.maxRegisterLen old.length = true := by
                    rw [heq]; exact hLim
                  obtain ⟨stReg, hChecked⟩ :
                      ∃ stReg, checkedSetRegister? store.wasm 1 old = some stReg := by
                    simp only [checkedSetRegister?,
                               show ¬ (1 : UInt64) = u64Max from by decide, ite_false,
                               ite_eq_left hLim_host]
                    exact ⟨_, rfl⟩
                  have := storageWriteFn_invoke_present store.wasm key val old
                      (UInt64.ofNat klen_u32.toNat) 4
                      (UInt64.ofNat (UInt32.ofNat val.length).toNat)
                      (UInt64.ofNat klen_u32.toNat + 8) 1 stReg
                      hView_host hkeyGet hvalGet hKeyLim_host hValLim_host hStorage' hChecked
                  have hinvoke_flat : storageWriteFn.invoke store.wasm
                      [.i64 (UInt64.ofNat klen_u32.toNat), .i64 4,
                       .i64 (UInt64.ofNat (UInt32.ofNat val.length).toNat),
                       .i64 (UInt64.ofNat klen_u32.toNat + 8), .i64 1] =
                      .Return results5 postWasm := hinvoke
                  rw [this] at hinvoke_flat; simp at hinvoke_flat
                  exact Or.inr hinvoke_flat.1.symm
              imodintro
              isplitl [Hhost_final HcP]
              · isplitr [Hhost_final HcP]
                · ipureexact hresults5
                · isplitr [HcP]
                  · iexists ns_final; isplitl_exact Hhost_final; ipureexact hStorageFacts
                  · iexact HcP
              · iexact Hσ2)
            (fun store ns obs nt _ postWasm msg hinvoke => by
              iintro ⟨⟨HP2, Hkey_raw2, Hval_raw2, Hklen2, _⟩, Hσ⟩
              ihave %heq : ⌜store.wasm.host = ns1⌝ $$ [Hσ HP2]
              · iapply (stateInterp_host_agree store ns obs nt ns1); iframe Hσ HP2
              have hView' : store.wasm.host.context.isView = false := by
                rw [heq]; simp only [ns1, NearState.setRegister]; exact hView
              have hKeyLim' : withinLimit store.wasm.host.config.maxStorageKeyLen key.length = true := by
                rw [heq]; simp only [ns1, NearState.setRegister]; exact hKeyLim
              have hValLim' : withinLimit store.wasm.host.config.maxStorageValueLen val.length = true := by
                rw [heq]; simp only [ns1, NearState.setRegister]; exact hValLim
              wasm_points_to_bytes_agree hkeyFacts, (4 : UInt32), key, obs $$
                [Hσ Hkey_raw2]
              wasm_points_to_bytes_agree hvalFacts, (4 + klen_u32 + 4), val, obs $$
                [Hσ Hval_raw2]
              ihave Hklen2_bytes := (pointsTo_u32_as_bytes 0 (0 : UInt32) klen_u32).mp $$ Hklen2
              wasm_points_to_bytes_agree hklenFacts, (0 : UInt32),
                [u32Byte klen_u32 0, u32Byte klen_u32 1, u32Byte klen_u32 2, u32Byte klen_u32 3],
                obs $$ [Hσ Hklen2_bytes]
              have hNbound : key.length + val.length + 8 ≤ 65536 := hLen
              have hmem3 : 3 < store.wasm.mem.pages * 65536 := by
                have h := (hklenFacts 3 (u32Byte klen_u32 3) (by simp)).2
                simpa using h
              have hkeyRead : store.wasm.mem.readBytes 4 key.length = key :=
                pointsToBytes_facts_readBytes (fun i b hi => (hkeyFacts i b hi).1)
                  (by simp only [show UInt32.toNat (4 : UInt32) = 4 from rfl]; omega)
              have hvalRead : store.wasm.mem.readBytes (key.length + 8) val.length = val := by
                have := pointsToBytes_facts_readBytes (fun i b hi => (hvalFacts i b hi).1)
                  (by have h44 : (4 + klen_u32 + 4 : UInt32).toNat = key.length + 8 := by
                          rw [show (4 + klen_u32 + 4 : UInt32) = klen_u32 + 4 + 4 from by
                            rw [hComm4k]]
                          rw [UInt32.toNat_add, hk4nowrap]
                          simp only [show UInt32.toNat (4 : UInt32) = 4 from rfl]
                          omega
                      simp only [h44, UInt32.size]; omega)
                convert this using 2; simp [klen_u32, hklen_toNat]; omega
              have hkeyGet : getMemOrReg store.wasm 4
                  (UInt64.ofNat klen_u32.toNat) = some key := by
                rw [show UInt64.ofNat klen_u32.toNat = UInt64.ofNat key.length from
                    by simp [hklen_toNat], getMemOrReg_mem]
                · simp [u64_toNat_of_u32_len key.length hKey]; exact hkeyRead
                · exact u64_ofNat_ne_u64Max_of_u32_len key.length hKey
                · simp only [u64_toNat_of_u32_len key.length hKey, memBytes]
                  rcases Nat.eq_zero_or_pos key.length with hz | hpos
                  · simp only [show UInt64.toNat (4 : UInt64) = 4 from rfl]; omega
                  · exact pointsToBytes_facts_bound hkeyFacts hpos
                      (by simp only [show UInt32.toNat (4 : UInt32) = 4 from rfl];
                          omega)
              have hvalGet : getMemOrReg store.wasm
                  (UInt64.ofNat klen_u32.toNat + 8)
                  (UInt64.ofNat (UInt32.ofNat val.length).toNat) = some val := by
                rw [show UInt64.ofNat klen_u32.toNat = UInt64.ofNat key.length from
                    by simp [hklen_toNat],
                    show UInt64.ofNat (UInt32.ofNat val.length).toNat =
                        UInt64.ofNat val.length from by
                      simp [Nat.mod_eq_of_lt hVal],
                    getMemOrReg_mem]
                · simp [u64_key_add8_toNat key hKey, u64_toNat_of_u32_len val.length hVal]
                  exact hvalRead
                · exact u64_ofNat_ne_u64Max_of_u32_len val.length hVal
                · simp only [u64_key_add8_toNat key hKey, u64_toNat_of_u32_len val.length hVal,
                              memBytes]
                  rcases Nat.eq_zero_or_pos val.length with hz | hpos
                  · omega
                  · have := pointsToBytes_facts_bound hvalFacts hpos
                        (by simp [klen_u32, hklen_toNat]; omega)
                    simp [klen_u32, hklen_toNat] at this; omega
              obtain ⟨results', postWasm', hret⟩ :=
                  storageWriteFn_isReturn store.wasm key val klen_u32 ns1 heq
                    hView' hKeyLim' hValLim' hkeyGet hvalGet
                    (fun old hOld => by
                      simp only [ns1, NearState.setRegister] at hOld
                      exact hMaxReg old hOld)
              have hinvoke_flat : storageWriteFn.invoke store.wasm
                  [.i64 (UInt64.ofNat klen_u32.toNat), .i64 4,
                   .i64 (UInt64.ofNat (UInt32.ofNat val.length).toNat),
                   .i64 (UInt64.ofNat klen_u32.toNat + 8), .i64 1] =
                  .Trap postWasm msg := hinvoke
              rw [hret] at hinvoke_flat; contradiction)
            (fun store ns obs nt _ postWasm tag xs hinvoke => by
              iintro ⟨⟨HP2, Hkey_raw2, Hval_raw2, Hklen2, _⟩, Hσ⟩
              ihave %heq : ⌜store.wasm.host = ns1⌝ $$ [Hσ HP2]
              · iapply (stateInterp_host_agree store ns obs nt ns1); iframe Hσ HP2
              have hView' : store.wasm.host.context.isView = false := by
                rw [heq]; simp only [ns1, NearState.setRegister]; exact hView
              have hKeyLim' : withinLimit store.wasm.host.config.maxStorageKeyLen key.length = true := by
                rw [heq]; simp only [ns1, NearState.setRegister]; exact hKeyLim
              have hValLim' : withinLimit store.wasm.host.config.maxStorageValueLen val.length = true := by
                rw [heq]; simp only [ns1, NearState.setRegister]; exact hValLim
              wasm_points_to_bytes_agree hkeyFacts, (4 : UInt32), key, obs $$
                [Hσ Hkey_raw2]
              wasm_points_to_bytes_agree hvalFacts, (4 + klen_u32 + 4), val, obs $$
                [Hσ Hval_raw2]
              ihave Hklen2_bytes := (pointsTo_u32_as_bytes 0 (0 : UInt32) klen_u32).mp $$ Hklen2
              wasm_points_to_bytes_agree hklenFacts, (0 : UInt32),
                [u32Byte klen_u32 0, u32Byte klen_u32 1, u32Byte klen_u32 2, u32Byte klen_u32 3],
                obs $$ [Hσ Hklen2_bytes]
              have hNbound : key.length + val.length + 8 ≤ 65536 := hLen
              have hmem3 : 3 < store.wasm.mem.pages * 65536 := by
                have h := (hklenFacts 3 (u32Byte klen_u32 3) (by simp)).2
                simpa using h
              have hkeyRead : store.wasm.mem.readBytes 4 key.length = key :=
                pointsToBytes_facts_readBytes (fun i b hi => (hkeyFacts i b hi).1)
                  (by simp only [show UInt32.toNat (4 : UInt32) = 4 from rfl]; omega)
              have hvalRead : store.wasm.mem.readBytes (key.length + 8) val.length = val := by
                have := pointsToBytes_facts_readBytes (fun i b hi => (hvalFacts i b hi).1)
                  (by have h44 : (4 + klen_u32 + 4 : UInt32).toNat = key.length + 8 := by
                          rw [show (4 + klen_u32 + 4 : UInt32) = klen_u32 + 4 + 4 from by
                            rw [hComm4k]]
                          rw [UInt32.toNat_add, hk4nowrap]
                          simp only [show UInt32.toNat (4 : UInt32) = 4 from rfl]
                          omega
                      simp only [h44, UInt32.size]; omega)
                convert this using 2; simp [klen_u32, hklen_toNat]; omega
              have hkeyGet : getMemOrReg store.wasm 4
                  (UInt64.ofNat klen_u32.toNat) = some key := by
                rw [show UInt64.ofNat klen_u32.toNat = UInt64.ofNat key.length from
                    by simp [hklen_toNat], getMemOrReg_mem]
                · simp [u64_toNat_of_u32_len key.length hKey]; exact hkeyRead
                · exact u64_ofNat_ne_u64Max_of_u32_len key.length hKey
                · simp only [u64_toNat_of_u32_len key.length hKey, memBytes]
                  rcases Nat.eq_zero_or_pos key.length with hz | hpos
                  · simp only [show UInt64.toNat (4 : UInt64) = 4 from rfl]; omega
                  · exact pointsToBytes_facts_bound hkeyFacts hpos
                      (by simp only [show UInt32.toNat (4 : UInt32) = 4 from rfl];
                          omega)
              have hvalGet : getMemOrReg store.wasm
                  (UInt64.ofNat klen_u32.toNat + 8)
                  (UInt64.ofNat (UInt32.ofNat val.length).toNat) = some val := by
                rw [show UInt64.ofNat klen_u32.toNat = UInt64.ofNat key.length from
                    by simp [hklen_toNat],
                    show UInt64.ofNat (UInt32.ofNat val.length).toNat =
                        UInt64.ofNat val.length from by
                      simp [Nat.mod_eq_of_lt hVal],
                    getMemOrReg_mem]
                · simp [u64_key_add8_toNat key hKey, u64_toNat_of_u32_len val.length hVal]
                  exact hvalRead
                · exact u64_ofNat_ne_u64Max_of_u32_len val.length hVal
                · simp only [u64_key_add8_toNat key hKey, u64_toNat_of_u32_len val.length hVal,
                              memBytes]
                  rcases Nat.eq_zero_or_pos val.length with hz | hpos
                  · omega
                  · have := pointsToBytes_facts_bound hvalFacts hpos
                        (by simp [klen_u32, hklen_toNat]; omega)
                    simp [klen_u32, hklen_toNat] at this; omega
              obtain ⟨results', postWasm', hret⟩ :=
                  storageWriteFn_isReturn store.wasm key val klen_u32 ns1 heq
                    hView' hKeyLim' hValLim' hkeyGet hvalGet
                    (fun old hOld => by
                      simp only [ns1, NearState.setRegister] at hOld
                      exact hMaxReg old hOld)
              have hinvoke_flat : storageWriteFn.invoke store.wasm
                  [.i64 (UInt64.ofNat klen_u32.toNat), .i64 4,
                   .i64 (UInt64.ofNat (UInt32.ofNat val.length).toNat),
                   .i64 (UInt64.ofNat klen_u32.toNat + 8), .i64 1] =
                  .Throw postWasm tag xs := hinvoke
              rw [hret] at hinvoke_flat; contradiction)
            $$ [$Hhost2 $Hkey_raw $Hval_raw $Hklen $Hvlen] Hruntime2 Henv2_back
        · iintro %_pre %results5 %_post %_hinvoke
              ⟨⟨%hresults5, ⟨%ns_final, Hhost_final, %hStorageFacts⟩, _, _, _, _⟩,
               Hruntime3⟩
          obtain ⟨v, rfl⟩ : ∃ v : UInt64, results5 = [Value.i64 v] := by
            rcases hresults5 with rfl | rfl <;> exact ⟨_, rfl⟩
          simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero,
            List.drop_succ_cons, List.drop_zero, List.append_nil]
          wasm_twp_pures [twp_drop]
          wasm_twp_terminal_value (twp_finish (locals := { }))
          iintro %store_final %_obs Hσ_final
          ihave %hfinalHost : ⌜store_final.wasm.host = ns_final⌝ $$ [Hσ_final Hhost_final]
          · iapply (stateInterp_host_agree store_final 0 [] 0 ns_final)
            iframe Hσ_final Hhost_final
          ipureexact ⟨hfinalHost ▸ hStorageFacts.1,
            fun k hk => hfinalHost ▸ hStorageFacts.2 k hk⟩
        · iintro %_pre %_post %_msg %_h Hfalse; iexfalso; iexact Hfalse
        · iintro %_pre %_post %_tag %_xs %_h Hfalse; iexfalso; iexact Hfalse
      · iintro %_pre %_post %_msg %_h Hfalse; iexfalso; iexact Hfalse
      · iintro %_pre %_post %_tag %_xs %_h Hfalse; iexfalso; iexact Hfalse
    · iintro %_pre %_results %_post %_h Hfalse; iexfalso; iexact Hfalse
    · iintro %_pre %_post %_tag %_xs %_h Hfalse; iexfalso; iexact Hfalse

theorem set_partiallyMeets (nearSt : NearState) (key val : List UInt8)
    (hView : nearSt.context.isView = false)
    (hKey : key.length < 4294967296) (hVal : val.length < 4294967296)
    (hLen : key.length + val.length + 8 ≤ 65536)
    (hReg : withinLimit nearSt.config.maxRegisterLen (encodeKV key val).length)
    (hKeyLim : withinLimit nearSt.config.maxStorageKeyLen key.length)
    (hValLim : withinLimit nearSt.config.maxStorageValueLen val.length)
    (hMaxReg : ∀ old, nearSt.storage key = some old →
        withinLimit nearSt.config.maxRegisterLen old.length)
    (hInput : nearSt.context.input = encodeKV key val) :
    SmallStep.PartiallyMeets (setConfig nearSt)
      (fun _ store => store.wasm.host.storage key = some val ∧
        ∀ k, k ≠ key → store.wasm.host.storage k = nearSt.storage k) :=
  (set_terminatesWith nearSt key val hView hKey hVal hLen hReg hKeyLim hValLim hMaxReg hInput).toPartiallyMeets

/-! ## Concrete end-to-end validation

These run the contract through the interpreter on a concrete input and
check the resulting storage projection, exercising the entire host
pipeline. The kernel checks each resulting storage projection. -/

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
theorem demo_ranOk : ranOk demoNs = true := by cbv

/-- After the call, the parsed key holds the parsed value. -/
theorem demo_stored : storedAt demoNs [1, 2] = some [7, 8, 9] := by cbv

/-- Frame: a key that was not written stays absent. -/
theorem demo_frame_absent : storedAt demoNs [9, 9] = none := by cbv

/-- Frame against a non-empty incoming store: a pre-existing unrelated key
survives the write untouched. -/
def demoNs2 : NearState :=
  { storage := fun k => if k = [42] then some [100] else none
    context := { input := encodeKV [1, 2] [7, 8, 9] } }

theorem demo2_stored : storedAt demoNs2 [1, 2] = some [7, 8, 9] := by cbv

theorem demo2_frame_other : storedAt demoNs2 [42] = some [100] := by cbv

/-! ## Host semantic regression checks -/

def initialWith (ns : NearState) : Store NearState :=
  { («module».initialStore : Store NearState) with host := ns }

/-- Guest-memory inputs must trap when the requested range exceeds memory. -/
def valueReturnOobTraps : Bool :=
  match valueReturnFn.invoke (initialWith {}) [.i64 1, .i64 (UInt64.ofNat 65536)] with
  | .Trap _ _ => true
  | _         => false

theorem value_return_oob_traps : valueReturnOobTraps = true := by decide +kernel

/-- Output `register_id = u64::MAX` discards the output instead of writing
to an actual register with that numeric id. -/
def inputMaxDiscards : Bool :=
  match inputFn.invoke (initialWith { context := { input := [1, 2, 3] } }) [.i64 u64Max] with
  | .Return [] st => (st.host.registers u64Max.toNat).isNone
  | _             => false

theorem input_max_discards : inputMaxDiscards = true := by decide +kernel

def storageReadMaxDiscards : Bool :=
  let ns : NearState :=
    { storage := fun k => if k = [1] then some [2] else none
      registers := fun i => if i = 0 then some [1] else none }
  match storageReadFn.invoke (initialWith ns) [.i64 u64Max, .i64 0, .i64 u64Max] with
  | .Return [.i64 1] st => (st.host.registers u64Max.toNat).isNone
  | _                   => false

theorem storage_read_max_discards : storageReadMaxDiscards = true := by decide +kernel

def resolvesImportSubset : Bool :=
  match resolveImports?
      [ { «module» := "env", name := "current_account_id", params := [.i64], results := [] }
      , { «module» := "env", name := "storage_write",
          params := [.i64, .i64, .i64, .i64, .i64], results := [.i64] } ] with
  | some env => env.funcs.length == 2
  | none     => false

theorem resolve_import_subset : resolvesImportSubset = true := by decide +kernel

def rejectsBadImportSignature : Bool :=
  match resolveImports?
      [ { «module» := "env", name := "storage_write",
          params := [.i64, .i64], results := [.i64] } ] with
  | none   => true
  | some _ => false

theorem reject_bad_import_signature : rejectsBadImportSignature = true := by decide +kernel

def resolvesSpecSubset : Bool :=
  match resolveContracts?
      [ { «module» := "env", name := "current_account_id", params := [.i64], results := [] }
      , { «module» := "env", name := "storage_write",
          params := [.i64, .i64, .i64, .i64, .i64], results := [.i64] } ] with
  | some spec => spec.contracts.length == 2
  | none      => false

theorem resolve_spec_subset : resolvesSpecSubset = true := by decide +kernel

def rejectsBadSpecSignature : Bool :=
  match resolveContracts?
      [ { «module» := "env", name := "storage_write",
          params := [.i64, .i64], results := [.i64] } ] with
  | none   => true
  | some _ => false

theorem reject_bad_spec_signature : rejectsBadSpecSignature = true := by decide +kernel

def currentAccountWritesRegister : Bool :=
  let ns : NearState := { context := { currentAccountId := [99, 100] } }
  match currentAccountIdFn.invoke (initialWith ns) [.i64 7] with
  | .Return [] st => st.host.registers 7 == some [99, 100]
  | _             => false

theorem current_account_writes_register : currentAccountWritesRegister = true := by decide +kernel

def accountBalanceWritesU128 : Bool :=
  let ns : NearState := { context := { accountBalance := 258 } }
  match accountBalanceFn.invoke (initialWith ns) [.i64 0] with
  | .Return [] st => st.mem.readBytes 0 16 == leU128Bytes 258
  | _             => false

theorem account_balance_writes_u128 : accountBalanceWritesU128 = true := by decide +kernel

def sha256HookWritesRegister : Bool :=
  let ns : NearState := { sha256 := fun bs => bs ++ [9] }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match sha256Fn.invoke st [.i64 2, .i64 0, .i64 5] with
  | .Return [] st' => st'.host.registers 5 == some [1, 2, 9]
  | _              => false

theorem sha256_hook_writes_register : sha256HookWritesRegister = true := by decide +kernel

def randomSeedWritesRegister : Bool :=
  let ns : NearState := { randomSeed := [4, 5, 6] }
  match randomSeedFn.invoke (initialWith ns) [.i64 3] with
  | .Return [] st => st.host.registers 3 == some [4, 5, 6]
  | _             => false

theorem random_seed_writes_register : randomSeedWritesRegister = true := by decide +kernel

def storageWriteViewTraps : Bool :=
  let ns : NearState := { context := { isView := true } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match storageWriteFn.invoke st [.i64 1, .i64 0, .i64 1, .i64 1, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem storage_write_view_traps : storageWriteViewTraps = true := by decide +kernel

def storageReadAllowedInView : Bool :=
  let ns : NearState :=
    { storage := fun k => if k = [1] then some [9] else none
      context := { isView := true } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1] }
  match storageReadFn.invoke st [.i64 1, .i64 0, .i64 4] with
  | .Return [.i64 1] st' => st'.host.registers 4 == some [9]
  | _                    => false

theorem storage_read_allowed_in_view : storageReadAllowedInView = true := by decide +kernel

def attachedDepositViewTraps : Bool :=
  let ns : NearState := { context := { isView := true, attachedDeposit := 7 } }
  match attachedDepositFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem attached_deposit_view_traps : attachedDepositViewTraps = true := by decide +kernel

def signerAccountViewTraps : Bool :=
  let ns : NearState := { context := { isView := true, signerAccountId := [1] } }
  match signerAccountIdFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem signer_account_view_traps : signerAccountViewTraps = true := by decide +kernel

def promiseResultsCountWorks : Bool :=
  let ns : NearState := { promiseResults := [.notReady, .successful [7], .failed] }
  match promiseResultsCountFn.invoke (initialWith ns) [] with
  | .Return [.i64 n] _ => n == 3
  | _                  => false

theorem promise_results_count_works : promiseResultsCountWorks = true := by decide +kernel

def promiseResultSuccessWritesRegister : Bool :=
  let ns : NearState := { promiseResults := [.notReady, .successful [7, 8], .failed] }
  match promiseResultFn.invoke (initialWith ns) [.i64 1, .i64 9] with
  | .Return [.i64 1] st => st.host.registers 9 == some [7, 8]
  | _                   => false

theorem promise_result_success_writes_register :
    promiseResultSuccessWritesRegister = true := by decide +kernel

def promiseResultFailedLeavesRegister : Bool :=
  let ns : NearState :=
    { promiseResults := [.failed]
      registers := fun i => if i = 9 then some [1] else none }
  match promiseResultFn.invoke (initialWith ns) [.i64 0, .i64 9] with
  | .Return [.i64 2] st => st.host.registers 9 == some [1]
  | _                   => false

theorem promise_result_failed_leaves_register :
    promiseResultFailedLeavesRegister = true := by decide +kernel

def promiseResultBadIndexTraps : Bool :=
  let ns : NearState := { promiseResults := [.successful [7]] }
  match promiseResultFn.invoke (initialWith ns) [.i64 1, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem promise_result_bad_index_traps : promiseResultBadIndexTraps = true := by decide +kernel

def promiseResultViewTraps : Bool :=
  let ns : NearState := { context := { isView := true }, promiseResults := [.successful [7]] }
  match promiseResultFn.invoke (initialWith ns) [.i64 0, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem promise_result_view_traps : promiseResultViewTraps = true := by decide +kernel

def promiseReturnRecordsPromise : Bool :=
  let ns : NearState := { promises := [.batch [1] [], .batch [2] []] }
  match promiseReturnFn.invoke (initialWith ns) [.i64 1] with
  | .Return [] st => st.host.returnedPromise == some 1
  | _             => false

theorem promise_return_records_promise : promiseReturnRecordsPromise = true := by decide +kernel

def promiseReturnBadIndexTraps : Bool :=
  let ns : NearState := { promises := [.batch [1] []] }
  match promiseReturnFn.invoke (initialWith ns) [.i64 1] with
  | .Trap _ _ => true
  | _         => false

theorem promise_return_bad_index_traps : promiseReturnBadIndexTraps = true := by decide +kernel

def promiseBatchCreateRecordsAccount : Bool :=
  let st0 := initialWith {}
  let st := { st0 with mem := st0.mem.writeBytes 0 [10, 11] }
  match promiseBatchCreateFn.invoke st [.i64 2, .i64 0] with
  | .Return [.i64 0] st' => st'.host.promises == [.batch [10, 11] []]
  | _                    => false

theorem promise_batch_create_records_account :
    promiseBatchCreateRecordsAccount = true := by decide +kernel

def promiseCreateRecordsFunctionCall : Bool :=
  let st0 := initialWith {}
  let st1 := { st0 with mem := st0.mem.writeBytes 0 [10, 11] }
  let st2 := { st1 with mem := st1.mem.writeBytes 8 [109] }
  let st3 := { st2 with mem := st2.mem.writeBytes 16 [7] }
  let st := { st3 with mem := st3.mem.writeBytes 24 (leU128Bytes 5) }
  match promiseCreateFn.invoke st [.i64 2, .i64 0, .i64 1, .i64 8, .i64 1, .i64 16, .i64 24, .i64 30] with
  | .Return [.i64 0] st' =>
    st'.host.promises ==
      [.batch [10, 11] [PromiseAction.functionCall [109] [7] 5 30]]
  | _ => false

theorem promise_create_records_function_call :
    promiseCreateRecordsFunctionCall = true := by decide +kernel

def promiseThenRecordsCallback : Bool :=
  let ns : NearState := { promises := [.batch [1] []] }
  let st0 := initialWith ns
  let st1 := { st0 with mem := st0.mem.writeBytes 0 [10] }
  let st2 := { st1 with mem := st1.mem.writeBytes 8 [109] }
  let st3 := { st2 with mem := st2.mem.writeBytes 16 [7] }
  let st := { st3 with mem := st3.mem.writeBytes 24 (leU128Bytes 5) }
  match promiseThenFn.invoke st [.i64 0, .i64 1, .i64 0, .i64 1, .i64 8, .i64 1, .i64 16, .i64 24, .i64 30] with
  | .Return [.i64 1] st' =>
    st'.host.promises ==
      [.batch [1] [], .callback 0 [10] [PromiseAction.functionCall [109] [7] 5 30]]
  | _ => false

theorem promise_then_records_callback :
    promiseThenRecordsCallback = true := by decide +kernel

def promiseAndRecordsDependencies : Bool :=
  let ns : NearState := { promises := [.batch [1] [], .batch [2] []] }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 (le64 0 ++ le64 1) }
  match promiseAndFn.invoke st [.i64 0, .i64 2] with
  | .Return [.i64 2] st' =>
    st'.host.promises == [.batch [1] [], .batch [2] [], .and [0, 1]]
  | _ => false

theorem promise_and_records_dependencies :
    promiseAndRecordsDependencies = true := by decide +kernel

def promiseBatchFunctionCallAppendsAction : Bool :=
  let ns : NearState := { promises := [.batch [1] []] }
  let st0 := initialWith ns
  let st1 := { st0 with mem := st0.mem.writeBytes 0 [109] }
  let st2 := { st1 with mem := st1.mem.writeBytes 8 [7] }
  let st := { st2 with mem := st2.mem.writeBytes 16 (leU128Bytes 5) }
  match promiseBatchActionFunctionCallFn.invoke st [.i64 0, .i64 1, .i64 0, .i64 1, .i64 8, .i64 16, .i64 30] with
  | .Return [] st' =>
    st'.host.promises ==
      [.batch [1] [PromiseAction.functionCall [109] [7] 5 30]]
  | _ => false

theorem promise_batch_function_call_appends_action :
    promiseBatchFunctionCallAppendsAction = true := by decide +kernel

def promiseBatchTransferAppendsAction : Bool :=
  let ns : NearState := { promises := [.batch [1] []] }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 (leU128Bytes 9) }
  match promiseBatchActionTransferFn.invoke st [.i64 0, .i64 0] with
  | .Return [] st' => st'.host.promises == [.batch [1] [PromiseAction.transfer 9]]
  | _              => false

theorem promise_batch_transfer_appends_action :
    promiseBatchTransferAppendsAction = true := by decide +kernel

def promiseActionOnJointTraps : Bool :=
  let ns : NearState := { promises := [.and [0]] }
  match promiseBatchActionCreateAccountFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem promise_action_on_joint_traps : promiseActionOnJointTraps = true := by decide +kernel

def promiseBatchCreateViewTraps : Bool :=
  let ns : NearState := { context := { isView := true } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [10] }
  match promiseBatchCreateFn.invoke st [.i64 1, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem promise_batch_create_view_traps :
    promiseBatchCreateViewTraps = true := by decide +kernel

def promiseYieldCreateRecordsToken : Bool :=
  let ns : NearState :=
    { yieldCreateToken := fun method args gas weight =>
        method ++ args ++ [UInt8.ofNat gas.toNat, UInt8.ofNat weight.toNat] }
  let st0 := initialWith ns
  let st1 := { st0 with mem := st0.mem.writeBytes 0 [109] }
  let st := { st1 with mem := st1.mem.writeBytes 8 [7] }
  match promiseYieldCreateFn.invoke st [.i64 1, .i64 0, .i64 1, .i64 8, .i64 3, .i64 4, .i64 9] with
  | .Return [.i64 0] st' =>
    st'.host.registers 9 == some [109, 7, 3, 4] &&
      st'.host.promises == [.yielded [109] [7] 3 4 [109, 7, 3, 4]]
  | _ => false

theorem promise_yield_create_records_token :
    promiseYieldCreateRecordsToken = true := by decide +kernel

def promiseYieldResumeRecordsPayload : Bool :=
  let ns : NearState := { promises := [.yielded [109] [7] 3 4 [1, 2]] }
  let st0 := initialWith ns
  let st1 := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  let st := { st1 with mem := st1.mem.writeBytes 8 [9] }
  match promiseYieldResumeFn.invoke st [.i64 2, .i64 0, .i64 1, .i64 8] with
  | .Return [.i64 1] st' => st'.host.yieldResumes == [([1, 2], [9])]
  | _                    => false

theorem promise_yield_resume_records_payload :
    promiseYieldResumeRecordsPayload = true := by decide +kernel

def promiseYieldResumeUnknownReturnsZero : Bool :=
  let ns : NearState := { promises := [.yielded [109] [7] 3 4 [1, 2]] }
  let st0 := initialWith ns
  let st1 := { st0 with mem := st0.mem.writeBytes 0 [3, 4] }
  let st := { st1 with mem := st1.mem.writeBytes 8 [9] }
  match promiseYieldResumeFn.invoke st [.i64 2, .i64 0, .i64 1, .i64 8] with
  | .Return [.i64 0] st' => st'.host.yieldResumes == []
  | _                    => false

theorem promise_yield_resume_unknown_returns_zero :
    promiseYieldResumeUnknownReturnsZero = true := by decide +kernel

def promiseYieldCreateViewTraps : Bool :=
  let ns : NearState := { context := { isView := true } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [109] }
  match promiseYieldCreateFn.invoke st [.i64 1, .i64 0, .i64 0, .i64 0, .i64 3, .i64 4, .i64 9] with
  | .Trap _ _ => true
  | _         => false

theorem promise_yield_create_view_traps :
    promiseYieldCreateViewTraps = true := by decide +kernel

def iterNs : NearState :=
  { storage := fun k =>
      if k = [1, 2] then some [7]
      else if k = [1, 3] then some [8]
      else if k = [2] then some [9]
      else none
    storageKeys := [[1, 2], [1, 3], [2]] }

def storageIterPrefixNextWorks : Bool :=
  let st0 := initialWith iterNs
  let st := { st0 with mem := st0.mem.writeBytes 0 [1] }
  match storageIterPrefixFn.invoke st [.i64 1, .i64 0] with
  | .Return [.i64 0] st' =>
    match storageIterNextFn.invoke st' [.i64 0, .i64 4, .i64 5] with
    | .Return [.i64 1] st'' =>
      st''.host.registers 4 == some [1, 2] &&
        st''.host.registers 5 == some [7]
    | _ => false
  | _ => false

theorem storage_iter_prefix_next_works :
    storageIterPrefixNextWorks = true := by decide +kernel

def storageIterRangeNextWorks : Bool :=
  let st0 := initialWith iterNs
  let st1 := { st0 with mem := st0.mem.writeBytes 0 [1] }
  let st := { st1 with mem := st1.mem.writeBytes 8 [2] }
  match storageIterRangeFn.invoke st [.i64 1, .i64 0, .i64 1, .i64 8] with
  | .Return [.i64 0] st' =>
    match storageIterNextFn.invoke st' [.i64 0, .i64 4, .i64 5] with
    | .Return [.i64 1] st'' =>
      st''.host.registers 4 == some [1, 2] &&
        st''.host.registers 5 == some [7]
    | _ => false
  | _ => false

theorem storage_iter_range_next_works :
    storageIterRangeNextWorks = true := by decide +kernel

def storageIterDuplicateRegistersTrap : Bool :=
  let st0 := initialWith iterNs
  let st := { st0 with mem := st0.mem.writeBytes 0 [1] }
  match storageIterPrefixFn.invoke st [.i64 1, .i64 0] with
  | .Return [.i64 0] st' =>
    match storageIterNextFn.invoke st' [.i64 0, .i64 4, .i64 4] with
    | .Trap _ _ => true
    | _         => false
  | _ => false

theorem storage_iter_duplicate_registers_trap :
    storageIterDuplicateRegistersTrap = true := by decide +kernel

def storageWriteInvalidatesIterators : Bool :=
  let st0 := initialWith iterNs
  let st1 := { st0 with mem := st0.mem.writeBytes 0 [1] }
  match storageIterPrefixFn.invoke st1 [.i64 1, .i64 0] with
  | .Return [.i64 0] stIter =>
    let st2 := { stIter with mem := stIter.mem.writeBytes 16 [3, 4] }
    match storageWriteFn.invoke st2 [.i64 1, .i64 16, .i64 1, .i64 17, .i64 0] with
    | .Return [.i64 0] stWritten => (stWritten.host.iterators 0).isNone
    | _ => false
  | _ => false

theorem storage_write_invalidates_iterators :
    storageWriteInvalidatesIterators = true := by decide +kernel

def inputRegisterLimitTraps : Bool :=
  let ns : NearState :=
    { context := { input := [1, 2, 3] }
      config := { maxRegisterLen := some 2 } }
  match inputFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem input_register_limit_traps : inputRegisterLimitTraps = true := by decide +kernel

def valueReturnLimitTraps : Bool :=
  let ns : NearState := { config := { maxReturnLen := some 2 } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2, 3] }
  match valueReturnFn.invoke st [.i64 3, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem value_return_limit_traps : valueReturnLimitTraps = true := by decide +kernel

def storageWriteValueLimitTraps : Bool :=
  let ns : NearState := { config := { maxStorageValueLen := some 0 } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match storageWriteFn.invoke st [.i64 1, .i64 0, .i64 1, .i64 1, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem storage_write_value_limit_traps :
    storageWriteValueLimitTraps = true := by decide +kernel

def logCountLimitTraps : Bool :=
  let ns : NearState :=
    { logs := [[]]
      config := { maxNumberLogs := some 1 } }
  match logUtf8Fn.invoke (initialWith ns) [.i64 0, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem log_count_limit_traps : logCountLimitTraps = true := by decide +kernel

def logLenLimitTraps : Bool :=
  let ns : NearState := { config := { maxLogLen := some 1 } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match logUtf8Fn.invoke st [.i64 2, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem log_len_limit_traps : logLenLimitTraps = true := by decide +kernel

def logUtf8StoresRawBytes : Bool :=
  let st0 := initialWith {}
  let st := { st0 with mem := st0.mem.writeBytes 0 [255] }
  match logUtf8Fn.invoke st [.i64 1, .i64 0] with
  | .Return [] st' => st'.host.logs == [[255]]
  | _              => false

theorem log_utf8_stores_raw_bytes : logUtf8StoresRawBytes = true := by decide +kernel

def currentAccountInvalidTraps : Bool :=
  let ns : NearState :=
    { context := { currentAccountId := [1] }
      config := { validAccountId := fun _ => false } }
  match currentAccountIdFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem current_account_invalid_traps : currentAccountInvalidTraps = true := by decide +kernel

def validatorStakeInvalidAccountTraps : Bool :=
  let ns : NearState := { config := { validAccountId := fun _ => false } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1] }
  match validatorStakeFn.invoke st [.i64 1, .i64 0, .i64 8] with
  | .Trap _ _ => true
  | _         => false

theorem validator_stake_invalid_account_traps :
    validatorStakeInvalidAccountTraps = true := by decide +kernel

def signerPkInvalidTraps : Bool :=
  let ns : NearState :=
    { context := { signerAccountPk := [1, 2] }
      config := { validPublicKey := fun _ => false } }
  match signerAccountPkFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem signer_pk_invalid_traps : signerPkInvalidTraps = true := by decide +kernel

def ed25519InvalidPublicKeyTraps : Bool :=
  let ns : NearState := { config := { validPublicKey := fun _ => false } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1] }
  match ed25519VerifyFn.invoke st [.i64 0, .i64 0, .i64 0, .i64 0, .i64 1, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem ed25519_invalid_public_key_traps :
    ed25519InvalidPublicKeyTraps = true := by decide +kernel

def altBn128HookWritesRegister : Bool :=
  let ns : NearState := { altBn128G1Multiexp := fun bs => bs ++ [9] }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match altBn128G1MultiexpFn.invoke st [.i64 2, .i64 0, .i64 5] with
  | .Return [] st' => st'.host.registers 5 == some [1, 2, 9]
  | _              => false

theorem alt_bn128_hook_writes_register :
    altBn128HookWritesRegister = true := by decide +kernel

def bls12381HookWritesRegister : Bool :=
  let ns : NearState := { bls12381G1Multiexp := fun bs => (0, bs ++ [9]) }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match bls12381G1MultiexpFn.invoke st [.i64 2, .i64 0, .i64 5] with
  | .Return [.i64 0] st' => st'.host.registers 5 == some [1, 2, 9]
  | _                    => false

theorem bls12381_hook_writes_register :
    bls12381HookWritesRegister = true := by decide +kernel

def bls12381InvalidLeavesRegister : Bool :=
  let ns : NearState :=
    { bls12381G1Multiexp := fun _ => (1, [9])
      registers := fun i => if i = 5 then some [1] else none }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match bls12381G1MultiexpFn.invoke st [.i64 2, .i64 0, .i64 5] with
  | .Return [.i64 1] st' => st'.host.registers 5 == some [1]
  | _                    => false

theorem bls12381_invalid_leaves_register :
    bls12381InvalidLeavesRegister = true := by decide +kernel

def bls12381PairingStatusReturns : Bool :=
  let ns : NearState := { bls12381PairingCheck := fun _ => 1 }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match bls12381PairingCheckFn.invoke st [.i64 2, .i64 0] with
  | .Return [.i64 1] _ => true
  | _                  => false

theorem bls12381_pairing_status_returns :
    bls12381PairingStatusReturns = true := by decide +kernel

end KvSetter
end Near
end Wasm
