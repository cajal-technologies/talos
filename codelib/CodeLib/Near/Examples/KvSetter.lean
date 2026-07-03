import CodeLib.Entry
import CodeLib.Near.Proof

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
as a `def … : Prop` and fully proved (`set_spec`) via the WP layer. The
`native_decide` theorems below additionally validate the *whole pipeline*
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
  le32 key.length ++ key ++ le32 val.length ++ val

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
    rw [Nat.mod_eq_of_lt hKey]
    exact Nat.mod_eq_of_lt hKeyAddr
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
  · simp [encodeKV, le32]
    omega

@[simp] theorem readBytes_writeBytes_encode_val (m : Mem) (key val : List UInt8) :
    (m.writeBytes 0 (encodeKV key val)).readBytes (key.length + 8) val.length = val := by
  rw [show key.length + 8 = 0 + (key.length + 8) by omega]
  rw [readBytes_writeBytes_slice]
  · simp [encodeKV, le32]
  · simp [encodeKV, le32]
    omega

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
  norm_num at ht
  omega

theorem u64_key_add8_toNat (key : List UInt8) (hKey : key.length < 4294967296) :
    (UInt64.ofNat key.length + 8).toNat = key.length + 8 := by
  rw [UInt64.toNat_add]
  change ((UInt64.ofNat key.length).toNat + (8#64).toNat) %
      18446744073709551616 = key.length + 8
  rw [u64_toNat_of_u32_len key.length hKey]
  norm_num
  omega

theorem getMemOrReg_writeBytes_encode_key (st : Store NearState) (key val : List UInt8)
    (hKey : key.length < 4294967296)
    (hMem : (encodeKV key val).length ≤ memBytes st) :
    getMemOrReg { st with mem := st.mem.writeBytes 0 (encodeKV key val) }
      (4 : UInt64) (UInt64.ofNat key.length) = some key := by
  rw [getMemOrReg_mem]
  · simp [u64_toNat_of_u32_len key.length hKey]
  · exact u64_ofNat_ne_u64Max_of_u32_len key.length hKey
  · simp [u64_toNat_of_u32_len key.length hKey, memBytes, encodeKV, le32] at hMem ⊢
    omega

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

/-- **Spec for `set`.** For any non-view incoming NEAR state whose `input`
is the length-prefixed encoding of `(key, val)` (with sizes that fit a u32,
the single memory page, and the configured NEAR host limits), the call
terminates and:

* *projection after the call:* `storage[key] = val`;
* *frame condition:* every other key is unchanged from the incoming state.

The store is pinned to the module's `initialStore` (memory + globals set up
by instantiation) with the NEAR projection injected as `host := ns`, per
the repo convention for memory-touching specs. -/
def SetSpec : Prop :=
  ∀ (ns : NearState) (key val : List UInt8),
    ns.context.isView = false →
    key.length < 4294967296 → val.length < 4294967296 →
    (encodeKV key val).length ≤ 65536 →
    withinLimit ns.config.maxRegisterLen (encodeKV key val).length →
    withinLimit ns.config.maxStorageKeyLen key.length →
    withinLimit ns.config.maxStorageValueLen val.length →
    (match ns.storage key with
     | some old => withinLimit ns.config.maxRegisterLen old.length
     | none     => true) →
    ns.context.input = encodeKV key val →
    TerminatesWith nearEnv «module» setIdx
      { («module».initialStore : Store NearState) with host := ns } []
      (fun st _ =>
        st.host.storage key = some val ∧
        (∀ k, k ≠ key → st.host.storage k = ns.storage k))

def afterInputStore (ns : NearState) (key val : List UInt8) : Store NearState :=
  { globals := {}, mem := Mem.empty 1, host := ns.setRegister 0 (encodeKV key val) }

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
    · simpa [afterInputStore, memBytes, Mem.empty] using hLen
  · apply getMemOrReg_writeBytes_encode_val
    · exact hKey
    · exact hVal
    · simpa [afterInputStore, memBytes, Mem.empty] using hLen
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
    · simpa [afterInputStore, memBytes, Mem.empty] using hLen
  · apply getMemOrReg_writeBytes_encode_val
    · exact hKey
    · exact hVal
    · simpa [afterInputStore, memBytes, Mem.empty] using hLen
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hKeyLim
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hValLim
  · simpa [storageCallStore, afterInputStore, NearState.setRegister] using hOld

theorem set_spec : SetSpec := by
  intro ns key val hView hKey hVal hLen hReg hKeyLim hValLim hOldLim hInput
  apply TerminatesWith.of_wp_entry_for
    (f := { params := [], locals := [], body := setBody, results := [] })
  · simp [«module», setIdx, importCount]
  · unfold setBody
    wp_run
    refine wp_call_host_cons
      (imp := { «module» := "env", name := "input", params := [.i64], results := [] })
      (hf := inputFn) rfl rfl ?_ ?_
    · intro vs st' hInv
      simp [inputFn, writeRegisterResult, checkedSetRegister?, hInput, hReg, u64Max] at hInv
      rcases hInv with ⟨rfl, hst⟩
      subst st'
      wp_run
      have hReg0 :
          (ns.setRegister 0 (encodeKV key val)).registers 0 = some (encodeKV key val) := by
        simp [NearState.setRegister]
      have hReadBound :
          ¬ ((«module».initialStore : Store NearState).mem.pages * 65536) <
            (encodeKV key val).length := by
        change ¬ 65536 < (encodeKV key val).length
        omega
      refine wp_call_host_cons
        (imp := { «module» := "env", name := "read_register", params := [.i64, .i64], results := [] })
        (hf := readRegisterFn) rfl rfl ?_ ?_
      · intro vs st' hInv
        simp [readRegisterFn, hReg0, memBytes, hReadBound] at hInv
        rcases hInv with ⟨rfl, hst⟩
        subst st'
        wp_run
        have hEncodeLen : key.length + val.length + 8 ≤ 65536 := by
          simpa [encodeKV, le32, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLen
        have hKeyAddr : key.length + 4 < 4294967296 := by omega
        have hKeyMod : key.length % 4294967296 = key.length := Nat.mod_eq_of_lt hKey
        have hValMod : val.length % 4294967296 = val.length := Nat.mod_eq_of_lt hVal
        simp [read32_writeBytes_encode_keyLen, read32_writeBytes_encode_valLen, hKeyAddr,
          hKeyMod, hValMod, «module», Module.initialStore, Mem.empty]
        constructor
        · omega
        refine wp_call_host_cons
          (imp := { «module» := "env", name := "storage_write", params := [.i64, .i64, .i64, .i64, .i64], results := [.i64] })
          (hf := storageWriteFn) rfl rfl ?_ ?_
        · intro vs st' hInv
          simp only [List.take, List.reverse_cons, List.reverse_nil] at hInv
          change storageWriteFn.invoke (storageCallStore ns key val)
              [.i64 (UInt64.ofNat key.length), .i64 4, .i64 (UInt64.ofNat val.length),
                .i64 (UInt64.ofNat key.length + 8), .i64 1] = .Return vs st' at hInv
          cases hOldEq : ns.storage key with
          | none =>
            rw [storageWrite_invoke_encode_absent ns key val hView hKey hVal hLen
              hKeyLim hValLim hOldEq] at hInv
            injection hInv with hvs hst
            subst hvs
            subst st'
            wp_run
            constructor
            · simp [NearState.setStorage, NearState.setRegister, NearState.invalidateIterators]
            · intro k hk
              simp [NearState.setStorage, NearState.setRegister, NearState.invalidateIterators, hk]
          | some old =>
            have hOldLimOld : withinLimit ns.config.maxRegisterLen old.length = true := by
              simpa [hOldEq] using hOldLim
            rw [storageWrite_invoke_encode_present ns key val old hView hKey hVal hLen
              hKeyLim hValLim hOldEq hOldLimOld] at hInv
            injection hInv with hvs hst
            subst hvs
            subst st'
            wp_run
            constructor
            · simp [NearState.setStorage, NearState.setRegister, NearState.invalidateIterators]
            · intro k hk
              simp [NearState.setStorage, NearState.setRegister, NearState.invalidateIterators, hk]
        · intro st' msg hInv
          simp only [List.take, List.reverse_cons, List.reverse_nil] at hInv
          change storageWriteFn.invoke (storageCallStore ns key val)
              [.i64 (UInt64.ofNat key.length), .i64 4, .i64 (UInt64.ofNat val.length),
                .i64 (UInt64.ofNat key.length + 8), .i64 1] = .Trap st' msg at hInv
          cases hOldEq : ns.storage key with
          | none =>
            rw [storageWrite_invoke_encode_absent ns key val hView hKey hVal hLen
              hKeyLim hValLim hOldEq] at hInv
            contradiction
          | some old =>
            have hOldLimOld : withinLimit ns.config.maxRegisterLen old.length = true := by
              simpa [hOldEq] using hOldLim
            rw [storageWrite_invoke_encode_present ns key val old hView hKey hVal hLen
              hKeyLim hValLim hOldEq hOldLimOld] at hInv
            contradiction
      · intro st' msg hInv
        simp [readRegisterFn, hReg0, memBytes, hReadBound] at hInv
    · intro st' msg hInv
      simp [inputFn, writeRegisterResult, checkedSetRegister?, hInput, hReg, u64Max] at hInv

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

def resolvesSpecSubset : Bool :=
  match resolveContracts?
      [ { «module» := "env", name := "current_account_id", params := [.i64], results := [] }
      , { «module» := "env", name := "storage_write",
          params := [.i64, .i64, .i64, .i64, .i64], results := [.i64] } ] with
  | some spec => spec.contracts.length == 2
  | none      => false

theorem resolve_spec_subset : resolvesSpecSubset = true := by native_decide

def rejectsBadSpecSignature : Bool :=
  match resolveContracts?
      [ { «module» := "env", name := "storage_write",
          params := [.i64, .i64], results := [.i64] } ] with
  | none   => true
  | some _ => false

theorem reject_bad_spec_signature : rejectsBadSpecSignature = true := by native_decide

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

def storageWriteViewTraps : Bool :=
  let ns : NearState := { context := { isView := true } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match storageWriteFn.invoke st [.i64 1, .i64 0, .i64 1, .i64 1, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem storage_write_view_traps : storageWriteViewTraps = true := by native_decide

def storageReadAllowedInView : Bool :=
  let ns : NearState :=
    { storage := fun k => if k = [1] then some [9] else none
      context := { isView := true } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1] }
  match storageReadFn.invoke st [.i64 1, .i64 0, .i64 4] with
  | .Return [.i64 1] st' => st'.host.registers 4 == some [9]
  | _                    => false

theorem storage_read_allowed_in_view : storageReadAllowedInView = true := by native_decide

def attachedDepositViewTraps : Bool :=
  let ns : NearState := { context := { isView := true, attachedDeposit := 7 } }
  match attachedDepositFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem attached_deposit_view_traps : attachedDepositViewTraps = true := by native_decide

def signerAccountViewTraps : Bool :=
  let ns : NearState := { context := { isView := true, signerAccountId := [1] } }
  match signerAccountIdFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem signer_account_view_traps : signerAccountViewTraps = true := by native_decide

def promiseResultsCountWorks : Bool :=
  let ns : NearState := { promiseResults := [.notReady, .successful [7], .failed] }
  match promiseResultsCountFn.invoke (initialWith ns) [] with
  | .Return [.i64 n] _ => n == 3
  | _                  => false

theorem promise_results_count_works : promiseResultsCountWorks = true := by native_decide

def promiseResultSuccessWritesRegister : Bool :=
  let ns : NearState := { promiseResults := [.notReady, .successful [7, 8], .failed] }
  match promiseResultFn.invoke (initialWith ns) [.i64 1, .i64 9] with
  | .Return [.i64 1] st => st.host.registers 9 == some [7, 8]
  | _                   => false

theorem promise_result_success_writes_register :
    promiseResultSuccessWritesRegister = true := by native_decide

def promiseResultFailedLeavesRegister : Bool :=
  let ns : NearState :=
    { promiseResults := [.failed]
      registers := fun i => if i = 9 then some [1] else none }
  match promiseResultFn.invoke (initialWith ns) [.i64 0, .i64 9] with
  | .Return [.i64 2] st => st.host.registers 9 == some [1]
  | _                   => false

theorem promise_result_failed_leaves_register :
    promiseResultFailedLeavesRegister = true := by native_decide

def promiseResultBadIndexTraps : Bool :=
  let ns : NearState := { promiseResults := [.successful [7]] }
  match promiseResultFn.invoke (initialWith ns) [.i64 1, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem promise_result_bad_index_traps : promiseResultBadIndexTraps = true := by native_decide

def promiseResultViewTraps : Bool :=
  let ns : NearState := { context := { isView := true }, promiseResults := [.successful [7]] }
  match promiseResultFn.invoke (initialWith ns) [.i64 0, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem promise_result_view_traps : promiseResultViewTraps = true := by native_decide

def promiseReturnRecordsPromise : Bool :=
  let ns : NearState := { promises := [.batch [1] [], .batch [2] []] }
  match promiseReturnFn.invoke (initialWith ns) [.i64 1] with
  | .Return [] st => st.host.returnedPromise == some 1
  | _             => false

theorem promise_return_records_promise : promiseReturnRecordsPromise = true := by native_decide

def promiseReturnBadIndexTraps : Bool :=
  let ns : NearState := { promises := [.batch [1] []] }
  match promiseReturnFn.invoke (initialWith ns) [.i64 1] with
  | .Trap _ _ => true
  | _         => false

theorem promise_return_bad_index_traps : promiseReturnBadIndexTraps = true := by native_decide

def promiseBatchCreateRecordsAccount : Bool :=
  let st0 := initialWith {}
  let st := { st0 with mem := st0.mem.writeBytes 0 [10, 11] }
  match promiseBatchCreateFn.invoke st [.i64 2, .i64 0] with
  | .Return [.i64 0] st' => st'.host.promises == [.batch [10, 11] []]
  | _                    => false

theorem promise_batch_create_records_account :
    promiseBatchCreateRecordsAccount = true := by native_decide

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
    promiseCreateRecordsFunctionCall = true := by native_decide

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
    promiseThenRecordsCallback = true := by native_decide

def promiseAndRecordsDependencies : Bool :=
  let ns : NearState := { promises := [.batch [1] [], .batch [2] []] }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 (le64 0 ++ le64 1) }
  match promiseAndFn.invoke st [.i64 0, .i64 2] with
  | .Return [.i64 2] st' =>
    st'.host.promises == [.batch [1] [], .batch [2] [], .and [0, 1]]
  | _ => false

theorem promise_and_records_dependencies :
    promiseAndRecordsDependencies = true := by native_decide

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
    promiseBatchFunctionCallAppendsAction = true := by native_decide

def promiseBatchTransferAppendsAction : Bool :=
  let ns : NearState := { promises := [.batch [1] []] }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 (leU128Bytes 9) }
  match promiseBatchActionTransferFn.invoke st [.i64 0, .i64 0] with
  | .Return [] st' => st'.host.promises == [.batch [1] [PromiseAction.transfer 9]]
  | _              => false

theorem promise_batch_transfer_appends_action :
    promiseBatchTransferAppendsAction = true := by native_decide

def promiseActionOnJointTraps : Bool :=
  let ns : NearState := { promises := [.and [0]] }
  match promiseBatchActionCreateAccountFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem promise_action_on_joint_traps : promiseActionOnJointTraps = true := by native_decide

def promiseBatchCreateViewTraps : Bool :=
  let ns : NearState := { context := { isView := true } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [10] }
  match promiseBatchCreateFn.invoke st [.i64 1, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem promise_batch_create_view_traps :
    promiseBatchCreateViewTraps = true := by native_decide

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
    promiseYieldCreateRecordsToken = true := by native_decide

def promiseYieldResumeRecordsPayload : Bool :=
  let ns : NearState := { promises := [.yielded [109] [7] 3 4 [1, 2]] }
  let st0 := initialWith ns
  let st1 := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  let st := { st1 with mem := st1.mem.writeBytes 8 [9] }
  match promiseYieldResumeFn.invoke st [.i64 2, .i64 0, .i64 1, .i64 8] with
  | .Return [.i64 1] st' => st'.host.yieldResumes == [([1, 2], [9])]
  | _                    => false

theorem promise_yield_resume_records_payload :
    promiseYieldResumeRecordsPayload = true := by native_decide

def promiseYieldResumeUnknownReturnsZero : Bool :=
  let ns : NearState := { promises := [.yielded [109] [7] 3 4 [1, 2]] }
  let st0 := initialWith ns
  let st1 := { st0 with mem := st0.mem.writeBytes 0 [3, 4] }
  let st := { st1 with mem := st1.mem.writeBytes 8 [9] }
  match promiseYieldResumeFn.invoke st [.i64 2, .i64 0, .i64 1, .i64 8] with
  | .Return [.i64 0] st' => st'.host.yieldResumes == []
  | _                    => false

theorem promise_yield_resume_unknown_returns_zero :
    promiseYieldResumeUnknownReturnsZero = true := by native_decide

def promiseYieldCreateViewTraps : Bool :=
  let ns : NearState := { context := { isView := true } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [109] }
  match promiseYieldCreateFn.invoke st [.i64 1, .i64 0, .i64 0, .i64 0, .i64 3, .i64 4, .i64 9] with
  | .Trap _ _ => true
  | _         => false

theorem promise_yield_create_view_traps :
    promiseYieldCreateViewTraps = true := by native_decide

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
    storageIterPrefixNextWorks = true := by native_decide

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
    storageIterRangeNextWorks = true := by native_decide

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
    storageIterDuplicateRegistersTrap = true := by native_decide

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
    storageWriteInvalidatesIterators = true := by native_decide

def inputRegisterLimitTraps : Bool :=
  let ns : NearState :=
    { context := { input := [1, 2, 3] }
      config := { maxRegisterLen := some 2 } }
  match inputFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem input_register_limit_traps : inputRegisterLimitTraps = true := by native_decide

def valueReturnLimitTraps : Bool :=
  let ns : NearState := { config := { maxReturnLen := some 2 } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2, 3] }
  match valueReturnFn.invoke st [.i64 3, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem value_return_limit_traps : valueReturnLimitTraps = true := by native_decide

def storageWriteValueLimitTraps : Bool :=
  let ns : NearState := { config := { maxStorageValueLen := some 0 } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match storageWriteFn.invoke st [.i64 1, .i64 0, .i64 1, .i64 1, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem storage_write_value_limit_traps :
    storageWriteValueLimitTraps = true := by native_decide

def logCountLimitTraps : Bool :=
  let ns : NearState :=
    { logs := [[]]
      config := { maxNumberLogs := some 1 } }
  match logUtf8Fn.invoke (initialWith ns) [.i64 0, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem log_count_limit_traps : logCountLimitTraps = true := by native_decide

def logLenLimitTraps : Bool :=
  let ns : NearState := { config := { maxLogLen := some 1 } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match logUtf8Fn.invoke st [.i64 2, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem log_len_limit_traps : logLenLimitTraps = true := by native_decide

def logUtf8StoresRawBytes : Bool :=
  let st0 := initialWith {}
  let st := { st0 with mem := st0.mem.writeBytes 0 [255] }
  match logUtf8Fn.invoke st [.i64 1, .i64 0] with
  | .Return [] st' => st'.host.logs == [[255]]
  | _              => false

theorem log_utf8_stores_raw_bytes : logUtf8StoresRawBytes = true := by native_decide

def currentAccountInvalidTraps : Bool :=
  let ns : NearState :=
    { context := { currentAccountId := [1] }
      config := { validAccountId := fun _ => false } }
  match currentAccountIdFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem current_account_invalid_traps : currentAccountInvalidTraps = true := by native_decide

def validatorStakeInvalidAccountTraps : Bool :=
  let ns : NearState := { config := { validAccountId := fun _ => false } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1] }
  match validatorStakeFn.invoke st [.i64 1, .i64 0, .i64 8] with
  | .Trap _ _ => true
  | _         => false

theorem validator_stake_invalid_account_traps :
    validatorStakeInvalidAccountTraps = true := by native_decide

def signerPkInvalidTraps : Bool :=
  let ns : NearState :=
    { context := { signerAccountPk := [1, 2] }
      config := { validPublicKey := fun _ => false } }
  match signerAccountPkFn.invoke (initialWith ns) [.i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem signer_pk_invalid_traps : signerPkInvalidTraps = true := by native_decide

def ed25519InvalidPublicKeyTraps : Bool :=
  let ns : NearState := { config := { validPublicKey := fun _ => false } }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1] }
  match ed25519VerifyFn.invoke st [.i64 0, .i64 0, .i64 0, .i64 0, .i64 1, .i64 0] with
  | .Trap _ _ => true
  | _         => false

theorem ed25519_invalid_public_key_traps :
    ed25519InvalidPublicKeyTraps = true := by native_decide

def altBn128HookWritesRegister : Bool :=
  let ns : NearState := { altBn128G1Multiexp := fun bs => bs ++ [9] }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match altBn128G1MultiexpFn.invoke st [.i64 2, .i64 0, .i64 5] with
  | .Return [] st' => st'.host.registers 5 == some [1, 2, 9]
  | _              => false

theorem alt_bn128_hook_writes_register :
    altBn128HookWritesRegister = true := by native_decide

def bls12381HookWritesRegister : Bool :=
  let ns : NearState := { bls12381G1Multiexp := fun bs => (0, bs ++ [9]) }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match bls12381G1MultiexpFn.invoke st [.i64 2, .i64 0, .i64 5] with
  | .Return [.i64 0] st' => st'.host.registers 5 == some [1, 2, 9]
  | _                    => false

theorem bls12381_hook_writes_register :
    bls12381HookWritesRegister = true := by native_decide

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
    bls12381InvalidLeavesRegister = true := by native_decide

def bls12381PairingStatusReturns : Bool :=
  let ns : NearState := { bls12381PairingCheck := fun _ => 1 }
  let st0 := initialWith ns
  let st := { st0 with mem := st0.mem.writeBytes 0 [1, 2] }
  match bls12381PairingCheckFn.invoke st [.i64 2, .i64 0] with
  | .Return [.i64 1] _ => true
  | _                  => false

theorem bls12381_pairing_status_returns :
    bls12381PairingStatusReturns = true := by native_decide

end KvSetter
end Near
end Wasm
