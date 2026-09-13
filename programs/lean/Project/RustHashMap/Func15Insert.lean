import Project.RustHashMap.CollectBodyContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.BitPures
import Project.RustHashMap.ProbeStop
import CodeLib.RustStd.HashMap.CtrlWrite

/-!
# The insert arm of absolute `func 18`

`Project.RustHashMap.Func15Hash` covers the inlined SipHash of WAT lines
4143 to 4297.  This module covers the four straight-line pieces that the
probe loop of WAT lines 4339 to 4545 reaches after the walk:

* `twp_fix_insert`, the `fix_insert_index` block of WAT 4432 to 4456;
* `twp_insert_tail`, the write of a new pair at WAT 4457 to 4505;
* `twp_found_arm`, the replace of an old value at WAT 4508 to 4518;
* `twp_option_return`, the two result stores and the stack-pointer
  restore at WAT 4520 to 4529.

The word bridges above them turn the two's-complement constants of the
compiled body into subtractions, and the focus lemmas cut one control byte
or one bucket out of the table.

`twp_store32_addr` of `CodeLib.SepLogic.SmallStepTotalLiftingBytes` holds
for the normal-result adapter alone, so every store at offset 0 goes
through `twp_store32` and `wordMove` carries the word between `addr` and
`addr + 0`.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

section terminalGenericLoad8S

variable {hlc : outParam HasLC} {α : Type}
variable [WasmSmallStepGS hlc α]
variable {Terminal : Type}
variable [view : TerminalView α Terminal]
local instance (priority := high) activeTerminalLanguageLoad8S :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage
local instance (priority := high) activeTerminalIrisGSLoad8S :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      activeTerminalLanguageLoad8S (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }
variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

/-- The offset-zero form of `twp_load8S_gen`, which `codelib` states only
with an explicit offset. -/
theorem twp_load8S_addr_gen
    {params localValues values : List Value}
    {address : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some byte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some byte) -∗
      WP (.running ⟨⟨params, localValues,
        .i32 (Int32.ofInt (signExtend byte.toNat 8)).toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running ⟨⟨params, localValues, .i32 address :: values⟩,
      .load8S 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  simpa only [UInt32.add_zero] using
    (twp_load8S_gen (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (params := params)
      (localValues := localValues) (values := values) (code := code)
      (arity := arity) (remainder := remainder) (controls := controls)
      (calls := calls) byte (by simp))

end terminalGenericLoad8S

end Wasm.SmallStep

namespace Project.RustHashMap.Func15Insert

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Wasm.RustStd.HashMap.Table
open Project.RustHashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.BitPures
open Project.RustHashMap.ProbeStop
open scoped Wasm.SmallStep.Outcome

/-! ## Small word bridges -/

theorem addNegEight (x : UInt32) : x + 4294967288 = x - 8 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967288 : UInt32).toNat = 4294967288 from rfl,
    show (8 : UInt32).toNat = 8 from rfl] at *
  omega

theorem negEightAdd (x : UInt32) : 4294967288 + x = x - 8 := by
  rw [UInt32.add_comm]; exact addNegEight x

theorem addNegFour (x : UInt32) : x + 4294967292 = x - 4 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967292 : UInt32).toNat = 4294967292 from rfl,
    show (4 : UInt32).toNat = 4 from rfl] at *
  omega

theorem negFourAdd (x : UInt32) : 4294967292 + x = x - 4 := by
  rw [UInt32.add_comm]; exact addNegFour x

theorem add_shuffle (a b c : UInt32) : a + (b + c) = c + (b + a) := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add]
  omega

theorem shl3_ofNat (i : Nat) : UInt32.ofNat i <<< (3 : UInt32) = UInt32.ofNat (8 * i) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    show (3 : UInt32).toNat % 32 = 3 from rfl]
  simp only [Nat.shiftLeft_eq, Nat.pow_succ]
  omega

theorem ofNatSubOne (n : Nat) (h : 1 ≤ n) : UInt32.ofNat n - 1 = UInt32.ofNat (n - 1) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_sub, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    show (1 : UInt32).toNat = 1 from rfl]
  omega

theorem oneAddOfNat (n : Nat) : 1 + UInt32.ofNat n = UInt32.ofNat (n + 1) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    show (1 : UInt32).toNat = 1 from rfl]
  omega

theorem slotAddr_of_wasm (ctrl : UInt32) (i : Nat) :
    ctrl - (UInt32.ofNat i <<< (3 : UInt32)) - 8 = bucketAddr ctrl i := by
  rw [shl3_ofNat, sub_sub_addr, bucketAddr, Nat.mul_succ, UInt32.ofNat_add]
  rfl

/-- The mirror address that `set_ctrl` builds at WAT lines 4466 to 4474, in
the operand order the compiled code leaves on the stack. -/
theorem index2_addr_of_wasm {K V : Type} (t : Table K V) {m : Nat} (hm : m ≤ 32)
    (hb : t.buckets = 2 ^ m) (ctrl : UInt32) {i : Nat} (hi : i < 2 ^ 32) :
    (8 : UInt32) +
        (((4294967288 + UInt32.ofNat i) &&& UInt32.ofNat (t.buckets - 1)) + ctrl)
      = ctrl + UInt32.ofNat (index2 t.buckets i) := by
  have hmask : (4294967288 + UInt32.ofNat i) &&& UInt32.ofNat (t.buckets - 1)
      = UInt32.ofNat (wrapSub i 8 t.buckets) := by
    rw [negEightAdd, ← index2_of_wasm t hm hb hi, UInt32.ofNat_toNat]
  rw [hmask, index2, UInt32.ofNat_add, show (UInt32.ofNat 8 : UInt32) = 8 from rfl]
  exact add_shuffle 8 (UInt32.ofNat (wrapSub i 8 t.buckets)) ctrl

/-! ## One byte of an owned range -/

section Focus

variable {α : Type} [WasmHeapGS α]

theorem byteSlice_focus_getD (memId : Nat) (ptr : UInt32) (bytes : List UInt8)
    {i : Nat} (hi : i < bytes.length) :
    Slices.ByteSlice (α := α) memId ptr bytes ⊣⊢
      iprop(Slices.ByteSlice memId ptr (bytes.take i) ∗
        (⌜(ptr + UInt32.ofNat i).toNat + 1 < UInt32.size⌝ ∗
          (⟨memId, ptr + UInt32.ofNat i⟩ ↦w bytes.getD i EMPTY)) ∗
        Slices.ByteSlice memId (ptr + UInt32.ofNat (i + 1)) (bytes.drop (i + 1))) := by
  refine (ByteSlice_window memId ptr bytes i 1 hi).trans ?_
  refine BI.sep_congr .rfl (BI.sep_congr ?_ .rfl)
  have hbyte : (bytes.drop i).take 1 = [bytes.getD i EMPTY] := by
    rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.take_zero,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  rw [hbyte]
  exact Slices.ByteSlice_singleton memId _ _

/-- Lend one byte of an owned range and take a new byte back. -/
theorem byteFocusSet (memId : Nat) (ptr : UInt32) (bytes : List UInt8)
    {i : Nat} (hi : i < bytes.length) (cnew : UInt8) :
    Slices.ByteSlice (α := α) memId ptr bytes ⊢
      iprop((⟨memId, ptr + UInt32.ofNat i⟩ ↦w bytes.getD i EMPTY) ∗
        ((⟨memId, ptr + UInt32.ofNat i⟩ ↦w cnew) -∗
          Slices.ByteSlice memId ptr (bytes.set i cnew))) := by
  iintro Hbytes
  icases (byteSlice_focus_getD memId ptr bytes hi).mp $$ Hbytes with
    ⟨Hpre, ⟨%hb, Hbyte⟩, Hpost⟩
  isplitl [Hbyte]
  · iexact Hbyte
  · iintro Hnew
    iapply (ByteSlice_set memId ptr bytes hi cnew).mpr
    isplitl [Hpre]
    · iexact Hpre
    · isplitl [Hnew]
      · isplitl_pureexact hb
        iexact Hnew
      · iexact Hpost

end Focus

/-! ## The fields of `insertAt` -/

theorem insertAt_ctrl (t : Table UInt32 UInt32) (i : Nat) (tag : UInt8)
    (kv : UInt32 × UInt32) :
    (Table.insertAt t i tag kv).ctrl
      = (t.ctrl.set i tag).set (Table.index2 t.buckets i) tag := rfl

theorem insertAt_slots (t : Table UInt32 UInt32) (i : Nat) (tag : UInt8)
    (kv : UInt32 × UInt32) :
    (Table.insertAt t i tag kv).slots = t.slots.set i (some kv) := rfl

theorem insertAt_buckets (t : Table UInt32 UInt32) (i : Nat) (tag : UInt8)
    (kv : UInt32 × UInt32) :
    (Table.insertAt t i tag kv).buckets = t.buckets := rfl

theorem insertAt_items (t : Table UInt32 UInt32) (i : Nat) (tag : UInt8)
    (kv : UInt32 × UInt32) :
    (Table.insertAt t i tag kv).items = t.items + 1 := rfl

theorem insertAt_growthLeft (t : Table UInt32 UInt32) {i : Nat} (tag : UInt8)
    (kv : UInt32 × UInt32) (hempty : t.ctrlAt i = Table.EMPTY) :
    (Table.insertAt t i tag kv).growthLeft = t.growthLeft - 1 := by
  simp only [Table.insertAt, Table.setCtrl, hempty, Table.isEmpty, beq_self_eq_true,
    if_true]

theorem sub_eight_add_four (x : UInt32) : x - 8 + 4 = x - 4 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (8 : UInt32).toNat = 8 from rfl, show (4 : UInt32).toNat = 4 from rfl] at *
  omega

theorem slotValueAddr_of_wasm (ctrl : UInt32) (i : Nat) :
    ctrl - (UInt32.ofNat i <<< (3 : UInt32)) - 4 = bucketAddr ctrl i + 4 := by
  rw [← slotAddr_of_wasm ctrl i, sub_eight_add_four]

/-- The three address facts that the offset-free `twp_load32_addr` asks for. -/
theorem addr3 (addr : UInt32) (h : addr.toNat + 4 ≤ UInt32.size) :
    (addr + 1).toNat = addr.toNat + 1 ∧ (addr + 2).toNat = addr.toNat + 2 ∧
      (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using Slices.byteOffset_toNat addr 1 (by omega),
    by simpa using Slices.byteOffset_toNat addr 2 (by omega),
    by simpa using Slices.byteOffset_toNat addr 3 (by omega)⟩

/-- Move an owned word between two names of one address.  The offset-free
`twp_store32_addr` holds for the normal-result adapter alone, so a store at
offset 0 goes through `twp_store32` and this lemma carries the word between
`addr` and `addr + 0` on both sides of the rule. -/
theorem wordMove [WasmHeapGS Universal.State]
    (addr target word : UInt32) (haddr : target = addr) :
    pointsTo_u32 0 addr word ⊢ pointsTo_u32 0 target word := by
  subst haddr
  iintro Hword
  iexact Hword

/-- `insert_at_index` on an `EMPTY` byte, with every field computed. -/
theorem insertAt_fields (t : Table UInt32 UInt32) {i : Nat} (tag : UInt8)
    (kv : UInt32 × UInt32) (hempty : t.ctrlAt i = Table.EMPTY) :
    Table.insertAt t i tag kv =
      { buckets := t.buckets,
        ctrl := (t.ctrl.set i tag).set (Table.index2 t.buckets i) tag,
        slots := t.slots.set i (some kv),
        items := t.items + 1,
        growthLeft := t.growthLeft - 1 } := by
  simp only [Table.insertAt, Table.setCtrl, hempty, Table.isEmpty, beq_self_eq_true,
    if_true]

/-! ## The locals of the probe loop -/

/-- The locals of `func 18` while the probe loop runs. -/
@[reducible] def walkLocals (out mapBase key value l4 : UInt32)
    (w5 w6 w7 w8 w9 w10 : UInt64)
    (l11 l12 l13 l14 l15 l16 l17 : UInt32) : Locals :=
  { params := [.i32 out, .i32 mapBase, .i32 key, .i32 value],
    locals := [.i32 l4, .i64 w5, .i64 w6, .i64 w7, .i64 w8, .i64 w9, .i64 w10,
      .i32 l11, .i32 l12, .i32 l13, .i32 l14, .i32 l15, .i32 l16, .i32 l17],
    values := [] }

/-- The insert tail, WAT lines 4457 to 4505: the two control byte writes,
the two counter updates, and the key and value of the new bucket. -/
@[reducible] def insertTail (contCode : Program) : Program :=
  Instruction.localGet 13 :: .localGet 17 :: .add :: .localGet 8 :: .wrapI64 ::
    .const 127 :: .and :: .localTee 16 :: .store8 0 ::
  .localGet 13 :: .localGet 17 :: .const 4294967288 :: .add :: .localGet 11 ::
    .and :: .add :: .const 8 :: .add :: .localGet 16 :: .store8 0 ::
  .localGet 1 :: .localGet 1 :: .load32 8 :: .localGet 14 :: .const 1 :: .and ::
    .sub :: .store32 8 ::
  .localGet 1 :: .localGet 1 :: .load32 12 :: .const 1 :: .add :: .store32 12 ::
  .localGet 13 :: .localGet 17 :: .const 3 :: .shl :: .sub :: .localTee 1 ::
    .const 4294967288 :: .add :: .localGet 2 :: .store32 0 ::
  .localGet 1 :: .const 4294967292 :: .add :: .localGet 3 :: .store32 0 :: contCode

set_option maxHeartbeats 2000000 in
/-- The insert tail of WAT lines 4457 to 4505.  It writes the tag at bucket
`i` and at its mirror, drops `growth_left` by one, raises `items` by one, and
stores the pair.  That is `Table.insertAt`. -/
theorem twp_insert_tail [WasmSmallStepGS hlc Universal.State]
    {out mapBase key value l4 : UInt32}
    {w5 w6 w7 w8 w9 w10 : UInt64} {l12 l14 l15 l16 : UInt32}
    {ctrl : UInt32} {t : Table UInt32 UInt32} {hashf : UInt32 → UInt64}
    {m i : Nat} {tag : UInt8}
    {contCode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlayout : Table.Layout hashf t) (hm : m ≤ 32) (hbShape : t.buckets = 2 ^ m)
    (hi : i < t.buckets) (hempty : t.ctrlAt i = Table.EMPTY)
    (hw14 : l14 &&& 1 = 1) (hgrowth : 1 ≤ t.growthLeft)
    (hmapBound : mapBase.toNat + 32 < UInt32.size)
    (htagByte : (w8.toUInt32 &&& 127).toUInt8 = tag) :
    iprop(
      Table.TableBody 0 mapBase ctrl t ∗
      (Table.TableBody 0 mapBase ctrl (Table.insertAt t i tag (key, value)) -∗
        WP (.running ⟨walkLocals out (ctrl - (UInt32.ofNat i <<< (3 : UInt32)))
              key value l4 w5 w6 w7 w8 w9 w10
              (UInt32.ofNat (t.buckets - 1)) l12 ctrl l14 l15
              (w8.toUInt32 &&& 127) (UInt32.ofNat i),
            contCode, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨walkLocals out mapBase key value l4 w5 w6 w7 w8 w9 w10
            (UInt32.ofNat (t.buckets - 1)) l12 ctrl l14 l15 l16 (UInt32.ofNat i),
          insertTail contCode, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbody, Hcont⟩
  have hclen : t.ctrl.length = t.buckets + 8 := hlayout.ctrl_len
  have hslen : t.slots.length = t.buckets := hlayout.slots_len
  have hbpos : 0 < t.buckets := hlayout.pos
  have hiCtrl : i < t.ctrl.length := by omega
  have hi32 : i < 2 ^ 32 := by
    have hble : t.buckets ≤ 2 ^ 32 := by
      rw [hbShape]; exact Nat.pow_le_pow_right (by decide) hm
    omega
  have hi2lt : Table.index2 t.buckets i < t.ctrl.length := by
    have := Nat.mod_lt (i + 2 ^ 32 - 8) hbpos
    unfold Table.index2 Table.wrapSub
    omega
  have hi2set : Table.index2 t.buckets i < (t.ctrl.set i tag).length := by
    rw [List.length_set]; exact hi2lt
  isimp only [Table.TableBody, Table.tableHeader] at Hbody
  icases Hbody with ⟨%hctrlBound, ⟨H0, H4, H8, H12⟩, Hctrl, Hslots⟩
  have hh8 := FrameCells.offset_facts mapBase 8 8 rfl (by omega)
  have hh12 := FrameCells.offset_facts mapBase 12 12 rfl (by omega)
  have hbucketNat := Table.bucketAddr_toNat ctrl hi hctrlBound
  have hctrlLt := UInt32.toNat_lt ctrl
  have hslotRoom : (Table.bucketAddr ctrl i).toNat + 8 ≤ UInt32.size := by
    simp only [UInt32.size] at *
    omega
  have hslotStep : (Table.bucketAddr ctrl i + 4).toNat = (Table.bucketAddr ctrl i).toNat + 4 := by
    simpa using Slices.byteOffset_toNat (Table.bucketAddr ctrl i) 4 (by omega)
  have hkeyFacts := FrameCells.offset_facts (Table.bucketAddr ctrl i) 0 0 rfl (by omega)
  have hvalFacts :=
    FrameCells.offset_facts (Table.bucketAddr ctrl i + 4) 0 0 rfl (by omega)
  have hzeroK : Table.bucketAddr ctrl i + 0 = Table.bucketAddr ctrl i :=
    UInt32.add_zero _
  have hzeroV : Table.bucketAddr ctrl i + 4 + 0 = Table.bucketAddr ctrl i + 4 :=
    UInt32.add_zero _
  -- the tag byte at bucket `i`
  wasm_twp_pures [twp_localGet twp_localGet twp_add]
    rewriting [UInt32.add_comm (UInt32.ofNat i) ctrl]
  wasm_twp_pures [twp_localGet twp_wrapI64 twp_const twp_and]
  isimp only [wrapWasm]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  ihave ⟨Hbyte, Hclose⟩ := byteFocusSet 0 ctrl t.ctrl hiCtrl tag $$ Hctrl
  wasm_twp_rebind twp_store8_addr_gen (t.ctrl.getD i Table.EMPTY) with Hbyte
  isimp only [htagByte] at Hbyte
  ihave Hctrl := Hclose $$ Hbyte
  -- the tag byte at the mirror
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add twp_localGet twp_and
    twp_add twp_const twp_add twp_localGet]
    rewriting [index2_addr_of_wasm t hm hbShape ctrl hi32]
  ihave ⟨Hbyte, Hclose⟩ :=
    byteFocusSet 0 ctrl (t.ctrl.set i tag) hi2set tag $$ Hctrl
  wasm_twp_rebind twp_store8_addr_gen
    ((t.ctrl.set i tag).getD (Table.index2 t.buckets i) Table.EMPTY) with Hbyte
  isimp only [htagByte] at Hbyte
  ihave Hctrl := Hclose $$ Hbyte
  -- `growth_left` drops by one
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := mapBase) (offset := 8)
    (UInt32.ofNat t.growthLeft) hh8.1 hh8.2.1 hh8.2.2.1 hh8.2.2.2 with H8
  wasm_twp_pures [twp_localGet twp_const twp_and twp_sub]
  isimp only [hw14, ofNatSubOne t.growthLeft hgrowth]
  wasm_twp_rebind twp_store32 (address := mapBase) (offset := 8)
    (UInt32.ofNat t.growthLeft) hh8.1 hh8.2.1 hh8.2.2.1 hh8.2.2.2 with H8
  -- `items` grows by one
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := mapBase) (offset := 12)
    (UInt32.ofNat t.items) hh12.1 hh12.2.1 hh12.2.2.1 hh12.2.2.2 with H12
  wasm_twp_pures [twp_const twp_add]
  isimp only [oneAddOfNat t.items]
  wasm_twp_rebind twp_store32 (address := mapBase) (offset := 12)
    (UInt32.ofNat t.items) hh12.1 hh12.2.1 hh12.2.2.1 hh12.2.2.2 with H12
  -- the pair
  have hslotNone : t.slotAt i = none := by
    rcases hs : t.slotAt i with _ | ⟨k, v⟩
    · rfl
    · have := (hlayout.full_iff i hi).mpr (by rw [hs]; rfl)
      rw [hempty] at this
      exact absurd this (by decide)
  ihave ⟨Hpre, Hcell, Hpost⟩ :=
    (Table.slotsBefore_focus (i := i) 0 ctrl t.slots (by omega)).mp $$ Hslots
  isimp only [show t.slots[i]'(by omega) = t.slotAt i from by
    rw [Table.slotAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < t.slots.length)]
    rfl, hslotNone] at Hcell
  icases (Table.slotCell_none_as_words 0 (Table.bucketAddr ctrl i)).mp $$ Hcell with
    ⟨%oldKey, %oldValue, Hkey, Hvalue⟩
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl twp_sub]
  isimp only [shl32Wasm3]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  wasm_twp_pures [twp_const twp_add twp_localGet]
    rewriting [negEightAdd (ctrl - (UInt32.ofNat i <<< (3 : UInt32))),
      slotAddr_of_wasm ctrl i]
  ihave Hkey := wordMove (Table.bucketAddr ctrl i) (Table.bucketAddr ctrl i + 0)
    oldKey hzeroK $$ Hkey
  wasm_twp_rebind twp_store32 (address := Table.bucketAddr ctrl i) (offset := 0)
    oldKey hkeyFacts.1 hkeyFacts.2.1 hkeyFacts.2.2.1 hkeyFacts.2.2.2 with Hkey
  ihave Hkey := wordMove (Table.bucketAddr ctrl i + 0) (Table.bucketAddr ctrl i)
    key hzeroK.symm $$ Hkey
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet]
    rewriting [negFourAdd (ctrl - (UInt32.ofNat i <<< (3 : UInt32))),
      slotValueAddr_of_wasm ctrl i]
  ihave Hvalue := wordMove (Table.bucketAddr ctrl i + 4)
    (Table.bucketAddr ctrl i + 4 + 0) oldValue hzeroV $$ Hvalue
  wasm_twp_rebind twp_store32 (address := Table.bucketAddr ctrl i + 4) (offset := 0)
    oldValue hvalFacts.1 hvalFacts.2.1 hvalFacts.2.2.1 hvalFacts.2.2.2 with Hvalue
  ihave Hvalue := wordMove (Table.bucketAddr ctrl i + 4 + 0)
    (Table.bucketAddr ctrl i + 4) value hzeroV.symm $$ Hvalue
  -- rebuild the table
  ihave Hcell : Table.slotCell 0 (Table.bucketAddr ctrl i) (some (key, value)) $$
      [Hkey Hvalue]
  · isimp only [Table.slotCell]
    iframe Hkey Hvalue
  ihave Hslots :=
    (Table.slotsBefore_set (i := i) 0 ctrl t.slots (by omega) (some (key, value))).mpr $$
      [Hpre Hcell Hpost]
  · iframe Hpre Hcell Hpost
  ihave Hnew : Table.TableBody 0 mapBase ctrl (Table.insertAt t i tag (key, value)) $$
      [H0 H4 H8 H12 Hctrl Hslots]
  · rw [insertAt_fields t tag (key, value) hempty]
    isimp only [Table.TableBody, Table.tableHeader]
    isplitl_pureexact hctrlBound
    iframe H0 H4 H8 H12 Hctrl Hslots
  ihave Hgo := Hcont $$ Hnew
  iexact Hgo


/-! ## The return of func 18, WAT 4520 to 4530 -/

/-- An eight-byte out-parameter holds two words. -/
theorem outWords {α : Type} [WasmHeapGS α] (memId : Nat) (ptr : UInt32)
    (bytes : List UInt8) (hlength : bytes.length = 8)
    (hnowrap : ptr.toNat + 8 < UInt32.size) :
    Slices.ByteSlice (α := α) memId ptr bytes ⊢
      iprop(∃ w0 : UInt32, ∃ w1 : UInt32,
        pointsTo_u32 memId ptr w0 ∗ pointsTo_u32 memId (ptr + 4) w1) := by
  have hhead : (bytes.take 4).length = 4 := by rw [List.length_take]; omega
  have htail : (bytes.drop 4).length = 4 := by rw [List.length_drop]; omega
  have hstep : (ptr + 4).toNat = ptr.toNat + 4 := by
    simpa using Slices.byteOffset_toNat ptr 4 (by omega)
  have happ :=
    (Slices.ByteSlice_append (α := α) memId ptr (bytes.take 4) (bytes.drop 4)).mp
  rw [List.take_append_drop, hhead,
    show (UInt32.ofNat 4 : UInt32) = 4 from rfl] at happ
  iintro Hbytes
  icases happ $$ Hbytes with ⟨Hhead, Htail⟩
  iexists WordCodec.decodeU32 (bytes.take 4)
  iexists WordCodec.decodeU32 (bytes.drop 4)
  isplitl [Hhead]
  · iapply (Slices.ByteSlice_four_as_word memId ptr (bytes.take 4) hhead
      (by omega)).mp
    iexact Hhead
  · iapply (Slices.ByteSlice_four_as_word memId (ptr + 4) (bytes.drop 4) htail
      (by omega)).mp
    iexact Htail

/-- The two result stores and the stack-pointer restore, WAT 4520 to 4529.
The `return` at WAT 4530 is not here, because it pops the call frame. -/
@[reducible] def optionReturn (contCode : Program) : Program :=
  Instruction.localGet 0 :: .localGet 1 :: .store32 4 :: .localGet 0 ::
    .localGet 12 :: .store32 0 :: .localGet 4 :: .const 16 :: .add ::
    .globalSet 0 :: contCode

set_option maxHeartbeats 2000000 in
/-- WAT 4520 to 4529.  Both terminating arms of func 18 reach it.  Local 12
carries the discriminant and local 1 the payload word. -/
theorem twp_option_return [WasmSmallStepGS hlc Universal.State]
    {sp out payload key value : UInt32}
    {w5 w6 w7 w8 w9 w10 : UInt64}
    {l11 l12 l13 l14 l15 l16 l17 : UInt32}
    {outBefore : List UInt8} {o : Option UInt32}
    {contCode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlength : outBefore.length = 8) (hout : out.toNat + 8 < UInt32.size)
    (htag : l12 = if o.isSome then 1 else 0)
    (hpayload : ∀ v : UInt32, o = some v → payload = v) :
    iprop(
      Slices.ByteSlice 0 out outBefore ∗ StackPointer (sp - 16) ∗
      (Table.optionU32At 0 out o -∗ StackPointer sp -∗
        WP (.running ⟨walkLocals out payload key value (sp - 16) w5 w6 w7 w8 w9 w10
              l11 l12 l13 l14 l15 l16 l17,
            contCode, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
    WP (.running ⟨walkLocals out payload key value (sp - 16) w5 w6 w7 w8 w9 w10
          l11 l12 l13 l14 l15 l16 l17,
        optionReturn contCode, arity, remainder, controls, calls⟩ :
      Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hout, Hsp, Hcont⟩
  subst htag
  have hstep : (out + 4).toNat = out.toNat + 4 := by
    simpa using Slices.byteOffset_toNat out 4 (by omega)
  have hf4 := FrameCells.offset_facts out 4 4 rfl (by omega)
  have hf0 := FrameCells.offset_facts out 0 0 rfl (by omega)
  have hzero : out + 0 = out := UInt32.add_zero out
  icases outWords 0 out outBefore hlength hout $$ Hout with ⟨%w0, %w1, Hw0, Hw1⟩
  simp only [optionReturn]
  -- the payload word
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := out) (offset := 4) w1
    hf4.1 hf4.2.1 hf4.2.2.1 hf4.2.2.2 with Hw1
  -- the discriminant word
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hw0 := wordMove out (out + 0) w0 hzero $$ Hw0
  wasm_twp_rebind twp_store32 (address := out) (offset := 0) w0
    hf0.1 hf0.2.1 hf0.2.2.1 hf0.2.2.2 with Hw0
  ihave Hw0 :=
    wordMove (out + 0) out (if o.isSome then 1 else 0) hzero.symm $$ Hw0
  ihave Hopt : Table.optionU32At 0 out o $$ [Hw0 Hw1]
  · iapply Table.optionU32At_of_words 0 out o payload hpayload
    isplitl [Hw0]
    · iexact Hw0
    · iexact Hw1
  -- the stack pointer goes back
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (16 : UInt32) + (sp - 16) = sp by
    rw [UInt32.add_comm, UInt32.sub_add_cancel]]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer sp $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iapply Hcont $$ Hopt Hsp


/-! ## The found arm of func 18, WAT 4508 to 4518 -/

/-- The arm that replaces the value of a key that is already there. -/
@[reducible] def foundArm (contCode : Program) : Program :=
  Instruction.localGet 16 :: .const 4294967292 :: .add :: .localTee 13 ::
    .load32 0 :: .localSet 1 :: .localGet 13 :: .localGet 3 :: .store32 0 ::
    .const 1 :: .localSet 12 :: contCode

set_option maxHeartbeats 2000000 in
/-- WAT 4508 to 4518.  Local 16 holds `ctrl - 8 * j`, so four bytes below it
is the value cell of bucket `j`.  The arm reads the old value into local 1,
writes the new one, and sets the discriminant. -/
theorem twp_found_arm [WasmSmallStepGS hlc Universal.State]
    {out mapBase key value l4 : UInt32}
    {w5 w6 w7 w8 w9 w10 : UInt64} {l11 l12 l13 l14 l15 l17 : UInt32}
    {ctrl : UInt32} {t : Table UInt32 UInt32}
    {j : Nat} {oldValue : UInt32}
    {contCode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hj : j < t.slots.length) (hslot : t.slotAt j = some (key, oldValue))
    (hroom : (Table.bucketAddr ctrl j).toNat + 8 ≤ UInt32.size) :
    iprop(
      Table.slotsBefore 0 ctrl t.slots ∗
      (Table.slotsBefore 0 ctrl (t.slots.set j (some (key, value))) -∗
        WP (.running ⟨walkLocals out oldValue key value l4 w5 w6 w7 w8 w9 w10
              l11 1 (Table.bucketAddr ctrl j + 4) l14 l15
              (ctrl - (UInt32.ofNat j <<< (3 : UInt32))) l17,
            contCode, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
    WP (.running ⟨walkLocals out mapBase key value l4 w5 w6 w7 w8 w9 w10
          l11 l12 l13 l14 l15 (ctrl - (UInt32.ofNat j <<< (3 : UInt32))) l17,
        foundArm contCode, arity, remainder, controls, calls⟩ :
      Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hslots, Hcont⟩
  have hstep : (Table.bucketAddr ctrl j + 4).toNat
      = (Table.bucketAddr ctrl j).toNat + 4 := by
    simpa using Slices.byteOffset_toNat (Table.bucketAddr ctrl j) 4 (by omega)
  have hload := addr3 (Table.bucketAddr ctrl j + 4) (by omega)
  have hstore :=
    FrameCells.offset_facts (Table.bucketAddr ctrl j + 4) 0 0 rfl (by omega)
  have hzero : Table.bucketAddr ctrl j + 4 + 0 = Table.bucketAddr ctrl j + 4 :=
    UInt32.add_zero _
  ihave ⟨Hpre, Hcell, Hpost⟩ :=
    (Table.slotsBefore_focus (i := j) 0 ctrl t.slots hj).mp $$ Hslots
  isimp only [show t.slots[j]'hj = t.slotAt j from by
    rw [Table.slotAt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj]
    rfl, hslot, Table.slotCell] at Hcell
  icases Hcell with ⟨Hkey, Hvalue⟩
  simp only [foundArm]
  -- the value cell of bucket `j`
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [negFourAdd (ctrl - (UInt32.ofNat j <<< (3 : UInt32))),
      slotValueAddr_of_wasm ctrl j]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  wasm_twp_rebind twp_load32_addr (addr := Table.bucketAddr ctrl j + 4)
    oldValue hload.1 hload.2.1 hload.2.2 with Hvalue
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  -- the new value goes in
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hvalue := wordMove (Table.bucketAddr ctrl j + 4)
    (Table.bucketAddr ctrl j + 4 + 0) oldValue hzero $$ Hvalue
  wasm_twp_rebind twp_store32 (address := Table.bucketAddr ctrl j + 4)
    (offset := 0) oldValue hstore.1 hstore.2.1 hstore.2.2.1 hstore.2.2.2
    with Hvalue
  ihave Hvalue := wordMove (Table.bucketAddr ctrl j + 4 + 0)
    (Table.bucketAddr ctrl j + 4) value hzero.symm $$ Hvalue
  -- the discriminant
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  ihave Hcell : Table.slotCell 0 (Table.bucketAddr ctrl j) (some (key, value)) $$
      [Hkey Hvalue]
  · isimp only [Table.slotCell]
    iframe Hkey Hvalue
  ihave Hslots :=
    (Table.slotsBefore_set (i := j) 0 ctrl t.slots hj (some (key, value))).mpr $$
      [Hpre Hcell Hpost]
  · iframe Hpre Hcell Hpost
  iapply Hcont $$ Hslots

/-! ## The candidate repair, WAT 4432 to 4456 -/

/-- Move an owned double word between two names of one address. -/
theorem wordMove64
    [WasmSmallStepGS hlc Universal.State]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 0 address value ⊢ pointsTo_u64 0 address' value := by
  rw [haddress]

/-- One control byte of a table, with a wand that takes the same byte
back. -/
theorem ctrlByte_focus [WasmSmallStepGS hlc Universal.State]
    (ctrl : UInt32) (t : Table UInt32 UInt32) {i : Nat} (hi : i < t.ctrl.length) :
    Slices.ByteSlice (α := Universal.State) 0 ctrl t.ctrl ⊢
      iprop((⟨0, ctrl + UInt32.ofNat i⟩ ↦w Table.ctrlAt t i) ∗
        ((⟨0, ctrl + UInt32.ofNat i⟩ ↦w Table.ctrlAt t i) -∗
          Slices.ByteSlice 0 ctrl t.ctrl)) := by
  iintro Hctrl
  icases (Table.ByteSlice_ctrlAt 0 ctrl t hi).mp $$ Hctrl with
    ⟨Hpre, ⟨%hb, Hbyte⟩, Hpost⟩
  isplitl [Hbyte]
  · iexact Hbyte
  · iintro Hbyte
    iapply (Table.ByteSlice_ctrlAt 0 ctrl t hi).mpr
    isplitl [Hpre]
    · iexact Hpre
    · isplitl [Hbyte]
      · isplitl_pureexact hb
        iexact Hbyte
      · iexact Hpost

/-- The first group of the control bytes, as one owned `u64` at the address
that `local.get 13` puts on the stack, with a wand that takes it back. -/
theorem group0_focus [WasmSmallStepGS hlc Universal.State]
    (ctrl : UInt32) (t : Table UInt32 UInt32) (h8 : 8 ≤ t.ctrl.length) :
    Slices.ByteSlice (α := Universal.State) 0 ctrl t.ctrl ⊢
      iprop(⌜ctrl.toNat + 8 < UInt32.size⌝ ∗
        pointsTo_u64 0 (ctrl + 0) (Table.groupWord (Table.groupAt t 0)) ∗
        (pointsTo_u64 0 (ctrl + 0) (Table.groupWord (Table.groupAt t 0)) -∗
          Slices.ByteSlice 0 ctrl t.ctrl)) := by
  have haddr : ctrl + UInt32.ofNat 0 = ctrl + 0 := by
    rw [show UInt32.ofNat 0 = (0 : UInt32) from rfl]
  have hbound : ctrl + 0 = ctrl := UInt32.add_zero ctrl
  iintro Hctrl
  icases (Table.ByteSlice_groupAt 0 ctrl t (by omega : 0 + 8 ≤ t.ctrl.length)).mp
      $$ Hctrl with ⟨Hpre, ⟨%hgb, Hgroup⟩, Hpost⟩
  rw [haddr] at hgb
  rw [hbound] at hgb
  isplitl_pureexact hgb
  isplitl [Hgroup]
  · iapply wordMove64 haddr
    iexact Hgroup
  · iintro Hgroup
    iapply (Table.ByteSlice_groupAt 0 ctrl t (by omega : 0 + 8 ≤ t.ctrl.length)).mpr
    isplitl [Hpre]
    · iexact Hpre
    · isplitl [Hgroup]
      · isplitl_pureexact (by rw [haddr, hbound]; exact hgb)
        iapply wordMove64 haddr.symm
        iexact Hgroup
      · iexact Hpost

/-- The body of the `fix_insert_index` block, WAT lines 4434 to 4456. -/
@[reducible] def fixInsertBody : Program :=
  [.localGet 13, .localGet 17, .add, .load8S 0, .localTee 14, .const 0, .ltS,
    .br_if 0, .localGet 13, .localGet 13, .load64 0,
    .constI64 9259542123273814144, .andI64, .ctzI64, .wrapI64, .const 3,
    .shrU, .localTee 17, .add, .load8U 0, .localSet 14]

set_option maxHeartbeats 2000000 in
/-- `fix_insert_index`, WAT lines 4432 to 4456.  The compiled code keeps the
candidate when its control byte is special, and otherwise takes the lowest
special byte of the first group.  Both paths leave an `EMPTY` byte in
local 14, whose low bit is the one that `growth_left` subtracts. -/
theorem twp_fix_insert [WasmSmallStepGS hlc Universal.State]
    {out mapBase key value l4 : UInt32}
    {w5 w6 w7 w8 w9 w10 : UInt64} {l11 l12 l14 l15 l16 : UInt32}
    {ctrl : UInt32} {t : Table UInt32 UInt32} {hashf : UInt32 -> UInt64}
    {c : Nat}
    {contCode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hwf : Table.WF hashf t) (hcl : Table.Clean t) (hg : 1 ≤ t.growthLeft)
    (hc : c < t.buckets)
    (hspecial : Table.isSpecial (t.ctrlAt c) = true ∨ t.buckets ≤ 8) :
    iprop(
      Slices.ByteSlice 0 ctrl t.ctrl ∗
      (∀ w14 : UInt32, ⌜w14 &&& 1 = 1⌝ -∗
        Slices.ByteSlice 0 ctrl t.ctrl -∗
        WP (.running ⟨walkLocals out mapBase key value l4 w5 w6 w7 w8 w9 w10
              l11 l12 ctrl w14 l15 l16
              (UInt32.ofNat (Table.fixInsertIndex t c)),
            contCode, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨walkLocals out mapBase key value l4 w5 w6 w7 w8 w9 w10
            l11 l12 ctrl l14 l15 l16 (UInt32.ofNat c),
          Instruction.block 0 0 fixInsertBody :: contCode, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hctrl, Hexit⟩
  have hlayout : Table.Layout hashf t := hwf.toLayout
  have hclen : t.ctrl.length = t.buckets + 8 := hlayout.ctrl_len
  have hbpos : 0 < t.buckets := hlayout.pos
  have hcLt : c < t.ctrl.length := by omega
  iapply Wasm.SmallStep.twp_block
  simp only [fixInsertBody, walkLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_add]
    rewriting [UInt32.add_comm (UInt32.ofNat c) ctrl]
  ihave ⟨Hbyte, Hclose⟩ := ctrlByte_focus ctrl t hcLt $$ Hctrl
  wasm_twp_rebind twp_load8S_addr_gen (Table.ctrlAt t c) with Hbyte
  ihave Hctrl := Hclose $$ Hbyte
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const]
  by_cases hsp : Table.isSpecial (Table.ctrlAt t c) = true
  · -- the candidate byte is special, so it is `EMPTY` and the index stands
    have hempty : Table.ctrlAt t c = Table.EMPTY := hcl.1 c hc hsp
    have hlt := (ProbeStop.ltS_signByte (Table.ctrlAt t c)).mpr hsp
    iapply Wasm.SmallStep.twp_ltS (result := 1) (by rw [if_pos hlt])
    iapply Wasm.SmallStep.twp_brIf (targetCode := contCode)
      (targetControl := controls) (targetValues := ([] : List Value))
      (by decide : (1 : UInt32) ≠ 0) (by rfl)
    have hfix : Table.fixInsertIndex t c = c := by
      unfold Table.fixInsertIndex
      rw [if_neg (Table.isSpecial_iff.mp hsp)]
    rw [hfix]
    ihave Hgo := Hexit $$
      %((Int32.ofInt (signExtend (Table.ctrlAt t c).toNat 8)).toUInt32)
      %(by rw [hempty]; decide) Hctrl
    iexact Hgo
  · -- the candidate byte is full: take the lowest special byte of group zero
    have hfull : Table.isFull (Table.ctrlAt t c) = true := by
      by_contra hf
      exact hsp (Table.isSpecial_iff.mpr hf)
    have hb8 : t.buckets ≤ 8 := by
      rcases hspecial with hs | hs
      · exact absurd hs hsp
      · exact hs
    have hltFalse :
        ¬ ((Int32.ofInt (signExtend (Table.ctrlAt t c).toNat 8)).toUInt32.toInt32
          < (0 : UInt32).toInt32) := fun h => hsp ((ProbeStop.ltS_signByte _).mp h)
    iapply Wasm.SmallStep.twp_ltS (result := 0) (by rw [if_neg hltFalse])
    iapply Wasm.SmallStep.twp_brIfZero
    obtain ⟨j0, hls0, hj0b, hj0e⟩ :=
      ProbeStop.lowestSpecial_groupAt_zero hwf hcl hg hb8
    have hfix : Table.fixInsertIndex t c = j0 := by
      unfold Table.fixInsertIndex
      rw [if_pos hfull, hls0, Option.getD_some]
    have hmask : Table.swarMatchEmptyOrDeleted
          (Table.groupWord (Table.groupAt t 0)) &&& Table.REP80
        = Table.swarMatchEmptyOrDeleted (Table.groupWord (Table.groupAt t 0)) := by
      unfold Table.swarMatchEmptyOrDeleted
      rw [UInt64.and_assoc, UInt64.and_self]
    have hlow : Table.lowestSetByte
        (Table.swarMatchEmptyOrDeleted (Table.groupWord (Table.groupAt t 0)))
        = some j0 := by
      rw [Table.lowestSetByte_swarMatchEmptyOrDeleted (Table.groupAt_length t 0), hls0]
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨%hgb, Hgroup, Hclose⟩ := group0_focus ctrl t (by omega) $$ Hctrl
    have hgf := FrameCells.offset_facts64 ctrl 0 0 rfl (by
      have : (ctrl + 0) = ctrl := UInt32.add_zero ctrl
      omega)
    wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := ctrl) (offset := 0)
      (Table.groupWord (Table.groupAt t 0))
      hgf.1 hgf.2.1 hgf.2.2.1 hgf.2.2.2.1 hgf.2.2.2.2.1
      hgf.2.2.2.2.2.1 hgf.2.2.2.2.2.2.1 hgf.2.2.2.2.2.2.2 with Hgroup
    ihave Hctrl := Hclose $$ Hgroup
    wasm_twp_pures [twp_constI64 twp_andI64 twp_ctzI64 twp_wrapI64 twp_const
      twp_shrU]
    isimp only [ProbeStop.swarMatchEmptyOrDeleted_wasm, wrapWasm, shrU32Wasm3,
      ProbeStop.ctzByte_of_wasm hmask hlow]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_add] rewriting [UInt32.add_comm (UInt32.ofNat j0) ctrl]
    have hj0Lt : j0 < t.ctrl.length := by omega
    ihave ⟨Hbyte, Hclose⟩ := ctrlByte_focus ctrl t hj0Lt $$ Hctrl
    wasm_twp_rebind twp_load8U_addr_gen (Table.ctrlAt t j0) with Hbyte
    ihave Hctrl := Hclose $$ Hbyte
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_exitControl (by rfl)
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    rw [hfix]
    ihave Hgo := Hexit $$ %((Table.ctrlAt t j0).toUInt32)
      %(by rw [hj0e]; decide) Hctrl
    iexact Hgo

end Project.RustHashMap.Func15Insert
