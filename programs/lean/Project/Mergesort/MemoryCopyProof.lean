import Project.Mergesort.FunctionSpecs

/-!
# Total Iris rule for generated u64 slice copies

The generated `copy_from_slice` implementation lowers its successful path to
one atomic `memory.copy`.  This file gives that instruction a length-polymorphic
ownership rule and then packages it for the exact generated function body.
-/

namespace Project.Mergesort.MemoryCopyProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic
open Wasm.SmallStep

def encodeWord (value : UInt64) : List UInt8 :=
  [u64Byte value 0, u64Byte value 1, u64Byte value 2, u64Byte value 3,
   u64Byte value 4, u64Byte value 5, u64Byte value 6, u64Byte value 7]

def encodeWords : List UInt64 → List UInt8
  | [] => []
  | x :: xs => encodeWord x ++ encodeWords xs

@[simp] theorem encodeWord_length (value : UInt64) :
    (encodeWord value).length = 8 := rfl

@[simp] theorem encodeWords_length (values : List UInt64) :
    (encodeWords values).length = 8 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [encodeWords, ih, Nat.mul_add]; omega

/-- Full ownership of consecutive bytes, indexed from one stable base. -/
def bytesAt [WasmHeapGS] (base : UInt32) (offset : Nat) :
    List UInt8 → IProp WasmHeapGF
  | [] => iprop% emp
  | byte :: bytes =>
      iprop% (base + UInt32.ofNat offset ↦w byte) ∗
        bytesAt base (offset + 1) bytes

theorem bytesAt_append [WasmHeapGS] (base : UInt32) (offset : Nat)
    (left right : List UInt8) :
    bytesAt base offset (left ++ right) ⊣⊢
      bytesAt base offset left ∗ bytesAt base (offset + left.length) right := by
  induction left generalizing offset with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero, bytesAt]
    exact BI.emp_sep.symm
  | cons byte bytes ih =>
    simp only [List.cons_append, List.length_cons, bytesAt]
    have hoffset : offset + (bytes.length + 1) = offset + 1 + bytes.length := by
      omega
    rw [hoffset]
    exact (BI.sep_congr_right (ih (offset + 1))).trans BI.sep_assoc.symm

theorem bytesAt_rebase [WasmHeapGS] (base : UInt32) (shift offset : Nat)
    (bytes : List UInt8) :
    bytesAt (base + UInt32.ofNat shift) offset bytes ⊣⊢
      bytesAt base (shift + offset) bytes := by
  induction bytes generalizing offset with
  | nil => exact .rfl
  | cons byte bytes ih =>
    simp only [bytesAt]
    have haddress :
        (base + UInt32.ofNat shift) + UInt32.ofNat offset =
          base + UInt32.ofNat (shift + offset) := by
      rw [UInt32.ofNat_add, UInt32.add_assoc]
    have hoffset : shift + (offset + 1) = shift + offset + 1 := by omega
    rw [haddress]
    have htail := ih (offset + 1)
    rw [hoffset] at htail
    exact BI.sep_congr_right htail

theorem pointsTo_u64_bytesAt [WasmHeapGS] (base : UInt32) (value : UInt64) :
    pointsTo_u64 base value ⊣⊢ bytesAt base 0 (encodeWord value) := by
  simp only [pointsTo_u64, encodeWord, bytesAt]
  rw [show UInt32.ofNat 0 = 0 by decide,
    show UInt32.ofNat 1 = 1 by decide,
    show UInt32.ofNat 2 = 2 by decide,
    show UInt32.ofNat 3 = 3 by decide,
    show UInt32.ofNat 4 = 4 by decide,
    show UInt32.ofNat 5 = 5 by decide,
    show UInt32.ofNat 6 = 6 by decide,
    show UInt32.ofNat 7 = 7 by decide]
  norm_num
  exact BI.sep_congr_right (BI.sep_congr_right (BI.sep_congr_right
    (BI.sep_congr_right (BI.sep_congr_right (BI.sep_congr_right
      (BI.sep_congr_right (BI.sep_emp (PROP := IProp WasmHeapGF)
        (P := pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (base + 7) (DFrac.own 1) (some (u64Byte value 7)))).symm))))))

theorem array64At_bytesAt [WasmHeapGS] (base : UInt32) (values : List UInt64) :
    array64At base values ⊣⊢ bytesAt base 0 (encodeWords values) := by
  induction values generalizing base with
  | nil => exact .rfl
  | cons value values ih =>
    simp only [array64At, encodeWords]
    have hlength : (encodeWord value).length = 8 := by rfl
    calc
      pointsTo_u64 base value ∗ array64At (base + 8) values ⊣⊢
          bytesAt base 0 (encodeWord value) ∗
            bytesAt (base + 8) 0 (encodeWords values) :=
        BI.sep_congr (pointsTo_u64_bytesAt base value) (ih (base + 8))
      _ ⊣⊢ bytesAt base 0 (encodeWord value) ∗
            bytesAt base 8 (encodeWords values) :=
        BI.sep_congr_right (bytesAt_rebase base 8 0 (encodeWords values))
      _ ⊣⊢ bytesAt base 0 (encodeWord value ++ encodeWords values) := by
        rw [← hlength]
        exact (bytesAt_append base 0 (encodeWord value) (encodeWords values)).symm

theorem Mem.copy_eq_writeBytes_readBytes (mem : Mem) (dst src len : Nat) :
    mem.copy dst src len = mem.writeBytes dst (mem.readBytes src len) := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.copy, Mem.writeBytes]
    have hlen : (({ pages := pages, bytes := bytes } : Mem).readBytes src len).length =
        len := by simp [Mem.readBytes]
    simp only [hlen]
    congr 1
    funext i
    by_cases h : dst ≤ i ∧ i < dst + len
    · simp only [if_pos h, dif_pos h]
      simp [Mem.readBytes]
    · simp only [if_neg h, dif_neg h]

private theorem readBytes_one_add (mem : Mem) (offset n : Nat) :
    mem.readBytes offset (1 + n) =
      mem.bytes offset :: mem.readBytes (offset + 1) n := by
  unfold Mem.readBytes
  rw [List.range_add]
  simp only [List.map_append, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append]
  simp [Nat.add_assoc]

/-- Byte facts in framed form, needed to inspect a whole owned interval. -/
private theorem stateInterp_byte_facts_frame [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) (some value) ==∗
      stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) (some value) ∗
      ⌜store.wasm.mem.read8 address = value ∧
        address.toNat < store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hlookup : ⌜get? σ address = some (some value)⌝ $$ [Hheap Hpointsto]
  · imod genHeap_valid $$ [$Hheap $Hpointsto] with %hlookup
    ipureintro
    exact hlookup
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [Hpointsto]
    · iexact Hpointsto
    · ipureintro
      exact ⟨Hfacts.1 address value hlookup,
        Hfacts.2.1 address value hlookup⟩

/-- An owned nonempty byte interval determines the corresponding physical
`readBytes` result and proves the complete interval is in bounds. -/
theorem stateInterp_bytesAt_facts [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (base : UInt32) (offset : Nat) (byte : UInt8) (bytes : List UInt8)
    (hroom : base.toNat + offset + (byte :: bytes).length ≤ UInt32.size) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      bytesAt base offset (byte :: bytes) ==∗
      stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      bytesAt base offset (byte :: bytes) ∗
      ⌜store.wasm.mem.readBytes (base.toNat + offset) (byte :: bytes).length =
          byte :: bytes ∧
        base.toNat + offset + (byte :: bytes).length ≤
          store.wasm.mem.pages * 65536⌝ := by
  induction bytes generalizing offset byte with
  | nil =>
    simp only [List.length_cons, List.length_nil] at hroom
    iintro ⟨Hstate, Hbytes⟩
    isimp only [bytesAt] at Hbytes
    icases Hbytes with ⟨Hbyte, Hemp⟩
    imod stateInterp_byte_facts_frame store steps observations threads
        (base + UInt32.ofNat offset) byte $$
        [$Hstate $Hbyte] with ⟨Hstate, Hbyte, %Hfacts⟩
    have hoff : offset < 4294967296 := by
      simpa only [UInt32.size] using (show offset < UInt32.size by omega)
    have haddr : (base + UInt32.ofNat offset).toNat =
        base.toNat + offset := by
      apply UInt32.add_ofNat_toNat_noWrap base offset hoff
      simpa only [UInt32.size] using (show base.toNat + offset < UInt32.size by omega)
    have hread : store.wasm.mem.readBytes (base.toNat + offset) 1 = [byte] := by
      rw [show 1 = 1 + 0 by omega, readBytes_one_add]
      simp only [Mem.read8] at Hfacts
      rw [← haddr, Hfacts.1]
      simp [Mem.readBytes]
    imodintro
    isplitl [Hstate]
    · iexact Hstate
    isplitl [Hbyte Hemp]
    · isimp only [bytesAt]
      isplitl [Hbyte]
      · iexact Hbyte
      · iexact Hemp
    · ipureintro
      refine ⟨hread, ?_⟩
      simp only [List.length_cons, List.length_nil]
      rw [← haddr]
      omega
  | cons next rest ih =>
    simp only [List.length_cons] at hroom
    iintro ⟨Hstate, Hbytes⟩
    isimp only [bytesAt] at Hbytes
    icases Hbytes with ⟨Hbyte, Htail⟩
    imod stateInterp_byte_facts_frame store steps observations threads
        (base + UInt32.ofNat offset) byte $$
        [$Hstate $Hbyte] with ⟨Hstate, Hbyte, %Hfacts⟩
    have htailRoom :
        base.toNat + (offset + 1) + (next :: rest).length ≤ UInt32.size := by
      simp only [List.length_cons]
      omega
    ihave Htail' : bytesAt base (offset + 1) (next :: rest) $$ [Htail]
    · isimp only [bytesAt]
      iexact Htail
    imod ih (offset + 1) next htailRoom $$
        [$Hstate $Htail'] with ⟨Hstate, Htail, %HtailFacts⟩
    simp only [List.length_cons] at HtailFacts
    have hoff : offset < 4294967296 := by
      simpa only [UInt32.size] using (show offset < UInt32.size by omega)
    have haddr : (base + UInt32.ofNat offset).toNat =
        base.toNat + offset := by
      apply UInt32.add_ofNat_toNat_noWrap base offset hoff
      simpa only [UInt32.size] using (show base.toNat + offset < UInt32.size by omega)
    have hread :
        store.wasm.mem.readBytes (base.toNat + offset)
            (byte :: next :: rest).length = byte :: next :: rest := by
      rw [show (byte :: next :: rest).length =
          1 + (next :: rest).length by simp only [List.length_cons]; omega,
        readBytes_one_add]
      have hhead : store.wasm.mem.bytes (base.toNat + offset) = byte := by
        simpa only [Mem.read8, haddr] using Hfacts.1
      rw [hhead]
      simp only [List.length_cons]
      have hstart : base.toNat + offset + 1 = base.toNat + (offset + 1) := by omega
      rw [hstart, HtailFacts.1]
    imodintro
    isplitl [Hstate]
    · iexact Hstate
    isplitl [Hbyte Htail]
    · isimp only [bytesAt]
      isimp only [bytesAt] at Htail
      isplitl [Hbyte]
      · iexact Hbyte
      · iexact Htail
    · ipureintro
      refine ⟨hread, ?_⟩
      simp only [List.length_cons]
      omega

private theorem Mem.writeBytes_singleton (mem : Mem) (address : UInt32)
    (value : UInt8) :
    mem.writeBytes address.toNat [value] = mem.write8 address value := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.writeBytes, Mem.write8, List.length_cons, List.length_nil]
    congr
    funext i
    by_cases h : i = address.toNat
    · subst i
      simp
    · simp [h]
      intro hlo hhi
      exfalso
      apply h
      omega

private theorem Mem.writeBytes_cons (mem : Mem) (base : UInt32)
    (offset : Nat) (value : UInt8) (values : List UInt8)
    (haddr : (base + UInt32.ofNat offset).toNat = base.toNat + offset) :
    mem.writeBytes (base.toNat + offset) (value :: values) =
      (mem.write8 (base + UInt32.ofNat offset) value).writeBytes
        (base.toNat + (offset + 1)) values := by
  rw [show value :: values = [value] ++ values by rfl,
    Mem.writeBytes_append]
  rw [show mem.writeBytes (base.toNat + offset) [value] =
      mem.write8 (base + UInt32.ofNat offset) value by
        rw [← haddr, Mem.writeBytes_singleton]]
  congr 1

/-- Store update shared by owned-range bulk-memory rules. -/
def writeBytesStore (store : MachineStore α) (offset : Nat)
    (bytes : List UInt8) : MachineStore α :=
  { store with wasm :=
      { store.wasm with mem := store.wasm.mem.writeBytes offset bytes } }

private def writeByteStore (store : MachineStore α) (address : UInt32)
    (byte : UInt8) : MachineStore α :=
  { store with wasm :=
      { store.wasm with mem := store.wasm.mem.write8 address byte } }

private theorem Mem.writeBytes_nil (mem : Mem) (offset : Nat) :
    mem.writeBytes offset [] = mem := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.writeBytes, List.length_nil, Nat.add_zero]
    congr
    funext i
    simp

/-- Atomic physical/ghost update for an arbitrary same-length byte interval. -/
theorem stateInterp_bytesAt_write [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (base : UInt32) (offset : Nat) (oldBytes newBytes : List UInt8)
    (hlength : oldBytes.length = newBytes.length)
    (hroom : base.toNat + offset + oldBytes.length ≤ UInt32.size) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      bytesAt base offset oldBytes ==∗
      stateInterp (GF := WasmHeapGF)
        (writeBytesStore store (base.toNat + offset) newBytes)
        steps observations threads ∗
      bytesAt base offset newBytes := by
  induction oldBytes generalizing store offset newBytes with
  | nil =>
    cases newBytes with
    | nil =>
      iintro ⟨Hstate, Hemp⟩
      have hstore : writeBytesStore store (base.toNat + offset) [] = store := by
        unfold writeBytesStore
        rw [Mem.writeBytes_nil]
      rw [hstore]
      imodintro
      isplitl [Hstate]
      · iexact Hstate
      · iexact Hemp
    | cons newByte newTail => simp at hlength
  | cons oldByte oldTail ih =>
    cases newBytes with
    | nil => simp at hlength
    | cons newByte newTail =>
      simp only [List.length_cons] at hlength hroom
      have htailLength : oldTail.length = newTail.length := by omega
      iintro ⟨Hstate, Hbytes⟩
      isimp only [bytesAt] at Hbytes
      icases Hbytes with ⟨Hold, Htail⟩
      imod stateInterp_byte_facts_frame store steps observations threads
          (base + UInt32.ofNat offset) oldByte $$
          [$Hstate $Hold] with ⟨Hstate, Hold, %Hfacts⟩
      imod stateInterp_store8 store steps observations threads
          (base + UInt32.ofNat offset) oldByte newByte Hfacts.2 $$
          [$Hstate $Hold] with ⟨Hstate, Hnew⟩
      have htailRoom :
          base.toNat + (offset + 1) + oldTail.length ≤ UInt32.size := by
        omega
      ihave Htail' : bytesAt base (offset + 1) oldTail $$ [Htail]
      · iexact Htail
      ihave Hstate' : stateInterp
          (writeByteStore store (base + UInt32.ofNat offset) newByte)
          steps observations threads $$ [Hstate]
      · isimp only [writeByteStore]
        iexact Hstate
      imod ih (store := writeByteStore store
          (base + UInt32.ofNat offset) newByte) (offset := offset + 1)
          (newBytes := newTail) htailLength htailRoom $$
          [$Hstate' $Htail'] with ⟨Hstate, Htail⟩
      have hoff : offset < 4294967296 := by
        simpa only [UInt32.size] using (show offset < UInt32.size by omega)
      have haddr : (base + UInt32.ofNat offset).toNat =
          base.toNat + offset := by
        apply UInt32.add_ofNat_toNat_noWrap base offset hoff
        simpa only [UInt32.size] using
          (show base.toNat + offset < UInt32.size by omega)
      have hmem := Mem.writeBytes_cons store.wasm.mem base offset
        newByte newTail haddr
      have hstore :
          writeBytesStore
              (writeByteStore store (base + UInt32.ofNat offset) newByte)
              (base.toNat + (offset + 1)) newTail =
            writeBytesStore store (base.toNat + offset) (newByte :: newTail) := by
        unfold writeByteStore writeBytesStore
        simp only
        rw [hmem]
      ihave HstateFinal : stateInterp
          (writeBytesStore store (base.toNat + offset) (newByte :: newTail))
          steps observations threads $$ [Hstate]
      · rw [← hstore]
        iexact Hstate
      imodintro
      isplitl [HstateFinal]
      · iexact HstateFinal
      · isimp only [bytesAt]
        isplitl [Hnew]
        · iexact Hnew
        · iexact Htail

private def copyStore (store : MachineStore α) (destination source : UInt32)
    (length : Nat) : MachineStore α :=
  { store with wasm :=
      { store.wasm with mem :=
          store.wasm.mem.copy destination.toNat source.toNat length } }

/-- The state update underlying `memory.copy`: source ownership is preserved,
and complete destination ownership is replaced by the source bytes. -/
theorem stateInterp_memoryCopy_bytes [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (destination source : UInt32) (byte : UInt8) (bytes oldBytes : List UInt8)
    (hlength : (byte :: bytes).length = oldBytes.length)
    (hsourceRoom : source.toNat + (byte :: bytes).length ≤ UInt32.size)
    (hdestinationRoom :
      destination.toNat + oldBytes.length ≤ UInt32.size) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      bytesAt source 0 (byte :: bytes) ∗ bytesAt destination 0 oldBytes ==∗
      stateInterp (GF := WasmHeapGF)
        (copyStore store destination source (byte :: bytes).length)
        steps observations threads ∗
      bytesAt source 0 (byte :: bytes) ∗
        bytesAt destination 0 (byte :: bytes) ∗
      ⌜source.toNat + (byte :: bytes).length ≤
          store.wasm.mem.pages * 65536 ∧
        destination.toNat + (byte :: bytes).length ≤
          store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hsource, Hdestination⟩
  imod stateInterp_bytesAt_facts store steps observations threads
      source 0 byte bytes (by simpa using hsourceRoom) $$
      [$Hstate $Hsource] with ⟨Hstate, Hsource, %HsourceFacts⟩
  simp only [Nat.add_zero] at HsourceFacts
  imod stateInterp_bytesAt_write store steps observations threads
      destination 0 oldBytes (byte :: bytes) hlength.symm
      (by simpa using hdestinationRoom) $$
      [$Hstate $Hdestination] with ⟨Hstate, Hdestination⟩
  have hstore :
      writeBytesStore store (destination.toNat + 0) (byte :: bytes) =
        copyStore store destination source (byte :: bytes).length := by
    unfold writeBytesStore copyStore
    simp only [Nat.add_zero]
    rw [Mem.copy_eq_writeBytes_readBytes, HsourceFacts.1]
  ihave Hstate' : stateInterp
      (copyStore store destination source (byte :: bytes).length)
      steps observations threads $$ [Hstate]
  · rw [← hstore]
    iexact Hstate
  imod stateInterp_bytesAt_facts
      (copyStore store destination source (byte :: bytes).length)
      steps observations threads destination 0 byte bytes
      (by simpa [hlength] using hdestinationRoom) $$
      [$Hstate' $Hdestination] with ⟨Hstate', Hdestination, %HdestinationFacts⟩
  imodintro
  isplitl [Hstate']
  · iexact Hstate'
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Hdestination]
  · iexact Hdestination
  · ipureintro
    refine ⟨HsourceFacts.2, ?_⟩
    simpa only [Nat.add_zero, copyStore, Mem.copy] using HdestinationFacts.2

/-- Total Iris lifting rule for an arbitrary successful `memory.copy`. -/
theorem twp_memoryCopy_bytes [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {destination source length : UInt32}
    {byte oldByte : UInt8} {bytes oldBytes : List UInt8}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hlengthValue : length.toNat = (byte :: bytes).length)
    (hlength : (byte :: bytes).length = (oldByte :: oldBytes).length)
    (hsourceRoom : source.toNat + (byte :: bytes).length ≤ UInt32.size)
    (hdestinationRoom :
      destination.toNat + (oldByte :: oldBytes).length ≤ UInt32.size) :
    let current : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 length :: .i32 source :: .i32 destination :: values⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    (bytesAt source 0 (byte :: bytes) ∗
      bytesAt destination 0 (oldByte :: oldBytes)) -∗
    (bytesAt source 0 (byte :: bytes) ∗
        bytesAt destination 0 (byte :: bytes) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro ⟨Hsource, Hdestination⟩ Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  imod stateInterp_bytesAt_facts store ns obs nt source 0 byte bytes
      (by simpa using hsourceRoom) $$
      [$Hσ $Hsource] with ⟨Hσ, Hsource, %HsourceFacts⟩
  imod stateInterp_bytesAt_facts store ns obs nt destination 0
      oldByte oldBytes (by simpa using hdestinationRoom) $$
      [$Hσ $Hdestination] with ⟨Hσ, Hdestination, %HdestinationFacts⟩
  have hsourceBound : source.toNat + length.toNat ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hlengthValue, Nat.add_zero] using HsourceFacts.2
  have hdestinationBound : destination.toNat + length.toNat ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hlengthValue, Nat.add_zero, hlength] using HdestinationFacts.2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
      ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
      copyStore store destination source length.toNat,
      [], ⟨rfl, .instruction .memoryCopy, rfl,
        Step.memoryCopy32 hdestinationBound hsourceBound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues,
            .i32 length :: .i32 source :: .i32 destination :: values⟩,
          .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction .memoryCopy)
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        copyStore store destination source length.toNat⟩ :=
    Step.memoryCopy32 hdestinationBound hsourceBound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_memoryCopy_bytes store ns obs nt destination source
      byte bytes (oldByte :: oldBytes) hlength hsourceRoom hdestinationRoom $$
      [$Hσ $Hsource $Hdestination] with
      ⟨Hσ, Hsource, Hdestination, %Hbounds⟩
  ihave Hσ' : stateInterp
      (copyStore store destination source length.toNat)
      ns obs nt $$ [Hσ]
  · isimp only [copyStore] at Hσ
    isimp only [copyStore, hlengthValue]
    iexact Hσ
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ']
  · iexact Hσ'
  · iapply Htwp
    iframe

/-- List-shaped wrapper around `twp_memoryCopy_bytes`. The nonempty premise
matches the generated caller, which skips `memory.copy` when the byte length
is zero. -/
theorem twp_memoryCopy_owned_bytes [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {destination source length : UInt32}
    {sourceBytes destinationBytes : List UInt8}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hnonempty : sourceBytes ≠ [])
    (hlengthValue : length.toNat = sourceBytes.length)
    (hlength : sourceBytes.length = destinationBytes.length)
    (hsourceRoom : source.toNat + sourceBytes.length ≤ UInt32.size)
    (hdestinationRoom :
      destination.toNat + destinationBytes.length ≤ UInt32.size) :
    let current : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 length :: .i32 source :: .i32 destination :: values⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    (bytesAt source 0 sourceBytes ∗ bytesAt destination 0 destinationBytes) -∗
    (bytesAt source 0 sourceBytes ∗ bytesAt destination 0 sourceBytes -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  cases sourceBytes with
  | nil => exact (hnonempty rfl).elim
  | cons byte bytes =>
    cases destinationBytes with
    | nil => simp at hlength
    | cons oldByte oldBytes =>
      exact twp_memoryCopy_bytes hlengthValue hlength hsourceRoom
        hdestinationRoom

/-- U64-array specialization used directly by generated slice cloning. -/
theorem twp_memoryCopy_u64 [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stackValues : List Value}
    {destination source length : UInt32}
    {sourceValues destinationValues : List UInt64}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hnonempty : sourceValues ≠ [])
    (hlengthValue : length.toNat = 8 * sourceValues.length)
    (hlength : sourceValues.length = destinationValues.length)
    (hsourceRoom : source.toNat + 8 * sourceValues.length ≤ UInt32.size)
    (hdestinationRoom :
      destination.toNat + 8 * destinationValues.length ≤ UInt32.size) :
    let current : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 length :: .i32 source :: .i32 destination :: stackValues⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, stackValues⟩,
        code, arity, remainder, controls, calls⟩
    (array64At source sourceValues ∗ array64At destination destinationValues) -∗
    (array64At source sourceValues ∗ array64At destination sourceValues -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro ⟨Hsource, Hdestination⟩ Htwp
  ihave HsourceBytes : bytesAt source 0 (encodeWords sourceValues) $$ [Hsource]
  · iapply (array64At_bytesAt source sourceValues).mp
    iexact Hsource
  ihave HdestinationBytes :
      bytesAt destination 0 (encodeWords destinationValues) $$ [Hdestination]
  · iapply (array64At_bytesAt destination destinationValues).mp
    iexact Hdestination
  have hbytesNonempty : encodeWords sourceValues ≠ [] := by
    cases sourceValues with
    | nil => exact (hnonempty rfl).elim
    | cons value values => simp [encodeWords, encodeWord]
  iapply twp_memoryCopy_owned_bytes
      (sourceBytes := encodeWords sourceValues)
      (destinationBytes := encodeWords destinationValues) hbytesNonempty
      (by simpa only [encodeWords_length] using hlengthValue)
      (by simp only [encodeWords_length, hlength])
      (by simpa only [encodeWords_length] using hsourceRoom)
      (by simpa only [encodeWords_length] using hdestinationRoom) $$
      [HsourceBytes HdestinationBytes]
  · iframe
  · iintro ⟨HsourceBytes, HdestinationBytes⟩
    iapply Htwp
    isplitl [HsourceBytes]
    · iapply (array64At_bytesAt source sourceValues).mpr
      iexact HsourceBytes
    · iapply (array64At_bytesAt destination sourceValues).mpr
      iexact HdestinationBytes

end Project.Mergesort.MemoryCopyProof
