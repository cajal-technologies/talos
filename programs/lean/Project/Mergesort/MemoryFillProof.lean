import Project.Mergesort.MemoryCopyProof

/-!
# Total owned-range rule for `memory.fill`

The Wasm heap is authoritative in `stateInterp`, while byte ownership is
carried by `bytesAt`.  A fill therefore updates an already-owned interval; it
does not allocate or mint heap fragments.  This is the reusable primitive
needed by the generated zeroed-allocation path.
-/

namespace Project.Mergesort.MemoryFillProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.MemoryCopyProof

/- Total owned-byte counterpart of `i32.load8_u`, used to inspect an
allocator header before deciding whether the returned payload needs filling. -/
theorem twp_load8U_owned
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some byte) -∗
    (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some byte) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hpt Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hstate
  ihave %Hfacts : ⌜store.wasm.mem.read8 (address + offset) = byte ∧
      (address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$
      [Hstate Hpt]
  · imod stateInterp_pointsTo_facts store ns obs nt
      (address + offset) byte $$ [$Hstate $Hpt] with %Hfacts
    ipureintro
    exact Hfacts
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    rw [← hnowrap]
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction (.load8U offset), rfl,
        by simpa [Hfacts.1] using
          (Step.load8U (α := α) (address := address) hbound)⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, _kind, _hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.load8U offset))
      ⟨.running ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hfacts.1] using
      (Step.load8U (α := α) (address := address) hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hstate]
  · iexact Hstate
  · iapply Htwp
    iexact Hpt

theorem Mem.writeBytes_replicate_eq_fill
    (mem : Mem) (offset length : Nat) (value : UInt8) :
    mem.writeBytes offset (List.replicate length value) =
      mem.fill offset length value := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.writeBytes, Mem.fill, List.length_replicate]
    congr
    funext i
    by_cases h : offset ≤ i ∧ i < offset + length
    · simp only [dif_pos h, if_pos h]
      rw [List.getElem_replicate]
    · simp only [dif_neg h, if_neg h]

private def fillStore (store : MachineStore α)
    (destination length : UInt32) (value : UInt8) : MachineStore α :=
  { store with wasm :=
      { store.wasm with mem :=
          store.wasm.mem.fill destination.toNat length.toNat value } }

/- Atomic physical/ghost update for a fill over a completely owned byte
interval.  The list length matches the Wasm operand, so the postcondition owns
exactly the same addresses with their new repeated byte value. -/
theorem stateInterp_memoryFill_bytes [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (destination length : UInt32) (value : UInt8) (oldBytes : List UInt8)
    (hlength : length.toNat = oldBytes.length)
    (hroom : destination.toNat + oldBytes.length ≤ UInt32.size) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      bytesAt destination 0 oldBytes ==∗
      stateInterp (GF := WasmHeapGF)
        (fillStore store destination length value)
        steps observations threads ∗
      bytesAt destination 0 (List.replicate oldBytes.length value) := by
  iintro ⟨Hstate, Hbytes⟩
  have hnewLength :
      oldBytes.length = (List.replicate oldBytes.length value).length := by
    simp
  imod stateInterp_bytesAt_write store steps observations threads
      destination 0 oldBytes (List.replicate oldBytes.length value)
      hnewLength (by simpa using hroom) $$
      [$Hstate $Hbytes] with ⟨Hstate, Hbytes⟩
  have hstore :
      writeBytesStore store (destination.toNat + 0)
          (List.replicate oldBytes.length value) =
        fillStore store destination length value := by
    unfold writeBytesStore fillStore
    simp only [Nat.add_zero]
    rw [Mem.writeBytes_replicate_eq_fill, ← hlength]
  ihave Hstate' : stateInterp (fillStore store destination length value)
      steps observations threads $$ [Hstate]
  · rw [← hstore]
    iexact Hstate
  imodintro
  isplitl [Hstate']
  · iexact Hstate'
  · iexact Hbytes

/- Total Iris lifting rule for an arbitrary successful 32-bit
`memory.fill`.  All affected bytes are required in the precondition. -/
theorem twp_memoryFill_owned_bytes [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {destination length fillValue : UInt32}
    {oldByte : UInt8} {oldBytes : List UInt8}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hlength : length.toNat = (oldByte :: oldBytes).length)
    (hroom :
      destination.toNat + (oldByte :: oldBytes).length ≤ UInt32.size) :
    let newBytes :=
      List.replicate (oldByte :: oldBytes).length fillValue.toUInt8
    let current : ThreadState α :=
      ⟨⟨params, localValues,
          .i32 length :: .i32 fillValue :: .i32 destination :: values⟩,
        .memoryFill :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    bytesAt destination 0 (oldByte :: oldBytes) -∗
    (bytesAt destination 0 newBytes -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hbytes Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hstate
  imod stateInterp_bytesAt_facts store ns obs nt destination 0
      oldByte oldBytes (by simpa using hroom) $$
      [$Hstate $Hbytes] with ⟨Hstate, Hbytes, %Hfacts⟩
  have hbound : destination.toNat + length.toNat ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hlength, Nat.add_zero] using Hfacts.2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
      ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
      fillStore store destination length fillValue.toUInt8,
      [], ⟨rfl, .instruction .memoryFill, rfl,
        by simpa only [fillStore, Wasm.SmallStep.setMemory_eq] using
          (Step.memoryFill32 (α := α) hbound)⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues,
            .i32 length :: .i32 fillValue :: .i32 destination :: values⟩,
          .memoryFill :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction .memoryFill)
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        fillStore store destination length fillValue.toUInt8⟩ := by
    simpa only [fillStore, Wasm.SmallStep.setMemory_eq] using
      (Step.memoryFill32 (α := α) hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_memoryFill_bytes store ns obs nt destination length
      fillValue.toUInt8 (oldByte :: oldBytes) hlength
      (by simpa using hroom) $$
      [$Hstate $Hbytes] with ⟨Hstate, Hbytes⟩
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hstate]
  · iexact Hstate
  · iapply Htwp
    iexact Hbytes

@[simp] theorem encodeWords_replicate_zero (count : Nat) :
    encodeWords (List.replicate count 0) = List.replicate (8 * count) 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ, encodeWords, encodeWord, ih,
      Nat.mul_add, Nat.mul_one]
    simp [u64Byte]

/- Word-shaped specialization used by `Vec<u64>::from_elem(0, count)`.
The allocation interval is still explicitly pre-owned; the instruction
changes only its contents to `count` little-endian zero words. -/
theorem twp_memoryFill_zero_array64 [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {destination length : UInt32}
    {oldWord : UInt64} {oldWords : List UInt64}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hlength : length.toNat = 8 * (oldWord :: oldWords).length)
    (hroom :
      destination.toNat + 8 * (oldWord :: oldWords).length ≤ UInt32.size) :
    array64At destination (oldWord :: oldWords) ∗
      (array64At destination
          (List.replicate (oldWord :: oldWords).length 0) -∗
        WP (.running
          ⟨⟨params, localValues, values⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 length :: .i32 0 :: .i32 destination :: values⟩,
        .memoryFill :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Harray, Htwp⟩
  ihave Hbytes :
      bytesAt destination 0 (encodeWords (oldWord :: oldWords)) $$ [Harray]
  · iapply (array64At_bytesAt destination (oldWord :: oldWords)).mp
    iexact Harray
  isimp only [encodeWords, encodeWord, List.cons_append, List.nil_append]
    at Hbytes
  have hbyteLength :
      (u64Byte oldWord 0 :: u64Byte oldWord 1 :: u64Byte oldWord 2 ::
          u64Byte oldWord 3 :: u64Byte oldWord 4 :: u64Byte oldWord 5 ::
          u64Byte oldWord 6 :: u64Byte oldWord 7 :: encodeWords oldWords).length =
        8 * (oldWord :: oldWords).length := by
    simp only [List.length_cons, encodeWords_length]
    omega
  iapply twp_memoryFill_owned_bytes
      (s := s) (E := E) (Φ := Φ)
      (params := params) (localValues := localValues) (values := values)
      (destination := destination) (length := length) (fillValue := 0)
      (oldByte := u64Byte oldWord 0)
      (oldBytes :=
        u64Byte oldWord 1 :: u64Byte oldWord 2 :: u64Byte oldWord 3 ::
          u64Byte oldWord 4 :: u64Byte oldWord 5 :: u64Byte oldWord 6 ::
          u64Byte oldWord 7 :: encodeWords oldWords)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls)
      (hlength := hlength.trans hbyteLength.symm)
      (hroom := by rw [hbyteLength]; exact hroom) $$ Hbytes
  iintro Hbytes
  ihave Hbytes' : bytesAt destination 0
      (List.replicate (8 * (oldWord :: oldWords).length) 0) $$ [Hbytes]
  · rw [← hbyteLength]
    change bytesAt destination 0
      (List.replicate
        (u64Byte oldWord 0 :: u64Byte oldWord 1 :: u64Byte oldWord 2 ::
          u64Byte oldWord 3 :: u64Byte oldWord 4 :: u64Byte oldWord 5 ::
          u64Byte oldWord 6 :: u64Byte oldWord 7 :: encodeWords oldWords).length
        (0 : UInt32).toUInt8) ⊢
      bytesAt destination 0
        (List.replicate
          (u64Byte oldWord 0 :: u64Byte oldWord 1 :: u64Byte oldWord 2 ::
            u64Byte oldWord 3 :: u64Byte oldWord 4 :: u64Byte oldWord 5 ::
            u64Byte oldWord 6 :: u64Byte oldWord 7 :: encodeWords oldWords).length
          0)
    exact .rfl
  ihave Harray : array64At destination
      (List.replicate (oldWord :: oldWords).length 0) $$ [Hbytes']
  · iapply (array64At_bytesAt destination
      (List.replicate (oldWord :: oldWords).length 0)).mpr
    rw [encodeWords_replicate_zero]
    iexact Hbytes'
  iapply Htwp $$ Harray

end Project.Mergesort.MemoryFillProof
