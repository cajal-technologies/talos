import Project.Mergesort.RangeProof

/-!
# Exact contracts for generated `split_at`

`func97` checks the split point, invokes `func96`, and copies the two returned
slice descriptors from its stack frame to the caller-provided result area.
-/

namespace Project.Mergesort.SplitAtProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.SliceProof
open Project.Mergesort.RangeProof

/-- Little-endian representation used when generated Wasm copies a
`(pointer, length)` descriptor with one 64-bit load/store. -/
def packU32 (low high : UInt32) : UInt64 :=
  low.toUInt64 ||| (high.toUInt64 <<< 32)

def sliceDescriptorAt [WasmHeapGS]
    (base data length : UInt32) : IProp WasmHeapGF :=
  iprop% pointsTo_u32 base data ∗ pointsTo_u32 (base + 4) length

private theorem packU32_lowByte (low high : UInt32) (n : Nat) (hn : n < 4) :
    u64Byte (packU32 low high) n = u32Byte low n := by
  interval_cases n <;> simp [packU32, u64Byte, u32Byte] <;> bv_decide

private theorem packU32_highByte (low high : UInt32) (n : Nat) (hn : n < 4) :
    u64Byte (packU32 low high) (n + 4) = u32Byte high n := by
  interval_cases n <;> simp [packU32, u64Byte, u32Byte] <;> bv_decide

/-- Two adjacent owned `u32` cells are exactly one owned packed `u64` cell. -/
theorem sliceDescriptorAt_eq_u64 [WasmHeapGS]
    (base low high : UInt32) :
    sliceDescriptorAt base low high ⊣⊢
      pointsTo_u64 base (packU32 low high) := by
  simp only [sliceDescriptorAt, pointsTo_u32, pointsTo_u64]
  rw [packU32_lowByte low high 0 (by decide),
    packU32_lowByte low high 1 (by decide),
    packU32_lowByte low high 2 (by decide),
    packU32_lowByte low high 3 (by decide),
    packU32_highByte low high 0 (by decide),
    packU32_highByte low high 1 (by decide),
    packU32_highByte low high 2 (by decide),
    packU32_highByte low high 3 (by decide)]
  rw [show base + 4 + 1 = base + 5 by bv_decide,
    show base + 4 + 2 = base + 6 by bv_decide,
    show base + 4 + 3 = base + 7 by bv_decide]
  constructor
  · iintro ⟨⟨Ha, Hb, Hc, Hd⟩, He, Hf, Hg, Hh⟩
    iframe
  · iintro ⟨Ha, Hb, Hc, Hd, He, Hf, Hg, Hh⟩
    iframe

private theorem sliceDescriptorAt_intro [WasmHeapGS]
    (base data length : UInt32) :
    pointsTo_u32 base data ∗ pointsTo_u32 (base + 4) length ⊢
      sliceDescriptorAt base data length := by
  rw [sliceDescriptorAt]

private theorem slot32Facts (base : UInt32) (offset total : Nat)
    (hroom : base.toNat + total ≤ UInt32.size)
    (hoffset : offset + 4 ≤ total) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 3) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega), by simpa using hstep 3 (by omega)⟩

private theorem slot64Facts (base : UInt32) (offset total : Nat)
    (hroom : base.toNat + total ≤ UInt32.size)
    (hoffset : offset + 8 ≤ total) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 ∧
    ((base + UInt32.ofNat offset) + 4).toNat =
      (base + UInt32.ofNat offset).toNat + 4 ∧
    ((base + UInt32.ofNat offset) + 5).toNat =
      (base + UInt32.ofNat offset).toNat + 5 ∧
    ((base + UInt32.ofNat offset) + 6).toNat =
      (base + UInt32.ofNat offset).toNat + 6 ∧
    ((base + UInt32.ofNat offset) + 7).toNat =
      (base + UInt32.ofNat offset).toNat + 7 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 7) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega), by simpa using hstep 3 (by omega),
    by simpa using hstep 4 (by omega), by simpa using hstep 5 (by omega),
    by simpa using hstep 6 (by omega), by simpa using hstep 7 (by omega)⟩

private def uncheckedLocals
    (resultPtr dataPtr length mid sourceLoc : UInt32) : Locals :=
  ⟨[.i32 resultPtr, .i32 dataPtr, .i32 length, .i32 mid, .i32 sourceLoc],
    [.i32 0, .i32 0], []⟩

private theorem pointsTo_u32_add_zero
    [WasmSmallStepGS hlc] (address value : UInt32) :
    pointsTo_u32 (address + UInt32.ofNat 0) value ⊢
      pointsTo_u32 address value := by
  rw [show UInt32.ofNat 0 = 0 by rfl, UInt32.add_zero]

private theorem pointsTo_u32_shift_three
    [WasmSmallStepGS hlc] (address data index : UInt32) :
    pointsTo_u32 address (data + (index <<< (3 % 32))) ⊢
      pointsTo_u32 address (data + (index <<< 3)) := by
  rw [show (3 % 32 : UInt32) = 3 by decide]

private theorem pointsTo_u32_at_eq
    [WasmSmallStepGS hlc] {address address' value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 address value ⊢ pointsTo_u32 address' value := by
  rw [haddress]

private theorem pointsTo_u64_at_eq
    [WasmSmallStepGS hlc] {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 address value ⊢ pointsTo_u64 address' value := by
  rw [haddress]

/-- Composable exact call rule for generated `func96` at absolute index `98`.
This is the call boundary used inside `func97`. -/
theorem twp_call_splitAtUnchecked
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr dataPtr length mid sourceLoc : UInt32)
    (old0 old1 old2 old3 : UInt32)
    (hroom : resultPtr.toNat + 16 ≤ UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      pointsTo_u32 resultPtr old0 ∗
      pointsTo_u32 (resultPtr + 4) old1 ∗
      pointsTo_u32 (resultPtr + 8) old2 ∗
      pointsTo_u32 (resultPtr + 12) old3 ∗
      (runtimeModuleOwn «module» -∗
        pointsTo_u32 resultPtr dataPtr -∗
        pointsTo_u32 (resultPtr + 4) mid -∗
        pointsTo_u32 (resultPtr + 8)
          (dataPtr + (mid <<< (3 % 32))) -∗
        pointsTo_u32 (resultPtr + 12) (length - mid) -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 sourceLoc :: .i32 mid :: .i32 length :: .i32 dataPtr ::
            .i32 resultPtr :: stack⟩,
        .call 98 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h00, h01, h02, h03⟩ := slot32Facts resultPtr 0 16 hroom (by decide)
  obtain ⟨h40, h41, h42, h43⟩ := slot32Facts resultPtr 4 16 hroom (by decide)
  obtain ⟨h80, h81, h82, h83⟩ := slot32Facts resultPtr 8 16 hroom (by decide)
  obtain ⟨h120, h121, h122, h123⟩ :=
    slot32Facts resultPtr 12 16 hroom (by decide)
  iintro ⟨Hruntime, H0, H1, H2, H3, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 98 splitAtUncheckedFunction
      (by decide) splitAtUnchecked_index $$ Hruntime
  iintro Hruntime
  simp [splitAtUncheckedFunction, func96Def, Function.toLocals,
    Function.numParams, ValueType.zero]
  simp only [func96]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shl
  iapply twp_add
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave H0' : pointsTo_u32 (resultPtr + 0) old0 $$ [H0]
  · rw [UInt32.add_zero]
    iexact H0
  iapply twp_store32 old0 h00 h01 h02 h03 $$ H0'
  iintro H0
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old1 h40 h41 h42 h43 $$ H1
  iintro H1
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old2 h80 h81 h82 h83 $$ H2
  iintro H2
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old3 h120 h121 h122 h123 $$ H3
  iintro H3
  iapply Wasm.SmallStep.twp_returnFromCallExplicit
  simp only [List.take_zero, List.nil_append,
    List.drop_eq_nil_of_le (by decide : 5 ≤
      [.i32 resultPtr, .i32 dataPtr, .i32 length, .i32 mid,
        .i32 sourceLoc].length)]
  ihave H2' : pointsTo_u32 (resultPtr + 8)
      (dataPtr + (mid <<< (3 % 32))) $$ [H2]
  · rw [UInt32.add_comm dataPtr]
    iexact H2
  ihave H0' : pointsTo_u32 resultPtr dataPtr $$ [H0]
  · iapply pointsTo_u32_add_zero
    iexact H0
  ihave H2'' : pointsTo_u32 (resultPtr + 8)
      (dataPtr + (mid <<< 3)) $$ [H2']
  · iapply pointsTo_u32_shift_three
    iexact H2'
  iapply Hdone $$ Hruntime H0' H1 H2'' H3

private def splitAtParams
    (resultPtr dataPtr length mid sourceLoc : UInt32) : List Value :=
  [.i32 resultPtr, .i32 dataPtr, .i32 length, .i32 mid, .i32 sourceLoc]

private def splitAtLocals (frame : UInt32) : List Value := [.i32 frame]

/-- Exact successful-path body contract for generated `func97` (`split_at`).
All four words in each returned pair remain individually owned, while the
proof uses packed `u64` views only for the generated descriptor copies. -/
theorem splitAt_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr dataPtr length mid sourceLoc stackTop : UInt32)
    (oldFrame0 oldFrame4 oldFrame8 oldFrame12
      oldFrame16 oldFrame20 oldFrame24 oldFrame28
      oldResult0 oldResult4 oldResult8 oldResult12 : UInt32)
    (hmid : mid ≤ length)
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 32) + 0) oldFrame0 ∗
      pointsTo_u32 ((stackTop - 32) + 4) oldFrame4 ∗
      pointsTo_u32 ((stackTop - 32) + 8) oldFrame8 ∗
      pointsTo_u32 ((stackTop - 32) + 12) oldFrame12 ∗
      pointsTo_u32 ((stackTop - 32) + 16) oldFrame16 ∗
      pointsTo_u32 ((stackTop - 32) + 20) oldFrame20 ∗
      pointsTo_u32 ((stackTop - 32) + 24) oldFrame24 ∗
      pointsTo_u32 ((stackTop - 32) + 28) oldFrame28 ∗
      pointsTo_u32 resultPtr oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      pointsTo_u32 (resultPtr + 8) oldResult8 ∗
      pointsTo_u32 (resultPtr + 12) oldResult12 ∗
      ((runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 stackTop) ∗
        sliceDescriptorAt ((stackTop - 32) + 0) dataPtr mid ∗
        sliceDescriptorAt ((stackTop - 32) + 8)
          (dataPtr + (mid <<< 3)) (length - mid) ∗
        sliceDescriptorAt ((stackTop - 32) + 16) dataPtr mid ∗
        sliceDescriptorAt ((stackTop - 32) + 24)
          (dataPtr + (mid <<< 3)) (length - mid) ∗
        sliceDescriptorAt resultPtr dataPtr mid ∗
        sliceDescriptorAt (resultPtr + 8)
          (dataPtr + (mid <<< 3)) (length - mid)) -∗
        ∀ controls : List ControlFrame,
          WP (.running
            ⟨⟨splitAtParams resultPtr dataPtr length mid sourceLoc,
                splitAtLocals (stackTop - 32), []⟩,
              [.ret], 0, [], controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨splitAtParams resultPtr dataPtr length mid sourceLoc,
          splitAtLocals 0, []⟩,
        func97, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 32
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ :=
    slot64Facts frame 0 32 hframeRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83, hf84, hf85, hf86, hf87⟩ :=
    slot64Facts frame 8 32 hframeRoom (by decide)
  obtain ⟨hf160, hf161, hf162, hf163, hf164, hf165, hf166, hf167⟩ :=
    slot64Facts frame 16 32 hframeRoom (by decide)
  obtain ⟨hf240, hf241, hf242, hf243, hf244, hf245, hf246, hf247⟩ :=
    slot64Facts frame 24 32 hframeRoom (by decide)
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ :=
    slot64Facts resultPtr 0 16 hresultRoom (by decide)
  obtain ⟨hr80, hr81, hr82, hr83, hr84, hr85, hr86, hr87⟩ :=
    slot64Facts resultPtr 8 16 hresultRoom (by decide)
  have hinnerRoom : (frame + 16).toNat + 16 ≤ UInt32.size := by
    change (frame + UInt32.ofNat 16).toNat + 16 ≤ UInt32.size
    rw [hf160]
    omega
  iintro ⟨Hruntime, Hglobal, Hf0, Hf4, Hf8, Hf12, Hf16, Hf20,
    Hf24, Hf28, Hr0, Hr4, Hr8, Hr12, Hcont⟩
  simp only [func97]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [splitAtParams, splitAtLocals]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_leU (result := 1) (by simp [hmid])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) rfl
  simp only [List.drop_zero, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  have Hunchecked := twp_call_splitAtUnchecked (α := α)
    (frame + 16) dataPtr length mid 1049524
    oldFrame16 oldFrame20 oldFrame24 oldFrame28 hinnerRoom
    (s := s) (E := E) (Φ := Φ)
    (params := splitAtParams resultPtr dataPtr length mid sourceLoc)
    (localValues := splitAtLocals frame) (stack := [])
    (code :=
      [.localGet 5, .localGet 5, .load64 24, .store64 8,
        .localGet 5, .localGet 5, .load64 16, .store64 0,
        .localGet 0, .localGet 5, .load64 8, .store64 8,
        .localGet 0, .localGet 5, .load64 0, .store64 0,
        .localGet 5, .const 32, .add, .globalSet 0, .ret])
    (arity := 0) (remainder := []) (controls := []) (calls := calls)
  simp only [splitAtParams, splitAtLocals, frame] at Hunchecked
  simp only [List.set, List.length_cons, List.length_nil, Nat.reduceSub,
    Nat.reduceAdd]
  rw [UInt32.add_comm 16 (stackTop - 32)]
  iapply Hunchecked
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hf16]
  · rw [show frame + 16 = (stackTop - 32) + 16 by rfl]
    iexact Hf16
  isplitl [Hf20]
  · rw [show (frame + 16) + 4 = (stackTop - 32) + 20 by bv_decide]
    iexact Hf20
  isplitl [Hf24]
  · rw [show (frame + 16) + 8 = (stackTop - 32) + 24 by bv_decide]
    iexact Hf24
  isplitl [Hf28]
  · rw [show (frame + 16) + 12 = (stackTop - 32) + 28 by bv_decide]
    iexact Hf28
  iintro Hruntime Hf16 Hf20 Hf24 Hf28
  ihave Hf24' : pointsTo_u32 (frame + 24)
      (dataPtr + (mid <<< 3)) $$ [Hf24]
  · iapply pointsTo_u32_at_eq
      (show (stackTop - 32) + 16 + 8 = frame + 24 by
        simp only [frame]
        bv_decide)
    iapply pointsTo_u32_shift_three
    iexact Hf24
  ihave Hf28' : pointsTo_u32 ((frame + 24) + 4) (length - mid) $$ [Hf28]
  · iapply pointsTo_u32_at_eq
      (show (stackTop - 32) + 16 + 12 = (frame + 24) + 4 by
        simp only [frame]
        bv_decide)
    iexact Hf28
  ihave Hf24Word : pointsTo_u64 (frame + 24)
      (packU32 (dataPtr + (mid <<< 3)) (length - mid)) $$ [Hf24' Hf28']
  · iapply (sliceDescriptorAt_eq_u64 (frame + 24)
      (dataPtr + (mid <<< 3)) (length - mid)).mp
    iapply sliceDescriptorAt_intro
    iframe
  ihave Hf8' : pointsTo_u32 (frame + 8) oldFrame8 $$ [Hf8]
  · iapply pointsTo_u32_at_eq
      (show (stackTop - 32) + 8 = frame + 8 by rfl)
    iexact Hf8
  ihave Hf12' : pointsTo_u32 ((frame + 8) + 4) oldFrame12 $$ [Hf12]
  · iapply pointsTo_u32_at_eq
      (show (stackTop - 32) + 12 = (frame + 8) + 4 by
        simp only [frame]
        bv_decide)
    iexact Hf12
  ihave Hf8Word : pointsTo_u64 (frame + 8)
      (packU32 oldFrame8 oldFrame12) $$ [Hf8' Hf12']
  · iapply (sliceDescriptorAt_eq_u64 (frame + 8)
      oldFrame8 oldFrame12).mp
    iapply sliceDescriptorAt_intro
    iframe
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 (dataPtr + (mid <<< 3)) (length - mid))
    hf240 hf241 hf242 hf243 hf244 hf245 hf246 hf247 $$ Hf24Word
  iintro Hf24Word
  iapply twp_store64 (packU32 oldFrame8 oldFrame12)
    hf80 hf81 hf82 hf83 hf84 hf85 hf86 hf87 $$ Hf8Word
  iintro Hf8Word
  ihave Hf16Word : pointsTo_u64 (frame + 16) (packU32 dataPtr mid) $$
      [Hf16 Hf20]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 16) dataPtr mid).mp
    iapply sliceDescriptorAt_intro
    iframe
  ihave Hf0' : pointsTo_u32 (frame + 0) oldFrame0 $$ [Hf0]
  · iapply pointsTo_u32_at_eq
      (show (stackTop - 32) + 0 = frame + 0 by rfl)
    iexact Hf0
  ihave Hf4' : pointsTo_u32 ((frame + 0) + 4) oldFrame4 $$ [Hf4]
  · iapply pointsTo_u32_at_eq
      (show (stackTop - 32) + 4 = (frame + 0) + 4 by
        simp only [frame]
        bv_decide)
    iexact Hf4
  ihave Hf0Word : pointsTo_u64 (frame + 0)
      (packU32 oldFrame0 oldFrame4) $$ [Hf0' Hf4']
  · iapply (sliceDescriptorAt_eq_u64 (frame + 0)
      oldFrame0 oldFrame4).mp
    iapply sliceDescriptorAt_intro
    iframe
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 dataPtr mid)
    hf160 hf161 hf162 hf163 hf164 hf165 hf166 hf167 $$ Hf16Word
  iintro Hf16Word
  iapply twp_store64 (packU32 oldFrame0 oldFrame4)
    hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 $$ Hf0Word
  iintro Hf0Word
  ihave Hr12' : pointsTo_u32 ((resultPtr + 8) + 4) oldResult12 $$ [Hr12]
  · iapply pointsTo_u32_at_eq
      (show resultPtr + 12 = (resultPtr + 8) + 4 by bv_decide)
    iexact Hr12
  ihave Hr8Word : pointsTo_u64 (resultPtr + 8)
      (packU32 oldResult8 oldResult12) $$ [Hr8 Hr12']
  · iapply (sliceDescriptorAt_eq_u64 (resultPtr + 8)
      oldResult8 oldResult12).mp
    iapply sliceDescriptorAt_intro
    iframe
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 (dataPtr + (mid <<< 3)) (length - mid))
    hf80 hf81 hf82 hf83 hf84 hf85 hf86 hf87 $$ Hf8Word
  iintro Hf8Word
  iapply twp_store64 (packU32 oldResult8 oldResult12)
    hr80 hr81 hr82 hr83 hr84 hr85 hr86 hr87 $$ Hr8Word
  iintro Hr8Word
  ihave Hr0' : pointsTo_u32 (resultPtr + 0) oldResult0 $$ [Hr0]
  · iapply pointsTo_u32_at_eq
      (show resultPtr = resultPtr + 0 by bv_decide)
    iexact Hr0
  ihave Hr4' : pointsTo_u32 ((resultPtr + 0) + 4) oldResult4 $$ [Hr4]
  · iapply pointsTo_u32_at_eq
      (show resultPtr + 4 = (resultPtr + 0) + 4 by bv_decide)
    iexact Hr4
  ihave Hr0Word : pointsTo_u64 (resultPtr + 0)
      (packU32 oldResult0 oldResult4) $$ [Hr0' Hr4']
  · iapply (sliceDescriptorAt_eq_u64 (resultPtr + 0)
      oldResult0 oldResult4).mp
    iapply sliceDescriptorAt_intro
    iframe
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 (packU32 dataPtr mid)
    hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 $$ Hf0Word
  iintro Hf0Word
  iapply twp_store64 (packU32 oldResult0 oldResult4)
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 $$ Hr0Word
  iintro Hr0Word
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  ihave HglobalTop : globalPointsTo 0 (.i32 stackTop) $$ [Hglobal]
  · rw [show (32 : UInt32) + (stackTop - 32) = stackTop by bv_decide]
    iexact Hglobal
  ihave Hf0Desc : sliceDescriptorAt (frame + 0) dataPtr mid $$ [Hf0Word]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 0) dataPtr mid).mpr
    iexact Hf0Word
  ihave Hf8Desc : sliceDescriptorAt (frame + 8)
      (dataPtr + (mid <<< 3)) (length - mid) $$ [Hf8Word]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 8)
      (dataPtr + (mid <<< 3)) (length - mid)).mpr
    iexact Hf8Word
  ihave Hf16Desc : sliceDescriptorAt (frame + 16) dataPtr mid $$ [Hf16Word]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 16) dataPtr mid).mpr
    iexact Hf16Word
  ihave Hf24Desc : sliceDescriptorAt (frame + 24)
      (dataPtr + (mid <<< 3)) (length - mid) $$ [Hf24Word]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 24)
      (dataPtr + (mid <<< 3)) (length - mid)).mpr
    iexact Hf24Word
  ihave Hr0Desc : sliceDescriptorAt resultPtr dataPtr mid $$ [Hr0Word]
  · iapply (sliceDescriptorAt_eq_u64 resultPtr dataPtr mid).mpr
    iapply pointsTo_u64_at_eq
      (show resultPtr + 0 = resultPtr by bv_decide)
    iexact Hr0Word
  ihave Hr8Desc : sliceDescriptorAt (resultPtr + 8)
      (dataPtr + (mid <<< 3)) (length - mid) $$ [Hr8Word]
  · iapply (sliceDescriptorAt_eq_u64 (resultPtr + 8)
      (dataPtr + (mid <<< 3)) (length - mid)).mpr
    iexact Hr8Word
  ispecialize Hcont $$ [Hruntime HglobalTop Hf0Desc Hf8Desc Hf16Desc
    Hf24Desc Hr0Desc Hr8Desc]
  · iframe
  ispecialize Hcont $$ %_
  iapply Hcont

/-- Composable total call rule for generated `func97` at absolute index `99`.
It returns both output slice descriptors and all shadow-frame ownership. -/
theorem splitAt_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr dataPtr length mid sourceLoc stackTop : UInt32)
    (oldFrame0 oldFrame4 oldFrame8 oldFrame12
      oldFrame16 oldFrame20 oldFrame24 oldFrame28
      oldResult0 oldResult4 oldResult8 oldResult12 : UInt32)
    (hmid : mid ≤ length)
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    (hresultRoom : resultPtr.toNat + 16 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 32) + 0) oldFrame0 ∗
      pointsTo_u32 ((stackTop - 32) + 4) oldFrame4 ∗
      pointsTo_u32 ((stackTop - 32) + 8) oldFrame8 ∗
      pointsTo_u32 ((stackTop - 32) + 12) oldFrame12 ∗
      pointsTo_u32 ((stackTop - 32) + 16) oldFrame16 ∗
      pointsTo_u32 ((stackTop - 32) + 20) oldFrame20 ∗
      pointsTo_u32 ((stackTop - 32) + 24) oldFrame24 ∗
      pointsTo_u32 ((stackTop - 32) + 28) oldFrame28 ∗
      pointsTo_u32 resultPtr oldResult0 ∗
      pointsTo_u32 (resultPtr + 4) oldResult4 ∗
      pointsTo_u32 (resultPtr + 8) oldResult8 ∗
      pointsTo_u32 (resultPtr + 12) oldResult12 ∗
      ((runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 stackTop) ∗
        sliceDescriptorAt ((stackTop - 32) + 0) dataPtr mid ∗
        sliceDescriptorAt ((stackTop - 32) + 8)
          (dataPtr + (mid <<< 3)) (length - mid) ∗
        sliceDescriptorAt ((stackTop - 32) + 16) dataPtr mid ∗
        sliceDescriptorAt ((stackTop - 32) + 24)
          (dataPtr + (mid <<< 3)) (length - mid) ∗
        sliceDescriptorAt resultPtr dataPtr mid ∗
        sliceDescriptorAt (resultPtr + 8)
          (dataPtr + (mid <<< 3)) (length - mid)) -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 sourceLoc, .i32 mid, .i32 length, .i32 dataPtr,
            .i32 resultPtr] ++ stack },
        .call 99 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hf0, Hf4, Hf8, Hf12, Hf16, Hf20,
    Hf24, Hf28, Hr0, Hr4, Hr8, Hr12, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 99 splitAtFunction
      (by decide) splitAt_index $$ Hruntime
  iintro Hruntime
  simp [splitAtFunction, func97Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  have Hbody := splitAt_body_twp (α := α)
    resultPtr dataPtr length mid sourceLoc stackTop
    oldFrame0 oldFrame4 oldFrame8 oldFrame12
    oldFrame16 oldFrame20 oldFrame24 oldFrame28
    oldResult0 oldResult4 oldResult8 oldResult12
    hmid hframeRoom hresultRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [splitAtParams, splitAtLocals, UInt32.add_zero] at Hbody
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hf0]
  · iexact Hf0
  isplitl [Hf4]
  · iexact Hf4
  isplitl [Hf8]
  · iexact Hf8
  isplitl [Hf12]
  · iexact Hf12
  isplitl [Hf16]
  · iexact Hf16
  isplitl [Hf20]
  · iexact Hf20
  isplitl [Hf24]
  · iexact Hf24
  isplitl [Hf28]
  · iexact Hf28
  isplitl [Hr0]
  · iexact Hr0
  isplitl [Hr4]
  · iexact Hr4
  isplitl [Hr8]
  · iexact Hr8
  isplitl [Hr12]
  · iexact Hr12
  iintro Hpost
  iintro %calleeControls
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append,
    List.drop_eq_nil_of_le (by decide : 5 ≤
      [.i32 resultPtr, .i32 dataPtr, .i32 length, .i32 mid,
        .i32 sourceLoc].length)]
  iapply Hdone
  iexact Hpost

end Project.Mergesort.SplitAtProof
