import Project.ByteEcho.HostProof

set_option maxRecDepth 8388608
set_option maxHeartbeats 0

/-!
# Proof of the byte-echo driver suffix

The generated allocator is discharged in `Adequacy.lean`.  This file starts
immediately after the allocator has returned the one-byte buffer to the
exported body, and proves the rest of the driver with total Iris WP: the
buffer is zeroed, one byte is read into it, the read count is compared with
`1`, the byte is written back, and the no-op deallocator returns.
-/

namespace Project.ByteEcho.DriverProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.ByteEcho.Contracts
open scoped Wasm.SmallStep.Outcome

-- Unfold the definitionally equal generic/outcome Iris instances when matching WPs.
set_option backward.isDefEq.respectTransparency false

private abbrev HeapIProp := IProp (WasmHeapGF Universal.State)

/-! ## Outcome-generic `i32.store8`

`CodeLib.SepLogic.SmallStepTotalLiftingBytes.twp_store8` is stated only for the
`List Value` terminal, while this proof runs in the outcome view.  The rule
below is the same proof, stated for the outcome view and written in the style
`SmallStepTotalLifting` uses for `twp_store32`.  Once #235 lands (byte rules
generic over `TerminalView`) this local copy can be dropped. -/

section outcomeStore8

variable {hlc : outParam HasLC} {α : Type}
variable [WasmSmallStepGS hlc α]
variable {s : Stuckness} {E : CoPset}
variable {Φ : ObservableOutcome → IProp (WasmHeapGF α)}

/-- Total `i32.store8` in the outcome view. -/
private theorem twp_store8
    {params localValues values : List Value}
    {address offset value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldByte : UInt8)
    (hnowrap :
      (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store8 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some oldByte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some value.toUInt8) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hpt Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave_pure HinBounds :
      ⌜(address + offset).toNat < store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_inBounds store ns obs nt
      (address + offset) oldByte $$ [Hσ Hpt]
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    omega
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
          .store8 offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.store8 offset))
      ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder,
          controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write8
                (address + offset) value.toUInt8 } }⟩ := by
    simpa only [setMemory_eq] using
      Step.store8 (α := α) (address := Value.i32 address) rfl hbound
  wasm_twp_step expectedStep =>
    imod stateInterp_store8 store ns obs nt
        (address + offset) oldByte value.toUInt8
        (by simpa [hnowrap] using HinBounds) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
    wasm_twp_frame
      iapply_exact Htwp with Hpt

end outcomeStore8

def echoBody : Program :=
  [.localGet 0, .const 1, .call 8, .const 1, .ne, .br_if 0,
    .localGet 0, .const 1, .call 9]

def releaseBody : Program :=
  [.localGet 0, .const 1, .const 1, .call 7, .ret]

def oomBody : Program :=
  [.const 1, .const 1, .call 15, .unreachable]

def afterAllocBody : Program :=
  [.localTee 0, .eqz, .br_if 0,
    .localGet 0, .const 0, .store8 0,
    .block 0 0 echoBody] ++ releaseBody

def outerBody : Program :=
  [.const 1, .const 1, .call 5] ++ afterAllocBody

def echoFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := echoBody
    continuation := releaseBody
    belowStack := [] }

def outerFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := outerBody
    continuation := oomBody
    belowStack := [] }

/-- The exported body immediately after `call 5` has returned `heapBase`. -/
def afterAllocExpr : Expr Universal.State := .running
  { locals := ⟨[], [.i32 0], [.i32 heapBase]⟩
    code := afterAllocBody
    resultArity := 0
    callerRemainder := []
    control := [outerFrame]
    calls := [] }

private theorem func4_index :
    Project.ByteEcho.module.funcs[4]? = some Project.ByteEcho.func4Def := by
  rfl

/-- Total correctness of the suffix beginning immediately after the
allocator's return. -/
theorem twp_afterAlloc
    [WasmSmallStepGS hlc Universal.State]
    (b oldByte : UInt8) {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      Project.ByteEcho.Contracts.ByteSlice heapBase [oldByte] ∗
      Streams [b] [] false ∗
      (RuntimeContext -∗ Streams [] [b] false -∗ Phi (.done []))) ⊢
      WP afterAllocExpr @ s; E [{ Phi }] := by
  iintro ⟨Hruntime, Hslice, Hstreams, Hfinal⟩
  simp only [afterAllocExpr, afterAllocBody, releaseBody, List.cons_append,
    List.nil_append]
  iapply twp_localTee rfl
  simp only [List.length, Nat.sub_self, List.set_cons_zero]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  isimp only [Project.ByteEcho.Contracts.ByteSlice, Project.Mergesort.Representations.ByteSlice,
    pointsToBytes] at Hslice
  icases Hslice with ⟨%hnowrap, Hbyte, _Hemp⟩
  ihave Hbyte0 : pointsTo (GF := WasmHeapGF Universal.State)
      (H := WasmHeapMap) (⟨0, heapBase + 0⟩ : MemoryKey) (DFrac.own 1)
      (some oldByte) $$ [Hbyte]
  · rw [UInt32.add_zero]
    iexact Hbyte
  iapply twp_store8 (address := heapBase) (offset := 0) (value := 0)
      oldByte (by decide) $$ Hbyte0
  iintro Hbyte
  have hzeroByte : (0 : UInt32).toUInt8 = (0 : UInt8) := by decide
  isimp only [hzeroByte] at Hbyte
  ihave Hbuffer : Project.ByteEcho.Contracts.ByteSlice heapBase [0] $$ [Hbyte]
  · unfold Project.ByteEcho.Contracts.ByteSlice Project.Mergesort.Representations.ByteSlice
    isplitl []
    · ipureintro
      decide
    · -- twice: the head cell, then the empty tail
      unfold pointsToBytes pointsToBytes
      rw [UInt32.add_zero] at *
      isplitl [Hbyte]
      · iexact Hbyte
      · iempintro
  iapply twp_block
  simp only [echoBody, List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_const
  have Hread := Project.ByteEcho.HostProof.func5_correct (hlc := hlc)
      (ptr := heapBase) (requested := 1)
      (buffer := [0]) (input := [b]) (output := []) (raised := false)
      (callerLocals := ⟨[], [.i32 heapBase], []⟩)
      (stack := [])
      (code := echoBody.drop 3)
      (arity := 0) (remainder := [])
      (controls := [echoFrame, outerFrame])
      (calls := []) (s := s) (E := E) (Phi := Phi)
  unfold CallContract callExpr
    Project.Mergesort.Contracts.callExpr at Hread
  simp only [echoBody, echoFrame, releaseBody, List.drop_succ_cons,
    List.drop_zero, List.cons_append, List.nil_append] at Hread
  iapply Hread
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hstreams]
  · iexact Hstreams
  isplitl [Hbuffer]
  · iexact Hbuffer
  isplitl []
  · ipureintro
    decide
  iintro Hruntime Hstreams Hbuffer %_hcount
  have hcount : min (UInt32.toNat 1) [b].length = 1 := by simp
  isimp only [hcount, List.drop_one, List.tail_cons, List.take_one,
    List.head?_cons, Option.toList_some, List.drop_nil, List.append_nil,
    List.take_succ_cons, List.take_zero] at Hstreams Hbuffer
  unfold ResumeWP resumeExpr Project.Mergesort.Contracts.resumeExpr
  simp only [hcount, List.cons_append, List.nil_append]
  iapply twp_const
  iapply twp_ne (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  have Hwrite := Project.ByteEcho.HostProof.func6_correct (hlc := hlc)
      (ptr := heapBase) (requested := 1)
      (bytes := [b]) (input := []) (output := []) (raised := false)
      (callerLocals := ⟨[], [.i32 heapBase], []⟩)
      (stack := []) (code := [])
      (arity := 0) (remainder := [])
      (controls := [echoFrame, outerFrame])
      (calls := []) (s := s) (E := E) (Phi := Phi)
  unfold CallContract callExpr
    Project.Mergesort.Contracts.callExpr at Hwrite
  simp only [echoBody, echoFrame, releaseBody, List.cons_append,
    List.nil_append] at Hwrite
  iapply Hwrite
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hstreams]
  · iexact Hstreams
  isplitl [Hbuffer]
  · iexact Hbuffer
  isplitl []
  · ipureintro
    simp
  iintro Hruntime Hstreams _Hbuffer
  unfold ResumeWP resumeExpr Project.Mergesort.Contracts.resumeExpr
  simp only [List.nil_append]
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_const
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  iapply Wasm.SmallStep.twp_call Project.ByteEcho.module 7
      Project.ByteEcho.func4Def (by decide) func4_index $$ Hmodule
  iintro Hmodule
  simp [Project.ByteEcho.func4Def, Project.ByteEcho.func4,
    Function.toLocals, Function.numParams]
  iapply Wasm.SmallStep.twp_returnFromCallFallthrough $$ Hmodule
  iintro Hmodule
  simp only [List.take_zero, List.nil_append]
  iapply twp_returnFromFunction
  simp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_outcome_done
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · unfold RuntimeContext
    iframe
  iapply Hfinal $$ Hruntime Hstreams

end Project.ByteEcho.DriverProof
