import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Byte rules for every terminal view

`CodeLib.SepLogic.SmallStepTotalLiftingBytes` states the byte rules
`twp_load8U` and `twp_store8`, and the rule `twp_drop`, for the
normal-result adapter only.  A proof that opens `Wasm.SmallStep.Outcome`
cannot apply them.  This module states the same five rules in the
terminal-generic form of `CodeLib.SepLogic.SmallStepTotalLifting`, so they
apply under every `TerminalView`.  The proofs of the four byte rules follow
`twp_load32` and `twp_store32`, and `twp_drop_gen` is one pure step.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

section terminalGenericBytes

variable {hlc : outParam HasLC} {α : Type}
variable [WasmSmallStepGS hlc α]
variable {Terminal : Type}
variable [view : TerminalView α Terminal]
local instance (priority := high) activeTerminalLanguageBytes :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage
local instance (priority := high) activeTerminalIrisGSBytes :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      activeTerminalLanguageBytes (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }
variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

/-- Total rule for `i32.load8_u` under every terminal view. -/
theorem twp_load8U_gen
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some byte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some byte) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  wasm_twp_start_with iintro Hpt Htwp
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read8 (address + offset) = byte ∧
        (address + offset).toNat < store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_facts store ns obs nt (address + offset) byte $$
      [Hσ Hpt]
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by omega
  wasm_twp_step (by
      simpa [Hread] using
        (Step.load8U (α := α) (address := Value.i32 address) rfl hbound)) =>
    wasm_twp_frame
      iapply_exact Htwp with Hpt

/-- Offset-zero form of `twp_load8U_gen`. -/
theorem twp_load8U_addr_gen
    {params localValues values : List Value}
    {address : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some byte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some byte) -∗
      WP (.running ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running ⟨⟨params, localValues, .i32 address :: values⟩,
      .load8U 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  simpa only [UInt32.add_zero] using
    (twp_load8U_gen (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (params := params)
      (localValues := localValues) (values := values) (code := code)
      (arity := arity) (remainder := remainder) (controls := controls)
      (calls := calls) byte (by simp))

/-- Total rule for `i32.store8` under every terminal view. -/
theorem twp_store8_gen
    {params localValues values : List Value}
    {address offset value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldByte : UInt8)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat) :
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
  wasm_twp_start_with iintro Hpt Htwp
  ihave_pure HinBounds :
      ⌜(address + offset).toNat < store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_inBounds store ns obs nt (address + offset)
      oldByte $$ [Hσ Hpt]
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by omega
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
          .store8 offset :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.store8 offset))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write8 (address + offset)
                value.toUInt8 } }⟩ := by
    simpa only [setMemory_eq] using
      Step.store8 (α := α) (address := Value.i32 address) rfl hbound
  wasm_twp_step expectedStep =>
    imod stateInterp_store8 store ns obs nt
        (address + offset) oldByte value.toUInt8 HinBounds $$
        [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
    wasm_twp_frame
      iapply_exact Htwp with Hpt

/-- Offset-zero form of `twp_store8_gen`. -/
theorem twp_store8_addr_gen
    {params localValues values : List Value}
    {address value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldByte : UInt8) :
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some oldByte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some value.toUInt8) -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store8 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  simpa only [UInt32.add_zero] using
    (twp_store8_gen (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) (value := value)
      (params := params) (localValues := localValues) (values := values)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls) oldByte (by simp))

/-- Total rule for `drop` under every terminal view. -/
theorem twp_drop_gen
    {params localValues values : List Value}
    {value : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, localValues, value :: values⟩,
        .drop :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.drop)

end terminalGenericBytes

end Wasm.SmallStep
