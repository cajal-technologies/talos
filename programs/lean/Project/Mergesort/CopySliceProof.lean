import Project.Mergesort.MemoryCopyProof

/-!
# Exact contracts for the generated slice-copy wrappers

`func93` is Rust's monomorphised `copy_from_slice` implementation. Its
successful nonempty path checks equal lengths and executes one `memory.copy`.
`func94` and `func95` are forwarding wrappers.
-/

namespace Project.Mergesort.CopySliceProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic
open Wasm.SmallStep
open Project.Mergesort.MemoryCopyProof

def copyLocals (destination length source metadata : UInt32) : Locals :=
  ⟨[.i32 destination, .i32 length, .i32 source, .i32 length, .i32 metadata],
    [.i32 0], []⟩

def forwardLocals (destination length source metadata : UInt32) : Locals :=
  ⟨[.i32 destination, .i32 length, .i32 source, .i32 length, .i32 metadata],
    [], []⟩

private theorem twp_ne
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≠ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .ne :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.ne hresult)

private theorem twp_and
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (lhs &&& rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .and :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.and)

theorem shiftedLength_toNat (length : UInt32) (count : Nat)
    (hlength : length.toNat = count)
    (hbytes : 8 * count < UInt32.size) :
    (length <<< (3 % 32)).toNat = 8 * count := by
  rw [UInt32.toNat_shiftLeft]
  norm_num
  rw [hlength]
  simp [Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt]
  · omega
  · simpa only [UInt32.size, Nat.mul_comm] using hbytes

theorem twp_copySliceImpl_body [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (destination source length metadata : UInt32)
    (sourceValues destinationValues : List UInt64)
    (hnonempty : sourceValues ≠ [])
    (hlengthValue : length.toNat = sourceValues.length)
    (hlength : sourceValues.length = destinationValues.length)
    (hsourceRoom : source.toNat + 8 * sourceValues.length ≤ UInt32.size)
    (hdestinationRoom :
      destination.toNat + 8 * destinationValues.length ≤ UInt32.size)
    (hbytes : 8 * sourceValues.length < UInt32.size)
    (caller : CallFrame) {calls : List CallFrame} :
    array64At source sourceValues ∗ array64At destination destinationValues ∗
      (array64At source sourceValues -∗
        array64At destination sourceValues -∗
        WP (.running
          ⟨{ caller.locals with values := caller.locals.values },
            caller.continuation, caller.resultArity, caller.callerRemainder,
            caller.control, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨copyLocals destination length source metadata,
        func93, 0, [], [], caller :: calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hshift : (length <<< (3 % 32)).toNat =
      8 * sourceValues.length :=
    shiftedLength_toNat length sourceValues.length hlengthValue hbytes
  have hshiftNonzero : length <<< (3 % 32) ≠ 0 := by
    intro heq
    have hzero := congrArg UInt32.toNat heq
    rw [hshift] at hzero
    simp only [UInt32.toNat_zero] at hzero
    have hpositive : 0 < sourceValues.length := by
      cases sourceValues with
      | nil => exact (hnonempty rfl).elim
      | cons value values => simp
    omega
  have hshiftNonzero' : length <<< 3 ≠ 0 := by
    simpa using hshiftNonzero
  iintro ⟨Hsource, Hdestination, Hdone⟩
  simp only [func93]
  iapply Wasm.SmallStep.twp_block
  iapply Wasm.SmallStep.twp_block
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply twp_ne (lhs := length) (rhs := length) (result := 0) (by simp)
  iapply Wasm.SmallStep.twp_const
  iapply twp_and (lhs := 0) (rhs := 1)
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply Wasm.SmallStep.twp_brIfZero
  iapply Wasm.SmallStep.twp_br rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_const
  iapply Wasm.SmallStep.twp_shl
  iapply Wasm.SmallStep.twp_localSet rfl
  iapply Wasm.SmallStep.twp_block
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_eqz
      (value := length <<< (3 % 32)) (result := 0)
      (by simp [hshiftNonzero'])
  iapply Wasm.SmallStep.twp_brIfZero
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply twp_memoryCopy_u64 hnonempty hshift hlength hsourceRoom
      hdestinationRoom $$ [Hsource Hdestination]
  · iframe
  · iintro ⟨Hsource, Hdestination⟩
    iapply Wasm.SmallStep.twp_exitControl rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    iapply Wasm.SmallStep.twp_returnFromCallExplicit
    simp only [List.take_zero, List.nil_append]
    iapply Hdone $$ Hsource Hdestination

/-- Composable call rule for absolute Wasm function index `95` (`func93`). -/
theorem twp_call_copySliceImpl [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (destination source length metadata : UInt32)
    (sourceValues destinationValues : List UInt64)
    (hnonempty : sourceValues ≠ [])
    (hlengthValue : length.toNat = sourceValues.length)
    (hlength : sourceValues.length = destinationValues.length)
    (hsourceRoom : source.toNat + 8 * sourceValues.length ≤ UInt32.size)
    (hdestinationRoom :
      destination.toNat + 8 * destinationValues.length ≤ UInt32.size)
    (hbytes : 8 * sourceValues.length < UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source sourceValues ∗ array64At destination destinationValues ∗
      (runtimeModuleOwn «module» -∗
        array64At source sourceValues -∗
        array64At destination sourceValues -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 metadata :: .i32 length :: .i32 source ::
            .i32 length :: .i32 destination :: stack⟩,
        .call 95 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsource, Hdestination, Hdone⟩
  ihave HruntimeLater : runtimeModuleOwn «module» $$ [Hruntime]
  · iexact Hruntime
  iapply Wasm.SmallStep.twp_call (α := α) «module» 95 func93Def
      (by decide) (by rfl) $$ HruntimeLater
  iintro Hruntime
  simp [func93Def, Function.toLocals, Function.numParams, ValueType.zero]
  let caller : CallFrame :=
    { locals := ⟨params, localValues, stack⟩
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls }
  have Hbody := twp_copySliceImpl_body (α := α)
      (s := s) (E := E) (Φ := Φ)
      destination source length metadata
      sourceValues destinationValues hnonempty hlengthValue hlength
      hsourceRoom hdestinationRoom hbytes caller (calls := calls)
  simp only [copyLocals, caller] at Hbody
  iapply Hbody
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Hdestination]
  · iexact Hdestination
  · iintro Hsource Hdestination
    iapply Hdone $$ Hruntime Hsource Hdestination

/-- Exact body contract for `func95`, the forwarding `spec_clone_from` shim. -/
theorem twp_specCloneFrom_body [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (destination source length metadata : UInt32)
    (sourceValues destinationValues : List UInt64)
    (hnonempty : sourceValues ≠ [])
    (hlengthValue : length.toNat = sourceValues.length)
    (hlength : sourceValues.length = destinationValues.length)
    (hsourceRoom : source.toNat + 8 * sourceValues.length ≤ UInt32.size)
    (hdestinationRoom :
      destination.toNat + 8 * destinationValues.length ≤ UInt32.size)
    (hbytes : 8 * sourceValues.length < UInt32.size)
    (caller : CallFrame) {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source sourceValues ∗ array64At destination destinationValues ∗
      (runtimeModuleOwn «module» -∗
        array64At source sourceValues -∗
        array64At destination sourceValues -∗
        WP (.running
          ⟨{ caller.locals with values := caller.locals.values },
            caller.continuation, caller.resultArity, caller.callerRemainder,
            caller.control, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨forwardLocals destination length source metadata,
        func95, 0, [], [], caller :: calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsource, Hdestination, Hdone⟩
  simp only [func95]
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  ihave Hafter : runtimeModuleOwn «module» -∗
      array64At source sourceValues -∗
      array64At destination sourceValues -∗
      WP (.running
        ⟨forwardLocals destination length source metadata,
          [.ret], 0, [], [], caller :: calls⟩ : Expr α)
        @ s; E [{ Φ }] $$ [Hdone]
  · iintro Hruntime Hsource Hdestination
    iapply Wasm.SmallStep.twp_returnFromCallExplicit
    simp only [List.take_zero, List.nil_append]
    iapply Hdone $$ Hruntime Hsource Hdestination
  iapply twp_call_copySliceImpl destination source length metadata
      sourceValues destinationValues hnonempty hlengthValue hlength
      hsourceRoom hdestinationRoom hbytes $$
      [Hruntime Hsource Hdestination Hafter]
  iframe

/-- Composable call rule for absolute index `97` (`func95`). -/
theorem twp_call_specCloneFrom [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (destination source length metadata : UInt32)
    (sourceValues destinationValues : List UInt64)
    (hnonempty : sourceValues ≠ [])
    (hlengthValue : length.toNat = sourceValues.length)
    (hlength : sourceValues.length = destinationValues.length)
    (hsourceRoom : source.toNat + 8 * sourceValues.length ≤ UInt32.size)
    (hdestinationRoom :
      destination.toNat + 8 * destinationValues.length ≤ UInt32.size)
    (hbytes : 8 * sourceValues.length < UInt32.size)
    {params localValues stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source sourceValues ∗ array64At destination destinationValues ∗
      (runtimeModuleOwn «module» -∗
        array64At source sourceValues -∗
        array64At destination sourceValues -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues,
          .i32 metadata :: .i32 length :: .i32 source ::
            .i32 length :: .i32 destination :: stack⟩,
        .call 97 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsource, Hdestination, Hdone⟩
  ihave HruntimeLater : runtimeModuleOwn «module» $$ [Hruntime]
  · iexact Hruntime
  iapply Wasm.SmallStep.twp_call (α := α) «module» 97 func95Def
      (by decide) (by rfl) $$ HruntimeLater
  iintro Hruntime
  simp [func95Def, Function.toLocals, Function.numParams]
  let caller : CallFrame :=
    { locals := ⟨params, localValues, stack⟩
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls }
  have Hbody := twp_specCloneFrom_body (α := α)
      (s := s) (E := E) (Φ := Φ)
      destination source length metadata sourceValues destinationValues
      hnonempty hlengthValue hlength hsourceRoom hdestinationRoom hbytes
      caller (calls := calls)
  simp only [forwardLocals, caller] at Hbody
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Hdestination]
  · iexact Hdestination
  · iintro Hruntime Hsource Hdestination
    iapply Hdone $$ Hruntime Hsource Hdestination

end Project.Mergesort.CopySliceProof
