import Interpreter.Wasm.SmallStep
import Interpreter.Wasm.Examples.UIntLemmas
import Mathlib.Tactic

/-! ## Example: mutually recursive parity

The proof is contextual in the saved Wasm call stack. Consequently an
induction hypothesis for a recursive callee returns into the exact suspended
caller, instead of proving only root-level completion.
-/

namespace Wasm
open SmallStep

def IsEvenRec : Program := [
  .block 0 0 [
    .localGet 0,
    .eqz,
    .br_if 0,
    .localGet 0,
    .const 1,
    .sub,
    .call 1,
    .eqz,
    .localSet 0
  ],
  .localGet 0,
  .eqz
]

def IsOddRec : Program := [
  .block 0 0 [
    .localGet 0,
    .eqz,
    .br_if 0,
    .localGet 0,
    .const 1,
    .sub,
    .call 0,
    .localSet 0
  ],
  .localGet 0
]

def evenOddModule : Module :=
  { funcs := [
      { params := [.i32], body := IsEvenRec, results := [.i32] },
      { params := [.i32], body := IsOddRec, results := [.i32] }] }

private def parityStore : MachineStore Unit :=
  { runtime := { module := evenOddModule, host := {} }
    wasm := evenOddModule.initialStore }

private def evenValue (n : UInt32) : UInt32 :=
  if n.toNat % 2 = 0 then 1 else 0

private def oddValue (n : UInt32) : UInt32 :=
  if n.toNat % 2 = 1 then 1 else 0

private def boolNot (value : UInt32) : UInt32 :=
  if value = 0 then 1 else 0

private def parityCallee
    (body : Program) (n : UInt32) (calls : List CallFrame) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 n] }
        code := body
        resultArity := 1
        callerRemainder := []
        calls }
    store := parityStore }

def evenConfig (n : UInt32) : Config Unit :=
  parityCallee IsEvenRec n []

def oddConfig (n : UInt32) : Config Unit :=
  parityCallee IsOddRec n []

private def parityCompleted
    (parameter result : UInt32) (calls : List CallFrame) : Config Unit :=
  { expr := .running
      { locals :=
          { params := [.i32 parameter]
            values := [.i32 result] }
        code := []
        resultArity := 1
        callerRemainder := []
        calls }
    store := parityStore }

private def parityReturn
    (result : UInt32) (calls : List CallFrame) : Config Unit :=
  match calls with
  | [] => ⟨.done [.i32 result], parityStore⟩
  | caller :: rest =>
      { expr := .running
          (resumeCaller
            { locals := { values := [.i32 result] }
              code := []
              resultArity := 1
              callerRemainder := []
              calls := caller :: rest }
            caller rest)
        store := parityStore }

private theorem parity_complete_steps
    (parameter result : UInt32) (calls : List CallFrame) :
    ∃ trace,
      Steps (parityCompleted parameter result calls) trace
        (parityReturn result calls) := by
  cases calls with
  | nil =>
      exact ⟨[.administrative .finish], Steps.single .finish⟩
  | cons caller rest =>
      exact ⟨[.administrative .returnFromCall],
        Steps.single .returnFromCallFallthrough⟩

private def evenBlockBody : Program := [
  .localGet 0,
  .eqz,
  .br_if 0,
  .localGet 0,
  .const 1,
  .sub,
  .call 1,
  .eqz,
  .localSet 0
]

private def oddBlockBody : Program := [
  .localGet 0,
  .eqz,
  .br_if 0,
  .localGet 0,
  .const 1,
  .sub,
  .call 0,
  .localSet 0
]

private def evenBlockFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := evenBlockBody
    continuation := [.localGet 0, .eqz]
    belowStack := [] }

private def oddBlockFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := oddBlockBody
    continuation := [.localGet 0]
    belowStack := [] }

private def evenCaller (n : UInt32) : CallFrame :=
  { locals := { params := [.i32 n] }
    continuation := [.eqz, .localSet 0]
    resultArity := 1
    callerRemainder := []
    control := [evenBlockFrame] }

private def oddCaller (n : UInt32) : CallFrame :=
  { locals := { params := [.i32 n] }
    continuation := [.localSet 0]
    resultArity := 1
    callerRemainder := []
    control := [oddBlockFrame] }

private theorem even_zero_prefix (calls : List CallFrame) :
    ∃ trace,
      Steps (parityCallee IsEvenRec 0 calls) trace
        (parityCompleted 0 1 calls) := by
  refine ⟨[
    .instruction (.block 0 0 evenBlockBody),
    .instruction (.localGet 0),
    .instruction .eqz,
    .instruction (.br_if 0),
    .instruction (.localGet 0),
    .instruction .eqz], ?_⟩
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqz rfl)
  apply Steps.cons (.brIf (by decide) (by rfl))
  apply Steps.cons (.localGet rfl)
  exact Steps.single (.eqz rfl)

private theorem odd_zero_prefix (calls : List CallFrame) :
    ∃ trace,
      Steps (parityCallee IsOddRec 0 calls) trace
        (parityCompleted 0 0 calls) := by
  refine ⟨[
    .instruction (.block 0 0 oddBlockBody),
    .instruction (.localGet 0),
    .instruction .eqz,
    .instruction (.br_if 0),
    .instruction (.localGet 0)], ?_⟩
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqz rfl)
  apply Steps.cons (.brIf (by decide) (by rfl))
  exact Steps.single (.localGet rfl)

private theorem even_nonzero_prefix
    (n : UInt32) (calls : List CallFrame) (hn : n ≠ 0) :
    ∃ trace,
      Steps (parityCallee IsEvenRec n calls) trace
        (parityCallee IsOddRec (n - 1) (evenCaller n :: calls)) := by
  refine ⟨[
    .instruction (.block 0 0 evenBlockBody),
    .instruction (.localGet 0),
    .instruction .eqz,
    .instruction (.br_if 0),
    .instruction (.localGet 0),
    .instruction (.const 1),
    .instruction .sub,
    .instruction (.call 1)], ?_⟩
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqz (result := 0) (by simp [hn]))
  apply Steps.cons .brIfZero
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .sub
  exact Steps.single (.call
    (functionIndex := 1) (store := parityStore)
    (fn := evenOddModule.funcs[1]!) (by decide) rfl)

private theorem odd_nonzero_prefix
    (n : UInt32) (calls : List CallFrame) (hn : n ≠ 0) :
    ∃ trace,
      Steps (parityCallee IsOddRec n calls) trace
        (parityCallee IsEvenRec (n - 1) (oddCaller n :: calls)) := by
  refine ⟨[
    .instruction (.block 0 0 oddBlockBody),
    .instruction (.localGet 0),
    .instruction .eqz,
    .instruction (.br_if 0),
    .instruction (.localGet 0),
    .instruction (.const 1),
    .instruction .sub,
    .instruction (.call 0)], ?_⟩
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqz (result := 0) (by simp [hn]))
  apply Steps.cons .brIfZero
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .sub
  exact Steps.single (.call
    (functionIndex := 0) (store := parityStore)
    (fn := evenOddModule.funcs[0]!) (by decide) rfl)

private theorem even_after_call
    (n result : UInt32) (calls : List CallFrame) :
    ∃ trace,
      Steps (parityReturn result (evenCaller n :: calls)) trace
        (parityCompleted (boolNot result) (boolNot (boolNot result)) calls) := by
  refine ⟨[
    .instruction .eqz,
    .instruction (.localSet 0),
    .administrative .exitControl,
    .instruction (.localGet 0),
    .instruction .eqz], ?_⟩
  simp only [parityReturn, evenCaller, resumeCaller]
  apply Steps.cons (.eqz (by rfl))
  apply Steps.cons (.localSet rfl)
  apply Steps.cons (.exitControl rfl)
  apply Steps.cons (.localGet rfl)
  exact Steps.single (.eqz rfl)

private theorem odd_after_call
    (n result : UInt32) (calls : List CallFrame) :
    ∃ trace,
      Steps (parityReturn result (oddCaller n :: calls)) trace
        (parityCompleted result result calls) := by
  refine ⟨[
    .instruction (.localSet 0),
    .administrative .exitControl,
    .instruction (.localGet 0)], ?_⟩
  simp only [parityReturn, oddCaller, resumeCaller]
  apply Steps.cons (.localSet rfl)
  apply Steps.cons (.exitControl rfl)
  exact Steps.single (.localGet rfl)

private theorem evenOdd_contextual_steps : ∀ n : UInt32,
    (∀ calls, ∃ trace,
      Steps (parityCallee IsEvenRec n calls) trace
        (parityReturn (evenValue n) calls)) ∧
    (∀ calls, ∃ trace,
      Steps (parityCallee IsOddRec n calls) trace
        (parityReturn (oddValue n) calls)) := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | h measure ih =>
    subst measure
    by_cases hn : n = 0
    · subst n
      constructor
      · intro calls
        obtain ⟨initialTrace, hinitial⟩ := even_zero_prefix calls
        obtain ⟨suffix, hsuffix⟩ := parity_complete_steps 0 1 calls
        simpa [evenValue] using
          ⟨initialTrace ++ suffix, Steps.trans hinitial hsuffix⟩
      · intro calls
        obtain ⟨initialTrace, hinitial⟩ := odd_zero_prefix calls
        obtain ⟨suffix, hsuffix⟩ := parity_complete_steps 0 0 calls
        simpa [oddValue] using
          ⟨initialTrace ++ suffix, Steps.trans hinitial hsuffix⟩
    · have hnn : n.toNat ≠ 0 := by
        intro hz
        exact hn (UInt32.toNat.inj hz)
      have hpred : (n - 1).toNat < n.toNat :=
        UInt32.toNat_sub_one_lt hnn
      have ihpair := ih (n - 1).toNat hpred (n - 1) rfl
      constructor
      · intro calls
        obtain ⟨prefixTrace, hprefix⟩ :=
          even_nonzero_prefix n calls hn
        obtain ⟨calleeTrace, hcallee⟩ :=
          ihpair.2 (evenCaller n :: calls)
        obtain ⟨resumeTrace, hresume⟩ :=
          even_after_call n (oddValue (n - 1)) calls
        obtain ⟨returnTrace, hreturn⟩ :=
          parity_complete_steps (boolNot (oddValue (n - 1)))
            (boolNot (boolNot (oddValue (n - 1)))) calls
        have hnsub := UInt32.toNat_sub_one_eq hnn
        have hresult :
            boolNot (boolNot (oddValue (n - 1))) = evenValue n := by
          unfold boolNot oddValue evenValue
          rw [hnsub]
          split_ifs <;> simp_all <;> omega
        have execution :=
          Steps.trans (Steps.trans (Steps.trans hprefix hcallee) hresume)
            hreturn
        rw [hresult] at execution
        exact ⟨_, execution⟩
      · intro calls
        obtain ⟨prefixTrace, hprefix⟩ :=
          odd_nonzero_prefix n calls hn
        obtain ⟨calleeTrace, hcallee⟩ :=
          ihpair.1 (oddCaller n :: calls)
        obtain ⟨resumeTrace, hresume⟩ :=
          odd_after_call n (evenValue (n - 1)) calls
        obtain ⟨returnTrace, hreturn⟩ :=
          parity_complete_steps (evenValue (n - 1))
            (evenValue (n - 1)) calls
        have hnsub := UInt32.toNat_sub_one_eq hnn
        have hresult : evenValue (n - 1) = oddValue n := by
          unfold evenValue oddValue
          rw [hnsub]
          split_ifs <;> simp_all <;> omega
        have execution :=
          Steps.trans (Steps.trans (Steps.trans hprefix hcallee) hresume)
            hreturn
        rw [hresult] at execution
        exact ⟨_, execution⟩

theorem even_steps (n : UInt32) :
    ∃ trace,
      Steps (evenConfig n) trace
        ⟨.done [.i32 (evenValue n)], parityStore⟩ := by
  simpa [evenConfig, parityReturn] using
    (evenOdd_contextual_steps n).1 []

theorem odd_steps (n : UInt32) :
    ∃ trace,
      Steps (oddConfig n) trace
        ⟨.done [.i32 (oddValue n)], parityStore⟩ := by
  simpa [oddConfig, parityReturn] using
    (evenOdd_contextual_steps n).2 []

theorem evenSpec (n : UInt32) :
    TerminatesWith (evenConfig n)
      (fun values _ => values = [.i32 (evenValue n)]) := by
  obtain ⟨trace, execution⟩ := even_steps n
  exact ⟨trace, _, _, execution, rfl⟩

theorem oddSpec (n : UInt32) :
    TerminatesWith (oddConfig n)
      (fun values _ => values = [.i32 (oddValue n)]) := by
  obtain ⟨trace, execution⟩ := odd_steps n
  exact ⟨trace, _, _, execution, rfl⟩

theorem evenPartial (n : UInt32) :
    PartiallyMeets (evenConfig n)
      (fun values _ => values = [.i32 (evenValue n)]) := by
  intro trace values store observed
  obtain ⟨expectedTrace, expected⟩ := even_steps n
  obtain ⟨rfl, rfl⟩ := steps_done_deterministic expected observed
  rfl

theorem oddPartial (n : UInt32) :
    PartiallyMeets (oddConfig n)
      (fun values _ => values = [.i32 (oddValue n)]) := by
  intro trace values store observed
  obtain ⟨expectedTrace, expected⟩ := odd_steps n
  obtain ⟨rfl, rfl⟩ := steps_done_deterministic expected observed
  rfl

end Wasm
