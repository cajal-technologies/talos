import Project.RustArrayTests.Program
import Interpreter.Wasm.Wp.Call

/-!
# Reuse tests for the `CodeLib/RustStd/Array` corpus
-/

namespace Project.RustArrayTests.Spec

open Wasm Wasm.RustStd Wasm.RustStd.Array

set_option linter.unusedSimpArgs false

private theorem isEmpty_call {env : HostEnv Unit} (st : Store Unit)
    (ptr len : UInt32) (rest : List Value) :
    TerminatesWith env «module» 3 st (.i32 len :: .i32 ptr :: rest)
      (fun st' vs => vs = .i32 (isEmptyValue len) :: rest ∧ framePost st st') :=
  TerminatesWith.of_returns_wp (f := func3Def) (rs := [.i32 (isEmptyValue len)]) rfl rfl
    (isEmptyBodyWp st 1 len [] rfl) rfl

/-! ## len -/

@[spec_of "rust-internal" "rust_array_tests::len_plus_one"]
def LenPlusOneSpec : Prop := ∀ (env : HostEnv Unit) (ptr len : UInt32),
  TerminatesWith env «module» 1 «module».initialStore [.i32 len, .i32 ptr]
    (fun _ rs => rs = [.i32 (len + 1)])

set_option maxRecDepth 4096 in
@[proves Project.RustArrayTests.Spec.LenPlusOneSpec]
theorem len_plus_one_correct : LenPlusOneSpec := by
  intro env ptr len
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop]
  rw [len_seq 1 len [] rfl]
  simp only [wp_const_cons, wp_add_cons, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, and_true, List.append_nil]
  rw [show (1 : UInt32) + len = len + 1 from by bv_decide]
  simp

@[spec_of "rust-internal" "rust_array_tests::len_plus_arg"]
def LenPlusArgSpec : Prop := ∀ (env : HostEnv Unit) (ptr len n : UInt32),
  TerminatesWith env «module» 0 «module».initialStore [.i32 n, .i32 len, .i32 ptr]
    (fun _ rs => rs = [.i32 (len + n)])

set_option maxRecDepth 4096 in
@[proves Project.RustArrayTests.Spec.LenPlusArgSpec]
theorem len_plus_arg_correct : LenPlusArgSpec := by
  intro env ptr len n
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  unfold func0Def func0
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop]
  rw [len_seq 1 len [] rfl]
  simp only [wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    wp_add_cons, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, and_true,
    List.append_nil]
  rw [show n + len = len + n from by bv_decide]
  simp

/-! ## is_empty -/

@[spec_of "rust-internal" "rust_array_tests::empty_plus_three"]
def EmptyPlusThreeSpec : Prop := ∀ (env : HostEnv Unit) (ptr len : UInt32),
  TerminatesWith env «module» 4 «module».initialStore [.i32 len, .i32 ptr]
    (fun _ rs => rs = [.i32 (isEmptyValue len + 3)])

set_option maxRecDepth 4096 in
@[proves Project.RustArrayTests.Spec.EmptyPlusThreeSpec]
theorem empty_plus_three_correct : EmptyPlusThreeSpec := by
  intro env ptr len
  apply TerminatesWith.of_wp_entry_for (f := func4Def) rfl
  unfold func4Def func4
  wp_run
  apply wp_call_tw (isEmpty_call «module».initialStore ptr len [])
  intro st1 vs1 h1
  obtain ⟨hvs1, _, _⟩ := h1
  subst hvs1
  wp_run
  rw [isEmptyValue_and_one]
  rw [show (3 : UInt32) + isEmptyValue len = isEmptyValue len + 3 from by bv_decide]
  simp

@[spec_of "rust-internal" "rust_array_tests::empty_xor_flag"]
def EmptyXorFlagSpec : Prop := ∀ (env : HostEnv Unit) (ptr len flag : UInt32),
  TerminatesWith env «module» 2 «module».initialStore [.i32 flag, .i32 len, .i32 ptr]
    (fun _ rs => rs = [.i32 (isEmptyValue len ^^^ flag)])

set_option maxRecDepth 4096 in
@[proves Project.RustArrayTests.Spec.EmptyXorFlagSpec]
theorem empty_xor_flag_correct : EmptyXorFlagSpec := by
  intro env ptr len flag
  apply TerminatesWith.of_wp_entry_for (f := func2Def) rfl
  unfold func2Def func2
  wp_run
  apply wp_call_tw (isEmpty_call «module».initialStore ptr len [])
  intro st1 vs1 h1
  obtain ⟨hvs1, _, _⟩ := h1
  subst hvs1
  wp_run
  rw [isEmptyValue_and_one]
  simp

end Project.RustArrayTests.Spec
