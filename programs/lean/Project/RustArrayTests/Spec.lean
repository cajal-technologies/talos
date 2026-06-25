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

/-! ## Exported ABI wrappers (fat pointer in memory)

The internal specs above verify the inlined-reuse impl bodies. The wasm exports
(`func5`–`func8`) receive the slice as a fat pointer in linear memory: each loads
`(dataPtr, len)` back with `fatPtrLoadWp` and calls the impl body above. So, like
the `rust_u64_tests` crate, the actual exported functions are verified — here
end-to-end through the memory marshalling, conditional on the in-bounds ABI
contract. Each call bridge re-proves the impl's behaviour at an arbitrary store
(the impls touch no memory), reusing the same CodeLib chunks. -/

private theorem lenPlusOne_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len : UInt32) (rest : List Value) :
    TerminatesWith env «module» 1 st (.i32 len :: .i32 dataPtr :: rest)
      (fun _ vs => vs = .i32 (len + 1) :: rest) := by
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop]
  rw [len_seq 1 len [] rfl]
  simp only [wp_const_cons, wp_add_cons, wp_ret_cons, Continuation.Return.injEq,
    List.cons.injEq, List.cons_append, and_true, List.append_nil]
  rw [show (1 : UInt32) + len = len + 1 from by bv_decide]
  simp

private theorem lenPlusArg_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len n : UInt32) (rest : List Value) :
    TerminatesWith env «module» 0 st (.i32 n :: .i32 len :: .i32 dataPtr :: rest)
      (fun _ vs => vs = .i32 (len + n) :: rest) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  unfold func0Def func0
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, ValueType.zero, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.drop]
  rw [len_seq 1 len [] rfl]
  simp only [wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    wp_add_cons, wp_ret_cons, Continuation.Return.injEq, List.cons.injEq, List.cons_append,
    and_true, List.append_nil]
  rw [show n + len = len + n from by bv_decide]
  simp

private theorem emptyPlusThree_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len : UInt32) (rest : List Value) :
    TerminatesWith env «module» 4 st (.i32 len :: .i32 dataPtr :: rest)
      (fun _ vs => vs = .i32 (isEmptyValue len + 3) :: rest) := by
  apply TerminatesWith.of_wp_entry_for (f := func4Def) rfl
  unfold func4Def func4
  wp_run
  apply wp_call_tw (isEmpty_call st dataPtr len [])
  intro st1 vs1 h1
  obtain ⟨hvs1, _, _⟩ := h1
  subst hvs1
  wp_run
  rw [isEmptyValue_and_one]
  rw [show (3 : UInt32) + isEmptyValue len = isEmptyValue len + 3 from by bv_decide]
  simp

private theorem emptyXorFlag_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len flag : UInt32) (rest : List Value) :
    TerminatesWith env «module» 2 st (.i32 flag :: .i32 len :: .i32 dataPtr :: rest)
      (fun _ vs => vs = .i32 (isEmptyValue len ^^^ flag) :: rest) := by
  apply TerminatesWith.of_wp_entry_for (f := func2Def) rfl
  unfold func2Def func2
  wp_run
  apply wp_call_tw (isEmpty_call st dataPtr len [])
  intro st1 vs1 h1
  obtain ⟨hvs1, _, _⟩ := h1
  subst hvs1
  wp_run
  rw [isEmptyValue_and_one]
  simp

@[spec_of "rust-exported" "rust_array_tests::len_plus_one"]
def LenPlusOneExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
    st.mem.read32 (p + 0) = dataPtr → st.mem.read32 (p + 4) = len →
    p.toNat + 8 ≤ st.mem.pages * 65536 →
    TerminatesWith env «module» 8 st [.i32 p] (fun _ rs => rs = [.i32 (len + 1)])

set_option maxRecDepth 4096 in
@[proves Project.RustArrayTests.Spec.LenPlusOneExportSpec]
theorem len_plus_one_export_correct : LenPlusOneExportSpec := by
  intro env st p dataPtr len hdata hlen hbound
  apply TerminatesWith.of_wp_entry_for (f := func8Def) rfl
  unfold func8Def func8
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, List.length_cons, List.length_nil]
  rw [fatPtrLoadWp 0 p dataPtr len [] (by simp) hbound hdata hlen]
  apply wp_call_tw (lenPlusOne_call st dataPtr len [])
  intro st1 vs1 h1
  subst h1
  wp_run
  simp

@[spec_of "rust-exported" "rust_array_tests::len_plus_arg"]
def LenPlusArgExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len n : UInt32),
    st.mem.read32 (p + 0) = dataPtr → st.mem.read32 (p + 4) = len →
    p.toNat + 8 ≤ st.mem.pages * 65536 →
    TerminatesWith env «module» 7 st [.i32 n, .i32 p] (fun _ rs => rs = [.i32 (len + n)])

set_option maxRecDepth 4096 in
@[proves Project.RustArrayTests.Spec.LenPlusArgExportSpec]
theorem len_plus_arg_export_correct : LenPlusArgExportSpec := by
  intro env st p dataPtr len n hdata hlen hbound
  apply TerminatesWith.of_wp_entry_for (f := func7Def) rfl
  unfold func7Def func7
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, List.length_cons, List.length_nil]
  rw [fatPtrLoadWp 0 p dataPtr len [] (by simp) hbound hdata hlen]
  wp_run
  apply wp_call_tw (lenPlusArg_call st dataPtr len n [])
  intro st1 vs1 h1
  subst h1
  wp_run
  simp

@[spec_of "rust-exported" "rust_array_tests::empty_plus_three"]
def EmptyPlusThreeExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
    st.mem.read32 (p + 0) = dataPtr → st.mem.read32 (p + 4) = len →
    p.toNat + 8 ≤ st.mem.pages * 65536 →
    TerminatesWith env «module» 5 st [.i32 p] (fun _ rs => rs = [.i32 (isEmptyValue len + 3)])

set_option maxRecDepth 4096 in
@[proves Project.RustArrayTests.Spec.EmptyPlusThreeExportSpec]
theorem empty_plus_three_export_correct : EmptyPlusThreeExportSpec := by
  intro env st p dataPtr len hdata hlen hbound
  apply TerminatesWith.of_wp_entry_for (f := func5Def) rfl
  unfold func5Def func5
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, List.length_cons, List.length_nil]
  rw [fatPtrLoadWp 0 p dataPtr len [] (by simp) hbound hdata hlen]
  apply wp_call_tw (emptyPlusThree_call st dataPtr len [])
  intro st1 vs1 h1
  subst h1
  wp_run
  simp

@[spec_of "rust-exported" "rust_array_tests::empty_xor_flag"]
def EmptyXorFlagExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len flag : UInt32),
    st.mem.read32 (p + 0) = dataPtr → st.mem.read32 (p + 4) = len →
    p.toNat + 8 ≤ st.mem.pages * 65536 →
    TerminatesWith env «module» 6 st [.i32 flag, .i32 p]
      (fun _ rs => rs = [.i32 (isEmptyValue len ^^^ flag)])

set_option maxRecDepth 4096 in
@[proves Project.RustArrayTests.Spec.EmptyXorFlagExportSpec]
theorem empty_xor_flag_export_correct : EmptyXorFlagExportSpec := by
  intro env st p dataPtr len flag hdata hlen hbound
  apply TerminatesWith.of_wp_entry_for (f := func6Def) rfl
  unfold func6Def func6
  simp only [Function.toLocals, Function.numParams, List.take, List.reverse, List.reverseAux,
    List.map, List.length_cons, List.length_nil]
  rw [fatPtrLoadWp 0 p dataPtr len [] (by simp) hbound hdata hlen]
  wp_run
  apply wp_call_tw (emptyXorFlag_call st dataPtr len flag [])
  intro st1 vs1 h1
  subst h1
  wp_run
  simp

end Project.RustArrayTests.Spec
