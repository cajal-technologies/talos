import Project.MergeSort.MergeFull
import Project.MergeSort.ContentLemmas
import Project.MergeSort.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.AllocSpec

namespace Wasm.SepLogic.MergeSort

open Wasm Project.MergeSort Project.MergeSort.Spec Project.MergeSort.Framing

variable [WasmHeapGS]

/-
call graph (imports = [], .call N = funcN):
  func33 (export "merge_sort", params: i32 i32) →
    func15 (slice-header init, straight-line) →
    func1  (sort with pre-allocated scratch) →
      func2  → func20 (vec init, allocator deferred)
      func0  (field copy, straight-line)
      func3  (recursive sort) →
        func5  (slice split, allocator deferred)
        func3  (left half, recursive)
        func3  (right half, recursive)
        func6  (merge, proven by func6_terminates)
        func7  → func13 (copy-back, deferred)
      func4  → func8, func9 (dealloc, allocator deferred)
-/

-- func15: straight-line, stores v1 at ptr, v2 at ptr+4
omit [WasmHeapGS] in
private theorem func15_terminates
    (st : Store Unit) (ptr v1 v2 v3 : UInt32)
    (hb : ptr.toNat + 8 ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 15 st
      [.i32 v3, .i32 v2, .i32 v1, .i32 ptr]
      (fun st' _ => st'.mem.read32 ptr = v1 ∧ st'.mem.read32 (ptr + 4) = v2) := by
  have hb4 : ¬(ptr.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    have : (4 : UInt32).toNat = 4 := rfl; omega
  have hb0 : ¬(ptr.toNat + (0 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    have : (0 : UInt32).toNat = 0 := rfl; omega
  have hdisj : ptr.toNat + 4 ≤ (ptr + 4 : UInt32).toNat
      ∨ (ptr + 4 : UInt32).toNat + 4 ≤ ptr.toNat := by
    simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]
    omega
  have hz : ptr + (0 : UInt32) = ptr := UInt32.add_zero ptr
  apply TerminatesWith.of_run 1 []
      { st with mem := (st.mem.write32 (ptr + 4) v2).write32 ptr v1 }
  · rw [run_eq (show «module».imports[15]? = none from rfl)]
    conv_lhs =>
      simp only [
        show «module».funcs[15 - «module».imports.length]? = some func15Def from rfl,
        func15Def, func15,
        Function.numParams, Function.toLocals, List.map,
        List.take, List.reverse, List.reverseAux, List.drop,
        List.length_cons, List.length_nil,
        exec, execOne.eq_def,
        Locals.get,
        show (0 : Nat) < 4 from by omega,
        show (1 : Nat) < 4 from by omega,
        show (2 : Nat) < 4 from by omega,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        Mem.write32_pages,
        if_neg hb4, if_neg hb0, hz,
        ite_true, ite_false,
        List.nil_append]
  · constructor
    · exact Mem.read32_write32_same _ _ _
    · rw [Mem.read32_write32_of_disjoint _ _ _ _ hdisj]
      exact Mem.read32_write32_same _ _ _

-- func3: recursive merge sort; strong induction on src_n.toNat
-- sp parameter required: globalGet 0 reads the stack pointer from global 0
set_option maxHeartbeats 8000000 in
private theorem func3_terminates
    (st : Store Unit) (src_ptr src_n dst_ptr dst_n sp : UInt32)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hpristine : ∀ i, i < 1050240 →
      st.mem.bytes i = («module».initialStore (α := Unit)).mem.bytes i)
    (hmargin : 1050240 + 4 * src_n.toNat ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 3 st
      [.i32 dst_n, .i32 dst_ptr, .i32 src_n, .i32 src_ptr]
      (fun st' _ =>
        (wordsAt st'.mem src_ptr src_n.toNat).Pairwise (· ≤ ·) ∧
        (wordsAt st'.mem src_ptr src_n.toNat).Perm
          (wordsAt st.mem src_ptr src_n.toNat)) := by
  suffices key : ∀ (n : Nat) (st : Store Unit) (src_ptr src_n dst_ptr dst_n sp : UInt32),
      src_n.toNat = n →
      st.globals.globals[0]? = some (.i32 sp) →
      (∀ i, i < 1050240 →
        st.mem.bytes i = («module».initialStore (α := Unit)).mem.bytes i) →
      1050240 + 4 * src_n.toNat ≤ st.mem.pages * 65536 →
      TerminatesWith {} «module» 3 st
        [.i32 dst_n, .i32 dst_ptr, .i32 src_n, .i32 src_ptr]
        (fun st' _ =>
          (wordsAt st'.mem src_ptr src_n.toNat).Pairwise (· ≤ ·) ∧
          (wordsAt st'.mem src_ptr src_n.toNat).Perm
            (wordsAt st.mem src_ptr src_n.toNat)) from
    key _ st src_ptr src_n dst_ptr dst_n sp rfl hsp hpristine hmargin
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro st src_ptr src_n dst_ptr dst_n sp hn hsp hpristine hmargin
    by_cases hbase : src_n.toNat ≤ 1
    · -- base case: src_n ≤ 1, block exits via br_if 0, no allocator calls
      -- trace: globalGet/const/sub/localSet/localGet/globalSet (preamble, 6),
      --   block 0 0 (localGet/const/leU/const/and/br_if → Break 0, 6 body insts),
      --   localGet/const/add/globalSet/ret (postamble, 5) = 18 fuel total
      have hlocals_init : List.map ValueType.zero
          [ValueType.i32, ValueType.i32, ValueType.i32, ValueType.i32, ValueType.i32,
           ValueType.i32, ValueType.i32, ValueType.i32, ValueType.i32, ValueType.i32] =
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0] := by
        native_decide
      have h_leU  : src_n ≤ (1 : UInt32) := UInt32.le_iff_toNat_le.mpr (by simpa using hbase)
      have h_and1 : (1 : UInt32) &&& 1 = 1 := by decide
      have h_br   : (1 : UInt32) ≠ 0 := by decide
      -- List.length_cons leaves params.length as (((0+1)+1)+1)+1 rather than 4;
      -- add normalisation lemmas so the if-guards fire correctly
      have h_plen : ((((0 : Nat) + 1) + 1) + 1) + 1 = 4 := rfl
      have h_llen : ((((((((((0 : Nat) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 10 := rfl
      -- postamble add gives (32 : UInt32) + (sp - 32); use exact form in witness & dset
      have h_dset : (st.globals.globals.set 0 (.i32 (sp - 32))).set 0 (.i32 (32 + (sp - 32)))
          = st.globals.globals.set 0 (.i32 (32 + (sp - 32))) := by
        cases hg : st.globals.globals with
        | nil  => simp [hg] at hsp
        | cons hd tl => simp [List.set]
      -- postamble globalSet 0 needs a bounds check on the already-set globals
      have h_gset_ok : (st.globals.globals.set 0 (.i32 (sp - 32)))[0]? =
          some (.i32 (sp - 32)) := by
        cases hg : st.globals.globals with
        | nil  => simp [hg] at hsp
        | cons hd tl => simp [List.set_cons_zero]
      apply TerminatesWith.of_run 18 []
          { st with globals := { globals :=
              st.globals.globals.set 0 (.i32 (32 + (sp - 32))) } }
      · rw [run_eq (show «module».imports[3]? = none from rfl)]
        conv_lhs =>
          simp only [
            show «module».funcs[3 - «module».imports.length]? = some func3Def from rfl,
            func3Def, func3, Function.toLocals, Function.numParams,
            List.take, List.reverse, List.reverseAux, List.drop,
            List.length_cons, List.length_nil, List.length_set,
            h_plen, h_llen,
            Locals.get, Locals.set?,
            hlocals_init,
            show (1 : Nat) < 4 from by omega,
            show ¬((4 : Nat) < 4) from by omega,
            show (4 : Nat) < 4 + 10 from by omega,
            show (4 - 4 : Nat) = 0 from by omega,
            List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
            List.set_cons_zero, List.set_cons_succ,
            exec, execOne.eq_def,
            hsp,
            if_pos h_leU, h_and1, h_br,
            h_dset, h_gset_ok,
            Mem.write32_pages,
            ite_true, ite_false,
            List.nil_append, List.take_zero
          ]
      · -- postcondition: src_n ≤ 1, result state has same mem as st, so sorted (trivially) and perm (refl)
        refine ⟨?_, List.Perm.refl _⟩
        simp only [wordsAt]
        have h01 : src_n.toNat = 0 ∨ src_n.toNat = 1 := by omega
        rcases h01 with h | h <;> simp [h]
    · -- recursive case: src_n > 1
      -- Intended proof structure (all but allocator sorry'd):
      --   preamble (6 insts, simp): globalGet 0 / const 32 / sub / localSet 4 / localGet 4 / globalSet 0
      --   block 0 0:
      --     base-check (6 insts, simp): src_n > 1 → leU = 0 → and = 0 → br_if falls through
      --     mid computation (4 insts, simp): localGet 1 / const 1 / shrU / localSet 5 → mid = src_n>>>1
      --     call 5 (sorry: allocator terminates: deferred per MergeSortSpec)
      --     loads frame[0..12] into local[6..9] (simp)
      --     call 5 (sorry: allocator terminates: deferred per MergeSortSpec)
      --     loads frame[16..28] into local[10..13] (simp)
      --     call 3 left: wp_wasm_prop_call (IH local7.toNat hlt_left, where local7=mid from func5)
      --     call 3 right: wp_wasm_prop_call (IH local9.toNat hlt_right, where local9=n-mid from func5)
      --     call 6: wp_wasm_prop_call (func6_terminates, preconditions from func5 spec)
      --     call 7 (sorry: copy-back deferred)
      --   postamble (5 insts, simp): localGet 4 / const 32 / add / globalSet 0 / ret
      simp only [not_le] at hbase
      apply wp_wasm_prop_to_TerminatesWith (f := func3Def)
      · rfl
      · rfl
      · rfl
      · simp [Function.numParams, func3Def]
      · intro _ _ h; exact h
      -- dlmalloc_alloc_spec covers func5 (call 5 × 2); state-threading deferred
      -- hpristine supplies the pristine-allocator obligation; margin: (src_n>>>1).toNat ≤ src_n.toNat
      exact (dlmalloc_alloc_spec {} «module» st (src_n >>> 1) hpristine
          (by have h : (src_n >>> 1).toNat ≤ src_n.toNat := by
                rw [UInt32.toNat_shiftRight]; exact Nat.shiftRight_le _ _
              omega)).elim fun _ _ =>
        sorry -- TODO: state-thread alloc ptr → left IH (src_n>>>1 < src_n via hbase) → right IH → func6_terminates → copy-back (func7 deferred)

-- func1: sort with pre-allocated scratch; delegates to func3
-- allocator calls (func2, func4) deferred
-- Intended structure:
--   preamble (6 insts, simp): frame = sp-32
--   call 2 (sorry: allocator terminates: deferred per MergeSortSpec)
--   call 0 (func0 copy, straight-line, simp)
--   load frame[12] into local[3] (simp)
--   call 3: wp_wasm_prop_call (func3_terminates, sp from preamble global)
--   call 4 (sorry: allocator terminates: deferred per MergeSortSpec)
--   postamble (5 insts, simp): frame+32 / globalSet 0 / ret
private theorem func1_terminates
    (st : Store Unit) (data_ptr len : UInt32)
    (hpristine : ∀ i, i < 1050240 →
      st.mem.bytes i = («module».initialStore (α := Unit)).mem.bytes i)
    (hmargin : 1050240 + 4 * len.toNat ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 1 st
      [.i32 len, .i32 data_ptr]
      (fun st' _ =>
        (wordsAt st'.mem data_ptr len.toNat).Pairwise (· ≤ ·) ∧
        (wordsAt st'.mem data_ptr len.toNat).Perm
          (wordsAt st.mem data_ptr len.toNat)) := by
  apply wp_wasm_prop_to_TerminatesWith (f := func1Def)
  · rfl
  · rfl
  · rfl
  · simp [Function.numParams, func1Def]
  · intro _ _ h; exact h
  -- dlmalloc_alloc_spec covers func2/func4 allocator calls; state-threading deferred
  -- hpristine and hmargin directly satisfy dlmalloc's obligations
  exact (dlmalloc_alloc_spec {} «module» st len hpristine hmargin).elim fun _ _ =>
    sorry -- TODO: state-thread alloc ptr → func0 (copy, simp) → func3_terminates hpristine (derived margin) → func4 dealloc (deferred)

-- merge_sort_correct: compose func33 → func15 + func1
-- Intended structure:
--   preamble (6 insts, simp): frame = sp-16
--   const/localSet (2 insts, simp): local[3] = 1048956
--   call 15: wp_wasm_prop_call (func15_terminates, ptr=frame+8, v1=data_ptr, v2=len, v3=1048956)
--   load frame[12] → local[4] / load frame[8] (simp)
--   call 1: wp_wasm_prop_call (func1_terminates)
--   postamble (4 insts, simp): frame+16 / globalSet 0 / ret
-- sorted/perm postcondition deferred (requires func3 content correctness)
-- env bridge: «module».imports = [], run is env-independent
theorem merge_sort_correct : MergeSortSpec := by
  intro env st dataPtr len n dLo dHi hdHi hpristine hmargin
  have hpristine' : ∀ i, i < 1050240 →
      st.mem.bytes i = («module».initialStore (α := Unit)).mem.bytes i :=
    fun i hi => hpristine i (by have : heapBase = 1050240 := rfl; omega)
  have hmargin' : 1050240 + 4 * len.toNat ≤ st.mem.pages * 65536 := by
    have : heapBase = 1050240 := rfl; omega
  exact (func1_terminates st dataPtr len hpristine' hmargin').elim fun _ _ =>
    sorry -- TODO: wire func1 result into func33 via wp_wasm_prop_to_TerminatesWith for func33: preamble → func15_terminates → func1 call → postamble

end Wasm.SepLogic.MergeSort
