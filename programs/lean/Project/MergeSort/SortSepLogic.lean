import Project.MergeSort.MergeFull
import Project.MergeSort.ContentLemmas
import Project.MergeSort.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.AllocSpec
import CodeLib.Entry
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call
import Interpreter.Wasm.Wp.Block

namespace Wasm.SepLogic.MergeSort

open Wasm Wasm.SepLogic Project.MergeSort Project.MergeSort.Spec Project.MergeSort.Framing

variable [WasmHeapGS]

/-
call graph (imports = [], .call N = funcN):
  func33 (export "merge_sort", params: i32 i32) →
    func15 (slice-header init, straight-line) →
    func1  (sort with pre-allocated scratch) →
      func2  → func20 (vec init, allocator deferred)
      func0  (field copy, straight-line)
      func3  (recursive sort) →
        func5  (split_at_mut, func5_tw exists in Leaves.lean)
        func3  (left half, recursive)
        func3  (right half, recursive)
        func6  (merge, func6_terminates exists in MergeFull.lean)
        func7  → func13 (copy-back, func7_tw exists in Leaves.lean)
      func4  → func8, func9 (dealloc, allocator deferred)
-/

local macro "mstep" : tactic => `(tactic|
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex, Function.toLocals,
    Function.numParams, Function.numLocals, List.take, List.drop, List.replicate,
    List.length, List.map, ValueType.zero, List.headD,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.append_assoc, List.set_cons_zero, List.set_cons_succ, List.set_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte])

-- env-independence: run on an import-free module does not use the host environment
private theorem TerminatesWith.env_lift {env : HostEnv Unit} {id : Nat}
    {st : Store Unit} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : TerminatesWith {} «module» id st args P) :
    TerminatesWith env «module» id st args P := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hle => ?_⟩
  obtain ⟨vs, st', hrun, hpost⟩ := hN fuel hle
  exact ⟨vs, st',
    (run_env_indep «module» (by native_decide) fuel id st args env {}).trans hrun,
    hpost⟩

-- func15: straight-line, stores v1 at ptr, v2 at ptr+4; structural postcondition
omit [WasmHeapGS] in
private theorem func15_terminates
    (st : Store Unit) (ptr v1 v2 v3 : UInt32)
    (hb : ptr.toNat + 8 ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 15 st
      [.i32 v3, .i32 v2, .i32 v1, .i32 ptr]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (st.mem.write32 (ptr + 4) v2).write32 ptr v1 ∧
        st'.globals = st.globals) := by
  have hb4 : ¬(ptr.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    have : (4 : UInt32).toNat = 4 := rfl; omega
  have hb0 : ¬(ptr.toNat + (0 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    have : (0 : UInt32).toNat = 0 := rfl; omega
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
  · exact ⟨rfl, rfl, rfl⟩

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
    · -- base case: src_n ≤ 1, block exits via br_if 0, no calls
      have hlocals_init : List.map ValueType.zero
          [ValueType.i32, ValueType.i32, ValueType.i32, ValueType.i32, ValueType.i32,
           ValueType.i32, ValueType.i32, ValueType.i32, ValueType.i32, ValueType.i32] =
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0] := by
        native_decide
      have h_leU  : src_n ≤ (1 : UInt32) := UInt32.le_iff_toNat_le.mpr (by simpa using hbase)
      have h_and1 : (1 : UInt32) &&& 1 = 1 := by decide
      have h_br   : (1 : UInt32) ≠ 0 := by decide
      have h_plen : ((((0 : Nat) + 1) + 1) + 1) + 1 = 4 := rfl
      have h_llen : ((((((((((0 : Nat) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 10 := rfl
      have h_dset : (st.globals.globals.set 0 (.i32 (sp - 32))).set 0 (.i32 (32 + (sp - 32)))
          = st.globals.globals.set 0 (.i32 (32 + (sp - 32))) := by
        cases hg : st.globals.globals with
        | nil  => simp [hg] at hsp
        | cons hd tl => simp [List.set]
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
      · refine ⟨?_, List.Perm.refl _⟩
        simp only [wordsAt]
        have h01 : src_n.toNat = 0 ∨ src_n.toNat = 1 := by omega
        rcases h01 with h | h <;> simp [h]
    · -- recursive case: src_n > 1
      -- func3 calls: func5 (split_at_mut, func5_tw), func3 x2 (IH), func6 (func6_terminates), func7 (func7_tw)
      -- All sub-specs exist. Remaining proof work:
      --   (1) func5_tw only gives vs=[]∧globals=st.globals; loads at frame[0..12]/frame[16..28]
      --       need memory postcondition (what func5 wrote). Requires a stronger func5_tw.
      --   (2) func3_terminates needs sp_lo (32 ≤ sp.toNat) and sp_hi preconditions for func5_tw.
      --   (3) func3_terminates postcondition needs st'.globals = st.globals for IH chaining.
      --   (4) disjointness for func6_terminates is complex to derive from func5_tw memory postcondition.
      simp only [not_le] at hbase
      apply wp_wasm_prop_to_TerminatesWith (f := func3Def)
      · rfl
      · rfl
      · rfl
      · simp [Function.numParams, func3Def]
      · intro _ _ h; exact h
      sorry -- needs: (1) func5_tw with memory postcondition; (2) func3_terminates sp_lo/sp_hi preconditions; (3) globals preservation in postcondition; (4) disjointness for func6_terminates

-- func1: sort with pre-allocated scratch; delegates to func3
-- WP proof structure (once blockers below are resolved):
--   preamble (6 insts): globalGet 0 / const 32 / sub / localSet 2 / localGet 2 / globalSet 0
--   call 2 (Vec init via func20): BLOCKER (2): no TerminatesWith for func2 or func20.
--   call 0 (func0 field copy): provable via simp once func2 memory layout is known.
--   load frame[12]: scratch pointer from func2's result.
--   call 3 (func3_terminates): needs hsp' (post-preamble), hpristine, hmargin.
--   call 4 (dealloc): BLOCKER (3): no TerminatesWith for func4, func8, or func9.
--   postamble (5 insts): localGet 2 / const 32 / add / globalSet 0 / ret
private theorem func1_terminates
    (st : Store Unit) (data_ptr len : UInt32)
    (sp : UInt32)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hmargin : 1050240 + 4 * len.toNat ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 1 st
      [.i32 len, .i32 data_ptr]
      (fun st' vs =>
        vs = [] ∧
        (wordsAt st'.mem data_ptr len.toNat).Pairwise (· ≤ ·) ∧
        (wordsAt st'.mem data_ptr len.toNat).Perm
          (wordsAt st.mem data_ptr len.toNat) ∧
        st'.globals = st.globals) := by
  apply wp_wasm_prop_to_TerminatesWith (f := func1Def)
  · rfl
  · rfl
  · rfl
  · simp [Function.numParams, func1Def]
  · intro _ _ ⟨_, h1, h2, h3⟩; exact ⟨rfl, h1, h2, h3⟩
  sorry -- BLOCKED: (2) no func2/func20 TerminatesWith (Vec init); (3) no func4/func8/func9 TerminatesWith (dealloc)

-- merge_sort_correct: prove MergeSortSpec by composing func33 → func15 + func1
-- func33 instruction sequence (27 insts):
--   preamble (6): globalGet 0 / const 16 / sub / localSet 2 / localGet 2 / globalSet 0
--     → frame = sp-16 = 1048560, global[0] = 1048560
--   setup (2): const 1048956 / localSet 3 → local[3] = 1048956
--   stack-build (6): localGet 2 / const 8 / add / localGet 0 / localGet 1 / localGet 3
--     → values = [1048956, len, dataPtr, frame+8=1048568]
--   call 15: func15(ptr=1048568, v1=dataPtr, v2=len, v3=1048956)
--     → mem[1048568] = dataPtr, mem[1048572] = len
--   loads (5): localGet 2 / load32 12 / localSet 4 / localGet 2 / load32 8
--     → local[4] = len, stack has [dataPtr]
--   load/push (1): localGet 4 → stack = [len, dataPtr]
--   call 1 with [len, dataPtr]: func1_terminates → sorts dataPtr in place
--   postamble (4): localGet 2 / const 16 / add / globalSet 0 / ret
set_option maxRecDepth 100000 in
theorem merge_sort_correct : MergeSortSpec := by
  intro env st dataPtr len n dLo dHi hdHi hpristine hmargin hsp hpages
  apply TerminatesWith.env_lift
  apply TerminatesWith.of_wp_entry_for (f := func33Def) rfl
  unfold func33Def func33
  -- preamble + setup + stack build (14 insts): globalGet 0 reads hsp=1048576,
  -- sub gives frame=1048560, setup local[3]=1048956, build [1048956,len,dataPtr,1048568]
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex, Function.toLocals,
      Function.numParams, Function.numLocals, List.take, List.drop, List.replicate,
      List.length, List.map, ValueType.zero, List.headD,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc, List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, hsp,
      show (1048576 : UInt32) - 16 = 1048560 from rfl,
      show (1048560 : UInt32) + 8 = 1048568 from rfl,
      show (1048560 : UInt32) + 16 = 1048576 from rfl]
  -- call 15: store dataPtr at frame+8=1048568, len at frame+12=1048572
  have hb15 : (1048568 : UInt32).toNat + 8 ≤ st.mem.pages * 65536 := by
    simp only [show (1048568 : UInt32).toNat = 1048568 from rfl]
    have := hdHi; have : heapBase = 1050240 := rfl; omega
  -- call 15 is invoked on the post-preamble store (globals[0]=1048560, mem=st.mem)
  let stP : Store Unit := { st with globals := { globals := st.globals.globals.set 0 (.i32 1048560) } }
  refine wp_call_tw (func15_terminates stP 1048568 dataPtr len 1048956 hb15) ?_
  intro st15 vs15 hpost15
  obtain ⟨rfl, hmem15, hglobals15⟩ := hpost15
  -- hmem15   : st15.mem = (stP.mem.write32 1048572 len).write32 1048568 dataPtr
  --          = (st.mem.write32 1048572 len).write32 1048568 dataPtr  (stP.mem = st.mem by rfl)
  -- hglobals15 : st15.globals = stP.globals = { globals := st.globals.globals.set 0 (.i32 1048560) }
  have hmem8 : st15.mem.read32 1048568 = dataPtr := by
    rw [hmem15]; exact Mem.read32_write32_same _ _ _
  have hmem12 : st15.mem.read32 1048572 = len := by
    rw [hmem15]
    rw [Mem.read32_write32_of_disjoint _ 1048568 1048572 dataPtr
        (Or.inl (by native_decide))]
    exact Mem.read32_write32_same _ _ _
  -- stP.mem = st.mem definitionally; use omega on Nat witnesses to avoid rfl recursion
  have hstP_pages : stP.mem.pages = st.mem.pages := by
    change ({ st with globals := { globals := st.globals.globals.set 0 (.i32 1048560) } } : Store Unit).mem.pages = st.mem.pages
    rfl
  have hstP_mem : stP.mem = st.mem := by
    change ({ st with globals := { globals := st.globals.globals.set 0 (.i32 1048560) } } : Store Unit).mem = st.mem
    rfl
  have hstP_gl : stP.globals.globals = st.globals.globals.set 0 (.i32 1048560) := by
    change ({ st with globals := { globals := st.globals.globals.set 0 (.i32 1048560) } } : Store Unit).globals.globals = st.globals.globals.set 0 (.i32 1048560)
    rfl
  have hpages15 : st15.mem.pages = st.mem.pages := by
    have h1 : st15.mem.pages = stP.mem.pages := by
      rw [hmem15]; simp only [Mem.write32_pages]
    exact h1.trans hstP_pages
  have hbnd12 : ¬((1048560 : UInt32).toNat + (12 : UInt32).toNat + 4 > st15.mem.pages * 65536) := by
    simp only [show (1048560 : UInt32).toNat = 1048560 from rfl,
               show (12 : UInt32).toNat = 12 from rfl, hpages15]
    have := hdHi; have : heapBase = 1050240 := rfl; omega
  have hbnd8 : ¬((1048560 : UInt32).toNat + (8 : UInt32).toNat + 4 > st15.mem.pages * 65536) := by
    simp only [show (1048560 : UInt32).toNat = 1048560 from rfl,
               show (8 : UInt32).toNat = 8 from rfl, hpages15]
    clear hbnd12
    have := hdHi; have : heapBase = 1050240 := rfl; omega
  -- mid 6 insts: localGet 2, load32 12, localSet 4, localGet 2, load32 8, localGet 4
  -- mstep reduces localGet 2, then wp_load32_cons fires but stalls on the if (abstract pages)
  mstep
  -- resolve load32 12 bounds-if; simp continues through localSet 4, localGet 2, stalls at load32 8 if
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      if_neg hbnd12,
      show (1048560 : UInt32) + 12 = 1048572 from rfl,
      hmem12]
  -- resolve load32 8 bounds-if; simp continues through localGet 4, stops at .call 1
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      if_neg hbnd8,
      show (1048560 : UInt32) + 8 = 1048568 from rfl,
      hmem8]
  -- call 1: sort dataPtr in place; needs hsp1 (global[0] = frame = 1048560)
  have hsp1 : st15.globals.globals[0]? = some (.i32 1048560) := by
    rw [hglobals15]
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl => simp only [hstP_gl, hg, List.set_cons_zero, List.getElem?_cons_zero]
  have hmargin1 : 1050240 + 4 * len.toNat ≤ st15.mem.pages * 65536 := by
    rw [hpages15]; have := hdHi; have : heapBase = 1050240 := rfl; omega
  refine wp_call_tw (func1_terminates st15 dataPtr len 1048560 hsp1 hmargin1) ?_
  intro st1 vs1 hpost1
  obtain ⟨rfl, hsorted, hperm1, hglobals1⟩ := hpost1
  -- postamble (4 insts): localGet 2 / const 16 / add / globalSet 0 / ret
  -- globalSet 0 needs to know current global[0] value
  have hsp_post : st1.globals.globals[0]? = some (.i32 1048560) := by
    rw [hglobals1, hglobals15]
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl => simp only [hstP_gl, hg, List.set_cons_zero, List.getElem?_cons_zero]
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      hsp_post,
      show (1048560 : UInt32) + 16 = 1048576 from rfl]
  -- postcondition: rs=[], sorted, perm
  refine ⟨trivial, hsorted, ?_⟩
  -- perm: (wordsAt st1.mem dataPtr n).Perm (wordsAt st.mem dataPtr n)
  -- via hperm1 and wordsAt st15.mem = wordsAt st.mem (func15 only wrote at 1048568/1048572 < dataPtr)
  have hub : dataPtr.toNat + 4 * n ≤ 4294967296 := by have := hpages; have := hdHi; omega
  have hmem_eq : wordsAt st15.mem dataPtr n = wordsAt st.mem dataPtr n := by
    rw [hmem15, show (1048568 : UInt32) + 4 = 1048572 from rfl]
    rw [wordsAt_write32_of_disjoint _ dataPtr 1048568 dataPtr n hub
        (Or.inl (by simp only [show (1048568 : UInt32).toNat = 1048568 from rfl]
                    have := hmargin; have : heapBase = 1050240 := rfl; omega))]
    rw [wordsAt_write32_of_disjoint _ dataPtr 1048572 len n hub
        (Or.inl (by simp only [show (1048572 : UInt32).toNat = 1048572 from rfl]
                    have := hmargin; have : heapBase = 1050240 := rfl; omega))]
  exact hperm1.trans (hmem_eq ▸ List.Perm.refl _)

end Wasm.SepLogic.MergeSort
