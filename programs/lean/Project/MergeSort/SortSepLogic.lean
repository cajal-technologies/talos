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

-- func3: recursive merge sort (axiomatized; inductive proof deferred)
-- sp parameter required: globalGet 0 reads the stack pointer from global 0
private axiom func3_terminates
    (st : Store Unit) (src_ptr src_n dst_ptr dst_n sp : UInt32)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hsp_lo : 32 * (Nat.log 2 src_n.toNat + 2) ≤ sp.toNat)
    (hpages : st.mem.pages * 65536 ≤ 4294967296)
    (hmargin : 1050240 + 4 * src_n.toNat ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 3 st
      [.i32 dst_n, .i32 dst_ptr, .i32 src_n, .i32 src_ptr]
      (fun st' vs =>
        vs = [] ∧
        (wordsAt st'.mem src_ptr src_n.toNat).Pairwise (· ≤ ·) ∧
        (wordsAt st'.mem src_ptr src_n.toNat).Perm
          (wordsAt st.mem src_ptr src_n.toNat) ∧
        st'.globals = st.globals)

-- func2: Vec::with_capacity (deferred allocator proof; axiomatized)
private axiom func2_vec_init
    (st : Store Unit) (out_ptr len : UInt32)
    (hmargin : 1050240 + 4 * len.toNat ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 2 st
      [.i32 len, .i32 0, .i32 out_ptr]
      (fun st' rs =>
        rs = [] ∧
        ∃ heap_ptr : UInt32,
          heap_ptr.toNat = 1050240 ∧
          heap_ptr.toNat + 4 * len.toNat ≤ st'.mem.pages * 65536 ∧
          st'.mem.pages * 65536 ≤ 4294967296 ∧
          st.mem.pages ≤ st'.mem.pages ∧
          st'.globals = st.globals ∧
          st'.mem.read32 (out_ptr + 4) = heap_ptr ∧
          st'.mem.read32 (out_ptr + 8) = len ∧
          ∀ i, i ≥ 1050240 + 4 * len.toNat → st'.mem.bytes i = st.mem.bytes i)

-- func4: Vec dealloc (deferred allocator proof; axiomatized)
private axiom func4_dealloc
    (st : Store Unit) (vec_ptr heap_ptr : UInt32) (cap_bytes : Nat) :
    TerminatesWith {} «module» 4 st [.i32 vec_ptr]
      (fun st' rs =>
        rs = [] ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages ∧
        ∀ i, i ≥ heap_ptr.toNat + cap_bytes → st'.mem.bytes i = st.mem.bytes i)

-- func0: straight-line field copy (11 insts, no subcalls)
set_option maxRecDepth 100000 in
omit [WasmHeapGS] in
private theorem func0_tw
    (st : Store Unit) (dst src : UInt32)
    (hb1 : ¬(src.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536))
    (hb2 : ¬(src.toNat + (8 : UInt32).toNat + 4 > st.mem.pages * 65536))
    (hb3 : ¬(dst.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536))
    (hb4 : ¬(dst.toNat + (0 : UInt32).toNat + 4 > st.mem.pages * 65536)) :
    TerminatesWith {} «module» 0 st [.i32 src, .i32 dst]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (st.mem.write32 (dst + 4) (st.mem.read32 (src + 8))).write32 dst
            (st.mem.read32 (src + 4)) ∧
        st'.globals = st.globals) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  unfold func0Def func0
  -- localGet 1 → push src; stop before load32 4
  mstep
  -- load32 4 (src+4, bound hb1), localSet 2, localGet 0, localGet 1; stop before load32 8
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex, Function.toLocals,
      Function.numParams, Function.numLocals, List.take, List.drop, List.replicate,
      List.length, List.map, ValueType.zero, List.headD,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc, List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, if_neg hb1]
  -- load32 8 (src+8, bound hb2), store32 4 (dst+4, bound hb3), localGet 0, localGet 2; stop before store32 0
  simp only [wp_simp, Locals.get, Locals.set?, Mem.write32_pages,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, if_neg hb2, if_neg hb3]
  -- store32 0 (dst, bound hb4), ret
  simp only [wp_simp, Locals.get, Locals.set?, Mem.write32_pages,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, if_neg hb4]
  refine ⟨trivial, ?_, trivial⟩
  rw [show (dst + (0 : UInt32)) = dst from UInt32.add_zero dst]

-- func1: sort with pre-allocated scratch; delegates to func3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem func1_terminates
    (st : Store Unit) (data_ptr len : UInt32)
    (sp : UInt32)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hsp_lo : 32 * (Nat.log 2 len.toNat + 2) + 32 ≤ sp.toNat)
    (hsp_hi : sp.toNat ≤ 1048576)
    (hpages : st.mem.pages * 65536 ≤ 4294967296)
    (hmargin : 1050240 + 4 * len.toNat ≤ st.mem.pages * 65536)
    (hdHi : data_ptr.toNat + 4 * len.toNat ≤ st.mem.pages * 65536)
    (hdata_lo : 1050240 + 4 * len.toNat ≤ data_ptr.toNat) :
    TerminatesWith {} «module» 1 st
      [.i32 len, .i32 data_ptr]
      (fun st' vs =>
        vs = [] ∧
        (wordsAt st'.mem data_ptr len.toNat).Pairwise (· ≤ ·) ∧
        (wordsAt st'.mem data_ptr len.toNat).Perm
          (wordsAt st.mem data_ptr len.toNat) ∧
        st'.globals = st.globals) := by
  set frame := sp - (32 : UInt32) with hframe_def
  have hsp_lo_ge : 32 ≤ sp.toNat := by linarith
  have hframe32 : frame + (32 : UInt32) = sp := by
    apply UInt32.toNat.inj
    rw [hframe_def]
    simp only [UInt32.toNat_add, UInt32.toNat_sub, show (32:UInt32).toNat = 32 from rfl]
    have hlt : sp.toNat < 4294967296 := UInt32.toNat_lt_size sp
    omega
  have hframe_nat : frame.toNat = sp.toNat - 32 := by
    have hconv := congrArg UInt32.toNat hframe32
    simp only [UInt32.toNat_add, show (32:UInt32).toNat = 32 from rfl] at hconv
    have hlt_f : frame.toNat < 4294967296 := UInt32.toNat_lt_size frame
    omega
  have hglob_set_frame : (st.globals.globals.set 0 (.i32 frame))[0]? = some (.i32 frame) := by
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl => simp [hg, List.set_cons_zero]
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  -- preamble: globalGet 0, const 32, sub, localSet 2, localGet 2, globalSet 0
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex, Function.toLocals,
      Function.numParams, Function.numLocals, List.take, List.drop, List.replicate,
      List.length, List.map, ValueType.zero, List.headD,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc, List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      hsp, show sp - (32 : UInt32) = frame from hframe_def.symm]
  simp only [show (20 : UInt32) + frame = frame + 20 from UInt32.add_comm 20 frame]
  -- call 2: func2_vec_init  (out_ptr = frame+20, args = [len, 0, frame+20])
  refine wp_call_tw (func2_vec_init { st with globals := { globals := st.globals.globals.set 0 (.i32 frame) } } (frame + 20) len hmargin) ?_
  intro st2 _ hpost2
  obtain ⟨rfl, heap_ptr, hheap_nat, hheap_cap, hpages2, hpages_mono, hglob2, hmem2_r4, hmem2_r8, hmem2_bytes⟩ := hpost2
  have hpages2_frame : sp.toNat ≤ st2.mem.pages * 65536 := by
    have h1 : sp.toNat ≤ 1050240 := by omega
    have h2 : 1050240 ≤ 1050240 + 4 * len.toNat := by omega
    omega
  -- bounds for func0_tw (dst = frame+8, src = frame+20)
  have hlt_f : frame.toNat < 4294967296 := UInt32.toNat_lt_size frame
  have hfb : frame.toNat ≤ 1048544 := by clear hsp_lo; omega
  have hbf0_1 : ¬((frame + 20).toNat + (4 : UInt32).toNat + 4 > st2.mem.pages * 65536) := by
    simp only [UInt32.toNat_add, show (20 : UInt32).toNat = 20 from rfl,
               show (4 : UInt32).toNat = 4 from rfl]; omega
  have hbf0_2 : ¬((frame + 20).toNat + (8 : UInt32).toNat + 4 > st2.mem.pages * 65536) := by
    simp only [UInt32.toNat_add, show (20 : UInt32).toNat = 20 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have hbf0_3 : ¬((frame + 8).toNat + (4 : UInt32).toNat + 4 > st2.mem.pages * 65536) := by
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
               show (4 : UInt32).toNat = 4 from rfl]; omega
  have hbf0_4 : ¬((frame + 8).toNat + (0 : UInt32).toNat + 4 > st2.mem.pages * 65536) := by
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
               show (0 : UInt32).toNat = 0 from rfl]; omega
  -- reduce: localGet 2, const 8, add, localGet 2, const 20, add  (before call 0)
  mstep
  simp only [show (8 : UInt32) + frame = frame + 8 from UInt32.add_comm 8 frame,
             show (20 : UInt32) + frame = frame + 20 from UInt32.add_comm 20 frame]
  -- call 0: func0_tw  (dst = frame+8, src = frame+20)
  refine wp_call_tw (func0_tw st2 (frame + 8) (frame + 20) hbf0_1 hbf0_2 hbf0_3 hbf0_4) ?_
  intro st0 _ hpost0
  obtain ⟨rfl, hmem0_eq, hglob0⟩ := hpost0
  -- simplify func0's memory result
  have hmem0_simp : st0.mem =
      (st2.mem.write32 (frame + 12) len).write32 (frame + 8) heap_ptr := by
    rw [hmem0_eq, show (frame + 8 : UInt32) + 4 = frame + 12 from by rw [UInt32.add_assoc]; rfl,
        hmem2_r8, hmem2_r4]
  have hmem0_r12 : st0.mem.read32 (frame + 12) = len := by
    rw [hmem0_simp]
    rw [Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 12) heap_ptr
        (Or.inl (by
          simp only [UInt32.toNat_add, show (8:UInt32).toNat = 8 from rfl,
                     show (12:UInt32).toNat = 12 from rfl]; omega))]
    exact Mem.read32_write32_same _ _ _
  have hmem0_r8 : st0.mem.read32 (frame + 8) = heap_ptr := by
    rw [hmem0_simp]; exact Mem.read32_write32_same _ _ _
  have hpages0 : st0.mem.pages = st2.mem.pages := by
    rw [hmem0_simp, Mem.write32_pages, Mem.write32_pages]
  have hpages0_le : 1050240 + 4 * len.toNat ≤ st0.mem.pages * 65536 := by
    rw [hpages0]; linarith [hheap_nat ▸ hheap_cap]
  have hbnd12 : ¬(frame.toNat + (12 : UInt32).toNat + 4 > st0.mem.pages * 65536) := by
    have h12 : (12 : UInt32).toNat = 12 := rfl; rw [h12]; linarith [hfb, hpages0_le]
  have hbnd8 : ¬(frame.toNat + (8 : UInt32).toNat + 4 > st0.mem.pages * 65536) := by
    have h8 : (8 : UInt32).toNat = 8 := rfl; rw [h8]; linarith [hfb, hpages0_le]
  -- globals chain: st0.globals = st2.globals = preamble_store.globals
  have hglob_f0 : st0.globals.globals[0]? = some (.i32 frame) := by
    have e0 : st0.globals.globals = st2.globals.globals := congrArg Globals.globals hglob0
    have e2 : st2.globals.globals = st.globals.globals.set 0 (.i32 frame) := by
      have := congrArg Globals.globals hglob2
      simp only [this]
    rw [e0, e2]; exact hglob_set_frame
  -- induction hypothesis for func3
  have hsp_lo_f3 : 32 * (Nat.log 2 len.toNat + 2) ≤ frame.toNat := by
    rw [hframe_nat]
    linarith [hsp_lo, Nat.sub_add_cancel hsp_lo_ge]
  have hpages0_h : st0.mem.pages * 65536 ≤ 4294967296 := by rw [hpages0]; exact hpages2
  -- reduce: localGet 2, load32 12; first simp also consumes localSet3/localGet0/1/2
  mstep
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      if_neg hbnd12, hmem0_r12]
  -- at load32 8; simp also consumes localGet 3
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      if_neg hbnd8, hmem0_r8]
  -- call 3: func3_terminates  (src_ptr=data_ptr, src_n=len, dst_ptr=heap_ptr, dst_n=len, sp=frame)
  refine wp_call_tw (func3_terminates st0 data_ptr len heap_ptr len frame
      hglob_f0 hsp_lo_f3 hpages0_h hpages0_le) ?_
  intro st3 _ hpost3
  obtain ⟨rfl, hsorted3, hperm3, hglob3⟩ := hpost3
  -- reduce: localGet 2, const 20, add  (before call 4)
  mstep
  simp only [show (20 : UInt32) + frame = frame + 20 from UInt32.add_comm 20 frame]
  -- call 4: func4_dealloc  (vec_ptr = frame+20)
  refine wp_call_tw (func4_dealloc st3 (frame + 20) (1050240 : UInt32) (4 * len.toNat)) ?_
  intro st4 _ hpost4
  obtain ⟨rfl, hglob4, hpages4_eq, hbytes4⟩ := hpost4
  -- globals chain: st4.globals.globals = st.globals.globals.set 0 (.i32 frame)
  have hchain : st4.globals.globals = st.globals.globals.set 0 (.i32 frame) := by
    have e4 : st4.globals.globals = st3.globals.globals := congrArg Globals.globals hglob4
    have e3 : st3.globals.globals = st0.globals.globals := congrArg Globals.globals hglob3
    have e0 : st0.globals.globals = st2.globals.globals := congrArg Globals.globals hglob0
    have e2 : st2.globals.globals = st.globals.globals.set 0 (.i32 frame) := by
      have := congrArg Globals.globals hglob2
      simp only [this]
    simp only [e4, e3, e0, e2]
  have hglob_f4 : st4.globals.globals[0]? = some (.i32 frame) := by
    rw [hchain]; exact hglob_set_frame
  -- postamble: localGet 2, const 32, add, globalSet 0, ret
  mstep
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      hglob_f4, show (32:UInt32) + frame = sp from by rw [UInt32.add_comm]; exact hframe32,
      List.take_zero]
  -- postcondition: vs=[], sorted, perm, globals
  have hub : data_ptr.toNat + 4 * len.toNat ≤ 4294967296 := by linarith [hpages]
  have hwa4_eq : wordsAt st4.mem data_ptr len.toNat = wordsAt st3.mem data_ptr len.toNat := by
    apply wordsAt_congr_of_bytes _ _ _ _ hub
    intro i hlo hhi
    apply hbytes4 i
    simp only [show (1050240 : UInt32).toNat = 1050240 from rfl]; omega
  have hwa0_eq : wordsAt st0.mem data_ptr len.toNat = wordsAt st.mem data_ptr len.toNat := by
    rw [hmem0_simp]
    rw [wordsAt_write32_of_disjoint _ data_ptr (frame + 8) heap_ptr len.toNat hub
        (Or.inl (by
          have hf8 : (frame + (8:UInt32)).toNat = frame.toNat + 8 := by
            simp only [UInt32.toNat_add, show (8:UInt32).toNat = 8 from rfl]
            apply Nat.mod_eq_of_lt; linarith [hfb]
          linarith [hfb, hdata_lo, hf8]))]
    rw [wordsAt_write32_of_disjoint _ data_ptr (frame + 12) len len.toNat hub
        (Or.inl (by
          have hf12 : (frame + (12:UInt32)).toNat = frame.toNat + 12 := by
            simp only [UInt32.toNat_add, show (12:UInt32).toNat = 12 from rfl]
            apply Nat.mod_eq_of_lt; linarith [hfb]
          linarith [hfb, hdata_lo, hf12]))]
    apply wordsAt_congr_of_bytes _ _ _ _ hub
    intro i hlo hhi
    exact hmem2_bytes i (by linarith [hdata_lo])
  -- globals preservation: set frame then set sp = no-op (sp = st.globals[0])
  have h_globals_id : st.globals.globals.set 0 (.i32 sp) = st.globals.globals := by
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl =>
      obtain rfl : hd = .i32 sp := by simpa [hg] using hsp
      simp [hg, List.set_cons_zero]
  refine ⟨trivial, ?hsorted, ?hperm, ?hglob⟩
  · -- sorted: wordsAt st4'.mem = wordsAt st4.mem (globalSet doesn't change mem)
    rw [hwa4_eq]; exact hsorted3
  · -- perm: chain through func3 and memory equalities
    rw [hwa4_eq, ← hwa0_eq]; exact hperm3
  · -- globals: { globals := st4.globals.globals.set 0 (.i32 sp) } = st.globals
    show { globals := st4.globals.globals.set 0 (.i32 sp) } = st.globals
    rw [hchain]
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl =>
      obtain rfl : hd = .i32 sp := by simpa [hg] using hsp
      simp only [List.set_cons_zero]
      rw [← hg]

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
  have hsp_lo1 : 32 * (Nat.log 2 len.toNat + 2) + 32 ≤ (1048560 : UInt32).toNat := by
    simp only [show (1048560 : UInt32).toNat = 1048560 from rfl]
    have hlen_lt : n < 4294967296 := by
      have h1 : heapBase + 4 * n ≤ dLo := hmargin
      have h2 : dLo + 4 * n ≤ st.mem.pages * 65536 := hdHi
      simp only [show heapBase = 1050240 from rfl] at h1; linarith [hpages]
    have hlog : Nat.log 2 len.toNat ≤ 31 := by
      have hle : len.toNat ≤ 4294967295 := by omega
      calc Nat.log 2 len.toNat ≤ Nat.log 2 4294967295 := Nat.log_mono_right hle
        _ = 31 := by native_decide
    omega
  have hsp_hi1 : (1048560 : UInt32).toNat ≤ 1048576 := by native_decide
  have hpages1 : st15.mem.pages * 65536 ≤ 4294967296 := by rw [hpages15]; exact hpages
  have hdHi1 : dataPtr.toNat + 4 * len.toNat ≤ st15.mem.pages * 65536 := by
    rw [hpages15]; exact hdHi
  have hdata_lo1 : 1050240 + 4 * len.toNat ≤ dataPtr.toNat := by
    have : heapBase = 1050240 := rfl; linarith [hmargin]
  refine wp_call_tw (func1_terminates st15 dataPtr len 1048560 hsp1 hsp_lo1 hsp_hi1 hpages1
      hmargin1 hdHi1 hdata_lo1) ?_
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
