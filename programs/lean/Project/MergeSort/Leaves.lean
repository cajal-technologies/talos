import Project.MergeSort.Framing
import CodeLib.Entry
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Call

/-!
# Phase B — leaf function specs (split_at_mut)

`func14` is the inner store-the-two-descriptors helper of `split_at_mut`:
given `(out, ptr, len, mid)` it writes the pair of `(ptr,len)` slice
descriptors `(ptr, mid)` and `(ptr + 4*mid, len - mid)` into the 16-byte
struct at `out`. No stack frame, no calls.
-/

namespace Project.MergeSort.Leaves

open Wasm Project.MergeSort

/-- Symbolic-execution stepper for these opt-0 bodies: `wp_run`'s lemmas plus
the list/Nat/ite reductions needed to compute the concrete local frame
(`reverse`/`append`/`set`/`getElem?`/lengths) that `of_wp_entry` produces. -/
local macro "mstep" : tactic => `(tactic|
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex, Function.toLocals,
    Function.numParams, Function.numLocals, List.take, List.drop, List.replicate,
    List.length, List.map, ValueType.zero, List.headD,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.append_assoc, List.set_cons_zero, List.set_cons_succ, List.set_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte])

set_option maxRecDepth 8192 in
theorem func14_tw (env : HostEnv Unit) (st : Store Unit)
    (out ptr len mid pl : UInt32)
    (hb : out.toNat + 16 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 14 st
      [.i32 pl, .i32 mid, .i32 len, .i32 ptr, .i32 out]
      (fun st' vs => vs = [] ∧
        st' = { st with mem :=
          (((st.mem.write32 out ptr).write32 (out + 4) mid).write32
            (out + 8) (ptr + mid <<< 2)).write32 (out + 12) (len - mid) }) := by
  apply TerminatesWith.of_wp_entry_for (f := func14Def) rfl
  unfold func14Def func14
  wp_run
  simp
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  rw [UInt32.add_comm (mid <<< 2) ptr]

set_option maxRecDepth 8192 in
theorem func5_tw (env : HostEnv Unit) (st : Store Unit)
    (out ptr len mid pl sp : UInt32)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hsplit : mid.toNat ≤ len.toNat)
    (hlo : 32 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536)
    (hout : out.toNat + 16 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 5 st
      [.i32 pl, .i32 mid, .i32 len, .i32 ptr, .i32 out]
      (fun st' vs => vs = [] ∧ st'.globals = st.globals) := by
  apply TerminatesWith.of_wp_entry_for (f := func5Def) rfl
  unfold func5Def func5
  simp only [wp_simp, Locals.get, Locals.set?, Function.toLocals,
    Function.numParams, List.take, List.drop,
    List.length, List.map, ValueType.zero, hsp,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.set_cons_zero, List.set_cons_succ, List.set_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte]
  apply wp_block_cons
  mstep
  by_cases hle : mid ≤ len
  · -- guard passes: skip the panic, run split + descriptor writeback
    simp only [hle, reduceIte, UInt32.and_self]
    split
    · rename_i heq; simp at heq
    · rename_i heq
      have h32 : (32 : UInt32) ≤ sp := by
        rw [UInt32.le_iff_toNat_le, show (32 : UInt32).toNat = 32 from rfl]; omega
      have hlt : sp.toNat < 4294967296 := sp.toNat_lt
      have hsub : (sp - 32).toNat = sp.toNat - 32 := UInt32.toNat_sub_of_le sp 32 h32
      refine wp_call_tw
        (func14_tw env _ (16 + (sp - 32)) ptr len mid 1048896 ?_) ?_
      · simp only [UInt32.toNat_add, hsub, show (16 : UInt32).toNat = 16 from rfl]
        omega
      · intro st' vs hpost
        obtain ⟨rfl, rfl⟩ := hpost
        mstep
        simp only [Mem.write32_pages, Mem.write64_pages, hsub,
          show (24 : UInt32).toNat = 24 from rfl, show (16 : UInt32).toNat = 16 from rfl,
          show (8 : UInt32).toNat = 8 from rfl, show (0 : UInt32).toNat = 0 from rfl]
        split_ifs <;> try omega
        have hlen : 0 < st.globals.globals.length := by
          rcases hg : st.globals.globals with _ | ⟨a, l⟩ <;> simp_all
        have hval : (32 + (sp - 32) : UInt32) = sp := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_add, hsub, show (32 : UInt32).toNat = 32 from rfl]; omega
        rw [List.getElem?_set, if_pos rfl, if_pos hlen]
        refine ⟨trivial, ?_⟩
        have hset : st.globals.globals.set 0 (Value.i32 sp) = st.globals.globals := by
          apply List.ext_getElem?
          intro j
          rw [List.getElem?_set]
          split
          · rename_i hj; subst hj; exact hsp.symm
          · rfl
        rw [List.set_set, hval, hset]
    · rename_i h₁ h₂; exact (h₂ _ _ rfl)
  · -- guard fails: contradicts the no-panic precondition `mid ≤ len`
    exact absurd (UInt32.le_iff_toNat_le.mpr hsplit) hle

end Project.MergeSort.Leaves
