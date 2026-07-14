import Project.Encode.Program
import CodeLib
import Interpreter.Wasm.Wp.Call

/-!
# Proof of `EncodeSpec` (in progress)

General total-correctness proof of `encode`, built bottom-up like `gcd_u64`:
`encode` (func 8) → `encode::encode` (func 7) → `<[T]>::to_vec` (func 1) →
`ConvertVec::to_vec` (func 2, the `Vec` build + `memory.copy`) → `with_capacity_in`
(func 6) → … → `dlmalloc::malloc` (func 29).

Everything above `func6` is loop-free; the allocator (`func6` downward) has the
loops and is discharged separately. This file lands the loop-free layers.
-/

namespace Project.Encode.Proofs

open Wasm Project.Encode

/-- The exported `encode` (func 8) loads the `&str` fields `(dataPtr, len)` from
the argument struct at `argPtr` and forwards to the pure `encode::encode`
(func 7). So whatever post `func7` guarantees, the export guarantees — given the
struct is readable at `argPtr`. -/
theorem func8_of_func7 (env : HostEnv Unit) (st : Store Unit)
    (retPtr argPtr dataPtr len : UInt32) (P : Store Unit → Prop)
    (hdata : st.mem.read32 argPtr = dataPtr)
    (hlen : st.mem.read32 (argPtr + 4) = len)
    (hb : argPtr.toNat + 8 ≤ st.mem.pages * 65536)
    (hf7 : TerminatesWith env «module» 7 st [.i32 len, .i32 dataPtr, .i32 retPtr]
             (fun st' _ => P st')) :
    TerminatesWith env «module» 8 st [.i32 argPtr, .i32 retPtr] (fun st' _ => P st') := by
  apply TerminatesWith.of_wp_entry_for (f := func8Def) rfl
  unfold func8Def func8
  wp_run
  simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    show UInt32.toNat 0 = 0 from rfl, show UInt32.toNat 4 = 4 from rfl, Nat.add_zero]
  simp only [show argPtr + (0 : UInt32) = argPtr from by simp, hdata, hlen]
  rw [if_neg (by omega), if_neg (by omega)]
  apply wp_call_tw hf7
  intro st' vs hP
  wp_run
  exact hP

/-- `encode::encode` (func 7) is a thin pass-through to `<[T]>::to_vec` (func 1). -/
theorem func7_of_func1 (env : HostEnv Unit) (st : Store Unit)
    (sret dataPtr len : UInt32) (P : Store Unit → Prop)
    (hf1 : TerminatesWith env «module» 1 st [.i32 len, .i32 dataPtr, .i32 sret]
             (fun st' _ => P st')) :
    TerminatesWith env «module» 7 st [.i32 len, .i32 dataPtr, .i32 sret]
      (fun st' _ => P st') := by
  apply TerminatesWith.of_wp_entry_for (f := func7Def) rfl
  unfold func7Def func7
  wp_run
  apply wp_call_tw hf1
  intro st' vs hP
  wp_run
  exact hP

/-- `<[T]>::to_vec` (func 1) is a thin pass-through to `ConvertVec::to_vec` (func 2). -/
theorem func1_of_func2 (env : HostEnv Unit) (st : Store Unit)
    (sret dataPtr len : UInt32) (P : Store Unit → Prop)
    (hf2 : TerminatesWith env «module» 2 st [.i32 len, .i32 dataPtr, .i32 sret]
             (fun st' _ => P st')) :
    TerminatesWith env «module» 1 st [.i32 len, .i32 dataPtr, .i32 sret]
      (fun st' _ => P st') := by
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  apply wp_call_tw hf2
  intro st' vs hP
  wp_run
  exact hP

/-- `ConvertVec::to_vec` (func 2): the heart — allocate via `with_capacity_in`
(func 6, isolated as the contract `hcap`), write the `Vec` header `{cap, ptr, 0}`
at `sret`, then `memory.copy` the input into the fresh buffer `ptr` and set the
length. Given the allocator returns a buffer disjoint from the input and the
return slot, the buffer ends up holding a byte-for-byte copy of the input. -/
theorem func2_terminates (env : HostEnv Unit) (st : Store Unit)
    (sret dataPtr len sp cap ptr : UInt32)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hcap : TerminatesWith env «module» 6
      { st with globals := { globals := st.globals.globals.set 0 (.i32 (sp - 16)) } }
      [.i32 1, .i32 1, .i32 len, .i32 (8 + (sp - 16))]
      (fun s6 vs6 => vs6 = []
        ∧ s6.globals.globals[0]? = some (.i32 (sp - 16))
        ∧ s6.mem.pages ≤ 65536
        ∧ (sp - 16).toNat + 16 ≤ s6.mem.pages * 65536
        ∧ s6.mem.read32 (sp - 16 + 8) = cap
        ∧ s6.mem.read32 (sp - 16 + 12) = ptr
        ∧ ptr.toNat + len.toNat ≤ s6.mem.pages * 65536
        ∧ dataPtr.toNat + len.toNat ≤ s6.mem.pages * 65536
        ∧ sret.toNat + 12 ≤ s6.mem.pages * 65536
        ∧ (ptr.toNat + len.toNat ≤ dataPtr.toNat ∨ dataPtr.toNat + len.toNat ≤ ptr.toNat)
        ∧ (ptr.toNat + len.toNat ≤ sret.toNat ∨ sret.toNat + 12 ≤ ptr.toNat)
        ∧ (∀ k : UInt32, k.toNat < len.toNat →
             s6.mem.read8 (dataPtr + k) = st.mem.read8 (dataPtr + k))))
    (hsd : sret.toNat + 12 ≤ dataPtr.toNat ∨ dataPtr.toNat + len.toNat ≤ sret.toNat) :
    TerminatesWith env «module» 2 st [.i32 len, .i32 dataPtr, .i32 sret]
      (fun st' vs => vs = []
        ∧ st'.mem.read32 (sret + 8) = len
        ∧ st'.mem.read32 (sret + 4) = ptr
        ∧ ∀ k : UInt32, k.toNat < len.toNat →
            st'.mem.read8 (ptr + k) = st.mem.read8 (dataPtr + k)) := by
  apply TerminatesWith.of_wp_entry_for (f := func2Def) rfl
  unfold func2Def func2
  wp_run
  rw [hsp]
  simp
  apply wp_call_tw hcap
  rintro s6 vs6 ⟨rfl, hglob6, hpg, hframe, hc8, hp12, hpbound, hdbound, hsbound,
    hdisj_d, hdisj_s, hpres⟩
  have e4 : (sret + 4).toNat = sret.toNat + 4 := by
    rw [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; simp only [Nat.reducePow]; omega
  have e8 : (sret + 8).toNat = sret.toNat + 8 := by
    rw [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl]; simp only [Nat.reducePow]; omega
  wp_run
  simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ, List.getElem?_nil,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, Mem.write32_pages,
    show UInt32.toNat 0 = 0 from rfl, show UInt32.toNat 4 = 4 from rfl,
    show UInt32.toNat 8 = 8 from rfl, show UInt32.toNat 12 = 12 from rfl, hp12, hc8]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  apply wp_block_cons
  by_cases hlen : len = 0
  · subst hlen
    wp_run
    simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, show UInt32.toNat 0 = 0 from rfl,
      hglob6, gt_iff_lt, Nat.lt_irrefl]
    rw [show (if ((1 : UInt32) &&& if (0 : UInt32) < 0 then 1 else 0) = 0 then (1 : UInt32) else 0)
          = 1 from by decide]
    refine ⟨Mem.read32_write32_same _ _ _, ?_, ?_⟩
    · rw [Mem.read32_write32_disjoint _ (sret + 4) (sret + 8) 0 (by rw [e4, e8]; omega)]
      exact Mem.read32_write32_same _ _ _
    · intro k hk; exact absurd hk (Nat.not_lt_zero _)
  · -- len > 0: the guard passes, run the memory.copy
    have hpos : (0 : UInt32) < len := by
      have h2 : 0 < len.toNat := by
        rcases Nat.eq_zero_or_pos len.toNat with hz | hp
        · exact absurd (by rw [← UInt32.toNat_inj]; simpa using hz) hlen
        · exact hp
      exact UInt32.lt_iff_toNat_lt.mpr (by simpa using h2)
    wp_run
    simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, hpos, hglob6, Mem.write32_pages,
      show UInt32.toNat 4 = 4 from rfl]
    rw [if_neg (show ¬ ((1 : UInt32) &&& 1 = 0) from by decide)]
    simp only [reduceIte]
    rw [if_neg (by omega)]
    have hdst : (((s6.mem.write32 (sret + 0) cap).write32 (sret + 4) ptr).write32 (sret + 8) 0).read32
        (sret + 4) = ptr := by
      rw [Mem.read32_write32_disjoint _ (sret + 4) (sret + 8) 0 (by rw [e4, e8]; omega),
        Mem.read32_write32_same]
    rw [hdst]
    apply wp_block_cons
    wp_run
    simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, hdst, hglob6, Mem.copy_pages,
      Mem.write32_pages, hlen, show UInt32.toNat 8 = 8 from rfl,
      show len <<< (0 % 32) = len from by simp]
    rw [if_neg (by omega), if_neg (by omega)]
    refine ⟨Mem.read32_write32_same _ _ _, ?_, ?_⟩
    · rw [Mem.read32_write32_disjoint _ (sret + 4) (sret + 8) len (by rw [e4, e8]; omega),
        Mem.read32_copy_outside _ ptr.toNat dataPtr.toNat len.toNat (sret + 4) (by rw [e4]; omega)]
      exact hdst
    · intro k hk
      have ek : (ptr + k).toNat = ptr.toNat + k.toNat := by
        rw [UInt32.toNat_add]; simp only [Nat.reducePow]; omega
      have edk : (dataPtr + k).toNat = dataPtr.toNat + k.toNat := by
        rw [UInt32.toNat_add]; simp only [Nat.reducePow]; omega
      have hs0 : (sret + 0).toNat = sret.toNat := by simp
      have hbyte : (((s6.mem.write32 (sret + 0) cap).write32 (sret + 4) ptr).write32 (sret + 8) 0).read8
          (dataPtr + k) = st.mem.read8 (dataPtr + k) := by
        rw [Mem.read8_write32_disjoint _ (dataPtr + k) (sret + 8) 0 (by rw [edk, e8]; omega),
          Mem.read8_write32_disjoint _ (dataPtr + k) (sret + 4) ptr (by rw [edk, e4]; omega),
          Mem.read8_write32_disjoint _ (dataPtr + k) (sret + 0) cap (by rw [edk, hs0]; omega)]
        exact hpres k hk
      rw [Mem.read8_write32_disjoint _ (ptr + k) (sret + 8) len (by rw [ek, e8]; omega),
        Mem.read8_copy_inside _ ptr.toNat dataPtr.toNat len.toNat (ptr + k) (by rw [ek]; omega),
        show dataPtr.toNat + ((ptr + k).toNat - ptr.toNat) = (dataPtr + k).toNat
          from by rw [ek, edk]; omega]
      exact hbyte

/-- **Encode is correct for all inputs, modulo the allocator.** Composing the
four loop-free layers, the exported `encode` (func 8) — given the
`with_capacity_in`/allocator contract `hcap` — terminates writing a `Vec<u8>`
whose length is the input length and whose buffer holds a byte-for-byte copy of
the input string. The only remaining obligation for an unconditional `EncodeSpec`
is discharging `hcap` (the `dlmalloc` frontier). -/
theorem encode_of_alloc (env : HostEnv Unit) (st : Store Unit)
    (retPtr argPtr dataPtr len sp cap ptr : UInt32)
    (hdata : st.mem.read32 argPtr = dataPtr)
    (hlen : st.mem.read32 (argPtr + 4) = len)
    (hb : argPtr.toNat + 8 ≤ st.mem.pages * 65536)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hcap : TerminatesWith env «module» 6
      { st with globals := { globals := st.globals.globals.set 0 (.i32 (sp - 16)) } }
      [.i32 1, .i32 1, .i32 len, .i32 (8 + (sp - 16))]
      (fun s6 vs6 => vs6 = []
        ∧ s6.globals.globals[0]? = some (.i32 (sp - 16))
        ∧ s6.mem.pages ≤ 65536
        ∧ (sp - 16).toNat + 16 ≤ s6.mem.pages * 65536
        ∧ s6.mem.read32 (sp - 16 + 8) = cap
        ∧ s6.mem.read32 (sp - 16 + 12) = ptr
        ∧ ptr.toNat + len.toNat ≤ s6.mem.pages * 65536
        ∧ dataPtr.toNat + len.toNat ≤ s6.mem.pages * 65536
        ∧ retPtr.toNat + 12 ≤ s6.mem.pages * 65536
        ∧ (ptr.toNat + len.toNat ≤ dataPtr.toNat ∨ dataPtr.toNat + len.toNat ≤ ptr.toNat)
        ∧ (ptr.toNat + len.toNat ≤ retPtr.toNat ∨ retPtr.toNat + 12 ≤ ptr.toNat)
        ∧ (∀ k : UInt32, k.toNat < len.toNat →
             s6.mem.read8 (dataPtr + k) = st.mem.read8 (dataPtr + k))))
    (hsd : retPtr.toNat + 12 ≤ dataPtr.toNat ∨ dataPtr.toNat + len.toNat ≤ retPtr.toNat) :
    TerminatesWith env «module» 8 st [.i32 argPtr, .i32 retPtr]
      (fun st' _ => st'.mem.read32 (retPtr + 8) = len ∧ st'.mem.read32 (retPtr + 4) = ptr ∧
        ∀ k : UInt32, k.toNat < len.toNat → st'.mem.read8 (ptr + k) = st.mem.read8 (dataPtr + k)) := by
  apply func8_of_func7 env st retPtr argPtr dataPtr len _ hdata hlen hb
  apply func7_of_func1 env st retPtr dataPtr len _
  apply func1_of_func2 env st retPtr dataPtr len _
  exact (func2_terminates env st retPtr dataPtr len sp cap ptr hsp hcap hsd).mono
    (fun _ _ h => h.2)

/-! ## Allocator plumbing (loop-free layers above `dlmalloc`)

The call chain from `with_capacity_in` down to the real allocator is
`func6 → func3 → func5 → func0 → func9 → func27 → func29 (dlmalloc::malloc)`.
Every layer is loop-free except `func29`. These lemmas peel the loop-free layers,
reducing the allocation obligation to a single `dlmalloc::malloc` contract. -/

/-- `__rust_alloc` (func 9) is a pass-through to `__rdl_alloc` (func 27). -/
theorem func9_of_func27 (env : HostEnv Unit) (st : Store Unit) (size align : UInt32)
    (R : Store Unit → UInt32 → Prop)
    (hf27 : TerminatesWith env «module» 27 st [.i32 align, .i32 size]
              (fun st' vs => ∃ p, vs = [.i32 p] ∧ R st' p)) :
    TerminatesWith env «module» 9 st [.i32 align, .i32 size]
      (fun st' vs => ∃ p, vs = [.i32 p] ∧ R st' p) := by
  apply TerminatesWith.of_wp_entry_for (f := func9Def) rfl
  unfold func9Def func9
  wp_run
  apply wp_call_tw hf27
  rintro st' vs ⟨p, rfl, hR⟩
  wp_run
  exact ⟨p, rfl, hR⟩

/-- `__rdl_alloc` (func 27) calls `dlmalloc::malloc` (func 29) directly when the
alignment is small (`< 9`), which is always the case for byte buffers. -/
theorem func27_of_func29 (env : HostEnv Unit) (st : Store Unit) (size align : UInt32)
    (R : Store Unit → UInt32 → Prop) (halign : align.toNat < 9)
    (hf29 : TerminatesWith env «module» 29 st [.i32 size]
              (fun st' vs => ∃ p, vs = [.i32 p] ∧ R st' p)) :
    TerminatesWith env «module» 27 st [.i32 align, .i32 size]
      (fun st' vs => ∃ p, vs = [.i32 p] ∧ R st' p) := by
  have hlt : align < 9 := UInt32.lt_iff_toNat_lt.mpr (by simpa using halign)
  apply TerminatesWith.of_wp_entry_for (f := func27Def) rfl
  unfold func27Def func27
  apply wp_block_cons
  wp_run
  simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.getElem?_nil, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, hlt]
  apply wp_call_tw hf29
  rintro st' vs ⟨p, rfl, hR⟩
  wp_run
  exact ⟨p, rfl, hR⟩

/-- `__rust_no_alloc_shim_is_unstable_v2` (func 13) is a no-op that returns. -/
theorem func13_terminates (env : HostEnv Unit) (st : Store Unit) :
    TerminatesWith env «module» 13 st [] (fun st' vs => st' = st ∧ vs = []) := by
  apply TerminatesWith.of_wp_entry_for (f := func13Def) rfl
  unfold func13Def func13
  wp_run
  exact ⟨trivial, rfl⟩

end Project.Encode.Proofs
