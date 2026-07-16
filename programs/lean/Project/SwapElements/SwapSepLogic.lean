import Project.SwapElements.Program
import Project.SwapElements.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmWP
import CodeLib.Entry
import CodeLib.RustStd.Frame

/-! # Swap Elements — Separation Logic Proof

End-to-end proof of `SwapElementsSpec` through the SepLogic layer.

Call chain: func4 → func0 → func1 → func2 (and func4 → func3 for the
fat-pointer spill). The leaves (func2, func3) are proved through the
iris-lean pipeline: `wasm_heap_adequacy` enters the iProp world, the
per-instruction `wp_wasm_*` rules step each instruction (with `ghost_id`
discharging the — currently trivial — ghost-heap obligation), and
`wp_wasm_prop_to_TerminatesWith` lowers the result to a spec-level
statement. The callers (func0, func1, func4) compose at the Prop level:
`wp_wasm_prop_of_exec_eq` hops over the already-traced straight-line (or
bounds-check block) prefix to the `.call` site, and `wp_wasm_prop_call`
splices in the callee's `TerminatesWith`. No concrete fuel values appear
outside the hop offsets, which are fixed by the block nesting depth.

Key memory facts after the swap:
  final_mem = (st.mem
    .write32(1048568, ptr)         -- func3: ptr spill
    .write32(1048572, len)         -- func3: len spill
    .write64(1048552, vA)          -- func2: temp = *ptr_a
    .write64(ptr + 8*i, vB)       -- func2: *ptr_a = *ptr_b
    .write64(ptr + 8*j, vA))      -- func2: *ptr_b = temp
  where vA = st.mem.read64(ptr + 8*i), vB = st.mem.read64(ptr + 8*j).

The `Mem.*_disjoint` framing lemmas (CodeLib.RustStd.Frame) show that
addresses ≥ 1048576 other than ptr+8*i and ptr+8*j are unchanged by all
these writes.

The spec's global0 and pages-bound preconditions are load-bearing here:
without `global 0 = 1048576` on entry, func4's scratch frame (`global 0 −
16`) could alias the array and the swap postcondition would be false. -/

namespace Project.SwapElements.SwapSepLogic

open Iris Wasm Wasm.SepLogic Project.SwapElements.Spec

-- func3 spills ptr/len into the 8-byte slot at [1048568, 1048575]
-- body: write32(1048572, len) then write32(1048568, ptr)
set_option maxHeartbeats 4000000 in
private theorem func3_terminates (env : HostEnv Unit) (st : Store Unit)
    (ptr len : UInt32)
    (hpg : (1048576 : Nat) ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 3 st
      [.i32 (1048652 : UInt32), .i32 len, .i32 ptr, .i32 (1048568 : UInt32)]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read32 (1048568 : UInt32) = ptr
        ∧ st'.mem.read32 (1048572 : UInt32) = len
        ∧ ∀ a : UInt32, (1048576 : Nat) ≤ a.toNat →
            st'.mem.read64 a = st.mem.read64 a) := by
  have himp : «module».imports[3]? = none := rfl
  have hf : «module».funcs[3 - «module».imports.length]? = some func3Def := rfl
  have hwp : wp_wasm_prop «module» st
      (func3Def.toLocals ([.i32 (1048652 : UInt32), .i32 len, .i32 ptr,
                           .i32 (1048568 : UInt32)].take func3Def.numParams).reverse)
      func3Def.body env
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read32 (1048568 : UInt32) = ptr
        ∧ st'.mem.read32 (1048572 : UInt32) = len
        ∧ ∀ a : UInt32, (1048576 : Nat) ≤ a.toNat →
            st'.mem.read64 a = st.mem.read64 a) := by
    apply wasm_heap_adequacy
    intro inst
    let m₁ := st.mem.write32 ((1048568 : UInt32) + (4 : UInt32)) len
    let m₂ := m₁.write32 ((1048568 : UInt32) + (0 : UInt32)) ptr
    have hm₁ : m₁ = st.mem.write32 ((1048568 : UInt32) + (4 : UInt32)) len := rfl
    have hm₂ : m₂ = m₁.write32 ((1048568 : UInt32) + (0 : UInt32)) ptr := rfl
    have hpages : m₂.pages = st.mem.pages := by
      simp only [hm₂, hm₁, Mem.write32_pages]
    have hread_1568 : m₂.read32 (1048568 : UInt32) = ptr := by
      simp only [hm₂, show (1048568 : UInt32) + (0 : UInt32) = (1048568 : UInt32) from rfl]
      exact Mem.read32_write32_same m₁ (1048568 : UInt32) ptr
    have hread_1572 : m₂.read32 (1048572 : UInt32) = len := by
      simp only [hm₂, show (1048568 : UInt32) + (0 : UInt32) = (1048568 : UInt32) from rfl]
      rw [Mem.read32_write32_disjoint m₁ (1048568 : UInt32) (1048572 : UInt32) ptr
            (Or.inr (by simp only [show (1048568 : UInt32).toNat = 1048568 from rfl,
                                   show (1048572 : UInt32).toNat = 1048572 from rfl]; omega))]
      simp only [hm₁, show (1048568 : UInt32) + (4 : UInt32) = (1048572 : UInt32) from rfl]
      exact Mem.read32_write32_same st.mem (1048572 : UInt32) len
    have hread_ne : ∀ a : UInt32, (1048576 : Nat) ≤ a.toNat →
        m₂.read64 a = st.mem.read64 a := by
      intro a ha
      simp only [hm₂, show (1048568 : UInt32) + (0 : UInt32) = (1048568 : UInt32) from rfl]
      rw [Mem.read64_write32_disjoint m₁ a (1048568 : UInt32) ptr
            (Or.inl (by simp only [show (1048568 : UInt32).toNat = 1048568 from rfl]; omega))]
      simp only [hm₁, show (1048568 : UInt32) + (4 : UInt32) = (1048572 : UInt32) from rfl]
      rw [Mem.read64_write32_disjoint st.mem a (1048572 : UInt32) len
            (Or.inl (by simp only [show (1048572 : UInt32).toNat = 1048572 from rfl]; omega))]
    show ⊢ wp_wasm «module» st
      { params := [.i32 (1048568 : UInt32), .i32 ptr, .i32 len, .i32 (1048652 : UInt32)],
        locals := [], values := [] }
      [.localGet 0, .localGet 2, .store32 (4 : UInt32),
       .localGet 0, .localGet 1, .store32 (0 : UInt32), .ret] env _
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_store32 rfl
        (by simp only [show (1048568 : UInt32).toNat = 1048568 from rfl,
                       show (4 : UInt32).toNat = 4 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_store32 rfl
        (by simp only [Mem.write32_pages,
                       show (1048568 : UInt32).toNat = 1048568 from rfl,
                       show (0 : UInt32).toNat = 0 from rfl]; omega)
        (ghost_id ?_)
    exact wp_wasm_ret ⟨rfl, rfl, hpages, hread_1568, hread_1572, hread_ne⟩
  exact wp_wasm_prop_to_TerminatesWith hf himp rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

-- func2: the actual swap via scratch at 1048552 (global0 = 1048560 at call time)
set_option maxHeartbeats 4000000 in
private theorem func2_terminates (env : HostEnv Unit) (st : Store Unit)
    (ptr_a ptr_b : UInt32)
    (hg0 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32)))
    (hpg_scratch : (1048560 : Nat) ≤ st.mem.pages * 65536)
    (hpg_a : ptr_a.toNat + 8 ≤ st.mem.pages * 65536)
    (hpg_b : ptr_b.toNat + 8 ≤ st.mem.pages * 65536)
    -- ptr_a and ptr_b are both above the scratch region [1048544,1048559]
    (hge_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hge_b : (1048560 : Nat) ≤ ptr_b.toNat)
    -- either equal or 8-byte disjoint (guaranteed by 8-byte array stride)
    (hdisj : ptr_a = ptr_b ∨
             ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat) :
    TerminatesWith env «module» 2 st [.i32 ptr_b, .i32 ptr_a]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 ptr_a = st.mem.read64 ptr_b
        ∧ st'.mem.read64 ptr_b = st.mem.read64 ptr_a
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ ptr_a.toNat ∨ ptr_a.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
  have himp : «module».imports[2]? = none := rfl
  have hf : «module».funcs[2 - «module».imports.length]? = some func2Def := rfl
  have hwp : wp_wasm_prop «module» st
      (func2Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func2Def.numParams).reverse)
      func2Def.body env
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 ptr_a = st.mem.read64 ptr_b
        ∧ st'.mem.read64 ptr_b = st.mem.read64 ptr_a
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ ptr_a.toNat ∨ ptr_a.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
    apply wasm_heap_adequacy
    intro inst
    -- pre-prove memory postcondition on the exact write64 chain used by the wp steps
    -- addresses: 1048560-16+8, ptr_a+0, ptr_b+0 (offset immediates not yet reduced)
    have h1552_nat : (1048552 : UInt32).toNat = 1048552 := rfl
    have hne_a : (1048552 : UInt32).toNat + 8 ≤ ptr_a.toNat := by omega
    have hne_b : (1048552 : UInt32).toNat + 8 ≤ ptr_b.toNat := by omega
    have ha0 : ptr_a + (0 : UInt32) = ptr_a := by simp
    have hb0 : ptr_b + (0 : UInt32) = ptr_b := by simp
    have h1552eq : ((1048560 : UInt32) - 16 + 8) = (1048552 : UInt32) := rfl
    let m₁ := st.mem.write64 ((1048560 : UInt32) - 16 + 8) (st.mem.read64 (ptr_a + 0))
    let m₂ := m₁.write64 (ptr_a + 0) (m₁.read64 (ptr_b + 0))
    let m₃ := m₂.write64 (ptr_b + 0) (m₂.read64 ((1048560 : UInt32) - 16 + 8))
    have hm₁ : m₁ = st.mem.write64 ((1048560 : UInt32) - 16 + 8) (st.mem.read64 (ptr_a + 0)) := rfl
    have hm₂ : m₂ = m₁.write64 (ptr_a + 0) (m₁.read64 (ptr_b + 0)) := rfl
    have hm₃ : m₃ = m₂.write64 (ptr_b + 0) (m₂.read64 ((1048560 : UInt32) - 16 + 8)) := rfl
    have hpages : m₃.pages = st.mem.pages := by
      simp only [hm₃, hm₂, hm₁, Mem.write64_pages]
    have hread_a : m₃.read64 ptr_a = st.mem.read64 ptr_b := by
      simp only [hm₃, hm₂, hm₁, ha0, hb0, h1552eq]
      rcases hdisj with rfl | h | h
      · rw [Mem.read64_write64_same,
            Mem.read64_write64_disjoint _ ptr_a _ _ (Or.inl hne_a),
            Mem.read64_write64_same]
      · rw [Mem.read64_write64_disjoint _ ptr_b _ _ (Or.inl h),
            Mem.read64_write64_same,
            Mem.read64_write64_disjoint _ (1048552 : UInt32) _ _ (Or.inr hne_b)]
      · rw [Mem.read64_write64_disjoint _ ptr_b _ _ (Or.inr h),
            Mem.read64_write64_same,
            Mem.read64_write64_disjoint _ (1048552 : UInt32) _ _ (Or.inr hne_b)]
    have hread_b : m₃.read64 ptr_b = st.mem.read64 ptr_a := by
      simp only [hm₃, hm₂, hm₁, ha0, hb0, h1552eq]
      rw [Mem.read64_write64_same,
          Mem.read64_write64_disjoint _ ptr_a _ _ (Or.inl hne_a),
          Mem.read64_write64_same]
    have hread_ne : ∀ a : UInt32,
        (a.toNat + 8 ≤ ptr_a.toNat ∨ ptr_a.toNat + 8 ≤ a.toNat) →
        (a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ a.toNat) →
        (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
        m₃.read64 a = st.mem.read64 a := by
      intro a h1 h2 h3
      simp only [hm₃, hm₂, hm₁, ha0, hb0, h1552eq]
      rw [Mem.read64_write64_disjoint _ ptr_b _ _ h2,
          Mem.read64_write64_disjoint _ ptr_a _ _ h1,
          Mem.read64_write64_disjoint _ (1048552 : UInt32) _ _
            (by rcases h3 with h | h
                · exact Or.inl (by omega)
                · exact Or.inr (by omega))]
    show ⊢ wp_wasm «module» st
      { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)], values := [] }
      [.globalGet 0, .const (16 : UInt32), .sub, .localSet 2, .localGet 2, .localGet 0,
       .load64 (0 : UInt32), .store64 (8 : UInt32), .localGet 0, .localGet 1,
       .load64 (0 : UInt32), .store64 (0 : UInt32), .localGet 1, .localGet 2,
       .load64 (8 : UInt32), .store64 (0 : UInt32), .ret] env _
    refine wp_wasm_globalGet hg0 (ghost_id ?_)
    refine wp_wasm_const (16 : UInt32) (ghost_id ?_)
    refine wp_wasm_sub rfl (ghost_id ?_)
    refine wp_wasm_localSet rfl rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_load64 rfl
        (by simp only [show (0 : UInt32).toNat = 0 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_store64 rfl
        (by simp only [show (1048560 - 16 : UInt32).toNat = 1048544 from rfl,
                       show (8 : UInt32).toNat = 8 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_load64 rfl
        (by simp only [Mem.write64_pages, show (0 : UInt32).toNat = 0 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_store64 rfl
        (by simp only [Mem.write64_pages, show (0 : UInt32).toNat = 0 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_localGet rfl (ghost_id ?_)
    refine wp_wasm_load64 rfl
        (by simp only [Mem.write64_pages,
                       show (1048560 - 16 : UInt32).toNat = 1048544 from rfl,
                       show (8 : UInt32).toNat = 8 from rfl]; omega)
        (ghost_id ?_)
    refine wp_wasm_store64 rfl
        (by simp only [Mem.write64_pages, show (0 : UInt32).toNat = 0 from rfl]; omega)
        (ghost_id ?_)
    exact wp_wasm_ret ⟨rfl, rfl, hpages, hread_a, hread_b, hread_ne⟩
  exact wp_wasm_prop_to_TerminatesWith hf himp rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

-- func1: bounds-check i < len and j < len, compute addresses, call func2.
-- The three nested bounds-check blocks exit via an outward break on the
-- happy path (`br_if 1` → `Break 1`), which is outside the block rule's
-- Fallthrough/Break-0 shape — so the block section is traced once at the
-- exec level and hopped over with `wp_wasm_prop_of_exec_eq`; the call is
-- then composed with `wp_wasm_prop_call`.
private theorem func1_terminates_sw (env : HostEnv Unit) (st : Store Unit)
    (ptr len i j : UInt32)
    (hi : i < len) (hj : j < len)
    (hpg : ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536)
    (hpages_bound : st.mem.pages * 65536 ≤ 4294967296)
    (hptr : (1048576 : Nat) ≤ ptr.toNat)
    (hg0 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32))) :
    TerminatesWith env «module» 1 st
      [.i32 (1048604 : UInt32), .i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ (elemAddr ptr i).toNat ∨ (elemAddr ptr i).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (elemAddr ptr j).toNat ∨ (elemAddr ptr j).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
  have hi_nat : i.toNat < len.toNat := hi
  have hj_nat : j.toNat < len.toNat := hj
  have helemI : (elemAddr ptr i).toNat = ptr.toNat + 8 * i.toNat :=
    elemAddr_toNat ptr i (by omega)
  have helemJ : (elemAddr ptr j).toNat = ptr.toNat + 8 * j.toNat :=
    elemAddr_toNat ptr j (by omega)
  have hpg_a : (elemAddr ptr i).toNat + 8 ≤ st.mem.pages * 65536 := by
    rw [helemI]; omega
  have hpg_b : (elemAddr ptr j).toNat + 8 ≤ st.mem.pages * 65536 := by
    rw [helemJ]; omega
  have hge_a : (1048560 : Nat) ≤ (elemAddr ptr i).toNat := by rw [helemI]; omega
  have hge_b : (1048560 : Nat) ≤ (elemAddr ptr j).toNat := by rw [helemJ]; omega
  have hdisj : elemAddr ptr i = elemAddr ptr j ∨
               (elemAddr ptr i).toNat + 8 ≤ (elemAddr ptr j).toNat ∨
               (elemAddr ptr j).toNat + 8 ≤ (elemAddr ptr i).toNat := by
    rcases eq_or_ne i j with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr (elemAddr_disjoint ptr i j (by omega) (by omega) hne)
  have himp₁ : «module».imports[1]? = none := rfl
  have hf₁ : «module».funcs[1 - «module».imports.length]? = some func1Def := rfl
  -- the address arithmetic the codegen emits, in the form the exec trace
  -- produces (`3 % 32` already reduced to `3` by the simp normal form)
  have haddr : ∀ k : UInt32, k <<< (3 : UInt32) + ptr = elemAddr ptr k := fun k => by
    simpa using elemAddr_of_shl ptr k
  have hwp : wp_wasm_prop «module» st
      (func1Def.toLocals ([.i32 (1048604 : UInt32), .i32 j, .i32 i, .i32 len,
                           .i32 ptr].take func1Def.numParams).reverse)
      func1Def.body env
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ (elemAddr ptr i).toNat ∨ (elemAddr ptr i).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (elemAddr ptr j).toNat ∨ (elemAddr ptr j).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
    apply wp_wasm_prop_of_exec_eq (K := 4) (c := 3) (st' := st)
        (locals' := { params := [.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 (1048604 : UInt32)],
                      locals := [.i32 (elemAddr ptr i)],
                      values := [.i32 (elemAddr ptr j), .i32 (elemAddr ptr i)] })
        (prog' := [.call 2, .ret])
    · intro fuel
      show exec (fuel + 4) «module» st
        { params := [.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 (1048604 : UInt32)],
          locals := [.i32 (0 : UInt32)], values := [] }
        func1 env = _
      simp only [func1]
      simp [exec, execOne.eq_def, Locals.get, Locals.set?, hi, hj, haddr]
      -- both sides are now matches over the same `run` of func2; the block
      -- wrapper on the left only differs syntactically, so split on the result
      rcases run (fuel + 2) «module» 2 st
          [.i32 (elemAddr ptr j), .i32 (elemAddr ptr i)] env <;> rfl
    · apply wp_wasm_prop_call
      refine (func2_terminates env st (elemAddr ptr i) (elemAddr ptr j)
          hg0 (by omega) hpg_a hpg_b hge_a hge_b hdisj).mono ?_
      rintro st' vs ⟨rfl, hglob2, hpages2, hrA2, hrB2, hother2⟩
      refine ⟨1, ?_⟩
      simp only [exec, execOne]
      exact ⟨trivial, hglob2, hpages2, hrA2, hrB2, hother2⟩
  exact wp_wasm_prop_to_TerminatesWith hf₁ himp₁ rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

-- func0: simple wrapper that forwards to func1; a one-hop prefix
-- (five pushes) then `wp_wasm_prop_call`.
private theorem func0_terminates_sw (env : HostEnv Unit) (st : Store Unit)
    (ptr len i j : UInt32)
    (hi : i < len) (hj : j < len)
    (hpg : ptr.toNat + 8 * len.toNat ≤ st.mem.pages * 65536)
    (hpages_bound : st.mem.pages * 65536 ≤ 4294967296)
    (hptr : (1048576 : Nat) ≤ ptr.toNat)
    (hg0 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32))) :
    TerminatesWith env «module» 0 st
      [.i32 j, .i32 i, .i32 len, .i32 ptr]
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ (elemAddr ptr i).toNat ∨ (elemAddr ptr i).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (elemAddr ptr j).toNat ∨ (elemAddr ptr j).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
  have himp : «module».imports[0]? = none := rfl
  have hf : «module».funcs[0 - «module».imports.length]? = some func0Def := rfl
  have hwp : wp_wasm_prop «module» st
      (func0Def.toLocals ([.i32 j, .i32 i, .i32 len, .i32 ptr].take
        func0Def.numParams).reverse)
      func0Def.body env
      (fun st' rs =>
        rs = [] ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ a : UInt32,
            (a.toNat + 8 ≤ (elemAddr ptr i).toNat ∨ (elemAddr ptr i).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (elemAddr ptr j).toNat ∨ (elemAddr ptr j).toNat + 8 ≤ a.toNat) →
            (a.toNat + 8 ≤ (1048552 : Nat) ∨ (1048560 : Nat) ≤ a.toNat) →
            st'.mem.read64 a = st.mem.read64 a) := by
    apply wp_wasm_prop_of_exec_eq (K := 1) (c := 1) (st' := st)
        (locals' := { params := [.i32 ptr, .i32 len, .i32 i, .i32 j],
                      locals := [],
                      values := [.i32 (1048604 : UInt32), .i32 j, .i32 i, .i32 len,
                                 .i32 ptr] })
        (prog' := [.call 1, .ret])
    · intro fuel
      show exec (fuel + 1) «module» st
        { params := [.i32 ptr, .i32 len, .i32 i, .i32 j], locals := [], values := [] }
        func0 env = _
      simp only [func0]
      simp [exec, execOne.eq_def, Locals.get]
    · apply wp_wasm_prop_call
      refine (func1_terminates_sw env st ptr len i j hi hj hpg hpages_bound
          hptr hg0).mono ?_
      rintro st' vs ⟨rfl, hglob1, hpages1, hrA1, hrB1, hother1⟩
      refine ⟨1, ?_⟩
      simp only [exec, execOne]
      exact ⟨trivial, hglob1, hpages1, hrA1, hrB1, hother1⟩
  exact wp_wasm_prop_to_TerminatesWith hf himp rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

/-! ## Top-level spec -/

set_option maxRecDepth 1048576 in
@[proves Project.SwapElements.Spec.SwapElementsSpec]
theorem swap_spec_sep : SwapElementsSpec := by
  intro env st ptr len i j hi hj hbound hptr hpages hg0
  have hpages_bound : st.mem.pages * 65536 ≤ 4294967296 := by omega
  have himp₄ : «module».imports[4]? = none := rfl
  have hf₄ : «module».funcs[4 - «module».imports.length]? = some func4Def := rfl
  -- Shadow-stack descend: global0 goes from 1048576 → 1048560
  let stg : Store Unit :=
    { st with globals := { st.globals with globals := st.globals.globals.set 0 (.i32 1048560) } }
  have hpg3 : (1048576 : Nat) ≤ stg.mem.pages * 65536 := by simp only [stg]; omega
  -- Helper for helemI/helemJ/helemK proofs
  have helem_toNat : ∀ k : UInt32, k < len →
      (elemAddr ptr k).toNat = ptr.toNat + 8 * k.toNat := by
    intro k hk
    have hk_nat : k.toNat < len.toNat := hk
    exact elemAddr_toNat ptr k (by omega)
  have helemI := helem_toNat i hi
  have helemJ := helem_toNat j hj
  have hwp : wp_wasm_prop «module» st
      (func4Def.toLocals ([.i32 j, .i32 i, .i32 len, .i32 ptr].take
        func4Def.numParams).reverse)
      func4Def.body env
      (fun st' rs =>
        rs = []
        ∧ st'.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
        ∧ st'.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
        ∧ ∀ k : UInt32, k < len → k ≠ i → k ≠ j →
            st'.mem.read64 (elemAddr ptr k) = st.mem.read64 (elemAddr ptr k)) := by
    -- hop 1: frame setup (globalGet/sub/globalSet, spill args) up to `call 3`
    apply wp_wasm_prop_of_exec_eq (K := 1) (c := 1) (st' := stg)
        (locals' := { params := [.i32 ptr, .i32 len, .i32 i, .i32 j],
                      locals := [.i32 (1048560 : UInt32), .i32 (1048652 : UInt32),
                                 .i32 (0 : UInt32)],
                      values := [.i32 (1048652 : UInt32), .i32 len, .i32 ptr,
                                 .i32 (1048568 : UInt32)] })
        (prog' := [.call 3, .localGet 4, .load32 (12 : UInt32), .localSet 6,
                   .localGet 4, .load32 (8 : UInt32), .localGet 6, .localGet 2,
                   .localGet 3, .call 0, .localGet 4, .const (16 : UInt32), .add,
                   .globalSet 0, .ret])
    · intro fuel
      show exec (fuel + 1) «module» st
        { params := [.i32 ptr, .i32 len, .i32 i, .i32 j],
          locals := [.i32 (0 : UInt32), .i32 (0 : UInt32), .i32 (0 : UInt32)],
          values := [] }
        func4 env = _
      simp only [func4]
      simp [exec, execOne.eq_def, Locals.get, Locals.set?, hg0, stg]
    · apply wp_wasm_prop_call
      refine (func3_terminates env stg ptr len hpg3).mono ?_
      rintro st3 vs ⟨rfl, hglob3, hpages3, hread3_1568, hread3_1572, hread3_ne⟩
      -- Derive global0 = 1048560 in st3 (func3 preserved globals; globals is a List)
      have hg0_3 : st3.globals.globals[0]? = some (.i32 (1048560 : UInt32)) := by
        rw [hglob3]
        simp only [stg]
        match hnn : st.globals.globals with
        | [] => simp [hnn] at hg0
        | _ :: _ => simp [List.set]
      have hst3_pages : st3.mem.pages = st.mem.pages := by rw [hpages3]
      have hpg_st3 : ¬ (st3.mem.pages * 65536 < (1048576 : Nat)) := by
        rw [hst3_pages]; omega
      have hpg_st3_lo : ¬ (st3.mem.pages * 65536 < (1048572 : Nat)) := by
        rw [hst3_pages]; omega
      -- hop 2: read the fat pointer back up to `call 0`
      apply wp_wasm_prop_of_exec_eq (K := 1) (c := 1) (st' := st3)
          (locals' := { params := [.i32 ptr, .i32 len, .i32 i, .i32 j],
                        locals := [.i32 (1048560 : UInt32), .i32 (1048652 : UInt32),
                                   .i32 len],
                        values := [.i32 j, .i32 i, .i32 len, .i32 ptr] })
          (prog' := [.call 0, .localGet 4, .const (16 : UInt32), .add,
                     .globalSet 0, .ret])
      · intro fuel
        simp [exec, execOne.eq_def, Locals.get, Locals.set?,
              hread3_1568, hread3_1572, hpg_st3, hpg_st3_lo]
      · apply wp_wasm_prop_call
        refine (func0_terminates_sw env st3 ptr len i j hi hj
            (by rw [hst3_pages]; exact hbound)
            (by rw [hst3_pages]; exact hpages_bound)
            hptr hg0_3).mono ?_
        rintro st0 vs ⟨rfl, hglob0, hpages0, hrA0, hrB0, hother0⟩
        have hg0_st0 : st0.globals.globals[0]? = some (.i32 (1048560 : UInt32)) :=
          hglob0 ▸ hg0_3
        -- frame teardown: restore global0 = 1048576, then return.
        -- Assemble the spec postcondition from func0's swap facts and
        -- func3's frame-write framing.
        refine ⟨1, ?_⟩
        simp [exec, execOne.eq_def, Locals.get, hg0_st0]
        refine ⟨?_, ?_, ?_⟩
        · -- read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j):
          -- func0 swapped relative to st3; func3's two store32s at
          -- [1048568,1048576) don't touch array addresses (≥ 1048576);
          -- stg.mem = st.mem (globals-only change)
          rw [hrA0, hread3_ne (elemAddr ptr j) (by rw [helemJ]; omega)]
        · rw [hrB0, hread3_ne (elemAddr ptr i) (by rw [helemI]; omega)]
        · intro k hk hki hkj
          have helemK := helem_toNat k hk
          trans st3.mem.read64 (elemAddr ptr k)
          · apply hother0
            · -- disjoint with elemAddr ptr i
              rcases Nat.lt_or_ge k.toNat i.toNat with h | h
              · left; rw [helemK, helemI]; omega
              · rcases Nat.eq_or_lt_of_le h with heq | hlt
                · exact absurd (UInt32.toNat.inj heq.symm) hki
                · right; rw [helemK, helemI]; omega
            · -- disjoint with elemAddr ptr j
              rcases Nat.lt_or_ge k.toNat j.toNat with h | h
              · left; rw [helemK, helemJ]; omega
              · rcases Nat.eq_or_lt_of_le h with heq | hlt
                · exact absurd (UInt32.toNat.inj heq.symm) hkj
                · right; rw [helemK, helemJ]; omega
            · -- above scratch region
              right; rw [helemK]; omega
          · rw [hread3_ne (elemAddr ptr k) (by rw [helemK]; omega)]
  exact wp_wasm_prop_to_TerminatesWith hf₄ himp₄ rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

end Project.SwapElements.SwapSepLogic
