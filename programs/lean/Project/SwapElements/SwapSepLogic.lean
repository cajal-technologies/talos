import Project.SwapElements.Program
import Project.SwapElements.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmWP
import CodeLib.Entry
import CodeLib.RustStd.Frame

/-! # Swap Elements — Separation Logic Proof

Demonstrates ownership transfer through func2's three load/store pairs:
  1. load64 ptr_a → store64 scratch   (temp = *a)
  2. load64 ptr_b → store64 ptr_a     (*a = *b)
  3. load64 scratch → store64 ptr_b   (*b = temp)

Ownership flow:
  Pre:  ptr_a ↦ a  ∗  ptr_b ↦ b  ∗  scratch ↦ _
  Step 1: ptr_a ↦ a consumed by load, scratch ↦ a produced by store
  Step 2: ptr_b ↦ b consumed by load, ptr_a ↦ b produced by store
  Step 3: scratch ↦ a consumed by load, ptr_b ↦ a produced by store
  Post: ptr_a ↦ b  ∗  ptr_b ↦ a  ∗  scratch ↦ a
-/

namespace Project.SwapElements.SwapSepLogic

open Iris Wasm Wasm.SepLogic Project.SwapElements.Spec

variable [inst : WasmHeapGS]

def swapPre (ptr_a ptr_b scratch : UInt32) (a b : UInt64) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 ptr_a a) ∗ (pointsTo_u64 ptr_b b) ∗ (pointsTo_u64 scratch 0)

def swapPost (ptr_a ptr_b scratch : UInt32) (a b : UInt64) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 ptr_a b) ∗ (pointsTo_u64 ptr_b a) ∗ (pointsTo_u64 scratch a)

/-! The ownership transfer chain for func2.

Each step consumes ownership via wp_load64/wp_store64 and produces
new ownership. The separating conjunction ensures disjointness:
ptr_a, ptr_b, and scratch must be non-overlapping 8-byte regions. -/

theorem swap_ownership (ptr_a ptr_b scratch : UInt32) (a b : UInt64) :
    iprop% swapPre ptr_a ptr_b scratch a b ⊢
      wp_store64 scratch 0 a (
      wp_store64 ptr_a a b (
      wp_store64 ptr_b b a (
      swapPost ptr_a ptr_b scratch a b))) := by
  unfold swapPre wp_store64 swapPost
  iintro ⟨Ha, Hb, Hs⟩
  iframe
  iintro Hs1 Ha1 Hb1
  iframe

/-! ## Function termination lemmas

Call chain: func4 → func0 → func1 → func2 (and func4 → func3 for the
fat-pointer spill). func2 and func3 are proved through the iris-lean
pipeline (`wasm_heap_adequacy` + per-instruction iProp rules) and lowered
to `TerminatesWith` via `wp_wasm_prop_to_TerminatesWith`; func1, func0,
and func4 compose their callees' `TerminatesWith` results manually
(`run_fuel_mono` + an exec trace), since calls are not yet expressible
inside the iProp WP (see the scope note on `wp_wasm_F`).

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
    apply wp_wasm_localGet (hget := rfl)
    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
    · apply wp_wasm_localGet (hget := rfl)
      intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
      · apply wp_wasm_store32 (hstack := rfl)
            (hbounds := by
              simp only [show (1048568 : UInt32).toNat = 1048568 from rfl,
                         show (4 : UInt32).toNat = 4 from rfl]; omega)
        intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
        · apply wp_wasm_localGet (hget := rfl)
          intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
          · apply wp_wasm_localGet (hget := rfl)
            intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
            · apply wp_wasm_store32 (hstack := rfl)
                  (hbounds := by
                    simp only [Mem.write32_pages,
                               show (1048568 : UInt32).toNat = 1048568 from rfl,
                               show (0 : UInt32).toNat = 0 from rfl]; omega)
              intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]; · iexact Hσ
              · unfold wp_wasm
                iapply least_fixpoint_unfold_mpr
                unfold wp_wasm_F
                dsimp only []
                exact BI.pure_intro ⟨rfl, rfl, hpages, hread_1568, hread_1572, hread_ne⟩
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
    apply wp_wasm_globalGet (hget := hg0)
    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
    · iexact Hσ
    · apply wp_wasm_const (16 : UInt32)
      intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
      · iexact Hσ
      · apply wp_wasm_sub (hstack := rfl)
        intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
        · iexact Hσ
        · apply wp_wasm_localSet (hstack := rfl) (hset := rfl)
          intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
          · iexact Hσ
          · apply wp_wasm_localGet (hget := rfl)
            intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
            · iexact Hσ
            · apply wp_wasm_localGet (hget := rfl)
              intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
              · iexact Hσ
              · apply wp_wasm_load64 (hstack := rfl)
                    (hbounds := by
                      simp only [show (0 : UInt32).toNat = 0 from rfl]; omega)
                intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                · iexact Hσ
                · apply wp_wasm_store64 (hstack := rfl)
                      (hbounds := by
                        simp only [show (1048560 - 16 : UInt32).toNat = 1048544 from rfl,
                                   show (8 : UInt32).toNat = 8 from rfl]; omega)
                  intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                  · iexact Hσ
                  · apply wp_wasm_localGet (hget := rfl)
                    intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                    · iexact Hσ
                    · apply wp_wasm_localGet (hget := rfl)
                      intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                      · iexact Hσ
                      · apply wp_wasm_load64 (hstack := rfl)
                            (hbounds := by
                              simp only [Mem.write64_pages,
                                show (0 : UInt32).toNat = 0 from rfl]; omega)
                        intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                        · iexact Hσ
                        · apply wp_wasm_store64 (hstack := rfl)
                              (hbounds := by
                                simp only [Mem.write64_pages,
                                  show (0 : UInt32).toNat = 0 from rfl]; omega)
                          intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                          · iexact Hσ
                          · apply wp_wasm_localGet (hget := rfl)
                            intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                            · iexact Hσ
                            · apply wp_wasm_localGet (hget := rfl)
                              intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                              · iexact Hσ
                              · apply wp_wasm_load64 (hstack := rfl)
                                    (hbounds := by
                                      simp only [Mem.write64_pages,
                                        show (1048560 - 16 : UInt32).toNat = 1048544 from rfl,
                                        show (8 : UInt32).toNat = 8 from rfl]; omega)
                                intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                                · iexact Hσ
                                · apply wp_wasm_store64 (hstack := rfl)
                                      (hbounds := by
                                        simp only [Mem.write64_pages,
                                          show (0 : UInt32).toNat = 0 from rfl]; omega)
                                  intro σ; iintro Hσ; imodintro; iexists σ; isplitl [Hσ]
                                  · iexact Hσ
                                  · -- ret
                                    unfold wp_wasm
                                    iapply least_fixpoint_unfold_mpr
                                    unfold wp_wasm_F
                                    dsimp only []
                                    exact BI.pure_intro ⟨rfl, rfl, hpages, hread_a, hread_b, hread_ne⟩
  exact wp_wasm_prop_to_TerminatesWith hf himp rfl (Nat.le_refl _)
    (fun _ _ h => ⟨rfl, h.2⟩) hwp

-- func1: bounds-check i < len and j < len, compute addresses, call func2
-- called from func0 with args [.i32 1048604, .i32 j, .i32 i, .i32 len, .i32 ptr]
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
  have helemI : (elemAddr ptr i).toNat = ptr.toNat + 8 * i.toNat := by
    unfold elemAddr
    rw [UInt32.toNat_add, UInt32.toNat_mul]
    simp only [show (8 : UInt32).toNat = 8 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have helemJ : (elemAddr ptr j).toNat = ptr.toNat + 8 * j.toNat := by
    unfold elemAddr
    rw [UInt32.toNat_add, UInt32.toNat_mul]
    simp only [show (8 : UInt32).toNat = 8 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hpg_a : (elemAddr ptr i).toNat + 8 ≤ st.mem.pages * 65536 := by
    rw [helemI]; omega
  have hpg_b : (elemAddr ptr j).toNat + 8 ≤ st.mem.pages * 65536 := by
    rw [helemJ]; omega
  have hge_a : (1048560 : Nat) ≤ (elemAddr ptr i).toNat := by rw [helemI]; omega
  have hge_b : (1048560 : Nat) ≤ (elemAddr ptr j).toNat := by rw [helemJ]; omega
  have hdisj : elemAddr ptr i = elemAddr ptr j ∨
               (elemAddr ptr i).toNat + 8 ≤ (elemAddr ptr j).toNat ∨
               (elemAddr ptr j).toNat + 8 ≤ (elemAddr ptr i).toNat := by
    rcases Nat.lt_or_ge i.toNat j.toNat with h | h
    · right; left; rw [helemI, helemJ]; omega
    · rcases Nat.eq_or_lt_of_le h with heq | hlt
      · left; apply UInt32.toNat.inj; rw [helemI, helemJ]; omega
      · right; right; rw [helemI, helemJ]; omega
  -- Call func2 and build the exec trace through func1's nested blocks
  obtain ⟨N2, hN2⟩ := func2_terminates env st (elemAddr ptr i) (elemAddr ptr j)
      hg0 (by omega) hpg_a hpg_b hge_a hge_b hdisj
  obtain ⟨_, st2, hrun2, hpost2⟩ := hN2 N2 le_rfl
  obtain ⟨hrs2, hglob2, hpages2, hrA2, hrB2, hother2⟩ := hpost2
  subst hrs2
  have himp₁ : «module».imports[1]? = none := rfl
  have hf₁ : «module».funcs[1 - «module».imports.length]? = some func1Def := rfl
  have hrun2_ext : run (N2 + 51) «module» 2 st
      [.i32 (elemAddr ptr j), .i32 (elemAddr ptr i)] env = .Success [] st2 :=
    (run_fuel_mono (by omega) (by rw [hrun2]; intro h; cases h)).trans hrun2
  -- Connect shl-computed addresses to elemAddr
  have haddr_i : (i : UInt32) <<< (3 : UInt32) + ptr = elemAddr ptr i := by
    unfold elemAddr
    apply UInt32.toNat.inj
    simp only [UInt32.toNat_add, UInt32.toNat_shiftLeft,
               show (3 : UInt32).toNat = 3 from rfl, Nat.shiftLeft_eq,
               UInt32.toNat_mul, show (8 : UInt32).toNat = 8 from rfl,
               show (3 : Nat) % 32 = 3 from rfl, show (2 : Nat) ^ 3 = 8 from rfl]
    omega
  have haddr_j : (j : UInt32) <<< (3 : UInt32) + ptr = elemAddr ptr j := by
    unfold elemAddr
    apply UInt32.toNat.inj
    simp only [UInt32.toNat_add, UInt32.toNat_shiftLeft,
               show (3 : UInt32).toNat = 3 from rfl, Nat.shiftLeft_eq,
               UInt32.toNat_mul, show (8 : UInt32).toNat = 8 from rfl,
               show (3 : Nat) % 32 = 3 from rfl, show (2 : Nat) ^ 3 = 8 from rfl]
    omega
  have hrun2_shl : run (N2 + 51) «module» 2 st
      [.i32 ((j : UInt32) <<< (3 : UInt32) + ptr),
       .i32 ((i : UInt32) <<< (3 : UInt32) + ptr)] env = .Success [] st2 := by
    rw [haddr_j, haddr_i]; exact hrun2_ext
  -- Exec trace: three nested blocks (happy path) + rest ending in call 2 + ret
  have hexec₁ : exec (N2 + 53) «module» st
      (func1Def.toLocals ([.i32 (1048604 : UInt32), .i32 j, .i32 i, .i32 len, .i32 ptr].take
        func1Def.numParams).reverse)
      func1Def.body env = .Return st2 [] := by
    show exec (N2 + 53) «module» st
      { params := [.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 (1048604 : UInt32)],
        locals := [.i32 (0 : UInt32)], values := [] }
      func1 env = .Return st2 []
    simp only [func1]
    conv_lhs => simp [exec, execOne.eq_def, Locals.get, Locals.set?, hi, hj]
    rw [hrun2_shl]
  apply TerminatesWith.of_run (N2 + 53) [] st2
  · rw [run_eq himp₁]
    simp only [hf₁, show func1Def.results.length = 0 from rfl,
               show ([.i32 (1048604 : UInt32), .i32 j, .i32 i, .i32 len, .i32 ptr] : List Value).drop
                 func1Def.numParams = [] from rfl,
               List.take_zero, List.nil_append, hexec₁]
  · exact ⟨rfl, hglob2, hpages2, hrA2, hrB2, hother2⟩

-- func0: simple wrapper that calls func1
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
  obtain ⟨N1, hN1⟩ := func1_terminates_sw env st ptr len i j hi hj hpg hpages_bound hptr hg0
  obtain ⟨vs1, st1, hrun1, hpost1⟩ := hN1 N1 le_rfl
  obtain ⟨hrs1, hglob1, hpages1, hrA1, hrB1, hother1⟩ := hpost1
  subst hrs1
  have hrun_ext : run (N1 + 8) «module» 1 st
      [.i32 (1048604 : UInt32), .i32 j, .i32 i, .i32 len, .i32 ptr] env
      = .Success [] st1 :=
    (run_fuel_mono (by omega) (by rw [hrun1]; intro h; cases h)).trans hrun1
  -- trace through func0's body: 5 simple pushes then call 1 then ret
  have hexec : exec (N1 + 9) «module» st
      (func0Def.toLocals ([.i32 j, .i32 i, .i32 len, .i32 ptr].take func0Def.numParams).reverse)
      func0Def.body env = .Return st1 [] := by
    show exec (N1 + 9) «module» st
      { params := [.i32 ptr, .i32 len, .i32 i, .i32 j], locals := [], values := [] }
      [.localGet 0, .localGet 1, .localGet 2, .localGet 3,
       .const (1048604 : UInt32), .call 1, .ret] env = .Return st1 []
    conv_lhs => simp [exec, execOne.eq_def, Locals.get]
    rw [hrun_ext]
  apply TerminatesWith.of_run (N1 + 9) [] st1
  · rw [run_eq himp]
    simp only [hf, show func0Def.results.length = 0 from rfl,
               show ([.i32 j, .i32 i, .i32 len, .i32 ptr] : List Value).drop func0Def.numParams = [] from rfl,
               List.take_zero, List.nil_append, hexec]
  · exact ⟨rfl, hglob1, hpages1, hrA1, hrB1, hother1⟩

/-! ## Top-level spec -/

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
  -- func3 spills ptr and len onto the shadow stack
  obtain ⟨N3, hN3⟩ := func3_terminates env stg ptr len hpg3
  obtain ⟨_, st3, hrun3, hpost3⟩ := hN3 N3 le_rfl
  obtain ⟨hrs3, hglob3, hpages3, hread3_1568, hread3_1572, hread3_ne⟩ := hpost3
  subst hrs3
  -- Derive global0 = 1048560 in st3 (func3 preserved globals; globals is a List)
  have hg0_3 : st3.globals.globals[0]? = some (.i32 (1048560 : UInt32)) := by
    rw [hglob3]
    simp only [stg]
    match hnn : st.globals.globals with
    | [] => simp [hnn] at hg0
    | _ :: _ => simp [List.set]
  -- func0 performs the actual swap on the loaded ptr/len
  have hst3_pages : st3.mem.pages = st.mem.pages := by rw [hpages3]
  have hpg_st3 : ¬ (st3.mem.pages * 65536 < (1048576 : Nat)) := by
    have h1 : st3.mem.pages * 65536 = st.mem.pages * 65536 := by rw [hst3_pages]
    have h2 : (1048576 : Nat) ≤ st.mem.pages * 65536 := hpg3
    omega
  have hpg_st3_lo : ¬ (st3.mem.pages * 65536 < (1048572 : Nat)) := by
    have h1 : st3.mem.pages * 65536 = st.mem.pages * 65536 := by rw [hst3_pages]
    have h2 : (1048576 : Nat) ≤ st.mem.pages * 65536 := hpg3
    omega
  obtain ⟨N0, hN0⟩ := func0_terminates_sw env st3 ptr len i j hi hj
      (by rw [hst3_pages]; exact hbound)
      (by rw [hst3_pages]; exact hpages_bound)
      hptr hg0_3
  obtain ⟨_, st0, hrun0, hpost0⟩ := hN0 N0 le_rfl
  obtain ⟨hrs0, hglob0, hpages0, hrA0, hrB0, hother0⟩ := hpost0
  subst hrs0
  have hg0_st0 : st0.globals.globals[0]? = some (.i32 (1048560 : UInt32)) := hglob0 ▸ hg0_3
  -- Lift runs to the shared fuel level
  have hrun3_ext : run (N3 + N0 + 14) «module» 3 stg
      [.i32 (1048652 : UInt32), .i32 len, .i32 ptr, .i32 (1048568 : UInt32)] env
      = .Success [] st3 :=
    (run_fuel_mono (f₁ := N3) (f₂ := N3 + N0 + 14)
      (by omega) (by rw [hrun3]; intro h; cases h)).trans hrun3
  have hrun0_ext : run (N3 + N0 + 14) «module» 0 st3
      [.i32 j, .i32 i, .i32 len, .i32 ptr] env
      = .Success [] st0 :=
    (run_fuel_mono (f₁ := N0) (f₂ := N3 + N0 + 14)
      (by omega) (by rw [hrun0]; intro h; cases h)).trans hrun0
  -- Connect load32 addresses to func3's spilled values
  have hread_len : st3.mem.read32 (1048572 : UInt32) = len := hread3_1572
  have hread_ptr : st3.mem.read32 (1048568 : UInt32) = ptr := hread3_1568
  -- Helper for helemI/helemJ/helemK proofs
  have helem_toNat : ∀ k : UInt32, k < len →
      (elemAddr ptr k).toNat = ptr.toNat + 8 * k.toNat := by
    intro k hk
    have hk_nat : k.toNat < len.toNat := hk
    unfold elemAddr
    simp only [UInt32.toNat_add, UInt32.toNat_mul,
               show (8 : UInt32).toNat = 8 from rfl]
    omega
  have helemI := helem_toNat i hi
  have helemJ := helem_toNat j hj
  -- Final store after restoring global0 = 1048576
  let stf : Store Unit :=
    { st0 with globals := { st0.globals with globals := st0.globals.globals.set 0 (.i32 1048576) } }
  -- Exec trace for func4: globalGet/sub/set, func3 call, load32s, func0 call, globalSet, ret
  have hexec₄ : exec (N3 + N0 + 15) «module» st
      (func4Def.toLocals ([.i32 j, .i32 i, .i32 len, .i32 ptr].take func4Def.numParams).reverse)
      func4Def.body env = .Return stf [] := by
    show exec (N3 + N0 + 15) «module» st
      { params := [.i32 ptr, .i32 len, .i32 i, .i32 j],
        locals := [.i32 (0 : UInt32), .i32 (0 : UInt32), .i32 (0 : UInt32)], values := [] }
      func4 env = .Return stf []
    simp only [func4]
    -- Phase 1: reduce from start up to call 3
    conv_lhs => simp [exec, execOne.eq_def, Locals.get, Locals.set?, hg0, stg]
    rw [hrun3_ext]
    -- Phase 2: reduce from after call 3 up to call 0
    conv_lhs => simp [exec, execOne.eq_def, Locals.get, Locals.set?, hread_len, hread_ptr,
                      hpg_st3, hpg_st3_lo]
    rw [hrun0_ext]
    -- Phase 3: reduce globalSet 0 = 1048576 + ret
    simp [hg0_st0, stf]
  apply TerminatesWith.of_run (N3 + N0 + 15) [] stf
  · rw [run_eq himp₄]
    simp only [hf₄, show func4Def.results.length = 0 from rfl,
               show ([.i32 j, .i32 i, .i32 len, .i32 ptr] : List Value).drop func4Def.numParams = [] from rfl,
               List.take_zero, List.nil_append, hexec₄]
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · -- stf.mem.read64 (elemAddr ptr i) = st.mem.read64 (elemAddr ptr j)
      -- stf.mem = st0.mem (globalSet only changes globals)
      -- st0 got: read64 (elemAddr ptr i) = st3.mem.read64 (elemAddr ptr j)  [hrA0]
      -- st3 got: read64 (elemAddr ptr j) = stg.mem.read64 (elemAddr ptr j)  [hread3_ne]
      -- stg.mem = st.mem  [globals-only change]
      rw [hrA0, hread3_ne (elemAddr ptr j) (by rw [helemJ]; omega)]
    · -- stf.mem.read64 (elemAddr ptr j) = st.mem.read64 (elemAddr ptr i)
      rw [hrB0, hread3_ne (elemAddr ptr i) (by rw [helemI]; omega)]
    · -- ∀ k < len, k ≠ i, k ≠ j → stf.mem.read64 (elemAddr ptr k) = st.mem.read64 (elemAddr ptr k)
      intro k hk hki hkj
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

end Project.SwapElements.SwapSepLogic
