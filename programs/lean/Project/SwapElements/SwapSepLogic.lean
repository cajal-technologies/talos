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

open Iris Wasm Wasm.SepLogic Std LawfulPartialMap Project.SwapElements.Spec

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

Call chain: func4 → func0 → func1 → func2.
Each is proved through the iris-lean pipeline (wasm_heap_adequacy +
per-instruction iProp rules) and composed via wp_wasm_prop_call.

Key memory facts after the swap:
  final_mem = (st.mem
    .write32(1048568, ptr)         -- func3: ptr spill
    .write32(1048572, len)         -- func3: len spill
    .write64(1048552, vA)          -- func2: temp = *ptr_a
    .write64(ptr + 8*i, vB)       -- func2: *ptr_a = *ptr_b
    .write64(ptr + 8*j, vA))      -- func2: *ptr_b = temp
  where vA = st.mem.read64(ptr + 8*i), vB = st.mem.read64(ptr + 8*j).

The framing lemmas show that addresses ≥ 1048576 other than ptr+8*i and ptr+8*j
are unchanged by all these writes.

Spec gap: SwapElementsSpec does not require st.globals.globals[0]? = some (.i32 1048576).
Without that precondition, func4's globalGet 0 may trap and TerminatesWith is false
for those stores. The spec now includes the global0 and pages-bound preconditions,
added because func4's globalGet 0 would otherwise trap on arbitrary stores. -/

-- func3 spills ptr/len into the 8-byte slot at [1048568, 1048575]
-- body: write32(1048572, len) then write32(1048568, ptr)
set_option maxHeartbeats 800000000 in
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
    have hbds1 : ¬(st.mem.pages * 65536 < 1048576) := by omega
    have hbds2 : ¬(st.mem.pages * 65536 < 1048572) := by omega
    refine ⟨1, ?_⟩
    suffices h : exec 1 «module» st
        (func3Def.toLocals ([.i32 (1048652 : UInt32), .i32 len, .i32 ptr,
                             .i32 (1048568 : UInt32)].take func3Def.numParams).reverse)
        func3Def.body env = .Return {st with mem := m₂} [] by
      simp only [h]; exact ⟨trivial, trivial, hpages, hread_1568, hread_1572, hread_ne⟩
    show exec 1 «module» st
      { params := [.i32 (1048568 : UInt32), .i32 ptr, .i32 len, .i32 (1048652 : UInt32)],
        locals := [], values := [] }
      [.localGet 0, .localGet 2, .store32 (4 : UInt32),
       .localGet 0, .localGet 1, .store32 (0 : UInt32), .ret] env = .Return {st with mem := m₂} []
    conv_lhs =>
      simp [exec, execOne.eq_def, Locals.get, Locals.set?, Mem.write32_pages,
            if_neg hbds1, if_neg hbds2]
    rfl
  obtain ⟨fuel₀, hwp_fuel⟩ := hwp
  have hresults : func3Def.results.length = 0 := rfl
  have hcr : ([.i32 (1048652 : UInt32), .i32 len, .i32 ptr,
               .i32 (1048568 : UInt32)] : List Value).drop func3Def.numParams = [] := rfl
  cases hexec : exec fuel₀ «module» st
      (func3Def.toLocals ([.i32 (1048652 : UInt32), .i32 len, .i32 ptr,
                           .i32 (1048568 : UInt32)].take func3Def.numParams).reverse)
      func3Def.body env with
  | Fallthrough st' s' =>
    rw [hexec] at hwp_fuel; dsimp only at hwp_fuel
    exact TerminatesWith.of_run fuel₀ [] st'
      (by rw [run_eq himp]; simp [hf, hexec, hresults, hcr]) hwp_fuel
  | Return st' vals =>
    rw [hexec] at hwp_fuel; dsimp only at hwp_fuel
    exact TerminatesWith.of_run fuel₀ [] st'
      (by rw [run_eq himp]; simp [hf, hexec, hresults, hcr]) (hwp_fuel.1 ▸ hwp_fuel)
  | Break n st' s' => simp only [hexec] at hwp_fuel
  | Trap st' msg => simp only [hexec] at hwp_fuel
  | Invalid msg => simp only [hexec] at hwp_fuel
  | OutOfFuel => simp only [hexec] at hwp_fuel
  | ReturnCall fid st' vs => simp only [hexec] at hwp_fuel
  | Throwing tag targs st' s' => simp only [hexec] at hwp_fuel

-- func2: the actual swap via scratch at 1048552 (global0 = 1048560 at call time)
set_option maxHeartbeats 800000000 in
private theorem func2_terminates (env : HostEnv Unit) (st : Store Unit)
    (ptr_a ptr_b : UInt32)
    (hg0 : st.globals.globals[0]? = some (.i32 (1048560 : UInt32)))
    (hpg_scratch : (1048560 : Nat) ≤ st.mem.pages * 65536)
    (hpg_a : ptr_a.toNat + 8 ≤ st.mem.pages * 65536)
    (hpg_b : ptr_b.toNat + 8 ≤ st.mem.pages * 65536)
    -- ptr_a and ptr_b are both above the scratch region [1048544,1048559]
    (hge_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hge_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (hpages_bound : st.mem.pages * 65536 ≤ 4294967296)
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
    -- Scratch address: sp (1048560) - 16 + 8 = 1048552
    let scr : UInt32 := 1048552
    let vA : UInt64 := st.mem.read64 ptr_a
    let vB : UInt64 := st.mem.read64 ptr_b
    let vS : UInt64 := st.mem.read64 scr
    -- Memory after each store64 instruction
    let m₁ := st.mem.write64 scr vA
    let m₂ := m₁.write64 ptr_a vB
    let m₃ := m₂.write64 ptr_b vA
    -- scr arithmetic
    have hscr_nat : scr.toNat = 1048552 := rfl
    have hscr_lt_a : scr.toNat + 8 ≤ ptr_a.toNat := by omega
    have hscr_lt_b : scr.toNat + 8 ≤ ptr_b.toNat := by omega
    -- Bounds for execOne trap checks
    have hbds_scratch : ¬(st.mem.pages * 65536 < 1048560) := by omega
    have hbds_a : ¬(st.mem.pages * 65536 < ptr_a.toNat + 8) := by omega
    have hbds_b : ¬(st.mem.pages * 65536 < ptr_b.toNat + 8) := by omega
    -- Pages invariant
    have hpages : m₃.pages = st.mem.pages := rfl
    rcases hdisj with rfl | hlt | hlt
    · -- rfl case: ptr_a = ptr_b (swap is a no-op)
      -- vB = vA, m₂ = m₁.write64 ptr_a vA, m₃ = m₂.write64 ptr_a vA
      have hm₁_pa : m₁.read64 ptr_a = vA := by
        apply read64_of_digits; intro i hi
        rw [write64_bytes_ne st.mem scr vA (ptr_a.toNat + i) (Or.inr (by omega))]
        exact (byte64_read64 st.mem ptr_a i hi).symm
      have hread_a : m₃.read64 ptr_a = vA := by
        apply read64_of_digits; intro i hi
        exact write64_byte m₂ ptr_a vA i hi
      have hm₂_scr : m₂.read64 scr = vA := by
        apply read64_of_digits; intro i hi
        rw [write64_bytes_ne m₁ ptr_a vA (scr.toNat + i) (Or.inl (by omega))]
        exact write64_byte st.mem scr vA i hi
      refine ⟨1, ?_⟩
      suffices h : exec 1 «module» st
          (func2Def.toLocals ([.i32 ptr_a, .i32 ptr_a].take func2Def.numParams).reverse)
          func2Def.body env = .Return { st with mem := m₃ } [] by
        simp only [h]
        exact ⟨trivial, trivial, hpages, hread_a, hread_a, fun a h1 h2 h3 => by
          apply read64_of_digits; intro i hi
          rw [write64_bytes_ne m₂ ptr_a vA (a.toNat + i)
                (by rcases h2 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
          rw [write64_bytes_ne m₁ ptr_a vA (a.toNat + i)
                (by rcases h1 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
          rw [write64_bytes_ne st.mem scr vA (a.toNat + i)
                (by rcases h3 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
          exact (byte64_read64 st.mem a i hi).symm⟩
      show exec 1 «module» st
          { params := [.i32 ptr_a, .i32 ptr_a], locals := [.i32 (0 : UInt32)], values := [] }
          [.globalGet 0, .const (16 : UInt32), .sub, .localSet 2, .localGet 2, .localGet 0,
           .load64 (0 : UInt32), .store64 (8 : UInt32), .localGet 0, .localGet 1,
           .load64 (0 : UInt32), .store64 (0 : UInt32), .localGet 1, .localGet 2,
           .load64 (8 : UInt32), .store64 (0 : UInt32), .ret] env
          = .Return { st with mem := m₃ } []
      -- Provide reads in expanded form so simp can match the inlined terms after exec unfolding
      have hm₁_pa_exp : (st.mem.write64 (1048552 : UInt32) (st.mem.read64 ptr_a)).read64 ptr_a =
          st.mem.read64 ptr_a := hm₁_pa
      have hm₂_scr_exp : ((st.mem.write64 (1048552 : UInt32) (st.mem.read64 ptr_a)).write64
          ptr_a (st.mem.read64 ptr_a)).read64 (1048552 : UInt32) = st.mem.read64 ptr_a := hm₂_scr
      conv_lhs =>
        simp [exec, execOne.eq_def, Locals.get, Locals.set?,
              hg0, Mem.write64_pages, UInt32.add_zero,
              if_neg hbds_scratch, if_neg hbds_a,
              hm₁_pa_exp, hm₂_scr_exp]
    · -- hlt case 1: ptr_a.toNat + 8 ≤ ptr_b.toNat
      let σ₀ : WasmHeapMap (Option UInt8) :=
        insert (insert (insert (insert (insert (insert (insert (insert
        (insert (insert (insert (insert (insert (insert (insert (insert
        (insert (insert (insert (insert (insert (insert (insert (insert
          (∅ : WasmHeapMap (Option UInt8))
          scr (some (byte64 vS 0))) (scr + 1) (some (byte64 vS 1)))
          (scr + 2) (some (byte64 vS 2))) (scr + 3) (some (byte64 vS 3)))
          (scr + 4) (some (byte64 vS 4))) (scr + 5) (some (byte64 vS 5)))
          (scr + 6) (some (byte64 vS 6))) (scr + 7) (some (byte64 vS 7)))
          ptr_a (some (byte64 vA 0))) (ptr_a + 1) (some (byte64 vA 1)))
          (ptr_a + 2) (some (byte64 vA 2))) (ptr_a + 3) (some (byte64 vA 3)))
          (ptr_a + 4) (some (byte64 vA 4))) (ptr_a + 5) (some (byte64 vA 5)))
          (ptr_a + 6) (some (byte64 vA 6))) (ptr_a + 7) (some (byte64 vA 7)))
          ptr_b (some (byte64 vB 0))) (ptr_b + 1) (some (byte64 vB 1)))
          (ptr_b + 2) (some (byte64 vB 2))) (ptr_b + 3) (some (byte64 vB 3)))
          (ptr_b + 4) (some (byte64 vB 4))) (ptr_b + 5) (some (byte64 vB 5)))
          (ptr_b + 6) (some (byte64 vB 6))) (ptr_b + 7) (some (byte64 vB 7))
      have hagree₀ : heapAgreesWithMem σ₀ st.mem := by
        intro addr v hget
        simp only [σ₀, get?_insert, get?_empty] at hget
        split_ifs at hget <;>
          first
          | exact absurd hget (by simp)
          | (simp only [Option.some.injEq] at hget
             subst_vars
             first
             | exact (byte64_read64 st.mem scr _ (by omega)).symm
             | exact (byte64_read64 st.mem ptr_a _ (by omega)).symm
             | exact (byte64_read64 st.mem ptr_b _ (by omega)).symm
             | (rw [toNat_add_ofNat _ _ (by omega)]
                first
                | exact (byte64_read64 st.mem scr _ (by omega)).symm
                | exact (byte64_read64 st.mem ptr_a _ (by omega)).symm
                | exact (byte64_read64 st.mem ptr_b _ (by omega)).symm))
      have hg00 : get? σ₀ scr = some (some (byte64 vS 0)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg01 : get? σ₀ (scr + 1) = some (some (byte64 vS 1)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg02 : get? σ₀ (scr + 2) = some (some (byte64 vS 2)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg03 : get? σ₀ (scr + 3) = some (some (byte64 vS 3)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg04 : get? σ₀ (scr + 4) = some (some (byte64 vS 4)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg05 : get? σ₀ (scr + 5) = some (some (byte64 vS 5)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg06 : get? σ₀ (scr + 6) = some (some (byte64 vS 6)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg07 : get? σ₀ (scr + 7) = some (some (byte64 vS 7)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg08 : get? σ₀ ptr_a = some (some (byte64 vA 0)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg09 : get? σ₀ (ptr_a + 1) = some (some (byte64 vA 1)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg10 : get? σ₀ (ptr_a + 2) = some (some (byte64 vA 2)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg11 : get? σ₀ (ptr_a + 3) = some (some (byte64 vA 3)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg12 : get? σ₀ (ptr_a + 4) = some (some (byte64 vA 4)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg13 : get? σ₀ (ptr_a + 5) = some (some (byte64 vA 5)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg14 : get? σ₀ (ptr_a + 6) = some (some (byte64 vA 6)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg15 : get? σ₀ (ptr_a + 7) = some (some (byte64 vA 7)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg16 : get? σ₀ ptr_b = some (some (byte64 vB 0)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg17 : get? σ₀ (ptr_b + 1) = some (some (byte64 vB 1)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg18 : get? σ₀ (ptr_b + 2) = some (some (byte64 vB 2)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg19 : get? σ₀ (ptr_b + 3) = some (some (byte64 vB 3)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg20 : get? σ₀ (ptr_b + 4) = some (some (byte64 vB 4)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg21 : get? σ₀ (ptr_b + 5) = some (some (byte64 vB 5)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg22 : get? σ₀ (ptr_b + 6) = some (some (byte64 vB 6)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg23 : get? σ₀ (ptr_b + 7) = some (some (byte64 vB 7)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      exact wasm_heap_adequacy_with_mem «module» st
          (func2Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func2Def.numParams).reverse)
          func2Def.body env _ σ₀ hagree₀ fun [_inst : WasmHeapGS] => by
        iintro Hbig
        -- Peel 24 tokens from bigSepM
        icases bigSepM_delete hg00 $$ Hbig with ⟨Hs0, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg01) $$ Hbig with ⟨Hs1, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg02) $$ Hbig with ⟨Hs2, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg03) $$ Hbig with ⟨Hs3, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg04) $$ Hbig with ⟨Hs4, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg05) $$ Hbig with ⟨Hs5, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg06) $$ Hbig with ⟨Hs6, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg07) $$ Hbig with ⟨Hs7, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg08) $$ Hbig with ⟨Ha0, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg09) $$ Hbig with ⟨Ha1, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg10) $$ Hbig with ⟨Ha2, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg11) $$ Hbig with ⟨Ha3, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg12) $$ Hbig with ⟨Ha4, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg13) $$ Hbig with ⟨Ha5, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg14) $$ Hbig with ⟨Ha6, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg15) $$ Hbig with ⟨Ha7, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg16) $$ Hbig with ⟨Hb0, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg17) $$ Hbig with ⟨Hb1, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg18) $$ Hbig with ⟨Hb2, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg19) $$ Hbig with ⟨Hb3, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg20) $$ Hbig with ⟨Hb4, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg21) $$ Hbig with ⟨Hb5, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg22) $$ Hbig with ⟨Hb6, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg23) $$ Hbig with ⟨Hb7, _⟩
        -- Combine 8 tokens into pointsTo_u64 for each region
        ihave HS : pointsTo_u64 scr vS $$ [Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7]
        · simp only [pointsTo_u64]
          isplitl [Hs0]; · iexact Hs0
          isplitl [Hs1]; · iexact Hs1
          isplitl [Hs2]; · iexact Hs2
          isplitl [Hs3]; · iexact Hs3
          isplitl [Hs4]; · iexact Hs4
          isplitl [Hs5]; · iexact Hs5
          isplitl [Hs6]; · iexact Hs6
          iexact Hs7
        ihave HA : pointsTo_u64 ptr_a vA $$ [Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7]
        · simp only [pointsTo_u64]
          isplitl [Ha0]; · iexact Ha0
          isplitl [Ha1]; · iexact Ha1
          isplitl [Ha2]; · iexact Ha2
          isplitl [Ha3]; · iexact Ha3
          isplitl [Ha4]; · iexact Ha4
          isplitl [Ha5]; · iexact Ha5
          isplitl [Ha6]; · iexact Ha6
          iexact Ha7
        ihave HB : pointsTo_u64 ptr_b vB $$ [Hb0 Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7]
        · simp only [pointsTo_u64]
          isplitl [Hb0]; · iexact Hb0
          isplitl [Hb1]; · iexact Hb1
          isplitl [Hb2]; · iexact Hb2
          isplitl [Hb3]; · iexact Hb3
          isplitl [Hb4]; · iexact Hb4
          isplitl [Hb5]; · iexact Hb5
          isplitl [Hb6]; · iexact Hb6
          iexact Hb7
        -- Step through all 17 instructions using wp_wasm_F unfolding
        -- Inst 1: globalGet 0
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁ %hagree₁ Hσ₁
        imodintro
        iexists σ₁, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (1048560 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get, hg0])
        isplitl []; · exact BI.pure_intro hagree₁
        isplitl [Hσ₁]; · iexact Hσ₁
        -- Inst 2: const 16
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₂ %hagree₂ Hσ₂
        imodintro
        iexists σ₂, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (1048560 : UInt32), .i32 (16 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₂
        isplitl [Hσ₂]; · iexact Hσ₂
        -- Inst 3: sub
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₃ %hagree₃ Hσ₃
        imodintro
        iexists σ₃, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₃
        isplitl [Hσ₃]; · iexact Hσ₃
        -- Inst 4: localSet 2
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₄ %hagree₄ Hσ₄
        imodintro
        iexists σ₄, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get, Locals.set?])
        isplitl []; · exact BI.pure_intro hagree₄
        isplitl [Hσ₄]; · iexact Hσ₄
        -- Inst 5: localGet 2
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₅ %hagree₅ Hσ₅
        imodintro
        iexists σ₅, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₅
        isplitl [Hσ₅]; · iexact Hσ₅
        -- Inst 6: localGet 0
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₆ %hagree₆ Hσ₆
        imodintro
        iexists σ₆, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 (1048544 : UInt32), .i32 ptr_a] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₆
        isplitl [Hσ₆]; · iexact Hσ₆
        -- Inst 7: load64 0 at ptr_a → reads vA
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₇ %hagree₇ Hσ₇
        imod (wp_iProp_load64 hagree₇ (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [Hσ₇ HA] with ⟨Hσ₇, HA, %heq_a⟩
        imodintro
        iexists σ₇, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 (1048544 : UInt32), .i64 vA] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, if_neg hbds_a, UInt32.add_zero, heq_a])
        isplitl []; · exact BI.pure_intro hagree₇
        isplitl [Hσ₇]; · iexact Hσ₇
        -- Inst 8: store64 8 at 1048544+8=scr with value vA
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₈ %hagree₈ Hσ₈
        imod (wp_iProp_store64 (v_new := vA) hagree₈
          (show scr.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [Hσ₈ HS] with
          ⟨%σ₈', %hagree₈', Hσ₈', HS'⟩
        imodintro
        iexists σ₈', { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, if_neg hbds_scratch,
                  show (1048544 : UInt32) + 8 = scr from rfl])
        isplitl []; · exact BI.pure_intro hagree₈'
        isplitl [Hσ₈']; · iexact Hσ₈'
        -- Inst 9: localGet 0
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₉ %hagree₉ Hσ₉
        imodintro
        iexists σ₉, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_a] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₉
        isplitl [Hσ₉]; · iexact Hσ₉
        -- Inst 10: localGet 1
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₀ %hagree₁₀ Hσ₁₀
        imodintro
        iexists σ₁₀, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_a, .i32 ptr_b] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₀
        isplitl [Hσ₁₀]; · iexact Hσ₁₀
        -- Inst 11: load64 0 at ptr_b from m₁ → reads vB
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₁ %hagree₁₁ Hσ₁₁
        imod (wp_iProp_load64 hagree₁₁ (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [Hσ₁₁ HB] with ⟨Hσ₁₁, HB, %heq_b⟩
        imodintro
        iexists σ₁₁, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_a, .i64 vB] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, Mem.write64_pages,
                  if_neg hbds_b, UInt32.add_zero, heq_b])
        isplitl []; · exact BI.pure_intro hagree₁₁
        isplitl [Hσ₁₁]; · iexact Hσ₁₁
        -- Inst 12: store64 0 at ptr_a from m₁ with value vB
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₂ %hagree₁₂ Hσ₁₂
        imod (wp_iProp_store64 (v_new := vB) hagree₁₂
          (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [Hσ₁₂ HA] with
          ⟨%σ₁₂', %hagree₁₂', Hσ₁₂', HA'⟩
        imodintro
        iexists σ₁₂', { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, Mem.write64_pages,
                  if_neg hbds_a, UInt32.add_zero])
        isplitl []; · exact BI.pure_intro hagree₁₂'
        isplitl [Hσ₁₂']; · iexact Hσ₁₂'
        -- Inst 13: localGet 1
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₃ %hagree₁₃ Hσ₁₃
        imodintro
        iexists σ₁₃, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_b] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₃
        isplitl [Hσ₁₃]; · iexact Hσ₁₃
        -- Inst 14: localGet 2
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₄ %hagree₁₄ Hσ₁₄
        imodintro
        iexists σ₁₄, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_b, .i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₄
        isplitl [Hσ₁₄]; · iexact Hσ₁₄
        -- Inst 15: load64 8 at 1048544+8=scr from m₂ → reads vA
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₅ %hagree₁₅ Hσ₁₅
        imod (wp_iProp_load64 hagree₁₅ (show scr.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [Hσ₁₅ HS'] with ⟨Hσ₁₅, HS', %heq_s⟩
        imodintro
        iexists σ₁₅, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_b, .i64 vA] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, Mem.write64_pages, if_neg hbds_scratch,
                  show (1048544 : UInt32) + 8 = scr from rfl, heq_s])
        isplitl []; · exact BI.pure_intro hagree₁₅
        isplitl [Hσ₁₅]; · iexact Hσ₁₅
        -- Inst 16: store64 0 at ptr_b from m₂ with value vA
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₆ %hagree₁₆ Hσ₁₆
        imod (wp_iProp_store64 (v_new := vA) hagree₁₆
          (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [Hσ₁₆ HB] with
          ⟨%σ₁₆', %hagree₁₆', Hσ₁₆', HB'⟩
        -- Extract postcondition facts from ownership tokens using m₃ agreement
        imod (wp_iProp_load64 hagree₁₆' (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [Hσ₁₆' HA'] with ⟨Hσ_a, _, %heq_pa⟩
        imod (wp_iProp_load64 hagree₁₆' (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [Hσ_a HB'] with ⟨Hσ_b, _, %heq_pb⟩
        imodintro
        iexists σ₁₆', { st with mem := m₃ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, Mem.write64_pages,
                  if_neg hbds_b, UInt32.add_zero])
        isplitl []; · exact BI.pure_intro hagree₁₆'
        isplitl [Hσ_b]; · iexact Hσ_b
        -- Inst 17: ret
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        ipureintro
        refine ⟨rfl, rfl, hpages, heq_pa, heq_pb, fun a h1 h2 h3 => ?_⟩
        apply read64_of_digits; intro i hi
        rw [write64_bytes_ne m₂ ptr_b vA (a.toNat + i)
              (by rcases h2 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
        rw [write64_bytes_ne m₁ ptr_a vB (a.toNat + i)
              (by rcases h1 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
        rw [write64_bytes_ne st.mem scr vA (a.toNat + i)
              (by rcases h3 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
        exact (byte64_read64 st.mem a i hi).symm
    · -- hlt case 2: ptr_b.toNat + 8 ≤ ptr_a.toNat (symmetric)
      let σ₀ : WasmHeapMap (Option UInt8) :=
        insert (insert (insert (insert (insert (insert (insert (insert
        (insert (insert (insert (insert (insert (insert (insert (insert
        (insert (insert (insert (insert (insert (insert (insert (insert
          (∅ : WasmHeapMap (Option UInt8))
          scr (some (byte64 vS 0))) (scr + 1) (some (byte64 vS 1)))
          (scr + 2) (some (byte64 vS 2))) (scr + 3) (some (byte64 vS 3)))
          (scr + 4) (some (byte64 vS 4))) (scr + 5) (some (byte64 vS 5)))
          (scr + 6) (some (byte64 vS 6))) (scr + 7) (some (byte64 vS 7)))
          ptr_a (some (byte64 vA 0))) (ptr_a + 1) (some (byte64 vA 1)))
          (ptr_a + 2) (some (byte64 vA 2))) (ptr_a + 3) (some (byte64 vA 3)))
          (ptr_a + 4) (some (byte64 vA 4))) (ptr_a + 5) (some (byte64 vA 5)))
          (ptr_a + 6) (some (byte64 vA 6))) (ptr_a + 7) (some (byte64 vA 7)))
          ptr_b (some (byte64 vB 0))) (ptr_b + 1) (some (byte64 vB 1)))
          (ptr_b + 2) (some (byte64 vB 2))) (ptr_b + 3) (some (byte64 vB 3)))
          (ptr_b + 4) (some (byte64 vB 4))) (ptr_b + 5) (some (byte64 vB 5)))
          (ptr_b + 6) (some (byte64 vB 6))) (ptr_b + 7) (some (byte64 vB 7))
      have hagree₀ : heapAgreesWithMem σ₀ st.mem := by
        intro addr v hget
        simp only [σ₀, get?_insert, get?_empty] at hget
        split_ifs at hget <;>
          first
          | exact absurd hget (by simp)
          | (simp only [Option.some.injEq] at hget
             subst_vars
             first
             | exact (byte64_read64 st.mem scr _ (by omega)).symm
             | exact (byte64_read64 st.mem ptr_a _ (by omega)).symm
             | exact (byte64_read64 st.mem ptr_b _ (by omega)).symm
             | (rw [toNat_add_ofNat _ _ (by omega)]
                first
                | exact (byte64_read64 st.mem scr _ (by omega)).symm
                | exact (byte64_read64 st.mem ptr_a _ (by omega)).symm
                | exact (byte64_read64 st.mem ptr_b _ (by omega)).symm))
      have hg00 : get? σ₀ scr = some (some (byte64 vS 0)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg01 : get? σ₀ (scr + 1) = some (some (byte64 vS 1)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg02 : get? σ₀ (scr + 2) = some (some (byte64 vS 2)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg03 : get? σ₀ (scr + 3) = some (some (byte64 vS 3)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg04 : get? σ₀ (scr + 4) = some (some (byte64 vS 4)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg05 : get? σ₀ (scr + 5) = some (some (byte64 vS 5)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg06 : get? σ₀ (scr + 6) = some (some (byte64 vS 6)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg07 : get? σ₀ (scr + 7) = some (some (byte64 vS 7)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg08 : get? σ₀ ptr_a = some (some (byte64 vA 0)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg09 : get? σ₀ (ptr_a + 1) = some (some (byte64 vA 1)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg10 : get? σ₀ (ptr_a + 2) = some (some (byte64 vA 2)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg11 : get? σ₀ (ptr_a + 3) = some (some (byte64 vA 3)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg12 : get? σ₀ (ptr_a + 4) = some (some (byte64 vA 4)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg13 : get? σ₀ (ptr_a + 5) = some (some (byte64 vA 5)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg14 : get? σ₀ (ptr_a + 6) = some (some (byte64 vA 6)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg15 : get? σ₀ (ptr_a + 7) = some (some (byte64 vA 7)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg16 : get? σ₀ ptr_b = some (some (byte64 vB 0)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg17 : get? σ₀ (ptr_b + 1) = some (some (byte64 vB 1)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg18 : get? σ₀ (ptr_b + 2) = some (some (byte64 vB 2)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg19 : get? σ₀ (ptr_b + 3) = some (some (byte64 vB 3)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg20 : get? σ₀ (ptr_b + 4) = some (some (byte64 vB 4)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg21 : get? σ₀ (ptr_b + 5) = some (some (byte64 vB 5)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg22 : get? σ₀ (ptr_b + 6) = some (some (byte64 vB 6)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      have hg23 : get? σ₀ (ptr_b + 7) = some (some (byte64 vB 7)) := by
        simp only [σ₀, get?_insert, get?_empty]; split_ifs <;> first | rfl | omega
      exact wasm_heap_adequacy_with_mem «module» st
          (func2Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func2Def.numParams).reverse)
          func2Def.body env _ σ₀ hagree₀ fun [_inst : WasmHeapGS] => by
        iintro Hbig
        icases bigSepM_delete hg00 $$ Hbig with ⟨Hs0, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg01) $$ Hbig with ⟨Hs1, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg02) $$ Hbig with ⟨Hs2, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg03) $$ Hbig with ⟨Hs3, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg04) $$ Hbig with ⟨Hs4, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg05) $$ Hbig with ⟨Hs5, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg06) $$ Hbig with ⟨Hs6, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg07) $$ Hbig with ⟨Hs7, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg08) $$ Hbig with ⟨Ha0, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg09) $$ Hbig with ⟨Ha1, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg10) $$ Hbig with ⟨Ha2, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg11) $$ Hbig with ⟨Ha3, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg12) $$ Hbig with ⟨Ha4, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg13) $$ Hbig with ⟨Ha5, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg14) $$ Hbig with ⟨Ha6, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg15) $$ Hbig with ⟨Ha7, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg16) $$ Hbig with ⟨Hb0, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg17) $$ Hbig with ⟨Hb1, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg18) $$ Hbig with ⟨Hb2, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg19) $$ Hbig with ⟨Hb3, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg20) $$ Hbig with ⟨Hb4, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg21) $$ Hbig with ⟨Hb5, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg22) $$ Hbig with ⟨Hb6, Hbig⟩
        icases bigSepM_delete (by simp (discharger := omega) only [get?_delete_ne]; exact hg23) $$ Hbig with ⟨Hb7, _⟩
        ihave HS : pointsTo_u64 scr vS $$ [Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7]
        · simp only [pointsTo_u64]
          isplitl [Hs0]; · iexact Hs0
          isplitl [Hs1]; · iexact Hs1
          isplitl [Hs2]; · iexact Hs2
          isplitl [Hs3]; · iexact Hs3
          isplitl [Hs4]; · iexact Hs4
          isplitl [Hs5]; · iexact Hs5
          isplitl [Hs6]; · iexact Hs6
          iexact Hs7
        ihave HA : pointsTo_u64 ptr_a vA $$ [Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7]
        · simp only [pointsTo_u64]
          isplitl [Ha0]; · iexact Ha0
          isplitl [Ha1]; · iexact Ha1
          isplitl [Ha2]; · iexact Ha2
          isplitl [Ha3]; · iexact Ha3
          isplitl [Ha4]; · iexact Ha4
          isplitl [Ha5]; · iexact Ha5
          isplitl [Ha6]; · iexact Ha6
          iexact Ha7
        ihave HB : pointsTo_u64 ptr_b vB $$ [Hb0 Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7]
        · simp only [pointsTo_u64]
          isplitl [Hb0]; · iexact Hb0
          isplitl [Hb1]; · iexact Hb1
          isplitl [Hb2]; · iexact Hb2
          isplitl [Hb3]; · iexact Hb3
          isplitl [Hb4]; · iexact Hb4
          isplitl [Hb5]; · iexact Hb5
          isplitl [Hb6]; · iexact Hb6
          iexact Hb7
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁ %hagree₁ Hσ₁
        imodintro
        iexists σ₁, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (1048560 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get, hg0])
        isplitl []; · exact BI.pure_intro hagree₁
        isplitl [Hσ₁]; · iexact Hσ₁
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₂ %hagree₂ Hσ₂
        imodintro
        iexists σ₂, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (1048560 : UInt32), .i32 (16 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₂
        isplitl [Hσ₂]; · iexact Hσ₂
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₃ %hagree₃ Hσ₃
        imodintro
        iexists σ₃, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₃
        isplitl [Hσ₃]; · iexact Hσ₃
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₄ %hagree₄ Hσ₄
        imodintro
        iexists σ₄, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get, Locals.set?])
        isplitl []; · exact BI.pure_intro hagree₄
        isplitl [Hσ₄]; · iexact Hσ₄
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₅ %hagree₅ Hσ₅
        imodintro
        iexists σ₅, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₅
        isplitl [Hσ₅]; · iexact Hσ₅
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₆ %hagree₆ Hσ₆
        imodintro
        iexists σ₆, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 (1048544 : UInt32), .i32 ptr_a] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₆
        isplitl [Hσ₆]; · iexact Hσ₆
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₇ %hagree₇ Hσ₇
        imod (wp_iProp_load64 hagree₇ (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [Hσ₇ HA] with ⟨Hσ₇, HA, %heq_a⟩
        imodintro
        iexists σ₇, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 (1048544 : UInt32), .i64 vA] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, if_neg hbds_a, UInt32.add_zero, heq_a])
        isplitl []; · exact BI.pure_intro hagree₇
        isplitl [Hσ₇]; · iexact Hσ₇
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₈ %hagree₈ Hσ₈
        imod (wp_iProp_store64 (v_new := vA) hagree₈
          (show scr.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [Hσ₈ HS] with
          ⟨%σ₈', %hagree₈', Hσ₈', HS'⟩
        imodintro
        iexists σ₈', { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, if_neg hbds_scratch,
                  show (1048544 : UInt32) + 8 = scr from rfl])
        isplitl []; · exact BI.pure_intro hagree₈'
        isplitl [Hσ₈']; · iexact Hσ₈'
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₉ %hagree₉ Hσ₉
        imodintro
        iexists σ₉, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_a] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₉
        isplitl [Hσ₉]; · iexact Hσ₉
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₀ %hagree₁₀ Hσ₁₀
        imodintro
        iexists σ₁₀, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_a, .i32 ptr_b] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₀
        isplitl [Hσ₁₀]; · iexact Hσ₁₀
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₁ %hagree₁₁ Hσ₁₁
        imod (wp_iProp_load64 hagree₁₁ (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [Hσ₁₁ HB] with ⟨Hσ₁₁, HB, %heq_b⟩
        imodintro
        iexists σ₁₁, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_a, .i64 vB] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, Mem.write64_pages,
                  if_neg hbds_b, UInt32.add_zero, heq_b])
        isplitl []; · exact BI.pure_intro hagree₁₁
        isplitl [Hσ₁₁]; · iexact Hσ₁₁
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₂ %hagree₁₂ Hσ₁₂
        imod (wp_iProp_store64 (v_new := vB) hagree₁₂
          (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [Hσ₁₂ HA] with
          ⟨%σ₁₂', %hagree₁₂', Hσ₁₂', HA'⟩
        imodintro
        iexists σ₁₂', { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, Mem.write64_pages,
                  if_neg hbds_a, UInt32.add_zero])
        isplitl []; · exact BI.pure_intro hagree₁₂'
        isplitl [Hσ₁₂']; · iexact Hσ₁₂'
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₃ %hagree₁₃ Hσ₁₃
        imodintro
        iexists σ₁₃, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_b] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₃
        isplitl [Hσ₁₃]; · iexact Hσ₁₃
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₄ %hagree₁₄ Hσ₁₄
        imodintro
        iexists σ₁₄, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_b, .i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₄
        isplitl [Hσ₁₄]; · iexact Hσ₁₄
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₅ %hagree₁₅ Hσ₁₅
        imod (wp_iProp_load64 hagree₁₅ (show scr.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [Hσ₁₅ HS'] with ⟨Hσ₁₅, HS', %heq_s⟩
        imodintro
        iexists σ₁₅, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_b, .i64 vA] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, Mem.write64_pages, if_neg hbds_scratch,
                  show (1048544 : UInt32) + 8 = scr from rfl, heq_s])
        isplitl []; · exact BI.pure_intro hagree₁₅
        isplitl [Hσ₁₅]; · iexact Hσ₁₅
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₆ %hagree₁₆ Hσ₁₆
        imod (wp_iProp_store64 (v_new := vA) hagree₁₆
          (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [Hσ₁₆ HB] with
          ⟨%σ₁₆', %hagree₁₆', Hσ₁₆', HB'⟩
        imod (wp_iProp_load64 hagree₁₆' (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [Hσ₁₆' HA'] with ⟨Hσ_a, _, %heq_pa⟩
        imod (wp_iProp_load64 hagree₁₆' (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [Hσ_a HB'] with ⟨Hσ_b, _, %heq_pb⟩
        imodintro
        iexists σ₁₆', { st with mem := m₃ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, Mem.write64_pages,
                  if_neg hbds_b, UInt32.add_zero])
        isplitl []; · exact BI.pure_intro hagree₁₆'
        isplitl [Hσ_b]; · iexact Hσ_b
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        ipureintro
        refine ⟨rfl, rfl, hpages, heq_pa, heq_pb, fun a h1 h2 h3 => ?_⟩
        apply read64_of_digits; intro i hi
        rw [write64_bytes_ne m₂ ptr_b vA (a.toNat + i)
              (by rcases h2 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
        rw [write64_bytes_ne m₁ ptr_a vB (a.toNat + i)
              (by rcases h1 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
        rw [write64_bytes_ne st.mem scr vA (a.toNat + i)
              (by rcases h3 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
        exact (byte64_read64 st.mem a i hi).symm
  obtain ⟨fuel₀, hwp_fuel⟩ := hwp
  have hresults : func2Def.results.length = 0 := rfl
  have hcr : ([.i32 ptr_b, .i32 ptr_a] : List Value).drop func2Def.numParams = [] := rfl
  cases hexec : exec fuel₀ «module» st
      (func2Def.toLocals ([.i32 ptr_b, .i32 ptr_a].take func2Def.numParams).reverse)
      func2Def.body env with
  | Fallthrough st' s' =>
    rw [hexec] at hwp_fuel; dsimp only at hwp_fuel
    exact TerminatesWith.of_run fuel₀ [] st'
      (by rw [run_eq himp]; simp [hf, hexec, hresults, hcr]) hwp_fuel
  | Return st' vals =>
    rw [hexec] at hwp_fuel; dsimp only at hwp_fuel
    exact TerminatesWith.of_run fuel₀ [] st'
      (by rw [run_eq himp]; simp [hf, hexec, hresults, hcr]) (hwp_fuel.1 ▸ hwp_fuel)
  | Break n st' s' => simp only [hexec] at hwp_fuel
  | Trap st' msg => simp only [hexec] at hwp_fuel
  | Invalid msg => simp only [hexec] at hwp_fuel
  | OutOfFuel => simp only [hexec] at hwp_fuel
  | ReturnCall fid st' vs => simp only [hexec] at hwp_fuel
  | Throwing tag targs st' s' => simp only [hexec] at hwp_fuel

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
      hg0 (by omega) hpg_a hpg_b hge_a hge_b hpages_bound hdisj
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
               show UInt32.size = 4294967296 from rfl,
               show (3 : Nat) % 32 = 3 from rfl, show (2 : Nat) ^ 3 = 8 from rfl]
    omega
  have haddr_j : (j : UInt32) <<< (3 : UInt32) + ptr = elemAddr ptr j := by
    unfold elemAddr
    apply UInt32.toNat.inj
    simp only [UInt32.toNat_add, UInt32.toNat_shiftLeft,
               show (3 : UInt32).toNat = 3 from rfl, Nat.shiftLeft_eq,
               UInt32.toNat_mul, show (8 : UInt32).toNat = 8 from rfl,
               show UInt32.size = 4294967296 from rfl,
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

theorem swap_spec_sep : SwapElementsSpec := by
  intro env st ptr len i j hi hj hbound hpages_bound hptr hg0
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
               show (8 : UInt32).toNat = 8 from rfl,
               show UInt32.size = 4294967296 from rfl]
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
    simp [exec, execOne.eq_def, Locals.get, Locals.set?, hg0_st0, stf]
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
