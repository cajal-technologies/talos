import Project.SwapElements.Program
import Project.SwapElements.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmWP
import CodeLib.Entry
import CodeLib.RustStd.Frame

open Iris.BI.BigSepM

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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

private theorem addr_ne_intra
    {p : UInt32} {i j : UInt32}
    (hi : i.toNat < 8) (hj : j.toNat < 8)
    (hij : i.toNat ≠ j.toNat)
    (hp : p.toNat + 7 < 4294967296) :
    p + i ≠ p + j := by
  intro heq
  have := congrArg UInt32.toNat heq
  simp only [UInt32.toNat_add] at this
  rw [Nat.mod_eq_of_lt (show p.toNat + i.toNat < 4294967296 by omega),
      Nat.mod_eq_of_lt (show p.toNat + j.toNat < 4294967296 by omega)] at this
  omega

private theorem addr_ne_cross
    {p q : UInt32} {i j : UInt32}
    (hi : i.toNat < 8) (hj : j.toNat < 8)
    (h : p.toNat + 8 ≤ q.toNat ∨ q.toNat + 8 ≤ p.toNat)
    (hp : p.toNat + 7 < 4294967296)
    (hq : q.toNat + 7 < 4294967296) :
    p + i ≠ q + j := by
  intro heq
  have := congrArg UInt32.toNat heq
  simp only [UInt32.toNat_add] at this
  rw [Nat.mod_eq_of_lt (show p.toNat + i.toNat < 4294967296 by omega),
      Nat.mod_eq_of_lt (show q.toNat + j.toNat < 4294967296 by omega)] at this
  omega

private theorem addr_ne_symm {a b : UInt32} (h : a ≠ b) : b ≠ a :=
  Ne.symm h

private theorem addr_ne_cross_0r
    {p q : UInt32} {i : UInt32}
    (hi : i.toNat < 8)
    (h : p.toNat + 8 ≤ q.toNat ∨ q.toNat + 8 ≤ p.toNat)
    (hp : p.toNat + 7 < 4294967296)
    (hq : q.toNat + 7 < 4294967296) :
    p + i ≠ q := by
  intro heq
  have := congrArg UInt32.toNat heq
  simp only [UInt32.toNat_add] at this
  rw [Nat.mod_eq_of_lt (show p.toNat + i.toNat < 4294967296 by omega)] at this
  omega

private theorem addr_ne_cross_0l
    {p q : UInt32} {j : UInt32}
    (hj : j.toNat < 8)
    (h : p.toNat + 8 ≤ q.toNat ∨ q.toNat + 8 ≤ p.toNat)
    (hp : p.toNat + 7 < 4294967296)
    (hq : q.toNat + 7 < 4294967296) :
    p ≠ q + j := by
  intro heq
  have := congrArg UInt32.toNat heq
  simp only [UInt32.toNat_add] at this
  rw [Nat.mod_eq_of_lt (show q.toNat + j.toNat < 4294967296 by omega)] at this
  omega

private theorem addr_ne_cross_base
    {p q : UInt32}
    (h : p.toNat + 8 ≤ q.toNat ∨ q.toNat + 8 ≤ p.toNat) :
    p ≠ q := by
  intro heq; subst heq; omega

private theorem addr_ne_intra_0r
    {p : UInt32} {i : UInt32}
    (hi : i.toNat < 8) (hinz : i.toNat ≠ 0)
    (hp : p.toNat + 7 < 4294967296) :
    p + i ≠ p := by
  intro heq
  have := congrArg UInt32.toNat heq
  simp only [UInt32.toNat_add] at this
  rw [Nat.mod_eq_of_lt (show p.toNat + i.toNat < 4294967296 by omega)] at this
  omega

private theorem addr_ne_intra_0l
    {p : UInt32} {j : UInt32}
    (hj : j.toNat < 8) (hjnz : j.toNat ≠ 0)
    (hp : p.toNat + 7 < 4294967296) :
    p ≠ p + j :=
  addr_ne_symm (addr_ne_intra_0r hj hjnz hp)

section SwapSigmaLemmas
set_option maxHeartbeats 4000000

private def whmIns : WasmHeapMap (Option UInt8) → UInt32 → Option UInt8 → WasmHeapMap (Option UInt8) := insert

private lemma get?_whmIns_ne {m : WasmHeapMap (Option UInt8)} {k k' : UInt32} {v : Option UInt8}
    (h : k ≠ k') : get? (whmIns m k v) k' = get? m k' := by
  unfold whmIns; exact get?_insert_ne h

private lemma get?_whmIns_eq {m : WasmHeapMap (Option UInt8)} {k : UInt32} {v : Option UInt8} :
    get? (whmIns m k v) k = some v := by
  unfold whmIns; exact get?_insert_eq rfl

private lemma get?_whmIns {m : WasmHeapMap (Option UInt8)} {k k' : UInt32} {v : Option UInt8} :
    get? (whmIns m k v) k' = if k = k' then some v else get? m k' := by
  split_ifs with h
  · subst h; exact get?_whmIns_eq
  · exact get?_whmIns_ne h

private lemma ne_ptr_scr0 {ptr ptr_off : UInt32}
    (hge : (1048560 : Nat) ≤ ptr.toNat)
    (hp : ptr.toNat + 7 < 4294967296)
    (hpo : ptr_off.toNat < 8) :
    ptr + ptr_off ≠ (1048552 : UInt32) := by
  have hscr : (1048552 : UInt32).toNat = 1048552 := rfl
  intro heq
  have h := congrArg UInt32.toNat heq
  simp only [UInt32.toNat_add, hscr] at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  omega

private lemma ne_ptr_base_scr0 {ptr : UInt32}
    (hge : (1048560 : Nat) ≤ ptr.toNat) :
    ptr ≠ (1048552 : UInt32) := by
  have hscr : (1048552 : UInt32).toNat = 1048552 := rfl
  intro heq
  have h := congrArg UInt32.toNat heq
  rw [hscr] at h
  omega

private lemma ne_ptr_scr {ptr ptr_off scr_off : UInt32}
    (hge : (1048560 : Nat) ≤ ptr.toNat)
    (hp : ptr.toNat + 7 < 4294967296)
    (hpo : ptr_off.toNat < 8)
    (hso : scr_off.toNat < 8) :
    ptr + ptr_off ≠ (1048552 : UInt32) + scr_off := by
  have hscr : (1048552 : UInt32).toNat = 1048552 := rfl
  intro heq
  have h := congrArg UInt32.toNat heq
  simp only [UInt32.toNat_add, hscr] at h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

private lemma ne_ptr_base_scr {ptr scr_off : UInt32}
    (hge : (1048560 : Nat) ≤ ptr.toNat)
    (hso : scr_off.toNat < 8) :
    ptr ≠ (1048552 : UInt32) + scr_off := by
  have hscr : (1048552 : UInt32).toNat = 1048552 := rfl
  intro heq
  have h := congrArg UInt32.toNat heq
  simp only [UInt32.toNat_add, hscr] at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  omega

private def swap_σ₀ (ptr_a ptr_b : UInt32) (vA vB vS : UInt64) : WasmHeapMap (Option UInt8) :=
  whmIns (whmIns (whmIns (whmIns (whmIns (whmIns (whmIns (whmIns
  (whmIns (whmIns (whmIns (whmIns (whmIns (whmIns (whmIns (whmIns
  (whmIns (whmIns (whmIns (whmIns (whmIns (whmIns (whmIns (whmIns
    (∅ : WasmHeapMap (Option UInt8))
    (1048552 : UInt32) (some (byte64 vS 0))) ((1048552 : UInt32) + 1) (some (byte64 vS 1)))
    ((1048552 : UInt32) + 2) (some (byte64 vS 2))) ((1048552 : UInt32) + 3) (some (byte64 vS 3)))
    ((1048552 : UInt32) + 4) (some (byte64 vS 4))) ((1048552 : UInt32) + 5) (some (byte64 vS 5)))
    ((1048552 : UInt32) + 6) (some (byte64 vS 6))) ((1048552 : UInt32) + 7) (some (byte64 vS 7)))
    ptr_a (some (byte64 vA 0))) (ptr_a + 1) (some (byte64 vA 1)))
    (ptr_a + 2) (some (byte64 vA 2))) (ptr_a + 3) (some (byte64 vA 3)))
    (ptr_a + 4) (some (byte64 vA 4))) (ptr_a + 5) (some (byte64 vA 5)))
    (ptr_a + 6) (some (byte64 vA 6))) (ptr_a + 7) (some (byte64 vA 7)))
    ptr_b (some (byte64 vB 0))) (ptr_b + 1) (some (byte64 vB 1)))
    (ptr_b + 2) (some (byte64 vB 2))) (ptr_b + 3) (some (byte64 vB 3)))
    (ptr_b + 4) (some (byte64 vB 4))) (ptr_b + 5) (some (byte64 vB 5)))
    (ptr_b + 6) (some (byte64 vB 6))) (ptr_b + 7) (some (byte64 vB 7))

private theorem swap_σ₀_get_00
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (1048552 : UInt32) = some (some (byte64 vS 0)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_b hp_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_b hp_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_b hp_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_b hp_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_b hp_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_b hp_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_b hp_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr0 hscr_lt_b)]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_a hp_a (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_a hp_a (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_a hp_a (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_a hp_a (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_a hp_a (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_a hp_a (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr0 hscr_lt_a hp_a (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr0 hscr_lt_a)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) (by decide))]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_01
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) ((1048552 : UInt32) + 1) = some (some (byte64 vS 1)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_a (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_02
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) ((1048552 : UInt32) + 2) = some (some (byte64 vS 2)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_a (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_03
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) ((1048552 : UInt32) + 3) = some (some (byte64 vS 3)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_a (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_04
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) ((1048552 : UInt32) + 4) = some (some (byte64 vS 4)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_a (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_05
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) ((1048552 : UInt32) + 5) = some (some (byte64 vS 5)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_a (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_06
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) ((1048552 : UInt32) + 6) = some (some (byte64 vS 6)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_a (by decide))]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) (by decide))]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_07
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) ((1048552 : UInt32) + 7) = some (some (byte64 vS 7)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_b hp_b (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_b (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_scr hscr_lt_a hp_a (by decide) (by decide))]
  rw [get?_whmIns_ne (ne_ptr_base_scr hscr_lt_a (by decide))]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_08
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) ptr_a = some (some (byte64 vA 0)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_cross_0r (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0r (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0r (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0r (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0r (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0r (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0r (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_base (Or.comm.mp h_disj))]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_a)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_09
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_a + 1) = some (some (byte64 vA 1)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0l (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_10
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_a + 2) = some (some (byte64 vA 2)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0l (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_11
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_a + 3) = some (some (byte64 vA 3)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0l (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_12
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_a + 4) = some (some (byte64 vA 4)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0l (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_13
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_a + 5) = some (some (byte64 vA 5)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0l (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_14
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_a + 6) = some (some (byte64 vA 6)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0l (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_15
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_a + 7) = some (some (byte64 vA 7)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross (by decide) (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  rw [get?_whmIns_ne (addr_ne_cross_0l (by decide) (Or.comm.mp h_disj) hp_b hp_a)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_16
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) ptr_b = some (some (byte64 vB 0)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra_0r (by decide) (by decide) hp_b)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_17
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_b + 1) = some (some (byte64 vB 1)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_18
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_b + 2) = some (some (byte64 vB 2)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_19
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_b + 3) = some (some (byte64 vB 3)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_20
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_b + 4) = some (some (byte64 vB 4)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_21
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_b + 5) = some (some (byte64 vB 5)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_22
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_b + 6) = some (some (byte64 vB 6)) := by
  unfold swap_σ₀
  rw [get?_whmIns_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)]
  exact get?_whmIns_eq

private theorem swap_σ₀_get_23
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hscr_lt_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hscr_lt_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296) :
    get? (swap_σ₀ ptr_a ptr_b vA vB vS) (ptr_b + 7) = some (some (byte64 vB 7)) := by
  unfold swap_σ₀
  exact get?_whmIns_eq

set_option maxHeartbeats 8000000 in
private theorem swap_σ₀_hagree
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (st : Store Unit)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296)
    (hvA : vA = st.mem.read64 ptr_a)
    (hvB : vB = st.mem.read64 ptr_b)
    (hvS : vS = st.mem.read64 (1048552 : UInt32)) :
    heapAgreesWithMem (swap_σ₀ ptr_a ptr_b vA vB vS) st.mem := by
  subst hvA; subst hvB; subst hvS
  have hN1 : (1 : UInt32).toNat = 1 := rfl
  have hN2 : (2 : UInt32).toNat = 2 := rfl
  have hN3 : (3 : UInt32).toNat = 3 := rfl
  have hN4 : (4 : UInt32).toNat = 4 := rfl
  have hN5 : (5 : UInt32).toNat = 5 := rfl
  have hN6 : (6 : UInt32).toNat = 6 := rfl
  have hN7 : (7 : UInt32).toNat = 7 := rfl
  have hNscr : (1048552 : UInt32).toNat = 1048552 := rfl
  have hSz : UInt32.size = 4294967296 := rfl
  intro addr v hget
  unfold swap_σ₀ at hget
  simp only [get?_whmIns, get?_empty] at hget
  by_cases hc1 : ptr_b + 7 = addr
  · simp only [if_pos hc1, Option.some.injEq] at hget; subst_vars
    simp only [Mem.read8, UInt32.toNat_add, hN7, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
    exact (byte64_read64 st.mem _ _ (by omega)).symm
  · simp only [if_neg hc1] at hget
    by_cases hc2 : ptr_b + 6 = addr
    · simp only [if_pos hc2, Option.some.injEq] at hget; subst_vars
      simp only [Mem.read8, UInt32.toNat_add, hN6, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
      exact (byte64_read64 st.mem _ _ (by omega)).symm
    · simp only [if_neg hc2] at hget
      by_cases hc3 : ptr_b + 5 = addr
      · simp only [if_pos hc3, Option.some.injEq] at hget; subst_vars
        simp only [Mem.read8, UInt32.toNat_add, hN5, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
        exact (byte64_read64 st.mem _ _ (by omega)).symm
      · simp only [if_neg hc3] at hget
        by_cases hc4 : ptr_b + 4 = addr
        · simp only [if_pos hc4, Option.some.injEq] at hget; subst_vars
          simp only [Mem.read8, UInt32.toNat_add, hN4, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
          exact (byte64_read64 st.mem _ _ (by omega)).symm
        · simp only [if_neg hc4] at hget
          by_cases hc5 : ptr_b + 3 = addr
          · simp only [if_pos hc5, Option.some.injEq] at hget; subst_vars
            simp only [Mem.read8, UInt32.toNat_add, hN3, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
            exact (byte64_read64 st.mem _ _ (by omega)).symm
          · simp only [if_neg hc5] at hget
            by_cases hc6 : ptr_b + 2 = addr
            · simp only [if_pos hc6, Option.some.injEq] at hget; subst_vars
              simp only [Mem.read8, UInt32.toNat_add, hN2, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
              exact (byte64_read64 st.mem _ _ (by omega)).symm
            · simp only [if_neg hc6] at hget
              by_cases hc7 : ptr_b + 1 = addr
              · simp only [if_pos hc7, Option.some.injEq] at hget; subst_vars
                simp only [Mem.read8, UInt32.toNat_add, hN1, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                exact (byte64_read64 st.mem _ _ (by omega)).symm
              · simp only [if_neg hc7] at hget
                by_cases hc8 : ptr_b = addr
                · simp only [if_pos hc8, Option.some.injEq] at hget; subst_vars
                  simp only [Mem.read8]
                  exact (byte64_read64 st.mem _ 0 (by decide)).symm
                · simp only [if_neg hc8] at hget
                  by_cases hc9 : ptr_a + 7 = addr
                  · simp only [if_pos hc9, Option.some.injEq] at hget; subst_vars
                    simp only [Mem.read8, UInt32.toNat_add, hN7, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                    exact (byte64_read64 st.mem _ _ (by omega)).symm
                  · simp only [if_neg hc9] at hget
                    by_cases hc10 : ptr_a + 6 = addr
                    · simp only [if_pos hc10, Option.some.injEq] at hget; subst_vars
                      simp only [Mem.read8, UInt32.toNat_add, hN6, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                      exact (byte64_read64 st.mem _ _ (by omega)).symm
                    · simp only [if_neg hc10] at hget
                      by_cases hc11 : ptr_a + 5 = addr
                      · simp only [if_pos hc11, Option.some.injEq] at hget; subst_vars
                        simp only [Mem.read8, UInt32.toNat_add, hN5, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                        exact (byte64_read64 st.mem _ _ (by omega)).symm
                      · simp only [if_neg hc11] at hget
                        by_cases hc12 : ptr_a + 4 = addr
                        · simp only [if_pos hc12, Option.some.injEq] at hget; subst_vars
                          simp only [Mem.read8, UInt32.toNat_add, hN4, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                          exact (byte64_read64 st.mem _ _ (by omega)).symm
                        · simp only [if_neg hc12] at hget
                          by_cases hc13 : ptr_a + 3 = addr
                          · simp only [if_pos hc13, Option.some.injEq] at hget; subst_vars
                            simp only [Mem.read8, UInt32.toNat_add, hN3, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                            exact (byte64_read64 st.mem _ _ (by omega)).symm
                          · simp only [if_neg hc13] at hget
                            by_cases hc14 : ptr_a + 2 = addr
                            · simp only [if_pos hc14, Option.some.injEq] at hget; subst_vars
                              simp only [Mem.read8, UInt32.toNat_add, hN2, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                              exact (byte64_read64 st.mem _ _ (by omega)).symm
                            · simp only [if_neg hc14] at hget
                              by_cases hc15 : ptr_a + 1 = addr
                              · simp only [if_pos hc15, Option.some.injEq] at hget; subst_vars
                                simp only [Mem.read8, UInt32.toNat_add, hN1, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                                exact (byte64_read64 st.mem _ _ (by omega)).symm
                              · simp only [if_neg hc15] at hget
                                by_cases hc16 : ptr_a = addr
                                · simp only [if_pos hc16, Option.some.injEq] at hget; subst_vars
                                  simp only [Mem.read8]
                                  exact (byte64_read64 st.mem _ 0 (by decide)).symm
                                · simp only [if_neg hc16] at hget
                                  by_cases hc17 : (1048552 : UInt32) + 7 = addr
                                  · simp only [if_pos hc17, Option.some.injEq] at hget; subst_vars
                                    simp only [Mem.read8, UInt32.toNat_add, hN7, hNscr, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                                    exact (byte64_read64 st.mem (1048552:UInt32) 7 (by decide)).symm
                                  · simp only [if_neg hc17] at hget
                                    by_cases hc18 : (1048552 : UInt32) + 6 = addr
                                    · simp only [if_pos hc18, Option.some.injEq] at hget; subst_vars
                                      simp only [Mem.read8, UInt32.toNat_add, hN6, hNscr, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                                      exact (byte64_read64 st.mem (1048552:UInt32) 6 (by decide)).symm
                                    · simp only [if_neg hc18] at hget
                                      by_cases hc19 : (1048552 : UInt32) + 5 = addr
                                      · simp only [if_pos hc19, Option.some.injEq] at hget; subst_vars
                                        simp only [Mem.read8, UInt32.toNat_add, hN5, hNscr, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                                        exact (byte64_read64 st.mem (1048552:UInt32) 5 (by decide)).symm
                                      · simp only [if_neg hc19] at hget
                                        by_cases hc20 : (1048552 : UInt32) + 4 = addr
                                        · simp only [if_pos hc20, Option.some.injEq] at hget; subst_vars
                                          simp only [Mem.read8, UInt32.toNat_add, hN4, hNscr, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                                          exact (byte64_read64 st.mem (1048552:UInt32) 4 (by decide)).symm
                                        · simp only [if_neg hc20] at hget
                                          by_cases hc21 : (1048552 : UInt32) + 3 = addr
                                          · simp only [if_pos hc21, Option.some.injEq] at hget; subst_vars
                                            simp only [Mem.read8, UInt32.toNat_add, hN3, hNscr, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                                            exact (byte64_read64 st.mem (1048552:UInt32) 3 (by decide)).symm
                                          · simp only [if_neg hc21] at hget
                                            by_cases hc22 : (1048552 : UInt32) + 2 = addr
                                            · simp only [if_pos hc22, Option.some.injEq] at hget; subst_vars
                                              simp only [Mem.read8, UInt32.toNat_add, hN2, hNscr, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                                              exact (byte64_read64 st.mem (1048552:UInt32) 2 (by decide)).symm
                                            · simp only [if_neg hc22] at hget
                                              by_cases hc23 : (1048552 : UInt32) + 1 = addr
                                              · simp only [if_pos hc23, Option.some.injEq] at hget; subst_vars
                                                simp only [Mem.read8, UInt32.toNat_add, hN1, hNscr, hSz]; try rw [Nat.mod_eq_of_lt (by omega)]
                                                exact (byte64_read64 st.mem (1048552:UInt32) 1 (by decide)).symm
                                              · simp only [if_neg hc23] at hget
                                                by_cases hc24 : (1048552 : UInt32) = addr
                                                · simp only [if_pos hc24, Option.some.injEq] at hget; subst_vars
                                                  simp only [Mem.read8, hNscr]
                                                  exact (byte64_read64 st.mem (1048552:UInt32) 0 (by decide)).symm
                                                · simp only [if_neg hc24] at hget
                                                  exact absurd hget (by simp)

private theorem get?_foldl_delete (m : WasmHeapMap (Option UInt8)) (keys : List UInt32) (k : UInt32)
    (h_ne : ∀ k' ∈ keys, k' ≠ k) :
    get? (keys.foldl (fun acc k' => delete acc k') m) k = get? m k := by
  induction keys generalizing m with
  | nil => rfl
  | cons k' rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun k'' hk'' => h_ne k'' (List.mem_cons.mpr (Or.inr hk'')))]
    exact get?_delete_ne (h_ne k' List.mem_cons_self)

end SwapSigmaLemmas

variable [inst : WasmHeapGS]

def swapPre (ptr_a ptr_b scratch : UInt32) (a b : UInt64) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 ptr_a a) ∗ (pointsTo_u64 ptr_b b) ∗ (pointsTo_u64 scratch 0)

def swapPost (ptr_a ptr_b scratch : UInt32) (a b : UInt64) : IProp WasmHeapGF :=
  iprop% (pointsTo_u64 ptr_a b) ∗ (pointsTo_u64 ptr_b a) ∗ (pointsTo_u64 scratch a)

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

-- Decomposes the bigSepM over swap_σ₀ into three pointsTo_u64 assertions.
-- Used by both disjoint cases in func2_terminates to avoid duplicating the peel loop.
set_option maxHeartbeats 8000000 in
open Iris.BI.BigSepM in
private theorem swap_σ₀_to_pointsTo
    (ptr_a ptr_b : UInt32) (vA vB vS : UInt64)
    (hge_a : (1048560 : Nat) ≤ ptr_a.toNat)
    (hge_b : (1048560 : Nat) ≤ ptr_b.toNat)
    (h_disj : ptr_a.toNat + 8 ≤ ptr_b.toNat ∨ ptr_b.toNat + 8 ≤ ptr_a.toNat)
    (hp_a : ptr_a.toNat + 7 < 4294967296)
    (hp_b : ptr_b.toNat + 7 < 4294967296)
    [inst : WasmHeapGS] :
    ([∗map] k ↦ v ∈ swap_σ₀ ptr_a ptr_b vA vB vS, pointsTo k (DFrac.own 1) v) ⊢
      pointsTo_u64 (1048552 : UInt32) vS ∗ pointsTo_u64 ptr_a vA ∗ pointsTo_u64 ptr_b vB := by
  let scr : UInt32 := 1048552
  let σ₀ := swap_σ₀ ptr_a ptr_b vA vB vS
  have hg00 := swap_σ₀_get_00 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg01 := swap_σ₀_get_01 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg02 := swap_σ₀_get_02 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg03 := swap_σ₀_get_03 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg04 := swap_σ₀_get_04 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg05 := swap_σ₀_get_05 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg06 := swap_σ₀_get_06 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg07 := swap_σ₀_get_07 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg08 := swap_σ₀_get_08 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg09 := swap_σ₀_get_09 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg10 := swap_σ₀_get_10 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg11 := swap_σ₀_get_11 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg12 := swap_σ₀_get_12 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg13 := swap_σ₀_get_13 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg14 := swap_σ₀_get_14 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg15 := swap_σ₀_get_15 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg16 := swap_σ₀_get_16 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg17 := swap_σ₀_get_17 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg18 := swap_σ₀_get_18 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg19 := swap_σ₀_get_19 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg20 := swap_σ₀_get_20 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg21 := swap_σ₀_get_21 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg22 := swap_σ₀_get_22 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  have hg23 := swap_σ₀_get_23 ptr_a ptr_b vA vB vS hge_a hge_b h_disj hp_a hp_b
  iintro Hbig
  -- scr (0 prior peels)
  icases bigSepM_delete hg00 $$ Hbig with ⟨Hs0, Hbig⟩
  -- scr+1 (peel k0=scr)
  icases bigSepM_delete ((get?_delete_ne (by decide)).trans hg01) $$ Hbig with ⟨Hs1, Hbig⟩
  -- scr+2 (peel k1=scr+1, k0=scr)
  icases bigSepM_delete ((get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans hg02) $$ Hbig with ⟨Hs2, Hbig⟩
  -- scr+3
  icases bigSepM_delete ((get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans hg03) $$ Hbig with ⟨Hs3, Hbig⟩
  -- scr+4
  icases bigSepM_delete ((get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans hg04) $$ Hbig with ⟨Hs4, Hbig⟩
  -- scr+5
  icases bigSepM_delete ((get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans hg05) $$ Hbig with ⟨Hs5, Hbig⟩
  -- scr+6
  icases bigSepM_delete ((get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans hg06) $$ Hbig with ⟨Hs6, Hbig⟩
  -- scr+7
  icases bigSepM_delete ((get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans <|
      (get?_delete_ne (by decide)).trans hg07) $$ Hbig with ⟨Hs7, Hbig⟩
  -- ptr_a (peel k7=scr+7 .. k0=scr; each scr+i≠ptr_a)
  icases bigSepM_delete ((get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_a (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_a (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_a (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_a (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_a (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_a (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_a (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr0 hge_a))).trans hg08) $$ Hbig with ⟨Ha0, Hbig⟩
  -- ptr_a+1 (peel k8=ptr_a, k7..k0)
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_a hp_a (by decide)))).trans hg09) $$ Hbig with ⟨Ha1, Hbig⟩
  -- ptr_a+2
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_a hp_a (by decide)))).trans hg10) $$ Hbig with ⟨Ha2, Hbig⟩
  -- ptr_a+3
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_a hp_a (by decide)))).trans hg11) $$ Hbig with ⟨Ha3, Hbig⟩
  -- ptr_a+4
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_a hp_a (by decide)))).trans hg12) $$ Hbig with ⟨Ha4, Hbig⟩
  -- ptr_a+5
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_a hp_a (by decide)))).trans hg13) $$ Hbig with ⟨Ha5, Hbig⟩
  -- ptr_a+6
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_a hp_a (by decide)))).trans hg14) $$ Hbig with ⟨Ha6, Hbig⟩
  -- ptr_a+7
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_a)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_a hp_a (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_a hp_a (by decide)))).trans hg15) $$ Hbig with ⟨Ha7, Hbig⟩
  -- ptr_b (peel k15=ptr_a+7..k8=ptr_a, then k7=scr+7..k0=scr)
  icases bigSepM_delete ((get?_delete_ne (addr_ne_cross_0r (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0r (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0r (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0r (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0r (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0r (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0r (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_base h_disj)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_b (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_b (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_b (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_b (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_b (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_b (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr hge_b (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_base_scr0 hge_b))).trans hg16) $$ Hbig with ⟨Hb0, Hbig⟩
  -- ptr_b+1
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0l (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_b hp_b (by decide)))).trans hg17) $$ Hbig with ⟨Hb1, Hbig⟩
  -- ptr_b+2
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0l (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_b hp_b (by decide)))).trans hg18) $$ Hbig with ⟨Hb2, Hbig⟩
  -- ptr_b+3
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0l (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_b hp_b (by decide)))).trans hg19) $$ Hbig with ⟨Hb3, Hbig⟩
  -- ptr_b+4
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0l (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_b hp_b (by decide)))).trans hg20) $$ Hbig with ⟨Hb4, Hbig⟩
  -- ptr_b+5
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0l (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_b hp_b (by decide)))).trans hg21) $$ Hbig with ⟨Hb5, Hbig⟩
  -- ptr_b+6
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0l (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_b hp_b (by decide)))).trans hg22) $$ Hbig with ⟨Hb6, Hbig⟩
  -- ptr_b+7
  icases bigSepM_delete ((get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra (by decide) (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_intra_0l (by decide) (by decide) hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross (by decide) (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_cross_0l (by decide) h_disj hp_a hp_b)).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr hge_b hp_b (by decide) (by decide)))).trans <|
      (get?_delete_ne (addr_ne_symm (ne_ptr_scr0 hge_b hp_b (by decide)))).trans hg23) $$ Hbig with ⟨Hb7, _⟩
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
  isplitl [HS]; · iexact HS
  isplitl [HA]; · iexact HA
  iexact HB

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
    -- Bounds for execOne trap checks
    have hbds_scratch : ¬(st.mem.pages * 65536 < 1048560) := by omega
    have hbds_a : ¬(st.mem.pages * 65536 < ptr_a.toNat + 8) := by omega
    have hbds_b : ¬(st.mem.pages * 65536 < ptr_b.toNat + 8) := by omega
    -- Pages invariant
    have hpages : m₃.pages = st.mem.pages := rfl
    -- Opaque-let helpers: m₁/m₂/m₃ are opaque to simp, so derive equalities explicitly
    have hm₁_eq : m₁ = st.mem.write64 scr vA := rfl
    have hm₂_eq : m₂ = m₁.write64 ptr_a vB := rfl
    have hm₃_eq : m₃ = m₂.write64 ptr_b vA := rfl
    have hpages₁ : m₁.pages = st.mem.pages := rfl
    have hpages₂ : m₂.pages = st.mem.pages := rfl
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
      let σ₀ := swap_σ₀ ptr_a ptr_b vA vB vS
      have hp_a : ptr_a.toNat + 7 < 4294967296 := by omega
      have hp_b : ptr_b.toNat + 7 < 4294967296 := by omega
      have hagree₀ : heapAgreesWithMem σ₀ st.mem :=
        swap_σ₀_hagree ptr_a ptr_b vA vB vS st hp_a hp_b rfl rfl rfl
      exact wasm_heap_adequacy_with_mem «module» st
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
                st'.mem.read64 a = st.mem.read64 a)
          σ₀ hagree₀ fun [_inst : WasmHeapGS] => by
        iintro Hbig
        -- toNat offsets for simp discharger
        have hs1t : (scr + 1).toNat = 1048553 := rfl
        have hs2t : (scr + 2).toNat = 1048554 := rfl
        have hs3t : (scr + 3).toNat = 1048555 := rfl
        have hs4t : (scr + 4).toNat = 1048556 := rfl
        have hs5t : (scr + 5).toNat = 1048557 := rfl
        have hs6t : (scr + 6).toNat = 1048558 := rfl
        have hs7t : (scr + 7).toNat = 1048559 := rfl
        have hpa1t : (ptr_a + 1).toNat = ptr_a.toNat + 1 := toNat_add_ofNat ptr_a 1 (by omega)
        have hpa2t : (ptr_a + 2).toNat = ptr_a.toNat + 2 := toNat_add_ofNat ptr_a 2 (by omega)
        have hpa3t : (ptr_a + 3).toNat = ptr_a.toNat + 3 := toNat_add_ofNat ptr_a 3 (by omega)
        have hpa4t : (ptr_a + 4).toNat = ptr_a.toNat + 4 := toNat_add_ofNat ptr_a 4 (by omega)
        have hpa5t : (ptr_a + 5).toNat = ptr_a.toNat + 5 := toNat_add_ofNat ptr_a 5 (by omega)
        have hpa6t : (ptr_a + 6).toNat = ptr_a.toNat + 6 := toNat_add_ofNat ptr_a 6 (by omega)
        have hpa7t : (ptr_a + 7).toNat = ptr_a.toNat + 7 := toNat_add_ofNat ptr_a 7 (by omega)
        have hpb1t : (ptr_b + 1).toNat = ptr_b.toNat + 1 := toNat_add_ofNat ptr_b 1 (by omega)
        have hpb2t : (ptr_b + 2).toNat = ptr_b.toNat + 2 := toNat_add_ofNat ptr_b 2 (by omega)
        have hpb3t : (ptr_b + 3).toNat = ptr_b.toNat + 3 := toNat_add_ofNat ptr_b 3 (by omega)
        have hpb4t : (ptr_b + 4).toNat = ptr_b.toNat + 4 := toNat_add_ofNat ptr_b 4 (by omega)
        have hpb5t : (ptr_b + 5).toNat = ptr_b.toNat + 5 := toNat_add_ofNat ptr_b 5 (by omega)
        have hpb6t : (ptr_b + 6).toNat = ptr_b.toNat + 6 := toNat_add_ofNat ptr_b 6 (by omega)
        have hpb7t : (ptr_b + 7).toNat = ptr_b.toNat + 7 := toNat_add_ofNat ptr_b 7 (by omega)
        ihave ⟨HS, HA, HB⟩ := swap_σ₀_to_pointsTo ptr_a ptr_b vA vB vS hge_a hge_b (Or.inl hlt) hp_a hp_b $$ Hbig
        -- Step through all 17 instructions using wp_wasm_F unfolding
        -- Inst 1: globalGet 0
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [show func2Def.body = [.globalGet 0, .const (16 : UInt32), .sub, .localSet 2, .localGet 2, .localGet 0, .load64 (0 : UInt32), .store64 (8 : UInt32), .localGet 0, .localGet 1, .load64 (0 : UInt32), .store64 (0 : UInt32), .localGet 1, .localGet 2, .load64 (8 : UInt32), .store64 (0 : UInt32), .ret] from rfl, wp_wasm_F]
        iintro %σ₁ %hagree₁ Hσ₁
        imodintro
        iexists σ₁, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (1048560 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get, hg0, Function.toLocals, Function.numParams, func2Def, List.take, List.length, List.map, ValueType.zero])
        isplitl []; · exact BI.pure_intro hagree₁
        isplitl [Hσ₁]; · iexact Hσ₁
        -- Inst 2: const 16
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₂ %hagree₂ Hσ₂
        imodintro
        iexists σ₂, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (16 : UInt32), .i32 (1048560 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₂
        isplitl [Hσ₂]; · iexact Hσ₂
        -- Inst 3: sub
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₃ %hagree₃ Hσ₃
        imodintro
        iexists σ₃, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₃
        isplitl [Hσ₃]; · iexact Hσ₃
        -- Inst 4: localSet 2
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₄ %hagree₄ Hσ₄
        imodintro
        iexists σ₄, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get, Locals.set?])
        isplitl []; · exact BI.pure_intro hagree₄
        isplitl [Hσ₄]; · iexact Hσ₄
        -- Inst 5: localGet 2
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₅ %hagree₅ Hσ₅
        imodintro
        iexists σ₅, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₅
        isplitl [Hσ₅]; · iexact Hσ₅
        -- Inst 6: localGet 0
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₆ %hagree₆ Hσ₆
        imodintro
        iexists σ₆, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_a, .i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₆
        isplitl [Hσ₆]; · iexact Hσ₆
        -- Inst 7: load64 0 at ptr_a → reads vA
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₇ %hagree₇ Hσ₇
        imod (wp_iProp_load64 hagree₇ (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [$Hσ₇ $HA] with ⟨Hσ₇, HA, %heq_a⟩
        imodintro
        iexists σ₇, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i64 vA, .i32 (1048544 : UInt32)] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, if_neg hbds_a, UInt32.add_zero, heq_a])
        isplitl []; · exact BI.pure_intro hagree₇
        isplitl [Hσ₇]; · iexact Hσ₇
        -- Inst 8: store64 8 at 1048544+8=scr with value vA
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₈ %hagree₈ Hσ₈
        imod (wp_iProp_store64 (v_new := vA) hagree₈
          (show scr.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [$Hσ₈ $HS] with
          ⟨%σ₈', %hagree₈', Hσ₈', HS'⟩
        imodintro
        iexists σ₈', { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, if_neg hbds_scratch,
                  show (1048544 : UInt32) + 8 = scr from rfl, hm₁_eq])
        isplitl []; · exact BI.pure_intro hagree₈'
        isplitl [Hσ₈']; · iexact Hσ₈'
        -- Inst 9: localGet 0
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₉ %hagree₉ Hσ₉
        imodintro
        iexists σ₉, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_a] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₉
        isplitl [Hσ₉]; · iexact Hσ₉
        -- Inst 10: localGet 1
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₀ %hagree₁₀ Hσ₁₀
        imodintro
        iexists σ₁₀, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_b, .i32 ptr_a] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₀
        isplitl [Hσ₁₀]; · iexact Hσ₁₀
        -- Inst 11: load64 0 at ptr_b from m₁ → reads vB
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₁ %hagree₁₁ Hσ₁₁
        imod (wp_iProp_load64 hagree₁₁ (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [$Hσ₁₁ $HB] with ⟨Hσ₁₁, HB, %heq_b⟩
        imodintro
        iexists σ₁₁, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i64 vB, .i32 ptr_a] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, hpages₁,
                  if_neg hbds_b, UInt32.add_zero, heq_b])
        isplitl []; · exact BI.pure_intro hagree₁₁
        isplitl [Hσ₁₁]; · iexact Hσ₁₁
        -- Inst 12: store64 0 at ptr_a from m₁ with value vB
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₂ %hagree₁₂ Hσ₁₂
        imod (wp_iProp_store64 (v_new := vB) hagree₁₂
          (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [$Hσ₁₂ $HA] with
          ⟨%σ₁₂', %hagree₁₂', Hσ₁₂', HA'⟩
        imodintro
        iexists σ₁₂', { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, hpages₁,
                  if_neg hbds_a, UInt32.add_zero, hm₂_eq])
        isplitl []; · exact BI.pure_intro hagree₁₂'
        isplitl [Hσ₁₂']; · iexact Hσ₁₂'
        -- Inst 13: localGet 1
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₃ %hagree₁₃ Hσ₁₃
        imodintro
        iexists σ₁₃, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_b] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₃
        isplitl [Hσ₁₃]; · iexact Hσ₁₃
        -- Inst 14: localGet 2
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₄ %hagree₁₄ Hσ₁₄
        imodintro
        iexists σ₁₄, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 (1048544 : UInt32), .i32 ptr_b] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₄
        isplitl [Hσ₁₄]; · iexact Hσ₁₄
        -- Inst 15: load64 8 at 1048544+8=scr from m₂ → reads vA
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₅ %hagree₁₅ Hσ₁₅
        imod (wp_iProp_load64 hagree₁₅ (show scr.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [$Hσ₁₅ $HS'] with ⟨Hσ₁₅, HS', %heq_s⟩
        imodintro
        iexists σ₁₅, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i64 vA, .i32 ptr_b] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, hpages₂, if_neg hbds_scratch,
                  show (1048544 : UInt32) + 8 = scr from rfl, heq_s])
        isplitl []; · exact BI.pure_intro hagree₁₅
        isplitl [Hσ₁₅]; · iexact Hσ₁₅
        -- Inst 16: store64 0 at ptr_b from m₂ with value vA
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₆ %hagree₁₆ Hσ₁₆
        imod (wp_iProp_store64 (v_new := vA) hagree₁₆
          (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [$Hσ₁₆ $HB] with
          ⟨%σ₁₆', %hagree₁₆', Hσ₁₆', HB'⟩
        -- Extract postcondition facts from ownership tokens using m₃ agreement
        imod (wp_iProp_load64 hagree₁₆' (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [$Hσ₁₆' $HA'] with ⟨Hσ_a, _, %heq_pa⟩
        imod (wp_iProp_load64 hagree₁₆' (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [$Hσ_a $HB'] with ⟨Hσ_b, _, %heq_pb⟩
        imodintro
        iexists σ₁₆', { st with mem := m₃ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, hpages₂,
                  if_neg hbds_b, UInt32.add_zero, hm₃_eq])
        isplitl []; · exact BI.pure_intro hagree₁₆'
        isplitl [Hσ_b]; · iexact Hσ_b
        -- Inst 17: ret
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        ipureintro
        refine ⟨trivial, trivial, hpages, heq_pa, heq_pb, fun a h1 h2 h3 => ?_⟩
        apply read64_of_digits; intro i hi
        rw [write64_bytes_ne m₂ ptr_b vA (a.toNat + i)
              (by rcases h2 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
        rw [write64_bytes_ne m₁ ptr_a vB (a.toNat + i)
              (by rcases h1 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
        rw [write64_bytes_ne st.mem scr vA (a.toNat + i)
              (by rcases h3 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))]
        exact (byte64_read64 st.mem a i hi).symm
    · -- hlt case 2: ptr_b.toNat + 8 ≤ ptr_a.toNat (symmetric)
      let σ₀ := swap_σ₀ ptr_a ptr_b vA vB vS
      have hp_a : ptr_a.toNat + 7 < 4294967296 := by omega
      have hp_b : ptr_b.toNat + 7 < 4294967296 := by omega
      have hagree₀ : heapAgreesWithMem σ₀ st.mem :=
        swap_σ₀_hagree ptr_a ptr_b vA vB vS st hp_a hp_b rfl rfl rfl
      exact wasm_heap_adequacy_with_mem «module» st
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
                st'.mem.read64 a = st.mem.read64 a)
          σ₀ hagree₀ fun [_inst : WasmHeapGS] => by
        iintro Hbig
        -- toNat offsets for simp discharger
        have hs1t : (scr + 1).toNat = 1048553 := rfl
        have hs2t : (scr + 2).toNat = 1048554 := rfl
        have hs3t : (scr + 3).toNat = 1048555 := rfl
        have hs4t : (scr + 4).toNat = 1048556 := rfl
        have hs5t : (scr + 5).toNat = 1048557 := rfl
        have hs6t : (scr + 6).toNat = 1048558 := rfl
        have hs7t : (scr + 7).toNat = 1048559 := rfl
        have hpa1t : (ptr_a + 1).toNat = ptr_a.toNat + 1 := toNat_add_ofNat ptr_a 1 (by omega)
        have hpa2t : (ptr_a + 2).toNat = ptr_a.toNat + 2 := toNat_add_ofNat ptr_a 2 (by omega)
        have hpa3t : (ptr_a + 3).toNat = ptr_a.toNat + 3 := toNat_add_ofNat ptr_a 3 (by omega)
        have hpa4t : (ptr_a + 4).toNat = ptr_a.toNat + 4 := toNat_add_ofNat ptr_a 4 (by omega)
        have hpa5t : (ptr_a + 5).toNat = ptr_a.toNat + 5 := toNat_add_ofNat ptr_a 5 (by omega)
        have hpa6t : (ptr_a + 6).toNat = ptr_a.toNat + 6 := toNat_add_ofNat ptr_a 6 (by omega)
        have hpa7t : (ptr_a + 7).toNat = ptr_a.toNat + 7 := toNat_add_ofNat ptr_a 7 (by omega)
        have hpb1t : (ptr_b + 1).toNat = ptr_b.toNat + 1 := toNat_add_ofNat ptr_b 1 (by omega)
        have hpb2t : (ptr_b + 2).toNat = ptr_b.toNat + 2 := toNat_add_ofNat ptr_b 2 (by omega)
        have hpb3t : (ptr_b + 3).toNat = ptr_b.toNat + 3 := toNat_add_ofNat ptr_b 3 (by omega)
        have hpb4t : (ptr_b + 4).toNat = ptr_b.toNat + 4 := toNat_add_ofNat ptr_b 4 (by omega)
        have hpb5t : (ptr_b + 5).toNat = ptr_b.toNat + 5 := toNat_add_ofNat ptr_b 5 (by omega)
        have hpb6t : (ptr_b + 6).toNat = ptr_b.toNat + 6 := toNat_add_ofNat ptr_b 6 (by omega)
        have hpb7t : (ptr_b + 7).toNat = ptr_b.toNat + 7 := toNat_add_ofNat ptr_b 7 (by omega)
        ihave ⟨HS, HA, HB⟩ := swap_σ₀_to_pointsTo ptr_a ptr_b vA vB vS hge_a hge_b (Or.inr hlt) hp_a hp_b $$ Hbig
        unfold wp_wasm; iapply least_fixpoint_unfold_mpr; simp only [show func2Def.body = [.globalGet 0, .const (16 : UInt32), .sub, .localSet 2, .localGet 2, .localGet 0, .load64 (0 : UInt32), .store64 (8 : UInt32), .localGet 0, .localGet 1, .load64 (0 : UInt32), .store64 (0 : UInt32), .localGet 1, .localGet 2, .load64 (8 : UInt32), .store64 (0 : UInt32), .ret] from rfl, wp_wasm_F]
        iintro %σ₁ %hagree₁ Hσ₁
        imodintro
        iexists σ₁, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (1048560 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get, hg0, Function.toLocals, Function.numParams, func2Def, List.take, List.length, List.map, ValueType.zero])
        isplitl []; · exact BI.pure_intro hagree₁
        isplitl [Hσ₁]; · iexact Hσ₁
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₂ %hagree₂ Hσ₂
        imodintro
        iexists σ₂, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (16 : UInt32), .i32 (1048560 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₂
        isplitl [Hσ₂]; · iexact Hσ₂
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₃ %hagree₃ Hσ₃
        imodintro
        iexists σ₃, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (0 : UInt32)],
            values := [.i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₃
        isplitl [Hσ₃]; · iexact Hσ₃
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₄ %hagree₄ Hσ₄
        imodintro
        iexists σ₄, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get, Locals.set?])
        isplitl []; · exact BI.pure_intro hagree₄
        isplitl [Hσ₄]; · iexact Hσ₄
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₅ %hagree₅ Hσ₅
        imodintro
        iexists σ₅, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₅
        isplitl [Hσ₅]; · iexact Hσ₅
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₆ %hagree₆ Hσ₆
        imodintro
        iexists σ₆, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_a, .i32 (1048544 : UInt32)] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₆
        isplitl [Hσ₆]; · iexact Hσ₆
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₇ %hagree₇ Hσ₇
        imod (wp_iProp_load64 hagree₇ (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [$Hσ₇ $HA] with ⟨Hσ₇, HA, %heq_a⟩
        imodintro
        iexists σ₇, st,
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i64 vA, .i32 (1048544 : UInt32)] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, if_neg hbds_a, UInt32.add_zero, heq_a])
        isplitl []; · exact BI.pure_intro hagree₇
        isplitl [Hσ₇]; · iexact Hσ₇
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₈ %hagree₈ Hσ₈
        imod (wp_iProp_store64 (v_new := vA) hagree₈
          (show scr.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [$Hσ₈ $HS] with
          ⟨%σ₈', %hagree₈', Hσ₈', HS'⟩
        imodintro
        iexists σ₈', { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, if_neg hbds_scratch,
                  show (1048544 : UInt32) + 8 = scr from rfl, hm₁_eq])
        isplitl []; · exact BI.pure_intro hagree₈'
        isplitl [Hσ₈']; · iexact Hσ₈'
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₉ %hagree₉ Hσ₉
        imodintro
        iexists σ₉, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_a] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₉
        isplitl [Hσ₉]; · iexact Hσ₉
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₀ %hagree₁₀ Hσ₁₀
        imodintro
        iexists σ₁₀, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_b, .i32 ptr_a] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₀
        isplitl [Hσ₁₀]; · iexact Hσ₁₀
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₁ %hagree₁₁ Hσ₁₁
        imod (wp_iProp_load64 hagree₁₁ (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [$Hσ₁₁ $HB] with ⟨Hσ₁₁, HB, %heq_b⟩
        imodintro
        iexists σ₁₁, { st with mem := m₁ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i64 vB, .i32 ptr_a] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, hpages₁,
                  if_neg hbds_b, UInt32.add_zero, heq_b])
        isplitl []; · exact BI.pure_intro hagree₁₁
        isplitl [Hσ₁₁]; · iexact Hσ₁₁
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₂ %hagree₁₂ Hσ₁₂
        imod (wp_iProp_store64 (v_new := vB) hagree₁₂
          (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [$Hσ₁₂ $HA] with
          ⟨%σ₁₂', %hagree₁₂', Hσ₁₂', HA'⟩
        imodintro
        iexists σ₁₂', { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, hpages₁,
                  if_neg hbds_a, UInt32.add_zero, hm₂_eq])
        isplitl []; · exact BI.pure_intro hagree₁₂'
        isplitl [Hσ₁₂']; · iexact Hσ₁₂'
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₃ %hagree₁₃ Hσ₁₃
        imodintro
        iexists σ₁₃, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 ptr_b] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₃
        isplitl [Hσ₁₃]; · iexact Hσ₁₃
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₄ %hagree₁₄ Hσ₁₄
        imodintro
        iexists σ₁₄, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i32 (1048544 : UInt32), .i32 ptr_b] }
        isplitl []; · exact BI.pure_intro (by simp [execOne.eq_def, Locals.get])
        isplitl []; · exact BI.pure_intro hagree₁₄
        isplitl [Hσ₁₄]; · iexact Hσ₁₄
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₅ %hagree₁₅ Hσ₁₅
        imod (wp_iProp_load64 hagree₁₅ (show scr.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [$Hσ₁₅ $HS'] with ⟨Hσ₁₅, HS', %heq_s⟩
        imodintro
        iexists σ₁₅, { st with mem := m₂ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)],
            values := [.i64 vA, .i32 ptr_b] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, hpages₂, if_neg hbds_scratch,
                  show (1048544 : UInt32) + 8 = scr from rfl, heq_s])
        isplitl []; · exact BI.pure_intro hagree₁₅
        isplitl [Hσ₁₅]; · iexact Hσ₁₅
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        iintro %σ₁₆ %hagree₁₆ Hσ₁₆
        imod (wp_iProp_store64 (v_new := vA) hagree₁₆
          (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega)) $$ [$Hσ₁₆ $HB] with
          ⟨%σ₁₆', %hagree₁₆', Hσ₁₆', HB'⟩
        imod (wp_iProp_load64 hagree₁₆' (show ptr_a.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [$Hσ₁₆' $HA'] with ⟨Hσ_a, _, %heq_pa⟩
        imod (wp_iProp_load64 hagree₁₆' (show ptr_b.toNat + 8 ≤ 2 ^ 32 from by omega))
          $$ [$Hσ_a $HB'] with ⟨Hσ_b, _, %heq_pb⟩
        imodintro
        iexists σ₁₆', { st with mem := m₃ },
          { params := [.i32 ptr_a, .i32 ptr_b], locals := [.i32 (1048544 : UInt32)], values := [] }
        isplitl []
        · exact BI.pure_intro (by
            simp [execOne.eq_def, Locals.get, hpages₂,
                  if_neg hbds_b, UInt32.add_zero, hm₃_eq])
        isplitl []; · exact BI.pure_intro hagree₁₆'
        isplitl [Hσ_b]; · iexact Hσ_b
        iapply least_fixpoint_unfold_mpr; simp only [wp_wasm_F]
        ipureintro
        refine ⟨trivial, trivial, hpages, heq_pa, heq_pb, fun a h1 h2 h3 => ?_⟩
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
      (by rw [hst3_pages]; nlinarith [hptr])
      hpages_bound hg0_3
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
