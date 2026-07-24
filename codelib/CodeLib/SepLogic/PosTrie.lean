import Iris.Std.HeapInstances

/-! # PosTrie: positional binary trie for UInt32 keys

Bit-path trie keyed on UInt32. Key 0 reads the current node; even key→left,
odd key→right, both with key/2. Replacing ExtTreeMap for simp-heavy sep-logic
proofs. -/

namespace Wasm.SepLogic

-- do NOT open Iris.Std here; opening it pollutes 'get?' resolution below.
-- Each instance is opened locally.

inductive PosTrie (V : Type) where
  | empty : PosTrie V
  | leaf  : V → PosTrie V
  | node  : Option V → PosTrie V → PosTrie V → PosTrie V

namespace PosTrie

variable {V V' : Type}

-- ─── Smart constructor ────────────────────────────────────────────────────────

def mkNode (v : Option V) (l r : PosTrie V) : PosTrie V :=
  match v, l, r with
  | none,   .empty, .empty => .empty
  | some w, .empty, .empty => .leaf w
  | _,      _,      _      => .node v l r

-- ─── Accessors ───────────────────────────────────────────────────────────────

private def nodeVal : PosTrie V → Option V
  | .node v _ _ => v | .leaf v => some v | .empty => none

private def lc : PosTrie V → PosTrie V
  | .node _ l _ => l | _ => .empty

private def rc : PosTrie V → PosTrie V
  | .node _ _ r => r | _ => .empty

-- ─── Lookup ──────────────────────────────────────────────────────────────────

def get? : PosTrie V → UInt32 → Option V
  | .empty,      _ => none
  | .leaf v,     k => if k = 0 then some v else none
  | .node v l r, k =>
    if k = 0 then v
    else if k % 2 = 0 then get? l (k / 2)
    else get? r (k / 2)

-- named simp lemmas so 'simp [get?]' ambiguity never bites
@[simp] private theorem get?_empty_eq (k : UInt32) : (PosTrie.empty : PosTrie V).get? k = none := rfl
@[simp] private theorem get?_leaf_zero (v : V) : (PosTrie.leaf v).get? 0 = some v := rfl
private theorem get?_leaf_nz (v : V) (k : UInt32) (h : k ≠ 0) : (PosTrie.leaf v).get? k = none :=
  if_neg h
@[simp] private theorem get?_node_zero (v : Option V) (l r : PosTrie V) :
    (PosTrie.node v l r).get? 0 = v := rfl

-- ─── mkNode lemmas ───────────────────────────────────────────────────────────

@[simp] private theorem mkNode_get?_zero (v : Option V) (l r : PosTrie V) :
    (mkNode v l r).get? 0 = v := by
  simp only [mkNode]; split <;> simp_all [get?]

private theorem mkNode_get?_nz (v : Option V) (l r : PosTrie V)
    (k : UInt32) (hk : k ≠ 0) :
    (mkNode v l r).get? k = if k % 2 = 0 then l.get? (k / 2) else r.get? (k / 2) := by
  simp only [mkNode]
  split <;> rename_i h1 h2 h3 <;> simp_all [get?, hk]

@[simp] private theorem mkNode_nodeVal (v : Option V) (l r : PosTrie V) :
    (mkNode v l r).nodeVal = v := by
  simp only [mkNode]; split <;> simp_all [nodeVal]

private theorem get?_node_nz (v : Option V) (l r : PosTrie V)
    (k : UInt32) (hk : k ≠ 0) :
    get? (.node v l r) k = if k % 2 = 0 then l.get? (k / 2) else r.get? (k / 2) := by
  simp [get?, hk]

-- ─── UInt32 arithmetic ───────────────────────────────────────────────────────

private theorem two_toNat : (2 : UInt32).toNat = 2 := by decide

private theorem toNat_ne_zero {k : UInt32} (h : k ≠ 0) : k.toNat ≠ 0 :=
  fun e => h (UInt32.toNat.inj (by simpa using e))

private theorem toNat_div2 (k : UInt32) : (k / 2).toNat = k.toNat / 2 := by
  simp only [UInt32.toNat_div, two_toNat]

private theorem toNat_mod2 (k : UInt32) : (k % 2).toNat = k.toNat % 2 := by
  simp only [UInt32.toNat_mod, two_toNat]

private theorem toNat_div_lt {k : UInt32} (h : k ≠ 0) : (k / 2).toNat < k.toNat := by
  have := toNat_ne_zero h; rw [toNat_div2]; omega

private theorem uint32_div2_even {j : UInt32} (h : j % 2 = 0) : j / 2 * 2 = j := by
  apply UInt32.toNat.inj
  have hmod : j.toNat % 2 = 0 := by
    have h2 := toNat_mod2 j
    have h3 : (j % 2 : UInt32).toNat = 0 := by rw [h]; rfl
    omega
  have hlt := j.toNat_lt
  simp only [UInt32.toNat_mul, toNat_div2, two_toNat, UInt32.size]; omega

private theorem uint32_div2_odd {j : UInt32} (h : j % 2 ≠ 0) : j / 2 * 2 + 1 = j := by
  apply UInt32.toNat.inj
  have hmod : j.toNat % 2 = 1 := by
    have h2 := toNat_mod2 j
    have hne : (j % 2 : UInt32).toNat ≠ 0 := by
      intro e; exact h (UInt32.toNat.inj (by simp [e]))
    omega
  have hlt := j.toNat_lt
  simp only [UInt32.toNat_add, UInt32.toNat_mul, toNat_div2, two_toNat,
             show (1 : UInt32).toNat = 1 from rfl, UInt32.size]; omega

private theorem uint32_eq_of_div_mod {k k' : UInt32}
    (hdiv : k / 2 = k' / 2) (hmod : k % 2 = k' % 2) : k = k' := by
  apply UInt32.toNat.inj
  have hd : k.toNat / 2 = k'.toNat / 2 := by
    have := congrArg UInt32.toNat hdiv; simp only [toNat_div2] at this; exact this
  have hm : k.toNat % 2 = k'.toNat % 2 := by
    have := congrArg UInt32.toNat hmod; simp only [toNat_mod2] at this; exact this
  omega

private theorem mod2_eq_one {k : UInt32} (h : k % 2 ≠ 0) : k % 2 = 1 := by
  apply UInt32.toNat.inj
  rw [toNat_mod2, show (1 : UInt32).toNat = 1 from rfl]
  have hne : k.toNat % 2 ≠ 0 := by
    intro e
    exact h (UInt32.toNat.inj (by
      rw [toNat_mod2, show (0 : UInt32).toNat = 0 from rfl]; exact e))
  omega

-- mod 2^32 product helpers
private theorem mp_l (x y : Nat) : x % 2^32 * y % 2^32 = x * y % 2^32 := by
  rw [Nat.mul_mod (x % 2^32) y, Nat.mod_mod_of_dvd x (Nat.dvd_refl (2^32))]
  exact (Nat.mul_mod x y (2^32)).symm

private theorem mp_r (x y : Nat) : x * (y % 2^32) % 2^32 = x * y % 2^32 := by
  rw [Nat.mul_mod x (y % 2^32), Nat.mod_mod_of_dvd y (Nat.dvd_refl (2^32))]
  exact (Nat.mul_mod x y (2^32)).symm

-- a * (b * 2) = a * 2 * b
private theorem mul_step_comm (a b : UInt32) : a * (b * 2) = a * 2 * b := by
  apply UInt32.toNat.inj
  simp only [UInt32.toNat_mul, two_toNat]
  rw [mp_r, mp_l]
  congr 1
  rw [show b.toNat * 2 = 2 * b.toNat from Nat.mul_comm b.toNat 2, ← Nat.mul_assoc]

-- (a + b) * c = a * c + b * c
private theorem uint32_add_mul (a b c : UInt32) : (a + b) * c = a * c + b * c := by
  apply UInt32.toNat.inj
  simp only [UInt32.toNat_add, UInt32.toNat_mul]
  rw [mp_l, Nat.add_mul]; omega

-- 1 * a = a
private theorem uint32_one_mul (a : UInt32) : 1 * a = a := by
  apply UInt32.toNat.inj
  simp only [UInt32.toNat_mul, show (1 : UInt32).toNat = 1 from rfl]
  have := a.toNat_lt; omega

-- a + b + c = a + (b + c)
private theorem uint32_add_assoc (a b c : UInt32) : a + b + c = a + (b + c) := by
  apply UInt32.toNat.inj
  simp only [UInt32.toNat_add]; omega

-- a + b + c = a + c + b
private theorem uint32_add_right_comm (a b c : UInt32) : a + b + c = a + c + b := by
  apply UInt32.toNat.inj
  simp only [UInt32.toNat_add]; omega

-- k * 1 + 0 = k
private theorem uint32_mul1_add0 (k : UInt32) : k * 1 + 0 = k := by
  apply UInt32.toNat.inj
  simp only [UInt32.toNat_add, UInt32.toNat_mul, show (1 : UInt32).toNat = 1 from rfl,
             show (0 : UInt32).toNat = 0 from rfl]
  have := k.toNat_lt; omega

-- ─── Insert / Delete ─────────────────────────────────────────────────────────

def insert (t : PosTrie V) (k : UInt32) (v : V) : PosTrie V :=
  if h : k = 0 then
    match t with
    | .empty | .leaf _ => .leaf v
    | .node _ l r      => mkNode (some v) l r
  else
    if k % 2 = 0 then mkNode t.nodeVal (t.lc.insert (k / 2) v) t.rc
    else              mkNode t.nodeVal t.lc (t.rc.insert (k / 2) v)
termination_by k.toNat
decreasing_by all_goals exact toNat_div_lt ‹_›

def delete (t : PosTrie V) (k : UInt32) : PosTrie V :=
  if h : k = 0 then
    match t with
    | .empty | .leaf _ => .empty
    | .node _ l r      => mkNode none l r
  else
    if k % 2 = 0 then mkNode t.nodeVal (t.lc.delete (k / 2)) t.rc
    else              mkNode t.nodeVal t.lc (t.rc.delete (k / 2))
termination_by k.toNat
decreasing_by all_goals exact toNat_div_lt ‹_›

-- ─── get? helpers ────────────────────────────────────────────────────────────

private theorem get?_zero (t : PosTrie V) : t.get? 0 = t.nodeVal := by
  cases t <;> rfl

private theorem get?_nz (t : PosTrie V) (k : UInt32) (hk : k ≠ 0) :
    t.get? k = if k % 2 = 0 then t.lc.get? (k / 2) else t.rc.get? (k / 2) := by
  cases t with
  | empty   => simp [lc, rc]
  | leaf w  =>
    simp only [get?_leaf_nz w k hk, lc, rc]
    cases Decidable.em (k % 2 = 0) with
    | inl h => simp [h, get?_empty_eq]
    | inr h => simp [h, get?_empty_eq]
  | node w l r => exact get?_node_nz w l r k hk

-- ─── Correctness ─────────────────────────────────────────────────────────────

@[simp] theorem get?_empty (k : UInt32) : (PosTrie.empty : PosTrie V).get? k = none := rfl

theorem get?_insert (t : PosTrie V) (k k' : UInt32) (v : V) :
    (t.insert k v).get? k' = if k = k' then some v else t.get? k' := by
  suffices h : ∀ n, ∀ k : UInt32, k.toNat ≤ n →
      ∀ k' (t : PosTrie V),
      (t.insert k v).get? k' = if k = k' then some v else t.get? k' by
    exact h k.toNat k (Nat.le_refl _) k' t
  intro n
  induction n with
  | zero =>
    intro k hle k' t
    have hk0 : k = 0 := by
      have hn : k.toNat = 0 := Nat.le_zero.mp hle
      exact UInt32.toNat.inj (by simpa using hn)
    subst hk0
    rw (config := { occs := .pos [1] }) [PosTrie.insert.eq_def]
    simp only [dif_pos rfl]
    cases t with
    | empty =>
      by_cases hk' : k' = 0
      · subst hk'; rfl
      · simp [get?_leaf_nz _ _ hk', if_neg (Ne.symm hk'), if_neg hk']
    | leaf w =>
      by_cases hk' : k' = 0
      · subst hk'; rfl
      · simp [get?_leaf_nz _ _ hk', if_neg (Ne.symm hk'), get?_leaf_nz w k' hk']
    | node w l r =>
      by_cases hk' : k' = 0
      · subst hk'; simp [mkNode_get?_zero]
      · simp [mkNode_get?_nz _ _ _ _ hk', get?_node_nz _ _ _ _ hk', Ne.symm hk']
  | succ n ih =>
    intro k hle k' t
    by_cases hk0 : k = 0
    · subst hk0
      rw (config := { occs := .pos [1] }) [PosTrie.insert.eq_def]
      simp only [dif_pos rfl]
      cases t with
      | empty =>
        by_cases hk' : k' = 0
        · subst hk'; rfl
        · simp [get?_leaf_nz _ _ hk', if_neg (Ne.symm hk'), if_neg hk']
      | leaf w =>
        by_cases hk' : k' = 0
        · subst hk'; rfl
        · simp [get?_leaf_nz _ _ hk', if_neg (Ne.symm hk'), get?_leaf_nz w k' hk']
      | node w l r =>
        by_cases hk' : k' = 0
        · subst hk'; simp [mkNode_get?_zero]
        · simp [mkNode_get?_nz _ _ _ _ hk', get?_node_nz _ _ _ _ hk', Ne.symm hk']
    · have hdivle : (k / 2).toNat ≤ n := by
        rw [toNat_div2]; have := toNat_ne_zero hk0; omega
      rw (config := { occs := .pos [1] }) [PosTrie.insert.eq_def]
      simp only [dif_neg hk0]
      by_cases hmod : k % 2 = 0
      · simp only [if_pos hmod]
        by_cases hk'0 : k' = 0
        · subst hk'0
          simp only [if_neg hk0, mkNode_get?_zero]
          exact (get?_zero t).symm
        · rw [mkNode_get?_nz _ _ _ _ hk'0, get?_nz t k' hk'0]
          by_cases hmod' : k' % 2 = 0
          · simp only [hmod', ↓reduceIte]
            rw [ih (k / 2) hdivle (k' / 2) t.lc]
            by_cases heq : k / 2 = k' / 2
            · simp [heq, uint32_eq_of_div_mod heq (by rw [hmod, hmod'])]
            · simp [if_neg heq, if_neg (fun e : k = k' => heq (congrArg (· / 2) e))]
          · have hkk' : k ≠ k' := fun e => hmod' (e ▸ hmod)
            simp [if_neg hmod', if_neg hkk']
      · simp only [if_neg hmod]
        by_cases hk'0 : k' = 0
        · subst hk'0
          simp only [if_neg hk0, mkNode_get?_zero]
          exact (get?_zero t).symm
        · rw [mkNode_get?_nz _ _ _ _ hk'0, get?_nz t k' hk'0]
          by_cases hmod' : k' % 2 = 0
          · have hkk' : k ≠ k' := fun e => hmod (e ▸ hmod')
            simp [hmod', if_neg hkk']
          · simp only [if_neg hmod']
            rw [ih (k / 2) hdivle (k' / 2) t.rc]
            by_cases heq : k / 2 = k' / 2
            · simp [heq, uint32_eq_of_div_mod heq
                (by rw [mod2_eq_one hmod, mod2_eq_one hmod'])]
            · simp [if_neg heq, if_neg (fun e : k = k' => heq (congrArg (· / 2) e))]

theorem get?_insert_eq (t : PosTrie V) (k : UInt32) (v : V) :
    (t.insert k v).get? k = some v := by simp [get?_insert]

theorem get?_insert_ne (t : PosTrie V) (k k' : UInt32) (v : V) (h : k ≠ k') :
    (t.insert k v).get? k' = t.get? k' := by simp [get?_insert, h]

theorem get?_delete (t : PosTrie V) (k k' : UInt32) :
    (t.delete k).get? k' = if k = k' then none else t.get? k' := by
  suffices h : ∀ n, ∀ k : UInt32, k.toNat ≤ n →
      ∀ k' (t : PosTrie V),
      (t.delete k).get? k' = if k = k' then none else t.get? k' by
    exact h k.toNat k (Nat.le_refl _) k' t
  intro n
  induction n with
  | zero =>
    intro k hle k' t
    have hk0 : k = 0 := by
      have hn : k.toNat = 0 := Nat.le_zero.mp hle
      exact UInt32.toNat.inj (by simpa using hn)
    subst hk0
    rw (config := { occs := .pos [1] }) [PosTrie.delete.eq_def]
    simp only [dif_pos rfl]
    cases t with
    | empty =>
      by_cases hk' : k' = 0
      · subst hk'; rfl
      · simp [if_neg (Ne.symm hk'), if_neg hk']
    | leaf w =>
      by_cases hk' : k' = 0
      · subst hk'; rfl
      · simp [if_neg (Ne.symm hk'), get?_leaf_nz w k' hk']
    | node w l r =>
      by_cases hk' : k' = 0
      · subst hk'; simp [mkNode_get?_zero]
      · simp [mkNode_get?_nz _ _ _ _ hk', get?_node_nz _ _ _ _ hk', Ne.symm hk']
  | succ n ih =>
    intro k hle k' t
    by_cases hk0 : k = 0
    · subst hk0
      rw (config := { occs := .pos [1] }) [PosTrie.delete.eq_def]
      simp only [dif_pos rfl]
      cases t with
      | empty =>
        by_cases hk' : k' = 0
        · subst hk'; rfl
        · simp [if_neg (Ne.symm hk'), if_neg hk']
      | leaf w =>
        by_cases hk' : k' = 0
        · subst hk'; rfl
        · simp [if_neg (Ne.symm hk'), get?_leaf_nz w k' hk']
      | node w l r =>
        by_cases hk' : k' = 0
        · subst hk'; simp [mkNode_get?_zero]
        · simp [mkNode_get?_nz _ _ _ _ hk', get?_node_nz _ _ _ _ hk', Ne.symm hk']
    · have hdivle : (k / 2).toNat ≤ n := by
        rw [toNat_div2]; have := toNat_ne_zero hk0; omega
      rw (config := { occs := .pos [1] }) [PosTrie.delete.eq_def]
      simp only [dif_neg hk0]
      by_cases hmod : k % 2 = 0
      · simp only [if_pos hmod]
        by_cases hk'0 : k' = 0
        · subst hk'0
          simp only [if_neg hk0, mkNode_get?_zero]
          exact (get?_zero t).symm
        · rw [mkNode_get?_nz _ _ _ _ hk'0, get?_nz t k' hk'0]
          by_cases hmod' : k' % 2 = 0
          · simp only [hmod', ↓reduceIte]
            rw [ih (k / 2) hdivle (k' / 2) t.lc]
            by_cases heq : k / 2 = k' / 2
            · simp [heq, uint32_eq_of_div_mod heq (by rw [hmod, hmod'])]
            · simp [if_neg heq, if_neg (fun e : k = k' => heq (congrArg (· / 2) e))]
          · have hkk' : k ≠ k' := fun e => hmod' (e ▸ hmod)
            simp [if_neg hmod', if_neg hkk']
      · simp only [if_neg hmod]
        by_cases hk'0 : k' = 0
        · subst hk'0
          simp only [if_neg hk0, mkNode_get?_zero]
          exact (get?_zero t).symm
        · rw [mkNode_get?_nz _ _ _ _ hk'0, get?_nz t k' hk'0]
          by_cases hmod' : k' % 2 = 0
          · have hkk' : k ≠ k' := fun e => hmod (e ▸ hmod')
            simp [hmod', if_neg hkk']
          · simp only [if_neg hmod']
            rw [ih (k / 2) hdivle (k' / 2) t.rc]
            by_cases heq : k / 2 = k' / 2
            · simp [heq, uint32_eq_of_div_mod heq
                (by rw [mod2_eq_one hmod, mod2_eq_one hmod'])]
            · simp [if_neg heq, if_neg (fun e : k = k' => heq (congrArg (· / 2) e))]

theorem get?_delete_eq (t : PosTrie V) (k : UInt32) : (t.delete k).get? k = none := by
  simp [get?_delete]

theorem get?_delete_ne (t : PosTrie V) (k k' : UInt32) (h : k ≠ k') :
    (t.delete k).get? k' = t.get? k' := by simp [get?_delete, h]

-- ─── bindAlter ───────────────────────────────────────────────────────────────

-- (step, pfx) tracks global key: position j has global key j*step+pfx.
private def bindAlterAux (f : UInt32 → V → Option V')
    (t : PosTrie V) (step pfx : UInt32) : PosTrie V' :=
  match t with
  | .empty      => .empty
  | .leaf v     => mkNode (f pfx v) .empty .empty
  | .node v l r =>
    mkNode (v.bind (f pfx))
           (bindAlterAux f l (step * 2) pfx)
           (bindAlterAux f r (step * 2) (pfx + step))

def bindAlter (f : UInt32 → V → Option V') (t : PosTrie V) : PosTrie V' :=
  bindAlterAux f t 1 0

private theorem get?_bindAlterAux (f : UInt32 → V → Option V')
    (t : PosTrie V) (step pfx j : UInt32) :
    (bindAlterAux f t step pfx).get? j = (t.get? j).bind (f (j * step + pfx)) := by
  induction t generalizing step pfx j with
  | empty => simp [bindAlterAux]
  | leaf v =>
    simp only [bindAlterAux]
    by_cases hj : j = 0
    · subst hj; simp [mkNode_get?_zero]
    · rw [mkNode_get?_nz _ _ _ _ hj, get?_leaf_nz _ _ hj]
      simp [hj]
  | node v l r ihl ihr =>
    simp only [bindAlterAux]
    by_cases hj : j = 0
    · subst hj; simp [mkNode_get?_zero, get?_node_zero]
    · rw [mkNode_get?_nz _ _ _ _ hj, get?_node_nz _ _ _ _ hj]
      by_cases hmod : j % 2 = 0
      · simp only [hmod, ↓reduceIte]
        have hkey : j / 2 * (step * 2) + pfx = j * step + pfx := by
          have h1 : j / 2 * (step * 2) = j * step := by
            rw [mul_step_comm, uint32_div2_even hmod]
          rw [h1]
        rw [ihl (step * 2) pfx (j / 2), hkey]
      · simp only [if_neg hmod]
        have hkey : j / 2 * (step * 2) + (pfx + step) = j * step + pfx := by
          have h1 : j / 2 * (step * 2) = j / 2 * 2 * step := mul_step_comm (j / 2) step
          have h2 : j / 2 * 2 * step + (pfx + step) = (j / 2 * 2 + 1) * step + pfx := by
            rw [uint32_add_mul, uint32_one_mul]
            rw [← uint32_add_assoc (j / 2 * 2 * step) pfx step]
            rw [uint32_add_right_comm (j / 2 * 2 * step) pfx step]
          rw [h1, h2, uint32_div2_odd hmod]
        rw [ihr (step * 2) (pfx + step) (j / 2), hkey]

theorem get?_bindAlter_eq (f : UInt32 → V → Option V') (t : PosTrie V) (k : UInt32) :
    (t.bindAlter f).get? k = (t.get? k).bind (f k) := by
  simp only [bindAlter, get?_bindAlterAux, uint32_mul1_add0]

-- ─── merge ───────────────────────────────────────────────────────────────────

private def mergeAux (op : UInt32 → V → V → V)
    (t1 t2 : PosTrie V) (step pfx : UInt32) : PosTrie V :=
  match t1, t2 with
  | .empty, t  => t
  | t, .empty  => t
  | .leaf v,  .leaf w  => mkNode (some (op pfx v w)) .empty .empty
  | .leaf v,  .node w l2 r2 =>
    mkNode (Option.merge (op pfx) (some v) w) l2 r2
  | .node v l1 r1, .leaf w =>
    mkNode (Option.merge (op pfx) v (some w)) l1 r1
  | .node v l1 r1, .node w l2 r2 =>
    mkNode (Option.merge (op pfx) v w)
           (mergeAux op l1 l2 (step * 2) pfx)
           (mergeAux op r1 r2 (step * 2) (pfx + step))

def merge (op : UInt32 → V → V → V) (t1 t2 : PosTrie V) : PosTrie V :=
  mergeAux op t1 t2 1 0

private theorem get?_mergeAux (op : UInt32 → V → V → V)
    (t1 t2 : PosTrie V) (step pfx j : UInt32) :
    (mergeAux op t1 t2 step pfx).get? j =
      Option.merge (op (j * step + pfx)) (t1.get? j) (t2.get? j) := by
  induction t1 generalizing t2 step pfx j with
  | empty => simp [mergeAux]
  | leaf v =>
    cases t2 with
    | empty => simp [mergeAux]
    | leaf w =>
      simp only [mergeAux]
      by_cases hj : j = 0
      · subst hj; simp [mkNode_get?_zero]
      · rw [mkNode_get?_nz _ _ _ _ hj]
        simp [get?_leaf_nz _ _ hj, hj]
    | node w l2 r2 =>
      simp only [mergeAux]
      by_cases hj : j = 0
      · subst hj; simp [mkNode_get?_zero]
      · rw [mkNode_get?_nz _ _ _ _ hj, get?_node_nz _ _ _ _ hj]
        simp [get?_leaf_nz _ _ hj, hj]
  | node v l1 r1 ihl ihr =>
    cases t2 with
    | empty => simp [mergeAux]
    | leaf w =>
      simp only [mergeAux]
      by_cases hj : j = 0
      · subst hj; simp [mkNode_get?_zero]
      · rw [mkNode_get?_nz _ _ _ _ hj, get?_node_nz _ _ _ _ hj]
        simp [get?_leaf_nz _ _ hj, hj]
    | node w l2 r2 =>
      simp only [mergeAux]
      by_cases hj : j = 0
      · subst hj; simp [mkNode_get?_zero, get?_node_zero]
      · rw [mkNode_get?_nz _ _ _ _ hj, get?_node_nz _ _ _ _ hj, get?_node_nz _ _ _ _ hj]
        by_cases hmod : j % 2 = 0
        · simp only [hmod, ↓reduceIte]
          have hkey : j / 2 * (step * 2) + pfx = j * step + pfx := by
            have h1 : j / 2 * (step * 2) = j * step := by
              rw [mul_step_comm, uint32_div2_even hmod]
            rw [h1]
          rw [ihl l2 (step * 2) pfx (j / 2), hkey]
        · simp only [if_neg hmod]
          have hkey : j / 2 * (step * 2) + (pfx + step) = j * step + pfx := by
            have h1 : j / 2 * (step * 2) = j / 2 * 2 * step := mul_step_comm (j / 2) step
            have h2 : j / 2 * 2 * step + (pfx + step) = (j / 2 * 2 + 1) * step + pfx := by
              rw [uint32_add_mul, uint32_one_mul]
              rw [← uint32_add_assoc (j / 2 * 2 * step) pfx step]
              rw [uint32_add_right_comm (j / 2 * 2 * step) pfx step]
            rw [h1, h2, uint32_div2_odd hmod]
          rw [ihr r2 (step * 2) (pfx + step) (j / 2), hkey]

theorem get?_merge_eq (op : UInt32 → V → V → V) (t1 t2 : PosTrie V) (k : UInt32) :
    (merge op t1 t2).get? k = Option.merge (op k) (t1.get? k) (t2.get? k) := by
  simp only [merge, get?_mergeAux, uint32_mul1_add0]

-- ─── PartialMap instance ─────────────────────────────────────────────────────

open Iris.Std in
instance : Iris.Std.PartialMap PosTrie UInt32 where
  get?      t k   := t.get? k
  insert    t k v := t.insert k v
  delete    t k   := t.delete k
  empty           := .empty
  bindAlter f t   := t.bindAlter f
  merge op  t1 t2 := t1.merge op t2

-- ─── LawfulPartialMap instance ───────────────────────────────────────────────

open Iris.Std in
instance : Iris.Std.LawfulPartialMap PosTrie UInt32 where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [Iris.Std.get?, Iris.Std.insert]
    subst h; exact PosTrie.get?_insert_eq m k v
  get?_insert_ne {V m k k' v} h := by
    simp only [Iris.Std.get?, Iris.Std.insert]
    exact PosTrie.get?_insert_ne m k k' v h
  get?_delete_eq {V m k k'} h := by
    simp only [Iris.Std.get?, Iris.Std.delete]
    subst h; exact PosTrie.get?_delete_eq m k
  get?_delete_ne {V m k k'} h := by
    simp only [Iris.Std.get?, Iris.Std.delete]
    exact PosTrie.get?_delete_ne m k k' h
  get?_bindAlter := by
    simp only [Iris.Std.get?, Iris.Std.bindAlter]
    exact PosTrie.get?_bindAlter_eq _ _ _
  get?_merge {V op m₁ m₂ k} := by
    simp only [Iris.Std.get?, Iris.Std.merge]
    exact PosTrie.get?_merge_eq op m₁ m₂ k
  equiv_iff_eq {V m₁ m₂} :=
    ⟨fun _ => sorry, fun h => h ▸ fun _ => rfl⟩

-- ─── toList / FiniteMap / LawfulFiniteMap ────────────────────────────────────

-- depth replaces the old UInt32 step to avoid overflow at depth ≥ 32.
-- skipRoot=true skips position 0 of the current subtrie.
private def toListAux (t : PosTrie V) (depth : Nat) (pfx : UInt32) (skipRoot : Bool) :
    List (UInt32 × V) :=
  match t with
  | .empty  => []
  | .leaf u => if skipRoot then [] else [(pfx, u)]
  | .node o l r =>
    (if skipRoot then [] else match o with | none => [] | some u => [(pfx, u)]) ++
    if depth ≥ 32 then [] else
      toListAux l (depth + 1) pfx true ++
      toListAux r (depth + 1) (pfx + UInt32.ofNat (2 ^ depth)) false

def toList (t : PosTrie V) : List (UInt32 × V) := toListAux t 0 0 false

-- j < 2^(32-d) implies j < 2^32 = UInt32.size
private theorem tl_j_lt_size {d j : Nat} (hj : j < 2^(32-d)) : j < UInt32.size :=
  Nat.lt_of_lt_of_le hj (by
    simp only [UInt32.size]
    exact Nat.pow_le_pow_right (by omega) (Nat.sub_le 32 d))

-- j < 2^(32-d) and d ≤ 32 implies j * 2^d < 2^32 = UInt32.size
private theorem tl_pow_j_lt_size {d j : Nat} (hd : d ≤ 32) (hj : j < 2^(32-d)) :
    j * 2^d < UInt32.size := by
  simp only [UInt32.size]
  have hmul := (Nat.mul_lt_mul_right (Nat.two_pow_pos d)).mpr hj
  rw [show 2^(32-d) * 2^d = 2^32 from by rw [← Nat.pow_add, Nat.sub_add_cancel hd]] at hmul
  exact hmul

private theorem tl_ofNat_toNat {n : Nat} (h : n < UInt32.size) :
    (UInt32.ofNat n).toNat = n := by
  simp [UInt32.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem tl_ofNat_inj {n m : Nat} (hn : n < UInt32.size) (hm : m < UInt32.size)
    (h : UInt32.ofNat n = UInt32.ofNat m) : n = m := by
  have := congrArg UInt32.toNat h
  rwa [tl_ofNat_toNat hn, tl_ofNat_toNat hm] at this

private theorem tl_ofNat_div2 {n : Nat} (hn : n < UInt32.size) :
    UInt32.ofNat n / 2 = UInt32.ofNat (n / 2) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_div, tl_ofNat_toNat hn, show (2 : UInt32).toNat = 2 from by decide,
      tl_ofNat_toNat (by simp only [UInt32.size] at hn ⊢; omega)]

private theorem tl_ofNat_mod2 {n : Nat} (hn : n < UInt32.size) :
    UInt32.ofNat n % 2 = UInt32.ofNat (n % 2) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_mod, tl_ofNat_toNat hn, show (2 : UInt32).toNat = 2 from by decide,
      tl_ofNat_toNat (by simp only [UInt32.size] at hn ⊢; omega)]

private theorem tl_ofNat_add {a b : Nat} (h : a + b < UInt32.size) :
    UInt32.ofNat a + UInt32.ofNat b = UInt32.ofNat (a + b) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_add, tl_ofNat_toNat (by omega), tl_ofNat_toNat (by omega),
      tl_ofNat_toNat h, Nat.mod_eq_of_lt h]

-- 2^(32-(d+1)) * 2 = 2^(32-d) when d < 32
private theorem tl_pow_step (d : Nat) (hd : d < 32) : 2^(32-(d+1)) * 2 = 2^(32-d) := by
  rw [show (2:Nat) = 2^1 from (Nat.pow_one 2).symm, ← Nat.pow_add]
  congr 1; omega

-- full characterization: (k,v) ∈ toListAux t d pfx skip ↔
--   ∃ j < 2^(32-d), (skip → j≠0) ∧ k = pfx + ofNat(j*2^d) ∧ t.get? (ofNat j) = some v
private theorem mem_toListAux_iff (t : PosTrie V) (depth : Nat) (pfx : UInt32) (skip : Bool)
    (k : UInt32) (v : V) :
    (k, v) ∈ toListAux t depth pfx skip ↔
    ∃ j : Nat, j < 2^(32-depth) ∧ (skip → j ≠ 0) ∧
      k = pfx + UInt32.ofNat (j * 2^depth) ∧ t.get? (UInt32.ofNat j) = some v := by
  induction t generalizing depth pfx skip k v with
  | empty => simp [toListAux, get?]
  | leaf u =>
    simp only [toListAux]
    constructor
    · intro hmem
      cases skip with
      | true  => simp at hmem
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton,
                   Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        exact ⟨0, Nat.two_pow_pos _, fun h => absurd h (by decide),
               by simp, by simp [get?]⟩
    · rintro ⟨j, hj, hskip, hk, hget⟩
      have hjsz : j < UInt32.size := tl_j_lt_size hj
      -- get? (.leaf u) (ofNat j) = some v requires ofNat j = 0
      have hj0 : UInt32.ofNat j = 0 := by
        simp only [get?] at hget
        rcases Classical.em (UInt32.ofNat j = 0) with h | h
        · exact h
        · rw [if_neg h] at hget; simp at hget
      have hjz : j = 0 := tl_ofNat_inj hjsz (by decide) hj0
      subst hjz
      have h0 : UInt32.ofNat 0 = 0 := by decide
      simp only [Nat.zero_mul, h0, UInt32.add_zero] at hk
      simp only [get?, h0, ↓reduceIte] at hget
      cases skip with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton, Prod.mk.injEq]
        exact ⟨hk, (Option.some.inj hget).symm⟩
      | true  => exact absurd rfl (hskip rfl)
  | node o l r ihl ihr =>
    simp only [toListAux, List.mem_append]
    constructor
    · rintro (hmem | hmem)
      · -- root part: if skip then [] else match o
        cases skip with
        | true  => simp at hmem
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hmem
          cases o with
          | none   => simp at hmem
          | some u =>
            simp only [List.mem_singleton, Prod.mk.injEq] at hmem
            obtain ⟨rfl, rfl⟩ := hmem
            exact ⟨0, Nat.two_pow_pos _, fun h => absurd h (by decide),
                   by simp, by simp [get?]⟩
      · -- children: if depth≥32 then [] else (left ++ right)
        by_cases hge : depth ≥ 32
        · simp only [if_pos hge] at hmem; cases hmem
        · simp only [if_neg hge] at hmem
          have hd32 : depth < 32 := by omega
          simp only [List.mem_append] at hmem
          rcases hmem with hmem | hmem
          · -- left subtrie (skip=true, so j≠0 enforced)
            rw [ihl] at hmem
            obtain ⟨j', hj', hne, hk, hget⟩ := hmem
            have hj'ne  : j' ≠ 0 := hne rfl
            have hj2_lt : j' * 2 < 2^(32-depth) := by
              have h2pow := tl_pow_step depth hd32
              have := (Nat.mul_lt_mul_right (by omega : 0 < 2)).mpr hj'
              omega
            refine ⟨j' * 2, hj2_lt, fun _ => by omega, ?_, ?_⟩
            · -- key: pfx + ofNat(j'*2^(depth+1)) = pfx + ofNat(j'*2*2^depth)
              rw [hk]; congr 1
              rw [show j' * 2 * 2^depth = j' * 2^(depth+1) from by
                rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm (2^depth) 2,
                    ← Nat.mul_assoc j' 2 (2^depth)]]
            · -- get? (.node o l r) (ofNat(j'*2)) = some v
              have hj2sz : j' * 2 < UInt32.size := tl_j_lt_size hj2_lt
              simp only [get?]
              have hne0 : UInt32.ofNat (j' * 2) ≠ 0 := by
                intro h; exact absurd (tl_ofNat_inj hj2sz (by decide) h) (Nat.mul_ne_zero hj'ne (by decide))
              rw [if_neg hne0, tl_ofNat_mod2 hj2sz,
                  show UInt32.ofNat (j' * 2 % 2) = 0 from by simp,
                  if_pos rfl, tl_ofNat_div2 hj2sz,
                  show j' * 2 / 2 = j' from by omega]
              exact hget
          · -- right subtrie (skip=false)
            rw [ihr] at hmem
            obtain ⟨j', hj', _, hk, hget⟩ := hmem
            have hj21_lt : j' * 2 + 1 < 2^(32-depth) := by
              have h2pow := tl_pow_step depth hd32
              have := (Nat.mul_lt_mul_right (by omega : 0 < 2)).mpr hj'
              omega
            refine ⟨j' * 2 + 1, hj21_lt, fun _ => by omega, ?_, ?_⟩
            · -- key: pfx + ofNat(2^depth) + ofNat(j'*2^(depth+1))
              --      = pfx + ofNat((j'*2+1)*2^depth)
              have hj2sz  : j' * 2 < UInt32.size := tl_j_lt_size (show j' * 2 < 2^(32-depth) from by omega)
              have h_key : 2^depth + j' * 2^(depth+1) = (j' * 2 + 1) * 2^depth := by
                rw [Nat.add_mul, Nat.one_mul,
                    show j' * 2 * 2^depth = j' * 2^(depth+1) from by
                      rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm (2^depth) 2,
                          ← Nat.mul_assoc j' 2 (2^depth)],
                    Nat.add_comm]
              have hsum_lt : 2^depth + j' * 2^(depth+1) < UInt32.size :=
                h_key ▸ tl_pow_j_lt_size (by omega) hj21_lt
              rw [hk, UInt32.add_assoc, tl_ofNat_add hsum_lt]
              congr 1; exact congrArg UInt32.ofNat h_key
            · -- get? (.node o l r) (ofNat(j'*2+1)) = some v
              have hj21sz : j' * 2 + 1 < UInt32.size := tl_j_lt_size hj21_lt
              simp only [get?]
              have hne0 : UInt32.ofNat (j' * 2 + 1) ≠ 0 := by
                intro h; exact absurd (tl_ofNat_inj hj21sz (by decide) h) (Nat.succ_ne_zero _)
              rw [if_neg hne0, tl_ofNat_mod2 hj21sz,
                  show UInt32.ofNat ((j' * 2 + 1) % 2) = 1 from by simp,
                  if_neg (by decide),
                  tl_ofNat_div2 hj21sz, show (j' * 2 + 1) / 2 = j' from by omega]
              exact hget
    · -- backward direction
      rintro ⟨j, hj, hskip, hk, hget⟩
      simp only [get?] at hget
      by_cases hj0 : j = 0
      · -- j = 0: root entry
        subst hj0
        have h0 : UInt32.ofNat 0 = 0 := by decide
        simp only [Nat.zero_mul, h0, UInt32.add_zero] at hk
        simp only [h0, ↓reduceIte] at hget
        left
        cases skip with
        | true  => exact absurd rfl (hskip rfl)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hk, hget]; simp
      · -- j ≠ 0: from children
        right
        have hd32 : depth < 32 := by
          rcases Nat.lt_or_ge depth 32 with h | h
          · exact h
          · simp only [Nat.sub_eq_zero_of_le h, Nat.pow_zero] at hj; omega
        simp only [show ¬(depth ≥ 32) from by omega, ↓reduceIte, List.mem_append]
        have hjsz : j < UInt32.size := tl_j_lt_size hj
        have hne0 : UInt32.ofNat j ≠ 0 := by
          intro h; exact absurd (tl_ofNat_inj hjsz (by decide) h) hj0
        by_cases hmod : j % 2 = 0
        · -- even: in left subtrie
          left; rw [ihl]
          have hj'_lt : j / 2 < 2^(32-(depth+1)) := by
            have h2pow := tl_pow_step depth hd32
            have : j / 2 * 2 ≤ j := Nat.div_mul_le_self j 2
            have hmul := (Nat.mul_lt_mul_right (by omega : 0 < 2)).mp (by omega : j / 2 * 2 < 2^(32-(depth+1)) * 2)
            exact hmul
          refine ⟨j / 2, hj'_lt, fun _ => by omega, ?_, ?_⟩
          · -- key: pfx + ofNat(j*2^depth) = pfx + ofNat(j/2 * 2^(depth+1))
            rw [hk]; congr 1
            have hj2 : j / 2 * 2 = j := by omega
            have heq : j / 2 * 2^(depth+1) = j * 2^depth := by
              calc j / 2 * 2^(depth+1)
                  = j / 2 * (2^depth * 2)   := by rw [Nat.pow_add, Nat.pow_one]
                _ = j / 2 * (2 * 2^depth)   := by rw [Nat.mul_comm (2^depth) 2]
                _ = j / 2 * 2 * 2^depth     := by rw [← Nat.mul_assoc (j/2) 2 (2^depth)]
                _ = j * 2^depth              := by rw [hj2]
            rw [heq]
          · -- get? node (ofNat j) = some v → l.get? (ofNat(j/2)) = some v
            rw [if_neg hne0, tl_ofNat_mod2 hjsz,
                show UInt32.ofNat (j % 2) = 0 from by simp [hmod], if_pos rfl,
                tl_ofNat_div2 hjsz] at hget
            exact hget
        · -- odd: in right subtrie
          right; rw [ihr]
          have hmod1 : j % 2 = 1 := by omega
          have hj'_lt : j / 2 < 2^(32-(depth+1)) := by
            have h2pow := tl_pow_step depth hd32
            have : j / 2 * 2 ≤ j := Nat.div_mul_le_self j 2
            have hmul := (Nat.mul_lt_mul_right (by omega : 0 < 2)).mp (by omega : j / 2 * 2 < 2^(32-(depth+1)) * 2)
            exact hmul
          have hj'sz  : j / 2 < UInt32.size := tl_j_lt_size hj'_lt
          have h2d_lt : 2^depth < UInt32.size := by
            have h1 := tl_pow_j_lt_size (by omega) (show 1 < 2^(32-depth) from by omega)
            rwa [Nat.one_mul] at h1
          refine ⟨j / 2, hj'_lt, fun h => absurd h (by decide), ?_, ?_⟩
          · -- key: pfx + ofNat(j*2^depth) = (pfx + ofNat(2^depth)) + ofNat(j/2 * 2^(depth+1))
            rw [hk]
            have hsum : 2^depth + j / 2 * 2^(depth+1) < UInt32.size :=
              calc 2^depth + j / 2 * 2^(depth+1)
                  = (j / 2 * 2 + 1) * 2^depth := by
                        rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, Nat.pow_one,
                            Nat.mul_comm (2^depth) 2, ← Nat.mul_assoc (j/2) 2 (2^depth), Nat.add_comm]
                _ = j * 2^depth := by congr 1; omega
                _ < UInt32.size := tl_pow_j_lt_size (by omega) hj
            have hj2 : j / 2 * 2 + 1 = j := by omega
            have h_mul : j / 2 * 2^(depth+1) = j / 2 * 2 * 2^depth := by
              rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm (2^depth) 2,
                  ← Nat.mul_assoc (j/2) 2 (2^depth)]
            have hnat : 2^depth + j / 2 * 2^(depth+1) = j * 2^depth := by
              rw [h_mul, Nat.add_comm,
                  show j / 2 * 2 * 2^depth + 2^depth = (j / 2 * 2 + 1) * 2^depth from by
                    rw [Nat.add_mul, Nat.one_mul],
                  hj2]
            rw [UInt32.add_assoc, tl_ofNat_add hsum, hnat]
          · -- get? node (ofNat j) = some v → r.get? (ofNat(j/2)) = some v
            rw [if_neg hne0, tl_ofNat_mod2 hjsz,
                show UInt32.ofNat (j % 2) = 1 from by simp [hmod1],
                if_neg (by decide : ¬(1:UInt32) = 0),
                tl_ofNat_div2 hjsz] at hget
            exact hget

open Iris.Std in
instance : Iris.Std.FiniteMap PosTrie UInt32 where
  toList t := t.toList

-- j * 2^d < UInt32.size from j < 2^(32-d), even when d > 32
private theorem tl_pow_j_lt_size' {d j : Nat} (hj : j < 2^(32-d)) : j * 2^d < UInt32.size := by
  by_cases hd : d ≤ 32
  · exact tl_pow_j_lt_size hd hj
  · simp only [Nat.sub_eq_zero_of_le (show 32 ≤ d from by omega)] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [UInt32.size]

-- same key in toListAux means same value
private theorem toListAux_key_unique (t : PosTrie V) (d : Nat) (pfx : UInt32) (skip : Bool)
    (k : UInt32) (v₁ v₂ : V)
    (h₁ : (k, v₁) ∈ toListAux t d pfx skip) (h₂ : (k, v₂) ∈ toListAux t d pfx skip) :
    v₁ = v₂ := by
  rw [mem_toListAux_iff] at h₁ h₂
  obtain ⟨j₁, hj₁, _, hk₁, hg₁⟩ := h₁
  obtain ⟨j₂, hj₂, _, hk₂, hg₂⟩ := h₂
  have hj1sz : j₁ * 2^d < UInt32.size := tl_pow_j_lt_size' hj₁
  have hj2sz : j₂ * 2^d < UInt32.size := tl_pow_j_lt_size' hj₂
  have hpow_eq : UInt32.ofNat (j₁ * 2^d) = UInt32.ofNat (j₂ * 2^d) := by
    have h := hk₁.symm.trans hk₂
    have key := congrArg UInt32.toNat h
    simp only [UInt32.toNat_add, tl_ofNat_toNat hj1sz, tl_ofNat_toNat hj2sz] at key
    have hpfxlt := UInt32.toNat_lt pfx
    simp only [UInt32.size] at key hj1sz hj2sz hpfxlt
    exact congrArg UInt32.ofNat (by omega)
  have hj12 : j₁ = j₂ :=
    Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos d) (tl_ofNat_inj hj1sz hj2sz hpow_eq)
  exact Option.some.inj (hg₁.symm.trans (hj12 ▸ hg₂))

-- 2^d + jr * 2^(d+1) < UInt32.size when d < 32 and jr < 2^(32-(d+1))
private theorem tl_rsum_lt_size {d jr : Nat} (hd32 : d < 32) (hjr : jr < 2^(32-(d+1))) :
    2^d + jr * 2^(d+1) < UInt32.size := by
  have h2step := tl_pow_step d hd32
  have hd_le : d ≤ 32 := by omega
  have h1jr2_lt : 1 + jr * 2 < 2^(32-d) := by omega
  have hmul := (Nat.mul_lt_mul_right (Nat.two_pow_pos d)).mpr h1jr2_lt
  rw [show 2^(32-d) * 2^d = UInt32.size from by
    rw [← Nat.pow_add, Nat.sub_add_cancel hd_le]] at hmul
  rw [show 2^d + jr * 2^(d+1) = (1 + jr * 2) * 2^d from by
    rw [Nat.add_mul, Nat.one_mul,
        show jr * 2 * 2^d = jr * 2^(d+1) from by
          rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm (2^d) 2, ← Nat.mul_assoc jr 2 (2^d)]]]
  exact hmul

-- toListAux produces a nodup list of pairs
private theorem toListAux_nodup (t : PosTrie V) (d : Nat) (pfx : UInt32) (skip : Bool) :
    (toListAux t d pfx skip).Nodup := by
  induction t generalizing d pfx skip with
  | empty => simp [toListAux]
  | leaf u => cases skip <;> simp [toListAux]
  | node o l r ihl ihr =>
    simp only [toListAux]
    by_cases hge : d ≥ 32
    · simp only [if_pos hge, List.append_nil]
      cases skip <;> simp <;> cases o <;> simp
    · have hd32 : d < 32 := by omega
      simp only [if_neg hge]
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · cases skip <;> simp <;> cases o <;> simp
      · rw [List.nodup_append]
        refine ⟨ihl (d+1) pfx true, ihr (d+1) _ false, ?_⟩
        intro ⟨k, v⟩ hml ⟨k', v'⟩ hmr heq
        have hkeq : k = k' := congrArg Prod.fst heq
        rw [mem_toListAux_iff] at hml hmr
        obtain ⟨jl, hjl, _, hkl, _⟩ := hml
        obtain ⟨jr, hjr, _, hkr, _⟩ := hmr
        have hjlsz : jl * 2^(d+1) < UInt32.size := tl_pow_j_lt_size (by omega) hjl
        have hsum : 2^d + jr * 2^(d+1) < UInt32.size := tl_rsum_lt_size hd32 hjr
        have hnat_eq : jl * 2^(d+1) = 2^d + jr * 2^(d+1) := by
          have h := (hkl.symm.trans hkeq).trans hkr
          have hrhs := tl_ofNat_add hsum
          have h' : pfx + UInt32.ofNat (jl * 2^(d+1)) = pfx + UInt32.ofNat (2^d + jr * 2^(d+1)) :=
            h.trans (by rw [UInt32.add_assoc, hrhs])
          have key := congrArg UInt32.toNat h'
          simp only [UInt32.toNat_add, tl_ofNat_toNat hjlsz, tl_ofNat_toNat hsum] at key
          have hpfxlt := UInt32.toNat_lt pfx
          simp only [UInt32.size] at key hjlsz hsum hpfxlt
          -- generalize both nonlinear sides so omega has simple linear vars
          generalize hX : jl * 2^(d+1) = X
          generalize hY : 2^d + jr * 2^(d+1) = Y
          rw [hX] at key hjlsz
          rw [hY] at key hsum
          omega
        have h_parity : jl * 2 = 1 + jr * 2 := by
          apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos d)
          rw [show jl * 2 * 2^d = jl * 2^(d+1) from by
                rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm (2^d) 2, ← Nat.mul_assoc jl 2 (2^d)],
              hnat_eq,
              show 2^d + jr * 2^(d+1) = (1 + jr * 2) * 2^d from by
                rw [Nat.add_mul, Nat.one_mul,
                    show jr * 2 * 2^d = jr * 2^(d+1) from by
                      rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm (2^d) 2,
                          ← Nat.mul_assoc jr 2 (2^d)]]]
        exact absurd h_parity (by omega)
      · intro ⟨k, v⟩ hroot ⟨k', v'⟩ hmem heq
        have hkeq : k = k' := congrArg Prod.fst heq
        simp only [List.mem_append] at hmem
        cases hskip : skip with
        | true => simp [hskip] at hroot
        | false =>
          simp only [hskip, Bool.false_eq_true, ↓reduceIte] at hroot
          cases ho : o with
          | none => simp [ho] at hroot
          | some u =>
            simp only [ho, List.mem_singleton, Prod.mk.injEq] at hroot
            obtain ⟨rfl, rfl⟩ := hroot
            rcases hmem with hmem | hmem
            · rw [mem_toListAux_iff] at hmem
              obtain ⟨j', hj', hne, hk', _⟩ := hmem
              have hj'sz : j' * 2^(d+1) < UInt32.size := tl_pow_j_lt_size (by omega) hj'
              have hzero : UInt32.ofNat (j' * 2^(d+1)) = 0 := by
                have heq' := hkeq.trans hk'
                have key := congrArg UInt32.toNat heq'
                simp only [UInt32.toNat_add, tl_ofNat_toNat hj'sz] at key
                have hpfxlt := UInt32.toNat_lt k
                simp only [UInt32.size] at key hj'sz hpfxlt
                have hnat : j' * 2^(d+1) = 0 := by omega
                rw [hnat]; decide
              have h0nat : j' * 2^(d+1) = 0 :=
                tl_ofNat_inj hj'sz (by decide)
                  (hzero.trans (show (0 : UInt32) = UInt32.ofNat 0 from rfl))
              exact absurd ((Nat.mul_eq_zero.mp h0nat).resolve_right
                (by have := Nat.two_pow_pos (d+1); omega)) (hne rfl)
            · rw [mem_toListAux_iff] at hmem
              obtain ⟨j', hj', _, hk', _⟩ := hmem
              have hj'sz : j' * 2^(d+1) < UInt32.size := tl_pow_j_lt_size (by omega) hj'
              have hsum' : 2^d + j' * 2^(d+1) < UInt32.size := tl_rsum_lt_size hd32 hj'
              have h0nat : 2^d + j' * 2^(d+1) = 0 := by
                have h1 := hkeq.trans hk'
                have h2 := tl_ofNat_add hsum'
                have h3 : k = k + UInt32.ofNat (2^d + j' * 2^(d+1)) :=
                  h1.trans (by rw [UInt32.add_assoc, h2])
                have key := congrArg UInt32.toNat h3
                simp only [UInt32.toNat_add, tl_ofNat_toNat hsum'] at key
                have hpfxlt := UInt32.toNat_lt k
                simp only [UInt32.size] at key hsum' hpfxlt
                generalize hZ : 2^d + j' * 2^(d+1) = Z
                rw [hZ] at key hsum'
                omega
              have := Nat.two_pow_pos d; omega

open Iris.Std in
instance : Iris.Std.LawfulFiniteMap PosTrie UInt32 where
  toList_empty := rfl
  toList_noDupKeys {V m} := by
    show ((toListAux m 0 0 false).map (·.1)).Nodup
    apply FromMathlib.Nodup.map_on
    · intro ⟨k₁, v₁⟩ hm₁ ⟨k₂, v₂⟩ hm₂ hkeq
      simp only at hkeq; subst hkeq
      exact Prod.ext rfl (toListAux_key_unique m 0 0 false k₁ v₁ v₂ hm₁ hm₂)
    · exact toListAux_nodup m 0 0 false
  toList_get {V m k v} := by
    show (k, v) ∈ toListAux m 0 0 false ↔ m.get? k = some v
    rw [mem_toListAux_iff]
    simp only [Nat.sub_zero, show (2:Nat)^0 = 1 from rfl, Nat.mul_one,
               UInt32.zero_add, Bool.false_eq_true, false_implies, true_and]
    constructor
    · rintro ⟨j, _, hk, hget⟩
      rwa [hk]
    · intro hget
      refine ⟨k.toNat, ?_, UInt32.ofNat_toNat.symm, by rwa [UInt32.ofNat_toNat]⟩
      have h := UInt32.toNat_lt k
      omega

end PosTrie
end Wasm.SepLogic
