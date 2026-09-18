import CodeLib.RustStd.HashMap.SortedByKey

/-!
# The two sorting networks of the compiled small sort

The compiled `sort_unstable_by_key` of the entry buffer sorts a short run
with a fixed comparator network.  Absolute function 24 of
`programs/rust/build/rust_hash_map/program.wat` holds two such networks as
straight-line code.  The first block, WAT lines 6233 to 7008, sorts nine
entries with 25 comparators.  The second block, WAT lines 7016 to 8389,
sorts thirteen entries with 45 comparators.  Neither block holds a branch
instruction.

One comparator is one `i32.lt_u` on two key loads and then three `select`
instructions: one picks the whole eight-byte entry that goes to the low
slot, one picks the value word of the high slot, and one picks the key
word of the high slot.  The first block has 75 `select` instructions and
the second has 135, which is three per comparator.  A comparator writes
its two slots back with one `i64.store` at the low slot and two
`i32.store` at the high slot, so the store offsets name the two slots.
The lists `sort9Net` and `sort13Net` below are read from those offsets,
divided by the eight-byte entry stride.

`cmpSwap` is the pure model of one comparator and `applyNetwork` is the
pure model of a block.  The three facts a body proof wants are
`applyNetwork_length`, `applyNetwork_perm` and `sortsAll`.

`sortsAll net n` says that the network sorts every list of `n` keys.  It
is proved by the zero-one principle: a comparator network that sorts
every list of zeros and ones sorts every list.  `zeroOne` carries that
argument.  The zero-one check is exhaustive, so it is a `decide` over
`2 ^ n` bit masks.  A mask runs much faster than a list of `Bool` in the
kernel, because a comparator on a mask is a few `Nat` bit operations that
the kernel computes with GMP.  `applyMask_eq_bits` says that the mask run
and the list run agree.

The exhaustive checks use `decide +kernel`, so the Lean kernel itself
runs every one of the 512 masks of the first network and the 8192 masks
of the second.  No check is given to the compiler.
-/

namespace Wasm.RustStd.HashMap.Table

/-! ## One comparator -/

/-- A comparator names two slots of the list.  The first slot takes the
smaller of the two entries. -/
abbrev Comparator := Nat × Nat

section Pure

variable {α β : Type}

/-- The entry that a comparator sends to its low slot. -/
def cmpMin (lt : α → α → Bool) (a b : α) : α := if lt b a then b else a

/-- The entry that a comparator sends to its high slot. -/
def cmpMax (lt : α → α → Bool) (a b : α) : α := if lt b a then a else b

/-- The `select` that feeds the low slot. -/
theorem minPair_eq (lt : α → α → Bool) (a b : α) :
    cmpMin lt a b = if lt b a then b else a := rfl

/-- The `select` that feeds the high slot. -/
theorem maxPair_eq (lt : α → α → Bool) (a b : α) :
    cmpMax lt a b = if lt b a then a else b := rfl

/-- One comparator.  An index out of range leaves the list unchanged,
which no live network uses. -/
def cmpSwap (lt : α → α → Bool) (l : List α) (c : Comparator) : List α :=
  if h : c.1 < l.length ∧ c.2 < l.length then
    (l.set c.1 (cmpMin lt (l[c.1]'h.1) (l[c.2]'h.2))).set c.2
      (cmpMax lt (l[c.1]'h.1) (l[c.2]'h.2))
  else l

/-- In range a comparator is two `List.set` steps.  This is the shape
that `PairSlice.swapAt_eq_set_set` gives for the compiled stores. -/
theorem cmpSwap_eq_set_set (lt : α → α → Bool) (l : List α)
    {c : Comparator} (h1 : c.1 < l.length) (h2 : c.2 < l.length) :
    cmpSwap lt l c =
      (l.set c.1 (cmpMin lt l[c.1] l[c.2])).set c.2
        (cmpMax lt l[c.1] l[c.2]) :=
  dif_pos ⟨h1, h2⟩

/-- An index out of range keeps the list. -/
theorem cmpSwap_of_not_lt (lt : α → α → Bool) (l : List α)
    {c : Comparator} (h : ¬(c.1 < l.length ∧ c.2 < l.length)) :
    cmpSwap lt l c = l :=
  dif_neg h

@[simp] theorem cmpSwap_length (lt : α → α → Bool) (l : List α)
    (c : Comparator) : (cmpSwap lt l c).length = l.length := by
  unfold cmpSwap
  split <;> simp

private theorem set_set_perm [DecidableEq α] (l : List α) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) :
    ((l.set i l[j]).set j l[i]).Perm l := by
  rw [List.perm_iff_count]
  intro x
  have hlen : (l.set i l[j]).length = l.length := List.length_set
  rw [List.count_set (hlen ▸ hj), List.count_set hi]
  have hset : ((l.set i l[j])[j]'(hlen ▸ hj) == x) = (l[j] == x) := by
    congr 1
    simp [List.getElem_set]
  rw [hset]
  have hle : (if l[i] == x then 1 else 0) ≤ l.count x := by
    split_ifs with h
    · exact List.count_pos_iff.mpr ((beq_iff_eq.mp h) ▸ List.getElem_mem hi)
    · exact Nat.zero_le _
  omega

/-- A comparator keeps the content of the list. -/
theorem cmpSwap_perm [DecidableEq α] (lt : α → α → Bool) (l : List α)
    (c : Comparator) : (cmpSwap lt l c).Perm l := by
  by_cases h : c.1 < l.length ∧ c.2 < l.length
  · rw [cmpSwap_eq_set_set lt l h.1 h.2]
    by_cases hlt : lt l[c.2] l[c.1] = true
    · rw [minPair_eq, maxPair_eq, if_pos hlt, if_pos hlt]
      exact set_set_perm l h.1 h.2
    · rw [minPair_eq, maxPair_eq, if_neg hlt, if_neg hlt,
        List.set_getElem_self h.1]
      rw [List.set_getElem_self h.2]
  · rw [cmpSwap_of_not_lt lt l h]

/-- A comparator commutes with a map that keeps the two `select`
results. -/
theorem cmpSwap_map (lt : α → α → Bool) (lt' : β → β → Bool) (f : α → β)
    (hmin : ∀ a b : α, f (cmpMin lt a b) = cmpMin lt' (f a) (f b))
    (hmax : ∀ a b : α, f (cmpMax lt a b) = cmpMax lt' (f a) (f b))
    (l : List α) (c : Comparator) :
    (cmpSwap lt l c).map f = cmpSwap lt' (l.map f) c := by
  by_cases h : c.1 < l.length ∧ c.2 < l.length
  · have h1 : c.1 < (l.map f).length := by simpa using h.1
    have h2 : c.2 < (l.map f).length := by simpa using h.2
    rw [cmpSwap_eq_set_set lt l h.1 h.2,
      cmpSwap_eq_set_set lt' (l.map f) h1 h2, List.map_set, List.map_set,
      List.getElem_map, List.getElem_map, hmin, hmax]
  · have h' : ¬(c.1 < (l.map f).length ∧ c.2 < (l.map f).length) := by
      simpa using h
    rw [cmpSwap_of_not_lt lt l h, cmpSwap_of_not_lt lt' (l.map f) h']

/-! ## A network -/

/-- A whole comparator block, run in order. -/
def applyNetwork (lt : α → α → Bool) (net : List Comparator)
    (l : List α) : List α :=
  net.foldl (cmpSwap lt) l

@[simp] theorem applyNetwork_nil (lt : α → α → Bool) (l : List α) :
    applyNetwork lt [] l = l := rfl

theorem applyNetwork_cons (lt : α → α → Bool) (c : Comparator)
    (net : List Comparator) (l : List α) :
    applyNetwork lt (c :: net) l = applyNetwork lt net (cmpSwap lt l c) :=
  rfl

/-- Two blocks in a row are one block. -/
theorem applyNetwork_append (lt : α → α → Bool)
    (net₁ net₂ : List Comparator) (l : List α) :
    applyNetwork lt (net₁ ++ net₂) l =
      applyNetwork lt net₂ (applyNetwork lt net₁ l) :=
  List.foldl_append

@[simp] theorem applyNetwork_length (lt : α → α → Bool)
    (net : List Comparator) (l : List α) :
    (applyNetwork lt net l).length = l.length := by
  induction net generalizing l with
  | nil => rfl
  | cons c rest ih => rw [applyNetwork_cons, ih, cmpSwap_length]

/-- A network keeps the content of the list. -/
theorem applyNetwork_perm [DecidableEq α] (lt : α → α → Bool)
    (net : List Comparator) (l : List α) :
    (applyNetwork lt net l).Perm l := by
  induction net generalizing l with
  | nil => exact List.Perm.refl l
  | cons c rest ih =>
      rw [applyNetwork_cons]
      exact (ih (cmpSwap lt l c)).trans (cmpSwap_perm lt l c)

/-- A network commutes with a map that keeps the two `select` results.
The zero-one principle uses this with a step function to `Bool`. -/
theorem applyNetwork_map (lt : α → α → Bool) (lt' : β → β → Bool)
    (f : α → β)
    (hmin : ∀ a b : α, f (cmpMin lt a b) = cmpMin lt' (f a) (f b))
    (hmax : ∀ a b : α, f (cmpMax lt a b) = cmpMax lt' (f a) (f b))
    (net : List Comparator) (l : List α) :
    (applyNetwork lt net l).map f = applyNetwork lt' net (l.map f) := by
  induction net generalizing l with
  | nil => rfl
  | cons c rest ih =>
      rw [applyNetwork_cons, applyNetwork_cons, ih,
        cmpSwap_map lt lt' f hmin hmax l c]

end Pure

/-- The keys of a network run on entries are the network run on the
keys.  The compiled comparator compares key words only. -/
theorem applyNetwork_map_fst (net : List Comparator)
    (ps : List (UInt32 × UInt32)) :
    (applyNetwork (fun a b => decide (a.1 < b.1)) net ps).map Prod.fst =
      applyNetwork (fun a b => decide (a < b)) net (ps.map Prod.fst) := by
  refine applyNetwork_map _ _ Prod.fst ?_ ?_ net ps
  · intro a b
    rw [minPair_eq, minPair_eq]
    split <;> rfl
  · intro a b
    rw [maxPair_eq, maxPair_eq]
    split <;> rfl

/-! ## Bit masks -/

/-- The comparison of a zero-one run.  `false` is below `true`. -/
def ltBool (a b : Bool) : Bool := !a && b

theorem cmpMin_bool (a b : Bool) : cmpMin ltBool a b = (a && b) := by
  cases a <;> cases b <;> rfl

theorem cmpMax_bool (a b : Bool) : cmpMax ltBool a b = (a || b) := by
  cases a <;> cases b <;> rfl

/-- The first `n` bits of `m`, lowest bit first. -/
def maskList (n m : Nat) : List Bool :=
  (List.range n).map (fun i => m.testBit i)

@[simp] theorem maskList_length (n m : Nat) :
    (maskList n m).length = n := by simp [maskList]

@[simp] theorem maskList_getElem (n m k : Nat)
    (h : k < (maskList n m).length) :
    (maskList n m)[k] = m.testBit k := by
  simp [maskList]

/-- One comparator on a mask.  The low slot takes the `and` of the two
bits and the high slot takes the `or`, so the only case that changes the
mask is a one above a zero, and that case flips both bits. -/
def cmpMask (m : Nat) (c : Comparator) : Nat :=
  if m.testBit c.1 && !m.testBit c.2 then m ^^^ (2 ^ c.1 ||| 2 ^ c.2) else m

/-- A whole comparator block on a mask. -/
def applyMask (net : List Comparator) (m : Nat) : Nat := net.foldl cmpMask m

@[simp] theorem applyMask_nil (m : Nat) : applyMask [] m = m := rfl

theorem applyMask_cons (c : Comparator) (net : List Comparator) (m : Nat) :
    applyMask (c :: net) m = applyMask net (cmpMask m c) := rfl

/-- The bits of one comparator step. -/
theorem cmpMask_testBit (m : Nat) (c : Comparator) (k : Nat) :
    (cmpMask m c).testBit k =
      if k = c.1 then m.testBit c.1 && m.testBit c.2
      else if k = c.2 then m.testBit c.1 || m.testBit c.2
      else m.testBit k := by
  unfold cmpMask
  split_ifs with hcond h1 h2 h1 h2
  · subst h1
    simp [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow] at hcond ⊢
    simp [hcond]
  · subst h2
    simp [Nat.testBit_xor, Nat.testBit_or,
      Nat.testBit_two_pow] at hcond ⊢
    simp [hcond]
  · simp [Nat.testBit_xor, Nat.testBit_or, Ne.symm h1, Ne.symm h2]
  · subst h1
    simp at hcond
    cases hm : m.testBit c.1 <;> simp [hm] at hcond ⊢
    exact hcond
  · subst h2
    simp at hcond
    cases hm : m.testBit c.1 <;> simp [hm] at hcond ⊢
    exact hcond
  · rfl

/-- One comparator on the first `n` bits is one comparator on the run of
those bits. -/
theorem cmpSwap_maskList (n m : Nat) (c : Comparator) (h1 : c.1 < n)
    (h2 : c.2 < n) (hne : c.1 ≠ c.2) :
    cmpSwap ltBool (maskList n m) c = maskList n (cmpMask m c) := by
  have hl1 : c.1 < (maskList n m).length := by simpa using h1
  have hl2 : c.2 < (maskList n m).length := by simpa using h2
  rw [cmpSwap_eq_set_set ltBool _ hl1 hl2]
  refine List.ext_getElem (by simp) ?_
  intro k hk hk'
  rw [List.getElem_set, List.getElem_set]
  simp only [maskList_getElem, cmpMin_bool, cmpMax_bool,
    cmpMask_testBit m c k]
  by_cases hkc2 : c.2 = k
  · subst hkc2
    simp [Ne.symm hne]
  · by_cases hkc1 : c.1 = k
    · subst hkc1
      simp [hkc2]
    · simp [hkc1, hkc2, Ne.symm hkc1, Ne.symm hkc2]

/-- The mask run and the list run agree. -/
theorem applyMask_eq_bits (net : List Comparator) (n : Nat)
    (hnet : ∀ c ∈ net, c.1 < n ∧ c.2 < n ∧ c.1 ≠ c.2) (m : Nat) :
    applyNetwork ltBool net (maskList n m) = maskList n (applyMask net m) := by
  induction net generalizing m with
  | nil => rfl
  | cons c rest ih =>
      obtain ⟨h1, h2, hne⟩ := hnet c List.mem_cons_self
      rw [applyNetwork_cons, cmpSwap_maskList n m c h1 h2 hne,
        applyMask_cons]
      exact ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')) _

/-! ## Sorted masks -/

/-- The run never steps down from `true` to `false`. -/
def chainB : List Bool → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (!a || b) && chainB (b :: rest)

/-- The first `n` bits of `m` are in order. -/
def sortedMask (n m : Nat) : Bool := chainB (maskList n m)

/-- A run that never steps down is in order at every pair. -/
theorem pairwise_of_chainB : ∀ bs : List Bool, chainB bs = true →
    bs.Pairwise (fun a b => a = true → b = true) := by
  intro bs
  induction bs with
  | nil => intro _; exact List.Pairwise.nil
  | cons a rest ih =>
      cases rest with
      | nil => intro _; exact List.pairwise_singleton _ _
      | cons b r =>
          intro h
          rw [chainB, Bool.and_eq_true] at h
          have hp := ih h.2
          refine List.pairwise_cons.2 ⟨?_, hp⟩
          intro x hx ha
          have hb : b = true := by
            rw [ha] at h
            simpa using h.1
          rcases List.mem_cons.1 hx with rfl | hxr
          · exact hb
          · exact (List.pairwise_cons.1 hp).1 x hxr hb

theorem sortedMask_pairwise {n m : Nat} (h : sortedMask n m = true) :
    (maskList n m).Pairwise (fun a b => a = true → b = true) :=
  pairwise_of_chainB _ h

/-- The mask of a zero-one run, lowest bit first. -/
def listMask : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * listMask rest

theorem listMask_lt (bs : List Bool) : listMask bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [listMask]
  | cons b rest ih =>
      have hpow : 2 ^ (b :: rest).length = 2 * 2 ^ rest.length := by
        simp [List.length_cons, Nat.pow_succ]
        omega
      rw [hpow, listMask]
      split <;> omega

theorem listMask_testBit (bs : List Bool) (k : Nat) :
    (listMask bs).testBit k = bs.getD k false := by
  induction bs generalizing k with
  | nil => simp [listMask]
  | cons b rest ih =>
      have hdiv : ((if b then 1 else 0) + 2 * listMask rest) / 2 =
          listMask rest := by
        split <;> omega
      have hmod : ((if b then 1 else 0) + 2 * listMask rest) % 2 =
          (if b then 1 else 0) := by
        split <;> omega
      cases k with
      | zero =>
          rw [listMask, Nat.testBit_zero, hmod]
          cases b <;> simp
      | succ k =>
          rw [listMask, Nat.testBit_succ, hdiv, ih k]
          simp [List.getD]

theorem maskList_listMask (bs : List Bool) :
    maskList bs.length (listMask bs) = bs := by
  refine List.ext_getElem (by simp) ?_
  intro k hk hk'
  rw [maskList_getElem, listMask_testBit, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk']
  rfl

/-! ## The zero-one principle -/

/-- The network sorts every list of `n` keys. -/
def sortsAll (net : List Comparator) (n : Nat) : Prop :=
  ∀ l : List UInt32, l.length = n →
    (applyNetwork (fun a b => decide (a < b)) net l).Pairwise (· ≤ ·)

/-- The zero-one principle.  A network that puts the first `n` bits of
every mask below `2 ^ n` in order sorts every list of `n` keys.

The step function of a key `x` sends every key below `x` to `false` and
every other key to `true`.  It keeps both `select` results, so it carries
a run of the network on keys to the run of the same network on bits. -/
theorem zeroOne (net : List Comparator) (n : Nat)
    (hnet : ∀ c ∈ net, c.1 < n ∧ c.2 < n ∧ c.1 ≠ c.2)
    (h : ∀ m, m < 2 ^ n → sortedMask n (applyMask net m) = true) :
    sortsAll net n := by
  intro l hlen
  by_contra hcontra
  rw [List.pairwise_iff_getElem] at hcontra
  push Not at hcontra
  obtain ⟨i, j, hi, hj, hij, hnle⟩ := hcontra
  set out := applyNetwork (fun a b => decide (a < b)) net l with hout
  obtain ⟨g, hg⟩ : ∃ g : UInt32 → Bool, ∀ k, g k = decide (out[i] ≤ k) :=
    ⟨_, fun _ => rfl⟩
  have hstep : ∀ a b : UInt32, a ≤ b → g a = true → g b = true := by
    intro a b hab ha
    rw [hg] at ha ⊢
    rw [decide_eq_true_eq] at ha ⊢
    exact UInt32.le_trans ha hab
  have hmin : ∀ a b : UInt32,
      g (cmpMin (fun x y => decide (x < y)) a b) =
        cmpMin ltBool (g a) (g b) := by
    intro a b
    rw [cmpMin_bool, minPair_eq]
    by_cases hba : b < a
    · rw [if_pos (by simpa using hba)]
      have key : g b = true → g a = true := hstep b a (UInt32.le_of_lt hba)
      cases hga : g a <;> cases hgb : g b <;> simp_all
    · rw [if_neg (by simpa using hba)]
      have key : g a = true → g b = true := hstep a b (UInt32.not_lt.mp hba)
      cases hga : g a <;> cases hgb : g b <;> simp_all
  have hmax : ∀ a b : UInt32,
      g (cmpMax (fun x y => decide (x < y)) a b) =
        cmpMax ltBool (g a) (g b) := by
    intro a b
    rw [cmpMax_bool, maxPair_eq]
    by_cases hba : b < a
    · rw [if_pos (by simpa using hba)]
      have key : g b = true → g a = true := hstep b a (UInt32.le_of_lt hba)
      cases hga : g a <;> cases hgb : g b <;> simp_all
    · rw [if_neg (by simpa using hba)]
      have key : g a = true → g b = true := hstep a b (UInt32.not_lt.mp hba)
      cases hga : g a <;> cases hgb : g b <;> simp_all
  have hmapeq : out.map g = applyNetwork ltBool net (l.map g) :=
    applyNetwork_map _ ltBool g hmin hmax net l
  have hbl : (l.map g).length = n := by rw [List.length_map, hlen]
  have hml : listMask (l.map g) < 2 ^ n := by
    have hlt := listMask_lt (l.map g)
    rwa [hbl] at hlt
  have hmask : maskList n (listMask (l.map g)) = l.map g := by
    have heq := maskList_listMask (l.map g)
    rwa [hbl] at heq
  have hrun : out.map g = maskList n (applyMask net (listMask (l.map g))) := by
    rw [hmapeq, ← applyMask_eq_bits net n hnet (listMask (l.map g)), hmask]
  have hpw := sortedMask_pairwise (h _ hml)
  rw [← hrun, List.pairwise_iff_getElem] at hpw
  have hi' : i < (out.map g).length := by simpa using hi
  have hj' : j < (out.map g).length := by simpa using hj
  have hchain := hpw i j hi' hj' hij
  rw [List.getElem_map, List.getElem_map] at hchain
  have hgi : g out[i] = true := by
    rw [hg, decide_eq_true_eq]
    exact UInt32.le_refl _
  have hgj : g out[j] = false := by
    rw [hg, decide_eq_false_iff_not]
    exact hnle
  rw [hchain hgi] at hgj
  exact Bool.noConfusion hgj

/-- The entry form.  A network that sorts keys puts the entries of a full
buffer in key order. -/
theorem applyNetwork_pairs_sorted {net : List Comparator} {n : Nat}
    (hsort : sortsAll net n) (ps : List (UInt32 × UInt32))
    (hlen : ps.length = n) :
    SortedByKey (applyNetwork (fun a b => decide (a.1 < b.1)) net ps) := by
  have hkeys := hsort (ps.map Prod.fst) (by rw [List.length_map, hlen])
  rw [← applyNetwork_map_fst net ps, List.pairwise_map] at hkeys
  exact hkeys

/-! ## The two networks of the compiled sort -/

/-- The 25 comparators of the nine-entry block of absolute function 24,
WAT lines 6233 to 7008.  Each pair is the two store offsets of one
comparator, divided by the eight-byte entry stride. -/
def sort9Net : List Comparator :=
  [(0, 3), (1, 7), (2, 5), (4, 8), (0, 7), (2, 4), (3, 8), (5, 6),
   (0, 2), (1, 3), (4, 5), (7, 8), (1, 4), (3, 6), (5, 7), (0, 1),
   (2, 4), (3, 5), (6, 8), (2, 3), (4, 5), (6, 7), (1, 2), (3, 4),
   (5, 6)]

/-- The 45 comparators of the thirteen-entry block of absolute function
24, WAT lines 7016 to 8389. -/
def sort13Net : List Comparator :=
  [(0, 12), (1, 10), (2, 9), (3, 7), (5, 11), (6, 8), (1, 6), (2, 3),
   (4, 11), (7, 9), (8, 10), (0, 4), (1, 2), (3, 6), (7, 8), (9, 10),
   (11, 12), (4, 6), (5, 9), (8, 11), (10, 12), (0, 5), (3, 8), (4, 7),
   (6, 11), (9, 10), (0, 1), (2, 5), (6, 9), (7, 8), (10, 11), (1, 3),
   (2, 4), (5, 6), (9, 10), (1, 2), (3, 4), (5, 7), (6, 8), (2, 3),
   (4, 5), (6, 7), (8, 9), (3, 4), (5, 6)]

theorem sort9Net_range :
    ∀ c ∈ sort9Net, c.1 < 9 ∧ c.2 < 9 ∧ c.1 ≠ c.2 := by decide

theorem sort13Net_range :
    ∀ c ∈ sort13Net, c.1 < 13 ∧ c.2 < 13 ∧ c.1 ≠ c.2 := by decide

/-- The kernel runs the nine-entry network on all 512 masks. -/
theorem sort9Net_masks :
    ∀ m < 2 ^ 9, sortedMask 9 (applyMask sort9Net m) = true := by
  decide +kernel

/-- The nine-entry block of the compiled sort sorts nine keys. -/
theorem sort9Net_sorts : sortsAll sort9Net 9 :=
  zeroOne sort9Net 9 sort9Net_range sort9Net_masks

/-! The thirteen-entry check runs 8192 masks.  It is cut into eight
blocks of 1024 masks so that one kernel run stays small. -/

private theorem sort13_chunk0 : ∀ m < 1024,
    sortedMask 13 (applyMask sort13Net (m + 0 * 1024)) = true := by
  decide +kernel

private theorem sort13_chunk1 : ∀ m < 1024,
    sortedMask 13 (applyMask sort13Net (m + 1 * 1024)) = true := by
  decide +kernel

private theorem sort13_chunk2 : ∀ m < 1024,
    sortedMask 13 (applyMask sort13Net (m + 2 * 1024)) = true := by
  decide +kernel

private theorem sort13_chunk3 : ∀ m < 1024,
    sortedMask 13 (applyMask sort13Net (m + 3 * 1024)) = true := by
  decide +kernel

private theorem sort13_chunk4 : ∀ m < 1024,
    sortedMask 13 (applyMask sort13Net (m + 4 * 1024)) = true := by
  decide +kernel

private theorem sort13_chunk5 : ∀ m < 1024,
    sortedMask 13 (applyMask sort13Net (m + 5 * 1024)) = true := by
  decide +kernel

private theorem sort13_chunk6 : ∀ m < 1024,
    sortedMask 13 (applyMask sort13Net (m + 6 * 1024)) = true := by
  decide +kernel

private theorem sort13_chunk7 : ∀ m < 1024,
    sortedMask 13 (applyMask sort13Net (m + 7 * 1024)) = true := by
  decide +kernel

/-- The kernel runs the thirteen-entry network on all 8192 masks. -/
theorem sort13Net_masks :
    ∀ m < 2 ^ 13, sortedMask 13 (applyMask sort13Net m) = true := by
  intro m hm
  have hbound : m < 8192 := hm
  rcases Nat.lt_or_ge m 1024 with hc0 | hc0
  · have hchunk := sort13_chunk0 m hc0
    rwa [show m + 0 * 1024 = m by omega] at hchunk
  rcases Nat.lt_or_ge m 2048 with hc1 | hc1
  · have hchunk := sort13_chunk1 (m - 1024) (by omega)
    rwa [show m - 1024 + 1 * 1024 = m by omega] at hchunk
  rcases Nat.lt_or_ge m 3072 with hc2 | hc2
  · have hchunk := sort13_chunk2 (m - 2048) (by omega)
    rwa [show m - 2048 + 2 * 1024 = m by omega] at hchunk
  rcases Nat.lt_or_ge m 4096 with hc3 | hc3
  · have hchunk := sort13_chunk3 (m - 3072) (by omega)
    rwa [show m - 3072 + 3 * 1024 = m by omega] at hchunk
  rcases Nat.lt_or_ge m 5120 with hc4 | hc4
  · have hchunk := sort13_chunk4 (m - 4096) (by omega)
    rwa [show m - 4096 + 4 * 1024 = m by omega] at hchunk
  rcases Nat.lt_or_ge m 6144 with hc5 | hc5
  · have hchunk := sort13_chunk5 (m - 5120) (by omega)
    rwa [show m - 5120 + 5 * 1024 = m by omega] at hchunk
  rcases Nat.lt_or_ge m 7168 with hc6 | hc6
  · have hchunk := sort13_chunk6 (m - 6144) (by omega)
    rwa [show m - 6144 + 6 * 1024 = m by omega] at hchunk
  rcases Nat.lt_or_ge m 8192 with hc7 | hc7
  · have hchunk := sort13_chunk7 (m - 7168) (by omega)
    rwa [show m - 7168 + 7 * 1024 = m by omega] at hchunk
  omega

/-- The thirteen-entry block of the compiled sort sorts thirteen keys. -/
theorem sort13Net_sorts : sortsAll sort13Net 13 :=
  zeroOne sort13Net 13 sort13Net_range sort13Net_masks

end Wasm.RustStd.HashMap.Table
