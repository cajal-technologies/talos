import Project.RustHashMap.SortPures

/-!
# The heapsort model of the sort group

Absolute `func 25` of `programs/rust/build/rust_hash_map/program.wat` is
the heapsort that `ipnsort` falls back to.  `SortModels.heapsortModel` is
its pure model.  A body proof of absolute `func 25` reads two facts off
that model: the output holds the same entries as the input, and the
output is in key order.  This module proves those two facts.

Nothing here mentions Wasm, and no proof uses a weakest-precondition
rule.

There are five groups.

* The child that the sift picks.  `greaterChild_cases` splits
  `SortModels.greaterChild` into the childless case and the two child
  cases, and the lemmas below it give the bounds that every later proof
  needs.
* The sift moves the entries only.  `siftDownAux_perm` and
  `heapsortModel_perm` carry `List.Perm` from the model to the caller.
* The heap invariant.  `IsHeapFrom` is the heap property of the parents
  at or above an index, and `SiftInvFrom` is the invariant that one sift
  keeps.  `siftDownAux_heapFrom` is the induction that repairs the heap,
  and `siftDown_heap` is the case that the sort phase uses.
* The sort phase.  `SortInv` is the invariant of the second half of the
  merged loop: the first `i` entries are a heap, they are below every
  later entry, and the entries from `i` up are in key order.
* The assembly.  `heapsortUpto` is the fold of the merged loop down to a
  counter value.  The compiled loop counts `local 3` down, so
  `heapsortUpto` is the loop invariant of the body proof.
  `heapsortUpto_inv` gives the heap invariant above `len` and the sort
  invariant below it, and `heapsortModel_eq_sortByKey` is the result.

## The shape of the merged loop

The counter `i` starts at `len + len / 2` and counts down to `0`.  Above
`len` the loop builds the heap: step `i` sifts the node `i - len`, so
the nodes come in the order `len / 2 - 1` down to `0`.  Below `len` the
loop sorts: step `i` exchanges the root with entry `i` and repairs the
prefix of length `i`.
-/

namespace Project.RustHashMap.HeapModel

open Wasm.RustStd.HashMap
open Project.RustHashMap.SortModels
open Project.RustHashMap.SortPures

/-! ## The child that the sift picks -/

/-- The three cases of `greaterChild`.  Either `node` has no child below
`len`, or the answer is one of the two children and is below `len`. -/
theorem greaterChild_cases (ps : List (UInt32 × UInt32)) (len node : Nat) :
    greaterChild ps len node = node ∧ len ≤ 2 * node + 1 ∨
      (greaterChild ps len node = 2 * node + 1 ∨
          greaterChild ps len node = 2 * node + 2) ∧
        2 * node + 1 < len ∧ greaterChild ps len node < len := by
  rw [greaterChild]
  split_ifs with h1 h2
  · exact Or.inl ⟨rfl, h1⟩
  · have h21 := h2.1
    exact Or.inr ⟨Or.inr rfl, by omega, h21⟩
  · exact Or.inr ⟨Or.inl rfl, by omega, by omega⟩

/-- A child that is not `node` is below `len`. -/
theorem greaterChild_lt {ps : List (UInt32 × UInt32)} {len node : Nat}
    (h : greaterChild ps len node ≠ node) :
    greaterChild ps len node < len := by
  rcases greaterChild_cases ps len node with ⟨he, _⟩ | ⟨_, _, hlt⟩
  · exact absurd he h
  · exact hlt

/-- A child that is not `node` is one of the two children of `node`, and
then the first child is below `len`. -/
theorem greaterChild_ne_imp {ps : List (UInt32 × UInt32)} {len node : Nat}
    (h : greaterChild ps len node ≠ node) :
    2 * node + 1 < len ∧
      (greaterChild ps len node = 2 * node + 1 ∨
        greaterChild ps len node = 2 * node + 2) := by
  rcases greaterChild_cases ps len node with ⟨he, _⟩ | ⟨hor, hlt, _⟩
  · exact absurd he h
  · exact ⟨hlt, hor⟩

/-- A child that is not `node` is above `node`.  The sift therefore
moves down, and the fuel runs out. -/
theorem greaterChild_gt {ps : List (UInt32 × UInt32)} {len node : Nat}
    (h : greaterChild ps len node ≠ node) :
    node < greaterChild ps len node := by
  obtain ⟨_, hor⟩ := greaterChild_ne_imp h
  rcases hor with he | he <;> omega

/-- The parent of the child is `node`. -/
theorem greaterChild_parent {ps : List (UInt32 × UInt32)} {len node : Nat}
    (h : greaterChild ps len node ≠ node) :
    (greaterChild ps len node - 1) / 2 = node := by
  obtain ⟨_, hor⟩ := greaterChild_ne_imp h
  rcases hor with he | he <;> rw [he] <;> omega

/-- `node` answers itself only when it has no child below `len`. -/
theorem greaterChild_eq_imp {ps : List (UInt32 × UInt32)} {len node : Nat}
    (h : greaterChild ps len node = node) : len ≤ 2 * node + 1 := by
  rcases greaterChild_cases ps len node with ⟨_, hle⟩ | ⟨hor, _, _⟩
  · exact hle
  · rcases hor with he | he <;> omega

/-- The child that the sift picks has the greatest key of the children
of `node` that are below `len`. -/
theorem greaterChild_max (ps : List (UInt32 × UInt32)) (len node : Nat)
    {c : Nat} (hc : 0 < c) (hcl : c < len) (hp : (c - 1) / 2 = node) :
    keyAt ps c ≤ keyAt ps (greaterChild ps len node) := by
  have hcc : c = 2 * node + 1 ∨ c = 2 * node + 2 := by omega
  rw [greaterChild]
  rcases hcc with rfl | rfl
  · split_ifs with h1 h2
    · exact absurd hcl (by omega)
    · exact UInt32.le_of_lt h2.2
    · exact UInt32.le_refl _
  · split_ifs with h1 h2
    · exact absurd hcl (by omega)
    · exact UInt32.le_refl _
    · exact UInt32.not_lt.1 (fun hk => h2 ⟨hcl, hk⟩)

/-! ## The sift moves the entries only -/

private theorem siftDownAux_perm_aux (len : Nat) :
    ∀ (fuel : Nat) (ps : List (UInt32 × UInt32)) (node : Nat),
      len ≤ ps.length → (siftDownAux fuel ps len node).Perm ps := by
  intro fuel
  induction fuel with
  | zero =>
    intro ps _ _
    rw [siftDownAux]
  | succ fuel ih =>
    intro ps node hlen
    rw [siftDownAux]
    split
    · exact List.Perm.refl _
    · split
      · rename_i hne _
        have hgl : greaterChild ps len node < len := greaterChild_lt hne
        have hnl : node < len := by
          have := (greaterChild_ne_imp hne).1
          omega
        refine List.Perm.trans (ih _ _ ?_) ?_
        · rw [Table.swapAt_length]
          exact hlen
        · exact Table.swapAt_perm ps (by omega) (by omega)
      · exact List.Perm.refl _

/-- A sift-down only moves the entries. -/
theorem siftDownAux_perm (fuel : Nat) (ps : List (UInt32 × UInt32))
    (len node : Nat) (hlen : len ≤ ps.length) :
    (siftDownAux fuel ps len node).Perm ps :=
  siftDownAux_perm_aux len fuel ps node hlen

/-- The sift-down of one node only moves the entries. -/
theorem siftDown_perm (ps : List (UInt32 × UInt32)) (len node : Nat)
    (hlen : len ≤ ps.length) : (siftDown ps len node).Perm ps :=
  siftDownAux_perm len ps len node hlen

/-- One step of the merged loop only moves the entries. -/
theorem heapsortStep_perm (ps : List (UInt32 × UInt32)) (len i : Nat)
    (hlen : len ≤ ps.length) : (heapsortStep ps len i).Perm ps := by
  rw [heapsortStep]
  split
  · exact siftDown_perm ps len (i - len) hlen
  · rename_i hgt
    refine List.Perm.trans (siftDown_perm (Table.swapAt ps 0 i) i 0 ?_) ?_
    · rw [Table.swapAt_length]
      omega
    · exact Table.swapAt_perm ps (by omega) (by omega)

/-! ## The fuel of a sift -/

/-- A sift of a node with no child below `len` changes nothing. -/
theorem siftDownAux_eq_self (fuel : Nat) (ps : List (UInt32 × UInt32))
    (len node : Nat) (h : greaterChild ps len node = node) :
    siftDownAux fuel ps len node = ps := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [siftDownAux, if_pos h]

private theorem siftDownAux_fuel_aux (len : Nat) :
    ∀ (fuel : Nat) (ps : List (UInt32 × UInt32)) (node extra : Nat),
      len ≤ node + fuel →
      siftDownAux (fuel + extra) ps len node
        = siftDownAux fuel ps len node := by
  intro fuel
  induction fuel with
  | zero =>
    intro ps node extra hfuel
    have hgc : greaterChild ps len node = node := by
      by_contra hne
      have := (greaterChild_ne_imp hne).1
      omega
    rw [siftDownAux_eq_self (0 + extra) ps len node hgc,
      siftDownAux_eq_self 0 ps len node hgc]
  | succ fuel ih =>
    intro ps node extra hfuel
    have hstep : fuel + 1 + extra = fuel + extra + 1 := by omega
    rw [hstep, siftDownAux, siftDownAux]
    split
    · rfl
    · split
      · rename_i hne _
        have hgg : node < greaterChild ps len node := greaterChild_gt hne
        exact ih _ _ _ (by omega)
      · rfl

/-- Extra fuel changes nothing, as soon as the fuel reaches `len`.  Each
step at least doubles `node + 1`, so `len - node` steps are enough. -/
theorem siftDownAux_fuel (ps : List (UInt32 × UInt32)) (len node : Nat)
    {fuel fuel' : Nat} (hfuel : len ≤ node + fuel) (hle : fuel ≤ fuel') :
    siftDownAux fuel' ps len node = siftDownAux fuel ps len node := by
  have he : fuel' = fuel + (fuel' - fuel) := by omega
  rw [he]
  exact siftDownAux_fuel_aux len fuel ps node (fuel' - fuel) hfuel

/-! ## What a sift does not touch -/

private theorem siftDownAux_getElem?_aux (len : Nat) :
    ∀ (fuel : Nat) (ps : List (UInt32 × UInt32)) (node : Nat) (m : Nat),
      len ≤ m → (siftDownAux fuel ps len node)[m]? = ps[m]? := by
  intro fuel
  induction fuel with
  | zero =>
    intro ps _ m _
    rw [siftDownAux]
  | succ fuel ih =>
    intro ps node m hm
    rw [siftDownAux]
    split
    · rfl
    · split
      · rename_i hne _
        have hgl : greaterChild ps len node < len := greaterChild_lt hne
        have hnl : node < len := by
          have := (greaterChild_ne_imp hne).1
          omega
        rw [ih _ _ m hm]
        exact Table.swapAt_getElem?_other ps (by omega) (by omega)
      · rfl

/-- A sift-down keeps every entry from `len` up. -/
theorem siftDownAux_getElem?_ge (fuel : Nat) (ps : List (UInt32 × UInt32))
    (len node : Nat) (m : Nat) (hm : len ≤ m) :
    (siftDownAux fuel ps len node)[m]? = ps[m]? :=
  siftDownAux_getElem?_aux len fuel ps node m hm

theorem siftDown_getElem?_ge (ps : List (UInt32 × UInt32))
    (len node : Nat) (m : Nat) (hm : len ≤ m) :
    (siftDown ps len node)[m]? = ps[m]? :=
  siftDownAux_getElem?_ge len ps len node m hm

private theorem siftDownAux_key_le_aux (len : Nat) (b : UInt32) :
    ∀ (fuel : Nat) (ps : List (UInt32 × UInt32)) (node : Nat),
      len ≤ ps.length → (∀ m, m < len → keyAt ps m ≤ b) →
      ∀ m, m < len → keyAt (siftDownAux fuel ps len node) m ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
    intro ps _ _ h m hm
    rw [siftDownAux]
    exact h m hm
  | succ fuel ih =>
    intro ps node hlen h m hm
    rw [siftDownAux]
    split
    · exact h m hm
    · split
      · rename_i hne _
        have hgl : greaterChild ps len node < len := greaterChild_lt hne
        have hnl : node < len := by
          have := (greaterChild_ne_imp hne).1
          omega
        have hnp : node < ps.length := by omega
        have hgp : greaterChild ps len node < ps.length := by omega
        refine ih _ _ ?_ ?_ m hm
        · rw [Table.swapAt_length]
          exact hlen
        · intro j hj
          by_cases hjn : j = node
          · rw [hjn, keyAt_swapAt_left ps hnp hgp]
            exact h _ hgl
          · by_cases hjg : j = greaterChild ps len node
            · rw [hjg, keyAt_swapAt_right ps hnp hgp]
              exact h _ hnl
            · rw [keyAt_swapAt_other ps hjn hjg]
              exact h j hj
      · exact h m hm

/-- A sift-down never lifts a key above a bound that the whole prefix
already keeps. -/
theorem siftDownAux_key_le (fuel : Nat) (ps : List (UInt32 × UInt32))
    (len node : Nat) (b : UInt32) (hlen : len ≤ ps.length)
    (h : ∀ m, m < len → keyAt ps m ≤ b) (m : Nat) (hm : m < len) :
    keyAt (siftDownAux fuel ps len node) m ≤ b :=
  siftDownAux_key_le_aux len b fuel ps node hlen h m hm

theorem siftDown_key_le (ps : List (UInt32 × UInt32)) (len node : Nat)
    (b : UInt32) (hlen : len ≤ ps.length)
    (h : ∀ m, m < len → keyAt ps m ≤ b) (m : Nat) (hm : m < len) :
    keyAt (siftDown ps len node) m ≤ b :=
  siftDownAux_key_le len ps len node b hlen h m hm

/-! ## The heap invariant -/

/-- The heap property of the parents at or above `k`.  `IsHeapFrom ps len
0` is `IsHeap ps len`. -/
def IsHeapFrom (ps : List (UInt32 × UInt32)) (len k : Nat) : Prop :=
  ∀ c, 0 < c → c < len → k ≤ (c - 1) / 2 →
    keyAt ps c ≤ keyAt ps ((c - 1) / 2)

theorem isHeap_of_isHeapFrom_zero {ps : List (UInt32 × UInt32)}
    {len : Nat} (h : IsHeapFrom ps len 0) : IsHeap ps len :=
  fun c hc hcl => h c hc hcl (Nat.zero_le _)

theorem isHeapFrom_zero_of_isHeap {ps : List (UInt32 × UInt32)}
    {len : Nat} (h : IsHeap ps len) : IsHeapFrom ps len 0 :=
  fun c hc hcl _ => h c hc hcl

/-- The invariant that one sift keeps.  Every parent at or above `k`
other than `node` dominates its children, and, when `node` is above `k`,
the parent of `node` dominates the children of `node`.  The second part
is what makes the exchange of `node` with its child safe. -/
def SiftInvFrom (ps : List (UInt32 × UInt32)) (len k node : Nat) : Prop :=
  (∀ c, 0 < c → c < len → k ≤ (c - 1) / 2 → (c - 1) / 2 ≠ node →
      keyAt ps c ≤ keyAt ps ((c - 1) / 2)) ∧
    (k < node → ∀ c, 0 < c → c < len → (c - 1) / 2 = node →
      keyAt ps c ≤ keyAt ps ((node - 1) / 2))

/-- The invariant of a sift that repairs the whole heap. -/
def SiftInv (ps : List (UInt32 × UInt32)) (len node : Nat) : Prop :=
  SiftInvFrom ps len 0 node

private theorem siftDownAux_heapFrom_aux (len k : Nat) :
    ∀ (fuel : Nat) (ps : List (UInt32 × UInt32)) (node : Nat),
      len ≤ node + fuel → len ≤ ps.length → k ≤ node →
      (k < node → k ≤ (node - 1) / 2) → SiftInvFrom ps len k node →
      IsHeapFrom (siftDownAux fuel ps len node) len k := by
  intro fuel
  induction fuel with
  | zero =>
    intro ps node hfuel _ _ _ hinv
    rw [siftDownAux]
    intro c hc hcl hkp
    exact hinv.1 c hc hcl hkp (by omega)
  | succ fuel ih =>
    intro ps node hfuel hlen hk hpar hinv
    rw [siftDownAux]
    split
    · rename_i heq
      have hle := greaterChild_eq_imp heq
      intro c hc hcl hkp
      exact hinv.1 c hc hcl hkp (by omega)
    · split
      · rename_i hne hlt
        have hgl : greaterChild ps len node < len := greaterChild_lt hne
        have hgg : node < greaterChild ps len node := greaterChild_gt hne
        have hgp : (greaterChild ps len node - 1) / 2 = node :=
          greaterChild_parent hne
        have hnl : node < len := by
          have := (greaterChild_ne_imp hne).1
          omega
        have hnp : node < ps.length := by omega
        have hcp : greaterChild ps len node < ps.length := by omega
        have hg0 : 0 < greaterChild ps len node := by omega
        refine ih _ _ (by omega) ?_ (by omega) ?_ ⟨?_, ?_⟩
        · rw [Table.swapAt_length]
          exact hlen
        · intro _
          rw [hgp]
          exact hk
        · intro c hc hcl hkp hpne
          by_cases hpn : (c - 1) / 2 = node
          · rw [hpn, keyAt_swapAt_left ps hnp hcp]
            by_cases hcg : c = greaterChild ps len node
            · rw [hcg, keyAt_swapAt_right ps hnp hcp]
              exact UInt32.le_of_lt hlt
            · rw [keyAt_swapAt_other ps (by omega) hcg]
              exact greaterChild_max ps len node hc hcl hpn
          · rw [keyAt_swapAt_other ps hpn hpne]
            by_cases hcn : c = node
            · rw [hcn, keyAt_swapAt_left ps hnp hcp]
              have hkn : k < node := by omega
              exact hinv.2 hkn _ hg0 hgl hgp
            · by_cases hcg : c = greaterChild ps len node
              · exact absurd (by rw [hcg]; exact hgp) hpn
              · rw [keyAt_swapAt_other ps hcn hcg]
                exact hinv.1 c hc hcl hkp hpn
        · intro _ c hc hcl hpc
          have hcg : 2 * greaterChild ps len node + 1 ≤ c := by omega
          rw [hgp, keyAt_swapAt_left ps hnp hcp,
            keyAt_swapAt_other ps (by omega) (by omega)]
          have hkey := hinv.1 c hc hcl (by omega) (by omega)
          rw [hpc] at hkey
          exact hkey
      · rename_i hne hnlt
        intro c hc hcl hkp
        by_cases hpn : (c - 1) / 2 = node
        · rw [hpn]
          refine UInt32.le_trans (greaterChild_max ps len node hc hcl hpn) ?_
          exact UInt32.not_lt.1 hnlt
        · exact hinv.1 c hc hcl hkp hpn

/-- The sift repairs the heap from `k` up.  The proof is the induction
on the fuel: one step exchanges `node` with its greater child, and the
invariant moves down with it. -/
theorem siftDownAux_heapFrom (fuel : Nat) (ps : List (UInt32 × UInt32))
    (len k node : Nat) (hfuel : len ≤ node + fuel) (hlen : len ≤ ps.length)
    (hk : k ≤ node) (hpar : k < node → k ≤ (node - 1) / 2)
    (hinv : SiftInvFrom ps len k node) :
    IsHeapFrom (siftDownAux fuel ps len node) len k :=
  siftDownAux_heapFrom_aux len k fuel ps node hfuel hlen hk hpar hinv

/-- The build step.  A sift of `k` turns the heap above `k + 1` into the
heap above `k`. -/
theorem siftDown_heapFrom (ps : List (UInt32 × UInt32)) (len k : Nat)
    (hlen : len ≤ ps.length) (h : IsHeapFrom ps len (k + 1)) :
    IsHeapFrom (siftDown ps len k) len k := by
  refine siftDownAux_heapFrom len ps len k k (by omega) hlen
    (Nat.le_refl k) (by omega) ⟨?_, ?_⟩
  · intro c hc hcl hkp hpne
    exact h c hc hcl (by omega)
  · intro hkk
    exact absurd hkk (Nat.lt_irrefl k)

/-- The sift of `node` repairs the whole heap. -/
theorem siftDownAux_heap (fuel : Nat) (ps : List (UInt32 × UInt32))
    (len node : Nat) (hfuel : len ≤ node + fuel) (hlen : len ≤ ps.length)
    (hinv : SiftInv ps len node) :
    IsHeap (siftDownAux fuel ps len node) len :=
  isHeap_of_isHeapFrom_zero
    (siftDownAux_heapFrom fuel ps len 0 node hfuel hlen (Nat.zero_le _)
      (fun _ => Nat.zero_le _) hinv)

/-- The sort step.  A sift of the root repairs a prefix whose only fault
is at the root. -/
theorem siftDown_heap (ps : List (UInt32 × UInt32)) (len : Nat)
    (hlen : len ≤ ps.length)
    (h : ∀ c, 0 < c → c < len → 0 < (c - 1) / 2 →
      keyAt ps c ≤ keyAt ps ((c - 1) / 2)) :
    IsHeap (siftDown ps len 0) len :=
  isHeap_of_isHeapFrom_zero (siftDown_heapFrom ps len 0 hlen h)

/-- The heap above `len / 2` holds for nothing, because no parent of an
entry below `len` reaches `len / 2`.  This is where the build starts. -/
theorem isHeapFrom_half (ps : List (UInt32 × UInt32)) (len : Nat) :
    IsHeapFrom ps len (len / 2) := by
  intro c hc hcl hkp
  exact absurd hkp (by omega)

/-- The root of a heap holds the greatest key. -/
theorem heap_root_max {ps : List (UInt32 × UInt32)} {n : Nat}
    (h : IsHeap ps n) : ∀ j, j < n → keyAt ps j ≤ keyAt ps 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact UInt32.le_refl _
    · exact UInt32.le_trans (h j hj0 hj)
        (ih ((j - 1) / 2) (by omega) (by omega))

/-! ## The sort phase -/

/-- The invariant of the sort phase, at the counter value `i`.  The
first `i` entries are a heap, every one of them is below every entry
from `i` up, and the entries from `i` up are in key order. -/
def SortInv (ps : List (UInt32 × UInt32)) (len i : Nat) : Prop :=
  IsHeap ps i ∧
    (∀ j, j < i → ∀ m, i ≤ m → m < len → keyAt ps j ≤ keyAt ps m) ∧
    Table.SortedByKey (ps.drop i)

/-- The sort phase starts with the whole slice as the heap. -/
theorem sortInv_top (ps : List (UInt32 × UInt32)) (len i : Nat)
    (hlen : ps.length ≤ i) (hi : len ≤ i) (h : IsHeap ps i) :
    SortInv ps len i := by
  refine ⟨h, ?_, ?_⟩
  · intro _ _ m hm hml
    exact absurd hml (by omega)
  · rw [List.drop_eq_nil_of_le hlen]
    exact Table.SortedByKey.nil

/-- An entry of a drop is an entry of the list, at an index that the
drop counts. -/
private theorem mem_drop_index {α : Type} {l : List α} {k : Nat} {q : α}
    (h : q ∈ l.drop k) : ∃ m, k ≤ m ∧ m < l.length ∧ l[m]? = some q := by
  rw [List.mem_iff_getElem] at h
  obtain ⟨j, hj, hjq⟩ := h
  refine ⟨k + j, by omega, ?_, ?_⟩
  · rw [List.length_drop] at hj
    omega
  · rw [← List.getElem?_drop, List.getElem?_eq_getElem hj, hjq]

/-- One step of the sort phase.  The exchange moves the greatest key of
the prefix to entry `i`, and the sift repairs the shorter prefix. -/
theorem sort_step {ps : List (UInt32 × UInt32)} {len i : Nat}
    (hlen : ps.length = len) (hi : i < len)
    (hinv : SortInv ps len (i + 1)) :
    SortInv (siftDown (Table.swapAt ps 0 i) i 0) len i := by
  obtain ⟨hheap, hmid, hsort⟩ := hinv
  have h0 : 0 < ps.length := by omega
  have hil : i < ps.length := by omega
  have hswap : (Table.swapAt ps 0 i).length = len := by
    rw [Table.swapAt_length, hlen]
  have hqlen : (siftDown (Table.swapAt ps 0 i) i 0).length = len := by
    rw [siftDown_length, Table.swapAt_length, hlen]
  have hroot : ∀ j, j < i + 1 → keyAt ps j ≤ keyAt ps 0 :=
    heap_root_max hheap
  have hbound : ∀ m, m < i →
      keyAt (Table.swapAt ps 0 i) m ≤ keyAt ps 0 := by
    intro m hm
    by_cases hm0 : m = 0
    · rw [hm0, keyAt_swapAt_left ps h0 hil]
      exact hroot i (by omega)
    · rw [keyAt_swapAt_other ps hm0 (by omega)]
      exact hroot m (by omega)
  have hqbound : ∀ m, m < i →
      keyAt (siftDown (Table.swapAt ps 0 i) i 0) m ≤ keyAt ps 0 :=
    fun m hm =>
      siftDown_key_le (Table.swapAt ps 0 i) i 0 (keyAt ps 0) (by omega)
        hbound m hm
  have hkey : ∀ m, i ≤ m →
      keyAt (siftDown (Table.swapAt ps 0 i) i 0) m
        = keyAt (Table.swapAt ps 0 i) m := by
    intro m hm
    rw [keyAt_eq_getElem?, keyAt_eq_getElem?,
      siftDown_getElem?_ge (Table.swapAt ps 0 i) i 0 m hm]
  have hdrop : (siftDown (Table.swapAt ps 0 i) i 0).drop (i + 1)
      = ps.drop (i + 1) := by
    refine List.ext_getElem? fun j => ?_
    rw [List.getElem?_drop, List.getElem?_drop,
      siftDown_getElem?_ge (Table.swapAt ps 0 i) i 0 (i + 1 + j)
        (by omega)]
    exact Table.swapAt_getElem?_other ps (by omega) (by omega)
  have hdropi : (siftDown (Table.swapAt ps 0 i) i 0).drop i
      = (ps[0]'h0) :: ps.drop (i + 1) := by
    rw [← List.getElem_cons_drop (show i < _ from by omega), hdrop]
    congr 1
    have hget := siftDown_getElem?_ge (Table.swapAt ps 0 i) i 0 i
      (Nat.le_refl i)
    rw [Table.swapAt_getElem?_right ps h0 hil,
      List.getElem?_eq_getElem (show i < _ from by omega),
      List.getElem?_eq_getElem h0] at hget
    exact Option.some.inj hget
  refine ⟨?_, ?_, ?_⟩
  · refine siftDown_heap (Table.swapAt ps 0 i) i (by omega) ?_
    intro c hc hcl hp
    have hc0 : c ≠ 0 := by omega
    have hci : c ≠ i := by omega
    have hp0 : (c - 1) / 2 ≠ 0 := by omega
    have hpi : (c - 1) / 2 ≠ i := by omega
    rw [keyAt_swapAt_other ps hc0 hci, keyAt_swapAt_other ps hp0 hpi]
    exact hheap c hc (by omega)
  · intro j hj m hm hml
    have hjb := hqbound j hj
    rcases Nat.eq_or_lt_of_le hm with he | hlt
    · rw [← he, hkey i (Nat.le_refl i), keyAt_swapAt_right ps h0 hil]
      exact hjb
    · have hm0 : m ≠ 0 := by omega
      have hmi : m ≠ i := by omega
      rw [hkey m hm, keyAt_swapAt_other ps hm0 hmi]
      exact UInt32.le_trans hjb (hmid 0 (by omega) m (by omega) hml)
  · rw [hdropi, Table.SortedByKey.cons_iff]
    refine ⟨?_, hsort⟩
    intro q hq
    obtain ⟨m, hkm, hmp, hmq⟩ := mem_drop_index hq
    have hq1 : keyAt ps m = q.1 := by
      rw [keyAt_eq_getElem?, hmq]
      rfl
    have h01 : keyAt ps 0 = (ps[0]'h0).1 := keyAt_eq_getElem ps h0
    rw [← h01, ← hq1]
    exact hmid 0 (by omega) m hkm (by omega)

/-! ## The merged loop -/

/-- The fold of the merged loop from the top counter value down to `i`.
The compiled body counts `local 3` down from `len + len / 2`, so this is
the loop invariant of the body proof. -/
def heapsortUpto (ps : List (UInt32 × UInt32)) (len i : Nat) :
    List (UInt32 × UInt32) :=
  (((List.range (len + len / 2)).drop i).reverse).foldl
    (fun acc j => heapsortStep acc len j) ps

/-- At the top counter value the loop has done nothing. -/
theorem heapsortUpto_top (ps : List (UInt32 × UInt32)) (len : Nat) :
    heapsortUpto ps len (len + len / 2) = ps := by
  rw [heapsortUpto, List.drop_eq_nil_of_le (by rw [List.length_range])]
  rfl

/-- One step of the loop. -/
theorem heapsortUpto_succ (ps : List (UInt32 × UInt32)) (len i : Nat)
    (hi : i < len + len / 2) :
    heapsortUpto ps len i
      = heapsortStep (heapsortUpto ps len (i + 1)) len i := by
  rw [heapsortUpto, heapsortUpto,
    ← List.getElem_cons_drop
      (show i < (List.range (len + len / 2)).length from by
        rw [List.length_range]; exact hi),
    List.getElem_range, List.reverse_cons, List.foldl_append]
  rfl

/-- At the counter value `0` the loop has made the whole model. -/
theorem heapsortUpto_zero (ps : List (UInt32 × UInt32)) :
    heapsortUpto ps ps.length 0 = heapsortModel ps := by
  rw [heapsortUpto, heapsortModel, List.drop_zero]

theorem heapsortUpto_length (ps : List (UInt32 × UInt32)) (len i : Nat) :
    (heapsortUpto ps len i).length = ps.length := by
  rw [heapsortUpto]
  generalize (((List.range (len + len / 2)).drop i).reverse) = steps
  induction steps generalizing ps with
  | nil => rfl
  | cons j rest ih => rw [List.foldl_cons, ih, heapsortStep_length]

theorem heapsortUpto_perm (ps : List (UInt32 × UInt32)) (len i : Nat)
    (hlen : len ≤ ps.length) : (heapsortUpto ps len i).Perm ps := by
  rw [heapsortUpto]
  generalize (((List.range (len + len / 2)).drop i).reverse) = steps
  induction steps generalizing ps with
  | nil => exact List.Perm.refl _
  | cons j rest ih =>
    rw [List.foldl_cons]
    refine List.Perm.trans (ih _ ?_) (heapsortStep_perm ps len j hlen)
    rw [heapsortStep_length]
    exact hlen

/-- The model only moves the entries. -/
theorem heapsortModel_perm (ps : List (UInt32 × UInt32)) :
    (heapsortModel ps).Perm ps := by
  rw [← heapsortUpto_zero]
  exact heapsortUpto_perm ps ps.length 0 (Nat.le_refl _)

private theorem heapsortUpto_inv_aux (ps : List (UInt32 × UInt32))
    (len : Nat) (hlen : ps.length = len) :
    ∀ d i, i + d = len + len / 2 →
      (len ≤ i → IsHeapFrom (heapsortUpto ps len i) len (i - len)) ∧
      (i < len → SortInv (heapsortUpto ps len i) len i) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hie : i = len + len / 2 := by omega
    subst hie
    rw [heapsortUpto_top]
    refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
    rw [show len + len / 2 - len = len / 2 from by omega]
    exact isHeapFrom_half ps len
  | succ d ih =>
    intro i hi
    have hiN : i < len + len / 2 := by omega
    have hih := ih (i + 1) (by omega)
    have hqlen : (heapsortUpto ps len (i + 1)).length = len := by
      rw [heapsortUpto_length, hlen]
    rw [heapsortUpto_succ ps len i hiN]
    refine ⟨?_, ?_⟩
    · intro hli
      rw [heapsortStep, if_pos hli]
      have h1 := hih.1 (by omega)
      rw [show i + 1 - len = (i - len) + 1 from by omega] at h1
      exact siftDown_heapFrom _ len (i - len) (by omega) h1
    · intro hli
      rw [heapsortStep, if_neg (by omega)]
      refine sort_step hqlen hli ?_
      rcases Nat.lt_or_ge (i + 1) len with hlt | hge
      · exact hih.2 hlt
      · have h1 := hih.1 hge
        refine sortInv_top _ len (i + 1) (by omega) (by omega) ?_
        intro c hc hcl
        exact h1 c hc (by omega) (by omega)

/-- The invariant of the merged loop at every counter value.  Above
`len` the loop has built the heap down to the node `i - len`; below
`len` it has sorted the entries from `i` up. -/
theorem heapsortUpto_inv (ps : List (UInt32 × UInt32)) (len i : Nat)
    (hlen : ps.length = len) (hi : i ≤ len + len / 2) :
    (len ≤ i → IsHeapFrom (heapsortUpto ps len i) len (i - len)) ∧
    (i < len → SortInv (heapsortUpto ps len i) len i) :=
  heapsortUpto_inv_aux ps len hlen (len + len / 2 - i) i (by omega)

/-- The model puts the entries in key order. -/
theorem heapsortModel_sorted (ps : List (UInt32 × UInt32)) :
    Table.SortedByKey (heapsortModel ps) := by
  rcases Nat.eq_zero_or_pos ps.length with h0 | h0
  · obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero h0
    exact Table.SortedByKey.nil
  · have h := (heapsortUpto_inv ps ps.length 0 rfl (by omega)).2 h0
    rw [heapsortUpto_zero] at h
    have hs := h.2.2
    rwa [List.drop_zero] at hs

/-- The model of absolute `func 25` is the model sort, as soon as the
keys are distinct.  This is the fact that the body proof reports. -/
theorem heapsortModel_eq_sortByKey {ps : List (UInt32 × UInt32)}
    (hn : NodupKeys ps) : heapsortModel ps = sortByKey ps :=
  Table.eq_sortByKey_of_perm_of_sorted hn (heapsortModel_perm ps)
    (heapsortModel_sorted ps)

end Project.RustHashMap.HeapModel
