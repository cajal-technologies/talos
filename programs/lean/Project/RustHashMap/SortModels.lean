import CodeLib.RustStd.HashMap.SortingNetwork
import CodeLib.RustStd.HashMap.PairSlice
import CodeLib.RustStd.HashMap.SortedByKey

/-!
# The pure models of the compiled pair sort

`collect_entries` sorts its entry list by key.  The compiled form of that
call is `ipnsort`, absolute `func 14` of
`programs/rust/build/rust_hash_map/program.wat`.  `ipnsort` picks one of
three kernels by length:

* fewer than 2 entries: nothing to do;
* fewer than 21 entries: `insertion_sort_shift_left`, absolute `func 15`,
  with the offset 1;
* 21 entries or more: `quicksort`, absolute `func 24`, which falls back to
  `heapsort`, absolute `func 25`, when its recursion limit runs out.

This module gives the pure model of each kernel.  A model is a function on
`List (UInt32 x UInt32)`, the same entry list that
`Wasm.RustStd.HashMap.Table.PairSlice` owns.  A body proof shows that the
compiled kernel computes its model, and then reads the two facts it needs
off the model: the output is a permutation of the input, and the output is
in key order.  `Table.eq_sortByKey_of_perm_of_sorted` turns that pair into
the `sortByKey` that the specification names.

Nothing here mentions Wasm.  The contracts are in
`Project.RustHashMap.SortContracts`.

## What is proved and what is not

The insertion-sort model carries both facts.  The heapsort model and the
bidirectional merge carry their definitions only; their two facts belong
to the body proofs that need them, and are not proved here.
-/

namespace Project.RustHashMap.SortModels

open Wasm.RustStd.HashMap

/-! ## The key of an entry -/

/-- The key of entry `i`.  Out of range the model reads the key `0`.
Every consumer keeps `i` in range. -/
def keyAt (ps : List (UInt32 × UInt32)) (i : Nat) : UInt32 :=
  (ps.getD i (0, 0)).1

/-! ## `insertion_sort_shift_left`, absolute `func 15` -/

/-- Put one entry into a list that is already in key order.  The entry
goes after every entry with the same key, which is what the compiled loop
does: it stops as soon as the entry below it is not greater. -/
def insertTail (p : UInt32 × UInt32) :
    List (UInt32 × UInt32) → List (UInt32 × UInt32)
  | [] => [p]
  | q :: qs => if p.1 < q.1 then p :: q :: qs else q :: insertTail p qs

/-- The model of absolute `func 15`.  The first `offset` entries are
already in key order, and the loop puts each later entry into place. -/
def insertionShiftLeft (pairs : List (UInt32 × UInt32)) (offset : Nat) :
    List (UInt32 × UInt32) :=
  (pairs.drop offset).foldl (fun acc p => insertTail p acc)
    (pairs.take offset)

/-- One insertion only moves the entries. -/
theorem insertTail_perm (p : UInt32 × UInt32) (l : List (UInt32 × UInt32)) :
    (insertTail p l).Perm (p :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons q qs ih =>
    by_cases hlt : p.1 < q.1
    · simp only [insertTail, hlt, if_true]
      exact List.Perm.refl _
    · simp only [insertTail, hlt, if_false]
      exact (ih.cons q).trans (List.Perm.swap p q qs)

/-- One insertion keeps the key order. -/
theorem insertTail_sorted (p : UInt32 × UInt32)
    {l : List (UInt32 × UInt32)} (hs : Table.SortedByKey l) :
    Table.SortedByKey (insertTail p l) := by
  induction l with
  | nil => exact Table.sortedByKey_singleton p
  | cons q qs ih =>
    rw [Table.SortedByKey.cons_iff] at hs
    obtain ⟨hhead, htail⟩ := hs
    by_cases hlt : p.1 < q.1
    · simp only [insertTail, hlt, if_true]
      rw [Table.SortedByKey.cons_iff]
      refine ⟨?_, Table.SortedByKey.cons_iff.2 ⟨hhead, htail⟩⟩
      intro x hx
      rcases List.mem_cons.1 hx with hxq | hxqs
      · exact hxq ▸ UInt32.le_of_lt hlt
      · exact UInt32.le_trans (UInt32.le_of_lt hlt) (hhead x hxqs)
    · simp only [insertTail, hlt, if_false]
      rw [Table.SortedByKey.cons_iff]
      refine ⟨?_, ih htail⟩
      intro x hx
      rcases List.mem_cons.1 ((insertTail_perm p qs).subset hx) with
        hxp | hxqs
      · exact hxp ▸ UInt32.not_lt.1 hlt
      · exact hhead x hxqs

/-- The loop only moves the entries. -/
theorem foldl_insertTail_perm (rest acc : List (UInt32 × UInt32)) :
    (rest.foldl (fun a p => insertTail p a) acc).Perm (acc ++ rest) := by
  induction rest generalizing acc with
  | nil => simp
  | cons p ps ih =>
    refine (ih (insertTail p acc)).trans ?_
    refine ((insertTail_perm p acc).append_right ps).trans ?_
    exact (List.perm_middle (a := p) (l₁ := acc) (l₂ := ps)).symm

/-- The model of absolute `func 15` only moves the entries. -/
theorem insertionShiftLeft_perm (pairs : List (UInt32 × UInt32))
    (offset : Nat) : (insertionShiftLeft pairs offset).Perm pairs := by
  refine (foldl_insertTail_perm (pairs.drop offset)
    (pairs.take offset)).trans ?_
  rw [List.take_append_drop]

/-- The loop keeps the key order. -/
theorem foldl_insertTail_sorted (rest : List (UInt32 × UInt32))
    {acc : List (UInt32 × UInt32)} (hs : Table.SortedByKey acc) :
    Table.SortedByKey (rest.foldl (fun a p => insertTail p a) acc) := by
  induction rest generalizing acc with
  | nil => exact hs
  | cons p ps ih => exact ih (insertTail_sorted p hs)

/-- The model of absolute `func 15` puts the entries in key order, as soon
as the first `offset` entries are in key order. -/
theorem insertionShiftLeft_sorted (pairs : List (UInt32 × UInt32))
    (offset : Nat) (hs : Table.SortedByKey (pairs.take offset)) :
    Table.SortedByKey (insertionShiftLeft pairs offset) :=
  foldl_insertTail_sorted (pairs.drop offset) hs

/-! ## `heapsort`, absolute `func 25` -/

/-- The child of `node` that the compiled loop picks: the greater of the
two children, and `node` itself when `node` has no child below `len`.
`2 * node + 1` is always above `node`, so the answer is `node` exactly in
the childless case. -/
def greaterChild (ps : List (UInt32 × UInt32)) (len node : Nat) : Nat :=
  if len ≤ 2 * node + 1 then node
  else if 2 * node + 2 < len ∧
      keyAt ps (2 * node + 1) < keyAt ps (2 * node + 2) then
    2 * node + 2
  else 2 * node + 1

/-- `fuel` steps of the sift-down of `node` through the first `len`
entries.  One step swaps `node` with its greater child and moves down. -/
def siftDownAux (fuel : Nat) (ps : List (UInt32 × UInt32))
    (len node : Nat) : List (UInt32 × UInt32) :=
  match fuel with
  | 0 => ps
  | fuel + 1 =>
    let child := greaterChild ps len node
    if child = node then ps
    else if keyAt ps node < keyAt ps child then
      siftDownAux fuel (Table.swapAt ps node child) len child
    else ps

/-- The sift-down of `node` through the first `len` entries.  The index at
least doubles at every step, so `len` steps of fuel are enough. -/
def siftDown (ps : List (UInt32 × UInt32)) (len node : Nat) :
    List (UInt32 × UInt32) :=
  siftDownAux len ps len node

/-- The max-heap invariant over the first `len` entries: no child key is
above its parent key.  The parent of `child` is `(child - 1) / 2`. -/
def IsHeap (ps : List (UInt32 × UInt32)) (len : Nat) : Prop :=
  ∀ child, 0 < child → child < len →
    keyAt ps child ≤ keyAt ps ((child - 1) / 2)

/-- One step of the merged loop of absolute `func 25`.  The compiled body
counts `i` down from `len + len / 2` and splits on `len <= i`: above `len`
it builds the heap over the whole slice, below `len` it moves the greatest
entry to position `i` and repairs the shorter prefix. -/
def heapsortStep (ps : List (UInt32 × UInt32)) (len i : Nat) :
    List (UInt32 × UInt32) :=
  if len ≤ i then siftDown ps len (i - len)
  else siftDown (Table.swapAt ps 0 i) i 0

/-- The model of absolute `func 25`. -/
def heapsortModel (ps : List (UInt32 × UInt32)) : List (UInt32 × UInt32) :=
  (List.range (ps.length + ps.length / 2)).reverse.foldl
    (fun acc i => heapsortStep acc ps.length i) ps

/-- A sift-down keeps the length. -/
theorem siftDownAux_length (fuel : Nat) (ps : List (UInt32 × UInt32))
    (len node : Nat) : (siftDownAux fuel ps len node).length = ps.length := by
  induction fuel generalizing ps node with
  | zero => rfl
  | succ fuel ih =>
    rw [siftDownAux]
    split
    · rfl
    · split
      · rw [ih, Table.swapAt_length]
      · rfl

theorem siftDown_length (ps : List (UInt32 × UInt32)) (len node : Nat) :
    (siftDown ps len node).length = ps.length :=
  siftDownAux_length len ps len node

theorem heapsortStep_length (ps : List (UInt32 × UInt32)) (len i : Nat) :
    (heapsortStep ps len i).length = ps.length := by
  rw [heapsortStep]
  split
  · exact siftDown_length ps len _
  · rw [siftDown_length, Table.swapAt_length]

theorem heapsortModel_length (ps : List (UInt32 × UInt32)) :
    (heapsortModel ps).length = ps.length := by
  have hfold : ∀ (steps : List Nat) (acc : List (UInt32 × UInt32)),
      (steps.foldl (fun a i => heapsortStep a ps.length i) acc).length
        = acc.length := by
    intro steps
    induction steps with
    | nil => intro acc; rfl
    | cons i rest ih =>
      intro acc
      rw [List.foldl_cons, ih, heapsortStep_length]
  exact hfold _ ps

/-! ## The partition of `quicksort`, absolute `func 24` -/

/-- The register state of the compiled partition loop: the entries below
the pivot, the entries at or above it, the index of the hole the loop
writes into, and the one entry the loop holds in a register. -/
structure PartitionState where
  lt : List (UInt32 × UInt32)
  ge : List (UInt32 × UInt32)
  gap : Nat
  tmp : UInt32 × UInt32

/-! ## The bidirectional merge of the small sort -/

/-- The comparison of the forward half: the smaller key wins. -/
def keyLt (a b : UInt32 × UInt32) : Bool := a.1 < b.1

/-- The comparison of the backward half: the greater key wins. -/
def keyGt (a b : UInt32 × UInt32) : Bool := b.1 < a.1

/-- `n` steps of a merge of two runs that takes whichever head `lt`
prefers.  The result is the output, then what is left of each run.  The
compiled loop reads both heads on every step, and this model takes the
only head there is when one run is empty. -/
def mergeTake (lt : UInt32 × UInt32 → UInt32 × UInt32 → Bool) :
    Nat → List (UInt32 × UInt32) → List (UInt32 × UInt32) →
      List (UInt32 × UInt32) × List (UInt32 × UInt32) ×
        List (UInt32 × UInt32)
  | 0, l, r => ([], l, r)
  | _ + 1, [], [] => ([], [], [])
  | n + 1, x :: xs, [] =>
    let step := mergeTake lt n xs []
    (x :: step.1, step.2.1, step.2.2)
  | n + 1, [], y :: ys =>
    let step := mergeTake lt n [] ys
    (y :: step.1, step.2.1, step.2.2)
  | n + 1, x :: xs, y :: ys =>
    if lt y x then
      let step := mergeTake lt n (x :: xs) ys
      (y :: step.1, step.2.1, step.2.2)
    else
      let step := mergeTake lt n xs (y :: ys)
      (x :: step.1, step.2.1, step.2.2)

/-- The forward half of the bidirectional merge: `n` entries off the two
fronts, in key order. -/
def mergeUp (n : Nat) (l r : List (UInt32 × UInt32)) :
    List (UInt32 × UInt32) × List (UInt32 × UInt32) ×
      List (UInt32 × UInt32) :=
  mergeTake keyLt n l r

/-- The backward half of the bidirectional merge: `n` entries off the two
backs.  The compiled loop writes them from the end of the output down, so
the model reverses the two runs, takes the greater key first, and reverses
what it built. -/
def mergeDown (n : Nat) (l r : List (UInt32 × UInt32)) :
    List (UInt32 × UInt32) × List (UInt32 × UInt32) ×
      List (UInt32 × UInt32) :=
  let step := mergeTake keyGt n l.reverse r.reverse
  (step.1.reverse, step.2.1.reverse, step.2.2.reverse)

/-- The bidirectional merge of two runs that are each in key order.  Each
half writes `(l.length + r.length) / 2` entries, which is why the callers
merge runs of even total length. -/
def bimerge (l r : List (UInt32 × UInt32)) : List (UInt32 × UInt32) :=
  (mergeUp ((l.length + r.length) / 2) l r).1 ++
    (mergeDown ((l.length + r.length) / 2) l r).1

/-- The check that absolute `func 24` makes after a bidirectional merge:
the forward half and the backward half meet exactly, so together they take
every entry of both runs and neither half runs past the other.

A comparison that is not a strict total order breaks this, and the
compiled code answers with `call 107` and `unreachable`, which is the dead
arm X-F24-ORDER of `Analysis/scope-and-exclusions.md`.  The body proof of
absolute `func 24` must show this property from the strict key order and
`NodupKeys`.  It is stated here and not proved here. -/
def BimergeExhausts (l r : List (UInt32 × UInt32)) : Prop :=
  ((mergeUp ((l.length + r.length) / 2) l r).2.1).length +
      ((mergeDown ((l.length + r.length) / 2) l r).2.1).length = l.length ∧
    ((mergeUp ((l.length + r.length) / 2) l r).2.2).length +
      ((mergeDown ((l.length + r.length) / 2) l r).2.2).length = r.length

end Project.RustHashMap.SortModels
