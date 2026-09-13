import CodeLib.RustStd.HashMap.TableRefinement

/-!
# The sorted-by-key vocabulary of the pair sort

`collect_entries` builds a `Vec<(u32, u32)>` and then sorts it by key with
`sort_unstable_by_key`.  The encoder writes the sorted list, so a body
proof of the sort must end with a statement about key order.  This module
names that statement once.

`SortedByKey` is `List.Pairwise` of `fun a b => a.1 <= b.1`.  The relation
is `<=` and not `<` because `Table.eq_of_perm_of_pairwise` asks for `<=`.
On a list with distinct keys the two agree, so nothing is lost.

The one theorem a caller wants is `eq_sortByKey_of_perm_of_sorted`.  It
says that a sorted permutation of a list with distinct keys *is* the
model sort.  A body proof therefore never shows that the compiled code
runs merge sort.  It shows two much cheaper facts: the output is a
permutation of the input, and the output is in key order.

The rest of the file is the algebra that the network proofs of
`CodeLib.RustStd.HashMap.SortingNetwork` use to build such a proof:
`SortedByKey` of a singleton, of a cons, of an append, of a reversed
descending run, and of a strictly increasing run.
-/

namespace Wasm.RustStd.HashMap.Table

/-! ## The predicate -/

/-- The entry list is in key order.  Equal keys may be next to each
other, which `NodupKeys` then rules out. -/
def SortedByKey (l : List (UInt32 × UInt32)) : Prop :=
  l.Pairwise (fun a b => a.1 ≤ b.1)

instance (l : List (UInt32 × UInt32)) : Decidable (SortedByKey l) := by
  unfold SortedByKey; infer_instance

@[simp] theorem SortedByKey.nil : SortedByKey [] := List.Pairwise.nil

@[simp] theorem sortedByKey_singleton (p : UInt32 × UInt32) :
    SortedByKey [p] := List.pairwise_singleton _ _

/-- A cons is in key order when its head is below every later key and the
tail is in key order. -/
theorem SortedByKey.cons_iff {p : UInt32 × UInt32}
    {l : List (UInt32 × UInt32)} :
    SortedByKey (p :: l) ↔ (∀ q ∈ l, p.1 ≤ q.1) ∧ SortedByKey l :=
  List.pairwise_cons

/-- Two runs in a row are in key order exactly when each run is and every
key of the first run is below every key of the second. -/
theorem sortedByKey_append (a b : List (UInt32 × UInt32)) :
    SortedByKey (a ++ b) ↔
      SortedByKey a ∧ SortedByKey b ∧ ∀ x ∈ a, ∀ y ∈ b, x.1 ≤ y.1 :=
  List.pairwise_append

/-- A run with strictly increasing keys is in key order. -/
theorem sortedByKey_of_sorted_strict {l : List (UInt32 × UInt32)}
    (h : l.Pairwise (fun a b => a.1 < b.1)) : SortedByKey l :=
  h.imp (fun hlt => UInt32.le_of_lt hlt)

/-- A run with strictly decreasing keys is in key order after a reverse.
The compiled sort makes such a run when it walks a comparator backwards. -/
theorem sortedByKey_reverse_of_desc {l : List (UInt32 × UInt32)}
    (h : l.Pairwise (fun a b => b.1 < a.1)) : SortedByKey l.reverse :=
  List.pairwise_reverse.2 (h.imp (fun hlt => UInt32.le_of_lt hlt))

/-! ## The model sort -/

/-- The model sort puts the entries in key order. -/
theorem sortedByKey_sortByKey (l : List (UInt32 × UInt32)) :
    SortedByKey (sortByKey l) :=
  pairwise_sortByKey (fun _ _ _ => UInt32.le_trans)
    (fun a b => UInt32.le_total a b) l

/-- Distinct keys survive a reorder in either direction. -/
theorem nodupKeys_of_perm {l m : List (UInt32 × UInt32)} (hp : l.Perm m)
    (hn : NodupKeys m) : NodupKeys l :=
  ((hp.map Prod.fst).nodup_iff).2 hn

/-- A sorted permutation of a list with distinct keys is the model sort.

This is the bridge a body proof crosses.  The proof of the compiled sort
gives the permutation and the key order.  This theorem turns the two into
the `sortByKey` that `Project.RustHashMap.Spec` names. -/
theorem eq_sortByKey_of_perm_of_sorted {l out : List (UInt32 × UInt32)}
    (hn : NodupKeys l) (hp : out.Perm l) (hs : SortedByKey out) :
    out = sortByKey l :=
  Table.eq_of_perm_of_pairwise (fun _ _ => UInt32.le_antisymm) out
    (sortByKey l) hs (sortedByKey_sortByKey l) (nodupKeys_of_perm hp hn)
    (hp.trans (sortByKey_perm l).symm)

end Wasm.RustStd.HashMap.Table
