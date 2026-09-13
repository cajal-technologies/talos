import CodeLib.RustStd.HashMap.TableRefinement

/-!
# The insert fold of `collect_entries`

`Table.ofEntries` is `Table.extend` on `Table.empty`: one `Table.reserve`
with the exact length of the entry list, then one `Table.insert` per entry.
The compiled `collect_entries`, absolute `func 5` at WAT lines 851 to 974,
has the same two phases.  It calls `func 17` once with the entry count, and
then calls `func 18` once per pair, in wire order.

This file names the facts that a body proof of `func 5` needs.

* `reserve_empty` reads the `reserve` of the static empty singleton as
  `Table.withCapacity`, which is the table that the contract of `func 17`
  returns.
* `ofEntries_eq_insertAll` puts the two phases together, so the table after
  the last pair is the one that the contract of `func 5` names.
* `insertAll_prefix` is the loop invariant.  After the first `k` pairs the
  table is still well formed and clean, it keeps its bucket count, and it
  keeps room for the pairs that are left.  That room is the
  `1 ≤ growthLeft` that the contract of `func 18` asks for.
* `withCapacity_wf`, `withCapacity_clean`, `withCapacity_growthLeft` and
  `withCapacity_buckets_lt` start the invariant at the table that `func 17`
  returns.  `Clean.growthLeft_le` bounds `growthLeft` by the bucket count,
  which is the other hypothesis that `func 18` asks for.

`TableRefinement.insertAll_inv` proves the same invariant for the whole
list at once.  A compiled loop needs it one step at a time, with the step
count as the index, so `insertAll_prefix` states it over `List.take`.
-/

namespace Wasm.RustStd.HashMap.Table

open Wasm.RustStd.HashMap

variable {K V : Type}

/-! ## The reserve of the static empty table -/

/-- The empty singleton has no full bucket. -/
theorem fullIndices_empty : fullIndices (empty : Table K V) = [] := rfl

/-- `reserve` on the empty singleton is `with_capacity`, at every count.
The guard `additional ≤ growth_left` holds only at 0, where both sides are
the singleton, and every larger count resizes an empty table, which moves
no bucket. -/
theorem reserve_empty (hash : K → UInt64) (n : Nat) :
    Table.reserve hash (empty : Table K V) n = withCapacity n := by
  have hitems : (empty : Table K V).items = 0 := rfl
  have hcap : bucketMaskToCapacity ((empty : Table K V).buckets - 1) = 0 := rfl
  unfold Table.reserve
  by_cases h0 : n = 0
  · rw [h0, if_pos (show 0 ≤ (empty : Table K V).growthLeft from Nat.zero_le _)]
    rw [withCapacity, if_pos rfl]
  · rw [if_neg (show ¬ n ≤ (empty : Table K V).growthLeft by
      show ¬ n ≤ 0
      omega)]
    show (if (empty : Table K V).items + n ≤
        bucketMaskToCapacity ((empty : Table K V).buckets - 1) / 2 then _
      else Table.resize hash empty
        (max ((empty : Table K V).items + n)
          (bucketMaskToCapacity ((empty : Table K V).buckets - 1) + 1))) = _
    rw [if_neg (show ¬ (empty : Table K V).items + n ≤
        bucketMaskToCapacity ((empty : Table K V).buckets - 1) / 2 by
      rw [hitems, hcap, Nat.zero_div]
      omega)]
    rw [hitems, hcap, Nat.zero_add, Nat.zero_add, Nat.max_eq_left (by omega)]
    unfold Table.resize
    rw [fullIndices_empty, withCapacity_eq]
    rfl

/-- `from_iter` with the exact length: one `with_capacity`, then the insert
fold.  This is the shape of the compiled `collect_entries`. -/
theorem ofEntries_eq_insertAll [BEq K] (hash : K → UInt64) (es : List (K × V)) :
    ofEntries hash es = insertAll hash (withCapacity es.length) es := by
  rw [ofEntries_eq, reserve_empty]

/-! ## The table that `reserve_rehash_inner` returns -/

theorem withCapacity_wf {cap : Nat} (hc : cap * 8 / 7 ≤ 2 ^ 32) (hash : K → UInt64) :
    WF hash (withCapacity cap : Table K V) := by
  rw [withCapacity_eq]
  exact wf_newEmpty (capBuckets_spec hc).1 hash

theorem withCapacity_clean (cap : Nat) : Clean (withCapacity cap : Table K V) := by
  rw [withCapacity_eq]
  exact clean_newEmpty _

theorem withCapacity_growthLeft {cap : Nat} (hc : cap * 8 / 7 ≤ 2 ^ 32) :
    cap ≤ (withCapacity cap : Table K V).growthLeft := by
  rw [withCapacity_eq]
  exact (capBuckets_spec hc).2

theorem withCapacity_buckets_lt {cap : Nat} (hc : cap * 8 / 7 ≤ 2 ^ 31) :
    (withCapacity cap : Table K V).buckets < 2 ^ 32 := by
  rw [withCapacity_eq]
  exact capBuckets_lt hc

/-- `growth_left` never passes the bucket count of a clean table.  The
compiled `insert` reads it as a `u32` word, so a body proof needs it below
`2 ^ 32`. -/
theorem Clean.growthLeft_le {t : Table K V} (hcl : Clean t) : t.growthLeft ≤ t.buckets := by
  have h := hcl.2
  unfold bucketMaskToCapacity at h
  by_cases h8 : t.buckets - 1 < 8
  · rw [if_pos h8] at h
    omega
  · rw [if_neg h8] at h
    have : (t.buckets - 1 + 1) / 8 * 7 ≤ t.buckets := by omega
    omega

/-! ## The loop invariant -/

theorem insertAll_nil [BEq K] (hash : K → UInt64) (t : Table K V) :
    insertAll hash t [] = t := rfl

theorem insertAll_append [BEq K] (hash : K → UInt64) (t : Table K V)
    (es₁ es₂ : List (K × V)) :
    insertAll hash t (es₁ ++ es₂) = insertAll hash (insertAll hash t es₁) es₂ := by
  unfold insertAll
  rw [List.foldl_append]

section Prefix
variable [BEq K] [LawfulBEq K] {hash : K → UInt64}

/-- The compiled loop of `collect_entries` inserts one pair per iteration.
After `k` of them the table is still well formed and clean, it kept its
bucket count, and `growth_left` still covers the pairs that are left.

The bound on `growth_left` is the same accounting that
`TableRefinement.insertAll_inv` uses: `Clean` ties `growth_left + items` to
the bucket count, `WF` ties `items` to the entry list, and one insert grows
the entry list by at most one. -/
theorem insertAll_prefix (hash : K → UInt64) :
    ∀ (k : Nat) (t : Table K V) (es : List (K × V)), WF hash t → Clean t →
      es.length ≤ t.growthLeft → k ≤ es.length →
      WF hash (insertAll hash t (es.take k)) ∧
        Clean (insertAll hash t (es.take k)) ∧
        (insertAll hash t (es.take k)).buckets = t.buckets ∧
        es.length - k ≤ (insertAll hash t (es.take k)).growthLeft
  | 0, t, es, hw, hcl, hg, _ => by
    rw [List.take_zero, insertAll_nil]
    exact ⟨hw, hcl, rfl, by omega⟩
  | k + 1, t, es, hw, hcl, hg, hk => by
    have hlt : k < es.length := by omega
    obtain ⟨kv, hkv⟩ : ∃ kv, es[k]? = some kv :=
      ⟨es[k], List.getElem?_eq_getElem hlt⟩
    have hsplit : es.take (k + 1) = es.take k ++ [kv] := by
      rw [List.take_add_one, hkv]
      rfl
    obtain ⟨hw', hcl', hb', hg'⟩ := insertAll_prefix hash k t es hw hcl hg (by omega)
    set u := insertAll hash t (es.take k) with hu
    have hg1 : 1 ≤ u.growthLeft := by omega
    obtain ⟨hw2, hcl2, hb2, -, hperm2⟩ := hw'.insert_of_growth hcl' hg1 kv.1 kv.2
    rw [hsplit, insertAll_append, ← hu, insertAll_cons, insertAll_nil]
    refine ⟨hw2, hcl2, by rw [hb2, hb'], ?_⟩
    have c1 := hcl'.2
    have c2 := hcl2.2
    have c3 := hw'.items_eq
    have c4 := hw2.items_eq
    have c5 := hperm2.length_eq
    have c6 := length_insert_le (toList u) kv.1 kv.2
    rw [hb2] at c2
    show es.length - (k + 1) ≤ (Table.insert hash u kv.1 kv.2).2.growthLeft
    omega

end Prefix

end Wasm.RustStd.HashMap.Table
