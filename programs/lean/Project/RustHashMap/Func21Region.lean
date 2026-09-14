import Project.RustHashMap.Func21Network9
import Project.RustHashMap.Func21Network13

/-!
# The region sort of the `quicksort` small sort

Absolute `func 24` is `quicksort`, local `func21`.  WAT lines 6193 to
8501 of `programs/rust/build/rust_hash_map/program.wat` hold the region
half of the small sort, which is the guard, the split into regions, the
region loop and the step to the second region.  The merge of WAT 8503 to
8652 is not here.

## What the region half computes

The small sort runs on a length below 33.  WAT 6193 to 6196 leave at
once when the length is below two, because a list of one entry is
already in key order.  WAT 6197 to 6219 split the input:

* a length below 18 makes one region, the whole input;
* a length of 18 or more makes two regions, the first `len / 2` entries
  and the rest.

Local 7 holds the length of the region that runs now, local 8 its
address, local 13 the address of the second region, local 16 the half
length, local 17 the test `length < 18` and local 18 the length of the
second region.

The loop of WAT 6220 to 8502 sorts one region in each turn.  It picks a
kernel by the region length `n`:

* `n` of 8 or less: the insertion sort alone, from the offset one;
* `n` of 9 to 12: the nine-entry network, then the insertion sort from
  the offset nine;
* `n` of 13 or more: the thirteen-entry network, then the insertion
  sort from the offset thirteen.

Local 6 holds the offset that the insertion sort starts from, so it is
one, nine or thirteen.  The order test of WAT 8393 to 8396 is dead: the
offset never passes the region length.

The insertion sort of WAT 8397 to 8489 is the body of absolute `func 15`
again, inlined with other register names.  `Func12Proof` proves that
body; this module repeats its two loop invariants with the names of this
body.

## The register names of the inlined insertion sort

| `func 15` | here | Meaning |
| --- | --- | --- |
| 0 | 8 | the region address |
| 1 | 6 | the length, then the byte index of the hole |
| 2 | 7 | the offset, then the address of the hole |
| 3 | 15 | the address one entry past the region |
| 4 | 11 | the byte index of the outer cursor |
| 5 | 10 | the address of the outer cursor |
| 6 | 9 | the key of the entry that the body holds |
| 7 | 12 | the value of the entry that the body holds |

The setup of WAT 8398 to 8414 reads the length from local 7 and the
offset from local 6, and the two loops then use local 6 for the byte
index of the hole and local 7 for the address of the hole.  The region
length is therefore not in local 7 once the shift loop has run, so the
invariants carry it.

## What the four theorems say

* `twp_region_insertion` runs WAT 8397 to 8489 on one region whose first
  `k` entries are in key order, and leaves `insertionShiftLeft R k`.
* `twp_sort_region` runs one whole turn of the region loop, WAT 6221 to
  8489, and leaves a sorted permutation of the region.
* `twp_region_loop_single` runs WAT 6193 to 8501 for a length below 18.
  The loop makes one turn and leaves through WAT 8491.
* `twp_region_loop_double` runs the same code for a length of 18 to 32.
  The loop makes two turns and falls through to WAT 8503.

## The three registers that the networks take

The networks write the locals 2, 3 and 4, which hold the ancestor
pivot, the recursion limit and the comparison closure on entry.  The
small sort never reads those three again, so `NetScratch` carries them
with every other register that only a network writes.
-/

namespace Project.RustHashMap.Func21Region

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.SortModels
open Project.RustHashMap.SortPures
open Project.RustHashMap.Func21Defs
open scoped Wasm.SmallStep.Outcome

set_option maxRecDepth 40000

/-! ## Word and address bridges

Every lemma of this section is a copy of a private lemma of
`Project.RustHashMap.Func12Proof`, which this module cannot name.
-/

/-- `.const 4294967288` is minus eight. -/
private theorem addNegEight (x : UInt32) : x + 4294967288 = x - 8 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967288 : UInt32).toNat = 4294967288 from rfl,
    show (8 : UInt32).toNat = 8 from rfl] at *
  omega

/-- The address of entry `n + 1` is eight above the address of entry
`n`. -/
private theorem addr_succ (v : UInt32) (n : Nat) :
    v + UInt32.ofNat (8 * n) + 8 = v + UInt32.ofNat (8 * (n + 1)) := by
  have h8 : (8 : UInt32) = UInt32.ofNat 8 := rfl
  rw [show 8 * (n + 1) = 8 * n + 8 from by omega, UInt32.ofNat_add, h8,
    UInt32.add_assoc]

/-- Stepping the cursor back by one entry. -/
private theorem addr_back (v : UInt32) (n : Nat) :
    v + UInt32.ofNat (8 * (n + 1)) + 4294967288
      = v + UInt32.ofNat (8 * n) := by
  rw [← addr_succ, addNegEight, UInt32.add_sub_cancel]

/-- Stepping the cursor back by two entries. -/
private theorem addr_back_two (v : UInt32) (n : Nat) :
    v + UInt32.ofNat (8 * (n + 2)) + 4294967280
      = v + UInt32.ofNat (8 * n) := by
  have h : (4294967280 : UInt32) = 4294967288 + 4294967288 := by decide
  rw [h, ← UInt32.add_assoc, show n + 2 = (n + 1) + 1 from rfl,
    addr_back, addr_back]

/-- `i32.shl` by three is a multiplication by eight. -/
private theorem shift_three (x : UInt32)
    (hbound : 8 * x.toNat < UInt32.size) :
    x <<< (3 : UInt32) = UInt32.ofNat (8 * x.toNat) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have h2 : (2 : Nat) ^ 3 = 8 := by norm_num
  have hlt : x.toNat * 8 < 2 ^ 32 := by omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft, show (3 : UInt32).toNat % 32 = 3 by decide,
    Nat.shiftLeft_eq, h2, Nat.mod_eq_of_lt hlt,
    UInt32.toNat_ofNat_of_lt' hbound]
  omega

/-- The word that `i64.extend_i32_u` pushes. -/
private theorem extendU_eq (x : UInt32) :
    UInt64.ofNat x.toNat = x.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hx : x.toNat < 2 ^ 64 := by
    have := UInt32.toNat_lt x
    have hsz : UInt32.size = 4294967296 := rfl
    omega
  rw [UInt64.toNat_ofNat_of_lt' hx, UInt32.toNat_toUInt64]

/-- The shift count of the write back, after the Wasm mask. -/
private theorem shift_count : (32 : UInt64) % 64 = 32 := rfl

/-- `i32.shl` by three, after the Wasm mask. -/
private theorem shl_three (x : UInt32) : x <<< ((3 : UInt32) % 32)
    = x <<< 3 := rfl

/-! ## List vocabulary of the two invariants -/

/-- Entry `i` of a list, with no proof that `i` is in range. -/
private def entryAt (ps : List (UInt32 × UInt32)) (i : Nat) :
    UInt32 × UInt32 :=
  ps.getD i (0, 0)

private theorem keyAt_entryAt (ps : List (UInt32 × UInt32)) (i : Nat) :
    keyAt ps i = (entryAt ps i).1 := rfl

private theorem entryAt_eq_getElem (ps : List (UInt32 × UInt32))
    {i : Nat} (hi : i < ps.length) : entryAt ps i = ps[i] :=
  List.getD_eq_getElem _ _ hi

private theorem take_length_eq {α : Type} {l : List α} {i : Nat}
    (hi : i ≤ l.length) : (l.take i).length = i := by
  rw [List.length_take, Nat.min_eq_left hi]

private theorem take_succ_eq (l : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [entryAt l i] := by
  rw [List.take_add_one, entryAt_eq_getElem l hi,
    List.getElem?_eq_getElem hi]
  rfl

private theorem drop_eq_cons (l : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < l.length) :
    l.drop i = entryAt l i :: l.drop (i + 1) := by
  rw [entryAt_eq_getElem l hi, List.drop_eq_getElem_cons hi]

/-- Setting the one entry between two runs. -/
private theorem set_middle {α : Type} (pre : List α) (a q : α)
    (post : List α) :
    (pre ++ a :: post).set pre.length q = pre ++ q :: post := by
  induction pre with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- A sorted list has ascending keys. -/
private theorem keyAt_mono {A : List (UInt32 × UInt32)}
    (hs : Table.SortedByKey A) {m k : Nat} (hmk : m ≤ k)
    (hk : k < A.length) : keyAt A m ≤ keyAt A k := by
  have hm : m < A.length := Nat.lt_of_le_of_lt hmk hk
  rw [keyAt_eq_getElem A hm, keyAt_eq_getElem A hk]
  rcases Nat.eq_or_lt_of_le hmk with heq | hlt
  · subst heq; exact UInt32.le_refl _
  · exact (List.pairwise_iff_getElem.mp hs) m k hm hk hlt

/-! ## The model insertion as a split -/

/-- The compiled shift loop stops at the first entry whose key is above
the held key.  `insertTail` puts the held entry at exactly that
place. -/
private theorem insertTail_eq_of_split (p : UInt32 × UInt32) :
    ∀ (l : List (UInt32 × UInt32)) (i : Nat), i ≤ l.length →
      (∀ m, m < i → ¬ (p.1 < keyAt l m)) →
      (i < l.length → p.1 < keyAt l i) →
      insertTail p l = l.take i ++ p :: l.drop i := by
  intro l
  induction l with
  | nil =>
    intro i hi _ _
    have : i = 0 := Nat.le_zero.mp (by simpa using hi)
    subst this
    rfl
  | cons q qs ih =>
    intro i hi hbelow habove
    match i with
    | 0 =>
      have hlt : p.1 < q.1 := habove (by simp)
      simp only [insertTail, hlt, if_true, List.take_zero,
        List.drop_zero, List.nil_append]
    | i + 1 =>
      have hge : ¬ (p.1 < q.1) := hbelow 0 (Nat.succ_pos i)
      have hi' : i ≤ qs.length := by simpa using hi
      have hbelow' : ∀ m, m < i → ¬ (p.1 < keyAt qs m) := by
        intro m hm
        exact hbelow (m + 1) (by omega)
      have habove' : i < qs.length → p.1 < keyAt qs i := by
        intro hlt
        exact habove (by simpa using hlt)
      simp only [insertTail, hge, if_false, ih i hi' hbelow' habove',
        List.take_succ_cons, List.drop_succ_cons, List.cons_append]

/-! ## The state of the outer loop -/

/-- The region after the outer loop has put the first `j - off` later
entries into place. -/
private def outerAcc (pairs : List (UInt32 × UInt32)) (off j : Nat) :
    List (UInt32 × UInt32) :=
  ((pairs.drop off).take (j - off)).foldl
    (fun acc p => insertTail p acc) (pairs.take off)

private theorem foldl_insertTail_length
    (rest : List (UInt32 × UInt32)) :
    ∀ acc : List (UInt32 × UInt32),
      (rest.foldl (fun a p => insertTail p a) acc).length
        = acc.length + rest.length := by
  induction rest with
  | nil => intro acc; simp
  | cons p ps ih =>
    intro acc
    have hlen : (insertTail p acc).length = acc.length + 1 :=
      ((insertTail_perm p acc).length_eq).trans (by simp)
    simp only [List.foldl_cons, ih (insertTail p acc), hlen,
      List.length_cons]
    omega

private theorem outerAcc_self (pairs : List (UInt32 × UInt32))
    (off : Nat) : outerAcc pairs off off = pairs.take off := by
  simp [outerAcc]

private theorem outerAcc_length (pairs : List (UInt32 × UInt32))
    {off j : Nat} (hoff : off ≤ j) (hj : j ≤ pairs.length) :
    (outerAcc pairs off j).length = j := by
  have hle : off ≤ pairs.length := Nat.le_trans hoff hj
  rw [outerAcc, foldl_insertTail_length, take_length_eq hle,
    List.length_take, List.length_drop]
  omega

private theorem outerAcc_succ (pairs : List (UInt32 × UInt32))
    {off j : Nat} (hoff : off ≤ j) (hj : j < pairs.length) :
    outerAcc pairs off (j + 1)
      = insertTail (entryAt pairs j) (outerAcc pairs off j) := by
  have hlt : j - off < (pairs.drop off).length := by
    rw [List.length_drop]; omega
  have hget : entryAt (pairs.drop off) (j - off) = entryAt pairs j := by
    rw [entryAt_eq_getElem _ hlt, entryAt_eq_getElem pairs hj,
      List.getElem_drop]
    congr 1
    omega
  rw [outerAcc, outerAcc, show j + 1 - off = (j - off) + 1 from by omega,
    take_succ_eq _ hlt, hget, List.foldl_append]
  rfl

private theorem outerAcc_full (pairs : List (UInt32 × UInt32))
    (off : Nat) :
    outerAcc pairs off pairs.length = insertionShiftLeft pairs off := by
  rw [outerAcc, insertionShiftLeft]
  congr 1
  rw [List.take_of_length_le]
  rw [List.length_drop]

private theorem outerAcc_sorted (pairs : List (UInt32 × UInt32))
    {off j : Nat} (hs : Table.SortedByKey (pairs.take off)) :
    Table.SortedByKey (outerAcc pairs off j) :=
  foldl_insertTail_sorted _ hs

/-! ## Opening one entry of the buffer -/

section Slices

variable {α : Type} [WasmHeapGS α]

/-- Open the entry between two runs for an `i64` load or store. -/
private theorem slice_focus (v : UInt32) (pre : List (UInt32 × UInt32))
    (a : UInt32 × UInt32) (post : List (UInt32 × UInt32)) (n : Nat)
    (hn : pre.length = n) :
    Table.PairSlice (α := α) 0 v (pre ++ a :: post) ⊢
      iprop(pointsTo_u64 0 (v + UInt32.ofNat (8 * n))
          (Table.pairWord a) ∗
        (∀ q : UInt32 × UInt32,
          pointsTo_u64 0 (v + UInt32.ofNat (8 * n))
            (Table.pairWord q) -∗
            Table.PairSlice 0 v (pre ++ q :: post))) := by
  subst hn
  have hi : pre.length < (pre ++ a :: post).length := by simp
  have hget : (pre ++ a :: post)[pre.length] = a := by simp
  iintro Hs
  ihave ⟨Hcell, Hclose⟩ :=
    Table.PairSlice_focus 0 v (pre ++ a :: post) hi $$ Hs
  isimp only [hget] at Hcell
  isplitl_exact Hcell
  · iintro %q Hnew
    ihave Hdone := Hclose $$ %q Hnew
    isimp only [set_middle pre a q post] at Hdone
    iexact Hdone

/-- Open the key of the entry between two runs for an `i32` load. -/
private theorem slice_key (v : UInt32) (pre : List (UInt32 × UInt32))
    (a : UInt32 × UInt32) (post : List (UInt32 × UInt32)) (n : Nat)
    (hn : pre.length = n) :
    Table.PairSlice (α := α) 0 v (pre ++ a :: post) ⊢
      iprop(pointsTo_u32 0 (v + UInt32.ofNat (8 * n)) a.1 ∗
        (pointsTo_u32 0 (v + UInt32.ofNat (8 * n)) a.1 -∗
          Table.PairSlice 0 v (pre ++ a :: post))) := by
  subst hn
  have hi : pre.length < (pre ++ a :: post).length := by simp
  have hget : (pre ++ a :: post)[pre.length] = a := by simp
  iintro Hs
  ihave ⟨Hcell, Hclose⟩ :=
    Table.PairSlice_key 0 v (pre ++ a :: post) hi $$ Hs
  isimp only [hget] at Hcell
  isplitl_exact Hcell
  · iintro Hnew
    ihave Hdone := Hclose $$ %a.1 Hnew
    isimp only [hget, set_middle pre a a post] at Hdone
    iexact Hdone

/-- Open the value of the entry between two runs for an `i32` load. -/
private theorem slice_value (v : UInt32) (pre : List (UInt32 × UInt32))
    (a : UInt32 × UInt32) (post : List (UInt32 × UInt32)) (n : Nat)
    (hn : pre.length = n) :
    Table.PairSlice (α := α) 0 v (pre ++ a :: post) ⊢
      iprop(pointsTo_u32 0 (v + UInt32.ofNat (8 * n) + 4) a.2 ∗
        (pointsTo_u32 0 (v + UInt32.ofNat (8 * n) + 4) a.2 -∗
          Table.PairSlice 0 v (pre ++ a :: post))) := by
  subst hn
  have hi : pre.length < (pre ++ a :: post).length := by simp
  have hget : (pre ++ a :: post)[pre.length] = a := by simp
  iintro Hs
  ihave ⟨Hcell, Hclose⟩ :=
    Table.PairSlice_value 0 v (pre ++ a :: post) hi $$ Hs
  isimp only [hget] at Hcell
  isplitl_exact Hcell
  · iintro Hnew
    ihave Hdone := Hclose $$ %a.2 Hnew
    isimp only [hget, set_middle pre a a post] at Hdone
    iexact Hdone

/-- Open two entries in a row. -/
private theorem slice_two (v : UInt32) (pre : List (UInt32 × UInt32))
    (a b : UInt32 × UInt32) (post : List (UInt32 × UInt32)) (n : Nat)
    (hn : pre.length = n) :
    Table.PairSlice (α := α) 0 v (pre ++ a :: b :: post) ⊢
      iprop(pointsTo_u64 0 (v + UInt32.ofNat (8 * n))
          (Table.pairWord a) ∗
        pointsTo_u64 0 (v + UInt32.ofNat (8 * (n + 1)))
          (Table.pairWord b) ∗
        (∀ q : UInt32 × UInt32, ∀ r : UInt32 × UInt32,
          pointsTo_u64 0 (v + UInt32.ofNat (8 * n))
            (Table.pairWord q) -∗
          pointsTo_u64 0 (v + UInt32.ofNat (8 * (n + 1)))
            (Table.pairWord r) -∗
            Table.PairSlice 0 v (pre ++ q :: r :: post))) := by
  subst hn
  have haddr : v + UInt32.ofNat (8 * pre.length) + 8
      = v + UInt32.ofNat (8 * (pre.length + 1)) := addr_succ v pre.length
  have hsplit : ∀ q r : UInt32 × UInt32,
      Table.PairSlice (α := α) 0 v (pre ++ q :: r :: post) ⊣⊢
        iprop(Table.PairSlice 0 v pre ∗
          ((⌜(v + UInt32.ofNat (8 * pre.length)).toNat + 8
                < UInt32.size⌝ ∗
              pointsTo_u64 0 (v + UInt32.ofNat (8 * pre.length))
                (Table.pairWord q)) ∗
            ((⌜(v + UInt32.ofNat (8 * (pre.length + 1))).toNat + 8
                  < UInt32.size⌝ ∗
                pointsTo_u64 0 (v + UInt32.ofNat (8 * (pre.length + 1)))
                  (Table.pairWord r)) ∗
              Table.PairSlice 0
                (v + UInt32.ofNat (8 * (pre.length + 1)) + 8)
                post))) := by
    intro q r
    rw [← haddr]
    refine (Table.PairSlice_split 0 v (pre ++ q :: r :: post)
      pre.length (by simp)).trans ?_
    rw [show (pre ++ q :: r :: post).take pre.length = pre from by simp,
      show (pre ++ q :: r :: post).drop pre.length = q :: r :: post from
        by simp]
    refine BI.sep_congr .rfl ?_
    refine (Table.PairSlice_cons 0 _ q (r :: post)).trans ?_
    exact BI.sep_congr .rfl (Table.PairSlice_cons 0 _ r post)
  iintro Hs
  icases (hsplit a b).mp $$ Hs with ⟨Hpre, ⟨%h1, HA⟩, ⟨%h2, HB⟩, Hpost⟩
  isplitl_exact HA
  · isplitl_exact HB
    · iintro %q %r Hq Hr
      iapply (hsplit q r).mpr
      isplitl [Hpre]
      · iexact Hpre
      · isplitl [Hq]
        · isplitl_pureexact h1
          · iexact Hq
        · isplitl [Hr]
          · isplitl_pureexact h2
            · iexact Hr
          · iexact Hpost

/-- Two runs in a row are the two halves of one region. -/
private theorem slice_join (v : UInt32) (L T : List (UInt32 × UInt32))
    {m : Nat} (hL : L.length = m) :
    Table.PairSlice (α := α) 0 v (L ++ T) ⊣⊢
      iprop(Table.PairSlice 0 v L ∗
        Table.PairSlice 0 (v + UInt32.ofNat (8 * m)) T) := by
  refine (Table.PairSlice_split 0 v (L ++ T) m
    (by rw [List.length_append, hL]; omega)).trans ?_
  have ht : (L ++ T).take m = L := by
    have h : (L ++ T).take L.length = L := List.take_left
    rwa [hL] at h
  have hd : (L ++ T).drop m = T := by
    have h : (L ++ T).drop L.length = T := List.drop_left
    rwa [hL] at h
  rw [ht, hd]
  exact .rfl

end Slices

/-! ## Address facts of one entry cell -/

/-- Move an owned double word between two names of one address. -/
private theorem wordMove64 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 (α := α) 0 address value ⊢
      pointsTo_u64 0 address' value := by
  rw [haddress]

/-- The eight byte addresses of one `i64` cell. -/
private theorem offset_facts64 (base offset : UInt32) (o : Nat)
    (hoffset : UInt32.ofNat o = offset)
    (hbound : base.toNat + o + 8 ≤ UInt32.size) :
    (base + offset).toNat = base.toNat + offset.toNat ∧
      (base + offset + 1).toNat = (base + offset).toNat + 1 ∧
      (base + offset + 2).toNat = (base + offset).toNat + 2 ∧
      (base + offset + 3).toNat = (base + offset).toNat + 3 ∧
      (base + offset + 4).toNat = (base + offset).toNat + 4 ∧
      (base + offset + 5).toNat = (base + offset).toNat + 5 ∧
      (base + offset + 6).toNat = (base + offset).toNat + 6 ∧
      (base + offset + 7).toNat = (base + offset).toNat + 7 := by
  subst hoffset
  have ho : o < UInt32.size := by omega
  have hto : (UInt32.ofNat o).toNat = o := UInt32.toNat_ofNat_of_lt' ho
  have h0 : (base + UInt32.ofNat o).toNat = base.toNat + o :=
    Slices.byteOffset_toNat base o (by omega)
  refine ⟨by rw [h0, hto], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 4 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 5 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 6 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 7 (by omega)

/-- The three address facts that `twp_load32_addr` asks for. -/
private theorem addr_facts (addr : UInt32)
    (h : addr.toNat + 4 ≤ UInt32.size) :
    (addr + 1).toNat = addr.toNat + 1 ∧
      (addr + 2).toNat = addr.toNat + 2 ∧
      (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using Slices.byteOffset_toNat addr 1 (by omega),
    by simpa using Slices.byteOffset_toNat addr 2 (by omega),
    by simpa using Slices.byteOffset_toNat addr 3 (by omega)⟩

/-- The four byte addresses of one `i32` cell. -/
private theorem offset_facts (base offset : UInt32) (o : Nat)
    (hoffset : UInt32.ofNat o = offset)
    (hbound : base.toNat + o + 4 ≤ UInt32.size) :
    (base + offset).toNat = base.toNat + offset.toNat ∧
      (base + offset + 1).toNat = (base + offset).toNat + 1 ∧
      (base + offset + 2).toNat = (base + offset).toNat + 2 ∧
      (base + offset + 3).toNat = (base + offset).toNat + 3 := by
  subst hoffset
  have ho : o < UInt32.size := by omega
  have hto : (UInt32.ofNat o).toNat = o := UInt32.toNat_ofNat_of_lt' ho
  have h0 : (base + UInt32.ofNat o).toNat = base.toNat + o :=
    Slices.byteOffset_toNat base o (by omega)
  refine ⟨by rw [h0, hto], ?_, ?_, ?_⟩
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using
      Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)

/-- The cell of entry `i` of a buffer that does not wrap. -/
private theorem cell_facts64 (v : UInt32) (i n : Nat) (hin : i < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (v + UInt32.ofNat (8 * i) + 0).toNat
        = (v + UInt32.ofNat (8 * i)).toNat + (0 : UInt32).toNat ∧
      (v + UInt32.ofNat (8 * i) + 0 + 1).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 1 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 2).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 2 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 3).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 3 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 4).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 4 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 5).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 5 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 6).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 6 ∧
      (v + UInt32.ofNat (8 * i) + 0 + 7).toNat
        = (v + UInt32.ofNat (8 * i) + 0).toNat + 7 := by
  have hbase : (v + UInt32.ofNat (8 * i)).toNat = v.toNat + 8 * i :=
    Slices.byteOffset_toNat v (8 * i) (by omega)
  exact offset_facts64 (v + UInt32.ofNat (8 * i)) 0 0 rfl (by omega)

/-- The key cell of entry `i` of a buffer that does not wrap. -/
private theorem cell_facts32 (v : UInt32) (i n : Nat) (hin : i < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (v + UInt32.ofNat (8 * i) + 1).toNat
        = (v + UInt32.ofNat (8 * i)).toNat + 1 ∧
      (v + UInt32.ofNat (8 * i) + 2).toNat
        = (v + UInt32.ofNat (8 * i)).toNat + 2 ∧
      (v + UInt32.ofNat (8 * i) + 3).toNat
        = (v + UInt32.ofNat (8 * i)).toNat + 3 := by
  have hbase : (v + UInt32.ofNat (8 * i)).toNat = v.toNat + 8 * i :=
    Slices.byteOffset_toNat v (8 * i) (by omega)
  exact addr_facts (v + UInt32.ofNat (8 * i)) (by omega)

/-- The value cell of entry `i` of a buffer that does not wrap. -/
private theorem value_facts (v : UInt32) (i n : Nat) (hin : i < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (v + UInt32.ofNat (8 * i) + 4).toNat
        = (v + UInt32.ofNat (8 * i)).toNat + (4 : UInt32).toNat ∧
      (v + UInt32.ofNat (8 * i) + 4 + 1).toNat
        = (v + UInt32.ofNat (8 * i) + 4).toNat + 1 ∧
      (v + UInt32.ofNat (8 * i) + 4 + 2).toNat
        = (v + UInt32.ofNat (8 * i) + 4).toNat + 2 ∧
      (v + UInt32.ofNat (8 * i) + 4 + 3).toNat
        = (v + UInt32.ofNat (8 * i) + 4).toNat + 3 := by
  have hbase : (v + UInt32.ofNat (8 * i)).toNat = v.toNat + 8 * i :=
    Slices.byteOffset_toNat v (8 * i) (by omega)
  exact offset_facts (v + UInt32.ofNat (8 * i)) 4 4 rfl (by omega)

/-- Stepping the byte index back by one entry. -/
private theorem index_back (n : Nat) :
    UInt32.ofNat (8 * (n + 1)) + 4294967288 = UInt32.ofNat (8 * n) := by
  have h := addr_back 0 n
  simpa using h

/-- `i32.add` puts the second operand first. -/
private theorem addr_prev (v : UInt32) (n : Nat) :
    (4294967288 : UInt32) + (v + UInt32.ofNat (8 * (n + 1)))
      = v + UInt32.ofNat (8 * n) := by
  rw [UInt32.add_comm (4294967288 : UInt32), addr_back]

private theorem addr_prev_two (v : UInt32) (n : Nat) :
    (4294967280 : UInt32) + (v + UInt32.ofNat (8 * (n + 2)))
      = v + UInt32.ofNat (8 * n) := by
  rw [UInt32.add_comm (4294967280 : UInt32), addr_back_two]

private theorem index_prev (n : Nat) :
    (4294967288 : UInt32) + UInt32.ofNat (8 * (n + 1))
      = UInt32.ofNat (8 * n) := by
  rw [UInt32.add_comm (4294967288 : UInt32), index_back]

private theorem addr_next (v : UInt32) (n : Nat) :
    (8 : UInt32) + (v + UInt32.ofNat (8 * n))
      = v + UInt32.ofNat (8 * (n + 1)) := by
  rw [UInt32.add_comm (8 : UInt32), addr_succ]

private theorem index_next (n : Nat) :
    (8 : UInt32) + UInt32.ofNat (8 * n)
      = UInt32.ofNat (8 * (n + 1)) := by
  have h := addr_next 0 n
  simpa using h

/-! ## The registers of the small sort -/

/-- The registers that only the two sorting networks write.  The
insertion sort, the guards and the region switch leave every one of
them. -/
structure NetScratch where
  r2 : UInt32
  r3 : UInt32
  r4 : UInt32
  r14 : UInt32
  r19 : UInt64
  r20 : UInt64
  r21 : UInt32
  r22 : UInt32
  r23 : UInt32
  r24 : UInt32
  r25 : UInt64
  r26 : UInt32
  r27 : UInt64
  r28 : UInt32
  r29 : UInt32
  p30 : Value
  p31 : Value
  p32 : Value
  p33 : Value
  p34 : Value
  p35 : Value
  p36 : Value
  p37 : Value
  p38 : Value

/-- The locals of the small sort.  Local 0 is the buffer, local 1 the
length and local 5 the frame pointer; the small sort writes none of the
three. -/
@[reducible] def rLoc (buf len fp : UInt32) (nt : NetScratch)
    (r6 r7 r8 r9 r10 r11 : UInt32) (r12 : UInt64)
    (r13 r15 r16 r17 r18 : UInt32) (values : List Value) : Locals :=
  qsLocals buf len nt.r2 nt.r3 nt.r4
    [.i32 fp, .i32 r6, .i32 r7, .i32 r8, .i32 r9, .i32 r10, .i32 r11,
      .i64 r12, .i32 r13, .i32 nt.r14, .i32 r15, .i32 r16, .i32 r17,
      .i32 r18, .i64 nt.r19, .i64 nt.r20, .i32 nt.r21, .i32 nt.r22,
      .i32 nt.r23, .i32 nt.r24, .i64 nt.r25, .i32 nt.r26, .i64 nt.r27,
      .i32 nt.r28, .i32 nt.r29, nt.p30, nt.p31, nt.p32, nt.p33,
      nt.p34, nt.p35, nt.p36, nt.p37, nt.p38] values

/-- The vocabulary of this module is the vocabulary of the two
networks. -/
private theorem rLoc_net (buf len fp : UInt32) (nt : NetScratch)
    (r6 r7 r8 r9 r10 r11 : UInt32) (r12 : UInt64)
    (r13 r15 r16 r17 r18 : UInt32) (values : List Value) :
    rLoc buf len fp nt r6 r7 r8 r9 r10 r11 r12 r13 r15 r16 r17 r18
        values =
      Func21Network9.netLocals
        ⟨buf, len, fp, r7, r13, .i32 r16, .i32 r17, .i32 r18,
          nt.p30, nt.p31, nt.p32, nt.p33, nt.p34, nt.p35, nt.p36,
          nt.p37, nt.p38⟩
        r8 nt.r2 nt.r3 nt.r4 r6 r9 r10 r11 r12 nt.r14 r15 nt.r19 nt.r20
        nt.r21 nt.r22 nt.r23 nt.r24 nt.r25 nt.r26 nt.r27 nt.r28 nt.r29
        values :=
  rfl


/-! ## The regions of the inlined insertion sort

The five fragments below are the fragments `qsInsertion`,
`qsInsertSetup`, `qsInsertOuter`, `qsInsertCheck`, `qsInsertShiftBlock`
and `qsInsertShift` of `Func21Defs`, written out as instruction lists.
A proof that steps through a loop body needs the list, because the
`Func21Defs` name unfolds to a private extraction that no tactic can
reduce.  Each shape lemma is `rfl`, so the lists carry no new content.
-/

/-- One step of the shift loop, WAT 8433 to 8461. -/
@[reducible] private def shiftBody : Program :=
  [.localGet 8, .localGet 6, .add, .localTee 7, .localGet 7,
    .const 4294967288, .add, .load64 0, .store64 0,
    .block 0 0
      [.localGet 6, .const 8, .ne, .br_if 0, .localGet 8, .localSet 6,
        .br 2],
    .localGet 6, .const 4294967288, .add, .localSet 6, .localGet 9,
    .localGet 7, .const 4294967280, .add, .load32 0, .ltU, .br_if 0]

/-- The search for the hole, WAT 8432 to 8466. -/
@[reducible] private def holeBody : Program :=
  [.loop 0 0 shiftBody, .localGet 8, .localGet 6, .add, .localSet 6]

/-- The write back of the held entry, WAT 8468 to 8475. -/
@[reducible] private def writeBack : Program :=
  [.localGet 6, .localGet 12, .constI64 32, .shlI64, .localGet 9,
    .extendUI32, .orI64, .store64 0]

/-- The compare, the hold and the write back, WAT 8417 to 8475. -/
@[reducible] private def scanBody : Program :=
  .localGet 10 :: .load32 0 :: .localTee 9 :: .localGet 10 ::
    .const 4294967288 :: .add :: .load32 0 :: .geU :: .br_if 0 ::
    .localGet 10 :: .load32UI64 4 :: .localSet 12 :: .localGet 11 ::
    .localSet 6 :: .block 0 0 holeBody :: writeBack

/-- The cursor step and the back edge of the outer loop, WAT 8477 to
8487. -/
@[reducible] private def outerTail : Program :=
  [.localGet 11, .const 8, .add, .localSet 11, .localGet 10, .const 8,
    .add, .localTee 10, .localGet 15, .ne, .br_if 0]

/-- One step of the outer loop, WAT 8416 to 8487. -/
@[reducible] private def outerBody : Program :=
  .block 0 0 scanBody :: outerTail

/-- The whole insertion sort, WAT 8398 to 8488. -/
@[reducible] private def sortBody : Program :=
  [.localGet 6, .localGet 7, .eq, .br_if 0, .localGet 8, .localGet 7,
    .const 3, .shl, .add, .localSet 15, .localGet 8, .localGet 6,
    .const 3, .shl, .localTee 11, .add, .localSet 10,
    .loop 0 0 outerBody]

private theorem sortBody_shape : qsInsertion = sortBody := rfl

/-! ## The write back of the held entry -/

/-- Where the search for the hole leaves the machine: at the end of the
body of the block of WAT 8416, with the region holding the model
insertion.  The two registers that the search overwrites are free. -/
private def holeExit [WasmSmallStepGS hlc Universal.State]
    (buf len fp : UInt32) (nt : NetScratch)
    (rbase r10 r11 r13 r15 r16 r17 r18 : UInt32)
    (held : UInt32 × UInt32) (A post : List (UInt32 × UInt32))
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Phi : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ y6 : UInt32, ∀ y7 : UInt32,
    Table.PairSlice 0 rbase (insertTail held A ++ post) -∗
    WP (.running ⟨rLoc buf len fp nt y6 y7 rbase held.1 r10 r11
          held.2.toUInt64 r13 r15 r16 r17 r18 [],
        [], arity, remainder, controls, calls⟩ :
      Expr Universal.State) @ s; E [{ Phi }])

set_option maxHeartbeats 2000000 in
/-- The write back, WAT 8468 to 8475.  It stores the held entry into the
hole as one `i64`, and that store is the model insertion. -/
private theorem twp_write_back [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {rbase r6 r7 r10 r11 r13 r15 r16 r17 r18 : UInt32}
    {A post : List (UInt32 × UInt32)} {held : UInt32 × UInt32}
    {k j : Nat} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hr6 : r6 = rbase + UInt32.ofNat (8 * k))
    (hlen : A.length = j) (hk : k ≤ j)
    (hroom : rbase.toNat + 8 * (j + 1) < UInt32.size)
    (hbelow : ∀ m, m < k → ¬ (held.1 < keyAt A m))
    (habove : k < j → held.1 < keyAt A k) :
    iprop(
      (∃ a : UInt32 × UInt32,
        Table.PairSlice 0 rbase
          (A.take k ++ a :: (A.drop k ++ post))) ∗
      holeExit buf len fp nt rbase r10 r11 r13 r15 r16 r17 r18 held A
        post arity remainder controls calls s E Φ) ⊢
      WP (.running ⟨rLoc buf len fp nt r6 r7 rbase held.1 r10 r11
            held.2.toUInt64 r13 r15 r16 r17 r18 [],
          writeBack, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst hr6
  iintro ⟨Hslice, Hexit⟩
  icases Hslice with ⟨%a, Hslice⟩
  have hklen : (A.take k).length = k := take_length_eq (by omega)
  have hword : held.2.toUInt64 <<< ((32 : UInt64) % 64)
      ||| UInt64.ofNat held.1.toNat = Table.pairWord held := by
    rw [shift_count, extendU_eq, ← pairWord_eq_shl_or]
  have hfacts := cell_facts64 rbase k (j + 1) (by omega) hroom
  have hfinal : A.take k ++ held :: (A.drop k ++ post)
      = insertTail held A ++ post := by
    rw [insertTail_eq_of_split held A k (by omega) hbelow
      (by rw [hlen]; exact habove)]
    simp
  isimp only [writeBack, rLoc, qsLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_constI64 twp_shlI64
    twp_localGet twp_extendUI32 twp_orI64]
  isimp only [hword]
  ihave ⟨Hcell, Hclose⟩ :=
    slice_focus rbase (A.take k) a (A.drop k ++ post) k hklen $$ Hslice
  ihave Hcell := wordMove64 (UInt32.add_zero _).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store64
    (address := rbase + UInt32.ofNat (8 * k)) (offset := 0)
    (Table.pairWord a) hfacts.1 hfacts.2.1 hfacts.2.2.1
    hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _) $$ Hcell
  ihave Hslice := Hclose $$ %held Hcell
  isimp only [hfinal] at Hslice
  isimp only [holeExit] at Hexit
  ihave Hgo := Hexit $$ %(rbase + UInt32.ofNat (8 * k)) %r7 Hslice
  iexact Hgo

/-! ## The search for the hole -/

/-- Open the entry just below a prefix of length `i + 1`. -/
private theorem key_split (A tail : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < A.length) :
    A.take (i + 1) ++ tail = A.take i ++ entryAt A i :: tail := by
  rw [take_succ_eq A hi]
  simp

/-- The hole at `i` holds a stale copy of entry `i`. -/
private theorem hole_split (A post : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < A.length) :
    A.take i ++ entryAt A i :: (A.drop i ++ post)
      = A.take i ++ entryAt A i :: entryAt A i ::
          (A.drop (i + 1) ++ post) := by
  rw [drop_eq_cons A hi]
  simp

set_option maxHeartbeats 2000000 in
/-- The search for the hole and the write back, WAT 8431 to 8475.  The
shift loop moves one entry up per step and stops at the front or at the
first entry whose key is not above the held key.  Both stops reach the
write back, which puts the held entry into the hole. -/
private theorem twp_hole [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {rbase r7 r10 r11 r13 r15 r16 r17 r18 : UInt32}
    {A post : List (UInt32 × UInt32)} {held : UInt32 × UInt32} {j : Nat}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : A.length = j) (hj1 : 1 ≤ j)
    (hroom : rbase.toNat + 8 * (j + 1) < UInt32.size)
    (hsorted : Table.SortedByKey A)
    (hentry : held.1 < keyAt A (j - 1)) :
    iprop(
      Table.PairSlice 0 rbase (A ++ held :: post) ∗
      holeExit buf len fp nt rbase r10 r11 r13 r15 r16 r17 r18 held A
        post arity remainder controls calls s E Φ) ⊢
      WP (.running ⟨rLoc buf len fp nt (UInt32.ofNat (8 * j)) r7 rbase
            held.1 r10 r11 held.2.toUInt64 r13 r15 r16 r17 r18 [],
          .block 0 0 holeBody :: writeBack, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hexit⟩
  wasm_twp_pures [twp_block]
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := Nat × UInt32)
    (measure := fun p => p.1)
    (locals := fun p => rLoc buf len fp nt (UInt32.ofNat (8 * p.1)) p.2
      rbase held.1 r10 r11 held.2.toUInt64 r13 r15 r16 r17 r18 [])
    (I := fun p => iprop(
      ⌜1 ≤ p.1 ∧ p.1 ≤ j ∧
        ∀ m, p.1 ≤ m + 1 → m < j → held.1 < keyAt A m⌝ ∗
      (∃ a : UInt32 × UInt32,
        Table.PairSlice 0 rbase
          (A.take p.1 ++ a :: (A.drop p.1 ++ post))) ∗
      holeExit buf len fp nt rbase r10 r11 r13 r15 r16 r17 r18 held A
        post arity remainder controls calls s E Φ))
    (initial := (j, r7))
    (initialLocals := rLoc buf len fp nt (UInt32.ofNat (8 * j)) r7 rbase
      held.1 r10 r11 held.2.toUInt64 r13 r15 r16 r17 r18 [])
    rfl rfl
  · intro p
    obtain ⟨i, rr⟩ := p
    iintro Hrec ⟨%hinv, Hbuf, Hexit⟩
    obtain ⟨hi1, hij, hhist⟩ := hinv
    replace hi1 : 1 ≤ i := hi1
    replace hij : i ≤ j := hij
    replace hhist : ∀ m, i ≤ m + 1 → m < j → held.1 < keyAt A m := hhist
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    icases Hbuf with ⟨%a, Hbuf⟩
    have hi'A : i' < A.length := by omega
    have hpre : (A.take i').length = i' := take_length_eq (by omega)
    isimp only [key_split A (a :: (A.drop (i' + 1) ++ post)) hi'A]
      at Hbuf
    ihave ⟨Hlow, Hhigh, Hclose⟩ :=
      slice_two rbase (A.take i') (entryAt A i') a
        (A.drop (i' + 1) ++ post) i' hpre $$ Hbuf
    have hlowf := cell_facts64 rbase i' (j + 1) (by omega) hroom
    have hhighf := cell_facts64 rbase (i' + 1) (j + 1) (by omega) hroom
    simp only [Wasm.SmallStep.loopBodyExpr, shiftBody, rLoc, qsLocals]
    wasm_twp_pures [twp_localGet twp_localGet twp_add]
    isimp only [show UInt32.ofNat (8 * (i' + 1)) + rbase
      = rbase + UInt32.ofNat (8 * (i' + 1)) from UInt32.add_comm _ _]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    isimp only [addr_prev]
    ihave Hlow := wordMove64 (UInt32.add_zero _).symm $$ Hlow
    wasm_twp_rebind Wasm.SmallStep.twp_load64
      (address := rbase + UInt32.ofNat (8 * i')) (offset := 0)
      (Table.pairWord (entryAt A i')) hlowf.1 hlowf.2.1 hlowf.2.2.1
      hlowf.2.2.2.1 hlowf.2.2.2.2.1 hlowf.2.2.2.2.2.1
      hlowf.2.2.2.2.2.2.1 hlowf.2.2.2.2.2.2.2 with Hlow
    ihave Hhigh := wordMove64 (UInt32.add_zero _).symm $$ Hhigh
    wasm_twp_rebind Wasm.SmallStep.twp_store64
      (address := rbase + UInt32.ofNat (8 * (i' + 1))) (offset := 0)
      (Table.pairWord a) hhighf.1 hhighf.2.1 hhighf.2.2.1
      hhighf.2.2.2.1 hhighf.2.2.2.2.1 hhighf.2.2.2.2.2.1
      hhighf.2.2.2.2.2.2.1 hhighf.2.2.2.2.2.2.2 with Hhigh
    ihave Hlow := wordMove64 (UInt32.add_zero _) $$ Hlow
    ihave Hhigh := wordMove64 (UInt32.add_zero _) $$ Hhigh
    ihave Hbuf := Hclose $$ %(entryAt A i') %(entryAt A i') Hlow Hhigh
    isimp only [← hole_split A post hi'A] at Hbuf
    wasm_twp_pures [twp_block twp_localGet twp_const]
    match i', hi'A with
    | 0, hi'A =>
      iapply Wasm.SmallStep.twp_ne (result := 0) (by decide)
      iapply Wasm.SmallStep.twp_brIfZero
      wasm_twp_pures [twp_localGet]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply Wasm.SmallStep.twp_br rfl
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      iapply twp_write_back (k := 0) (j := j) (by simp) hlen
        (Nat.zero_le j) hroom
        (by intro m hm; exact absurd hm (Nat.not_lt_zero m))
        (by intro _; exact hhist 0 (by omega) (by omega))
      isplitl [Hbuf]
      · iexists entryAt A 0
        isimp only [List.take_zero, List.drop_zero, List.nil_append]
        iexact Hbuf
      · iexact Hexit
    | i'' + 1, hi'A =>
      have hne : UInt32.ofNat (8 * (i'' + 1 + 1)) ≠ (8 : UInt32) := by
        intro hc
        have h1 := congrArg UInt32.toNat hc
        rw [UInt32.toNat_ofNat_of_lt' (by omega),
          show (8 : UInt32).toNat = 8 from rfl] at h1
        omega
      iapply Wasm.SmallStep.twp_ne (result := 1) (by rw [if_pos hne])
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      isimp only [index_prev]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
      isimp only [addr_prev_two]
      have hi''A : i'' < A.length := by omega
      have hpre2 : (A.take i'').length = i'' :=
        take_length_eq (by omega)
      isimp only [key_split A (entryAt A (i'' + 1) ::
        (A.drop (i'' + 1) ++ post)) hi''A] at Hbuf
      ihave ⟨Hkey, Hclosek⟩ :=
        slice_key rbase (A.take i'') (entryAt A i'')
          (entryAt A (i'' + 1) :: (A.drop (i'' + 1) ++ post))
          i'' hpre2 $$ Hbuf
      have hkf := cell_facts32 rbase i'' (j + 1) (by omega) hroom
      wasm_twp_rebind Wasm.SmallStep.twp_load32_addr
        (entryAt A i'').1 hkf.1 hkf.2.1 hkf.2.2 with Hkey
      ihave Hbuf := Hclosek $$ Hkey
      isimp only [← key_split A (entryAt A (i'' + 1) ::
        (A.drop (i'' + 1) ++ post)) hi''A] at Hbuf
      by_cases hcmp : held.1 < keyAt A i''
      · iapply Wasm.SmallStep.twp_ltU (result := 1)
          (by rw [if_pos (by rw [← keyAt_entryAt]; exact hcmp)])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
          rfl
        simp only [List.take_zero, List.nil_append]
        ihave Hback := Hrec
          $$ %((i'' + 1, rbase + UInt32.ofNat (8 * (i'' + 1 + 1))) :
              Nat × UInt32)
          %(show i'' + 1 < i'' + 1 + 1 by omega)
        iapply Hback
        have hnext : 1 ≤ i'' + 1 ∧ i'' + 1 ≤ j ∧
            ∀ m, i'' + 1 ≤ m + 1 → m < j → held.1 < keyAt A m := by
          refine ⟨by omega, by omega, ?_⟩
          intro m hm1 hm2
          rcases Nat.lt_or_ge m (i'' + 1) with hlt | hge
          · have hmeq : m = i'' := by omega
            subst hmeq
            exact hcmp
          · exact hhist m (by omega) hm2
        isplitl_pureexact hnext
        · isplitl [Hbuf]
          · iexists entryAt A (i'' + 1)
            iexact Hbuf
          · iexact Hexit
      · iapply Wasm.SmallStep.twp_ltU (result := 0)
          (by rw [if_neg (by rw [← keyAt_entryAt]; exact hcmp)])
        iapply Wasm.SmallStep.twp_brIfZero
        wasm_twp_pures [twp_exitControl twp_localGet twp_localGet
          twp_add]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_exitControl]
        simp only [List.take_zero, List.nil_append]
        have hbelow : ∀ m, m < i'' + 1 → ¬ (held.1 < keyAt A m) := by
          intro m hm
          have hle : keyAt A m ≤ keyAt A i'' :=
            keyAt_mono hsorted (show m ≤ i'' by omega)
              (show i'' < A.length by omega)
          have hup : keyAt A i'' ≤ held.1 := UInt32.not_lt.mp hcmp
          exact UInt32.not_lt.mpr (UInt32.le_trans hle hup)
        iapply twp_write_back (k := i'' + 1) (j := j)
          (UInt32.add_comm _ _) hlen (by omega) hroom hbelow
          (fun _ => hhist (i'' + 1) (by omega) (by omega))
        isplitl [Hbuf]
        · iexists entryAt A (i'' + 1)
          iexact Hbuf
        · iexact Hexit
  · have hinit : 1 ≤ j ∧ j ≤ j ∧
        ∀ m, j ≤ m + 1 → m < j → held.1 < keyAt A m := by
      refine ⟨hj1, Nat.le_refl j, ?_⟩
      intro m hm1 hm2
      have hmeq : m = j - 1 := by omega
      subst hmeq
      exact hentry
    have hstart : A.take j ++ held :: (A.drop j ++ post)
        = A ++ held :: post := by
      rw [List.take_of_length_le (by omega),
        List.drop_of_length_le (by omega)]
      simp
    isplitl_pureexact hinit
    · isplitl [Hbuf]
      · iexists held
        isimp only [hstart]
        iexact Hbuf
      · iexact Hexit


/-! ## One step of the outer loop -/

set_option maxHeartbeats 2000000 in
/-- The compare, the hold and the write back, WAT 8417 to 8475.  The
entry above the sorted prefix either stays where it is, when its key is
not below its left neighbour, or moves down into the prefix.  Both arms
leave the block of WAT 8416 with the prefix holding the model
insertion. -/
private theorem twp_scan [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {rbase r6 r7 r9 r13 r15 r16 r17 r18 : UInt32} {r12 : UInt64}
    {A post : List (UInt32 × UInt32)} {held : UInt32 × UInt32} {j : Nat}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : A.length = j) (hj1 : 1 ≤ j)
    (hroom : rbase.toNat + 8 * (j + 1) < UInt32.size)
    (hsorted : Table.SortedByKey A) :
    iprop(
      Table.PairSlice 0 rbase (A ++ held :: post) ∗
      (∀ y6 : UInt32, ∀ y7 : UInt32, ∀ y9 : UInt32, ∀ y12 : UInt64,
        Table.PairSlice 0 rbase (insertTail held A ++ post) -∗
        WP (.running ⟨rLoc buf len fp nt y6 y7 rbase y9
              (rbase + UInt32.ofNat (8 * j)) (UInt32.ofNat (8 * j)) y12
              r13 r15 r16 r17 r18 [],
            outerTail, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨rLoc buf len fp nt r6 r7 rbase r9
            (rbase + UInt32.ofNat (8 * j)) (UInt32.ofNat (8 * j)) r12
            r13 r15 r16 r17 r18 [],
          .block 0 0 scanBody :: outerTail, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hexit⟩
  obtain ⟨j0, rfl⟩ : ∃ j0, j = j0 + 1 := ⟨j - 1, by omega⟩
  have hj0A : j0 < A.length := by omega
  have hpre0 : (A.take j0).length = j0 := take_length_eq (by omega)
  have hcell := cell_facts32 rbase (j0 + 1) (j0 + 1 + 1) (by omega)
    hroom
  have hcell0 := cell_facts32 rbase j0 (j0 + 1 + 1) (by omega) hroom
  have hval := value_facts rbase (j0 + 1) (j0 + 1 + 1) (by omega) hroom
  have hsplit0 : A ++ held :: post
      = A.take j0 ++ entryAt A j0 :: (held :: post) := by
    have h := key_split A (held :: post) hj0A
    rwa [List.take_of_length_le (show A.length ≤ j0 + 1 by omega)] at h
  isimp only [rLoc, qsLocals] at Hexit
  simp only [scanBody, rLoc, qsLocals]
  wasm_twp_pures [twp_block twp_localGet]
  ihave ⟨Hkey, Hclosek⟩ :=
    slice_key rbase A held post (j0 + 1) hlen $$ Hbuf
  wasm_twp_rebind Wasm.SmallStep.twp_load32_addr held.1
    hcell.1 hcell.2.1 hcell.2.2 with Hkey
  ihave Hbuf := Hclosek $$ Hkey
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [addr_prev]
  isimp only [hsplit0] at Hbuf
  ihave ⟨Hkey0, Hclose0⟩ :=
    slice_key rbase (A.take j0) (entryAt A j0) (held :: post) j0 hpre0
      $$ Hbuf
  wasm_twp_rebind Wasm.SmallStep.twp_load32_addr (entryAt A j0).1
    hcell0.1 hcell0.2.1 hcell0.2.2 with Hkey0
  ihave Hbuf := Hclose0 $$ Hkey0
  isimp only [← hsplit0] at Hbuf
  by_cases hcmp : held.1 < keyAt A j0
  · iapply Wasm.SmallStep.twp_geU (result := 0)
      (by
        rw [if_neg (show ¬ (held.1 ≥ (entryAt A j0).1) from
          fun hge => absurd hcmp (UInt32.not_lt.mpr hge))])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet]
    ihave ⟨Hval, Hclosev⟩ :=
      slice_value rbase A held post (j0 + 1) hlen $$ Hbuf
    wasm_twp_rebind Wasm.SmallStep.twp_load32UI64
      (address := rbase + UInt32.ofNat (8 * (j0 + 1))) (offset := 4)
      held.2 hval.1 hval.2.1 hval.2.2.1 hval.2.2.2 with Hval
    ihave Hbuf := Hclosev $$ Hval
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_hole hlen hj1 hroom hsorted (by simpa using hcmp)
    isplitl [Hbuf]
    · iexact Hbuf
    · isimp only [holeExit, rLoc, qsLocals]
      iintro %y6 %y7 Hdone
      wasm_twp_pures [twp_exitControl]
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      ihave Hgo := Hexit $$ %y6 %y7 %held.1 %held.2.toUInt64 Hdone
      iexact Hgo
  · iapply Wasm.SmallStep.twp_geU (result := 1)
      (by
        rw [if_pos (show held.1 ≥ (entryAt A j0).1 from
          UInt32.not_lt.mp hcmp)])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    have hbelow : ∀ m, m < A.length → ¬ (held.1 < keyAt A m) := by
      intro m hm
      have hle : keyAt A m ≤ keyAt A j0 :=
        keyAt_mono hsorted (show m ≤ j0 by omega)
          (show j0 < A.length by omega)
      exact UInt32.not_lt.mpr
        (UInt32.le_trans hle (UInt32.not_lt.mp hcmp))
    have hins : insertTail held A ++ post = A ++ held :: post := by
      rw [insertTail_eq_of_split held A A.length (Nat.le_refl _) hbelow
        (fun h => absurd h (Nat.lt_irrefl _))]
      simp
    isimp only [← hins] at Hbuf
    ihave Hgo := Hexit $$ %r6 %r7 %held.1 %r12 Hbuf
    iexact Hgo

/-! ## The whole insertion sort of one region -/

/-- The model of an insertion sort whose offset is the whole length. -/
private theorem insertionShiftLeft_self (R : List (UInt32 × UInt32))
    {k : Nat} (hk : R.length ≤ k) : insertionShiftLeft R k = R := by
  rw [insertionShiftLeft, List.drop_of_length_le hk,
    List.take_of_length_le hk]
  rfl

/-- A small index is what it says. -/
private theorem ofNat_toNat {m : Nat} (hm : m < UInt32.size) :
    (UInt32.ofNat m).toNat = m := UInt32.toNat_ofNat_of_lt' hm

/-- Two small indexes are equal exactly when their words are. -/
private theorem ofNat_inj {a b : Nat} (ha : a < UInt32.size)
    (hb : b < UInt32.size)
    (h : (UInt32.ofNat a : UInt32) = UInt32.ofNat b) : a = b := by
  have hc := congrArg UInt32.toNat h
  rwa [ofNat_toNat ha, ofNat_toNat hb] at hc

/-- `i32.shl` of a small index by three. -/
private theorem ofNat_shl (m : Nat) (hm : 8 * m < UInt32.size) :
    (UInt32.ofNat m : UInt32) <<< (3 : UInt32)
      = UInt32.ofNat (8 * m) := by
  have hto : (UInt32.ofNat m : UInt32).toNat = m :=
    ofNat_toNat (by omega)
  rw [shift_three _ (by rw [hto]; omega), hto]

set_option maxHeartbeats 2000000 in
/-- The insertion sort of one region, WAT 8397 to 8489.  The first `k`
entries of the region are already in key order, and the loop puts each
later entry into place.  The region switch of WAT 8490 follows. -/
theorem twp_region_insertion [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {rbase r6 r7 r9 r10 r11 r13 r15 r16 r17 r18 : UInt32}
    {r12 : UInt64} {R : List (UInt32 × UInt32)} {n k : Nat}
    {Rest : HeapIProp} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : R.length = n) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 32)
    (hsorted : Table.SortedByKey (R.take k))
    (hroom : rbase.toNat + 8 * n < UInt32.size)
    (h6 : r6 = UInt32.ofNat k) (h7 : r7 = UInt32.ofNat n)
    (hcont : ∀ (y6 y7 y9 y10 y11 : UInt32) (y12 : UInt64)
        (y15 : UInt32),
      iprop(Table.PairSlice 0 rbase (insertionShiftLeft R k) ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt y6 y7 rbase y9 y10 y11 y12 r13
            y15 r16 r17 r18 [], qsRegionNext, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 rbase R ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt r6 r7 rbase r9 r10 r11 r12 r13
            r15 r16 r17 r18 [],
          .block 0 0 qsInsertion :: qsRegionNext, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  subst h6
  subst h7
  have hsz : UInt32.size = 4294967296 := rfl
  iintro ⟨Hbuf, HRest⟩
  rw [sortBody_shape]
  simp only [sortBody, rLoc, qsLocals]
  wasm_twp_pures [twp_block twp_localGet twp_localGet]
  by_cases hkeq : k = n
  · -- WAT 8400 and 8401: the region is already in key order
    subst hkeq
    iapply Wasm.SmallStep.twp_eq (result := 1) (by rw [if_pos rfl])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    have hid : insertionShiftLeft R k = R :=
      insertionShiftLeft_self R (by omega)
    iapply (hcont (UInt32.ofNat k) (UInt32.ofNat k) r9 r10 r11 r12 r15)
    isimp only [hid]
    isplitl [Hbuf]
    · iexact Hbuf
    · iexact HRest
  · -- WAT 8402 to 8488: the cursor set-up and the outer loop
    iapply Wasm.SmallStep.twp_eq (result := 0)
      (by rw [if_neg (fun hc => hkeq (ofNat_inj (by omega) (by omega)
        hc))])
    iapply Wasm.SmallStep.twp_brIfZero
    have hkn' : k < n := by omega
    have hnshl : (UInt32.ofNat n : UInt32) <<< (3 : UInt32)
        = UInt32.ofNat (8 * n) := ofNat_shl n (by omega)
    have hkshl : (UInt32.ofNat k : UInt32) <<< (3 : UInt32)
        = UInt32.ofNat (8 * k) := ofNat_shl k (by omega)
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
    isimp only [shl_three, hnshl]
    wasm_twp_pures [twp_add]
    isimp only [show UInt32.ofNat (8 * n) + rbase
      = rbase + UInt32.ofNat (8 * n) from UInt32.add_comm _ _]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
    isimp only [shl_three, hkshl]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_add]
    isimp only [show UInt32.ofNat (8 * k) + rbase
      = rbase + UInt32.ofNat (8 * k) from UInt32.add_comm _ _]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_loop_wf_family
      (ι := Nat × UInt32 × UInt32 × UInt32 × UInt64)
      (measure := fun p => n - p.1)
      (locals := fun p => rLoc buf len fp nt p.2.1 p.2.2.1 rbase
        p.2.2.2.1 (rbase + UInt32.ofNat (8 * p.1))
        (UInt32.ofNat (8 * p.1)) p.2.2.2.2 r13
        (rbase + UInt32.ofNat (8 * n)) r16 r17 r18 [])
      (I := fun p => iprop(
        ⌜k ≤ p.1 ∧ p.1 < n⌝ ∗
        Table.PairSlice 0 rbase
          (outerAcc R k p.1 ++ R.drop p.1) ∗ Rest))
      (initial := (k, UInt32.ofNat k, UInt32.ofNat n, r9, r12))
      (initialLocals := rLoc buf len fp nt (UInt32.ofNat k)
        (UInt32.ofNat n) rbase r9 (rbase + UInt32.ofNat (8 * k))
        (UInt32.ofNat (8 * k)) r12 r13 (rbase + UInt32.ofNat (8 * n))
        r16 r17 r18 [])
      rfl rfl
    · intro p
      obtain ⟨jj, q6, q7, q9, q12⟩ := p
      iintro Hrec ⟨%hinv, Hbuf, HRest⟩
      obtain ⟨hkj, hjn⟩ := hinv
      replace hkj : k ≤ jj := hkj
      replace hjn : jj < n := hjn
      obtain ⟨A, hAdef⟩ : ∃ A, outerAcc R k jj = A := ⟨_, rfl⟩
      have hAlen : A.length = jj := by
        rw [← hAdef]
        exact outerAcc_length R hkj (by omega)
      have hAsorted : Table.SortedByKey A := by
        rw [← hAdef]
        exact outerAcc_sorted R hsorted
      have hdrop : R.drop jj = entryAt R jj :: R.drop (jj + 1) :=
        drop_eq_cons R (by omega)
      isimp only [hAdef, hdrop] at Hbuf
      simp only [Wasm.SmallStep.loopBodyExpr, outerBody]
      iapply twp_scan hAlen (by omega) (by omega) hAsorted
      isplitl [Hbuf]
      · iexact Hbuf
      · iintro %y6 %y7 %y9 %y12 Hdone
        have hstep : outerAcc R k (jj + 1) ++ R.drop (jj + 1)
            = insertTail (entryAt R jj) A ++ R.drop (jj + 1) := by
          rw [outerAcc_succ R hkj (by omega), hAdef]
        isimp only [← hstep] at Hdone
        simp only [outerTail, rLoc, qsLocals]
        wasm_twp_pures [twp_localGet twp_const twp_add]
        isimp only [index_next]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet twp_const twp_add]
        isimp only [addr_next]
        wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet]
        by_cases hlast : jj + 1 = n
        · -- WAT 8487: the cursor met the end pointer
          iapply Wasm.SmallStep.twp_ne (result := 0)
            (by rw [if_neg (by rw [hlast]; exact fun h => h rfl)])
          iapply Wasm.SmallStep.twp_brIfZero
          wasm_twp_pures [twp_exitControl]
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          wasm_twp_pures [twp_exitControl]
          simp only [List.take_zero, List.nil_append]
          have hfin : outerAcc R k (jj + 1) ++ R.drop (jj + 1)
              = insertionShiftLeft R k := by
            rw [hlast, ← hlen, outerAcc_full,
              List.drop_of_length_le (Nat.le_refl _)]
            simp
          isimp only [hfin] at Hdone
          iapply (hcont y6 y7 y9 (rbase + UInt32.ofNat (8 * (jj + 1)))
            (UInt32.ofNat (8 * (jj + 1))) y12
            (rbase + UInt32.ofNat (8 * n)))
          isplitl [Hdone]
          · iexact Hdone
          · iexact HRest
        · -- WAT 8486: one more entry to place
          have hne : rbase + UInt32.ofNat (8 * (jj + 1))
              ≠ rbase + UInt32.ofNat (8 * n) := by
            intro hc
            have h1 := congrArg UInt32.toNat hc
            rw [Slices.byteOffset_toNat rbase (8 * (jj + 1))
                (by omega),
              Slices.byteOffset_toNat rbase (8 * n) (by omega)] at h1
            omega
          iapply Wasm.SmallStep.twp_ne (result := 1)
            (by rw [if_pos hne])
          iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
            rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          ihave Hback := Hrec
            $$ %((jj + 1, y6, y7, y9, y12) :
                Nat × UInt32 × UInt32 × UInt32 × UInt64)
            %(show n - (jj + 1) < n - jj by omega)
          iapply Hback
          isplitl_pureexact (⟨by omega, by omega⟩ :
            k ≤ jj + 1 ∧ jj + 1 < n)
          · isplitl [Hdone]
            · iexact Hdone
            · iexact HRest
    · have hstart : outerAcc R k k ++ R.drop k = R := by
        rw [outerAcc_self, List.take_append_drop]
      isplitl_pureexact (⟨Nat.le_refl k, hkn'⟩ : k ≤ k ∧ k < n)
      · isplitl [Hbuf]
        · isimp only [hstart]
          iexact Hbuf
        · iexact HRest


/-! ## The order test and the insertion sort, WAT 8393 to 8489 -/

/-- Two small indexes compare as their numbers do. -/
private theorem ofNat_le {a b : Nat} (ha : a < UInt32.size)
    (hb : b < UInt32.size) (h : a ≤ b) :
    (UInt32.ofNat a : UInt32) ≤ UInt32.ofNat b := by
  rw [UInt32.le_iff_toNat_le, ofNat_toNat ha, ofNat_toNat hb]
  exact h

private theorem ofNat_lt {a b : Nat} (ha : a < UInt32.size)
    (hb : b < UInt32.size) (h : a < b) :
    (UInt32.ofNat a : UInt32) < UInt32.ofNat b := by
  rw [UInt32.lt_iff_toNat_lt, ofNat_toNat ha, ofNat_toNat hb]
  exact h

set_option maxHeartbeats 2000000 in
/-- The order test and the insertion sort, WAT 8393 to 8489.  The test
of WAT 8393 to 8396 is dead, because the offset of the insertion sort
never passes the region length. -/
private theorem twp_after_region [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {rbase r9 r10 r11 r13 r15 r16 r17 r18 : UInt32} {r12 : UInt64}
    {R : List (UInt32 × UInt32)} {n k : Nat}
    {Rest : HeapIProp} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : R.length = n) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hn : n ≤ 32)
    (hsorted : Table.SortedByKey (R.take k))
    (hroom : rbase.toNat + 8 * n < UInt32.size)
    (hcont : ∀ (y6 y7 y9 y10 y11 : UInt32) (y12 : UInt64)
        (y15 : UInt32),
      iprop(Table.PairSlice 0 rbase (insertionShiftLeft R k) ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt y6 y7 rbase y9 y10 y11 y12 r13
            y15 r16 r17 r18 [], qsRegionNext, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 rbase R ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt (UInt32.ofNat k)
            (UInt32.ofNat n) rbase r9 r10 r11 r12 r13 r15 r16 r17 r18
            [], qsAfterRegionBody, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  rw [qsAfterRegionBody_split, qsRegionOrder_shape]
  simp only [List.cons_append, List.nil_append]
  iintro ⟨Hbuf, HRest⟩
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply Wasm.SmallStep.twp_gtU (result := 0)
    (by
      rw [if_neg (show ¬ ((UInt32.ofNat k : UInt32)
          > UInt32.ofNat n) from
        UInt32.not_lt.mpr
          (ofNat_le (a := k) (b := n) (by omega) (by omega) hkn))])
  iapply Wasm.SmallStep.twp_brIfZero
  iapply twp_region_insertion (nt := nt) (R := R) (n := n) (k := k)
    hlen hk1 hkn hn hsorted hroom rfl rfl hcont
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

/-! ## The output of one sorting network -/

/-- The four facts about a region whose first `k` entries went through a
sorting network that sorts `k` entries. -/
private theorem netOut_facts {R : List (UInt32 × UInt32)} {n k : Nat}
    {net : List Table.Comparator}
    (hlen : R.length = n) (hk : k ≤ n)
    (hnet : Table.sortsAll net k) :
    (Table.applyNetwork keyLt net (R.take k) ++ R.drop k).length = n ∧
      (Table.applyNetwork keyLt net (R.take k) ++ R.drop k).take k
        = Table.applyNetwork keyLt net (R.take k) ∧
      (Table.applyNetwork keyLt net (R.take k) ++ R.drop k).Perm R ∧
      Table.SortedByKey (Table.applyNetwork keyLt net (R.take k)) := by
  have htk : (R.take k).length = k := take_length_eq (by omega)
  have hnl : (Table.applyNetwork keyLt net (R.take k)).length = k := by
    rw [Table.applyNetwork_length]; exact htk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.length_append, hnl, List.length_drop, hlen]
    omega
  · have h : (Table.applyNetwork keyLt net (R.take k) ++ R.drop k).take
        (Table.applyNetwork keyLt net (R.take k)).length
        = Table.applyNetwork keyLt net (R.take k) := List.take_left
    rwa [hnl] at h
  · have h := (Table.applyNetwork_perm keyLt net (R.take k)).append_right
      (R.drop k)
    rwa [List.take_append_drop] at h
  · rw [Func21Network9.keyLt_eq]
    exact Table.applyNetwork_pairs_sorted hnet (R.take k) htk

/-! ## The two network arms

An arm lemma carries its continuation as a resource, not as a Lean
hypothesis, because the continuation names the two block frames that the
region loop pushes and only the machine state holds those.
-/

/-- Where a network arm leaves the machine.  The network writes local 6,
so `v6` is the offset that the insertion sort then starts from, and it
writes every register of `NetScratch`. -/
private def armExit [WasmSmallStepGS hlc Universal.State]
    (buf len fp : UInt32) (rbase v6 r7 r13 r16 r17 r18 : UInt32)
    (Rout : List (UInt32 × UInt32)) (Rest : HeapIProp) (rest : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Phi : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ nt' : NetScratch, ∀ y9 : UInt32, ∀ y10 : UInt32,
    ∀ y11 : UInt32, ∀ y12 : UInt64, ∀ y15 : UInt32,
    Table.PairSlice 0 rbase Rout ∗ Rest -∗
    WP (.running ⟨rLoc buf len fp nt' v6 r7 rbase y9 y10 y11 y12 r13
          y15 r16 r17 r18 [], rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Phi }])

set_option maxHeartbeats 2000000 in
/-- The nine-entry network, WAT 6233 to 7008.  It runs on the first nine
entries of the region and leaves the rest of the region alone. -/
private theorem twp_arm9 [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {rbase r6 r7 r9 r10 r11 r13 r15 r16 r17 r18 : UInt32}
    {r12 : UInt64} {R : List (UInt32 × UInt32)} {n : Nat}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : R.length = n) (h9 : 9 ≤ n) (hn : n ≤ 32)
    (hroom : rbase.toNat + 8 * n < UInt32.size) :
    iprop(Table.PairSlice 0 rbase R ∗ Rest ∗
      armExit buf len fp rbase 9 r7 r13 r16 r17 r18
        (Table.applyNetwork keyLt Table.sort9Net (R.take 9)
          ++ R.drop 9) Rest rest arity remainder controls calls
        s E Φ) ⊢
      WP (.running ⟨rLoc buf len fp nt r6 r7 rbase r9 r10 r11 r12 r13
            r15 r16 r17 r18 [], qsSort9 ++ rest, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hM9 : (R.take 9).length = 9 := take_length_eq (by omega)
  have hroom9 : rbase.toNat + 72 < UInt32.size := by omega
  have hjoin2 := slice_join rbase
    (Table.applyNetwork keyLt Table.sort9Net (R.take 9)) (R.drop 9)
    (m := 9) (by rw [Table.applyNetwork_length]; exact hM9)
  have hcont9 : ∀ (y2 y3 y4 y9 y10 y11 y14 y15 y21 y22 y23 y24 y26 y28
        y29 : UInt32) (y12 y19 y20 y25 y27 : UInt64),
      iprop(Table.PairSlice 0 rbase
          (Table.applyNetwork keyLt Table.sort9Net (R.take 9)) ∗
        (Table.PairSlice 0 (rbase + UInt32.ofNat (8 * 9)) (R.drop 9) ∗
          Rest ∗
          armExit buf len fp rbase 9 r7 r13 r16 r17 r18
            (Table.applyNetwork keyLt Table.sort9Net (R.take 9)
              ++ R.drop 9) Rest rest arity remainder controls calls
            s E Φ)) ⊢
      WP (.running ⟨Func21Network9.netLocals
            ⟨buf, len, fp, r7, r13, .i32 r16, .i32 r17, .i32 r18,
              nt.p30, nt.p31, nt.p32, nt.p33, nt.p34, nt.p35, nt.p36,
              nt.p37, nt.p38⟩
            rbase y2 y3 y4 9 y9 y10 y11 y12 y14 y15 y19 y20 y21 y22
            y23 y24 y25 y26 y27 y28 y29 [], rest, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
    intro y2 y3 y4 y9 y10 y11 y14 y15 y21 y22 y23 y24 y26 y28 y29 y12
      y19 y20 y25 y27
    iintro ⟨HN, Hhi, HRest, Hexit⟩
    isimp only [armExit] at Hexit
    ihave Hgo := Hexit
      $$ %(⟨y2, y3, y4, y14, y19, y20, y21, y22, y23, y24, y25, y26,
          y27, y28, y29, nt.p30, nt.p31, nt.p32, nt.p33, nt.p34,
          nt.p35, nt.p36, nt.p37, nt.p38⟩ : NetScratch)
      %y9 %y10 %y11 %y12 %y15
    iapply Hgo
    isplitl [HN Hhi]
    · iapply hjoin2.mpr
      isplitl [HN]
      · iexact HN
      · iexact Hhi
    · iexact HRest
  iintro ⟨Hbuf, HRest, Hexit⟩
  icases (Table.PairSlice_split 0 rbase R 9 (by omega)).mp $$ Hbuf
    with ⟨Hlow, Hhigh⟩
  rw [rLoc_net]
  iapply Func21Network9.twp_sort9
    (f := ⟨buf, len, fp, r7, r13, .i32 r16, .i32 r17, .i32 r18,
      nt.p30, nt.p31, nt.p32, nt.p33, nt.p34, nt.p35, nt.p36, nt.p37,
      nt.p38⟩)
    (M := R.take 9)
    (N := Table.applyNetwork keyLt Table.sort9Net (R.take 9))
    (Rest := iprop(Table.PairSlice 0 (rbase + UInt32.ofNat (8 * 9))
      (R.drop 9) ∗ Rest ∗
      armExit buf len fp rbase 9 r7 r13 r16 r17 r18
        (Table.applyNetwork keyLt Table.sort9Net (R.take 9)
          ++ R.drop 9) Rest rest arity remainder controls calls s E Φ))
    hM9 hroom9 rfl hcont9
  isplitl [Hlow]
  · iexact Hlow
  · isplitl [Hhigh]
    · iexact Hhigh
    · isplitl [HRest]
      · iexact HRest
      · iexact Hexit

private theorem sort13_append_nil :
    (qsSort13 : Program) = qsSort13 ++ [] := (List.append_nil _).symm

set_option maxHeartbeats 2000000 in
/-- The thirteen-entry network, WAT 7011 to 8391.  It runs on the first
thirteen entries of the region and leaves the rest alone. -/
private theorem twp_arm13 [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {rbase r6 r7 r9 r10 r11 r13 r15 r16 r17 r18 : UInt32}
    {r12 : UInt64} {R : List (UInt32 × UInt32)} {n : Nat}
    {Rest : HeapIProp} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : R.length = n) (h13 : 13 ≤ n) (hn : n ≤ 32)
    (hroom : rbase.toNat + 8 * n < UInt32.size) :
    iprop(Table.PairSlice 0 rbase R ∗ Rest ∗
      armExit buf len fp rbase 13 r7 r13 r16 r17 r18
        (Table.applyNetwork keyLt Table.sort13Net (R.take 13)
          ++ R.drop 13) Rest [] arity remainder controls calls
        s E Φ) ⊢
      WP (.running ⟨rLoc buf len fp nt r6 r7 rbase r9 r10 r11 r12 r13
            r15 r16 r17 r18 [], qsSort13, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hM13 : (R.take 13).length = 13 := take_length_eq (by omega)
  have hroom13 : rbase.toNat + 104 < UInt32.size := by omega
  have hjoin2 := slice_join rbase
    (Table.applyNetwork keyLt Table.sort13Net (R.take 13)) (R.drop 13)
    (m := 13) (by rw [Table.applyNetwork_length]; exact hM13)
  have hcont13 : ∀ (y2 y3 y4 y9 y10 y11 y14 y15 y21 y22 y23 y24 y26 y28
        y29 : UInt32) (y12 y19 y20 y25 y27 : UInt64)
        (y30 y31 y32 y33 y34 y35 y36 y37 y38 : Value),
      iprop(Table.PairSlice 0 rbase
          (Table.applyNetwork keyLt Table.sort13Net (R.take 13)) ∗
        (Table.PairSlice 0 (rbase + UInt32.ofNat (8 * 13))
          (R.drop 13) ∗ Rest ∗
          armExit buf len fp rbase 13 r7 r13 r16 r17 r18
            (Table.applyNetwork keyLt Table.sort13Net (R.take 13)
              ++ R.drop 13) Rest [] arity remainder controls calls
            s E Φ)) ⊢
      WP (.running ⟨Func21Network9.netLocals
            ⟨buf, len, fp, r7, r13, .i32 r16, .i32 r17, .i32 r18,
              y30, y31, y32, y33, y34, y35, y36, y37, y38⟩
            rbase y2 y3 y4 13 y9 y10 y11 y12 y14 y15 y19 y20 y21 y22
            y23 y24 y25 y26 y27 y28 y29 [], [], arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
    intro y2 y3 y4 y9 y10 y11 y14 y15 y21 y22 y23 y24 y26 y28 y29 y12
      y19 y20 y25 y27 y30 y31 y32 y33 y34 y35 y36 y37 y38
    iintro ⟨HN, Hhi, HRest, Hexit⟩
    isimp only [armExit] at Hexit
    ihave Hgo := Hexit
      $$ %(⟨y2, y3, y4, y14, y19, y20, y21, y22, y23, y24, y25, y26,
          y27, y28, y29, y30, y31, y32, y33, y34, y35, y36, y37,
          y38⟩ : NetScratch)
      %y9 %y10 %y11 %y12 %y15
    iapply Hgo
    isplitl [HN Hhi]
    · iapply hjoin2.mpr
      isplitl [HN]
      · iexact HN
      · iexact Hhi
    · iexact HRest
  rw [sort13_append_nil]
  iintro ⟨Hbuf, HRest, Hexit⟩
  icases (Table.PairSlice_split 0 rbase R 13 (by omega)).mp $$ Hbuf
    with ⟨Hlow, Hhigh⟩
  rw [rLoc_net]
  iapply Func21Network13.twp_sort13
    (f := ⟨buf, len, fp, r7, r13, .i32 r16, .i32 r17, .i32 r18,
      nt.p30, nt.p31, nt.p32, nt.p33, nt.p34, nt.p35, nt.p36, nt.p37,
      nt.p38⟩)
    (M := R.take 13)
    (N := Table.applyNetwork keyLt Table.sort13Net (R.take 13))
    (Rest := iprop(Table.PairSlice 0 (rbase + UInt32.ofNat (8 * 13))
      (R.drop 13) ∗ Rest ∗
      armExit buf len fp rbase 13 r7 r13 r16 r17 r18
        (Table.applyNetwork keyLt Table.sort13Net (R.take 13)
          ++ R.drop 13) Rest [] arity remainder controls calls s E Φ))
    hM13 hroom13 rfl hcont13
  isplitl [Hlow]
  · iexact Hlow
  · isplitl [Hhigh]
    · iexact Hhigh
    · isplitl [HRest]
      · iexact HRest
      · iexact Hexit

/-! ## One turn of the region loop, WAT 6221 to 8489 -/

set_option maxHeartbeats 2000000 in
/-- One turn of the region loop.  The region length picks the kernel:
eight entries or fewer go through the insertion sort alone, nine to
twelve through the nine-entry network first, and thirteen or more
through the thirteen-entry network first.  Every arm leaves a sorted
permutation of the region and reaches the region switch of WAT 8490. -/
theorem twp_sort_region [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {rbase r6 r7 r9 r10 r11 r13 r15 r16 r17 r18 : UInt32}
    {r12 : UInt64} {R : List (UInt32 × UInt32)} {n : Nat}
    {Rest : HeapIProp} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : R.length = n) (h2 : 2 ≤ n) (hn : n ≤ 32)
    (hroom : rbase.toNat + 8 * n < UInt32.size)
    (h7 : r7 = UInt32.ofNat n)
    (hcont : ∀ (Rout : List (UInt32 × UInt32)) (nt' : NetScratch)
        (y6 y7 y9 y10 y11 : UInt32) (y12 : UInt64) (y15 : UInt32),
      Rout.Perm R → Table.SortedByKey Rout →
      iprop(Table.PairSlice 0 rbase Rout ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt' y6 y7 rbase y9 y10 y11 y12 r13
            y15 r16 r17 r18 [], qsRegionNext, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 rbase R ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt r6 r7 rbase r9 r10 r11 r12 r13
            r15 r16 r17 r18 [], qsRegionLoop, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  subst h7
  have hsz : UInt32.size = 4294967296 := rfl
  rw [qsRegionLoop_shape, qsRegionBody_shape, qsNetworkSelect_split,
    qsSmallGuard_shape]
  simp only [List.cons_append, List.nil_append]
  iintro ⟨Hbuf, HRest⟩
  wasm_twp_pures [twp_block twp_block twp_localGet twp_const]
  by_cases hbig : 13 ≤ n
  · -- WAT 6225 and 6226: the region goes to the second network
    iapply Wasm.SmallStep.twp_gtU (result := 1)
      (by
        rw [if_pos (show (UInt32.ofNat n : UInt32) > 12 from
          ofNat_lt (a := 12) (b := n) (by omega) (by omega)
            (by omega))])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    have hf := netOut_facts (k := 13) hlen (by omega)
      Table.sort13Net_sorts
    iapply twp_arm13 (nt := nt) hlen hbig hn hroom
    isplitl [Hbuf]
    · iexact Hbuf
    · isplitl [HRest]
      · iexact HRest
      · isimp only [armExit]
        iintro %nt' %y9 %y10 %y11 %y12 %y15 ⟨Hout, HRest'⟩
        wasm_twp_pures [twp_exitControl]
        simp only [List.take_zero, List.nil_append]
        iapply twp_after_region (nt := nt') (k := 13) hf.1 (by omega)
          (by omega) hn (by rw [hf.2.1]; exact hf.2.2.2) hroom
          (fun z6 z7 z9 z10 z11 z12 z15 =>
            hcont _ nt' z6 z7 z9 z10 z11 z12 z15
              ((insertionShiftLeft_perm _ 13).trans hf.2.2.1)
              (insertionShiftLeft_sorted _ 13
                (by rw [hf.2.1]; exact hf.2.2.2)))
        isplitl [Hout]
        · iexact Hout
        · iexact HRest'
  · -- WAT 6227 to 6232: the region has twelve entries or fewer
    iapply Wasm.SmallStep.twp_gtU (result := 0)
      (by
        rw [if_neg (show ¬ ((UInt32.ofNat n : UInt32) > 12) from
          UInt32.not_lt.mpr (ofNat_le (a := n) (b := 12) (by omega)
            (by omega) (by omega)))])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_const]
    by_cases hsmall : n ≤ 8
    · -- WAT 6232: the insertion sort alone
      iapply Wasm.SmallStep.twp_leU (result := 1)
        (by
          rw [if_pos (show (UInt32.ofNat n : UInt32) ≤ 8 from
            ofNat_le (a := n) (b := 8) (by omega) (by omega)
              hsmall)])
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      have hs1 : Table.SortedByKey (R.take 1) := by
        cases R with
        | nil => exact Table.SortedByKey.nil
        | cons a rest =>
          rw [show (a :: rest).take 1 = [a] from rfl]
          exact Table.sortedByKey_singleton a
      iapply twp_after_region (nt := nt) (k := 1) hlen (by omega)
        (by omega) hn hs1 hroom
        (fun z6 z7 z9 z10 z11 z12 z15 =>
          hcont _ nt z6 z7 z9 z10 z11 z12 z15
            (insertionShiftLeft_perm R 1)
            (insertionShiftLeft_sorted R 1 hs1))
      isplitl [Hbuf]
      · iexact Hbuf
      · iexact HRest
    · -- WAT 6233 to 7008: the first network
      iapply Wasm.SmallStep.twp_leU (result := 0)
        (by
          rw [if_neg (show ¬ ((UInt32.ofNat n : UInt32) ≤ 8) from
            UInt32.not_le.mpr (ofNat_lt (a := 8) (b := n) (by omega)
              (by omega) (by omega)))])
      iapply Wasm.SmallStep.twp_brIfZero
      have hf := netOut_facts (k := 9) hlen (by omega)
        Table.sort9Net_sorts
      iapply twp_arm9 (nt := nt) hlen (by omega) hn hroom
      isplitl [Hbuf]
      · iexact Hbuf
      · isplitl [HRest]
        · iexact HRest
        · isimp only [armExit]
          iintro %nt' %y9 %y10 %y11 %y12 %y15 ⟨Hout, HRest'⟩
          iapply Wasm.SmallStep.twp_br rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          iapply twp_after_region (nt := nt') (k := 9) hf.1 (by omega)
            (by omega) hn (by rw [hf.2.1]; exact hf.2.2.2) hroom
            (fun z6 z7 z9 z10 z11 z12 z15 =>
              hcont _ nt' z6 z7 z9 z10 z11 z12 z15
                ((insertionShiftLeft_perm _ 9).trans hf.2.2.1)
                (insertionShiftLeft_sorted _ 9
                  (by rw [hf.2.1]; exact hf.2.2.2)))
          isplitl [Hout]
          · iexact Hout
          · iexact HRest'


/-! ## The region loop, WAT 6193 to 8501 -/

/-- The three block frames that stand at WAT 6193.  Block 4 has already
ended, so the innermost frame is block 3.  `after` is the code that
follows the body of block 1, which is the stack epilogue. -/
def regBlocks (after : Program) (controls : List ControlFrame) :
    List ControlFrame :=
  qsFrame qsBlock3Body qsAfter3 :: qsFrame qsBlock2Body qsAfter2 ::
    qsFrame qsBlock1Body after :: controls

/-- A list of one entry or none is in key order. -/
private theorem sortedByKey_of_length_lt_two
    {l : List (UInt32 × UInt32)} (h : l.length < 2) :
    Table.SortedByKey l := by
  match l, h with
  | [], _ => exact Table.SortedByKey.nil
  | [a], _ => exact Table.sortedByKey_singleton a
  | a :: b :: t, h =>
    simp only [List.length_cons] at h
    omega

/-- A word is the word of its own number. -/
private theorem self_ofNat (x : UInt32) : x = UInt32.ofNat x.toNat := by
  apply UInt32.toNat_inj.mp
  rw [ofNat_toNat (UInt32.toNat_lt x)]

/-- `i32.shr_u` by one is a division by two, after the Wasm mask. -/
private theorem shr_one (x : UInt32) :
    x >>> ((1 : UInt32) % 32) = UInt32.ofNat (x.toNat / 2) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hx := UInt32.toNat_lt x
  have hd : x.toNat / 2 < UInt32.size := by omega
  have hsr : x.toNat >>> 1 = x.toNat / 2 := rfl
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight,
    show ((1 : UInt32) % 32).toNat % 32 = 1 from rfl, hsr,
    ofNat_toNat hd]

/-- `i32.sub` of a small index. -/
private theorem sub_ofNat (x : UInt32) (m : Nat) (hm : m ≤ x.toNat) :
    x - UInt32.ofNat m = UInt32.ofNat (x.toNat - m) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hx := UInt32.toNat_lt x
  have h1 : (UInt32.ofNat m : UInt32).toNat = m :=
    ofNat_toNat (by omega)
  have h2 : (UInt32.ofNat (x.toNat - m) : UInt32).toNat = x.toNat - m :=
    ofNat_toNat (by omega)
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_sub, h1, h2]
  omega

/-- Where one turn of the region loop leaves the machine: at the region
switch of WAT 8490, with the region sorted.  The turn writes every
register of `NetScratch` and the locals 6, 7, 9, 10, 11, 12 and 15. -/
private def turnExit [WasmSmallStepGS hlc Universal.State]
    (buf len fp rbase r13 r16 r17 r18 : UInt32)
    (R : List (UInt32 × UInt32)) (Rest : HeapIProp) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Phi : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ Rout : List (UInt32 × UInt32), ∀ nt' : NetScratch,
    ∀ y6 : UInt32, ∀ y7 : UInt32, ∀ y9 : UInt32, ∀ y10 : UInt32,
    ∀ y11 : UInt32, ∀ y12 : UInt64, ∀ y15 : UInt32,
    ⌜Rout.Perm R ∧ Table.SortedByKey Rout⌝ -∗
    (Table.PairSlice 0 rbase Rout ∗ Rest -∗
      WP (.running ⟨rLoc buf len fp nt' y6 y7 rbase y9 y10 y11 y12 r13
            y15 r16 r17 r18 [], qsRegionNext, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Phi }]))

set_option maxHeartbeats 2000000 in
/-- One turn of the region loop, with the continuation as a resource.
`twp_sort_region` states the same run with the continuation as a
hypothesis, which a caller that names the loop frame cannot use. -/
private theorem twp_turn [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {rbase r6 r7 r9 r10 r11 r13 r15 r16 r17 r18 : UInt32}
    {r12 : UInt64} {R : List (UInt32 × UInt32)} {n : Nat}
    {Rest : HeapIProp} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : R.length = n) (h2 : 2 ≤ n) (hn : n ≤ 32)
    (hroom : rbase.toNat + 8 * n < UInt32.size)
    (h7 : r7 = UInt32.ofNat n) :
    iprop(Table.PairSlice 0 rbase R ∗ Rest ∗
      turnExit buf len fp rbase r13 r16 r17 r18 R Rest arity remainder
        controls calls s E Φ) ⊢
      WP (.running ⟨rLoc buf len fp nt r6 r7 rbase r9 r10 r11 r12 r13
            r15 r16 r17 r18 [], qsRegionLoop, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hc : ∀ (Rout : List (UInt32 × UInt32)) (nt' : NetScratch)
      (y6 y7 y9 y10 y11 : UInt32) (y12 : UInt64) (y15 : UInt32),
      Rout.Perm R → Table.SortedByKey Rout →
      iprop(Table.PairSlice 0 rbase Rout ∗
        (Rest ∗ turnExit buf len fp rbase r13 r16 r17 r18 R Rest arity
          remainder controls calls s E Φ)) ⊢
      WP (.running ⟨rLoc buf len fp nt' y6 y7 rbase y9 y10 y11 y12 r13
            y15 r16 r17 r18 [], qsRegionNext, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
    intro Rout nt' y6 y7 y9 y10 y11 y12 y15 hp hs
    iintro ⟨Hout, HRest, Hexit⟩
    isimp only [turnExit] at Hexit
    ihave Hgo := Hexit $$ %Rout %nt' %y6 %y7 %y9 %y10 %y11 %y12 %y15
      %(⟨hp, hs⟩ : Rout.Perm R ∧ Table.SortedByKey Rout)
    iapply Hgo
    isplitl [Hout]
    · iexact Hout
    · iexact HRest
  iintro ⟨Hbuf, HRest, Hexit⟩
  iapply twp_sort_region (nt := nt) (R := R) (n := n)
    (Rest := iprop(Rest ∗ turnExit buf len fp rbase r13 r16 r17 r18 R
      Rest arity remainder controls calls s E Φ))
    hlen h2 hn hroom h7 hc
  isplitl [Hbuf]
  · iexact Hbuf
  · isplitl [HRest]
    · iexact HRest
    · iexact Hexit

set_option maxHeartbeats 2000000 in
/-- The small sort of a length below 18, WAT 6193 to 8501.  A length
below two leaves at WAT 6196 with the buffer unchanged.  Every other
length makes one region, which is the whole buffer, and the loop leaves
at WAT 8491 after one turn.  Both exits reach the code that follows
block 1. -/
theorem twp_region_loop_single [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {r6 r7 r8 r9 r10 r11 r13 r15 r16 r17 r18 : UInt32} {r12 : UInt64}
    {pairs : List (UInt32 × UInt32)}
    {Rest : HeapIProp} {after : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hpairs : pairs.length = len.toNat) (hlen : len.toNat < 18)
    (hroom : buf.toNat + 8 * len.toNat < UInt32.size)
    (hcont : ∀ (out : List (UInt32 × UInt32)) (nt' : NetScratch)
        (y6 y7 y8 y9 y10 y11 : UInt32) (y12 : UInt64)
        (y13 y15 y16 y17 y18 : UInt32),
      out.Perm pairs → Table.SortedByKey out →
      iprop(Table.PairSlice 0 buf out ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt' y6 y7 y8 y9 y10 y11 y12 y13
            y15 y16 y17 y18 [], after, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 buf pairs ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt r6 r7 r8 r9 r10 r11 r12 r13 r15
            r16 r17 r18 [], qsAfter4, arity, remainder,
          regBlocks after controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  rw [qsAfter4_split, qsSmallSetup_shape]
  simp only [List.cons_append, List.nil_append]
  iintro ⟨Hbuf, HRest⟩
  wasm_twp_pures [twp_localGet twp_const]
  by_cases h2 : 2 ≤ len.toNat
  · -- WAT 6197 to 8501: one region, the whole buffer
    iapply Wasm.SmallStep.twp_ltU (result := 0)
      (by
        rw [if_neg (show ¬ (len < (2 : UInt32)) from
          UInt32.not_lt.mpr (UInt32.le_iff_toNat_le.mpr
            (show (2 : UInt32).toNat ≤ len.toNat by
              rw [show (2 : UInt32).toNat = 2 from rfl]; omega)))])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shrU]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_const]
    iapply Wasm.SmallStep.twp_ltU (result := 1)
      (by
        rw [if_pos (show len < (18 : UInt32) from
          UInt32.lt_iff_toNat_lt.mpr
            (show len.toNat < (18 : UInt32).toNat by
              rw [show (18 : UInt32).toNat = 18 from rfl]; omega))])
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_select (selected := Value.i32 len)
      (by rw [if_pos (by decide : (1 : UInt32) ≠ 0)])
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet twp_sub]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl twp_add]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_loop
    simp only [List.drop_zero]
    iapply twp_turn (nt := nt) (R := pairs) (n := len.toNat)
      hpairs h2 (by omega) hroom (self_ofNat len)
    isplitl [Hbuf]
    · iexact Hbuf
    · isplitl [HRest]
      · iexact HRest
      · isimp only [turnExit]
        iintro %Rout %nt' %y6 %y7 %y9 %y10 %y11 %y12 %y15 %hps
          ⟨Hout, HRest'⟩
        rw [qsRegionNext_shape]
        wasm_twp_pures [twp_localGet]
        iapply Wasm.SmallStep.twp_brIf
          (by decide : (1 : UInt32) ≠ 0) rfl
        simp only [qsFrame, List.take_zero, List.nil_append]
        iapply (hcont Rout nt' y6 y7 buf y9 y10 y11 y12
          (len >>> ((1 : UInt32) % 32) <<< ((3 : UInt32) % 32) + buf)
          y15 (len >>> ((1 : UInt32) % 32)) 1
          (len - len >>> ((1 : UInt32) % 32)) hps.1 hps.2)
        isplitl [Hout]
        · iexact Hout
        · iexact HRest'
  · -- WAT 6196: a length below two leaves at once
    iapply Wasm.SmallStep.twp_ltU (result := 1)
      (by
        rw [if_pos (show len < (2 : UInt32) from
          UInt32.lt_iff_toNat_lt.mpr
            (show len.toNat < (2 : UInt32).toNat by
              rw [show (2 : UInt32).toNat = 2 from rfl]; omega))])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [qsFrame, List.take_zero, List.nil_append]
    iapply (hcont pairs nt r6 r7 r8 r9 r10 r11 r12 r13 r15 r16 r17 r18
      (List.Perm.refl pairs)
      (sortedByKey_of_length_lt_two (by omega)))
    isplitl [Hbuf]
    · iexact Hbuf
    · iexact HRest


set_option maxHeartbeats 2000000 in
/-- The small sort of a length of 18 to 32, WAT 6193 to 8501.  The
buffer splits into two regions, the first `len / 2` entries and the
rest.  The loop makes two turns, one for each region, and then falls
through to the merge of WAT 8503. -/
theorem twp_region_loop_double [WasmSmallStepGS hlc Universal.State]
    {buf len fp : UInt32} {nt : NetScratch}
    {r6 r7 r8 r9 r10 r11 r13 r15 r16 r17 r18 : UInt32} {r12 : UInt64}
    {pairs : List (UInt32 × UInt32)}
    {Rest : HeapIProp} {after : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hpairs : pairs.length = len.toNat) (hlow : 18 ≤ len.toNat)
    (hhigh : len.toNat ≤ 32)
    (hroom : buf.toNat + 8 * len.toNat < UInt32.size)
    (hcont : ∀ (L Rt : List (UInt32 × UInt32)) (nt' : NetScratch)
        (y9 y10 y11 : UInt32) (y12 : UInt64) (y15 : UInt32),
      L.length = len.toNat / 2 →
      Rt.length = len.toNat - len.toNat / 2 →
      Table.SortedByKey L → Table.SortedByKey Rt →
      (L ++ Rt).Perm pairs →
      iprop(Table.PairSlice 0 buf (L ++ Rt) ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt' 0
            (UInt32.ofNat (len.toNat - len.toNat / 2))
            (buf + UInt32.ofNat (8 * (len.toNat / 2))) y9 y10 y11 y12
            (buf + UInt32.ofNat (8 * (len.toNat / 2))) y15
            (UInt32.ofNat (len.toNat / 2)) 0
            (UInt32.ofNat (len.toNat - len.toNat / 2)) [],
          qsAfterRegion, arity, remainder, regBlocks after controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 buf pairs ∗ Rest) ⊢
      WP (.running ⟨rLoc buf len fp nt r6 r7 r8 r9 r10 r11 r12 r13 r15
            r16 r17 r18 [], qsAfter4, arity, remainder,
          regBlocks after controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  set m := len.toNat / 2 with hmdef
  have hm9 : 9 ≤ m := by omega
  have hm16 : m ≤ 16 := by omega
  have hmlen : m ≤ len.toNat := by omega
  have hrest9 : 9 ≤ len.toNat - m := by omega
  have hroom1 : buf.toNat + 8 * m < UInt32.size := by omega
  have hbase : (buf + UInt32.ofNat (8 * m)).toNat = buf.toNat + 8 * m :=
    Slices.byteOffset_toNat buf (8 * m) (by omega)
  have hroom2 : (buf + UInt32.ofNat (8 * m)).toNat
      + 8 * (len.toNat - m) < UInt32.size := by omega
  have hlen1 : (pairs.take m).length = m := take_length_eq (by omega)
  have hlen2 : (pairs.drop m).length = len.toNat - m := by
    rw [List.length_drop, hpairs]
  have hne13 : ¬ (buf + UInt32.ofNat (8 * m) = buf) := by
    intro hc
    have h1 := congrArg UInt32.toNat hc
    rw [hbase] at h1
    omega
  have hmshl : (UInt32.ofNat m : UInt32) <<< (3 : UInt32)
      = UInt32.ofNat (8 * m) := ofNat_shl m (by omega)
  rw [qsAfter4_split, qsSmallSetup_shape]
  simp only [List.cons_append, List.nil_append]
  iintro ⟨Hbuf, HRest⟩
  wasm_twp_pures [twp_localGet twp_const]
  iapply Wasm.SmallStep.twp_ltU (result := 0)
    (by
      rw [if_neg (show ¬ (len < (2 : UInt32)) from
        UInt32.not_lt.mpr (UInt32.le_iff_toNat_le.mpr
          (show (2 : UInt32).toNat ≤ len.toNat by
            rw [show (2 : UInt32).toNat = 2 from rfl]; omega)))])
  iapply Wasm.SmallStep.twp_brIfZero
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shrU]
  isimp only [shr_one, ← hmdef]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const]
  iapply Wasm.SmallStep.twp_ltU (result := 0)
    (by
      rw [if_neg (show ¬ (len < (18 : UInt32)) from
        UInt32.not_lt.mpr (UInt32.le_iff_toNat_le.mpr
          (show (18 : UInt32).toNat ≤ len.toNat by
            rw [show (18 : UInt32).toNat = 18 from rfl]; omega)))])
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply Wasm.SmallStep.twp_select
    (selected := Value.i32 (UInt32.ofNat m))
    (by rw [if_neg (by decide : ¬ ((0 : UInt32) ≠ 0))])
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_sub]
  isimp only [sub_ofNat len m hmlen]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
  isimp only [shl_three, hmshl]
  wasm_twp_pures [twp_add]
  isimp only [show UInt32.ofNat (8 * m) + buf
    = buf + UInt32.ofNat (8 * m) from UInt32.add_comm _ _]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply Wasm.SmallStep.twp_loop
  simp only [List.drop_zero]
  icases (Table.PairSlice_split 0 buf pairs m (by omega)).mp $$ Hbuf
    with ⟨Hlow, Hhigh⟩
  -- WAT 6221 to 8501: the first region
  iapply twp_turn (nt := nt) (R := pairs.take m) (n := m)
    (Rest := iprop(Table.PairSlice 0 (buf + UInt32.ofNat (8 * m))
      (pairs.drop m) ∗ Rest))
    hlen1 (by omega) (by omega) hroom1 rfl
  isplitl [Hlow]
  · iexact Hlow
  · isplitl [Hhigh HRest]
    · isplitl [Hhigh]
      · iexact Hhigh
      · iexact HRest
    · isimp only [turnExit]
      iintro %L %nt1 %y6 %y7 %y9 %y10 %y11 %y12 %y15 %hps
        ⟨HL, Hhi, HRest1⟩
      have hLlen : L.length = m := by
        rw [hps.1.length_eq, hlen1]
      rw [qsRegionNext_shape]
      wasm_twp_pures [twp_localGet]
      iapply Wasm.SmallStep.twp_brIfZero
      wasm_twp_pures [twp_localGet twp_localGet]
      iapply Wasm.SmallStep.twp_eq (result := 1) (by rw [if_pos rfl])
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet]
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
      simp only [List.take_zero, List.nil_append]
      -- WAT 6221 to 8501: the second region
      iapply twp_turn (nt := nt1) (R := pairs.drop m)
        (n := len.toNat - m)
        (Rest := iprop(Table.PairSlice 0 buf L ∗ Rest))
        hlen2 (by omega) (by omega) hroom2 rfl
      isplitl [Hhi]
      · iexact Hhi
      · isplitl [HL HRest1]
        · isplitl [HL]
          · iexact HL
          · iexact HRest1
        · isimp only [turnExit]
          iintro %Rt %nt2 %z6 %z7 %z9 %z10 %z11 %z12 %z15 %hps2
            ⟨HRt, HL2, HRest2⟩
          have hRtlen : Rt.length = len.toNat - m := by
            rw [hps2.1.length_eq, hlen2]
          have hperm : (L ++ Rt).Perm pairs := by
            have h := hps.1.append hps2.1
            rwa [List.take_append_drop] at h
          rw [qsRegionNext_shape]
          wasm_twp_pures [twp_localGet]
          iapply Wasm.SmallStep.twp_brIfZero
          wasm_twp_pures [twp_localGet twp_localGet]
          iapply Wasm.SmallStep.twp_eq (result := 0)
            (by rw [if_neg hne13])
          wasm_twp_localSet [List.set, List.length_cons,
            List.length_nil, Nat.reduceAdd, Nat.reduceSub]
          wasm_twp_pures [twp_localGet]
          wasm_twp_localSet [List.set, List.length_cons,
            List.length_nil, Nat.reduceAdd, Nat.reduceSub]
          wasm_twp_pures [twp_localGet]
          wasm_twp_localSet [List.set, List.length_cons,
            List.length_nil, Nat.reduceAdd, Nat.reduceSub]
          wasm_twp_pures [twp_localGet]
          iapply Wasm.SmallStep.twp_brIfZero
          wasm_twp_pures [twp_exitControl]
          simp only [List.take_zero, List.nil_append]
          iapply (hcont L Rt nt2 z9 z10 z11 z12 z15 hLlen hRtlen
            hps.2 hps2.2 hperm)
          isplitl [HL2 HRt]
          · iapply (slice_join buf L Rt (m := m) hLlen).mpr
            isplitl [HL2]
            · iexact HL2
            · iexact HRt
          · iexact HRest2

end Project.RustHashMap.Func21Region
