import Project.RustHashMap.SortPures

/-!
# Proof of `insertion_sort_shift_left`, absolute `func 15`

Absolute `func 15` is `insertion_sort_shift_left`, local `func12`, WAT
lines 2849 to 2952 of `programs/rust/build/rust_hash_map/program.wat`.
This module proves `SortContracts.Func12Spec`.

## The register map

The body has three parameters and five more registers.

| Register | Meaning |
| --- | --- |
| 0 | the buffer address, never written |
| 1 | the length on entry, then the byte index of the hole |
| 2 | the offset on entry, then the address of the hole |
| 3 | the address one entry past the end |
| 4 | the byte index of the outer cursor |
| 5 | the address of the outer cursor |
| 6 | the key of the entry that the body holds |
| 7 | the value of the entry that the body holds |

## The five regions

| Name | WAT | What it does |
| --- | --- | --- |
| `guardBody` | 2851 to 2950 | the two early exits and the whole sort |
| `sortBody` | 2856 to 2948 | the cursor set-up and the outer loop |
| `outerBody` | 2874 to 2947 | one step of the outer loop |
| `scanBody` | 2875 to 2935 | the compare, the hold and the write back |
| `holeBody` | 2890 to 2926 | the search for the hole |
| `shiftBody` | 2891 to 2921 | one step of the shift loop |

The `unreachable` at WAT 2951 is dead.  It is reached only through the
guard at WAT 2852 to 2855, which leaves the outer block when the offset
is above the length, and the contract asks for `offset <= len`.  That is
the row X-F15-OFFSET of `Analysis/scope-and-exclusions.md`.

## The two loops

The outer loop walks the index `j` from `offset` to `len`.  The buffer
holds `outerAcc pairs offset j ++ pairs.drop j`, where `outerAcc` is the
model fold over the first `j - offset` later entries.  The measure is
`len - j`.

The shift loop walks the hole index `i` down from `j`.  The buffer holds
`A.take i ++ a :: (A.drop i ++ post)`, where `A` is the sorted prefix,
`post` is the part above the held entry and `a` is a stale copy that the
write back overwrites.  The measure is `i`.  The invariant also carries
the history: every key from `i - 1` up to `j - 1` is above the held key.
`insertTail_eq_of_split` turns that history and the stop test into the
model insertion.
-/

namespace Project.RustHashMap.Func12Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.SortContracts
open Project.RustHashMap.SortModels
open Project.RustHashMap.SortPures
open scoped Wasm.SmallStep.Outcome

/-! ## Word and address bridges -/

/-- `.const 4294967288` is minus eight.  Copy of `LookupPures.lean:304`,
which this module does not import. -/
private theorem addNegEight (x : UInt32) : x + 4294967288 = x - 8 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967288 : UInt32).toNat = 4294967288 from rfl,
    show (8 : UInt32).toNat = 8 from rfl] at *
  omega

/-- The address of entry `n + 1` is eight above the address of entry
`n`.  No bound is needed, because `UInt32.ofNat` is already modular. -/
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

/-- `i32.shl` by three is a multiplication by eight.  Copy of
`CollectReserve.lean:52`, which is private there. -/
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

/-- The word that `i64.extend_i32_u` pushes, in the form that
`pairWord_eq_shl_or` uses. -/
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


/-! ## List vocabulary of the two invariants -/

/-- Entry `i` of a list, with no proof that `i` is in range.  Out of
range the model reads the entry `(0, 0)`, exactly as `keyAt` does. -/
private def entryAt (ps : List (UInt32 × UInt32)) (i : Nat) :
    UInt32 × UInt32 :=
  ps.getD i (0, 0)

private theorem keyAt_entryAt (ps : List (UInt32 × UInt32)) (i : Nat) :
    keyAt ps i = (entryAt ps i).1 := rfl

private theorem entryAt_eq_getElem (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : entryAt ps i = ps[i] :=
  List.getD_eq_getElem _ _ hi

private theorem take_length_eq {α : Type} {l : List α} {i : Nat}
    (hi : i ≤ l.length) : (l.take i).length = i := by
  rw [List.length_take, Nat.min_eq_left hi]

private theorem take_succ_eq (l : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < l.length) : l.take (i + 1) = l.take i ++ [entryAt l i] := by
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
the held key.  `insertTail` puts the held entry at exactly that place. -/
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

/-- The buffer after the outer loop has put the first `j - offset` later
entries into place. -/
private def outerAcc (pairs : List (UInt32 × UInt32)) (off j : Nat) :
    List (UInt32 × UInt32) :=
  ((pairs.drop off).take (j - off)).foldl (fun acc p => insertTail p acc)
    (pairs.take off)

private theorem foldl_insertTail_length (rest : List (UInt32 × UInt32)) :
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


/-! ## Opening one entry of the buffer

The two loops always know the buffer as `pre ++ a :: post`, so these
three rules are stated on that shape.  They cost no index arithmetic at
the call site: the address is `8 * pre.length` bytes above the base.
-/

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

/-- Open two entries in a row.  The shift loop reads the lower one and
writes the upper one in the same step, so it holds both at once. -/
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
          ((⌜(v + UInt32.ofNat (8 * pre.length)).toNat + 8 < UInt32.size⌝ ∗
              pointsTo_u64 0 (v + UInt32.ofNat (8 * pre.length))
                (Table.pairWord q)) ∗
            ((⌜(v + UInt32.ofNat (8 * (pre.length + 1))).toNat + 8
                  < UInt32.size⌝ ∗
                pointsTo_u64 0 (v + UInt32.ofNat (8 * (pre.length + 1)))
                  (Table.pairWord r)) ∗
              Table.PairSlice 0
                (v + UInt32.ofNat (8 * (pre.length + 1)) + 8) post))) := by
    intro q r
    rw [← haddr]
    refine (Table.PairSlice_split 0 v (pre ++ q :: r :: post) pre.length
      (by simp)).trans ?_
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

end Slices



/-! ## Address facts of one entry cell -/

/-- Move an owned double word between two names of one address.  Copy of
`LookupProbe.lean:106`, which is private there. -/
private theorem wordMove64 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 (α := α) 0 address value ⊢
      pointsTo_u64 0 address' value := by
  rw [haddress]

/-- The eight byte addresses of one `i64` cell.  Copy of
`FrameCells.lean:256`, which this module does not import. -/
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
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 4 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 5 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 6 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 7 (by omega)

/-- The three address facts that `twp_load32_addr` asks for.  Copy of
`LookupProbe.lean:111`, which is private there. -/
private theorem addr_facts (addr : UInt32)
    (h : addr.toNat + 4 ≤ UInt32.size) :
    (addr + 1).toNat = addr.toNat + 1 ∧
      (addr + 2).toNat = addr.toNat + 2 ∧
      (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using Slices.byteOffset_toNat addr 1 (by omega),
    by simpa using Slices.byteOffset_toNat addr 2 (by omega),
    by simpa using Slices.byteOffset_toNat addr 3 (by omega)⟩

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

/-- Stepping the byte index back by one entry. -/
private theorem index_back (n : Nat) :
    UInt32.ofNat (8 * (n + 1)) + 4294967288 = UInt32.ofNat (8 * n) := by
  have h := addr_back 0 n
  simpa using h

/-- `i32.add` puts the second operand first, so every compiled address
of this body has the constant on the left.  These three forms are the
ones the machine builds. -/
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
    (8 : UInt32) + UInt32.ofNat (8 * n) = UInt32.ofNat (8 * (n + 1)) := by
  have h := addr_next 0 n
  simpa using h

/-- `i32.shl` by three, after the Wasm mask. -/
private theorem shl_three (x : UInt32) : x <<< ((3 : UInt32) % 32)
    = x <<< 3 := rfl

/-- The four byte addresses of one `i32` cell.  Copy of
`FrameCells.lean:221`, which this module does not import. -/
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
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)

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

/-! ## The regions of the body -/

/-- The registers of the body.  Registers 0 to 2 are the parameters. -/
@[reducible] private def regs (l0 l1 l2 l3 l4 l5 l6 : UInt32)
    (l7 : UInt64) (vs : List Value) : Locals :=
  { params := [.i32 l0, .i32 l1, .i32 l2],
    locals := [.i32 l3, .i32 l4, .i32 l5, .i32 l6, .i64 l7],
    values := vs }

/-- One step of the shift loop, WAT 2891 to 2921. -/
@[reducible] private def shiftBody : Program :=
  [.localGet 0, .localGet 1, .add, .localTee 2, .localGet 2,
    .const 4294967288, .add, .load64 0, .store64 0,
    .block 0 0
      [.localGet 1, .const 8, .ne, .br_if 0, .localGet 0, .localSet 1,
        .br 2],
    .localGet 1, .const 4294967288, .add, .localSet 1, .localGet 6,
    .localGet 2, .const 4294967280, .add, .load32 0, .ltU, .br_if 0]

/-- The search for the hole, WAT 2890 to 2926. -/
@[reducible] private def holeBody : Program :=
  [.loop 0 0 shiftBody, .localGet 0, .localGet 1, .add, .localSet 1]

/-- The write back of the held entry, WAT 2927 to 2934. -/
@[reducible] private def writeBack : Program :=
  [.localGet 1, .localGet 7, .constI64 32, .shlI64, .localGet 6,
    .extendUI32, .orI64, .store64 0]

/-- The compare, the hold and the write back, WAT 2875 to 2935. -/
@[reducible] private def scanBody : Program :=
  .localGet 5 :: .load32 0 :: .localTee 6 :: .localGet 5 ::
    .const 4294967288 :: .add :: .load32 0 :: .geU :: .br_if 0 ::
    .localGet 5 :: .load32UI64 4 :: .localSet 7 :: .localGet 4 ::
    .localSet 1 :: .block 0 0 holeBody :: writeBack

/-- The cursor step and the back edge of the outer loop, WAT 2936 to
2946. -/
@[reducible] private def outerTail : Program :=
  [.localGet 4, .const 8, .add, .localSet 4, .localGet 5, .const 8,
    .add, .localTee 5, .localGet 3, .ne, .br_if 0]

/-- One step of the outer loop, WAT 2874 to 2947. -/
@[reducible] private def outerBody : Program :=
  .block 0 0 scanBody :: outerTail

/-- The cursor set-up and the outer loop, WAT 2856 to 2948. -/
@[reducible] private def sortBody : Program :=
  [.localGet 2, .localGet 1, .eq, .br_if 0, .localGet 0, .localGet 1,
    .const 3, .shl, .add, .localSet 3, .localGet 0, .localGet 2,
    .const 3, .shl, .localTee 4, .add, .localSet 5,
    .loop 0 0 outerBody]

/-- The whole body below the dead `unreachable`, WAT 2851 to 2950. -/
@[reducible] private def guardBody : Program :=
  [.localGet 2, .localGet 1, .gtU, .br_if 0, .block 0 0 sortBody, .ret]

set_option maxRecDepth 1048576 in
/-- The generated body is the guard block and the dead `unreachable`. -/
private theorem func12_shape :
    Project.RustHashMap.func12
      = [Instruction.block 0 0 guardBody, Instruction.unreachable] := rfl

private theorem func12_index :
    Project.RustHashMap.«module».funcs[12]? =
      some Project.RustHashMap.func12Def := by rfl


/-! ## The write back of the held entry -/

/-- Where the search for the hole leaves the machine: at the end of the
body of the block of WAT 2875, with the buffer holding the model
insertion.  The two registers that the search overwrites are free. -/
private def holeExit [WasmSmallStepGS hlc Universal.State]
    (v l3 l4 l5 : UInt32) (held : UInt32 × UInt32)
    (A post : List (UInt32 × UInt32)) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ r1 : UInt32, ∀ r2 : UInt32,
    Table.PairSlice 0 v (insertTail held A ++ post) -∗
    WP (.running ⟨regs v r1 r2 l3 l4 l5 held.1 held.2.toUInt64 [],
          [], arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }])

set_option maxHeartbeats 2000000 in
/-- The write back, WAT 2927 to 2934.  It stores the held entry into the
hole as one `i64`, and that store is the model insertion. -/
private theorem twp_write_back [WasmSmallStepGS hlc Universal.State]
    {v l3 l4 l5 r1 r2 : UInt32} {A post : List (UInt32 × UInt32)}
    {held : UInt32 × UInt32} {k j : Nat}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hr1 : r1 = v + UInt32.ofNat (8 * k))
    (hlen : A.length = j) (hk : k ≤ j)
    (hroom : v.toNat + 8 * (j + 1) < UInt32.size)
    (hbelow : ∀ m, m < k → ¬ (held.1 < keyAt A m))
    (habove : k < j → held.1 < keyAt A k) :
    iprop(
      (∃ a : UInt32 × UInt32,
        Table.PairSlice 0 v (A.take k ++ a :: (A.drop k ++ post))) ∗
      holeExit v l3 l4 l5 held A post arity remainder controls calls
        s E Φ) ⊢
      WP (.running ⟨regs v r1 r2 l3 l4 l5 held.1
            held.2.toUInt64 [],
          writeBack, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst hr1
  iintro ⟨Hslice, Hexit⟩
  icases Hslice with ⟨%a, Hslice⟩
  have hklen : (A.take k).length = k :=
    take_length_eq (by omega)
  have hword : held.2.toUInt64 <<< ((32 : UInt64) % 64)
      ||| UInt64.ofNat held.1.toNat = Table.pairWord held := by
    rw [shift_count, extendU_eq, ← pairWord_eq_shl_or]
  have hfacts := cell_facts64 v k (j + 1) (by omega) hroom
  have hfinal : A.take k ++ held :: (A.drop k ++ post)
      = insertTail held A ++ post := by
    rw [insertTail_eq_of_split held A k (by omega) hbelow
      (by rw [hlen]; exact habove)]
    simp
  isimp only [writeBack, regs]
  wasm_twp_pures [twp_localGet twp_localGet twp_constI64 twp_shlI64
    twp_localGet twp_extendUI32 twp_orI64]
  isimp only [hword]
  ihave ⟨Hcell, Hclose⟩ :=
    slice_focus v (A.take k) a (A.drop k ++ post) k hklen $$ Hslice
  ihave Hcell := wordMove64 (UInt32.add_zero _).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store64
    (address := v + UInt32.ofNat (8 * k)) (offset := 0)
    (Table.pairWord a) hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1
    hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _) $$ Hcell
  ihave Hslice := Hclose $$ %held Hcell
  isimp only [hfinal] at Hslice
  isimp only [holeExit] at Hexit
  ihave Hgo := Hexit $$ %(v + UInt32.ofNat (8 * k)) %r2 Hslice
  iexact Hgo


/-! ## The search for the hole -/

/-- Open the entry just below a prefix of length `i + 1`. -/
private theorem key_split (A tail : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < A.length) :
    A.take (i + 1) ++ tail = A.take i ++ entryAt A i :: tail := by
  rw [take_succ_eq A hi]
  simp

/-- The hole at `i` holds a stale copy of entry `i`, so the buffer names
that entry twice. -/
private theorem hole_split (A post : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < A.length) :
    A.take i ++ entryAt A i :: (A.drop i ++ post)
      = A.take i ++ entryAt A i :: entryAt A i ::
          (A.drop (i + 1) ++ post) := by
  rw [drop_eq_cons A hi]
  simp

set_option maxHeartbeats 2000000 in
/-- The search for the hole and the write back, WAT 2890 to 2934.  The
theorem starts at the block of WAT 2890 and ends at the end of the body
of the block of WAT 2875.

The shift loop moves one entry up per step and stops at the front or at
the first entry whose key is not above the held key.  Both stops reach
the write back, which puts the held entry into the hole. -/
private theorem twp_hole [WasmSmallStepGS hlc Universal.State]
    {v l3 l4 l5 r2 : UInt32} {A post : List (UInt32 × UInt32)}
    {held : UInt32 × UInt32} {j : Nat}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : A.length = j) (hj1 : 1 ≤ j)
    (hroom : v.toNat + 8 * (j + 1) < UInt32.size)
    (hsorted : Table.SortedByKey A)
    (hentry : held.1 < keyAt A (j - 1)) :
    iprop(
      Table.PairSlice 0 v (A ++ held :: post) ∗
      holeExit v l3 l4 l5 held A post arity remainder controls calls
        s E Φ) ⊢
      WP (.running ⟨regs v (UInt32.ofNat (8 * j)) r2 l3 l4 l5 held.1
            held.2.toUInt64 [],
          .block 0 0 holeBody :: writeBack, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hexit⟩
  wasm_twp_pures [twp_block]
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := Nat × UInt32)
    (measure := fun p => p.1)
    (locals := fun p => regs v (UInt32.ofNat (8 * p.1)) p.2 l3 l4 l5
      held.1 held.2.toUInt64 [])
    (I := fun p => iprop(
      ⌜1 ≤ p.1 ∧ p.1 ≤ j ∧
        ∀ m, p.1 ≤ m + 1 → m < j → held.1 < keyAt A m⌝ ∗
      (∃ a : UInt32 × UInt32,
        Table.PairSlice 0 v (A.take p.1 ++ a :: (A.drop p.1 ++ post))) ∗
      holeExit v l3 l4 l5 held A post arity remainder controls calls
        s E Φ))
    (initial := (j, r2))
    (initialLocals := regs v (UInt32.ofNat (8 * j)) r2 l3 l4 l5 held.1
      held.2.toUInt64 [])
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
    isimp only [key_split A (a :: (A.drop (i' + 1) ++ post)) hi'A] at Hbuf
    ihave ⟨Hlow, Hhigh, Hclose⟩ :=
      slice_two v (A.take i') (entryAt A i') a
        (A.drop (i' + 1) ++ post) i' hpre $$ Hbuf
    have hlowf := cell_facts64 v i' (j + 1) (by omega) hroom
    have hhighf := cell_facts64 v (i' + 1) (j + 1) (by omega) hroom
    have hcur : UInt32.ofNat (8 * (i' + 1)) + v
        = v + UInt32.ofNat (8 * (i' + 1)) := UInt32.add_comm _ _
    simp only [Wasm.SmallStep.loopBodyExpr, shiftBody, regs]
    wasm_twp_pures [twp_localGet twp_localGet twp_add]
    isimp only [hcur]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    isimp only [addr_prev]
    ihave Hlow := wordMove64 (UInt32.add_zero _).symm $$ Hlow
    wasm_twp_rebind Wasm.SmallStep.twp_load64
      (address := v + UInt32.ofNat (8 * i')) (offset := 0)
      (Table.pairWord (entryAt A i')) hlowf.1 hlowf.2.1 hlowf.2.2.1
      hlowf.2.2.2.1 hlowf.2.2.2.2.1 hlowf.2.2.2.2.2.1
      hlowf.2.2.2.2.2.2.1 hlowf.2.2.2.2.2.2.2 with Hlow
    ihave Hhigh := wordMove64 (UInt32.add_zero _).symm $$ Hhigh
    wasm_twp_rebind Wasm.SmallStep.twp_store64
      (address := v + UInt32.ofNat (8 * (i' + 1))) (offset := 0)
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
      have hpre2 : (A.take i'').length = i'' := take_length_eq (by omega)
      isimp only [key_split A (entryAt A (i'' + 1) ::
        (A.drop (i'' + 1) ++ post)) hi''A] at Hbuf
      ihave ⟨Hkey, Hclosek⟩ :=
        slice_key v (A.take i'') (entryAt A i'')
          (entryAt A (i'' + 1) :: (A.drop (i'' + 1) ++ post))
          i'' hpre2 $$ Hbuf
      have hkf := cell_facts32 v i'' (j + 1) (by omega) hroom
      wasm_twp_rebind Wasm.SmallStep.twp_load32_addr
        (entryAt A i'').1 hkf.1 hkf.2.1 hkf.2.2 with Hkey
      ihave Hbuf := Hclosek $$ Hkey
      isimp only [← key_split A (entryAt A (i'' + 1) ::
        (A.drop (i'' + 1) ++ post)) hi''A] at Hbuf
      by_cases hcmp : held.1 < keyAt A i''
      · iapply Wasm.SmallStep.twp_ltU (result := 1)
          (by rw [if_pos (by rw [← keyAt_entryAt]; exact hcmp)])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
        simp only [List.take_zero, List.nil_append]
        ihave Hback := Hrec
          $$ %((i'' + 1, v + UInt32.ofNat (8 * (i'' + 1 + 1))) :
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
        wasm_twp_pures [twp_exitControl twp_localGet twp_localGet twp_add]
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
/-- The compare, the hold and the write back, WAT 2875 to 2935.  The
entry above the sorted prefix either stays where it is, when its key is
not below its left neighbour, or moves down into the prefix.  Both arms
leave the block of WAT 2875 with the prefix holding the model
insertion. -/
private theorem twp_scan [WasmSmallStepGS hlc Universal.State]
    {v l1 l2 l3 l6 : UInt32} {l7 : UInt64}
    {A post : List (UInt32 × UInt32)} {held : UInt32 × UInt32} {j : Nat}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : A.length = j) (hj1 : 1 ≤ j)
    (hroom : v.toNat + 8 * (j + 1) < UInt32.size)
    (hsorted : Table.SortedByKey A) :
    iprop(
      Table.PairSlice 0 v (A ++ held :: post) ∗
      (∀ r1 : UInt32, ∀ r2 : UInt32, ∀ r6 : UInt32, ∀ r7 : UInt64,
        Table.PairSlice 0 v (insertTail held A ++ post) -∗
        WP (.running ⟨regs v r1 r2 l3 (UInt32.ofNat (8 * j))
              (v + UInt32.ofNat (8 * j)) r6 r7 [],
            outerTail, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨regs v l1 l2 l3 (UInt32.ofNat (8 * j))
            (v + UInt32.ofNat (8 * j)) l6 l7 [],
          .block 0 0 scanBody :: outerTail, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hexit⟩
  obtain ⟨j0, rfl⟩ : ∃ j0, j = j0 + 1 := ⟨j - 1, by omega⟩
  have hj0A : j0 < A.length := by omega
  have hpre0 : (A.take j0).length = j0 := take_length_eq (by omega)
  have hcell := cell_facts32 v (j0 + 1) (j0 + 1 + 1) (by omega) hroom
  have hcell0 := cell_facts32 v j0 (j0 + 1 + 1) (by omega) hroom
  have hval := value_facts v (j0 + 1) (j0 + 1 + 1) (by omega) hroom
  have hsplit0 : A ++ held :: post
      = A.take j0 ++ entryAt A j0 :: (held :: post) := by
    have h := key_split A (held :: post) hj0A
    rwa [List.take_of_length_le (show A.length ≤ j0 + 1 by omega)] at h
  isimp only [regs] at Hexit
  simp only [scanBody, regs]
  wasm_twp_pures [twp_block twp_localGet]
  ihave ⟨Hkey, Hclosek⟩ := slice_key v A held post (j0 + 1) hlen $$ Hbuf
  wasm_twp_rebind Wasm.SmallStep.twp_load32_addr held.1
    hcell.1 hcell.2.1 hcell.2.2 with Hkey
  ihave Hbuf := Hclosek $$ Hkey
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [addr_prev]
  isimp only [hsplit0] at Hbuf
  ihave ⟨Hkey0, Hclose0⟩ :=
    slice_key v (A.take j0) (entryAt A j0) (held :: post) j0 hpre0 $$ Hbuf
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
      slice_value v A held post (j0 + 1) hlen $$ Hbuf
    wasm_twp_rebind Wasm.SmallStep.twp_load32UI64
      (address := v + UInt32.ofNat (8 * (j0 + 1))) (offset := 4)
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
    · isimp only [holeExit, regs]
      iintro %r1 %r2 Hdone
      wasm_twp_pures [twp_exitControl]
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      ihave Hgo := Hexit $$ %r1 %r2 %held.1 %held.2.toUInt64 Hdone
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
    ihave Hgo := Hexit $$ %l1 %l2 %held.1 %l7 Hbuf
    iexact Hgo

/-! ## The body -/

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
/-- Absolute `func 15` sorts the entries from `offset` on into the sorted
prefix below them. -/
theorem func12_correct [WasmSmallStepGS hlc Universal.State] :
    Func12Spec (hlc := hlc) := by
  unfold Func12Spec CallContract callExpr
  intro v len offset pairs callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hbuf, %hpure, Hcont⟩
  obtain ⟨hpairs, hoff1, hoffle, hsorted, hroom⟩ := hpure
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 15
      Project.RustHashMap.func12Def (by decide) func12_index with Hmodule
  simp only [Project.RustHashMap.func12Def, Function.toLocals,
    Function.numParams, List.length_cons, List.length_nil, List.take,
    List.drop, List.reverse_cons, List.reverse_nil, List.map,
    List.nil_append, List.cons_append, ValueType.zero, func12_shape,
    Nat.reduceAdd]
  wasm_twp_pures [twp_block twp_localGet twp_localGet]
  iapply Wasm.SmallStep.twp_gtU (result := 0)
    (by
      rw [if_neg (show ¬ (offset > len) from
        UInt32.not_lt.mpr (UInt32.le_iff_toNat_le.mpr hoffle))])
  iapply Wasm.SmallStep.twp_brIfZero
  wasm_twp_pures [twp_block twp_localGet twp_localGet]
  by_cases heq : offset = len
  · -- WAT 2857 to 2860: the offset is the length, so nothing moves
    iapply Wasm.SmallStep.twp_eq (result := 1) (by rw [if_pos heq])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallExplicit with Hmodule
    simp only [List.take, List.nil_append]
    iclose_map_runtime Hruntime with Hmodule Henv
    isimp only [SortPostFrameless] at Hcont
    have hall : Table.SortedByKey pairs := by
      have h : pairs.take offset.toNat = pairs :=
        List.take_of_length_le (by rw [hpairs, heq])
      rwa [h] at hsorted
    ihave Hgo := Hcont $$ %pairs Hruntime Hbuf
      %(⟨List.Perm.refl pairs, hall⟩ :
        pairs.Perm pairs ∧ Table.SortedByKey pairs)
    isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
    iexact Hgo
  · -- WAT 2861 to 2947: the cursor set-up and the outer loop
    iapply Wasm.SmallStep.twp_eq (result := 0) (by rw [if_neg heq])
    iapply Wasm.SmallStep.twp_brIfZero
    have hoffn : offset.toNat < len.toNat := by
      rcases Nat.eq_or_lt_of_le hoffle with he | hlt
      · exact absurd (UInt32.toNat_inj.mp he) heq
      · exact hlt
    have hlenshl : len <<< (3 : UInt32) = UInt32.ofNat (8 * len.toNat) :=
      shift_three len (by omega)
    have hoffshl : offset <<< (3 : UInt32)
        = UInt32.ofNat (8 * offset.toNat) := shift_three offset (by omega)
    have hcomm1 : UInt32.ofNat (8 * len.toNat) + v
        = v + UInt32.ofNat (8 * len.toNat) := UInt32.add_comm _ _
    have hcomm2 : UInt32.ofNat (8 * offset.toNat) + v
        = v + UInt32.ofNat (8 * offset.toNat) := UInt32.add_comm _ _
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
    isimp only [shl_three, hlenshl]
    wasm_twp_pures [twp_add]
    isimp only [hcomm1]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
    isimp only [shl_three, hoffshl]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_add]
    isimp only [hcomm2]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_loop_wf_family
      (ι := Nat × UInt32 × UInt32 × UInt32 × UInt64)
      (measure := fun p => len.toNat - p.1)
      (locals := fun p => regs v p.2.1 p.2.2.1
        (v + UInt32.ofNat (8 * len.toNat)) (UInt32.ofNat (8 * p.1))
        (v + UInt32.ofNat (8 * p.1)) p.2.2.2.1 p.2.2.2.2 [])
      (I := fun p => iprop(
        ⌜offset.toNat ≤ p.1 ∧ p.1 < len.toNat⌝ ∗
        Table.PairSlice 0 v
          (outerAcc pairs offset.toNat p.1 ++ pairs.drop p.1) ∗
        runtimeModuleOwn ⟨0⟩ Project.RustHashMap.«module» ∗
        hostEnvOwn 0 (Universal.envFor Project.RustHashMap.«module») ∗
        SortPostFrameless v pairs callerLocals stack code arity remainder
          controls calls s E Φ))
      (initial := (offset.toNat, len, offset, 0, 0))
      (initialLocals := regs v len offset
        (v + UInt32.ofNat (8 * len.toNat))
        (UInt32.ofNat (8 * offset.toNat))
        (v + UInt32.ofNat (8 * offset.toNat)) 0 0 [])
      rfl rfl
    · intro p
      obtain ⟨jj, r1, r2, r6, r7⟩ := p
      iintro Hrec ⟨%hinv, Hbuf, Hmodule, Henv, Hcont⟩
      obtain ⟨hoffj, hjn⟩ := hinv
      replace hoffj : offset.toNat ≤ jj := hoffj
      replace hjn : jj < len.toNat := hjn
      obtain ⟨A, hAdef⟩ : ∃ A, outerAcc pairs offset.toNat jj = A :=
        ⟨_, rfl⟩
      have hAlen : A.length = jj := by
        rw [← hAdef]
        exact outerAcc_length pairs hoffj (by omega)
      have hAsorted : Table.SortedByKey A := by
        rw [← hAdef]
        exact outerAcc_sorted pairs hsorted
      have hdrop : pairs.drop jj
          = entryAt pairs jj :: pairs.drop (jj + 1) :=
        drop_eq_cons pairs (by omega)
      isimp only [hAdef, hdrop] at Hbuf
      simp only [Wasm.SmallStep.loopBodyExpr, outerBody]
      iapply twp_scan hAlen (by omega) (by omega) hAsorted
      isplitl [Hbuf]
      · iexact Hbuf
      · iintro %r1' %r2' %r6' %r7' Hdone
        have hstep : outerAcc pairs offset.toNat (jj + 1)
              ++ pairs.drop (jj + 1)
            = insertTail (entryAt pairs jj) A ++ pairs.drop (jj + 1) := by
          rw [outerAcc_succ pairs hoffj (by omega), hAdef]
        isimp only [← hstep] at Hdone
        simp only [outerTail, regs]
        wasm_twp_pures [twp_localGet twp_const twp_add]
        isimp only [index_next]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet twp_const twp_add]
        isimp only [addr_next]
        wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet]
        by_cases hlast : jj + 1 = len.toNat
        · -- WAT 2947: the cursor met the end pointer
          iapply Wasm.SmallStep.twp_ne (result := 0)
            (by rw [if_neg (by rw [hlast]; exact fun h => h rfl)])
          iapply Wasm.SmallStep.twp_brIfZero
          wasm_twp_pures [twp_exitControl]
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          wasm_twp_pures [twp_exitControl]
          simp only [List.take_zero, List.nil_append]
          wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallExplicit
            with Hmodule
          simp only [List.take, List.nil_append]
          iclose_map_runtime Hruntime with Hmodule Henv
          isimp only [SortPostFrameless] at Hcont
          have hfin : outerAcc pairs offset.toNat (jj + 1)
                ++ pairs.drop (jj + 1)
              = insertionShiftLeft pairs offset.toNat := by
            rw [hlast, ← hpairs, outerAcc_full,
              List.drop_of_length_le (Nat.le_refl _)]
            simp
          isimp only [hfin] at Hdone
          ihave Hgo := Hcont $$ %(insertionShiftLeft pairs offset.toNat)
            Hruntime Hdone
            %(⟨insertionShiftLeft_perm pairs offset.toNat,
                insertionShiftLeft_sorted pairs offset.toNat hsorted⟩ :
              (insertionShiftLeft pairs offset.toNat).Perm pairs ∧
                Table.SortedByKey
                  (insertionShiftLeft pairs offset.toNat))
          isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
          iexact Hgo
        · -- WAT 2946: one more entry to place
          have hne : v + UInt32.ofNat (8 * (jj + 1))
              ≠ v + UInt32.ofNat (8 * len.toNat) := by
            intro hc
            have h1 := congrArg UInt32.toNat hc
            rw [Slices.byteOffset_toNat v (8 * (jj + 1)) (by omega),
              Slices.byteOffset_toNat v (8 * len.toNat) (by omega)] at h1
            omega
          iapply Wasm.SmallStep.twp_ne (result := 1)
            (by rw [if_pos hne])
          iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
            rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          ihave Hback := Hrec
            $$ %((jj + 1, r1', r2', r6', r7') :
                Nat × UInt32 × UInt32 × UInt32 × UInt64)
            %(show len.toNat - (jj + 1) < len.toNat - jj by omega)
          iapply Hback
          isplitl_pureexact (⟨by omega, by omega⟩ :
            offset.toNat ≤ jj + 1 ∧ jj + 1 < len.toNat)
          · isplitl [Hdone]
            · iexact Hdone
            · iframe Hmodule Henv Hcont
    · have hstart : outerAcc pairs offset.toNat offset.toNat
          ++ pairs.drop offset.toNat = pairs := by
        rw [outerAcc_self, List.take_append_drop]
      isplitl_pureexact (⟨Nat.le_refl offset.toNat, hoffn⟩ :
        offset.toNat ≤ offset.toNat ∧ offset.toNat < len.toNat)
      · isplitl [Hbuf]
        · isimp only [hstart]
          iexact Hbuf
        · iframe Hmodule Henv Hcont

end Project.RustHashMap.Func12Proof
