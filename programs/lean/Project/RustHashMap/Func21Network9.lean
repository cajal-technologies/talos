import Project.RustHashMap.Func21Defs
import Project.RustHashMap.SortPures

/-!
# The nine-entry sorting network of `quicksort`

Absolute `func 24` is `quicksort`, local `func21`.  WAT lines 6233 to
7008 of `programs/rust/build/rust_hash_map/program.wat` hold the first
sorting network of the small sort, which is the fragment `qsSort9` of
`Project.RustHashMap.Func21Defs`.  This module proves `twp_sort9`, the
one stage lemma of that region.

## What the region computes

The region sorts the nine entries that start at the region base, which
local 8 holds, and then writes 9 into local 6.  The run is branch free.
It holds 75 `select` instructions, which is 25 comparators, and the pure
model of those comparators is `Table.sort9Net`.

One comparator of the slots `i` and `j`, with `i < j`, reads the two
keys, writes the smaller entry into slot `i` and the greater entry into
slot `j`.  That is `Table.cmpSwap keyLt (i, j)`, because the compiled
test is `key of j below key of i`, which is `keyLt` of the two entries
in that order.  A comparator makes three stores: the value of the
greater entry, the key of the greater entry, and the whole smaller
entry as one `i64`.  A tie moves nothing, which
`Table.cmpSwap_of_not_lt` matches.

## The comparator table

The table gives, for each comparator, the WAT span, the two slots, the
shape of the `select` that makes the smaller entry, where the two keys
come from, the local that caches the key of the greater entry, and the
local that caches the smaller entry.  `load` is a fresh `i32.load`,
`wrap Ln` is `i32.wrap_i64` of the entry word in local `n`, `reg n` is
the key already in local `n`, and `-` is no cache.

| # | WAT | slots | min | key i | key j | key reg | entry reg |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 6233-6267 | (0, 3) | addr | load | load | L3 | L19 |
| 1 | 6268-6308 | (1, 7) | off | load | load | L2 | L20 |
| 2 | 6309-6348 | (2, 5) | off | load | load | L4 | L12 |
| 3 | 6349-6388 | (4, 8) | off | load | load | L22 | L25 |
| 4 | 6389-6418 | (0, 7) | addr | wrap L19 | reg 2 | L2 | L19 |
| 5 | 6419-6448 | (2, 4) | word | wrap L12 | wrap L25 | L23 | L27 |
| 6 | 6449-6478 | (3, 8) | off | reg 3 | reg 22 | L22 | L12 |
| 7 | 6479-6513 | (5, 6) | off | reg 4 | load | L4 | L25 |
| 8 | 6514-6543 | (0, 2) | word | wrap L19 | wrap L27 | L24 | L19 |
| 9 | 6544-6573 | (1, 3) | word | wrap L20 | wrap L12 | L26 | L20 |
| 10 | 6574-6602 | (4, 5) | word | reg 23 | wrap L25 | L23 | L25 |
| 11 | 6603-6632 | (7, 8) | off | reg 2 | reg 22 | L2 | L12 |
| 12 | 6633-6662 | (1, 4) | word | wrap L20 | wrap L25 | L22 | L20 |
| 13 | 6663-6692 | (3, 6) | off | reg 26 | reg 4 | L4 | L25 |
| 14 | 6693-6721 | (5, 7) | word | reg 23 | wrap L12 | L23 | L27 |
| 15 | 6722-6750 | (0, 1) | word | wrap L19 | wrap L20 | L26 | - |
| 16 | 6751-6778 | (2, 4) | addr | reg 24 | reg 22 | L22 | L12 |
| 17 | 6779-6808 | (3, 5) | word | wrap L25 | wrap L27 | L24 | L19 |
| 18 | 6809-6837 | (6, 8) | off | reg 4 | reg 2 | - | L25 |
| 19 | 6838-6867 | (2, 3) | word | wrap L12 | wrap L19 | L2 | L19 |
| 20 | 6868-6895 | (4, 5) | addr | reg 22 | reg 24 | L4 | L12 |
| 21 | 6896-6925 | (6, 7) | word | wrap L25 | reg 23 | - | L25 |
| 22 | 6926-6952 | (1, 2) | word | reg 26 | wrap L19 | - | - |
| 23 | 6953-6979 | (3, 4) | word | reg 2 | wrap L12 | - | - |
| 24 | 6980-7006 | (5, 6) | word | reg 4 | wrap L25 | - | - |

The `min` column names three shapes, and one rule covers each:

* `addr`: the `select` picks the address of the smaller slot and an
  `i64.load` reads it.  `twp_min_addr` covers it.
* `off`: the `select` picks the byte offset of the smaller slot, an
  `i32.add` makes the address, and an `i64.load` reads it.
  `twp_min_off` covers it.
* `word`: the two entry words are already in locals, or one of them is
  read first, and the `select` picks between the words.  `twp_select`
  with `select_min_pair` covers it, and neither arm reads memory.

Every comparator makes the value of the greater entry with the same
`select` and `i32.load offset=4`, which `twp_max_value` covers, and the
key of the greater entry with the same `i32.gt_u` and `select`, which
`select_max_key` covers.

## How the proof is cut

`Func21Defs.qsSort9Chunk` cuts the run right after every fifteenth
`select`, which falls inside a comparator: the stores that finish that
comparator sit in the next chunk.  This module cuts after the last
store of every fifth comparator instead, so that each part runs five
whole comparators and each part lemma states one whole
`Table.applyNetwork` step.  `sort9Part` names the five parts, and
`qsSort9_parts` ties them to `qsSort9`.

Each part lemma carries the live registers of the network.  A register
that holds a key or an entry word names it as `eAt` of the list that
the memory holds at that point, so no register names a stale list.  The
three rules that follow a `select` split on the comparison once and
close both arms with one continuation, so no part lemma splits.
-/

namespace Project.RustHashMap.Func21Network9

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.SortModels
open Project.RustHashMap.Func21Defs
open scoped Wasm.SmallStep.Outcome

set_option maxRecDepth 40000

/-! ## The entry of one slot

`eAt` reads one entry of the model list without a bound proof, so that
a register value never carries a proof term.
-/

/-- The entry of slot `k`.  Outside the list it is `(0, 0)`. -/
def eAt (M : List (UInt32 × UInt32)) (k : Nat) : UInt32 × UInt32 :=
  M.getD k (0, 0)

private theorem eAt_eq (M : List (UInt32 × UInt32)) {k : Nat}
    (hk : k < M.length) : eAt M k = M[k] :=
  List.getD_eq_getElem _ _ hk

/-- A store into another slot leaves the entry alone. -/
private theorem eAt_set_ne (M : List (UInt32 × UInt32)) (k n : Nat)
    (h : n ≠ k) {q : UInt32 × UInt32} :
    eAt (M.set k q) n = eAt M n := by
  rw [eAt, eAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (Ne.symm h)]

/-! ## The pure model of one comparator

The compiled comparator of the slots `i` and `j`, with `i < j`, reads
the two keys, and writes the smaller entry into slot `i` and the greater
entry into slot `j`.  That is `Table.cmpSwap keyLt` of the pair `(i, j)`,
because `keyLt b a` is the test that the compiled code makes.
-/

/-- The order that the compiled comparator uses, in the form that
`Table.applyNetwork_pairs_sorted` takes. -/
theorem keyLt_eq : keyLt = fun a b => decide (a.1 < b.1) := rfl

/-- The smaller entry, when the second key is below the first. -/
private theorem cmpMin_pos {a b : UInt32 × UInt32} (h : b.1 < a.1) :
    Table.cmpMin keyLt a b = b := by
  rw [Table.minPair_eq, if_pos (by simpa [keyLt] using h)]

/-- The smaller entry, when the second key is not below the first. -/
private theorem cmpMin_neg {a b : UInt32 × UInt32} (h : ¬ b.1 < a.1) :
    Table.cmpMin keyLt a b = a := by
  rw [Table.minPair_eq, if_neg (by simpa [keyLt] using h)]

/-- The greater entry, when the second key is below the first. -/
private theorem cmpMax_pos {a b : UInt32 × UInt32} (h : b.1 < a.1) :
    Table.cmpMax keyLt a b = a := by
  rw [Table.maxPair_eq, if_pos (by simpa [keyLt] using h)]

/-- The greater entry, when the second key is not below the first. -/
private theorem cmpMax_neg {a b : UInt32 × UInt32} (h : ¬ b.1 < a.1) :
    Table.cmpMax keyLt a b = b := by
  rw [Table.maxPair_eq, if_neg (by simpa [keyLt] using h)]

/-- A flag that the compiled code made with `i32.lt_u` selects the arm
that the test names. -/
private theorem select_flag {α : Type _} (P : Prop) [Decidable P]
    (x y : α) :
    (if (if P then (1 : UInt32) else 0) ≠ 0 then x else y) =
      if P then x else y := by
  by_cases h : P <;> simp [h]

/-- The key that the compiled code keeps, which it makes with
`i32.gt_u`, is the key of the greater entry.  The two forms differ only
on a tie, where both keys are the same. -/
private theorem cmpMax_key (a b : UInt32 × UInt32) :
    (if a.1 < b.1 then b.1 else a.1) = (Table.cmpMax keyLt a b).1 := by
  by_cases h : b.1 < a.1
  · have h1 := UInt32.lt_iff_toNat_lt.mp h
    rw [cmpMax_pos h, if_neg (fun hc =>
      absurd (UInt32.lt_iff_toNat_lt.mp hc) (by omega))]
  · rw [cmpMax_neg h]
    by_cases h2 : a.1 < b.1
    · rw [if_pos h2]
    · rw [if_neg h2]
      have h1 : ¬ b.1.toNat < a.1.toNat := fun hc =>
        h (UInt32.lt_iff_toNat_lt.mpr hc)
      have h3 : ¬ a.1.toNat < b.1.toNat := fun hc =>
        h2 (UInt32.lt_iff_toNat_lt.mpr hc)
      exact UInt32.toNat_inj.mp (by omega)

/-- The entry of the greater slot, as the two halves that the compiled
code stores. -/
private theorem cmpMax_pair (a b : UInt32 × UInt32) :
    ((Table.cmpMax keyLt a b).1, (Table.cmpMax keyLt a b).2) =
      Table.cmpMax keyLt a b := rfl

/-! ## The list steps of one comparator -/

/-- An index stays below the length after a store. -/
private theorem lt_set (M : List (UInt32 × UInt32)) {n k : Nat}
    {q : UInt32 × UInt32} (h : n < M.length) :
    n < (M.set k q).length := by
  rw [List.length_set]; exact h

/-- A store keeps the length. -/
private theorem len_set (M : List (UInt32 × UInt32)) {k : Nat}
    {q : UInt32 × UInt32} (h : M.length = 9) :
    (M.set k q).length = 9 := by
  rw [List.length_set]; exact h

/-- A list with an entry put back where it came from. -/
private theorem set_self (M : List (UInt32 × UInt32)) {k : Nat}
    (hk : k < M.length) : M.set k (M[k].1, M[k].2) = M := by
  rw [show (M[k].1, M[k].2) = M[k] from rfl, List.set_getElem_self hk]

/-- Two stores into one slot keep the second. -/
private theorem set_value_key (M : List (UInt32 × UInt32)) {k : Nat}
    (hk : k < M.length) (key value : UInt32) :
    (M.set k ((eAt M k).1, value)).set k
        (key, (eAt (M.set k ((eAt M k).1, value)) k).2) =
      M.set k (key, value) := by
  rw [eAt_eq (M.set k ((eAt M k).1, value))
      (by rw [List.length_set]; exact hk),
    List.getElem_set_self, List.set_set]

/-- The three stores of one comparator make one `cmpSwap` step. -/
private theorem cmpSwap_writes (M : List (UInt32 × UInt32)) {i j : Nat}
    (hij : i ≠ j) (hi : i < M.length) (hj : j < M.length) :
    (M.set j (Table.cmpMax keyLt (eAt M i) (eAt M j))).set i
        (Table.cmpMin keyLt (eAt M i) (eAt M j)) =
      Table.cmpSwap keyLt M (i, j) := by
  rw [eAt_eq M hi, eAt_eq M hj, Table.cmpSwap_eq_set_set keyLt M hi hj,
    List.set_comm _ _ hij]

/-- A comparator leaves every other slot alone. -/
private theorem cmpSwap_getElem_ne (M : List (UInt32 × UInt32))
    {i j k : Nat} (hki : k ≠ i) (hkj : k ≠ j) (hk : k < M.length) :
    (Table.cmpSwap keyLt M (i, j))[k]'(by
        rwa [Table.cmpSwap_length]) = M[k] := by
  by_cases h : i < M.length ∧ j < M.length
  · simp only [Table.cmpSwap, dif_pos h,
      List.getElem_set_ne (Ne.symm hkj), List.getElem_set_ne (Ne.symm hki)]
  · simp only [Table.cmpSwap, dif_neg h]

/-- The low slot of a comparator takes the smaller entry. -/
private theorem cmpSwap_getElem_lo (M : List (UInt32 × UInt32))
    {i j : Nat} (hij : i ≠ j) (hi : i < M.length) (hj : j < M.length) :
    (Table.cmpSwap keyLt M (i, j))[i]'(by
        rwa [Table.cmpSwap_length]) =
      Table.cmpMin keyLt M[i] M[j] := by
  simp only [Table.cmpSwap, dif_pos (⟨hi, hj⟩ : i < M.length ∧
    j < M.length), List.getElem_set_ne (Ne.symm hij),
    List.getElem_set_self]

/-- The high slot of a comparator takes the greater entry. -/
private theorem cmpSwap_getElem_hi (M : List (UInt32 × UInt32))
    {i j : Nat} (hi : i < M.length) (hj : j < M.length) :
    (Table.cmpSwap keyLt M (i, j))[j]'(by
        rwa [Table.cmpSwap_length]) =
      Table.cmpMax keyLt M[i] M[j] := by
  simp only [Table.cmpSwap, dif_pos (⟨hi, hj⟩ : i < M.length ∧
    j < M.length), List.getElem_set_self]

/-- A comparator leaves the entry of every other slot alone. -/
private theorem eAt_step (M : List (UInt32 × UInt32)) (i j k : Nat)
    (hki : k ≠ i) (hkj : k ≠ j) :
    eAt (Table.cmpSwap keyLt M (i, j)) k = eAt M k := by
  by_cases hk : k < M.length
  · have h1 : k < (Table.cmpSwap keyLt M (i, j)).length := by
      rw [Table.cmpSwap_length]; exact hk
    rw [eAt_eq _ h1, eAt_eq M hk, cmpSwap_getElem_ne M hki hkj hk]
  · rw [eAt, eAt, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [Table.cmpSwap_length]; omega),
      List.getElem?_eq_none (by omega)]

/-- The entry that the low slot of a comparator takes. -/
private theorem eAt_lo (M : List (UInt32 × UInt32)) (i j : Nat)
    (hij : i ≠ j) (hi : i < M.length) (hj : j < M.length) :
    eAt (Table.cmpSwap keyLt M (i, j)) i =
      Table.cmpMin keyLt (eAt M i) (eAt M j) := by
  have h1 : i < (Table.cmpSwap keyLt M (i, j)).length := by
    rw [Table.cmpSwap_length]; exact hi
  rw [eAt_eq _ h1, eAt_eq M hi, eAt_eq M hj,
    cmpSwap_getElem_lo M hij hi hj]

/-- The entry that the high slot of a comparator takes. -/
private theorem eAt_hi (M : List (UInt32 × UInt32)) (i j : Nat)
    (hi : i < M.length) (hj : j < M.length) :
    eAt (Table.cmpSwap keyLt M (i, j)) j =
      Table.cmpMax keyLt (eAt M i) (eAt M j) := by
  have h1 : j < (Table.cmpSwap keyLt M (i, j)).length := by
    rw [Table.cmpSwap_length]; exact hj
  rw [eAt_eq _ h1, eAt_eq M hi, eAt_eq M hj, cmpSwap_getElem_hi M hi hj]

/-- The low half of an entry word is the key.  The compiled code reads a
cached entry back with `i32.wrap_i64`. -/
private theorem pairWord_low (p : UInt32 × UInt32) :
    UInt32.ofNat ((Table.pairWord p).toNat % 2 ^ 32) = p.1 := by
  have hkey : (Table.pairWord p).toUInt32 = p.1 :=
    Project.RustHashMap.SortPures.pairWord_key p.1 p.2
  apply UInt32.toNat_inj.mp
  rw [← hkey, UInt64.toNat_toUInt32,
    UInt32.toNat_ofNat_of_lt' (by
      have h : (Table.pairWord p).toNat % 2 ^ 32 < 2 ^ 32 :=
        Nat.mod_lt _ (Nat.two_pow_pos 32)
      change (Table.pairWord p).toNat % 2 ^ 32 < 4294967296
      omega)]

/-! ## One memory step on one slot

The rules below hide the cell arithmetic of one entry.  The three rules
that follow a `select` split on the comparison once, and close both arms
with one continuation, so that the caller never splits.
-/

/-- Move an owned double word between two names of one address. -/
private theorem wordMove64 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 (α := α) 0 address value ⊢
      pointsTo_u64 0 address' value := by
  rw [haddress]

/-- Move an owned word between two names of one address. -/
private theorem wordMove32 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 (α := α) 0 address value ⊢
      pointsTo_u32 0 address' value := by
  rw [haddress]

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
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)

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
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 4 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 5 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 6 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 7 (by omega)

/-- The whole cell of slot `k`, from the address of the slot. -/
private theorem cell_facts64 (v : UInt32) (k : Nat)
    (hk : 8 * k + 8 ≤ 72) (hroom : v.toNat + 72 < UInt32.size) :
    (v + UInt32.ofNat (8 * k) + 0).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + (0 : UInt32).toNat ∧
      (v + UInt32.ofNat (8 * k) + 0 + 1).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 1 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 2).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 2 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 3).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 3 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 4).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 4 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 5).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 5 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 6).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 6 ∧
      (v + UInt32.ofNat (8 * k) + 0 + 7).toNat
        = (v + UInt32.ofNat (8 * k) + 0).toNat + 7 := by
  have hbase : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  exact offset_facts64 (v + UInt32.ofNat (8 * k)) 0 0 rfl (by omega)

/-- The value cell of slot `k`, from the address of the slot. -/
private theorem cell_facts32 (v : UInt32) (k : Nat)
    (hk : 8 * k + 8 ≤ 72) (hroom : v.toNat + 72 < UInt32.size) :
    (v + UInt32.ofNat (8 * k) + 4).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + (4 : UInt32).toNat ∧
      (v + UInt32.ofNat (8 * k) + 4 + 1).toNat
        = (v + UInt32.ofNat (8 * k) + 4).toNat + 1 ∧
      (v + UInt32.ofNat (8 * k) + 4 + 2).toNat
        = (v + UInt32.ofNat (8 * k) + 4).toNat + 2 ∧
      (v + UInt32.ofNat (8 * k) + 4 + 3).toNat
        = (v + UInt32.ofNat (8 * k) + 4).toNat + 3 := by
  have hbase : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  exact offset_facts (v + UInt32.ofNat (8 * k)) 4 4 rfl (by omega)

set_option maxHeartbeats 2000000 in
/-- `i32.load offset=8k` of the key of slot `k`, from the region base. -/
private theorem twp_key_load [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v off : UInt32} {M : List (UInt32 × UInt32)} {k : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < M.length) (hlen : M.length = 9)
    (hroom : v.toNat + 72 < UInt32.size)
    (hoff : UInt32.ofNat (8 * k) = off) :
    iprop(Table.PairSlice 0 v M ∗
      (Table.PairSlice 0 v M -∗
        WP (.running ⟨⟨params, localValues, .i32 (eAt M k).1 :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 v :: values⟩,
          .load32 off :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  simp only [eAt_eq M hk]
  iintro ⟨Hbuf, Hcont⟩
  have hfacts := offset_facts v off (8 * k) hoff (by omega)
  have haddr : v + UInt32.ofNat (8 * k) = v + off := by rw [hoff]
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_key 0 v M hk $$ Hbuf
  ihave Hcell := wordMove32 haddr $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := v)
    (offset := off) M[k].1 hfacts.1 hfacts.2.1 hfacts.2.2.1
    hfacts.2.2.2 with Hcell
  ihave Hcell := wordMove32 haddr.symm $$ Hcell
  ihave Hbuf := Hclose $$ %M[k].1 Hcell
  isimp only [set_self M hk] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i64.load offset=8k` of the entry of slot `k`, from the region
base. -/
private theorem twp_pair_load [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v off : UInt32} {M : List (UInt32 × UInt32)} {k : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < M.length) (hlen : M.length = 9)
    (hroom : v.toNat + 72 < UInt32.size)
    (hoff : UInt32.ofNat (8 * k) = off) :
    iprop(Table.PairSlice 0 v M ∗
      (Table.PairSlice 0 v M -∗
        WP (.running ⟨⟨params, localValues,
              .i64 (Table.pairWord (eAt M k)) :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 v :: values⟩,
          .load64 off :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  simp only [eAt_eq M hk]
  iintro ⟨Hbuf, Hcont⟩
  have hfacts := offset_facts64 v off (8 * k) hoff (by omega)
  have haddr : v + UInt32.ofNat (8 * k) = v + off := by rw [hoff]
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v M hk $$ Hbuf
  ihave Hcell := wordMove64 haddr $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := v)
    (offset := off) (Table.pairWord M[k]) hfacts.1 hfacts.2.1
    hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 haddr.symm $$ Hcell
  ihave Hbuf := Hclose $$ %M[k] Hcell
  isimp only [List.set_getElem_self hk] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i64.load` of the entry of slot `k`, from the address of the slot. -/
private theorem twp_pair_read [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {M : List (UInt32 × UInt32)} {k : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < M.length) (hlen : M.length = 9)
    (hroom : v.toNat + 72 < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v M ∗
      (Table.PairSlice 0 v M -∗
        WP (.running ⟨⟨params, localValues,
              .i64 (Table.pairWord (eAt M k)) :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 addr :: values⟩,
          .load64 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  simp only [eAt_eq M hk]
  iintro ⟨Hbuf, Hcont⟩
  have hfacts := cell_facts64 v k (by omega) hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v M hk $$ Hbuf
  ihave Hcell := wordMove64 (UInt32.add_zero _).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := v + UInt32.ofNat (8 * k)) (offset := 0)
    (Table.pairWord M[k]) hfacts.1 hfacts.2.1 hfacts.2.2.1
    hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _) $$ Hcell
  ihave Hbuf := Hclose $$ %M[k] Hcell
  isimp only [List.set_getElem_self hk] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i32.load offset=4` of the value of slot `k`, from the address of
the slot. -/
private theorem twp_value_read [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {M : List (UInt32 × UInt32)} {k : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < M.length) (hlen : M.length = 9)
    (hroom : v.toNat + 72 < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v M ∗
      (Table.PairSlice 0 v M -∗
        WP (.running ⟨⟨params, localValues, .i32 (eAt M k).2 :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 addr :: values⟩,
          .load32 4 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  simp only [eAt_eq M hk]
  iintro ⟨Hbuf, Hcont⟩
  have hfacts := cell_facts32 v k (by omega) hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_value 0 v M hk $$ Hbuf
  wasm_twp_rebind Wasm.SmallStep.twp_load32
    (address := v + UInt32.ofNat (8 * k)) (offset := 4) M[k].2
    hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2 with Hcell
  ihave Hbuf := Hclose $$ %M[k].2 Hcell
  isimp only [set_self M hk] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

/-- The value cell of slot `k`, from the region base. -/
private theorem value_addr (v off : UInt32) (k : Nat)
    (hoff : UInt32.ofNat (8 * k + 4) = off) (hk : 8 * k + 8 ≤ 72)
    (hroom : v.toNat + 72 < UInt32.size) :
    v + UInt32.ofNat (8 * k) + 4 = v + off := by
  have hbase : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  have hfacts := cell_facts32 v k hk hroom
  have hright : (v + off).toNat = v.toNat + 8 * k + 4 := by
    rw [← hoff]
    exact Slices.byteOffset_toNat v (8 * k + 4) (by omega)
  apply UInt32.toNat_inj.mp
  rw [hfacts.1, hbase, hright, show (4 : UInt32).toNat = 4 from rfl]

set_option maxHeartbeats 2000000 in
/-- `i32.store offset=8k+4` of the value of slot `k`. -/
private theorem twp_value_store [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v off value : UInt32} {M R : List (UInt32 × UInt32)} {k : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < M.length) (hlen : M.length = 9)
    (hroom : v.toNat + 72 < UInt32.size)
    (hoff : UInt32.ofNat (8 * k + 4) = off)
    (hres : M.set k ((eAt M k).1, value) = R) :
    iprop(Table.PairSlice 0 v M ∗
      (Table.PairSlice 0 v R -∗
        WP (.running ⟨⟨params, localValues, values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i32 value :: .i32 v :: values⟩,
          .store32 off :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst hres
  simp only [eAt_eq M hk]
  iintro ⟨Hbuf, Hcont⟩
  have hfacts := offset_facts v off (8 * k + 4) hoff (by omega)
  have haddr : v + UInt32.ofNat (8 * k) + 4 = v + off :=
    value_addr v off k hoff (by omega) hroom
  ihave ⟨Hcell, Hclose⟩ :=
    Table.PairSlice_set_value 0 v M hk value $$ Hbuf
  ihave Hcell := wordMove32 haddr $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := v)
    (offset := off) (value := value) M[k].2 hfacts.1 hfacts.2.1
    hfacts.2.2.1 hfacts.2.2.2 with Hcell
  ihave Hcell := wordMove32 haddr.symm $$ Hcell
  ihave Hbuf := Hclose $$ Hcell
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i32.store offset=8k` of the key of slot `k`. -/
private theorem twp_key_store [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v off key : UInt32} {M R : List (UInt32 × UInt32)} {k : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < M.length) (hlen : M.length = 9)
    (hroom : v.toNat + 72 < UInt32.size)
    (hoff : UInt32.ofNat (8 * k) = off)
    (hres : M.set k (key, (eAt M k).2) = R) :
    iprop(Table.PairSlice 0 v M ∗
      (Table.PairSlice 0 v R -∗
        WP (.running ⟨⟨params, localValues, values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i32 key :: .i32 v :: values⟩,
          .store32 off :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst hres
  simp only [eAt_eq M hk]
  iintro ⟨Hbuf, Hcont⟩
  have hfacts := offset_facts v off (8 * k) hoff (by omega)
  have haddr : v + UInt32.ofNat (8 * k) = v + off := by rw [hoff]
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_key 0 v M hk $$ Hbuf
  ihave Hcell := wordMove32 haddr $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := v)
    (offset := off) (value := key) M[k].1 hfacts.1 hfacts.2.1
    hfacts.2.2.1 hfacts.2.2.2 with Hcell
  ihave Hcell := wordMove32 haddr.symm $$ Hcell
  ihave Hbuf := Hclose $$ %key Hcell
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i64.store offset=8k` of the entry of slot `k`. -/
private theorem twp_pair_store [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v off : UInt32} {M R : List (UInt32 × UInt32)}
    {q : UInt32 × UInt32} {k : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < M.length) (hlen : M.length = 9)
    (hroom : v.toNat + 72 < UInt32.size)
    (hoff : UInt32.ofNat (8 * k) = off)
    (hres : M.set k q = R) :
    iprop(Table.PairSlice 0 v M ∗
      (Table.PairSlice 0 v R -∗
        WP (.running ⟨⟨params, localValues, values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i64 (Table.pairWord q) :: .i32 v :: values⟩,
          .store64 off :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst hres
  iintro ⟨Hbuf, Hcont⟩
  have hfacts := offset_facts64 v off (8 * k) hoff (by omega)
  have haddr : v + UInt32.ofNat (8 * k) = v + off := by rw [hoff]
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v M hk $$ Hbuf
  ihave Hcell := wordMove64 haddr $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := v)
    (offset := off) (Table.pairWord M[k]) hfacts.1 hfacts.2.1
    hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 haddr.symm $$ Hcell
  ihave Hbuf := Hclose $$ %q Hcell
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

/-! ## The three steps that follow a `select`

Each rule below splits on the comparison once and closes both arms with
the same continuation.  The caller never splits.
-/

set_option maxHeartbeats 2000000 in
/-- The `select` of the two slot addresses that feeds the `i64.load` of
the smaller entry. -/
private theorem twp_min_addr [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addri addrj : UInt32} {M : List (UInt32 × UInt32)} {i j : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hi : i < M.length) (hj : j < M.length) (hlen : M.length = 9)
    (hroom : v.toNat + 72 < UInt32.size)
    (haddri : addri = v + UInt32.ofNat (8 * i))
    (haddrj : addrj = v + UInt32.ofNat (8 * j)) :
    iprop(Table.PairSlice 0 v M ∗
      (Table.PairSlice 0 v M -∗
        WP (.running ⟨⟨params, localValues,
              .i64 (Table.pairWord (Table.cmpMin keyLt (eAt M i)
                (eAt M j))) :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i32 (if (eAt M j).1 < (eAt M i).1 then 1 else 0) ::
              .i32 addri :: .i32 addrj :: values⟩,
          .select :: .load64 0 :: code, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hcont⟩
  iapply twp_select
    (selected := if (eAt M j).1 < (eAt M i).1 then Value.i32 addrj
      else Value.i32 addri) (select_flag _ _ _).symm
  by_cases h : (eAt M j).1 < (eAt M i).1
  · isimp only [cmpMin_pos h] at Hcont
    isimp only [if_pos h]
    iapply twp_pair_read (k := j) hj hlen hroom haddrj
    isplitl_exact Hbuf
    iintro Hbuf
    ihave Hgo := Hcont $$ Hbuf
    iexact Hgo
  · isimp only [cmpMin_neg h] at Hcont
    isimp only [if_neg h]
    iapply twp_pair_read (k := i) hi hlen hroom haddri
    isplitl_exact Hbuf
    iintro Hbuf
    ihave Hgo := Hcont $$ Hbuf
    iexact Hgo

set_option maxHeartbeats 2000000 in
/-- The `select` of the two slot offsets that feeds the `i64.load` of
the smaller entry. -/
private theorem twp_min_off [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v ci cj : UInt32} {M : List (UInt32 × UInt32)} {i j : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hi : i < M.length) (hj : j < M.length) (hlen : M.length = 9)
    (hroom : v.toNat + 72 < UInt32.size)
    (hci : ci = UInt32.ofNat (8 * i)) (hcj : cj = UInt32.ofNat (8 * j)) :
    iprop(Table.PairSlice 0 v M ∗
      (Table.PairSlice 0 v M -∗
        WP (.running ⟨⟨params, localValues,
              .i64 (Table.pairWord (Table.cmpMin keyLt (eAt M i)
                (eAt M j))) :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i32 (if (eAt M j).1 < (eAt M i).1 then 1 else 0) ::
              .i32 ci :: .i32 cj :: .i32 v :: values⟩,
          .select :: .add :: .load64 0 :: code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hcont⟩
  iapply twp_select
    (selected := if (eAt M j).1 < (eAt M i).1 then Value.i32 cj
      else Value.i32 ci) (select_flag _ _ _).symm
  by_cases h : (eAt M j).1 < (eAt M i).1
  · isimp only [cmpMin_pos h] at Hcont
    isimp only [if_pos h]
    iapply twp_add
    iapply twp_pair_read (k := j) hj hlen hroom
      (by rw [hcj]; exact UInt32.add_comm _ _)
    isplitl_exact Hbuf
    iintro Hbuf
    ihave Hgo := Hcont $$ Hbuf
    iexact Hgo
  · isimp only [cmpMin_neg h] at Hcont
    isimp only [if_neg h]
    iapply twp_add
    iapply twp_pair_read (k := i) hi hlen hroom
      (by rw [hci]; exact UInt32.add_comm _ _)
    isplitl_exact Hbuf
    iintro Hbuf
    ihave Hgo := Hcont $$ Hbuf
    iexact Hgo

set_option maxHeartbeats 2000000 in
/-- The `select` of the two slot addresses that feeds the `i32.load
offset=4` of the value of the greater entry. -/
private theorem twp_max_value [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addri addrj : UInt32} {M : List (UInt32 × UInt32)} {i j : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hi : i < M.length) (hj : j < M.length) (hlen : M.length = 9)
    (hroom : v.toNat + 72 < UInt32.size)
    (haddri : addri = v + UInt32.ofNat (8 * i))
    (haddrj : addrj = v + UInt32.ofNat (8 * j)) :
    iprop(Table.PairSlice 0 v M ∗
      (Table.PairSlice 0 v M -∗
        WP (.running ⟨⟨params, localValues,
              .i32 (Table.cmpMax keyLt (eAt M i) (eAt M j)).2 ::
                values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i32 (if (eAt M j).1 < (eAt M i).1 then 1 else 0) ::
              .i32 addrj :: .i32 addri :: values⟩,
          .select :: .load32 4 :: code, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hcont⟩
  iapply twp_select
    (selected := if (eAt M j).1 < (eAt M i).1 then Value.i32 addri
      else Value.i32 addrj) (select_flag _ _ _).symm
  by_cases h : (eAt M j).1 < (eAt M i).1
  · isimp only [cmpMax_pos h] at Hcont
    isimp only [if_pos h]
    iapply twp_value_read (k := i) hi hlen hroom haddri
    isplitl_exact Hbuf
    iintro Hbuf
    ihave Hgo := Hcont $$ Hbuf
    iexact Hgo
  · isimp only [cmpMax_neg h] at Hcont
    isimp only [if_neg h]
    iapply twp_value_read (k := j) hj hlen hroom haddrj
    isplitl_exact Hbuf
    iintro Hbuf
    ihave Hgo := Hcont $$ Hbuf
    iexact Hgo

/-! ## The registers

The network writes the locals 2, 3, 4, 6, 9 to 12, 14, 15, and 19 to 29.
`NetRegs` holds every other register of the body, which the region
carries unchanged.  Local 8 holds the region base and local 7 the region
length; the region reads both and writes neither.
-/

/-- The registers that the network does not touch. -/
structure NetRegs where
  buf : UInt32
  len : UInt32
  fp : UInt32
  reg7 : UInt32
  reg13 : UInt32
  pad16 : Value
  pad17 : Value
  pad18 : Value
  pad30 : Value
  pad31 : Value
  pad32 : Value
  pad33 : Value
  pad34 : Value
  pad35 : Value
  pad36 : Value
  pad37 : Value
  pad38 : Value

/-- The locals of the network, with the 21 live registers. -/
@[reducible] def netLocals (f : NetRegs)
    (v r2 r3 r4 r6 r9 r10 r11 : UInt32) (r12 : UInt64)
    (r14 r15 : UInt32) (r19 r20 : UInt64) (r21 r22 r23 r24 : UInt32)
    (r25 : UInt64) (r26 : UInt32) (r27 : UInt64) (r28 r29 : UInt32)
    (values : List Value) : Locals :=
  qsLocals f.buf f.len r2 r3 r4
    (.i32 f.fp :: .i32 r6 :: .i32 f.reg7 :: .i32 v :: .i32 r9 ::
      .i32 r10 :: .i32 r11 :: .i64 r12 :: .i32 f.reg13 :: .i32 r14 ::
      .i32 r15 :: f.pad16 :: f.pad17 :: f.pad18 :: .i64 r19 ::
      .i64 r20 :: .i32 r21 :: .i32 r22 :: .i32 r23 :: .i32 r24 ::
      .i64 r25 :: .i32 r26 :: .i64 r27 :: .i32 r28 :: .i32 r29 ::
      f.pad30 :: f.pad31 :: f.pad32 :: f.pad33 :: f.pad34 ::
      f.pad35 :: f.pad36 :: f.pad37 :: f.pad38 :: []) values

/-- The address of slot `k` of the region. -/
@[reducible] def sAddr (v : UInt32) (k : Nat) : UInt32 :=
  v + UInt32.ofNat (8 * k)

/-- The base is the address of slot 0. -/
private theorem addr_zero (v : UInt32) : v = sAddr v 0 := by
  show v = v + UInt32.ofNat 0
  rw [show UInt32.ofNat 0 = (0 : UInt32) from rfl, UInt32.add_zero]

/-- The address that `i32.add` of a slot offset and the base makes. -/
private theorem const_addr (v c : UInt32) (k : Nat)
    (hc : UInt32.ofNat (8 * k) = c) : c + v = sAddr v k := by
  rw [← hc]
  exact UInt32.add_comm _ _

/-- The `select` of the two keys keeps the key of the greater entry. -/
private theorem select_max_key (a b : UInt32 × UInt32) :
    Value.i32 (Table.cmpMax keyLt a b).1 =
      if (if a.1 < b.1 then (1 : UInt32) else 0) ≠ 0 then
        Value.i32 b.1 else Value.i32 a.1 := by
  rw [select_flag, ← cmpMax_key]
  by_cases h : a.1 < b.1 <;> simp [h]

/-- The `select` of the two entry words keeps the smaller entry. -/
private theorem select_min_pair (a b : UInt32 × UInt32) :
    Value.i64 (Table.pairWord (Table.cmpMin keyLt a b)) =
      if (if b.1 < a.1 then (1 : UInt32) else 0) ≠ 0 then
        Value.i64 (Table.pairWord b) else Value.i64 (Table.pairWord a) := by
  rw [select_flag]
  by_cases h : b.1 < a.1
  · rw [if_pos h, cmpMin_pos h]
  · rw [if_neg h, cmpMin_neg h]

/-- The two stores of the greater slot, in the order that the compiled
comparator makes them. -/
private theorem cmpSwap_pair (M : List (UInt32 × UInt32)) {i j : Nat}
    (hi : i < M.length) (hj : j < M.length) :
    (M.set i (Table.cmpMin keyLt (eAt M i) (eAt M j))).set j
        (Table.cmpMax keyLt (eAt M i) (eAt M j)) =
      Table.cmpSwap keyLt M (i, j) := by
  rw [eAt_eq M hi, eAt_eq M hj, Table.cmpSwap_eq_set_set keyLt M hi hj]

/-- The key store of a comparator, after the value store. -/
private theorem key_store_max (L : List (UInt32 × UInt32)) {j : Nat}
    (hj : j < L.length) (p : UInt32 × UInt32) :
    (L.set j ((eAt L j).1, p.2)).set j
        (p.1, (eAt (L.set j ((eAt L j).1, p.2)) j).2) = L.set j p := by
  rw [set_value_key L hj]

/-! ## The five parts of the network

Each part runs five whole comparators.  Part 4 also runs the two
instructions that write 9 into local 6.
-/

/-- The instruction index of the first instruction of each part. -/
private def sort9Bound : Nat → Nat
  | 0 => 0
  | 1 => 186
  | 2 => 341
  | 3 => 489
  | 4 => 635
  | _ => 776

/-- Part `k` of the network, for `k < 5`. -/
@[reducible] private def sort9Part (k : Nat) : Program :=
  (qsSort9.drop (sort9Bound k)).take (sort9Bound (k + 1) - sort9Bound k)

private theorem qsSort9_parts :
    qsSort9 =
      sort9Part 0 ++ sort9Part 1 ++ sort9Part 2 ++ sort9Part 3 ++
        sort9Part 4 := by
  rfl

/-- WAT 6233 to 6418. -/
private theorem sort9Part0_shape :
    sort9Part 0 =
      [Instruction.localGet 8, .const 24, .add, .localTee 9, .localGet 8,
        .localGet 8, .load32 24, .localTee 6, .localGet 8, .load32 0,
        .localTee 10, .ltU, .localTee 11, .select, .load64 0, .localSet 19,
        .localGet 8, .localGet 8, .localGet 9, .localGet 11, .select,
        .load32 4, .store32 28, .localGet 8, .localGet 6, .localGet 10,
        .localGet 6, .localGet 10, .gtU, .select, .localTee 3, .store32 24,
        .localGet 8, .localGet 19, .store64 0, .localGet 8, .const 8, .add,
        .localTee 14, .localGet 8, .const 56, .add, .localTee 15,
        .localGet 8, .load32 56, .localTee 6, .localGet 8, .load32 8,
        .localTee 10, .ltU, .localTee 11, .select, .load32 4, .localSet 2,
        .localGet 8, .localGet 8, .const 56, .const 8, .localGet 11, .select,
        .add, .load64 0, .localTee 20, .store64 8, .localGet 8, .localGet 2,
        .store32 60, .localGet 8, .localGet 6, .localGet 10, .localGet 6,
        .localGet 10, .gtU, .select, .localTee 2, .store32 56, .localGet 8,
        .const 40, .const 16, .localGet 8, .load32 40, .localTee 6,
        .localGet 8, .load32 16, .localTee 4, .ltU, .localTee 21, .select,
        .add, .load64 0, .localSet 12, .localGet 8, .localGet 8, .const 16,
        .add, .localTee 11, .localGet 8, .const 40, .add, .localTee 10,
        .localGet 21, .select, .load32 4, .store32 44, .localGet 8,
        .localGet 6, .localGet 4, .localGet 6, .localGet 4, .gtU, .select,
        .localTee 4, .store32 40, .localGet 8, .localGet 12, .store64 16,
        .localGet 8, .const 64, .const 32, .localGet 8, .load32 64,
        .localTee 22, .localGet 8, .load32 32, .localTee 23, .ltU,
        .localTee 24, .select, .add, .load64 0, .localSet 25, .localGet 8,
        .localGet 8, .const 32, .add, .localTee 6, .localGet 8, .const 64,
        .add, .localTee 21, .localGet 24, .select, .load32 4, .store32 68,
        .localGet 8, .localGet 22, .localGet 23, .localGet 22, .localGet 23,
        .gtU, .select, .localTee 22, .store32 64, .localGet 8, .localGet 25,
        .store64 32, .localGet 15, .localGet 8, .localGet 2, .localGet 19,
        .wrapI64, .localTee 23, .ltU, .localTee 24, .select, .load64 0,
        .localSet 19, .localGet 8, .localGet 8, .localGet 15, .localGet 24,
        .select, .load32 4, .store32 60, .localGet 8, .localGet 2,
        .localGet 23, .localGet 2, .localGet 23, .gtU, .select, .localTee 2,
        .store32 56, .localGet 8, .localGet 19, .store64 0] := by
  rfl

/-- WAT 6419 to 6573. -/
private theorem sort9Part1_shape :
    sort9Part 1 =
      [Instruction.localGet 8, .localGet 11, .localGet 6, .localGet 25,
        .wrapI64, .localTee 23, .localGet 12, .wrapI64, .localTee 24, .ltU,
        .localTee 26, .select, .load32 4, .store32 36, .localGet 8,
        .localGet 23, .localGet 24, .localGet 23, .localGet 24, .gtU,
        .select, .localTee 23, .store32 32, .localGet 8, .localGet 25,
        .localGet 12, .localGet 26, .select, .localTee 27, .store64 16,
        .localGet 8, .const 64, .const 24, .localGet 22, .localGet 3, .ltU,
        .localTee 24, .select, .add, .load64 0, .localSet 12, .localGet 8,
        .localGet 9, .localGet 21, .localGet 24, .select, .load32 4,
        .store32 68, .localGet 8, .localGet 22, .localGet 3, .localGet 22,
        .localGet 3, .gtU, .select, .localTee 22, .store32 64, .localGet 8,
        .localGet 12, .store64 24, .localGet 8, .const 48, .const 40,
        .localGet 8, .load32 48, .localTee 24, .localGet 4, .ltU,
        .localTee 26, .select, .add, .load64 0, .localSet 25, .localGet 8,
        .localGet 10, .localGet 8, .const 48, .add, .localTee 3,
        .localGet 26, .select, .load32 4, .store32 52, .localGet 8,
        .localGet 24, .localGet 4, .localGet 24, .localGet 4, .gtU, .select,
        .localTee 4, .store32 48, .localGet 8, .localGet 25, .store64 40,
        .localGet 8, .localGet 8, .localGet 11, .localGet 27, .wrapI64,
        .localTee 24, .localGet 19, .wrapI64, .localTee 26, .ltU,
        .localTee 28, .select, .load32 4, .store32 20, .localGet 8,
        .localGet 24, .localGet 26, .localGet 24, .localGet 26, .gtU,
        .select, .localTee 24, .store32 16, .localGet 8, .localGet 27,
        .localGet 19, .localGet 28, .select, .localTee 19, .store64 0,
        .localGet 8, .localGet 14, .localGet 9, .localGet 12, .wrapI64,
        .localTee 26, .localGet 20, .wrapI64, .localTee 28, .ltU,
        .localTee 29, .select, .load32 4, .store32 28, .localGet 8,
        .localGet 26, .localGet 28, .localGet 26, .localGet 28, .gtU,
        .select, .localTee 26, .store32 24, .localGet 8, .localGet 12,
        .localGet 20, .localGet 29, .select, .localTee 20, .store64 8] := by
  rfl

/-- WAT 6574 to 6721. -/
private theorem sort9Part2_shape :
    sort9Part 2 =
      [Instruction.localGet 8, .localGet 6, .localGet 10, .localGet 23,
        .localGet 25, .wrapI64, .localTee 28, .gtU, .localTee 29, .select,
        .load32 4, .store32 44, .localGet 8, .localGet 28, .localGet 23,
        .localGet 28, .localGet 23, .gtU, .select, .localTee 23, .store32 40,
        .localGet 8, .localGet 25, .localGet 8, .load64 32, .localGet 29,
        .select, .localTee 25, .store64 32, .localGet 8, .const 64,
        .const 56, .localGet 22, .localGet 2, .ltU, .localTee 28, .select,
        .add, .load64 0, .localSet 12, .localGet 8, .localGet 15,
        .localGet 21, .localGet 28, .select, .load32 4, .store32 68,
        .localGet 8, .localGet 22, .localGet 2, .localGet 22, .localGet 2,
        .gtU, .select, .localTee 2, .store32 64, .localGet 8, .localGet 12,
        .store64 56, .localGet 8, .localGet 14, .localGet 6, .localGet 25,
        .wrapI64, .localTee 22, .localGet 20, .wrapI64, .localTee 28, .ltU,
        .localTee 29, .select, .load32 4, .store32 36, .localGet 8,
        .localGet 22, .localGet 28, .localGet 22, .localGet 28, .gtU,
        .select, .localTee 22, .store32 32, .localGet 8, .localGet 25,
        .localGet 20, .localGet 29, .select, .localTee 20, .store64 8,
        .localGet 8, .const 48, .const 24, .localGet 4, .localGet 26, .ltU,
        .localTee 28, .select, .add, .load64 0, .localSet 25, .localGet 8,
        .localGet 9, .localGet 3, .localGet 28, .select, .load32 4,
        .store32 52, .localGet 8, .localGet 4, .localGet 26, .localGet 4,
        .localGet 26, .gtU, .select, .localTee 4, .store32 48, .localGet 8,
        .localGet 25, .store64 24, .localGet 8, .localGet 10, .localGet 15,
        .localGet 23, .localGet 12, .wrapI64, .localTee 26, .gtU,
        .localTee 28, .select, .load32 4, .store32 60, .localGet 8,
        .localGet 26, .localGet 23, .localGet 26, .localGet 23, .gtU,
        .select, .localTee 23, .store32 56, .localGet 8, .localGet 12,
        .localGet 8, .load64 40, .localGet 28, .select, .localTee 27,
        .store64 40] := by
  rfl

/-- WAT 6722 to 6867. -/
private theorem sort9Part3_shape :
    sort9Part 3 =
      [Instruction.localGet 8, .localGet 8, .localGet 14, .localGet 20,
        .wrapI64, .localTee 26, .localGet 19, .wrapI64, .localTee 28, .ltU,
        .localTee 29, .select, .load32 4, .store32 12, .localGet 8,
        .localGet 26, .localGet 28, .localGet 26, .localGet 28, .gtU,
        .select, .localTee 26, .store32 8, .localGet 8, .localGet 20,
        .localGet 19, .localGet 29, .select, .store64 0, .localGet 6,
        .localGet 11, .localGet 22, .localGet 24, .ltU, .localTee 28,
        .select, .load64 0, .localSet 12, .localGet 8, .localGet 11,
        .localGet 6, .localGet 28, .select, .load32 4, .store32 36,
        .localGet 8, .localGet 22, .localGet 24, .localGet 22, .localGet 24,
        .gtU, .select, .localTee 22, .store32 32, .localGet 8, .localGet 12,
        .store64 16, .localGet 8, .localGet 9, .localGet 10, .localGet 27,
        .wrapI64, .localTee 24, .localGet 25, .wrapI64, .localTee 28, .ltU,
        .localTee 29, .select, .load32 4, .store32 44, .localGet 8,
        .localGet 24, .localGet 28, .localGet 24, .localGet 28, .gtU,
        .select, .localTee 24, .store32 40, .localGet 8, .localGet 27,
        .localGet 25, .localGet 29, .select, .localTee 19, .store64 24,
        .localGet 8, .const 64, .const 48, .localGet 2, .localGet 4, .ltU,
        .localTee 28, .select, .add, .load64 0, .localSet 25, .localGet 8,
        .localGet 3, .localGet 21, .localGet 28, .select, .load32 4,
        .store32 68, .localGet 8, .localGet 2, .localGet 4, .localGet 2,
        .localGet 4, .gtU, .select, .store32 64, .localGet 8, .localGet 25,
        .store64 48, .localGet 8, .localGet 11, .localGet 9, .localGet 19,
        .wrapI64, .localTee 2, .localGet 12, .wrapI64, .localTee 4, .ltU,
        .localTee 21, .select, .load32 4, .store32 28, .localGet 8,
        .localGet 2, .localGet 4, .localGet 2, .localGet 4, .gtU, .select,
        .localTee 2, .store32 24, .localGet 8, .localGet 19, .localGet 12,
        .localGet 21, .select, .localTee 19, .store64 16] := by
  rfl

/-- WAT 6868 to 7008. -/
private theorem sort9Part4_shape :
    sort9Part 4 =
      [Instruction.localGet 10, .localGet 6, .localGet 24, .localGet 22,
        .ltU, .localTee 4, .select, .load64 0, .localSet 12, .localGet 8,
        .localGet 6, .localGet 10, .localGet 4, .select, .load32 4,
        .store32 44, .localGet 8, .localGet 24, .localGet 22, .localGet 24,
        .localGet 22, .gtU, .select, .localTee 4, .store32 40, .localGet 8,
        .localGet 12, .store64 32, .localGet 8, .load64 56, .localSet 20,
        .localGet 8, .localGet 3, .localGet 15, .localGet 23, .localGet 25,
        .wrapI64, .localTee 21, .ltU, .localTee 22, .select, .load32 4,
        .store32 60, .localGet 8, .localGet 23, .localGet 21, .localGet 23,
        .localGet 21, .gtU, .select, .store32 56, .localGet 8, .localGet 20,
        .localGet 25, .localGet 22, .select, .localTee 25, .store64 48,
        .localGet 8, .localGet 14, .localGet 11, .localGet 26, .localGet 19,
        .wrapI64, .localTee 15, .gtU, .localTee 21, .select, .load32 4,
        .store32 20, .localGet 8, .localGet 15, .localGet 26, .localGet 15,
        .localGet 26, .gtU, .select, .store32 16, .localGet 8, .localGet 19,
        .localGet 8, .load64 8, .localGet 21, .select, .store64 8,
        .localGet 8, .localGet 9, .localGet 6, .localGet 2, .localGet 12,
        .wrapI64, .localTee 11, .gtU, .localTee 15, .select, .load32 4,
        .store32 36, .localGet 8, .localGet 11, .localGet 2, .localGet 11,
        .localGet 2, .gtU, .select, .store32 32, .localGet 8, .localGet 12,
        .localGet 8, .load64 24, .localGet 15, .select, .store64 24,
        .localGet 8, .localGet 10, .localGet 3, .localGet 4, .localGet 25,
        .wrapI64, .localTee 6, .gtU, .localTee 9, .select, .load32 4,
        .store32 52, .localGet 8, .localGet 6, .localGet 4, .localGet 6,
        .localGet 4, .gtU, .select, .store32 48, .localGet 8, .localGet 25,
        .localGet 8, .load64 40, .localGet 9, .select, .store64 40, .const 9,
        .localSet 6] := by
  rfl


/-! ## The comparator block of each part -/

/-- The five comparators of part 0. -/
private def netBlock0 : List Table.Comparator :=
  [(0, 3), (1, 7), (2, 5), (4, 8), (0, 7)]

/-- The five comparators of part 1. -/
private def netBlock1 : List Table.Comparator :=
  [(2, 4), (3, 8), (5, 6), (0, 2), (1, 3)]

/-- The five comparators of part 2. -/
private def netBlock2 : List Table.Comparator :=
  [(4, 5), (7, 8), (1, 4), (3, 6), (5, 7)]

/-- The five comparators of part 3. -/
private def netBlock3 : List Table.Comparator :=
  [(0, 1), (2, 4), (3, 5), (6, 8), (2, 3)]

/-- The five comparators of part 4. -/
private def netBlock4 : List Table.Comparator :=
  [(4, 5), (6, 7), (1, 2), (3, 4), (5, 6)]


set_option maxHeartbeats 2000000 in
/-- Part 0 of the network, WAT 6233 to 6418.  It runs the
comparators 0 to 4 of `Table.sort9Net`. -/
private theorem twp_sort9_chunk0 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r2 r3 r4 r6 r9 r10 r11 r14 r15 r21 r22 r23 r24 r26 r28 r29 : UInt32} {r12
      r19 r20 r25 r27 : UInt64}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 9) (hroom : v.toNat + 72 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock0 M)
    (hcont : ∀ (y23 y24 y26 y28 y29 : UInt32) (y27 : UInt64),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨netLocals f v (eAt N 7).1 (eAt N 3).1 (eAt N 5).1 (sAddr v
        4) (sAddr v 3) (sAddr v 5) (sAddr v 2) (Table.pairWord (eAt N 2))
        (sAddr v 1) (sAddr v 7) (Table.pairWord (eAt N 0)) (Table.pairWord (eAt
        N 1)) (sAddr v 8) (eAt N 8).1 y23 y24 (Table.pairWord (eAt N 4)) y26
        y27 y28 y29 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨netLocals f v r2 r3 r4 r6 r9 r10 r11 r12 r14 r15 r19 r20
        r21 r22 r23 r24 r25 r26 r27 r28 r29 [],
        sort9Part 0 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (0, 3)) (1, 7)) (2, 5)) (4,
      8)) (0, 7)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort9Part0_shape, List.cons_append, List.nil_append]
  -- WAT 6233 to 6267: the comparator of the slots 0 and 3
  have ha0 : (0 : Nat) < M.length := by omega
  have hb0 : (3 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 24 3 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_key_load (k := 3) hb0 hlen hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_key_load (k := 0) ha0 hlen hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 0) (j := 3) ha0 hb0 hlen hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 0) (j := 3) ha0 hb0 hlen hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 3) (M := M) (value := (Table.cmpMax keyLt (eAt M
    0) (eAt M 3)).2) hb0 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 0) (eAt M
    3)).1) (select_max_key (eAt M 0) (eAt M 3))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 3) (M := M.set 3 ((eAt M 3).1, (Table.cmpMax keyLt
    (eAt M 0) (eAt M 3)).2)) (key := (Table.cmpMax keyLt (eAt M 0) (eAt M
    3)).1) (lt_set _ hb0) (len_set _ hlen) hroom rfl (key_store_max M hb0
    (Table.cmpMax keyLt (eAt M 0) (eAt M 3)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 0) (M := M.set 3 (Table.cmpMax keyLt (eAt M 0)
    (eAt M 3))) (q := (Table.cmpMin keyLt (eAt M 0) (eAt M 3))) (lt_set _ ha0)
    (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha0 hb0)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M 0 3 ha0 hb0, ← eAt_lo M 0 3 (by decide) ha0 hb0]
  set M1 := Table.cmpSwap keyLt M (0, 3) with hM1
  have hL1 : M1.length = 9 := by
    rw [hM1, Table.cmpSwap_length]; exact hlen
  -- WAT 6268 to 6308: the comparator of the slots 1 and 7
  have ha1 : (1 : Nat) < M1.length := by omega
  have hb1 : (7 : Nat) < M1.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 8 1 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 56 7 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_key_load (k := 7) hb1 hL1 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_key_load (k := 1) ha1 hL1 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 1) (j := 7) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_const twp_localGet]
  iapply twp_min_off (i := 1) (j := 7) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 1) (M := M1) (q := (Table.cmpMin keyLt (eAt M1 1)
    (eAt M1 7))) ha1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_value_store (k := 7) (M := M1.set 1 (Table.cmpMin keyLt (eAt M1 1)
    (eAt M1 7))) (value := (Table.cmpMax keyLt (eAt M1 1) (eAt M1 7)).2)
    (lt_set _ hb1) (len_set _ hL1) hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M1 1) (eAt
    M1 7)).1) (select_max_key (eAt M1 1) (eAt M1 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 7) (M := (M1.set 1 (Table.cmpMin keyLt (eAt M1 1)
    (eAt M1 7))).set 7 ((eAt (M1.set 1 (Table.cmpMin keyLt (eAt M1 1) (eAt M1
    7))) 7).1, (Table.cmpMax keyLt (eAt M1 1) (eAt M1 7)).2)) (key :=
    (Table.cmpMax keyLt (eAt M1 1) (eAt M1 7)).1) (lt_set _ (lt_set _ hb1))
    (len_set _ (len_set _ hL1)) hroom rfl ((key_store_max (M1.set 1
    (Table.cmpMin keyLt (eAt M1 1) (eAt M1 7))) (lt_set _ hb1) (Table.cmpMax
    keyLt (eAt M1 1) (eAt M1 7))).trans (cmpSwap_pair M1 ha1 hb1))
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M1 1 7 ha1 hb1, ← eAt_step M1 1 7 3 (by decide)
    (by decide), ← eAt_step M1 1 7 0 (by decide) (by decide), ← eAt_lo M1 1 7
    (by decide) ha1 hb1]
  set M2 := Table.cmpSwap keyLt M1 (1, 7) with hM2
  have hL2 : M2.length = 9 := by
    rw [hM2, Table.cmpSwap_length]; exact hL1
  -- WAT 6309 to 6348: the comparator of the slots 2 and 5
  have ha2 : (2 : Nat) < M2.length := by omega
  have hb2 : (5 : Nat) < M2.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet]
  iapply twp_key_load (k := 5) hb2 hL2 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_key_load (k := 2) ha2 hL2 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 2) (j := 5) ha2 hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  isimp only [const_addr v 16 2 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 40 5 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_max_value (i := 2) (j := 5) ha2 hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 5) (M := M2) (value := (Table.cmpMax keyLt (eAt
    M2 2) (eAt M2 5)).2) hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M2 2) (eAt
    M2 5)).1) (select_max_key (eAt M2 2) (eAt M2 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 5) (M := M2.set 5 ((eAt M2 5).1, (Table.cmpMax
    keyLt (eAt M2 2) (eAt M2 5)).2)) (key := (Table.cmpMax keyLt (eAt M2 2)
    (eAt M2 5)).1) (lt_set _ hb2) (len_set _ hL2) hroom rfl (key_store_max M2
    hb2 (Table.cmpMax keyLt (eAt M2 2) (eAt M2 5)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 2) (M := M2.set 5 (Table.cmpMax keyLt (eAt M2 2)
    (eAt M2 5))) (q := (Table.cmpMin keyLt (eAt M2 2) (eAt M2 5))) (lt_set _
    ha2) (len_set _ hL2) hroom rfl (cmpSwap_writes M2 (by decide) ha2 hb2)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M2 2 5 7 (by decide) (by decide), ← eAt_step M2 2 5 3
    (by decide) (by decide), ← eAt_hi M2 2 5 ha2 hb2, ← eAt_lo M2 2 5
    (by decide) ha2 hb2, ← eAt_step M2 2 5 0 (by decide) (by decide), ←
    eAt_step M2 2 5 1 (by decide) (by decide)]
  set M3 := Table.cmpSwap keyLt M2 (2, 5) with hM3
  have hL3 : M3.length = 9 := by
    rw [hM3, Table.cmpSwap_length]; exact hL2
  -- WAT 6349 to 6388: the comparator of the slots 4 and 8
  have ha3 : (4 : Nat) < M3.length := by omega
  have hb3 : (8 : Nat) < M3.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet]
  iapply twp_key_load (k := 8) hb3 hL3 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_key_load (k := 4) ha3 hL3 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 4) (j := 8) ha3 hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  isimp only [const_addr v 32 4 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 64 8 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_max_value (i := 4) (j := 8) ha3 hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 8) (M := M3) (value := (Table.cmpMax keyLt (eAt
    M3 4) (eAt M3 8)).2) hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M3 4) (eAt
    M3 8)).1) (select_max_key (eAt M3 4) (eAt M3 8))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 8) (M := M3.set 8 ((eAt M3 8).1, (Table.cmpMax
    keyLt (eAt M3 4) (eAt M3 8)).2)) (key := (Table.cmpMax keyLt (eAt M3 4)
    (eAt M3 8)).1) (lt_set _ hb3) (len_set _ hL3) hroom rfl (key_store_max M3
    hb3 (Table.cmpMax keyLt (eAt M3 4) (eAt M3 8)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 4) (M := M3.set 8 (Table.cmpMax keyLt (eAt M3 4)
    (eAt M3 8))) (q := (Table.cmpMin keyLt (eAt M3 4) (eAt M3 8))) (lt_set _
    ha3) (len_set _ hL3) hroom rfl (cmpSwap_writes M3 (by decide) ha3 hb3)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M3 4 8 7 (by decide) (by decide), ← eAt_step M3 4 8 3
    (by decide) (by decide), ← eAt_step M3 4 8 5 (by decide) (by decide), ←
    eAt_step M3 4 8 2 (by decide) (by decide), ← eAt_step M3 4 8 0 (by decide)
    (by decide), ← eAt_step M3 4 8 1 (by decide) (by decide), ← eAt_hi M3 4 8
    ha3 hb3, ← eAt_lo M3 4 8 (by decide) ha3 hb3]
  set M4 := Table.cmpSwap keyLt M3 (4, 8) with hM4
  have hL4 : M4.length = 9 := by
    rw [hM4, Table.cmpSwap_length]; exact hL3
  -- WAT 6389 to 6418: the comparator of the slots 0 and 7
  have ha4 : (0 : Nat) < M4.length := by omega
  have hb4 : (7 : Nat) < M4.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 0) (j := 7) ha4 hb4 hL4 hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 0) (j := 7) ha4 hb4 hL4 hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 7) (M := M4) (value := (Table.cmpMax keyLt (eAt
    M4 0) (eAt M4 7)).2) hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M4 0) (eAt
    M4 7)).1) (select_max_key (eAt M4 0) (eAt M4 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 7) (M := M4.set 7 ((eAt M4 7).1, (Table.cmpMax
    keyLt (eAt M4 0) (eAt M4 7)).2)) (key := (Table.cmpMax keyLt (eAt M4 0)
    (eAt M4 7)).1) (lt_set _ hb4) (len_set _ hL4) hroom rfl (key_store_max M4
    hb4 (Table.cmpMax keyLt (eAt M4 0) (eAt M4 7)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 0) (M := M4.set 7 (Table.cmpMax keyLt (eAt M4 0)
    (eAt M4 7))) (q := (Table.cmpMin keyLt (eAt M4 0) (eAt M4 7))) (lt_set _
    ha4) (len_set _ hL4) hroom rfl (cmpSwap_writes M4 (by decide) ha4 hb4)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M4 0 7 ha4 hb4, ← eAt_step M4 0 7 3 (by decide)
    (by decide), ← eAt_step M4 0 7 5 (by decide) (by decide), ← eAt_step M4 0 7
    2 (by decide) (by decide), ← eAt_lo M4 0 7 (by decide) ha4 hb4, ← eAt_step
    M4 0 7 1 (by decide) (by decide), ← eAt_step M4 0 7 8 (by decide)
    (by decide), ← eAt_step M4 0 7 4 (by decide) (by decide)]
  set M5 := Table.cmpSwap keyLt M4 (0, 7) with hM5
  have hL5 : M5.length = 9 := by
    rw [hM5, Table.cmpSwap_length]; exact hL4
  iapply (hcont _ _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 1 of the network, WAT 6419 to 6573.  It runs the
comparators 5 to 9 of `Table.sort9Net`. -/
private theorem twp_sort9_chunk1 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r23 r24 r26 r28 r29 : UInt32} {r27 : UInt64}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 9) (hroom : v.toNat + 72 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock1 M)
    (hcont : ∀ (y28 y29 : UInt32) (y12 y27 : UInt64), iprop(Table.PairSlice 0 v
      N ∗ Rest) ⊢
      WP (.running ⟨netLocals f v (eAt N 7).1 (sAddr v 6) (eAt N 6).1 (sAddr v
        4) (sAddr v 3) (sAddr v 5) (sAddr v 2) y12 (sAddr v 1) (sAddr v 7)
        (Table.pairWord (eAt N 0)) (Table.pairWord (eAt N 1)) (sAddr v 8) (eAt
        N 8).1 (eAt N 4).1 (eAt N 2).1 (Table.pairWord (eAt N 5)) (eAt N 3).1
        y27 y28 y29 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨netLocals f v (eAt M 7).1 (eAt M 3).1 (eAt M 5).1 (sAddr v
        4) (sAddr v 3) (sAddr v 5) (sAddr v 2) (Table.pairWord (eAt M 2))
        (sAddr v 1) (sAddr v 7) (Table.pairWord (eAt M 0)) (Table.pairWord (eAt
        M 1)) (sAddr v 8) (eAt M 8).1 r23 r24 (Table.pairWord (eAt M 4)) r26
        r27 r28 r29 [],
        sort9Part 1 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (2, 4)) (3, 8)) (5, 6)) (0,
      2)) (1, 3)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort9Part1_shape, List.cons_append, List.nil_append]
  -- WAT 6419 to 6448: the comparator of the slots 2 and 4
  have ha0 : (2 : Nat) < M.length := by omega
  have hb0 : (4 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 2) (j := 4) ha0 hb0 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 4) (M := M) (value := (Table.cmpMax keyLt (eAt M
    2) (eAt M 4)).2) hb0 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 2) (eAt M
    4)).1) (select_max_key (eAt M 2) (eAt M 4))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 4) (M := M.set 4 ((eAt M 4).1, (Table.cmpMax keyLt
    (eAt M 2) (eAt M 4)).2)) (key := (Table.cmpMax keyLt (eAt M 2) (eAt M
    4)).1) (lt_set _ hb0) (len_set _ hlen) hroom rfl (key_store_max M hb0
    (Table.cmpMax keyLt (eAt M 2) (eAt M 4)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M 2) (eAt M 4)))) (select_min_pair (eAt M 2) (eAt M 4))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 2) (M := M.set 4 (Table.cmpMax keyLt (eAt M 2)
    (eAt M 4))) (q := (Table.cmpMin keyLt (eAt M 2) (eAt M 4))) (lt_set _ ha0)
    (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha0 hb0)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M 2 4 7 (by decide) (by decide), ← eAt_step M 2 4 3
    (by decide) (by decide), ← eAt_step M 2 4 5 (by decide) (by decide), ←
    eAt_step M 2 4 0 (by decide) (by decide), ← eAt_step M 2 4 1 (by decide)
    (by decide), ← eAt_step M 2 4 8 (by decide) (by decide), ← eAt_hi M 2 4 ha0
    hb0, ← eAt_lo M 2 4 (by decide) ha0 hb0]
  set M1 := Table.cmpSwap keyLt M (2, 4) with hM1
  have hL1 : M1.length = 9 := by
    rw [hM1, Table.cmpSwap_length]; exact hlen
  -- WAT 6449 to 6478: the comparator of the slots 3 and 8
  have ha1 : (3 : Nat) < M1.length := by omega
  have hb1 : (8 : Nat) < M1.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet twp_localGet
    twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 3) (j := 8) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 3) (j := 8) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 8) (M := M1) (value := (Table.cmpMax keyLt (eAt
    M1 3) (eAt M1 8)).2) hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M1 3) (eAt
    M1 8)).1) (select_max_key (eAt M1 3) (eAt M1 8))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 8) (M := M1.set 8 ((eAt M1 8).1, (Table.cmpMax
    keyLt (eAt M1 3) (eAt M1 8)).2)) (key := (Table.cmpMax keyLt (eAt M1 3)
    (eAt M1 8)).1) (lt_set _ hb1) (len_set _ hL1) hroom rfl (key_store_max M1
    hb1 (Table.cmpMax keyLt (eAt M1 3) (eAt M1 8)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 3) (M := M1.set 8 (Table.cmpMax keyLt (eAt M1 3)
    (eAt M1 8))) (q := (Table.cmpMin keyLt (eAt M1 3) (eAt M1 8))) (lt_set _
    ha1) (len_set _ hL1) hroom rfl (cmpSwap_writes M1 (by decide) ha1 hb1)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M1 3 8 7 (by decide) (by decide), ← eAt_step M1 3 8 5
    (by decide) (by decide), ← eAt_lo M1 3 8 (by decide) ha1 hb1, ← eAt_step M1
    3 8 0 (by decide) (by decide), ← eAt_step M1 3 8 1 (by decide) (by decide),
    ← eAt_hi M1 3 8 ha1 hb1, ← eAt_step M1 3 8 4 (by decide) (by decide), ←
    eAt_step M1 3 8 2 (by decide) (by decide)]
  set M2 := Table.cmpSwap keyLt M1 (3, 8) with hM2
  have hL2 : M2.length = 9 := by
    rw [hM2, Table.cmpSwap_length]; exact hL1
  -- WAT 6479 to 6513: the comparator of the slots 5 and 6
  have ha2 : (5 : Nat) < M2.length := by omega
  have hb2 : (6 : Nat) < M2.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet]
  iapply twp_key_load (k := 6) hb2 hL2 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 5) (j := 6) ha2 hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const twp_add]
  isimp only [const_addr v 48 6 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_max_value (i := 5) (j := 6) ha2 hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 6) (M := M2) (value := (Table.cmpMax keyLt (eAt
    M2 5) (eAt M2 6)).2) hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M2 5) (eAt
    M2 6)).1) (select_max_key (eAt M2 5) (eAt M2 6))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 6) (M := M2.set 6 ((eAt M2 6).1, (Table.cmpMax
    keyLt (eAt M2 5) (eAt M2 6)).2)) (key := (Table.cmpMax keyLt (eAt M2 5)
    (eAt M2 6)).1) (lt_set _ hb2) (len_set _ hL2) hroom rfl (key_store_max M2
    hb2 (Table.cmpMax keyLt (eAt M2 5) (eAt M2 6)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 5) (M := M2.set 6 (Table.cmpMax keyLt (eAt M2 5)
    (eAt M2 6))) (q := (Table.cmpMin keyLt (eAt M2 5) (eAt M2 6))) (lt_set _
    ha2) (len_set _ hL2) hroom rfl (cmpSwap_writes M2 (by decide) ha2 hb2)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M2 5 6 7 (by decide) (by decide), ← eAt_hi M2 5 6 ha2
    hb2, ← eAt_step M2 5 6 3 (by decide) (by decide), ← eAt_step M2 5 6 0
    (by decide) (by decide), ← eAt_step M2 5 6 1 (by decide) (by decide), ←
    eAt_step M2 5 6 8 (by decide) (by decide), ← eAt_step M2 5 6 4 (by decide)
    (by decide), ← eAt_lo M2 5 6 (by decide) ha2 hb2, ← eAt_step M2 5 6 2
    (by decide) (by decide)]
  set M3 := Table.cmpSwap keyLt M2 (5, 6) with hM3
  have hL3 : M3.length = 9 := by
    rw [hM3, Table.cmpSwap_length]; exact hL2
  -- WAT 6514 to 6543: the comparator of the slots 0 and 2
  have ha3 : (0 : Nat) < M3.length := by omega
  have hb3 : (2 : Nat) < M3.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 0) (j := 2) ha3 hb3 hL3 hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 2) (M := M3) (value := (Table.cmpMax keyLt (eAt
    M3 0) (eAt M3 2)).2) hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M3 0) (eAt
    M3 2)).1) (select_max_key (eAt M3 0) (eAt M3 2))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 2) (M := M3.set 2 ((eAt M3 2).1, (Table.cmpMax
    keyLt (eAt M3 0) (eAt M3 2)).2)) (key := (Table.cmpMax keyLt (eAt M3 0)
    (eAt M3 2)).1) (lt_set _ hb3) (len_set _ hL3) hroom rfl (key_store_max M3
    hb3 (Table.cmpMax keyLt (eAt M3 0) (eAt M3 2)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M3 0) (eAt M3 2)))) (select_min_pair (eAt M3 0) (eAt M3 2))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 0) (M := M3.set 2 (Table.cmpMax keyLt (eAt M3 0)
    (eAt M3 2))) (q := (Table.cmpMin keyLt (eAt M3 0) (eAt M3 2))) (lt_set _
    ha3) (len_set _ hL3) hroom rfl (cmpSwap_writes M3 (by decide) ha3 hb3)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M3 0 2 7 (by decide) (by decide), ← eAt_step M3 0 2 6
    (by decide) (by decide), ← eAt_step M3 0 2 3 (by decide) (by decide), ←
    eAt_lo M3 0 2 (by decide) ha3 hb3, ← eAt_step M3 0 2 1 (by decide)
    (by decide), ← eAt_step M3 0 2 8 (by decide) (by decide), ← eAt_step M3 0 2
    4 (by decide) (by decide), ← eAt_hi M3 0 2 ha3 hb3, ← eAt_step M3 0 2 5
    (by decide) (by decide)]
  set M4 := Table.cmpSwap keyLt M3 (0, 2) with hM4
  have hL4 : M4.length = 9 := by
    rw [hM4, Table.cmpSwap_length]; exact hL3
  -- WAT 6544 to 6573: the comparator of the slots 1 and 3
  have ha4 : (1 : Nat) < M4.length := by omega
  have hb4 : (3 : Nat) < M4.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 1) (j := 3) ha4 hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 3) (M := M4) (value := (Table.cmpMax keyLt (eAt
    M4 1) (eAt M4 3)).2) hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M4 1) (eAt
    M4 3)).1) (select_max_key (eAt M4 1) (eAt M4 3))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 3) (M := M4.set 3 ((eAt M4 3).1, (Table.cmpMax
    keyLt (eAt M4 1) (eAt M4 3)).2)) (key := (Table.cmpMax keyLt (eAt M4 1)
    (eAt M4 3)).1) (lt_set _ hb4) (len_set _ hL4) hroom rfl (key_store_max M4
    hb4 (Table.cmpMax keyLt (eAt M4 1) (eAt M4 3)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M4 1) (eAt M4 3)))) (select_min_pair (eAt M4 1) (eAt M4 3))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 1) (M := M4.set 3 (Table.cmpMax keyLt (eAt M4 1)
    (eAt M4 3))) (q := (Table.cmpMin keyLt (eAt M4 1) (eAt M4 3))) (lt_set _
    ha4) (len_set _ hL4) hroom rfl (cmpSwap_writes M4 (by decide) ha4 hb4)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M4 1 3 7 (by decide) (by decide), ← eAt_step M4 1 3 6
    (by decide) (by decide), ← eAt_step M4 1 3 0 (by decide) (by decide), ←
    eAt_lo M4 1 3 (by decide) ha4 hb4, ← eAt_step M4 1 3 8 (by decide)
    (by decide), ← eAt_step M4 1 3 4 (by decide) (by decide), ← eAt_step M4 1 3
    2 (by decide) (by decide), ← eAt_step M4 1 3 5 (by decide) (by decide), ←
    eAt_hi M4 1 3 ha4 hb4]
  set M5 := Table.cmpSwap keyLt M4 (1, 3) with hM5
  have hL5 : M5.length = 9 := by
    rw [hM5, Table.cmpSwap_length]; exact hL4
  iapply (hcont _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 2 of the network, WAT 6574 to 6721.  It runs the
comparators 10 to 14 of `Table.sort9Net`. -/
private theorem twp_sort9_chunk2 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r28 r29 : UInt32} {r12 r27 : UInt64}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 9) (hroom : v.toNat + 72 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock2 M)
    (hcont : ∀ (y26 y28 y29 : UInt32) (y12 : UInt64), iprop(Table.PairSlice 0 v
      N ∗ Rest) ⊢
      WP (.running ⟨netLocals f v (eAt N 8).1 (sAddr v 6) (eAt N 6).1 (sAddr v
        4) (sAddr v 3) (sAddr v 5) (sAddr v 2) y12 (sAddr v 1) (sAddr v 7)
        (Table.pairWord (eAt N 0)) (Table.pairWord (eAt N 1)) (sAddr v 8) (eAt
        N 4).1 (eAt N 7).1 (eAt N 2).1 (Table.pairWord (eAt N 3)) y26
        (Table.pairWord (eAt N 5)) y28 y29 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨netLocals f v (eAt M 7).1 (sAddr v 6) (eAt M 6).1 (sAddr v
        4) (sAddr v 3) (sAddr v 5) (sAddr v 2) r12 (sAddr v 1) (sAddr v 7)
        (Table.pairWord (eAt M 0)) (Table.pairWord (eAt M 1)) (sAddr v 8) (eAt
        M 8).1 (eAt M 4).1 (eAt M 2).1 (Table.pairWord (eAt M 5)) (eAt M 3).1
        r27 r28 r29 [],
        sort9Part 2 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (4, 5)) (7, 8)) (1, 4)) (3,
      6)) (5, 7)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort9Part2_shape, List.cons_append, List.nil_append]
  -- WAT 6574 to 6602: the comparator of the slots 4 and 5
  have ha0 : (4 : Nat) < M.length := by omega
  have hb0 : (5 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 4) (j := 5) ha0 hb0 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 5) (M := M) (value := (Table.cmpMax keyLt (eAt M
    4) (eAt M 5)).2) hb0 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 4) (eAt M
    5)).1) (select_max_key (eAt M 4) (eAt M 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 5) (M := M.set 5 ((eAt M 5).1, (Table.cmpMax keyLt
    (eAt M 4) (eAt M 5)).2)) (key := (Table.cmpMax keyLt (eAt M 4) (eAt M
    5)).1) (lt_set _ hb0) (len_set _ hlen) hroom rfl (key_store_max M hb0
    (Table.cmpMax keyLt (eAt M 4) (eAt M 5)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 4) (M := M.set 5 (Table.cmpMax keyLt (eAt M 4)
    (eAt M 5))) (lt_set _ ha0) (len_set _ hlen) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M 5 4 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M 4) (eAt M 5)))) (select_min_pair (eAt M 4) (eAt M 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 4) (M := M.set 5 (Table.cmpMax keyLt (eAt M 4)
    (eAt M 5))) (q := (Table.cmpMin keyLt (eAt M 4) (eAt M 5))) (lt_set _ ha0)
    (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha0 hb0)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M 4 5 7 (by decide) (by decide), ← eAt_step M 4 5 6
    (by decide) (by decide), ← eAt_step M 4 5 0 (by decide) (by decide), ←
    eAt_step M 4 5 1 (by decide) (by decide), ← eAt_step M 4 5 8 (by decide)
    (by decide), ← eAt_hi M 4 5 ha0 hb0, ← eAt_step M 4 5 2 (by decide)
    (by decide), ← eAt_lo M 4 5 (by decide) ha0 hb0, ← eAt_step M 4 5 3
    (by decide) (by decide)]
  set M1 := Table.cmpSwap keyLt M (4, 5) with hM1
  have hL1 : M1.length = 9 := by
    rw [hM1, Table.cmpSwap_length]; exact hlen
  -- WAT 6603 to 6632: the comparator of the slots 7 and 8
  have ha1 : (7 : Nat) < M1.length := by omega
  have hb1 : (8 : Nat) < M1.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet twp_localGet
    twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 7) (j := 8) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 7) (j := 8) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 8) (M := M1) (value := (Table.cmpMax keyLt (eAt
    M1 7) (eAt M1 8)).2) hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M1 7) (eAt
    M1 8)).1) (select_max_key (eAt M1 7) (eAt M1 8))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 8) (M := M1.set 8 ((eAt M1 8).1, (Table.cmpMax
    keyLt (eAt M1 7) (eAt M1 8)).2)) (key := (Table.cmpMax keyLt (eAt M1 7)
    (eAt M1 8)).1) (lt_set _ hb1) (len_set _ hL1) hroom rfl (key_store_max M1
    hb1 (Table.cmpMax keyLt (eAt M1 7) (eAt M1 8)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 7) (M := M1.set 8 (Table.cmpMax keyLt (eAt M1 7)
    (eAt M1 8))) (q := (Table.cmpMin keyLt (eAt M1 7) (eAt M1 8))) (lt_set _
    ha1) (len_set _ hL1) hroom rfl (cmpSwap_writes M1 (by decide) ha1 hb1)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M1 7 8 ha1 hb1, ← eAt_step M1 7 8 6 (by decide)
    (by decide), ← eAt_lo M1 7 8 (by decide) ha1 hb1, ← eAt_step M1 7 8 0
    (by decide) (by decide), ← eAt_step M1 7 8 1 (by decide) (by decide), ←
    eAt_step M1 7 8 5 (by decide) (by decide), ← eAt_step M1 7 8 2 (by decide)
    (by decide), ← eAt_step M1 7 8 4 (by decide) (by decide), ← eAt_step M1 7 8
    3 (by decide) (by decide)]
  set M2 := Table.cmpSwap keyLt M1 (7, 8) with hM2
  have hL2 : M2.length = 9 := by
    rw [hM2, Table.cmpSwap_length]; exact hL1
  -- WAT 6633 to 6662: the comparator of the slots 1 and 4
  have ha2 : (1 : Nat) < M2.length := by omega
  have hb2 : (4 : Nat) < M2.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 1) (j := 4) ha2 hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 4) (M := M2) (value := (Table.cmpMax keyLt (eAt
    M2 1) (eAt M2 4)).2) hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M2 1) (eAt
    M2 4)).1) (select_max_key (eAt M2 1) (eAt M2 4))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 4) (M := M2.set 4 ((eAt M2 4).1, (Table.cmpMax
    keyLt (eAt M2 1) (eAt M2 4)).2)) (key := (Table.cmpMax keyLt (eAt M2 1)
    (eAt M2 4)).1) (lt_set _ hb2) (len_set _ hL2) hroom rfl (key_store_max M2
    hb2 (Table.cmpMax keyLt (eAt M2 1) (eAt M2 4)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M2 1) (eAt M2 4)))) (select_min_pair (eAt M2 1) (eAt M2 4))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 1) (M := M2.set 4 (Table.cmpMax keyLt (eAt M2 1)
    (eAt M2 4))) (q := (Table.cmpMin keyLt (eAt M2 1) (eAt M2 4))) (lt_set _
    ha2) (len_set _ hL2) hroom rfl (cmpSwap_writes M2 (by decide) ha2 hb2)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M2 1 4 8 (by decide) (by decide), ← eAt_step M2 1 4 6
    (by decide) (by decide), ← eAt_step M2 1 4 7 (by decide) (by decide), ←
    eAt_step M2 1 4 0 (by decide) (by decide), ← eAt_lo M2 1 4 (by decide) ha2
    hb2, ← eAt_hi M2 1 4 ha2 hb2, ← eAt_step M2 1 4 5 (by decide) (by decide),
    ← eAt_step M2 1 4 2 (by decide) (by decide), ← eAt_step M2 1 4 3
    (by decide) (by decide)]
  set M3 := Table.cmpSwap keyLt M2 (1, 4) with hM3
  have hL3 : M3.length = 9 := by
    rw [hM3, Table.cmpSwap_length]; exact hL2
  -- WAT 6663 to 6692: the comparator of the slots 3 and 6
  have ha3 : (3 : Nat) < M3.length := by omega
  have hb3 : (6 : Nat) < M3.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet twp_localGet
    twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 3) (j := 6) ha3 hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 3) (j := 6) ha3 hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 6) (M := M3) (value := (Table.cmpMax keyLt (eAt
    M3 3) (eAt M3 6)).2) hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M3 3) (eAt
    M3 6)).1) (select_max_key (eAt M3 3) (eAt M3 6))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 6) (M := M3.set 6 ((eAt M3 6).1, (Table.cmpMax
    keyLt (eAt M3 3) (eAt M3 6)).2)) (key := (Table.cmpMax keyLt (eAt M3 3)
    (eAt M3 6)).1) (lt_set _ hb3) (len_set _ hL3) hroom rfl (key_store_max M3
    hb3 (Table.cmpMax keyLt (eAt M3 3) (eAt M3 6)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 3) (M := M3.set 6 (Table.cmpMax keyLt (eAt M3 3)
    (eAt M3 6))) (q := (Table.cmpMin keyLt (eAt M3 3) (eAt M3 6))) (lt_set _
    ha3) (len_set _ hL3) hroom rfl (cmpSwap_writes M3 (by decide) ha3 hb3)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M3 3 6 8 (by decide) (by decide), ← eAt_hi M3 3 6 ha3
    hb3, ← eAt_step M3 3 6 7 (by decide) (by decide), ← eAt_step M3 3 6 0
    (by decide) (by decide), ← eAt_step M3 3 6 1 (by decide) (by decide), ←
    eAt_step M3 3 6 4 (by decide) (by decide), ← eAt_step M3 3 6 5 (by decide)
    (by decide), ← eAt_step M3 3 6 2 (by decide) (by decide), ← eAt_lo M3 3 6
    (by decide) ha3 hb3]
  set M4 := Table.cmpSwap keyLt M3 (3, 6) with hM4
  have hL4 : M4.length = 9 := by
    rw [hM4, Table.cmpSwap_length]; exact hL3
  -- WAT 6693 to 6721: the comparator of the slots 5 and 7
  have ha4 : (5 : Nat) < M4.length := by omega
  have hb4 : (7 : Nat) < M4.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 5) (j := 7) ha4 hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 7) (M := M4) (value := (Table.cmpMax keyLt (eAt
    M4 5) (eAt M4 7)).2) hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M4 5) (eAt
    M4 7)).1) (select_max_key (eAt M4 5) (eAt M4 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 7) (M := M4.set 7 ((eAt M4 7).1, (Table.cmpMax
    keyLt (eAt M4 5) (eAt M4 7)).2)) (key := (Table.cmpMax keyLt (eAt M4 5)
    (eAt M4 7)).1) (lt_set _ hb4) (len_set _ hL4) hroom rfl (key_store_max M4
    hb4 (Table.cmpMax keyLt (eAt M4 5) (eAt M4 7)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 5) (M := M4.set 7 (Table.cmpMax keyLt (eAt M4 5)
    (eAt M4 7))) (lt_set _ ha4) (len_set _ hL4) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M4 7 5 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M4 5) (eAt M4 7)))) (select_min_pair (eAt M4 5) (eAt M4 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 5) (M := M4.set 7 (Table.cmpMax keyLt (eAt M4 5)
    (eAt M4 7))) (q := (Table.cmpMin keyLt (eAt M4 5) (eAt M4 7))) (lt_set _
    ha4) (len_set _ hL4) hroom rfl (cmpSwap_writes M4 (by decide) ha4 hb4)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M4 5 7 8 (by decide) (by decide), ← eAt_step M4 5 7 6
    (by decide) (by decide), ← eAt_step M4 5 7 0 (by decide) (by decide), ←
    eAt_step M4 5 7 1 (by decide) (by decide), ← eAt_step M4 5 7 4 (by decide)
    (by decide), ← eAt_hi M4 5 7 ha4 hb4, ← eAt_step M4 5 7 2 (by decide)
    (by decide), ← eAt_step M4 5 7 3 (by decide) (by decide), ← eAt_lo M4 5 7
    (by decide) ha4 hb4]
  set M5 := Table.cmpSwap keyLt M4 (5, 7) with hM5
  have hL5 : M5.length = 9 := by
    rw [hM5, Table.cmpSwap_length]; exact hL4
  iapply (hcont _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 3 of the network, WAT 6722 to 6867.  It runs the
comparators 15 to 19 of `Table.sort9Net`. -/
private theorem twp_sort9_chunk3 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r26 r28 r29 : UInt32} {r12 : UInt64}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 9) (hroom : v.toNat + 72 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock3 M)
    (hcont : ∀ (y4 y21 y28 y29 : UInt32) (y12 y20 y27 : UInt64),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨netLocals f v (eAt N 3).1 (sAddr v 6) y4 (sAddr v 4) (sAddr
        v 3) (sAddr v 5) (sAddr v 2) y12 (sAddr v 1) (sAddr v 7)
        (Table.pairWord (eAt N 2)) y20 y21 (eAt N 4).1 (eAt N 7).1 (eAt N 5).1
        (Table.pairWord (eAt N 6)) (eAt N 1).1 y27 y28 y29 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨netLocals f v (eAt M 8).1 (sAddr v 6) (eAt M 6).1 (sAddr v
        4) (sAddr v 3) (sAddr v 5) (sAddr v 2) r12 (sAddr v 1) (sAddr v 7)
        (Table.pairWord (eAt M 0)) (Table.pairWord (eAt M 1)) (sAddr v 8) (eAt
        M 4).1 (eAt M 7).1 (eAt M 2).1 (Table.pairWord (eAt M 3)) r26
        (Table.pairWord (eAt M 5)) r28 r29 [],
        sort9Part 3 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (0, 1)) (2, 4)) (3, 5)) (6,
      8)) (2, 3)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort9Part3_shape, List.cons_append, List.nil_append]
  -- WAT 6722 to 6750: the comparator of the slots 0 and 1
  have ha0 : (0 : Nat) < M.length := by omega
  have hb0 : (1 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 0) (j := 1) ha0 hb0 hlen hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 1) (M := M) (value := (Table.cmpMax keyLt (eAt M
    0) (eAt M 1)).2) hb0 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 0) (eAt M
    1)).1) (select_max_key (eAt M 0) (eAt M 1))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 1) (M := M.set 1 ((eAt M 1).1, (Table.cmpMax keyLt
    (eAt M 0) (eAt M 1)).2)) (key := (Table.cmpMax keyLt (eAt M 0) (eAt M
    1)).1) (lt_set _ hb0) (len_set _ hlen) hroom rfl (key_store_max M hb0
    (Table.cmpMax keyLt (eAt M 0) (eAt M 1)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M 0) (eAt M 1)))) (select_min_pair (eAt M 0) (eAt M 1))
  iapply twp_pair_store (k := 0) (M := M.set 1 (Table.cmpMax keyLt (eAt M 0)
    (eAt M 1))) (q := (Table.cmpMin keyLt (eAt M 0) (eAt M 1))) (lt_set _ ha0)
    (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha0 hb0)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M 0 1 8 (by decide) (by decide), ← eAt_step M 0 1 6
    (by decide) (by decide), ← eAt_step M 0 1 4 (by decide) (by decide), ←
    eAt_step M 0 1 7 (by decide) (by decide), ← eAt_step M 0 1 2 (by decide)
    (by decide), ← eAt_step M 0 1 3 (by decide) (by decide), ← eAt_hi M 0 1 ha0
    hb0, ← eAt_step M 0 1 5 (by decide) (by decide)]
  set M1 := Table.cmpSwap keyLt M (0, 1) with hM1
  have hL1 : M1.length = 9 := by
    rw [hM1, Table.cmpSwap_length]; exact hlen
  -- WAT 6751 to 6778: the comparator of the slots 2 and 4
  have ha1 : (2 : Nat) < M1.length := by omega
  have hb1 : (4 : Nat) < M1.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 2) (j := 4) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 2) (j := 4) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 4) (M := M1) (value := (Table.cmpMax keyLt (eAt
    M1 2) (eAt M1 4)).2) hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M1 2) (eAt
    M1 4)).1) (select_max_key (eAt M1 2) (eAt M1 4))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 4) (M := M1.set 4 ((eAt M1 4).1, (Table.cmpMax
    keyLt (eAt M1 2) (eAt M1 4)).2)) (key := (Table.cmpMax keyLt (eAt M1 2)
    (eAt M1 4)).1) (lt_set _ hb1) (len_set _ hL1) hroom rfl (key_store_max M1
    hb1 (Table.cmpMax keyLt (eAt M1 2) (eAt M1 4)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 2) (M := M1.set 4 (Table.cmpMax keyLt (eAt M1 2)
    (eAt M1 4))) (q := (Table.cmpMin keyLt (eAt M1 2) (eAt M1 4))) (lt_set _
    ha1) (len_set _ hL1) hroom rfl (cmpSwap_writes M1 (by decide) ha1 hb1)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M1 2 4 8 (by decide) (by decide), ← eAt_step M1 2 4 6
    (by decide) (by decide), ← eAt_lo M1 2 4 (by decide) ha1 hb1, ← eAt_hi M1 2
    4 ha1 hb1, ← eAt_step M1 2 4 7 (by decide) (by decide), ← eAt_step M1 2 4 3
    (by decide) (by decide), ← eAt_step M1 2 4 1 (by decide) (by decide), ←
    eAt_step M1 2 4 5 (by decide) (by decide)]
  set M2 := Table.cmpSwap keyLt M1 (2, 4) with hM2
  have hL2 : M2.length = 9 := by
    rw [hM2, Table.cmpSwap_length]; exact hL1
  -- WAT 6779 to 6808: the comparator of the slots 3 and 5
  have ha2 : (3 : Nat) < M2.length := by omega
  have hb2 : (5 : Nat) < M2.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 3) (j := 5) ha2 hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 5) (M := M2) (value := (Table.cmpMax keyLt (eAt
    M2 3) (eAt M2 5)).2) hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M2 3) (eAt
    M2 5)).1) (select_max_key (eAt M2 3) (eAt M2 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 5) (M := M2.set 5 ((eAt M2 5).1, (Table.cmpMax
    keyLt (eAt M2 3) (eAt M2 5)).2)) (key := (Table.cmpMax keyLt (eAt M2 3)
    (eAt M2 5)).1) (lt_set _ hb2) (len_set _ hL2) hroom rfl (key_store_max M2
    hb2 (Table.cmpMax keyLt (eAt M2 3) (eAt M2 5)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M2 3) (eAt M2 5)))) (select_min_pair (eAt M2 3) (eAt M2 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 3) (M := M2.set 5 (Table.cmpMax keyLt (eAt M2 3)
    (eAt M2 5))) (q := (Table.cmpMin keyLt (eAt M2 3) (eAt M2 5))) (lt_set _
    ha2) (len_set _ hL2) hroom rfl (cmpSwap_writes M2 (by decide) ha2 hb2)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M2 3 5 8 (by decide) (by decide), ← eAt_step M2 3 5 6
    (by decide) (by decide), ← eAt_step M2 3 5 2 (by decide) (by decide), ←
    eAt_lo M2 3 5 (by decide) ha2 hb2, ← eAt_step M2 3 5 4 (by decide)
    (by decide), ← eAt_step M2 3 5 7 (by decide) (by decide), ← eAt_hi M2 3 5
    ha2 hb2, ← eAt_step M2 3 5 1 (by decide) (by decide)]
  set M3 := Table.cmpSwap keyLt M2 (3, 5) with hM3
  have hL3 : M3.length = 9 := by
    rw [hM3, Table.cmpSwap_length]; exact hL2
  -- WAT 6809 to 6837: the comparator of the slots 6 and 8
  have ha3 : (6 : Nat) < M3.length := by omega
  have hb3 : (8 : Nat) < M3.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet twp_localGet
    twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 6) (j := 8) ha3 hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 6) (j := 8) ha3 hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 8) (M := M3) (value := (Table.cmpMax keyLt (eAt
    M3 6) (eAt M3 8)).2) hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M3 6) (eAt
    M3 8)).1) (select_max_key (eAt M3 6) (eAt M3 8))
  iapply twp_key_store (k := 8) (M := M3.set 8 ((eAt M3 8).1, (Table.cmpMax
    keyLt (eAt M3 6) (eAt M3 8)).2)) (key := (Table.cmpMax keyLt (eAt M3 6)
    (eAt M3 8)).1) (lt_set _ hb3) (len_set _ hL3) hroom rfl (key_store_max M3
    hb3 (Table.cmpMax keyLt (eAt M3 6) (eAt M3 8)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 6) (M := M3.set 8 (Table.cmpMax keyLt (eAt M3 6)
    (eAt M3 8))) (q := (Table.cmpMin keyLt (eAt M3 6) (eAt M3 8))) (lt_set _
    ha3) (len_set _ hL3) hroom rfl (cmpSwap_writes M3 (by decide) ha3 hb3)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M3 6 8 2 (by decide) (by decide), ← eAt_step M3 6 8 3
    (by decide) (by decide), ← eAt_step M3 6 8 4 (by decide) (by decide), ←
    eAt_step M3 6 8 7 (by decide) (by decide), ← eAt_step M3 6 8 5 (by decide)
    (by decide), ← eAt_lo M3 6 8 (by decide) ha3 hb3, ← eAt_step M3 6 8 1
    (by decide) (by decide)]
  set M4 := Table.cmpSwap keyLt M3 (6, 8) with hM4
  have hL4 : M4.length = 9 := by
    rw [hM4, Table.cmpSwap_length]; exact hL3
  -- WAT 6838 to 6867: the comparator of the slots 2 and 3
  have ha4 : (2 : Nat) < M4.length := by omega
  have hb4 : (3 : Nat) < M4.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 2) (j := 3) ha4 hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 3) (M := M4) (value := (Table.cmpMax keyLt (eAt
    M4 2) (eAt M4 3)).2) hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M4 2) (eAt
    M4 3)).1) (select_max_key (eAt M4 2) (eAt M4 3))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 3) (M := M4.set 3 ((eAt M4 3).1, (Table.cmpMax
    keyLt (eAt M4 2) (eAt M4 3)).2)) (key := (Table.cmpMax keyLt (eAt M4 2)
    (eAt M4 3)).1) (lt_set _ hb4) (len_set _ hL4) hroom rfl (key_store_max M4
    hb4 (Table.cmpMax keyLt (eAt M4 2) (eAt M4 3)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M4 2) (eAt M4 3)))) (select_min_pair (eAt M4 2) (eAt M4 3))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 2) (M := M4.set 3 (Table.cmpMax keyLt (eAt M4 2)
    (eAt M4 3))) (q := (Table.cmpMin keyLt (eAt M4 2) (eAt M4 3))) (lt_set _
    ha4) (len_set _ hL4) hroom rfl (cmpSwap_writes M4 (by decide) ha4 hb4)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M4 2 3 ha4 hb4, ← eAt_lo M4 2 3 (by decide) ha4 hb4, ←
    eAt_step M4 2 3 4 (by decide) (by decide), ← eAt_step M4 2 3 7 (by decide)
    (by decide), ← eAt_step M4 2 3 5 (by decide) (by decide), ← eAt_step M4 2 3
    6 (by decide) (by decide), ← eAt_step M4 2 3 1 (by decide) (by decide)]
  set M5 := Table.cmpSwap keyLt M4 (2, 3) with hM5
  have hL5 : M5.length = 9 := by
    rw [hM5, Table.cmpSwap_length]; exact hL4
  iapply (hcont _ _ _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 4 of the network, WAT 6868 to 7006.  It runs the
comparators 20 to 24 of `Table.sort9Net`. -/
private theorem twp_sort9_chunk4 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r4 r21 r28 r29 : UInt32} {r12 r20 r27 : UInt64}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 9) (hroom : v.toNat + 72 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock4 M)
    (hcont : ∀ (y2 y3 y4 y9 y10 y11 y14 y15 y21 y22 y23 y24 y26 y28 y29 :
      UInt32) (y12 y19 y20 y25 y27 : UInt64), iprop(Table.PairSlice 0 v N ∗
      Rest) ⊢
      WP (.running ⟨netLocals f v y2 y3 y4 9 y9 y10 y11 y12 y14 y15 y19 y20 y21
        y22 y23 y24 y25 y26 y27 y28 y29 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨netLocals f v (eAt M 3).1 (sAddr v 6) r4 (sAddr v 4) (sAddr
        v 3) (sAddr v 5) (sAddr v 2) r12 (sAddr v 1) (sAddr v 7)
        (Table.pairWord (eAt M 2)) r20 r21 (eAt M 4).1 (eAt M 7).1 (eAt M 5).1
        (Table.pairWord (eAt M 6)) (eAt M 1).1 r27 r28 r29 [],
        sort9Part 4 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (4, 5)) (6, 7)) (1, 2)) (3,
      4)) (5, 6)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort9Part4_shape, List.cons_append, List.nil_append]
  -- WAT 6868 to 6895: the comparator of the slots 4 and 5
  have ha0 : (4 : Nat) < M.length := by omega
  have hb0 : (5 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 4) (j := 5) ha0 hb0 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 4) (j := 5) ha0 hb0 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 5) (M := M) (value := (Table.cmpMax keyLt (eAt M
    4) (eAt M 5)).2) hb0 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 4) (eAt M
    5)).1) (select_max_key (eAt M 4) (eAt M 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 5) (M := M.set 5 ((eAt M 5).1, (Table.cmpMax keyLt
    (eAt M 4) (eAt M 5)).2)) (key := (Table.cmpMax keyLt (eAt M 4) (eAt M
    5)).1) (lt_set _ hb0) (len_set _ hlen) hroom rfl (key_store_max M hb0
    (Table.cmpMax keyLt (eAt M 4) (eAt M 5)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 4) (M := M.set 5 (Table.cmpMax keyLt (eAt M 4)
    (eAt M 5))) (q := (Table.cmpMin keyLt (eAt M 4) (eAt M 5))) (lt_set _ ha0)
    (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha0 hb0)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M 4 5 3 (by decide) (by decide), ← eAt_hi M 4 5 ha0
    hb0, ← eAt_lo M 4 5 (by decide) ha0 hb0, ← eAt_step M 4 5 2 (by decide)
    (by decide), ← eAt_step M 4 5 7 (by decide) (by decide), ← eAt_step M 4 5 6
    (by decide) (by decide), ← eAt_step M 4 5 1 (by decide) (by decide)]
  set M1 := Table.cmpSwap keyLt M (4, 5) with hM1
  have hL1 : M1.length = 9 := by
    rw [hM1, Table.cmpSwap_length]; exact hlen
  -- WAT 6896 to 6925: the comparator of the slots 6 and 7
  have ha1 : (6 : Nat) < M1.length := by omega
  have hb1 : (7 : Nat) < M1.length := by omega
  wasm_twp_pures [twp_localGet]
  iapply twp_pair_load (k := 7) hb1 hL1 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 6) (j := 7) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 7) (M := M1) (value := (Table.cmpMax keyLt (eAt
    M1 6) (eAt M1 7)).2) hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M1 6) (eAt
    M1 7)).1) (select_max_key (eAt M1 6) (eAt M1 7))
  iapply twp_key_store (k := 7) (M := M1.set 7 ((eAt M1 7).1, (Table.cmpMax
    keyLt (eAt M1 6) (eAt M1 7)).2)) (key := (Table.cmpMax keyLt (eAt M1 6)
    (eAt M1 7)).1) (lt_set _ hb1) (len_set _ hL1) hroom rfl (key_store_max M1
    hb1 (Table.cmpMax keyLt (eAt M1 6) (eAt M1 7)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M1 6) (eAt M1 7)))) (select_min_pair (eAt M1 6) (eAt M1 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 6) (M := M1.set 7 (Table.cmpMax keyLt (eAt M1 6)
    (eAt M1 7))) (q := (Table.cmpMin keyLt (eAt M1 6) (eAt M1 7))) (lt_set _
    ha1) (len_set _ hL1) hroom rfl (cmpSwap_writes M1 (by decide) ha1 hb1)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M1 6 7 3 (by decide) (by decide), ← eAt_step M1 6 7 5
    (by decide) (by decide), ← eAt_step M1 6 7 4 (by decide) (by decide), ←
    eAt_step M1 6 7 2 (by decide) (by decide), ← eAt_lo M1 6 7 (by decide) ha1
    hb1, ← eAt_step M1 6 7 1 (by decide) (by decide)]
  set M2 := Table.cmpSwap keyLt M1 (6, 7) with hM2
  have hL2 : M2.length = 9 := by
    rw [hM2, Table.cmpSwap_length]; exact hL1
  -- WAT 6926 to 6952: the comparator of the slots 1 and 2
  have ha2 : (1 : Nat) < M2.length := by omega
  have hb2 : (2 : Nat) < M2.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 1) (j := 2) ha2 hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 2) (M := M2) (value := (Table.cmpMax keyLt (eAt
    M2 1) (eAt M2 2)).2) hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M2 1) (eAt
    M2 2)).1) (select_max_key (eAt M2 1) (eAt M2 2))
  iapply twp_key_store (k := 2) (M := M2.set 2 ((eAt M2 2).1, (Table.cmpMax
    keyLt (eAt M2 1) (eAt M2 2)).2)) (key := (Table.cmpMax keyLt (eAt M2 1)
    (eAt M2 2)).1) (lt_set _ hb2) (len_set _ hL2) hroom rfl (key_store_max M2
    hb2 (Table.cmpMax keyLt (eAt M2 1) (eAt M2 2)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 1) (M := M2.set 2 (Table.cmpMax keyLt (eAt M2 1)
    (eAt M2 2))) (lt_set _ ha2) (len_set _ hL2) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M2 2 1 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M2 1) (eAt M2 2)))) (select_min_pair (eAt M2 1) (eAt M2 2))
  iapply twp_pair_store (k := 1) (M := M2.set 2 (Table.cmpMax keyLt (eAt M2 1)
    (eAt M2 2))) (q := (Table.cmpMin keyLt (eAt M2 1) (eAt M2 2))) (lt_set _
    ha2) (len_set _ hL2) hroom rfl (cmpSwap_writes M2 (by decide) ha2 hb2)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M2 1 2 3 (by decide) (by decide), ← eAt_step M2 1 2 5
    (by decide) (by decide), ← eAt_step M2 1 2 4 (by decide) (by decide), ←
    eAt_step M2 1 2 6 (by decide) (by decide)]
  set M3 := Table.cmpSwap keyLt M2 (1, 2) with hM3
  have hL3 : M3.length = 9 := by
    rw [hM3, Table.cmpSwap_length]; exact hL2
  -- WAT 6953 to 6979: the comparator of the slots 3 and 4
  have ha3 : (3 : Nat) < M3.length := by omega
  have hb3 : (4 : Nat) < M3.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 3) (j := 4) ha3 hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 4) (M := M3) (value := (Table.cmpMax keyLt (eAt
    M3 3) (eAt M3 4)).2) hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M3 3) (eAt
    M3 4)).1) (select_max_key (eAt M3 3) (eAt M3 4))
  iapply twp_key_store (k := 4) (M := M3.set 4 ((eAt M3 4).1, (Table.cmpMax
    keyLt (eAt M3 3) (eAt M3 4)).2)) (key := (Table.cmpMax keyLt (eAt M3 3)
    (eAt M3 4)).1) (lt_set _ hb3) (len_set _ hL3) hroom rfl (key_store_max M3
    hb3 (Table.cmpMax keyLt (eAt M3 3) (eAt M3 4)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 3) (M := M3.set 4 (Table.cmpMax keyLt (eAt M3 3)
    (eAt M3 4))) (lt_set _ ha3) (len_set _ hL3) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M3 4 3 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M3 3) (eAt M3 4)))) (select_min_pair (eAt M3 3) (eAt M3 4))
  iapply twp_pair_store (k := 3) (M := M3.set 4 (Table.cmpMax keyLt (eAt M3 3)
    (eAt M3 4))) (q := (Table.cmpMin keyLt (eAt M3 3) (eAt M3 4))) (lt_set _
    ha3) (len_set _ hL3) hroom rfl (cmpSwap_writes M3 (by decide) ha3 hb3)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M3 3 4 5 (by decide) (by decide), ← eAt_step M3 3 4 6
    (by decide) (by decide)]
  set M4 := Table.cmpSwap keyLt M3 (3, 4) with hM4
  have hL4 : M4.length = 9 := by
    rw [hM4, Table.cmpSwap_length]; exact hL3
  -- WAT 6980 to 7006: the comparator of the slots 5 and 6
  have ha4 : (5 : Nat) < M4.length := by omega
  have hb4 : (6 : Nat) < M4.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 5) (j := 6) ha4 hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 6) (M := M4) (value := (Table.cmpMax keyLt (eAt
    M4 5) (eAt M4 6)).2) hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M4 5) (eAt
    M4 6)).1) (select_max_key (eAt M4 5) (eAt M4 6))
  iapply twp_key_store (k := 6) (M := M4.set 6 ((eAt M4 6).1, (Table.cmpMax
    keyLt (eAt M4 5) (eAt M4 6)).2)) (key := (Table.cmpMax keyLt (eAt M4 5)
    (eAt M4 6)).1) (lt_set _ hb4) (len_set _ hL4) hroom rfl (key_store_max M4
    hb4 (Table.cmpMax keyLt (eAt M4 5) (eAt M4 6)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 5) (M := M4.set 6 (Table.cmpMax keyLt (eAt M4 5)
    (eAt M4 6))) (lt_set _ ha4) (len_set _ hL4) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M4 6 5 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M4 5) (eAt M4 6)))) (select_min_pair (eAt M4 5) (eAt M4 6))
  iapply twp_pair_store (k := 5) (M := M4.set 6 (Table.cmpMax keyLt (eAt M4 5)
    (eAt M4 6))) (q := (Table.cmpMin keyLt (eAt M4 5) (eAt M4 6))) (lt_set _
    ha4) (len_set _ hL4) hroom rfl (cmpSwap_writes M4 (by decide) ha4 hb4)
  isplitl_exact Hbuf
  iintro Hbuf
  set M5 := Table.cmpSwap keyLt M4 (5, 6) with hM5
  have hL5 : M5.length = 9 := by
    rw [hM5, Table.cmpSwap_length]; exact hL4
  -- WAT 7007 and 7008: the network result
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply (hcont _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

/-! ## The whole network -/

/-- A comparator block keeps the length. -/
private theorem applyNetwork_len {blk : List Table.Comparator}
    {L : List (UInt32 × UInt32)} (h : L.length = 9) :
    (Table.applyNetwork keyLt blk L).length = 9 := by
  rw [Table.applyNetwork_length]; exact h

/-- The five parts, run in a row, are the whole network. -/
private theorem netBlocks_chain (M : List (UInt32 × UInt32)) :
    Table.applyNetwork keyLt netBlock4
        (Table.applyNetwork keyLt netBlock3
          (Table.applyNetwork keyLt netBlock2
            (Table.applyNetwork keyLt netBlock1
              (Table.applyNetwork keyLt netBlock0 M)))) =
      Table.applyNetwork keyLt Table.sort9Net M := by
  have hsplit : Table.sort9Net = netBlock0 ++ netBlock1 ++ netBlock2 ++
      netBlock3 ++ netBlock4 := by rfl
  rw [hsplit, Table.applyNetwork_append, Table.applyNetwork_append,
    Table.applyNetwork_append, Table.applyNetwork_append]

set_option maxHeartbeats 2000000 in
/-- The nine-entry sorting network of the `quicksort` body, WAT 6233 to
7008.  It runs `Table.sort9Net` on the nine entries at the region
base and then writes 9 into local 6.  Every other register that the
region writes is dead when the region ends. -/
theorem twp_sort9 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r2 r3 r4 r6 r9 r10 r11 r14 r15 r21 r22 r23 r24 r26 r28 r29 : UInt32}
    {r12 r19 r20 r25 r27 : UInt64}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 9) (hroom : v.toNat + 72 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt Table.sort9Net M)
    (hcont : ∀ (y2 y3 y4 y9 y10 y11 y14 y15 y21 y22 y23 y24 y26 y28 y29 :
      UInt32) (y12 y19 y20 y25 y27 : UInt64), iprop(Table.PairSlice 0 v N ∗
      Rest) ⊢
      WP (.running ⟨netLocals f v y2 y3 y4 9 y9 y10 y11 y12 y14 y15 y19 y20 y21
        y22 y23 y24 y25 y26 y27 y28 y29 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨netLocals f v r2 r3 r4 r6 r9 r10 r11 r12 r14 r15 r19 r20
        r21 r22 r23 r24 r25 r26 r27 r28 r29 [],
        qsSort9 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  rw [qsSort9_parts]
  simp only [List.append_assoc]
  refine twp_sort9_chunk0 hlen hroom rfl ?_
  intro a23 a24 a26 a28 a29 a27
  refine twp_sort9_chunk1 (applyNetwork_len hlen) hroom rfl ?_
  intro b28 b29 b12 b27
  refine twp_sort9_chunk2 (applyNetwork_len (applyNetwork_len hlen)) hroom
    rfl ?_
  intro c26 c28 c29 c12
  refine twp_sort9_chunk3
    (applyNetwork_len (applyNetwork_len (applyNetwork_len hlen))) hroom
    rfl ?_
  intro d4 d21 d28 d29 d12 d20 d27
  refine twp_sort9_chunk4
    (applyNetwork_len (applyNetwork_len (applyNetwork_len
      (applyNetwork_len hlen)))) hroom rfl ?_
  intro e2 e3 e4 e9 e10 e11 e14 e15 e21 e22 e23 e24 e26 e28 e29 e12 e19
    e20 e25 e27
  rw [netBlocks_chain M, ← hN]
  exact hcont e2 e3 e4 e9 e10 e11 e14 e15 e21 e22 e23 e24 e26 e28 e29 e12
    e19 e20 e25 e27


end Project.RustHashMap.Func21Network9
