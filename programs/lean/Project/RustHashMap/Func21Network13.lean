import Project.RustHashMap.Func21Network9

/-!
# The thirteen-entry sorting network of `quicksort`

Absolute `func 24` is `quicksort`, local `func21`.  WAT lines 7011 to
8391 of `programs/rust/build/rust_hash_map/program.wat` hold the second
sorting network of the small sort, which is the fragment `qsSort13` of
`Project.RustHashMap.Func21Defs`.  This module proves `twp_sort13`, the
one stage lemma of that region.

## What the region computes

The region sorts the thirteen entries that start at the region base,
which local 8 holds, and then writes 13 into local 6.  The run is branch
free.  It holds 135 `select` instructions, which is 45 comparators, and
the pure model of those comparators is `Table.sort13Net`.

One comparator of the slots `i` and `j`, with `i < j`, reads the two
keys, writes the smaller entry into slot `i` and the greater entry into
slot `j`.  That is `Table.cmpSwap keyLt (i, j)`, because the compiled
test is `key of j below key of i`, which is `keyLt` of the two entries
in that order.  A comparator makes three stores: the value of the
greater entry, the key of the greater entry, and the whole smaller entry
as one `i64`.  A tie moves nothing, which `Table.cmpSwap_of_not_lt`
matches.

## The comparator table

The table gives, for each comparator, the WAT span, the two slots, the
shape of the `select` that makes the smaller entry, where the two keys
come from, the local that caches the key of the greater entry, and the
local that caches the smaller entry.  `load` is a fresh `i32.load`,
`wrap Ln` is `i32.wrap_i64` of the entry word in local `n`, `reg n` is
the key already in local `n`, and `-` is no cache.

| # | WAT | slots | min | key i | key j | key reg | entry reg |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 7011-7045 | (0, 12) | addr | load | load | L24 | L12 |
| 1 | 7046-7085 | (1, 10) | off | load | load | L26 | L12 |
| 2 | 7086-7125 | (2, 9) | off | load | load | L28 | L25 |
| 3 | 7126-7165 | (3, 7) | off | load | load | L29 | L19 |
| 4 | 7166-7205 | (5, 11) | off | load | load | L30 | L20 |
| 5 | 7206-7245 | (6, 8) | off | load | load | L31 | L20 |
| 6 | 7246-7275 | (1, 6) | word | wrap L12 | wrap L20 | L32 | L20 |
| 7 | 7276-7305 | (2, 3) | word | wrap L25 | wrap L19 | L33 | L19 |
| 8 | 7306-7341 | (4, 11) | off | load | reg 30 | L30 | L27 |
| 9 | 7342-7371 | (7, 9) | off | reg 29 | reg 28 | L28 | L12 |
| 10 | 7372-7401 | (8, 10) | off | reg 31 | reg 26 | L26 | L25 |
| 11 | 7402-7431 | (0, 4) | word | load | wrap L27 | L29 | - |
| 12 | 7432-7460 | (1, 2) | word | wrap L20 | wrap L19 | L31 | - |
| 13 | 7461-7488 | (3, 6) | addr | reg 33 | reg 32 | L32 | L19 |
| 14 | 7489-7518 | (7, 8) | word | wrap L12 | wrap L25 | L33 | L27 |
| 15 | 7519-7548 | (9, 10) | off | reg 28 | reg 26 | L26 | L12 |
| 16 | 7549-7578 | (11, 12) | off | reg 30 | reg 24 | L24 | L25 |
| 17 | 7579-7606 | (4, 6) | addr | reg 29 | reg 32 | L28 | L20 |
| 18 | 7607-7637 | (5, 9) | word | load | wrap L12 | L29 | L37 |
| 19 | 7638-7666 | (8, 11) | word | reg 33 | wrap L25 | L30 | L25 |
| 20 | 7667-7695 | (10, 12) | off | reg 26 | reg 24 | - | L12 |
| 21 | 7696-7726 | (0, 5) | word | load | wrap L37 | L23 | L37 |
| 22 | 7727-7756 | (3, 8) | word | wrap L19 | wrap L25 | L24 | L38 |
| 23 | 7757-7786 | (4, 7) | word | wrap L20 | wrap L27 | L26 | L20 |
| 24 | 7787-7814 | (6, 11) | addr | reg 28 | reg 30 | L28 | L25 |
| 25 | 7815-7843 | (9, 10) | word | reg 29 | wrap L12 | L29 | L19 |
| 26 | 7844-7875 | (0, 1) | word | wrap L37 | load | L30 | - |
| 27 | 7876-7903 | (2, 5) | addr | reg 31 | reg 23 | L23 | L12 |
| 28 | 7904-7933 | (6, 9) | word | wrap L25 | wrap L19 | L31 | L27 |
| 29 | 7934-7961 | (7, 8) | addr | reg 26 | reg 24 | L24 | L25 |
| 30 | 7962-7988 | (10, 11) | addr | reg 29 | reg 28 | - | L19 |
| 31 | 7989-8017 | (1, 3) | word | reg 30 | wrap L38 | L21 | L37 |
| 32 | 8018-8047 | (2, 4) | word | wrap L12 | wrap L20 | L26 | L12 |
| 33 | 8048-8076 | (5, 6) | word | reg 23 | wrap L27 | L23 | L20 |
| 34 | 8077-8104 | (9, 10) | word | reg 31 | wrap L19 | - | L19 |
| 35 | 8105-8133 | (1, 2) | word | wrap L37 | wrap L12 | L14 | - |
| 36 | 8134-8161 | (3, 4) | addr | reg 21 | reg 26 | L21 | L12 |
| 37 | 8162-8191 | (5, 7) | word | wrap L20 | wrap L25 | L22 | L20 |
| 38 | 8192-8219 | (6, 8) | addr | reg 23 | reg 24 | L23 | L25 |
| 39 | 8220-8247 | (2, 3) | word | reg 14 | wrap L12 | L14 | - |
| 40 | 8248-8276 | (4, 5) | word | reg 21 | wrap L20 | L3 | L12 |
| 41 | 8277-8306 | (6, 7) | word | wrap L25 | reg 22 | - | L25 |
| 42 | 8307-8335 | (8, 9) | word | reg 23 | wrap L19 | - | - |
| 43 | 8336-8362 | (3, 4) | word | reg 14 | wrap L12 | - | - |
| 44 | 8363-8389 | (5, 6) | word | reg 3 | wrap L25 | - | - |

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

## The locals

The thirteen-entry network writes nine locals that the nine-entry
network leaves alone: 30 to 38.  `NetRegs` carries those as pad fields,
so `net13Locals` names them.  It is `netLocals` of the record whose nine
pads the caller gives, and the nine-entry vocabulary stays as it is.

## How the proof is cut

`Func21Defs.qsSort13Chunk` cuts the run right after every fifteenth
`select`, which falls inside a comparator: the stores that finish that
comparator sit in the next chunk.  This module cuts after the last store
of every fifth comparator instead, so that each part runs five whole
comparators and each part lemma states one whole `Table.applyNetwork`
step.  `sort13Part` names the nine parts, and `qsSort13_parts` ties them
to `qsSort13`.

Each part lemma carries the live registers of the network.  A register
that holds a key or an entry word names it as `eAt` of the list that the
memory holds at that point, so no register names a stale list.  The
three rules that follow a `select` split on the comparison once and
close both arms with one continuation, so no part lemma splits.
-/

namespace Project.RustHashMap.Func21Network13

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.SortModels
open Project.RustHashMap.Func21Defs
open Project.RustHashMap.Func21Network9
open scoped Wasm.SmallStep.Outcome

set_option maxRecDepth 40000

/-! ## The entry of one slot

`eAt` reads one entry of the model list without a bound proof, so that
a register value never carries a proof term.
-/

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
    {q : UInt32 × UInt32} (h : M.length = 13) :
    (M.set k q).length = 13 := by
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
    (hk : 8 * k + 8 ≤ 104) (hroom : v.toNat + 104 < UInt32.size) :
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
    (hk : 8 * k + 8 ≤ 104) (hroom : v.toNat + 104 < UInt32.size) :
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
    (hk : k < M.length) (hlen : M.length = 13)
    (hroom : v.toNat + 104 < UInt32.size)
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
    (hk : k < M.length) (hlen : M.length = 13)
    (hroom : v.toNat + 104 < UInt32.size)
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
    (hk : k < M.length) (hlen : M.length = 13)
    (hroom : v.toNat + 104 < UInt32.size)
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
    (hk : k < M.length) (hlen : M.length = 13)
    (hroom : v.toNat + 104 < UInt32.size)
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
    (hoff : UInt32.ofNat (8 * k + 4) = off) (hk : 8 * k + 8 ≤ 104)
    (hroom : v.toNat + 104 < UInt32.size) :
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
    (hk : k < M.length) (hlen : M.length = 13)
    (hroom : v.toNat + 104 < UInt32.size)
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
    (hk : k < M.length) (hlen : M.length = 13)
    (hroom : v.toNat + 104 < UInt32.size)
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
    (hk : k < M.length) (hlen : M.length = 13)
    (hroom : v.toNat + 104 < UInt32.size)
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
    (hi : i < M.length) (hj : j < M.length) (hlen : M.length = 13)
    (hroom : v.toNat + 104 < UInt32.size)
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
    (hi : i < M.length) (hj : j < M.length) (hlen : M.length = 13)
    (hroom : v.toNat + 104 < UInt32.size)
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
    (hi : i < M.length) (hj : j < M.length) (hlen : M.length = 13)
    (hroom : v.toNat + 104 < UInt32.size)
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


/-- The value store of a comparator, after the key store. -/
private theorem value_store_max (L : List (UInt32 × UInt32)) {j : Nat}
    (hj : j < L.length) (p : UInt32 × UInt32) :
    (L.set j (p.1, (eAt L j).2)).set j
        ((eAt (L.set j (p.1, (eAt L j).2)) j).1, p.2) = L.set j p := by
  rw [eAt_eq (L.set j (p.1, (eAt L j).2))
      (by rw [List.length_set]; exact hj),
    List.getElem_set_self, List.set_set]

/-! ## The locals of the thirteen-entry network -/

/-- The locals of the network, with the nine pads of `NetRegs` named.
The thirteen-entry network writes the locals 30 to 38, which the
nine-entry network leaves alone.  It is `netLocals` with those nine
locals explicit, so the two vocabularies stay the same. -/
@[reducible] private def net13Locals (f : NetRegs)
    (v r2 r3 r4 r6 r9 r10 r11 : UInt32) (r12 : UInt64)
    (r14 r15 : UInt32) (r19 r20 : UInt64) (r21 r22 r23 r24 : UInt32)
    (r25 : UInt64) (r26 : UInt32) (r27 : UInt64) (r28 r29 : UInt32)
    (p30 p31 p32 p33 p34 p35 p36 p37 p38 : Value)
    (values : List Value) : Locals :=
  qsLocals f.buf f.len r2 r3 r4
    (.i32 f.fp :: .i32 r6 :: .i32 f.reg7 :: .i32 v :: .i32 r9 ::
      .i32 r10 :: .i32 r11 :: .i64 r12 :: .i32 f.reg13 :: .i32 r14 ::
      .i32 r15 :: f.pad16 :: f.pad17 :: f.pad18 :: .i64 r19 ::
      .i64 r20 :: .i32 r21 :: .i32 r22 :: .i32 r23 :: .i32 r24 ::
      .i64 r25 :: .i32 r26 :: .i64 r27 :: .i32 r28 :: .i32 r29 ::
      p30 :: p31 :: p32 :: p33 :: p34 :: p35 :: p36 :: p37 ::
      p38 :: []) values

/-- The nine-entry vocabulary is the thirteen-entry one with the nine
pads of the record.  The two networks share one locals vocabulary. -/
private theorem netLocals_eq (f : NetRegs)
    (v r2 r3 r4 r6 r9 r10 r11 : UInt32) (r12 : UInt64)
    (r14 r15 : UInt32) (r19 r20 : UInt64) (r21 r22 r23 r24 : UInt32)
    (r25 : UInt64) (r26 : UInt32) (r27 : UInt64) (r28 r29 : UInt32)
    (values : List Value) :
    netLocals f v r2 r3 r4 r6 r9 r10 r11 r12 r14 r15 r19 r20 r21 r22
        r23 r24 r25 r26 r27 r28 r29 values =
      net13Locals f v r2 r3 r4 r6 r9 r10 r11 r12 r14 r15 r19 r20 r21
        r22 r23 r24 r25 r26 r27 r28 r29 f.pad30 f.pad31 f.pad32
        f.pad33 f.pad34 f.pad35 f.pad36 f.pad37 f.pad38 values :=
  rfl

/-! ## The nine parts of the network

Each part runs five whole comparators.  Part 8 also runs the two
instructions that write 13 into local 6.
-/

/-- The instruction index of the first instruction of each part. -/
private def sort13Bound : Nat → Nat
  | 0 => 0
  | 1 => 195
  | 2 => 361
  | 3 => 508
  | 4 => 656
  | 5 => 804
  | 6 => 951
  | 7 => 1094
  | 8 => 1237
  | _ => 1381

/-- Part `k` of the network, for `k < 9`. -/
@[reducible] private def sort13Part (k : Nat) : Program :=
  (qsSort13.drop (sort13Bound k)).take
    (sort13Bound (k + 1) - sort13Bound k)

private theorem qsSort13_parts :
    qsSort13 =
      sort13Part 0 ++ sort13Part 1 ++ sort13Part 2 ++ sort13Part 3 ++
        sort13Part 4 ++ sort13Part 5 ++ sort13Part 6 ++ sort13Part 7 ++
          sort13Part 8 := by
  rfl

/-- WAT 7011 to 7205. -/
private theorem sort13Part0_shape :
    sort13Part 0 =
      [Instruction.localGet 8, .const 96, .add, .localTee 23, .localGet 8,
        .localGet 8, .load32 96, .localTee 6, .localGet 8, .load32 0, .localTee
        9, .ltU, .localTee 10, .select, .load64 0, .localSet 12, .localGet 8,
        .localGet 8, .localGet 23, .localGet 10, .select, .load32 4, .store32
        100, .localGet 8, .localGet 6, .localGet 9, .localGet 6, .localGet 9,
        .gtU, .select, .localTee 24, .store32 96, .localGet 8, .localGet 12,
        .store64 0, .localGet 8, .const 80, .const 8, .localGet 8, .load32 80,
        .localTee 6, .localGet 8, .load32 8, .localTee 9, .ltU, .localTee 10,
        .select, .add, .load64 0, .localSet 12, .localGet 8, .localGet 8,
        .const 8, .add, .localTee 22, .localGet 8, .const 80, .add, .localTee
        14, .localGet 10, .select, .load32 4, .store32 84, .localGet 8,
        .localGet 6, .localGet 9, .localGet 6, .localGet 9, .gtU, .select,
        .localTee 26, .store32 80, .localGet 8, .localGet 12, .store64 8,
        .localGet 8, .const 72, .const 16, .localGet 8, .load32 72, .localTee
        6, .localGet 8, .load32 16, .localTee 9, .ltU, .localTee 10, .select,
        .add, .load64 0, .localSet 25, .localGet 8, .localGet 8, .const 16,
        .add, .localTee 3, .localGet 8, .const 72, .add, .localTee 2, .localGet
        10, .select, .load32 4, .store32 76, .localGet 8, .localGet 6,
        .localGet 9, .localGet 6, .localGet 9, .gtU, .select, .localTee 28,
        .store32 72, .localGet 8, .localGet 25, .store64 16, .localGet 8,
        .const 56, .const 24, .localGet 8, .load32 56, .localTee 6, .localGet
        8, .load32 24, .localTee 10, .ltU, .localTee 11, .select, .add, .load64
        0, .localSet 19, .localGet 8, .localGet 8, .const 24, .add, .localTee
        9, .localGet 8, .const 56, .add, .localTee 4, .localGet 11, .select,
        .load32 4, .store32 60, .localGet 8, .localGet 6, .localGet 10,
        .localGet 6, .localGet 10, .gtU, .select, .localTee 29, .store32 56,
        .localGet 8, .localGet 19, .store64 24, .localGet 8, .const 88, .const
        40, .localGet 8, .load32 88, .localTee 6, .localGet 8, .load32 40,
        .localTee 10, .ltU, .localTee 11, .select, .add, .load64 0, .localSet
        20, .localGet 8, .localGet 8, .const 40, .add, .localTee 15, .localGet
        8, .const 88, .add, .localTee 21, .localGet 11, .select, .load32 4,
        .store32 92, .localGet 8, .localGet 6, .localGet 10, .localGet 6,
        .localGet 10, .gtU, .select, .localTee 30, .store32 88, .localGet 8,
        .localGet 20, .store64 40] := by
  rfl

/-- WAT 7206 to 7371. -/
private theorem sort13Part1_shape :
    sort13Part 1 =
      [Instruction.localGet 8, .const 64, .const 48, .localGet 8, .load32 64,
        .localTee 11, .localGet 8, .load32 48, .localTee 31, .ltU, .localTee
        32, .select, .add, .load64 0, .localSet 20, .localGet 8, .localGet 8,
        .const 48, .add, .localTee 6, .localGet 8, .const 64, .add, .localTee
        10, .localGet 32, .select, .load32 4, .store32 68, .localGet 8,
        .localGet 11, .localGet 31, .localGet 11, .localGet 31, .gtU, .select,
        .localTee 31, .store32 64, .localGet 8, .localGet 20, .store64 48,
        .localGet 8, .localGet 22, .localGet 6, .localGet 20, .wrapI64,
        .localTee 11, .localGet 12, .wrapI64, .localTee 32, .ltU, .localTee 33,
        .select, .load32 4, .store32 52, .localGet 8, .localGet 11, .localGet
        32, .localGet 11, .localGet 32, .gtU, .select, .localTee 32, .store32
        48, .localGet 8, .localGet 20, .localGet 12, .localGet 33, .select,
        .localTee 20, .store64 8, .localGet 8, .localGet 3, .localGet 9,
        .localGet 19, .wrapI64, .localTee 11, .localGet 25, .wrapI64, .localTee
        33, .ltU, .localTee 34, .select, .load32 4, .store32 28, .localGet 8,
        .localGet 11, .localGet 33, .localGet 11, .localGet 33, .gtU, .select,
        .localTee 33, .store32 24, .localGet 8, .localGet 19, .localGet 25,
        .localGet 34, .select, .localTee 19, .store64 16, .localGet 8, .const
        32, .add, .localTee 11, .localGet 21, .localGet 30, .localGet 8,
        .load32 32, .localTee 34, .ltU, .localTee 35, .select, .load32 4,
        .localSet 36, .localGet 8, .localGet 8, .const 88, .const 32, .localGet
        35, .select, .add, .load64 0, .localTee 27, .store64 32, .localGet 8,
        .localGet 36, .store32 92, .localGet 8, .localGet 30, .localGet 34,
        .localGet 30, .localGet 34, .gtU, .select, .localTee 30, .store32 88,
        .localGet 8, .const 72, .const 56, .localGet 28, .localGet 29, .ltU,
        .localTee 34, .select, .add, .load64 0, .localSet 12, .localGet 8,
        .localGet 4, .localGet 2, .localGet 34, .select, .load32 4, .store32
        76, .localGet 8, .localGet 28, .localGet 29, .localGet 28, .localGet
        29, .gtU, .select, .localTee 28, .store32 72, .localGet 8, .localGet
        12, .store64 56] := by
  rfl

/-- WAT 7372 to 7518. -/
private theorem sort13Part2_shape :
    sort13Part 2 =
      [Instruction.localGet 8, .const 80, .const 64, .localGet 26, .localGet
        31, .ltU, .localTee 29, .select, .add, .load64 0, .localSet 25,
        .localGet 8, .localGet 10, .localGet 14, .localGet 29, .select, .load32
        4, .store32 84, .localGet 8, .localGet 26, .localGet 31, .localGet 26,
        .localGet 31, .gtU, .select, .localTee 26, .store32 80, .localGet 8,
        .localGet 25, .store64 64, .localGet 8, .localGet 8, .localGet 11,
        .localGet 8, .load32 0, .localTee 29, .localGet 27, .wrapI64, .localTee
        31, .gtU, .localTee 34, .select, .load32 4, .store32 36, .localGet 8,
        .localGet 31, .localGet 29, .localGet 31, .localGet 29, .gtU, .select,
        .localTee 29, .store32 32, .localGet 8, .localGet 27, .localGet 8,
        .load64 0, .localGet 34, .select, .store64 0, .localGet 8, .localGet
        22, .localGet 3, .localGet 19, .wrapI64, .localTee 31, .localGet 20,
        .wrapI64, .localTee 34, .ltU, .localTee 35, .select, .load32 4,
        .store32 20, .localGet 8, .localGet 31, .localGet 34, .localGet 31,
        .localGet 34, .gtU, .select, .localTee 31, .store32 16, .localGet 8,
        .localGet 19, .localGet 20, .localGet 35, .select, .store64 8,
        .localGet 6, .localGet 9, .localGet 32, .localGet 33, .ltU, .localTee
        34, .select, .load64 0, .localSet 19, .localGet 8, .localGet 9,
        .localGet 6, .localGet 34, .select, .load32 4, .store32 52, .localGet
        8, .localGet 32, .localGet 33, .localGet 32, .localGet 33, .gtU,
        .select, .localTee 32, .store32 48, .localGet 8, .localGet 19, .store64
        24, .localGet 8, .localGet 4, .localGet 10, .localGet 25, .wrapI64,
        .localTee 33, .localGet 12, .wrapI64, .localTee 34, .ltU, .localTee 35,
        .select, .load32 4, .store32 68, .localGet 8, .localGet 33, .localGet
        34, .localGet 33, .localGet 34, .gtU, .select, .localTee 33, .store32
        64, .localGet 8, .localGet 25, .localGet 12, .localGet 35, .select,
        .localTee 27, .store64 56] := by
  rfl

/-- WAT 7519 to 7666. -/
private theorem sort13Part3_shape :
    sort13Part 3 =
      [Instruction.localGet 8, .const 80, .const 72, .localGet 26, .localGet
        28, .ltU, .localTee 34, .select, .add, .load64 0, .localSet 12,
        .localGet 8, .localGet 2, .localGet 14, .localGet 34, .select, .load32
        4, .store32 84, .localGet 8, .localGet 26, .localGet 28, .localGet 26,
        .localGet 28, .gtU, .select, .localTee 26, .store32 80, .localGet 8,
        .localGet 12, .store64 72, .localGet 8, .const 96, .const 88, .localGet
        24, .localGet 30, .ltU, .localTee 28, .select, .add, .load64 0,
        .localSet 25, .localGet 8, .localGet 21, .localGet 23, .localGet 28,
        .select, .load32 4, .store32 100, .localGet 8, .localGet 24, .localGet
        30, .localGet 24, .localGet 30, .gtU, .select, .localTee 24, .store32
        96, .localGet 8, .localGet 25, .store64 88, .localGet 6, .localGet 11,
        .localGet 32, .localGet 29, .ltU, .localTee 28, .select, .load64 0,
        .localSet 20, .localGet 8, .localGet 11, .localGet 6, .localGet 28,
        .select, .load32 4, .store32 52, .localGet 8, .localGet 32, .localGet
        29, .localGet 32, .localGet 29, .gtU, .select, .localTee 28, .store32
        48, .localGet 8, .localGet 20, .store64 32, .localGet 8, .localGet 15,
        .localGet 2, .localGet 8, .load32 40, .localTee 29, .localGet 12,
        .wrapI64, .localTee 30, .gtU, .localTee 32, .select, .load32 4,
        .store32 76, .localGet 8, .localGet 30, .localGet 29, .localGet 30,
        .localGet 29, .gtU, .select, .localTee 29, .store32 72, .localGet 8,
        .localGet 12, .localGet 8, .load64 40, .localGet 32, .select, .localTee
        37, .store64 40, .localGet 8, .localGet 10, .localGet 21, .localGet 33,
        .localGet 25, .wrapI64, .localTee 30, .gtU, .localTee 32, .select,
        .load32 4, .store32 92, .localGet 8, .localGet 30, .localGet 33,
        .localGet 30, .localGet 33, .gtU, .select, .localTee 30, .store32 88,
        .localGet 8, .localGet 25, .localGet 8, .load64 64, .localGet 32,
        .select, .localTee 25, .store64 64] := by
  rfl

/-- WAT 7667 to 7814. -/
private theorem sort13Part4_shape :
    sort13Part 4 =
      [Instruction.localGet 8, .const 96, .const 80, .localGet 24, .localGet
        26, .ltU, .localTee 32, .select, .add, .load64 0, .localSet 12,
        .localGet 8, .localGet 14, .localGet 23, .localGet 32, .select, .load32
        4, .store32 100, .localGet 8, .localGet 24, .localGet 26, .localGet 24,
        .localGet 26, .gtU, .select, .store32 96, .localGet 8, .localGet 12,
        .store64 80, .localGet 8, .localGet 8, .localGet 15, .localGet 8,
        .load32 0, .localTee 23, .localGet 37, .wrapI64, .localTee 24, .gtU,
        .localTee 26, .select, .load32 4, .store32 44, .localGet 8, .localGet
        24, .localGet 23, .localGet 24, .localGet 23, .gtU, .select, .localTee
        23, .store32 40, .localGet 8, .localGet 37, .localGet 8, .load64 0,
        .localGet 26, .select, .localTee 37, .store64 0, .localGet 8, .localGet
        9, .localGet 10, .localGet 25, .wrapI64, .localTee 24, .localGet 19,
        .wrapI64, .localTee 26, .ltU, .localTee 32, .select, .load32 4,
        .store32 68, .localGet 8, .localGet 24, .localGet 26, .localGet 24,
        .localGet 26, .gtU, .select, .localTee 24, .store32 64, .localGet 8,
        .localGet 25, .localGet 19, .localGet 32, .select, .localTee 38,
        .store64 24, .localGet 8, .localGet 11, .localGet 4, .localGet 27,
        .wrapI64, .localTee 26, .localGet 20, .wrapI64, .localTee 32, .ltU,
        .localTee 33, .select, .load32 4, .store32 60, .localGet 8, .localGet
        26, .localGet 32, .localGet 26, .localGet 32, .gtU, .select, .localTee
        26, .store32 56, .localGet 8, .localGet 27, .localGet 20, .localGet 33,
        .select, .localTee 20, .store64 32, .localGet 21, .localGet 6,
        .localGet 30, .localGet 28, .ltU, .localTee 32, .select, .load64 0,
        .localSet 25, .localGet 8, .localGet 6, .localGet 21, .localGet 32,
        .select, .load32 4, .store32 92, .localGet 8, .localGet 30, .localGet
        28, .localGet 30, .localGet 28, .gtU, .select, .localTee 28, .store32
        88, .localGet 8, .localGet 25, .store64 48] := by
  rfl

/-- WAT 7815 to 7961. -/
private theorem sort13Part5_shape :
    sort13Part 5 =
      [Instruction.localGet 8, .localGet 2, .localGet 14, .localGet 29,
        .localGet 12, .wrapI64, .localTee 30, .gtU, .localTee 32, .select,
        .load32 4, .store32 84, .localGet 8, .localGet 30, .localGet 29,
        .localGet 30, .localGet 29, .gtU, .select, .localTee 29, .store32 80,
        .localGet 8, .localGet 12, .localGet 8, .load64 72, .localGet 32,
        .select, .localTee 19, .store64 72, .localGet 8, .load64 8, .localSet
        12, .localGet 8, .localGet 8, .localGet 22, .localGet 8, .load32 8,
        .localTee 30, .localGet 37, .wrapI64, .localTee 32, .ltU, .localTee 33,
        .select, .load32 4, .store32 12, .localGet 8, .localGet 30, .localGet
        32, .localGet 30, .localGet 32, .gtU, .select, .localTee 30, .store32
        8, .localGet 8, .localGet 12, .localGet 37, .localGet 33, .select,
        .store64 0, .localGet 15, .localGet 3, .localGet 23, .localGet 31,
        .ltU, .localTee 32, .select, .load64 0, .localSet 12, .localGet 8,
        .localGet 3, .localGet 15, .localGet 32, .select, .load32 4, .store32
        44, .localGet 8, .localGet 23, .localGet 31, .localGet 23, .localGet
        31, .gtU, .select, .localTee 23, .store32 40, .localGet 8, .localGet
        12, .store64 16, .localGet 8, .localGet 6, .localGet 2, .localGet 19,
        .wrapI64, .localTee 31, .localGet 25, .wrapI64, .localTee 32, .ltU,
        .localTee 33, .select, .load32 4, .store32 76, .localGet 8, .localGet
        31, .localGet 32, .localGet 31, .localGet 32, .gtU, .select, .localTee
        31, .store32 72, .localGet 8, .localGet 19, .localGet 25, .localGet 33,
        .select, .localTee 27, .store64 48, .localGet 10, .localGet 4,
        .localGet 24, .localGet 26, .ltU, .localTee 32, .select, .load64 0,
        .localSet 25, .localGet 8, .localGet 4, .localGet 10, .localGet 32,
        .select, .load32 4, .store32 68, .localGet 8, .localGet 24, .localGet
        26, .localGet 24, .localGet 26, .gtU, .select, .localTee 24, .store32
        64, .localGet 8, .localGet 25, .store64 56] := by
  rfl

/-- WAT 7962 to 8104. -/
private theorem sort13Part6_shape :
    sort13Part 6 =
      [Instruction.localGet 21, .localGet 14, .localGet 28, .localGet 29, .ltU,
        .localTee 26, .select, .load64 0, .localSet 19, .localGet 8, .localGet
        14, .localGet 21, .localGet 26, .select, .load32 4, .store32 92,
        .localGet 8, .localGet 28, .localGet 29, .localGet 28, .localGet 29,
        .gtU, .select, .store32 88, .localGet 8, .localGet 19, .store64 80,
        .localGet 8, .localGet 22, .localGet 9, .localGet 30, .localGet 38,
        .wrapI64, .localTee 21, .gtU, .localTee 26, .select, .load32 4,
        .store32 28, .localGet 8, .localGet 21, .localGet 30, .localGet 21,
        .localGet 30, .gtU, .select, .localTee 21, .store32 24, .localGet 8,
        .localGet 38, .localGet 8, .load64 8, .localGet 26, .select, .localTee
        37, .store64 8, .localGet 8, .localGet 3, .localGet 11, .localGet 20,
        .wrapI64, .localTee 26, .localGet 12, .wrapI64, .localTee 28, .ltU,
        .localTee 29, .select, .load32 4, .store32 36, .localGet 8, .localGet
        26, .localGet 28, .localGet 26, .localGet 28, .gtU, .select, .localTee
        26, .store32 32, .localGet 8, .localGet 20, .localGet 12, .localGet 29,
        .select, .localTee 12, .store64 16, .localGet 8, .localGet 15,
        .localGet 6, .localGet 23, .localGet 27, .wrapI64, .localTee 28, .gtU,
        .localTee 29, .select, .load32 4, .store32 52, .localGet 8, .localGet
        28, .localGet 23, .localGet 28, .localGet 23, .gtU, .select, .localTee
        23, .store32 48, .localGet 8, .localGet 27, .localGet 8, .load64 40,
        .localGet 29, .select, .localTee 20, .store64 40, .localGet 8,
        .localGet 2, .localGet 14, .localGet 31, .localGet 19, .wrapI64,
        .localTee 28, .gtU, .localTee 29, .select, .load32 4, .store32 84,
        .localGet 8, .localGet 28, .localGet 31, .localGet 28, .localGet 31,
        .gtU, .select, .store32 80, .localGet 8, .localGet 19, .localGet 8,
        .load64 72, .localGet 29, .select, .localTee 19, .store64 72] := by
  rfl

/-- WAT 8105 to 8247. -/
private theorem sort13Part7_shape :
    sort13Part 7 =
      [Instruction.localGet 8, .localGet 22, .localGet 3, .localGet 12,
        .wrapI64, .localTee 14, .localGet 37, .wrapI64, .localTee 28, .ltU,
        .localTee 29, .select, .load32 4, .store32 20, .localGet 8, .localGet
        14, .localGet 28, .localGet 14, .localGet 28, .gtU, .select, .localTee
        14, .store32 16, .localGet 8, .localGet 12, .localGet 37, .localGet 29,
        .select, .store64 8, .localGet 11, .localGet 9, .localGet 26, .localGet
        21, .ltU, .localTee 22, .select, .load64 0, .localSet 12, .localGet 8,
        .localGet 9, .localGet 11, .localGet 22, .select, .load32 4, .store32
        36, .localGet 8, .localGet 26, .localGet 21, .localGet 26, .localGet
        21, .gtU, .select, .localTee 21, .store32 32, .localGet 8, .localGet
        12, .store64 24, .localGet 8, .localGet 15, .localGet 4, .localGet 25,
        .wrapI64, .localTee 22, .localGet 20, .wrapI64, .localTee 26, .ltU,
        .localTee 28, .select, .load32 4, .store32 60, .localGet 8, .localGet
        22, .localGet 26, .localGet 22, .localGet 26, .gtU, .select, .localTee
        22, .store32 56, .localGet 8, .localGet 25, .localGet 20, .localGet 28,
        .select, .localTee 20, .store64 40, .localGet 10, .localGet 6,
        .localGet 24, .localGet 23, .ltU, .localTee 26, .select, .load64 0,
        .localSet 25, .localGet 8, .localGet 6, .localGet 10, .localGet 26,
        .select, .load32 4, .store32 68, .localGet 8, .localGet 24, .localGet
        23, .localGet 24, .localGet 23, .gtU, .select, .localTee 23, .store32
        64, .localGet 8, .localGet 25, .store64 48, .localGet 8, .localGet 3,
        .localGet 9, .localGet 14, .localGet 12, .wrapI64, .localTee 24, .gtU,
        .localTee 26, .select, .load32 4, .store32 28, .localGet 8, .localGet
        24, .localGet 14, .localGet 24, .localGet 14, .gtU, .select, .localTee
        14, .store32 24, .localGet 8, .localGet 12, .localGet 8, .load64 16,
        .localGet 26, .select, .store64 16] := by
  rfl

/-- WAT 8248 to 8391. -/
private theorem sort13Part8_shape :
    sort13Part 8 =
      [Instruction.localGet 8, .localGet 11, .localGet 15, .localGet 21,
        .localGet 20, .wrapI64, .localTee 3, .gtU, .localTee 24, .select,
        .load32 4, .store32 44, .localGet 8, .localGet 3, .localGet 21,
        .localGet 3, .localGet 21, .gtU, .select, .localTee 3, .store32 40,
        .localGet 8, .localGet 20, .localGet 8, .load64 32, .localGet 24,
        .select, .localTee 12, .store64 32, .localGet 8, .load64 56, .localSet
        20, .localGet 8, .localGet 6, .localGet 4, .localGet 22, .localGet 25,
        .wrapI64, .localTee 21, .ltU, .localTee 24, .select, .load32 4,
        .store32 60, .localGet 8, .localGet 22, .localGet 21, .localGet 22,
        .localGet 21, .gtU, .select, .store32 56, .localGet 8, .localGet 20,
        .localGet 25, .localGet 24, .select, .localTee 25, .store64 48,
        .localGet 10, .localGet 2, .localGet 23, .localGet 19, .wrapI64,
        .localTee 4, .gtU, .localTee 21, .select, .load32 4, .localSet 10,
        .localGet 8, .localGet 4, .localGet 23, .localGet 4, .localGet 23,
        .gtU, .select, .store32 72, .localGet 8, .localGet 10, .store32 76,
        .localGet 8, .localGet 19, .localGet 8, .load64 64, .localGet 21,
        .select, .store64 64, .localGet 8, .localGet 9, .localGet 11, .localGet
        14, .localGet 12, .wrapI64, .localTee 10, .gtU, .localTee 2, .select,
        .load32 4, .store32 36, .localGet 8, .localGet 10, .localGet 14,
        .localGet 10, .localGet 14, .gtU, .select, .store32 32, .localGet 8,
        .localGet 12, .localGet 8, .load64 24, .localGet 2, .select, .store64
        24, .localGet 8, .localGet 15, .localGet 6, .localGet 3, .localGet 25,
        .wrapI64, .localTee 9, .gtU, .localTee 10, .select, .load32 4, .store32
        52, .localGet 8, .localGet 9, .localGet 3, .localGet 9, .localGet 3,
        .gtU, .select, .store32 48, .localGet 8, .localGet 25, .localGet 8,
        .load64 40, .localGet 10, .select, .store64 40, .const 13, .localSet 6]
        := by
  rfl

/-! ## The comparator block of each part -/

/-- The five comparators of part 0. -/
private def netBlock0 : List Table.Comparator :=
  [(0, 12), (1, 10), (2, 9), (3, 7), (5, 11)]

/-- The five comparators of part 1. -/
private def netBlock1 : List Table.Comparator :=
  [(6, 8), (1, 6), (2, 3), (4, 11), (7, 9)]

/-- The five comparators of part 2. -/
private def netBlock2 : List Table.Comparator :=
  [(8, 10), (0, 4), (1, 2), (3, 6), (7, 8)]

/-- The five comparators of part 3. -/
private def netBlock3 : List Table.Comparator :=
  [(9, 10), (11, 12), (4, 6), (5, 9), (8, 11)]

/-- The five comparators of part 4. -/
private def netBlock4 : List Table.Comparator :=
  [(10, 12), (0, 5), (3, 8), (4, 7), (6, 11)]

/-- The five comparators of part 5. -/
private def netBlock5 : List Table.Comparator :=
  [(9, 10), (0, 1), (2, 5), (6, 9), (7, 8)]

/-- The five comparators of part 6. -/
private def netBlock6 : List Table.Comparator :=
  [(10, 11), (1, 3), (2, 4), (5, 6), (9, 10)]

/-- The five comparators of part 7. -/
private def netBlock7 : List Table.Comparator :=
  [(1, 2), (3, 4), (5, 7), (6, 8), (2, 3)]

/-- The five comparators of part 8. -/
private def netBlock8 : List Table.Comparator :=
  [(4, 5), (6, 7), (8, 9), (3, 4), (5, 6)]


set_option maxHeartbeats 2000000 in
/-- Part 0 of the network, WAT 7011 to 7205.  It runs the
comparators 0 to 4 of `Table.sort13Net`. -/
private theorem twp_sort13_chunk0 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r2 r3 r4 r6 r9 r10 r11 r14 r15 r21 r22 r23 r24 r26 r28 r29 : UInt32}
    {r12 r19 r20 r25 r27 : UInt64}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 13) (hroom : v.toNat + 104 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock0 M)
    (hcont : ∀ (y6 y10 y11 : UInt32) (y20 y27 : UInt64),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) y6
        (sAddr v 3) y10 y11 (Table.pairWord (eAt N 1)) (sAddr v 10) (sAddr v 5)
        (Table.pairWord (eAt N 3)) y20 (sAddr v 11) (sAddr v 1) (sAddr v 12)
        (eAt N 12).1 (Table.pairWord (eAt N 2)) (eAt N 10).1 y27 (eAt N 9).1
        (eAt N 7).1 (Value.i32 (eAt N 11).1) f.pad31 f.pad32 f.pad33 f.pad34
        f.pad35 f.pad36 f.pad37 f.pad38 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨netLocals f v r2 r3 r4 r6 r9 r10 r11 r12 r14 r15 r19 r20
        r21 r22 r23 r24 r25 r26 r27 r28 r29 [],
        sort13Part 0 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (0, 12)) (1, 10)) (2, 9)) (3,
      7)) (5, 11)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort13Part0_shape, List.cons_append, List.nil_append]
  -- WAT 7011 to 7045: the comparator of the slots 0 and 12
  have ha0 : (0 : Nat) < M.length := by omega
  have hb0 : (12 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 96 12 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_key_load (k := 12) hb0 hlen hroom rfl
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
  iapply twp_min_addr (i := 0) (j := 12) ha0 hb0 hlen hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 0) (j := 12) ha0 hb0 hlen hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 12) (M := M) (value := (Table.cmpMax keyLt (eAt
    M 0) (eAt M 12)).2) hb0 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 0) (eAt M
    12)).1) (select_max_key (eAt M 0) (eAt M 12))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 12) (M := (M.set 12 ((eAt M 12).1, (Table.cmpMax
    keyLt (eAt M 0) (eAt M 12)).2))) (key := (Table.cmpMax keyLt (eAt M 0) (eAt
    M 12)).1) (lt_set _ hb0) (len_set _ hlen) hroom rfl (key_store_max M hb0
    (Table.cmpMax keyLt (eAt M 0) (eAt M 12)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 0) (M := (M.set 12 (Table.cmpMax keyLt (eAt M 0)
    (eAt M 12)))) (q := (Table.cmpMin keyLt (eAt M 0) (eAt M 12))) (lt_set _
    ha0) (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha0 hb0)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M 0 12 ha0 hb0, ← eAt_lo M 0 12 (by decide) ha0 hb0]
  set M1 := Table.cmpSwap keyLt M (0, 12) with hM1
  have hL1 : M1.length = 13 := by
    rw [hM1, Table.cmpSwap_length]; exact hlen
  -- WAT 7046 to 7085: the comparator of the slots 1 and 10
  have ha1 : (1 : Nat) < M1.length := by omega
  have hb1 : (10 : Nat) < M1.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet]
  iapply twp_key_load (k := 10) hb1 hL1 hroom rfl
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
  iapply twp_min_off (i := 1) (j := 10) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  isimp only [const_addr v 8 1 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 80 10 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_max_value (i := 1) (j := 10) ha1 hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 10) (M := M1) (value := (Table.cmpMax keyLt (eAt
    M1 1) (eAt M1 10)).2) hb1 hL1 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M1 1) (eAt
    M1 10)).1) (select_max_key (eAt M1 1) (eAt M1 10))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 10) (M := (M1.set 10 ((eAt M1 10).1, (Table.cmpMax
    keyLt (eAt M1 1) (eAt M1 10)).2))) (key := (Table.cmpMax keyLt (eAt M1 1)
    (eAt M1 10)).1) (lt_set _ hb1) (len_set _ hL1) hroom rfl (key_store_max M1
    hb1 (Table.cmpMax keyLt (eAt M1 1) (eAt M1 10)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 1) (M := (M1.set 10 (Table.cmpMax keyLt (eAt M1
    1) (eAt M1 10)))) (q := (Table.cmpMin keyLt (eAt M1 1) (eAt M1 10)))
    (lt_set _ ha1) (len_set _ hL1) hroom rfl (cmpSwap_writes M1 (by decide) ha1
    hb1)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M1 1 10 ha1 hb1, ← eAt_lo M1 1 10 (by decide) ha1 hb1, ←
    eAt_step M1 1 10 12 (by decide) (by decide)]
  set M2 := Table.cmpSwap keyLt M1 (1, 10) with hM2
  have hL2 : M2.length = 13 := by
    rw [hM2, Table.cmpSwap_length]; exact hL1
  -- WAT 7086 to 7125: the comparator of the slots 2 and 9
  have ha2 : (2 : Nat) < M2.length := by omega
  have hb2 : (9 : Nat) < M2.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet]
  iapply twp_key_load (k := 9) hb2 hL2 hroom rfl
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
  iapply twp_min_off (i := 2) (j := 9) ha2 hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  isimp only [const_addr v 16 2 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 72 9 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_max_value (i := 2) (j := 9) ha2 hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 9) (M := M2) (value := (Table.cmpMax keyLt (eAt
    M2 2) (eAt M2 9)).2) hb2 hL2 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M2 2) (eAt
    M2 9)).1) (select_max_key (eAt M2 2) (eAt M2 9))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 9) (M := (M2.set 9 ((eAt M2 9).1, (Table.cmpMax
    keyLt (eAt M2 2) (eAt M2 9)).2))) (key := (Table.cmpMax keyLt (eAt M2 2)
    (eAt M2 9)).1) (lt_set _ hb2) (len_set _ hL2) hroom rfl (key_store_max M2
    hb2 (Table.cmpMax keyLt (eAt M2 2) (eAt M2 9)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 2) (M := (M2.set 9 (Table.cmpMax keyLt (eAt M2 2)
    (eAt M2 9)))) (q := (Table.cmpMin keyLt (eAt M2 2) (eAt M2 9))) (lt_set _
    ha2) (len_set _ hL2) hroom rfl (cmpSwap_writes M2 (by decide) ha2 hb2)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M2 2 9 ha2 hb2, ← eAt_lo M2 2 9 (by decide) ha2 hb2, ←
    eAt_step M2 2 9 1 (by decide) (by decide), ← eAt_step M2 2 9 10 (by decide)
    (by decide), ← eAt_step M2 2 9 12 (by decide) (by decide)]
  set M3 := Table.cmpSwap keyLt M2 (2, 9) with hM3
  have hL3 : M3.length = 13 := by
    rw [hM3, Table.cmpSwap_length]; exact hL2
  -- WAT 7126 to 7165: the comparator of the slots 3 and 7
  have ha3 : (3 : Nat) < M3.length := by omega
  have hb3 : (7 : Nat) < M3.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet]
  iapply twp_key_load (k := 7) hb3 hL3 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_key_load (k := 3) ha3 hL3 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 3) (j := 7) ha3 hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  isimp only [const_addr v 24 3 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 56 7 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_max_value (i := 3) (j := 7) ha3 hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 7) (M := M3) (value := (Table.cmpMax keyLt (eAt
    M3 3) (eAt M3 7)).2) hb3 hL3 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M3 3) (eAt
    M3 7)).1) (select_max_key (eAt M3 3) (eAt M3 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 7) (M := (M3.set 7 ((eAt M3 7).1, (Table.cmpMax
    keyLt (eAt M3 3) (eAt M3 7)).2))) (key := (Table.cmpMax keyLt (eAt M3 3)
    (eAt M3 7)).1) (lt_set _ hb3) (len_set _ hL3) hroom rfl (key_store_max M3
    hb3 (Table.cmpMax keyLt (eAt M3 3) (eAt M3 7)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 3) (M := (M3.set 7 (Table.cmpMax keyLt (eAt M3 3)
    (eAt M3 7)))) (q := (Table.cmpMin keyLt (eAt M3 3) (eAt M3 7))) (lt_set _
    ha3) (len_set _ hL3) hroom rfl (cmpSwap_writes M3 (by decide) ha3 hb3)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M3 3 7 ha3 hb3, ← eAt_lo M3 3 7 (by decide) ha3 hb3, ←
    eAt_step M3 3 7 1 (by decide) (by decide), ← eAt_step M3 3 7 2 (by decide)
    (by decide), ← eAt_step M3 3 7 9 (by decide) (by decide), ← eAt_step M3 3 7
    10 (by decide) (by decide), ← eAt_step M3 3 7 12 (by decide) (by decide)]
  set M4 := Table.cmpSwap keyLt M3 (3, 7) with hM4
  have hL4 : M4.length = 13 := by
    rw [hM4, Table.cmpSwap_length]; exact hL3
  -- WAT 7166 to 7205: the comparator of the slots 5 and 11
  have ha4 : (5 : Nat) < M4.length := by omega
  have hb4 : (11 : Nat) < M4.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet]
  iapply twp_key_load (k := 11) hb4 hL4 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_key_load (k := 5) ha4 hL4 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 5) (j := 11) ha4 hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  isimp only [const_addr v 40 5 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 88 11 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_max_value (i := 5) (j := 11) ha4 hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 11) (M := M4) (value := (Table.cmpMax keyLt (eAt
    M4 5) (eAt M4 11)).2) hb4 hL4 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M4 5) (eAt
    M4 11)).1) (select_max_key (eAt M4 5) (eAt M4 11))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 11) (M := (M4.set 11 ((eAt M4 11).1, (Table.cmpMax
    keyLt (eAt M4 5) (eAt M4 11)).2))) (key := (Table.cmpMax keyLt (eAt M4 5)
    (eAt M4 11)).1) (lt_set _ hb4) (len_set _ hL4) hroom rfl (key_store_max M4
    hb4 (Table.cmpMax keyLt (eAt M4 5) (eAt M4 11)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 5) (M := (M4.set 11 (Table.cmpMax keyLt (eAt M4
    5) (eAt M4 11)))) (q := (Table.cmpMin keyLt (eAt M4 5) (eAt M4 11)))
    (lt_set _ ha4) (len_set _ hL4) hroom rfl (cmpSwap_writes M4 (by decide) ha4
    hb4)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M4 5 11 ha4 hb4, ← eAt_lo M4 5 11 (by decide) ha4 hb4, ←
    eAt_step M4 5 11 1 (by decide) (by decide), ← eAt_step M4 5 11 2
    (by decide) (by decide), ← eAt_step M4 5 11 3 (by decide) (by decide), ←
    eAt_step M4 5 11 7 (by decide) (by decide), ← eAt_step M4 5 11 9
    (by decide) (by decide), ← eAt_step M4 5 11 10 (by decide) (by decide), ←
    eAt_step M4 5 11 12 (by decide) (by decide)]
  set M5 := Table.cmpSwap keyLt M4 (5, 11) with hM5
  have hL5 : M5.length = 13 := by
    rw [hM5, Table.cmpSwap_length]; exact hL4
  iapply (hcont _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 1 of the network, WAT 7206 to 7371.  It runs the
comparators 5 to 9 of `Table.sort13Net`. -/
private theorem twp_sort13_chunk1 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r6 r10 r11 : UInt32}
    {r20 r27 : UInt64}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 13) (hroom : v.toNat + 104 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock1 M)
    (hcont : ∀ (y29 : UInt32) (y25 : UInt64) (y34 y35 y36 : Value),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) (Table.pairWord (eAt N 7))
        (sAddr v 10) (sAddr v 5) (Table.pairWord (eAt N 2)) (Table.pairWord
        (eAt N 1)) (sAddr v 11) (sAddr v 1) (sAddr v 12) (eAt N 12).1 y25 (eAt
        N 10).1 (Table.pairWord (eAt N 4)) (eAt N 9).1 y29 (Value.i32 (eAt N
        11).1) (Value.i32 (eAt N 8).1) (Value.i32 (eAt N 6).1) (Value.i32 (eAt
        N 3).1) y34 y35 y36 f.pad37 f.pad38 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) r6
        (sAddr v 3) r10 r11 (Table.pairWord (eAt M 1)) (sAddr v 10) (sAddr v 5)
        (Table.pairWord (eAt M 3)) r20 (sAddr v 11) (sAddr v 1) (sAddr v 12)
        (eAt M 12).1 (Table.pairWord (eAt M 2)) (eAt M 10).1 r27 (eAt M 9).1
        (eAt M 7).1 (Value.i32 (eAt M 11).1) f.pad31 f.pad32 f.pad33 f.pad34
        f.pad35 f.pad36 f.pad37 f.pad38 [],
        sort13Part 1 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (6, 8)) (1, 6)) (2, 3)) (4,
      11)) (7, 9)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort13Part1_shape, List.cons_append, List.nil_append]
  -- WAT 7206 to 7245: the comparator of the slots 6 and 8
  have ha5 : (6 : Nat) < M.length := by omega
  have hb5 : (8 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet]
  iapply twp_key_load (k := 8) hb5 hlen hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_key_load (k := 6) ha5 hlen hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 6) (j := 8) ha5 hb5 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  isimp only [const_addr v 48 6 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 64 8 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  iapply twp_max_value (i := 6) (j := 8) ha5 hb5 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 8) (M := M) (value := (Table.cmpMax keyLt (eAt M
    6) (eAt M 8)).2) hb5 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 6) (eAt M
    8)).1) (select_max_key (eAt M 6) (eAt M 8))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 8) (M := (M.set 8 ((eAt M 8).1, (Table.cmpMax
    keyLt (eAt M 6) (eAt M 8)).2))) (key := (Table.cmpMax keyLt (eAt M 6) (eAt
    M 8)).1) (lt_set _ hb5) (len_set _ hlen) hroom rfl (key_store_max M hb5
    (Table.cmpMax keyLt (eAt M 6) (eAt M 8)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 6) (M := (M.set 8 (Table.cmpMax keyLt (eAt M 6)
    (eAt M 8)))) (q := (Table.cmpMin keyLt (eAt M 6) (eAt M 8))) (lt_set _ ha5)
    (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha5 hb5)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M 6 8 ha5 hb5, ← eAt_lo M 6 8 (by decide) ha5 hb5, ←
    eAt_step M 6 8 1 (by decide) (by decide), ← eAt_step M 6 8 2 (by decide)
    (by decide), ← eAt_step M 6 8 3 (by decide) (by decide), ← eAt_step M 6 8 7
    (by decide) (by decide), ← eAt_step M 6 8 9 (by decide) (by decide), ←
    eAt_step M 6 8 10 (by decide) (by decide), ← eAt_step M 6 8 11 (by decide)
    (by decide), ← eAt_step M 6 8 12 (by decide) (by decide)]
  set M6 := Table.cmpSwap keyLt M (6, 8) with hM6
  have hL6 : M6.length = 13 := by
    rw [hM6, Table.cmpSwap_length]; exact hlen
  -- WAT 7246 to 7275: the comparator of the slots 1 and 6
  have ha6 : (1 : Nat) < M6.length := by omega
  have hb6 : (6 : Nat) < M6.length := by omega
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
  iapply twp_max_value (i := 1) (j := 6) ha6 hb6 hL6 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 6) (M := M6) (value := (Table.cmpMax keyLt (eAt
    M6 1) (eAt M6 6)).2) hb6 hL6 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M6 1) (eAt
    M6 6)).1) (select_max_key (eAt M6 1) (eAt M6 6))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 6) (M := (M6.set 6 ((eAt M6 6).1, (Table.cmpMax
    keyLt (eAt M6 1) (eAt M6 6)).2))) (key := (Table.cmpMax keyLt (eAt M6 1)
    (eAt M6 6)).1) (lt_set _ hb6) (len_set _ hL6) hroom rfl (key_store_max M6
    hb6 (Table.cmpMax keyLt (eAt M6 1) (eAt M6 6)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M6 1) (eAt M6 6)))) (select_min_pair (eAt M6 1) (eAt M6 6))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 1) (M := (M6.set 6 (Table.cmpMax keyLt (eAt M6 1)
    (eAt M6 6)))) (q := (Table.cmpMin keyLt (eAt M6 1) (eAt M6 6))) (lt_set _
    ha6) (len_set _ hL6) hroom rfl (cmpSwap_writes M6 (by decide) ha6 hb6)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M6 1 6 ha6 hb6, ← eAt_lo M6 1 6 (by decide) ha6 hb6, ←
    eAt_step M6 1 6 2 (by decide) (by decide), ← eAt_step M6 1 6 3 (by decide)
    (by decide), ← eAt_step M6 1 6 7 (by decide) (by decide), ← eAt_step M6 1 6
    8 (by decide) (by decide), ← eAt_step M6 1 6 9 (by decide) (by decide), ←
    eAt_step M6 1 6 10 (by decide) (by decide), ← eAt_step M6 1 6 11
    (by decide) (by decide), ← eAt_step M6 1 6 12 (by decide) (by decide)]
  set M7 := Table.cmpSwap keyLt M6 (1, 6) with hM7
  have hL7 : M7.length = 13 := by
    rw [hM7, Table.cmpSwap_length]; exact hL6
  -- WAT 7276 to 7305: the comparator of the slots 2 and 3
  have ha7 : (2 : Nat) < M7.length := by omega
  have hb7 : (3 : Nat) < M7.length := by omega
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
  iapply twp_max_value (i := 2) (j := 3) ha7 hb7 hL7 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 3) (M := M7) (value := (Table.cmpMax keyLt (eAt
    M7 2) (eAt M7 3)).2) hb7 hL7 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M7 2) (eAt
    M7 3)).1) (select_max_key (eAt M7 2) (eAt M7 3))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 3) (M := (M7.set 3 ((eAt M7 3).1, (Table.cmpMax
    keyLt (eAt M7 2) (eAt M7 3)).2))) (key := (Table.cmpMax keyLt (eAt M7 2)
    (eAt M7 3)).1) (lt_set _ hb7) (len_set _ hL7) hroom rfl (key_store_max M7
    hb7 (Table.cmpMax keyLt (eAt M7 2) (eAt M7 3)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M7 2) (eAt M7 3)))) (select_min_pair (eAt M7 2) (eAt M7 3))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 2) (M := (M7.set 3 (Table.cmpMax keyLt (eAt M7 2)
    (eAt M7 3)))) (q := (Table.cmpMin keyLt (eAt M7 2) (eAt M7 3))) (lt_set _
    ha7) (len_set _ hL7) hroom rfl (cmpSwap_writes M7 (by decide) ha7 hb7)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M7 2 3 ha7 hb7, ← eAt_lo M7 2 3 (by decide) ha7 hb7, ←
    eAt_step M7 2 3 1 (by decide) (by decide), ← eAt_step M7 2 3 6 (by decide)
    (by decide), ← eAt_step M7 2 3 7 (by decide) (by decide), ← eAt_step M7 2 3
    8 (by decide) (by decide), ← eAt_step M7 2 3 9 (by decide) (by decide), ←
    eAt_step M7 2 3 10 (by decide) (by decide), ← eAt_step M7 2 3 11
    (by decide) (by decide), ← eAt_step M7 2 3 12 (by decide) (by decide)]
  set M8 := Table.cmpSwap keyLt M7 (2, 3) with hM8
  have hL8 : M8.length = 13 := by
    rw [hM8, Table.cmpSwap_length]; exact hL7
  -- WAT 7306 to 7341: the comparator of the slots 4 and 11
  have ha8 : (4 : Nat) < M8.length := by omega
  have hb8 : (11 : Nat) < M8.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_add]
  isimp only [const_addr v 32 4 rfl]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_key_load (k := 4) ha8 hL8 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 4) (j := 11) ha8 hb8 hL8 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_const twp_localGet]
  iapply twp_min_off (i := 4) (j := 11) ha8 hb8 hL8 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 4) (M := M8) (q := (Table.cmpMin keyLt (eAt M8 4)
    (eAt M8 11))) ha8 hL8 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_value_store (k := 11) (M := (M8.set 4 (Table.cmpMin keyLt (eAt M8
    4) (eAt M8 11)))) (value := (Table.cmpMax keyLt (eAt M8 4) (eAt M8 11)).2)
    (lt_set _ hb8) (len_set _ hL8) hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M8 4) (eAt
    M8 11)).1) (select_max_key (eAt M8 4) (eAt M8 11))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 11) (M := ((M8.set 4 (Table.cmpMin keyLt (eAt M8
    4) (eAt M8 11))).set 11 ((eAt (M8.set 4 (Table.cmpMin keyLt (eAt M8 4) (eAt
    M8 11))) 11).1, (Table.cmpMax keyLt (eAt M8 4) (eAt M8 11)).2))) (key :=
    (Table.cmpMax keyLt (eAt M8 4) (eAt M8 11)).1) (lt_set _ (lt_set _ hb8))
    (len_set _ (len_set _ hL8)) hroom rfl ((key_store_max (M8.set 4
    (Table.cmpMin keyLt (eAt M8 4) (eAt M8 11))) (lt_set _ hb8) (Table.cmpMax
    keyLt (eAt M8 4) (eAt M8 11))).trans (cmpSwap_pair M8 ha8 hb8))
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M8 4 11 ha8 hb8, ← eAt_lo M8 4 11 (by decide) ha8 hb8, ←
    eAt_step M8 4 11 1 (by decide) (by decide), ← eAt_step M8 4 11 2
    (by decide) (by decide), ← eAt_step M8 4 11 3 (by decide) (by decide), ←
    eAt_step M8 4 11 6 (by decide) (by decide), ← eAt_step M8 4 11 7
    (by decide) (by decide), ← eAt_step M8 4 11 8 (by decide) (by decide), ←
    eAt_step M8 4 11 9 (by decide) (by decide), ← eAt_step M8 4 11 10
    (by decide) (by decide), ← eAt_step M8 4 11 12 (by decide) (by decide)]
  set M9 := Table.cmpSwap keyLt M8 (4, 11) with hM9
  have hL9 : M9.length = 13 := by
    rw [hM9, Table.cmpSwap_length]; exact hL8
  -- WAT 7342 to 7371: the comparator of the slots 7 and 9
  have ha9 : (7 : Nat) < M9.length := by omega
  have hb9 : (9 : Nat) < M9.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet twp_localGet
    twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 7) (j := 9) ha9 hb9 hL9 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 7) (j := 9) ha9 hb9 hL9 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 9) (M := M9) (value := (Table.cmpMax keyLt (eAt
    M9 7) (eAt M9 9)).2) hb9 hL9 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M9 7) (eAt
    M9 9)).1) (select_max_key (eAt M9 7) (eAt M9 9))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 9) (M := (M9.set 9 ((eAt M9 9).1, (Table.cmpMax
    keyLt (eAt M9 7) (eAt M9 9)).2))) (key := (Table.cmpMax keyLt (eAt M9 7)
    (eAt M9 9)).1) (lt_set _ hb9) (len_set _ hL9) hroom rfl (key_store_max M9
    hb9 (Table.cmpMax keyLt (eAt M9 7) (eAt M9 9)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 7) (M := (M9.set 9 (Table.cmpMax keyLt (eAt M9 7)
    (eAt M9 9)))) (q := (Table.cmpMin keyLt (eAt M9 7) (eAt M9 9))) (lt_set _
    ha9) (len_set _ hL9) hroom rfl (cmpSwap_writes M9 (by decide) ha9 hb9)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M9 7 9 ha9 hb9, ← eAt_lo M9 7 9 (by decide) ha9 hb9, ←
    eAt_step M9 7 9 1 (by decide) (by decide), ← eAt_step M9 7 9 2 (by decide)
    (by decide), ← eAt_step M9 7 9 3 (by decide) (by decide), ← eAt_step M9 7 9
    4 (by decide) (by decide), ← eAt_step M9 7 9 6 (by decide) (by decide), ←
    eAt_step M9 7 9 8 (by decide) (by decide), ← eAt_step M9 7 9 10 (by decide)
    (by decide), ← eAt_step M9 7 9 11 (by decide) (by decide), ← eAt_step M9 7
    9 12 (by decide) (by decide)]
  set M10 := Table.cmpSwap keyLt M9 (7, 9) with hM10
  have hL10 : M10.length = 13 := by
    rw [hM10, Table.cmpSwap_length]; exact hL9
  iapply (hcont _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 2 of the network, WAT 7372 to 7518.  It runs the
comparators 10 to 14 of `Table.sort13Net`. -/
private theorem twp_sort13_chunk2 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r29 : UInt32}
    {r25 : UInt64}
    {r34 r35 r36 : Value}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 13) (hroom : v.toNat + 104 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock2 M)
    (hcont : ∀ (y12 y20 y25 : UInt64) (y34 y35 y36 : Value),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) y12 (sAddr v 10) (sAddr v 5)
        (Table.pairWord (eAt N 3)) y20 (sAddr v 11) (sAddr v 1) (sAddr v 12)
        (eAt N 12).1 y25 (eAt N 10).1 (Table.pairWord (eAt N 7)) (eAt N 9).1
        (eAt N 4).1 (Value.i32 (eAt N 11).1) (Value.i32 (eAt N 2).1) (Value.i32
        (eAt N 6).1) (Value.i32 (eAt N 8).1) y34 y35 y36 f.pad37 f.pad38 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) (Table.pairWord (eAt M 7))
        (sAddr v 10) (sAddr v 5) (Table.pairWord (eAt M 2)) (Table.pairWord
        (eAt M 1)) (sAddr v 11) (sAddr v 1) (sAddr v 12) (eAt M 12).1 r25 (eAt
        M 10).1 (Table.pairWord (eAt M 4)) (eAt M 9).1 r29 (Value.i32 (eAt M
        11).1) (Value.i32 (eAt M 8).1) (Value.i32 (eAt M 6).1) (Value.i32 (eAt
        M 3).1) r34 r35 r36 f.pad37 f.pad38 [],
        sort13Part 2 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (8, 10)) (0, 4)) (1, 2)) (3,
      6)) (7, 8)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort13Part2_shape, List.cons_append, List.nil_append]
  -- WAT 7372 to 7401: the comparator of the slots 8 and 10
  have ha10 : (8 : Nat) < M.length := by omega
  have hb10 : (10 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet twp_localGet
    twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 8) (j := 10) ha10 hb10 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 8) (j := 10) ha10 hb10 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 10) (M := M) (value := (Table.cmpMax keyLt (eAt
    M 8) (eAt M 10)).2) hb10 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 8) (eAt M
    10)).1) (select_max_key (eAt M 8) (eAt M 10))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 10) (M := (M.set 10 ((eAt M 10).1, (Table.cmpMax
    keyLt (eAt M 8) (eAt M 10)).2))) (key := (Table.cmpMax keyLt (eAt M 8) (eAt
    M 10)).1) (lt_set _ hb10) (len_set _ hlen) hroom rfl (key_store_max M hb10
    (Table.cmpMax keyLt (eAt M 8) (eAt M 10)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 8) (M := (M.set 10 (Table.cmpMax keyLt (eAt M 8)
    (eAt M 10)))) (q := (Table.cmpMin keyLt (eAt M 8) (eAt M 10))) (lt_set _
    ha10) (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha10 hb10)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M 8 10 ha10 hb10, ← eAt_lo M 8 10 (by decide) ha10 hb10,
    ← eAt_step M 8 10 1 (by decide) (by decide), ← eAt_step M 8 10 2
    (by decide) (by decide), ← eAt_step M 8 10 3 (by decide) (by decide), ←
    eAt_step M 8 10 4 (by decide) (by decide), ← eAt_step M 8 10 6 (by decide)
    (by decide), ← eAt_step M 8 10 7 (by decide) (by decide), ← eAt_step M 8 10
    9 (by decide) (by decide), ← eAt_step M 8 10 11 (by decide) (by decide), ←
    eAt_step M 8 10 12 (by decide) (by decide)]
  set M11 := Table.cmpSwap keyLt M (8, 10) with hM11
  have hL11 : M11.length = 13 := by
    rw [hM11, Table.cmpSwap_length]; exact hlen
  -- WAT 7402 to 7431: the comparator of the slots 0 and 4
  have ha11 : (0 : Nat) < M11.length := by omega
  have hb11 : (4 : Nat) < M11.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_key_load (k := 0) ha11 hL11 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 0) (j := 4) ha11 hb11 hL11 hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 4) (M := M11) (value := (Table.cmpMax keyLt (eAt
    M11 0) (eAt M11 4)).2) hb11 hL11 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M11 0) (eAt
    M11 4)).1) (select_max_key (eAt M11 0) (eAt M11 4))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 4) (M := (M11.set 4 ((eAt M11 4).1, (Table.cmpMax
    keyLt (eAt M11 0) (eAt M11 4)).2))) (key := (Table.cmpMax keyLt (eAt M11 0)
    (eAt M11 4)).1) (lt_set _ hb11) (len_set _ hL11) hroom rfl (key_store_max
    M11 hb11 (Table.cmpMax keyLt (eAt M11 0) (eAt M11 4)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 0) (M := (M11.set 4 (Table.cmpMax keyLt (eAt M11
    0) (eAt M11 4)))) (lt_set _ ha11) (len_set _ hL11) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M11 4 0 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M11 0) (eAt M11 4)))) (select_min_pair (eAt M11 0) (eAt M11 4))
  iapply twp_pair_store (k := 0) (M := (M11.set 4 (Table.cmpMax keyLt (eAt M11
    0) (eAt M11 4)))) (q := (Table.cmpMin keyLt (eAt M11 0) (eAt M11 4)))
    (lt_set _ ha11) (len_set _ hL11) hroom rfl (cmpSwap_writes M11 (by decide)
    ha11 hb11)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M11 0 4 ha11 hb11, ← eAt_step M11 0 4 1 (by decide)
    (by decide), ← eAt_step M11 0 4 2 (by decide) (by decide), ← eAt_step M11 0
    4 3 (by decide) (by decide), ← eAt_step M11 0 4 6 (by decide) (by decide),
    ← eAt_step M11 0 4 7 (by decide) (by decide), ← eAt_step M11 0 4 8
    (by decide) (by decide), ← eAt_step M11 0 4 9 (by decide) (by decide), ←
    eAt_step M11 0 4 10 (by decide) (by decide), ← eAt_step M11 0 4 11
    (by decide) (by decide), ← eAt_step M11 0 4 12 (by decide) (by decide)]
  set M12 := Table.cmpSwap keyLt M11 (0, 4) with hM12
  have hL12 : M12.length = 13 := by
    rw [hM12, Table.cmpSwap_length]; exact hL11
  -- WAT 7432 to 7460: the comparator of the slots 1 and 2
  have ha12 : (1 : Nat) < M12.length := by omega
  have hb12 : (2 : Nat) < M12.length := by omega
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
  iapply twp_max_value (i := 1) (j := 2) ha12 hb12 hL12 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 2) (M := M12) (value := (Table.cmpMax keyLt (eAt
    M12 1) (eAt M12 2)).2) hb12 hL12 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M12 1) (eAt
    M12 2)).1) (select_max_key (eAt M12 1) (eAt M12 2))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 2) (M := (M12.set 2 ((eAt M12 2).1, (Table.cmpMax
    keyLt (eAt M12 1) (eAt M12 2)).2))) (key := (Table.cmpMax keyLt (eAt M12 1)
    (eAt M12 2)).1) (lt_set _ hb12) (len_set _ hL12) hroom rfl (key_store_max
    M12 hb12 (Table.cmpMax keyLt (eAt M12 1) (eAt M12 2)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M12 1) (eAt M12 2)))) (select_min_pair (eAt M12 1) (eAt M12 2))
  iapply twp_pair_store (k := 1) (M := (M12.set 2 (Table.cmpMax keyLt (eAt M12
    1) (eAt M12 2)))) (q := (Table.cmpMin keyLt (eAt M12 1) (eAt M12 2)))
    (lt_set _ ha12) (len_set _ hL12) hroom rfl (cmpSwap_writes M12 (by decide)
    ha12 hb12)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M12 1 2 ha12 hb12, ← eAt_step M12 1 2 3 (by decide)
    (by decide), ← eAt_step M12 1 2 4 (by decide) (by decide), ← eAt_step M12 1
    2 6 (by decide) (by decide), ← eAt_step M12 1 2 7 (by decide) (by decide),
    ← eAt_step M12 1 2 8 (by decide) (by decide), ← eAt_step M12 1 2 9
    (by decide) (by decide), ← eAt_step M12 1 2 10 (by decide) (by decide), ←
    eAt_step M12 1 2 11 (by decide) (by decide), ← eAt_step M12 1 2 12
    (by decide) (by decide)]
  set M13 := Table.cmpSwap keyLt M12 (1, 2) with hM13
  have hL13 : M13.length = 13 := by
    rw [hM13, Table.cmpSwap_length]; exact hL12
  -- WAT 7461 to 7488: the comparator of the slots 3 and 6
  have ha13 : (3 : Nat) < M13.length := by omega
  have hb13 : (6 : Nat) < M13.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 3) (j := 6) ha13 hb13 hL13 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 3) (j := 6) ha13 hb13 hL13 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 6) (M := M13) (value := (Table.cmpMax keyLt (eAt
    M13 3) (eAt M13 6)).2) hb13 hL13 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M13 3) (eAt
    M13 6)).1) (select_max_key (eAt M13 3) (eAt M13 6))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 6) (M := (M13.set 6 ((eAt M13 6).1, (Table.cmpMax
    keyLt (eAt M13 3) (eAt M13 6)).2))) (key := (Table.cmpMax keyLt (eAt M13 3)
    (eAt M13 6)).1) (lt_set _ hb13) (len_set _ hL13) hroom rfl (key_store_max
    M13 hb13 (Table.cmpMax keyLt (eAt M13 3) (eAt M13 6)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 3) (M := (M13.set 6 (Table.cmpMax keyLt (eAt M13
    3) (eAt M13 6)))) (q := (Table.cmpMin keyLt (eAt M13 3) (eAt M13 6)))
    (lt_set _ ha13) (len_set _ hL13) hroom rfl (cmpSwap_writes M13 (by decide)
    ha13 hb13)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M13 3 6 ha13 hb13, ← eAt_lo M13 3 6 (by decide) ha13
    hb13, ← eAt_step M13 3 6 2 (by decide) (by decide), ← eAt_step M13 3 6 4
    (by decide) (by decide), ← eAt_step M13 3 6 7 (by decide) (by decide), ←
    eAt_step M13 3 6 8 (by decide) (by decide), ← eAt_step M13 3 6 9
    (by decide) (by decide), ← eAt_step M13 3 6 10 (by decide) (by decide), ←
    eAt_step M13 3 6 11 (by decide) (by decide), ← eAt_step M13 3 6 12
    (by decide) (by decide)]
  set M14 := Table.cmpSwap keyLt M13 (3, 6) with hM14
  have hL14 : M14.length = 13 := by
    rw [hM14, Table.cmpSwap_length]; exact hL13
  -- WAT 7489 to 7518: the comparator of the slots 7 and 8
  have ha14 : (7 : Nat) < M14.length := by omega
  have hb14 : (8 : Nat) < M14.length := by omega
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
  iapply twp_max_value (i := 7) (j := 8) ha14 hb14 hL14 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 8) (M := M14) (value := (Table.cmpMax keyLt (eAt
    M14 7) (eAt M14 8)).2) hb14 hL14 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M14 7) (eAt
    M14 8)).1) (select_max_key (eAt M14 7) (eAt M14 8))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 8) (M := (M14.set 8 ((eAt M14 8).1, (Table.cmpMax
    keyLt (eAt M14 7) (eAt M14 8)).2))) (key := (Table.cmpMax keyLt (eAt M14 7)
    (eAt M14 8)).1) (lt_set _ hb14) (len_set _ hL14) hroom rfl (key_store_max
    M14 hb14 (Table.cmpMax keyLt (eAt M14 7) (eAt M14 8)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M14 7) (eAt M14 8)))) (select_min_pair (eAt M14 7) (eAt M14 8))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 7) (M := (M14.set 8 (Table.cmpMax keyLt (eAt M14
    7) (eAt M14 8)))) (q := (Table.cmpMin keyLt (eAt M14 7) (eAt M14 8)))
    (lt_set _ ha14) (len_set _ hL14) hroom rfl (cmpSwap_writes M14 (by decide)
    ha14 hb14)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M14 7 8 ha14 hb14, ← eAt_lo M14 7 8 (by decide) ha14
    hb14, ← eAt_step M14 7 8 2 (by decide) (by decide), ← eAt_step M14 7 8 3
    (by decide) (by decide), ← eAt_step M14 7 8 4 (by decide) (by decide), ←
    eAt_step M14 7 8 6 (by decide) (by decide), ← eAt_step M14 7 8 9
    (by decide) (by decide), ← eAt_step M14 7 8 10 (by decide) (by decide), ←
    eAt_step M14 7 8 11 (by decide) (by decide), ← eAt_step M14 7 8 12
    (by decide) (by decide)]
  set M15 := Table.cmpSwap keyLt M14 (7, 8) with hM15
  have hL15 : M15.length = 13 := by
    rw [hM15, Table.cmpSwap_length]; exact hL14
  iapply (hcont _ _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 3 of the network, WAT 7519 to 7666.  It runs the
comparators 15 to 19 of `Table.sort13Net`. -/
private theorem twp_sort13_chunk3 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r12 r20 r25 : UInt64}
    {r34 r35 r36 : Value}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 13) (hroom : v.toNat + 104 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock3 M)
    (hcont : ∀ (y12 : UInt64) (y32 y33 y34 y35 y36 : Value),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) y12 (sAddr v 10) (sAddr v 5)
        (Table.pairWord (eAt N 3)) (Table.pairWord (eAt N 4)) (sAddr v 11)
        (sAddr v 1) (sAddr v 12) (eAt N 12).1 (Table.pairWord (eAt N 8)) (eAt N
        10).1 (Table.pairWord (eAt N 7)) (eAt N 6).1 (eAt N 9).1 (Value.i32
        (eAt N 11).1) (Value.i32 (eAt N 2).1) y32 y33 y34 y35 y36 (Value.i64
        (Table.pairWord (eAt N 5))) f.pad38 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) r12 (sAddr v 10) (sAddr v 5)
        (Table.pairWord (eAt M 3)) r20 (sAddr v 11) (sAddr v 1) (sAddr v 12)
        (eAt M 12).1 r25 (eAt M 10).1 (Table.pairWord (eAt M 7)) (eAt M 9).1
        (eAt M 4).1 (Value.i32 (eAt M 11).1) (Value.i32 (eAt M 2).1) (Value.i32
        (eAt M 6).1) (Value.i32 (eAt M 8).1) r34 r35 r36 f.pad37 f.pad38 [],
        sort13Part 3 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (9, 10)) (11, 12)) (4, 6))
      (5, 9)) (8, 11)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort13Part3_shape, List.cons_append, List.nil_append]
  -- WAT 7519 to 7548: the comparator of the slots 9 and 10
  have ha15 : (9 : Nat) < M.length := by omega
  have hb15 : (10 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet twp_localGet
    twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 9) (j := 10) ha15 hb15 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 9) (j := 10) ha15 hb15 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 10) (M := M) (value := (Table.cmpMax keyLt (eAt
    M 9) (eAt M 10)).2) hb15 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 9) (eAt M
    10)).1) (select_max_key (eAt M 9) (eAt M 10))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 10) (M := (M.set 10 ((eAt M 10).1, (Table.cmpMax
    keyLt (eAt M 9) (eAt M 10)).2))) (key := (Table.cmpMax keyLt (eAt M 9) (eAt
    M 10)).1) (lt_set _ hb15) (len_set _ hlen) hroom rfl (key_store_max M hb15
    (Table.cmpMax keyLt (eAt M 9) (eAt M 10)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 9) (M := (M.set 10 (Table.cmpMax keyLt (eAt M 9)
    (eAt M 10)))) (q := (Table.cmpMin keyLt (eAt M 9) (eAt M 10))) (lt_set _
    ha15) (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha15 hb15)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M 9 10 ha15 hb15, ← eAt_lo M 9 10 (by decide) ha15 hb15,
    ← eAt_step M 9 10 2 (by decide) (by decide), ← eAt_step M 9 10 3
    (by decide) (by decide), ← eAt_step M 9 10 4 (by decide) (by decide), ←
    eAt_step M 9 10 6 (by decide) (by decide), ← eAt_step M 9 10 7 (by decide)
    (by decide), ← eAt_step M 9 10 8 (by decide) (by decide), ← eAt_step M 9 10
    11 (by decide) (by decide), ← eAt_step M 9 10 12 (by decide) (by decide)]
  set M16 := Table.cmpSwap keyLt M (9, 10) with hM16
  have hL16 : M16.length = 13 := by
    rw [hM16, Table.cmpSwap_length]; exact hlen
  -- WAT 7549 to 7578: the comparator of the slots 11 and 12
  have ha16 : (11 : Nat) < M16.length := by omega
  have hb16 : (12 : Nat) < M16.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet twp_localGet
    twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 11) (j := 12) ha16 hb16 hL16 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 11) (j := 12) ha16 hb16 hL16 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 12) (M := M16) (value := (Table.cmpMax keyLt
    (eAt M16 11) (eAt M16 12)).2) hb16 hL16 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M16 11)
    (eAt M16 12)).1) (select_max_key (eAt M16 11) (eAt M16 12))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 12) (M := (M16.set 12 ((eAt M16 12).1,
    (Table.cmpMax keyLt (eAt M16 11) (eAt M16 12)).2))) (key := (Table.cmpMax
    keyLt (eAt M16 11) (eAt M16 12)).1) (lt_set _ hb16) (len_set _ hL16) hroom
    rfl (key_store_max M16 hb16 (Table.cmpMax keyLt (eAt M16 11) (eAt M16 12)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 11) (M := (M16.set 12 (Table.cmpMax keyLt (eAt
    M16 11) (eAt M16 12)))) (q := (Table.cmpMin keyLt (eAt M16 11) (eAt M16
    12))) (lt_set _ ha16) (len_set _ hL16) hroom rfl (cmpSwap_writes M16
    (by decide) ha16 hb16)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M16 11 12 ha16 hb16, ← eAt_lo M16 11 12 (by decide) ha16
    hb16, ← eAt_step M16 11 12 2 (by decide) (by decide), ← eAt_step M16 11 12
    3 (by decide) (by decide), ← eAt_step M16 11 12 4 (by decide) (by decide),
    ← eAt_step M16 11 12 6 (by decide) (by decide), ← eAt_step M16 11 12 7
    (by decide) (by decide), ← eAt_step M16 11 12 8 (by decide) (by decide), ←
    eAt_step M16 11 12 9 (by decide) (by decide), ← eAt_step M16 11 12 10
    (by decide) (by decide)]
  set M17 := Table.cmpSwap keyLt M16 (11, 12) with hM17
  have hL17 : M17.length = 13 := by
    rw [hM17, Table.cmpSwap_length]; exact hL16
  -- WAT 7579 to 7606: the comparator of the slots 4 and 6
  have ha17 : (4 : Nat) < M17.length := by omega
  have hb17 : (6 : Nat) < M17.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 4) (j := 6) ha17 hb17 hL17 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 4) (j := 6) ha17 hb17 hL17 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 6) (M := M17) (value := (Table.cmpMax keyLt (eAt
    M17 4) (eAt M17 6)).2) hb17 hL17 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M17 4) (eAt
    M17 6)).1) (select_max_key (eAt M17 4) (eAt M17 6))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 6) (M := (M17.set 6 ((eAt M17 6).1, (Table.cmpMax
    keyLt (eAt M17 4) (eAt M17 6)).2))) (key := (Table.cmpMax keyLt (eAt M17 4)
    (eAt M17 6)).1) (lt_set _ hb17) (len_set _ hL17) hroom rfl (key_store_max
    M17 hb17 (Table.cmpMax keyLt (eAt M17 4) (eAt M17 6)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 4) (M := (M17.set 6 (Table.cmpMax keyLt (eAt M17
    4) (eAt M17 6)))) (q := (Table.cmpMin keyLt (eAt M17 4) (eAt M17 6)))
    (lt_set _ ha17) (len_set _ hL17) hroom rfl (cmpSwap_writes M17 (by decide)
    ha17 hb17)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M17 4 6 ha17 hb17, ← eAt_lo M17 4 6 (by decide) ha17
    hb17, ← eAt_step M17 4 6 2 (by decide) (by decide), ← eAt_step M17 4 6 3
    (by decide) (by decide), ← eAt_step M17 4 6 7 (by decide) (by decide), ←
    eAt_step M17 4 6 8 (by decide) (by decide), ← eAt_step M17 4 6 9
    (by decide) (by decide), ← eAt_step M17 4 6 10 (by decide) (by decide), ←
    eAt_step M17 4 6 11 (by decide) (by decide), ← eAt_step M17 4 6 12
    (by decide) (by decide)]
  set M18 := Table.cmpSwap keyLt M17 (4, 6) with hM18
  have hL18 : M18.length = 13 := by
    rw [hM18, Table.cmpSwap_length]; exact hL17
  -- WAT 7607 to 7637: the comparator of the slots 5 and 9
  have ha18 : (5 : Nat) < M18.length := by omega
  have hb18 : (9 : Nat) < M18.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_key_load (k := 5) ha18 hL18 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 5) (j := 9) ha18 hb18 hL18 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 9) (M := M18) (value := (Table.cmpMax keyLt (eAt
    M18 5) (eAt M18 9)).2) hb18 hL18 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M18 5) (eAt
    M18 9)).1) (select_max_key (eAt M18 5) (eAt M18 9))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 9) (M := (M18.set 9 ((eAt M18 9).1, (Table.cmpMax
    keyLt (eAt M18 5) (eAt M18 9)).2))) (key := (Table.cmpMax keyLt (eAt M18 5)
    (eAt M18 9)).1) (lt_set _ hb18) (len_set _ hL18) hroom rfl (key_store_max
    M18 hb18 (Table.cmpMax keyLt (eAt M18 5) (eAt M18 9)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 5) (M := (M18.set 9 (Table.cmpMax keyLt (eAt M18
    5) (eAt M18 9)))) (lt_set _ ha18) (len_set _ hL18) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M18 9 5 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M18 5) (eAt M18 9)))) (select_min_pair (eAt M18 5) (eAt M18 9))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 5) (M := (M18.set 9 (Table.cmpMax keyLt (eAt M18
    5) (eAt M18 9)))) (q := (Table.cmpMin keyLt (eAt M18 5) (eAt M18 9)))
    (lt_set _ ha18) (len_set _ hL18) hroom rfl (cmpSwap_writes M18 (by decide)
    ha18 hb18)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M18 5 9 ha18 hb18, ← eAt_lo M18 5 9 (by decide) ha18
    hb18, ← eAt_step M18 5 9 2 (by decide) (by decide), ← eAt_step M18 5 9 3
    (by decide) (by decide), ← eAt_step M18 5 9 4 (by decide) (by decide), ←
    eAt_step M18 5 9 6 (by decide) (by decide), ← eAt_step M18 5 9 7
    (by decide) (by decide), ← eAt_step M18 5 9 8 (by decide) (by decide), ←
    eAt_step M18 5 9 10 (by decide) (by decide), ← eAt_step M18 5 9 11
    (by decide) (by decide), ← eAt_step M18 5 9 12 (by decide) (by decide)]
  set M19 := Table.cmpSwap keyLt M18 (5, 9) with hM19
  have hL19 : M19.length = 13 := by
    rw [hM19, Table.cmpSwap_length]; exact hL18
  -- WAT 7638 to 7666: the comparator of the slots 8 and 11
  have ha19 : (8 : Nat) < M19.length := by omega
  have hb19 : (11 : Nat) < M19.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 8) (j := 11) ha19 hb19 hL19 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 11) (M := M19) (value := (Table.cmpMax keyLt
    (eAt M19 8) (eAt M19 11)).2) hb19 hL19 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M19 8) (eAt
    M19 11)).1) (select_max_key (eAt M19 8) (eAt M19 11))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 11) (M := (M19.set 11 ((eAt M19 11).1,
    (Table.cmpMax keyLt (eAt M19 8) (eAt M19 11)).2))) (key := (Table.cmpMax
    keyLt (eAt M19 8) (eAt M19 11)).1) (lt_set _ hb19) (len_set _ hL19) hroom
    rfl (key_store_max M19 hb19 (Table.cmpMax keyLt (eAt M19 8) (eAt M19 11)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 8) (M := (M19.set 11 (Table.cmpMax keyLt (eAt M19
    8) (eAt M19 11)))) (lt_set _ ha19) (len_set _ hL19) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M19 11 8 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M19 8) (eAt M19 11)))) (select_min_pair (eAt M19 8) (eAt M19 11))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 8) (M := (M19.set 11 (Table.cmpMax keyLt (eAt M19
    8) (eAt M19 11)))) (q := (Table.cmpMin keyLt (eAt M19 8) (eAt M19 11)))
    (lt_set _ ha19) (len_set _ hL19) hroom rfl (cmpSwap_writes M19 (by decide)
    ha19 hb19)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M19 8 11 ha19 hb19, ← eAt_lo M19 8 11 (by decide) ha19
    hb19, ← eAt_step M19 8 11 2 (by decide) (by decide), ← eAt_step M19 8 11 3
    (by decide) (by decide), ← eAt_step M19 8 11 4 (by decide) (by decide), ←
    eAt_step M19 8 11 5 (by decide) (by decide), ← eAt_step M19 8 11 6
    (by decide) (by decide), ← eAt_step M19 8 11 7 (by decide) (by decide), ←
    eAt_step M19 8 11 9 (by decide) (by decide), ← eAt_step M19 8 11 10
    (by decide) (by decide), ← eAt_step M19 8 11 12 (by decide) (by decide)]
  set M20 := Table.cmpSwap keyLt M19 (8, 11) with hM20
  have hL20 : M20.length = 13 := by
    rw [hM20, Table.cmpSwap_length]; exact hL19
  iapply (hcont _ _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 4 of the network, WAT 7667 to 7814.  It runs the
comparators 20 to 24 of `Table.sort13Net`. -/
private theorem twp_sort13_chunk4 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r12 : UInt64}
    {r32 r33 r34 r35 r36 : Value}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 13) (hroom : v.toNat + 104 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock4 M)
    (hcont : ∀ (y19 y27 : UInt64) (y30 y32 y33 y34 y35 y36 : Value),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) (Table.pairWord (eAt N 10))
        (sAddr v 10) (sAddr v 5) y19 (Table.pairWord (eAt N 4)) (sAddr v 11)
        (sAddr v 1) (eAt N 5).1 (eAt N 8).1 (Table.pairWord (eAt N 6)) (eAt N
        7).1 y27 (eAt N 11).1 (eAt N 9).1 y30 (Value.i32 (eAt N 2).1) y32 y33
        y34 y35 y36 (Value.i64 (Table.pairWord (eAt N 0))) (Value.i64
        (Table.pairWord (eAt N 3))) [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) r12 (sAddr v 10) (sAddr v 5)
        (Table.pairWord (eAt M 3)) (Table.pairWord (eAt M 4)) (sAddr v 11)
        (sAddr v 1) (sAddr v 12) (eAt M 12).1 (Table.pairWord (eAt M 8)) (eAt M
        10).1 (Table.pairWord (eAt M 7)) (eAt M 6).1 (eAt M 9).1 (Value.i32
        (eAt M 11).1) (Value.i32 (eAt M 2).1) r32 r33 r34 r35 r36 (Value.i64
        (Table.pairWord (eAt M 5))) f.pad38 [],
        sort13Part 4 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (10, 12)) (0, 5)) (3, 8)) (4,
      7)) (6, 11)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort13Part4_shape, List.cons_append, List.nil_append]
  -- WAT 7667 to 7695: the comparator of the slots 10 and 12
  have ha20 : (10 : Nat) < M.length := by omega
  have hb20 : (12 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_const twp_const twp_localGet twp_localGet
    twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_off (i := 10) (j := 12) ha20 hb20 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 10) (j := 12) ha20 hb20 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 12) (M := M) (value := (Table.cmpMax keyLt (eAt
    M 10) (eAt M 12)).2) hb20 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 10) (eAt
    M 12)).1) (select_max_key (eAt M 10) (eAt M 12))
  iapply twp_key_store (k := 12) (M := (M.set 12 ((eAt M 12).1, (Table.cmpMax
    keyLt (eAt M 10) (eAt M 12)).2))) (key := (Table.cmpMax keyLt (eAt M 10)
    (eAt M 12)).1) (lt_set _ hb20) (len_set _ hlen) hroom rfl (key_store_max M
    hb20 (Table.cmpMax keyLt (eAt M 10) (eAt M 12)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 10) (M := (M.set 12 (Table.cmpMax keyLt (eAt M
    10) (eAt M 12)))) (q := (Table.cmpMin keyLt (eAt M 10) (eAt M 12))) (lt_set
    _ ha20) (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha20 hb20)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_lo M 10 12 (by decide) ha20 hb20, ← eAt_step M 10 12 2
    (by decide) (by decide), ← eAt_step M 10 12 3 (by decide) (by decide), ←
    eAt_step M 10 12 4 (by decide) (by decide), ← eAt_step M 10 12 5
    (by decide) (by decide), ← eAt_step M 10 12 6 (by decide) (by decide), ←
    eAt_step M 10 12 7 (by decide) (by decide), ← eAt_step M 10 12 8
    (by decide) (by decide), ← eAt_step M 10 12 9 (by decide) (by decide), ←
    eAt_step M 10 12 11 (by decide) (by decide)]
  set M21 := Table.cmpSwap keyLt M (10, 12) with hM21
  have hL21 : M21.length = 13 := by
    rw [hM21, Table.cmpSwap_length]; exact hlen
  -- WAT 7696 to 7726: the comparator of the slots 0 and 5
  have ha21 : (0 : Nat) < M21.length := by omega
  have hb21 : (5 : Nat) < M21.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_key_load (k := 0) ha21 hL21 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 0) (j := 5) ha21 hb21 hL21 hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 5) (M := M21) (value := (Table.cmpMax keyLt (eAt
    M21 0) (eAt M21 5)).2) hb21 hL21 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M21 0) (eAt
    M21 5)).1) (select_max_key (eAt M21 0) (eAt M21 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 5) (M := (M21.set 5 ((eAt M21 5).1, (Table.cmpMax
    keyLt (eAt M21 0) (eAt M21 5)).2))) (key := (Table.cmpMax keyLt (eAt M21 0)
    (eAt M21 5)).1) (lt_set _ hb21) (len_set _ hL21) hroom rfl (key_store_max
    M21 hb21 (Table.cmpMax keyLt (eAt M21 0) (eAt M21 5)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 0) (M := (M21.set 5 (Table.cmpMax keyLt (eAt M21
    0) (eAt M21 5)))) (lt_set _ ha21) (len_set _ hL21) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M21 5 0 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M21 0) (eAt M21 5)))) (select_min_pair (eAt M21 0) (eAt M21 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 0) (M := (M21.set 5 (Table.cmpMax keyLt (eAt M21
    0) (eAt M21 5)))) (q := (Table.cmpMin keyLt (eAt M21 0) (eAt M21 5)))
    (lt_set _ ha21) (len_set _ hL21) hroom rfl (cmpSwap_writes M21 (by decide)
    ha21 hb21)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M21 0 5 ha21 hb21, ← eAt_lo M21 0 5 (by decide) ha21
    hb21, ← eAt_step M21 0 5 2 (by decide) (by decide), ← eAt_step M21 0 5 3
    (by decide) (by decide), ← eAt_step M21 0 5 4 (by decide) (by decide), ←
    eAt_step M21 0 5 6 (by decide) (by decide), ← eAt_step M21 0 5 7
    (by decide) (by decide), ← eAt_step M21 0 5 8 (by decide) (by decide), ←
    eAt_step M21 0 5 9 (by decide) (by decide), ← eAt_step M21 0 5 10
    (by decide) (by decide), ← eAt_step M21 0 5 11 (by decide) (by decide)]
  set M22 := Table.cmpSwap keyLt M21 (0, 5) with hM22
  have hL22 : M22.length = 13 := by
    rw [hM22, Table.cmpSwap_length]; exact hL21
  -- WAT 7727 to 7756: the comparator of the slots 3 and 8
  have ha22 : (3 : Nat) < M22.length := by omega
  have hb22 : (8 : Nat) < M22.length := by omega
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
  iapply twp_max_value (i := 3) (j := 8) ha22 hb22 hL22 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 8) (M := M22) (value := (Table.cmpMax keyLt (eAt
    M22 3) (eAt M22 8)).2) hb22 hL22 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M22 3) (eAt
    M22 8)).1) (select_max_key (eAt M22 3) (eAt M22 8))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 8) (M := (M22.set 8 ((eAt M22 8).1, (Table.cmpMax
    keyLt (eAt M22 3) (eAt M22 8)).2))) (key := (Table.cmpMax keyLt (eAt M22 3)
    (eAt M22 8)).1) (lt_set _ hb22) (len_set _ hL22) hroom rfl (key_store_max
    M22 hb22 (Table.cmpMax keyLt (eAt M22 3) (eAt M22 8)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M22 3) (eAt M22 8)))) (select_min_pair (eAt M22 3) (eAt M22 8))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 3) (M := (M22.set 8 (Table.cmpMax keyLt (eAt M22
    3) (eAt M22 8)))) (q := (Table.cmpMin keyLt (eAt M22 3) (eAt M22 8)))
    (lt_set _ ha22) (len_set _ hL22) hroom rfl (cmpSwap_writes M22 (by decide)
    ha22 hb22)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M22 3 8 ha22 hb22, ← eAt_lo M22 3 8 (by decide) ha22
    hb22, ← eAt_step M22 3 8 0 (by decide) (by decide), ← eAt_step M22 3 8 2
    (by decide) (by decide), ← eAt_step M22 3 8 4 (by decide) (by decide), ←
    eAt_step M22 3 8 5 (by decide) (by decide), ← eAt_step M22 3 8 6
    (by decide) (by decide), ← eAt_step M22 3 8 7 (by decide) (by decide), ←
    eAt_step M22 3 8 9 (by decide) (by decide), ← eAt_step M22 3 8 10
    (by decide) (by decide), ← eAt_step M22 3 8 11 (by decide) (by decide)]
  set M23 := Table.cmpSwap keyLt M22 (3, 8) with hM23
  have hL23 : M23.length = 13 := by
    rw [hM23, Table.cmpSwap_length]; exact hL22
  -- WAT 7757 to 7786: the comparator of the slots 4 and 7
  have ha23 : (4 : Nat) < M23.length := by omega
  have hb23 : (7 : Nat) < M23.length := by omega
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
  iapply twp_max_value (i := 4) (j := 7) ha23 hb23 hL23 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 7) (M := M23) (value := (Table.cmpMax keyLt (eAt
    M23 4) (eAt M23 7)).2) hb23 hL23 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M23 4) (eAt
    M23 7)).1) (select_max_key (eAt M23 4) (eAt M23 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 7) (M := (M23.set 7 ((eAt M23 7).1, (Table.cmpMax
    keyLt (eAt M23 4) (eAt M23 7)).2))) (key := (Table.cmpMax keyLt (eAt M23 4)
    (eAt M23 7)).1) (lt_set _ hb23) (len_set _ hL23) hroom rfl (key_store_max
    M23 hb23 (Table.cmpMax keyLt (eAt M23 4) (eAt M23 7)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M23 4) (eAt M23 7)))) (select_min_pair (eAt M23 4) (eAt M23 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 4) (M := (M23.set 7 (Table.cmpMax keyLt (eAt M23
    4) (eAt M23 7)))) (q := (Table.cmpMin keyLt (eAt M23 4) (eAt M23 7)))
    (lt_set _ ha23) (len_set _ hL23) hroom rfl (cmpSwap_writes M23 (by decide)
    ha23 hb23)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M23 4 7 ha23 hb23, ← eAt_lo M23 4 7 (by decide) ha23
    hb23, ← eAt_step M23 4 7 0 (by decide) (by decide), ← eAt_step M23 4 7 2
    (by decide) (by decide), ← eAt_step M23 4 7 3 (by decide) (by decide), ←
    eAt_step M23 4 7 5 (by decide) (by decide), ← eAt_step M23 4 7 6
    (by decide) (by decide), ← eAt_step M23 4 7 8 (by decide) (by decide), ←
    eAt_step M23 4 7 9 (by decide) (by decide), ← eAt_step M23 4 7 10
    (by decide) (by decide), ← eAt_step M23 4 7 11 (by decide) (by decide)]
  set M24 := Table.cmpSwap keyLt M23 (4, 7) with hM24
  have hL24 : M24.length = 13 := by
    rw [hM24, Table.cmpSwap_length]; exact hL23
  -- WAT 7787 to 7814: the comparator of the slots 6 and 11
  have ha24 : (6 : Nat) < M24.length := by omega
  have hb24 : (11 : Nat) < M24.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 6) (j := 11) ha24 hb24 hL24 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 6) (j := 11) ha24 hb24 hL24 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 11) (M := M24) (value := (Table.cmpMax keyLt
    (eAt M24 6) (eAt M24 11)).2) hb24 hL24 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M24 6) (eAt
    M24 11)).1) (select_max_key (eAt M24 6) (eAt M24 11))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 11) (M := (M24.set 11 ((eAt M24 11).1,
    (Table.cmpMax keyLt (eAt M24 6) (eAt M24 11)).2))) (key := (Table.cmpMax
    keyLt (eAt M24 6) (eAt M24 11)).1) (lt_set _ hb24) (len_set _ hL24) hroom
    rfl (key_store_max M24 hb24 (Table.cmpMax keyLt (eAt M24 6) (eAt M24 11)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 6) (M := (M24.set 11 (Table.cmpMax keyLt (eAt M24
    6) (eAt M24 11)))) (q := (Table.cmpMin keyLt (eAt M24 6) (eAt M24 11)))
    (lt_set _ ha24) (len_set _ hL24) hroom rfl (cmpSwap_writes M24 (by decide)
    ha24 hb24)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M24 6 11 ha24 hb24, ← eAt_lo M24 6 11 (by decide) ha24
    hb24, ← eAt_step M24 6 11 0 (by decide) (by decide), ← eAt_step M24 6 11 2
    (by decide) (by decide), ← eAt_step M24 6 11 3 (by decide) (by decide), ←
    eAt_step M24 6 11 4 (by decide) (by decide), ← eAt_step M24 6 11 5
    (by decide) (by decide), ← eAt_step M24 6 11 7 (by decide) (by decide), ←
    eAt_step M24 6 11 8 (by decide) (by decide), ← eAt_step M24 6 11 9
    (by decide) (by decide), ← eAt_step M24 6 11 10 (by decide) (by decide)]
  set M25 := Table.cmpSwap keyLt M24 (6, 11) with hM25
  have hL25 : M25.length = 13 := by
    rw [hM25, Table.cmpSwap_length]; exact hL24
  iapply (hcont _ _ _ _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 5 of the network, WAT 7815 to 7961.  It runs the
comparators 25 to 29 of `Table.sort13Net`. -/
private theorem twp_sort13_chunk5 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r19 r27 : UInt64}
    {r30 r32 r33 r34 r35 r36 : Value}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 13) (hroom : v.toNat + 104 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock5 M)
    (hcont : ∀ (y26 : UInt32) (y19 : UInt64) (y32 y33 y34 y35 y36 y37 : Value),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) (Table.pairWord (eAt N 2))
        (sAddr v 10) (sAddr v 5) y19 (Table.pairWord (eAt N 4)) (sAddr v 11)
        (sAddr v 1) (eAt N 5).1 (eAt N 8).1 (Table.pairWord (eAt N 7)) y26
        (Table.pairWord (eAt N 6)) (eAt N 11).1 (eAt N 10).1 (Value.i32 (eAt N
        1).1) (Value.i32 (eAt N 9).1) y32 y33 y34 y35 y36 y37 (Value.i64
        (Table.pairWord (eAt N 3))) [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) (Table.pairWord (eAt M 10))
        (sAddr v 10) (sAddr v 5) r19 (Table.pairWord (eAt M 4)) (sAddr v 11)
        (sAddr v 1) (eAt M 5).1 (eAt M 8).1 (Table.pairWord (eAt M 6)) (eAt M
        7).1 r27 (eAt M 11).1 (eAt M 9).1 r30 (Value.i32 (eAt M 2).1) r32 r33
        r34 r35 r36 (Value.i64 (Table.pairWord (eAt M 0))) (Value.i64
        (Table.pairWord (eAt M 3))) [],
        sort13Part 5 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (9, 10)) (0, 1)) (2, 5)) (6,
      9)) (7, 8)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort13Part5_shape, List.cons_append, List.nil_append]
  -- WAT 7815 to 7843: the comparator of the slots 9 and 10
  have ha25 : (9 : Nat) < M.length := by omega
  have hb25 : (10 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 9) (j := 10) ha25 hb25 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 10) (M := M) (value := (Table.cmpMax keyLt (eAt
    M 9) (eAt M 10)).2) hb25 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 9) (eAt M
    10)).1) (select_max_key (eAt M 9) (eAt M 10))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 10) (M := (M.set 10 ((eAt M 10).1, (Table.cmpMax
    keyLt (eAt M 9) (eAt M 10)).2))) (key := (Table.cmpMax keyLt (eAt M 9) (eAt
    M 10)).1) (lt_set _ hb25) (len_set _ hlen) hroom rfl (key_store_max M hb25
    (Table.cmpMax keyLt (eAt M 9) (eAt M 10)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 9) (M := (M.set 10 (Table.cmpMax keyLt (eAt M 9)
    (eAt M 10)))) (lt_set _ ha25) (len_set _ hlen) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M 10 9 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M 9) (eAt M 10)))) (select_min_pair (eAt M 9) (eAt M 10))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 9) (M := (M.set 10 (Table.cmpMax keyLt (eAt M 9)
    (eAt M 10)))) (q := (Table.cmpMin keyLt (eAt M 9) (eAt M 10))) (lt_set _
    ha25) (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha25 hb25)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M 9 10 ha25 hb25, ← eAt_lo M 9 10 (by decide) ha25 hb25,
    ← eAt_step M 9 10 0 (by decide) (by decide), ← eAt_step M 9 10 2
    (by decide) (by decide), ← eAt_step M 9 10 3 (by decide) (by decide), ←
    eAt_step M 9 10 4 (by decide) (by decide), ← eAt_step M 9 10 5 (by decide)
    (by decide), ← eAt_step M 9 10 6 (by decide) (by decide), ← eAt_step M 9 10
    7 (by decide) (by decide), ← eAt_step M 9 10 8 (by decide) (by decide), ←
    eAt_step M 9 10 11 (by decide) (by decide)]
  set M26 := Table.cmpSwap keyLt M (9, 10) with hM26
  have hL26 : M26.length = 13 := by
    rw [hM26, Table.cmpSwap_length]; exact hlen
  -- WAT 7844 to 7875: the comparator of the slots 0 and 1
  have ha26 : (0 : Nat) < M26.length := by omega
  have hb26 : (1 : Nat) < M26.length := by omega
  wasm_twp_pures [twp_localGet]
  iapply twp_pair_load (k := 1) (M := M26) hb26 hL26 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_key_load (k := 1) hb26 hL26 hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 0) (j := 1) ha26 hb26 hL26 hroom (addr_zero v) rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 1) (M := M26) (value := (Table.cmpMax keyLt (eAt
    M26 0) (eAt M26 1)).2) hb26 hL26 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M26 0) (eAt
    M26 1)).1) (select_max_key (eAt M26 0) (eAt M26 1))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 1) (M := (M26.set 1 ((eAt M26 1).1, (Table.cmpMax
    keyLt (eAt M26 0) (eAt M26 1)).2))) (key := (Table.cmpMax keyLt (eAt M26 0)
    (eAt M26 1)).1) (lt_set _ hb26) (len_set _ hL26) hroom rfl (key_store_max
    M26 hb26 (Table.cmpMax keyLt (eAt M26 0) (eAt M26 1)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M26 0) (eAt M26 1)))) (select_min_pair (eAt M26 0) (eAt M26 1))
  iapply twp_pair_store (k := 0) (M := (M26.set 1 (Table.cmpMax keyLt (eAt M26
    0) (eAt M26 1)))) (q := (Table.cmpMin keyLt (eAt M26 0) (eAt M26 1)))
    (lt_set _ ha26) (len_set _ hL26) hroom rfl (cmpSwap_writes M26 (by decide)
    ha26 hb26)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M26 0 1 ha26 hb26, ← eAt_step M26 0 1 2 (by decide)
    (by decide), ← eAt_step M26 0 1 3 (by decide) (by decide), ← eAt_step M26 0
    1 4 (by decide) (by decide), ← eAt_step M26 0 1 5 (by decide) (by decide),
    ← eAt_step M26 0 1 6 (by decide) (by decide), ← eAt_step M26 0 1 7
    (by decide) (by decide), ← eAt_step M26 0 1 8 (by decide) (by decide), ←
    eAt_step M26 0 1 9 (by decide) (by decide), ← eAt_step M26 0 1 10
    (by decide) (by decide), ← eAt_step M26 0 1 11 (by decide) (by decide)]
  set M27 := Table.cmpSwap keyLt M26 (0, 1) with hM27
  have hL27 : M27.length = 13 := by
    rw [hM27, Table.cmpSwap_length]; exact hL26
  -- WAT 7876 to 7903: the comparator of the slots 2 and 5
  have ha27 : (2 : Nat) < M27.length := by omega
  have hb27 : (5 : Nat) < M27.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 2) (j := 5) ha27 hb27 hL27 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 2) (j := 5) ha27 hb27 hL27 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 5) (M := M27) (value := (Table.cmpMax keyLt (eAt
    M27 2) (eAt M27 5)).2) hb27 hL27 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M27 2) (eAt
    M27 5)).1) (select_max_key (eAt M27 2) (eAt M27 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 5) (M := (M27.set 5 ((eAt M27 5).1, (Table.cmpMax
    keyLt (eAt M27 2) (eAt M27 5)).2))) (key := (Table.cmpMax keyLt (eAt M27 2)
    (eAt M27 5)).1) (lt_set _ hb27) (len_set _ hL27) hroom rfl (key_store_max
    M27 hb27 (Table.cmpMax keyLt (eAt M27 2) (eAt M27 5)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 2) (M := (M27.set 5 (Table.cmpMax keyLt (eAt M27
    2) (eAt M27 5)))) (q := (Table.cmpMin keyLt (eAt M27 2) (eAt M27 5)))
    (lt_set _ ha27) (len_set _ hL27) hroom rfl (cmpSwap_writes M27 (by decide)
    ha27 hb27)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M27 2 5 ha27 hb27, ← eAt_lo M27 2 5 (by decide) ha27
    hb27, ← eAt_step M27 2 5 1 (by decide) (by decide), ← eAt_step M27 2 5 3
    (by decide) (by decide), ← eAt_step M27 2 5 4 (by decide) (by decide), ←
    eAt_step M27 2 5 6 (by decide) (by decide), ← eAt_step M27 2 5 7
    (by decide) (by decide), ← eAt_step M27 2 5 8 (by decide) (by decide), ←
    eAt_step M27 2 5 9 (by decide) (by decide), ← eAt_step M27 2 5 10
    (by decide) (by decide), ← eAt_step M27 2 5 11 (by decide) (by decide)]
  set M28 := Table.cmpSwap keyLt M27 (2, 5) with hM28
  have hL28 : M28.length = 13 := by
    rw [hM28, Table.cmpSwap_length]; exact hL27
  -- WAT 7904 to 7933: the comparator of the slots 6 and 9
  have ha28 : (6 : Nat) < M28.length := by omega
  have hb28 : (9 : Nat) < M28.length := by omega
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
  iapply twp_max_value (i := 6) (j := 9) ha28 hb28 hL28 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 9) (M := M28) (value := (Table.cmpMax keyLt (eAt
    M28 6) (eAt M28 9)).2) hb28 hL28 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M28 6) (eAt
    M28 9)).1) (select_max_key (eAt M28 6) (eAt M28 9))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 9) (M := (M28.set 9 ((eAt M28 9).1, (Table.cmpMax
    keyLt (eAt M28 6) (eAt M28 9)).2))) (key := (Table.cmpMax keyLt (eAt M28 6)
    (eAt M28 9)).1) (lt_set _ hb28) (len_set _ hL28) hroom rfl (key_store_max
    M28 hb28 (Table.cmpMax keyLt (eAt M28 6) (eAt M28 9)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M28 6) (eAt M28 9)))) (select_min_pair (eAt M28 6) (eAt M28 9))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 6) (M := (M28.set 9 (Table.cmpMax keyLt (eAt M28
    6) (eAt M28 9)))) (q := (Table.cmpMin keyLt (eAt M28 6) (eAt M28 9)))
    (lt_set _ ha28) (len_set _ hL28) hroom rfl (cmpSwap_writes M28 (by decide)
    ha28 hb28)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M28 6 9 ha28 hb28, ← eAt_lo M28 6 9 (by decide) ha28
    hb28, ← eAt_step M28 6 9 1 (by decide) (by decide), ← eAt_step M28 6 9 2
    (by decide) (by decide), ← eAt_step M28 6 9 3 (by decide) (by decide), ←
    eAt_step M28 6 9 4 (by decide) (by decide), ← eAt_step M28 6 9 5
    (by decide) (by decide), ← eAt_step M28 6 9 7 (by decide) (by decide), ←
    eAt_step M28 6 9 8 (by decide) (by decide), ← eAt_step M28 6 9 10
    (by decide) (by decide), ← eAt_step M28 6 9 11 (by decide) (by decide)]
  set M29 := Table.cmpSwap keyLt M28 (6, 9) with hM29
  have hL29 : M29.length = 13 := by
    rw [hM29, Table.cmpSwap_length]; exact hL28
  -- WAT 7934 to 7961: the comparator of the slots 7 and 8
  have ha29 : (7 : Nat) < M29.length := by omega
  have hb29 : (8 : Nat) < M29.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 7) (j := 8) ha29 hb29 hL29 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 7) (j := 8) ha29 hb29 hL29 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 8) (M := M29) (value := (Table.cmpMax keyLt (eAt
    M29 7) (eAt M29 8)).2) hb29 hL29 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M29 7) (eAt
    M29 8)).1) (select_max_key (eAt M29 7) (eAt M29 8))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 8) (M := (M29.set 8 ((eAt M29 8).1, (Table.cmpMax
    keyLt (eAt M29 7) (eAt M29 8)).2))) (key := (Table.cmpMax keyLt (eAt M29 7)
    (eAt M29 8)).1) (lt_set _ hb29) (len_set _ hL29) hroom rfl (key_store_max
    M29 hb29 (Table.cmpMax keyLt (eAt M29 7) (eAt M29 8)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 7) (M := (M29.set 8 (Table.cmpMax keyLt (eAt M29
    7) (eAt M29 8)))) (q := (Table.cmpMin keyLt (eAt M29 7) (eAt M29 8)))
    (lt_set _ ha29) (len_set _ hL29) hroom rfl (cmpSwap_writes M29 (by decide)
    ha29 hb29)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M29 7 8 ha29 hb29, ← eAt_lo M29 7 8 (by decide) ha29
    hb29, ← eAt_step M29 7 8 1 (by decide) (by decide), ← eAt_step M29 7 8 2
    (by decide) (by decide), ← eAt_step M29 7 8 3 (by decide) (by decide), ←
    eAt_step M29 7 8 4 (by decide) (by decide), ← eAt_step M29 7 8 5
    (by decide) (by decide), ← eAt_step M29 7 8 6 (by decide) (by decide), ←
    eAt_step M29 7 8 9 (by decide) (by decide), ← eAt_step M29 7 8 10
    (by decide) (by decide), ← eAt_step M29 7 8 11 (by decide) (by decide)]
  set M30 := Table.cmpSwap keyLt M29 (7, 8) with hM30
  have hL30 : M30.length = 13 := by
    rw [hM30, Table.cmpSwap_length]; exact hL29
  iapply (hcont _ _ _ _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 6 of the network, WAT 7962 to 8104.  It runs the
comparators 30 to 34 of `Table.sort13Net`. -/
private theorem twp_sort13_chunk6 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r26 : UInt32}
    {r19 : UInt64}
    {r32 r33 r34 r35 r36 r37 : Value}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 13) (hroom : v.toNat + 104 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock6 M)
    (hcont : ∀ (y14 y28 y29 : UInt32) (y27 : UInt64) (y30 y31 y32 y33 y34 y35
      y36 y38 : Value),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) (Table.pairWord (eAt N 2)) y14
        (sAddr v 5) (Table.pairWord (eAt N 9)) (Table.pairWord (eAt N 5)) (eAt
        N 3).1 (sAddr v 1) (eAt N 6).1 (eAt N 8).1 (Table.pairWord (eAt N 7))
        (eAt N 4).1 y27 y28 y29 y30 y31 y32 y33 y34 y35 y36 (Value.i64
        (Table.pairWord (eAt N 1))) y38 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) (Table.pairWord (eAt M 2))
        (sAddr v 10) (sAddr v 5) r19 (Table.pairWord (eAt M 4)) (sAddr v 11)
        (sAddr v 1) (eAt M 5).1 (eAt M 8).1 (Table.pairWord (eAt M 7)) r26
        (Table.pairWord (eAt M 6)) (eAt M 11).1 (eAt M 10).1 (Value.i32 (eAt M
        1).1) (Value.i32 (eAt M 9).1) r32 r33 r34 r35 r36 r37 (Value.i64
        (Table.pairWord (eAt M 3))) [],
        sort13Part 6 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (10, 11)) (1, 3)) (2, 4)) (5,
      6)) (9, 10)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort13Part6_shape, List.cons_append, List.nil_append]
  -- WAT 7962 to 7988: the comparator of the slots 10 and 11
  have ha30 : (10 : Nat) < M.length := by omega
  have hb30 : (11 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 10) (j := 11) ha30 hb30 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 10) (j := 11) ha30 hb30 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 11) (M := M) (value := (Table.cmpMax keyLt (eAt
    M 10) (eAt M 11)).2) hb30 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 10) (eAt
    M 11)).1) (select_max_key (eAt M 10) (eAt M 11))
  iapply twp_key_store (k := 11) (M := (M.set 11 ((eAt M 11).1, (Table.cmpMax
    keyLt (eAt M 10) (eAt M 11)).2))) (key := (Table.cmpMax keyLt (eAt M 10)
    (eAt M 11)).1) (lt_set _ hb30) (len_set _ hlen) hroom rfl (key_store_max M
    hb30 (Table.cmpMax keyLt (eAt M 10) (eAt M 11)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 10) (M := (M.set 11 (Table.cmpMax keyLt (eAt M
    10) (eAt M 11)))) (q := (Table.cmpMin keyLt (eAt M 10) (eAt M 11))) (lt_set
    _ ha30) (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha30 hb30)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_lo M 10 11 (by decide) ha30 hb30, ← eAt_step M 10 11 1
    (by decide) (by decide), ← eAt_step M 10 11 2 (by decide) (by decide), ←
    eAt_step M 10 11 3 (by decide) (by decide), ← eAt_step M 10 11 4
    (by decide) (by decide), ← eAt_step M 10 11 5 (by decide) (by decide), ←
    eAt_step M 10 11 6 (by decide) (by decide), ← eAt_step M 10 11 7
    (by decide) (by decide), ← eAt_step M 10 11 8 (by decide) (by decide), ←
    eAt_step M 10 11 9 (by decide) (by decide)]
  set M31 := Table.cmpSwap keyLt M (10, 11) with hM31
  have hL31 : M31.length = 13 := by
    rw [hM31, Table.cmpSwap_length]; exact hlen
  -- WAT 7989 to 8017: the comparator of the slots 1 and 3
  have ha31 : (1 : Nat) < M31.length := by omega
  have hb31 : (3 : Nat) < M31.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 1) (j := 3) ha31 hb31 hL31 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 3) (M := M31) (value := (Table.cmpMax keyLt (eAt
    M31 1) (eAt M31 3)).2) hb31 hL31 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M31 1) (eAt
    M31 3)).1) (select_max_key (eAt M31 1) (eAt M31 3))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 3) (M := (M31.set 3 ((eAt M31 3).1, (Table.cmpMax
    keyLt (eAt M31 1) (eAt M31 3)).2))) (key := (Table.cmpMax keyLt (eAt M31 1)
    (eAt M31 3)).1) (lt_set _ hb31) (len_set _ hL31) hroom rfl (key_store_max
    M31 hb31 (Table.cmpMax keyLt (eAt M31 1) (eAt M31 3)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 1) (M := (M31.set 3 (Table.cmpMax keyLt (eAt M31
    1) (eAt M31 3)))) (lt_set _ ha31) (len_set _ hL31) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M31 3 1 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M31 1) (eAt M31 3)))) (select_min_pair (eAt M31 1) (eAt M31 3))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 1) (M := (M31.set 3 (Table.cmpMax keyLt (eAt M31
    1) (eAt M31 3)))) (q := (Table.cmpMin keyLt (eAt M31 1) (eAt M31 3)))
    (lt_set _ ha31) (len_set _ hL31) hroom rfl (cmpSwap_writes M31 (by decide)
    ha31 hb31)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M31 1 3 ha31 hb31, ← eAt_lo M31 1 3 (by decide) ha31
    hb31, ← eAt_step M31 1 3 2 (by decide) (by decide), ← eAt_step M31 1 3 4
    (by decide) (by decide), ← eAt_step M31 1 3 5 (by decide) (by decide), ←
    eAt_step M31 1 3 6 (by decide) (by decide), ← eAt_step M31 1 3 7
    (by decide) (by decide), ← eAt_step M31 1 3 8 (by decide) (by decide), ←
    eAt_step M31 1 3 9 (by decide) (by decide), ← eAt_step M31 1 3 10
    (by decide) (by decide)]
  set M32 := Table.cmpSwap keyLt M31 (1, 3) with hM32
  have hL32 : M32.length = 13 := by
    rw [hM32, Table.cmpSwap_length]; exact hL31
  -- WAT 8018 to 8047: the comparator of the slots 2 and 4
  have ha32 : (2 : Nat) < M32.length := by omega
  have hb32 : (4 : Nat) < M32.length := by omega
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
  iapply twp_max_value (i := 2) (j := 4) ha32 hb32 hL32 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 4) (M := M32) (value := (Table.cmpMax keyLt (eAt
    M32 2) (eAt M32 4)).2) hb32 hL32 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M32 2) (eAt
    M32 4)).1) (select_max_key (eAt M32 2) (eAt M32 4))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 4) (M := (M32.set 4 ((eAt M32 4).1, (Table.cmpMax
    keyLt (eAt M32 2) (eAt M32 4)).2))) (key := (Table.cmpMax keyLt (eAt M32 2)
    (eAt M32 4)).1) (lt_set _ hb32) (len_set _ hL32) hroom rfl (key_store_max
    M32 hb32 (Table.cmpMax keyLt (eAt M32 2) (eAt M32 4)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M32 2) (eAt M32 4)))) (select_min_pair (eAt M32 2) (eAt M32 4))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 2) (M := (M32.set 4 (Table.cmpMax keyLt (eAt M32
    2) (eAt M32 4)))) (q := (Table.cmpMin keyLt (eAt M32 2) (eAt M32 4)))
    (lt_set _ ha32) (len_set _ hL32) hroom rfl (cmpSwap_writes M32 (by decide)
    ha32 hb32)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M32 2 4 ha32 hb32, ← eAt_lo M32 2 4 (by decide) ha32
    hb32, ← eAt_step M32 2 4 1 (by decide) (by decide), ← eAt_step M32 2 4 3
    (by decide) (by decide), ← eAt_step M32 2 4 5 (by decide) (by decide), ←
    eAt_step M32 2 4 6 (by decide) (by decide), ← eAt_step M32 2 4 7
    (by decide) (by decide), ← eAt_step M32 2 4 8 (by decide) (by decide), ←
    eAt_step M32 2 4 9 (by decide) (by decide), ← eAt_step M32 2 4 10
    (by decide) (by decide)]
  set M33 := Table.cmpSwap keyLt M32 (2, 4) with hM33
  have hL33 : M33.length = 13 := by
    rw [hM33, Table.cmpSwap_length]; exact hL32
  -- WAT 8048 to 8076: the comparator of the slots 5 and 6
  have ha33 : (5 : Nat) < M33.length := by omega
  have hb33 : (6 : Nat) < M33.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 5) (j := 6) ha33 hb33 hL33 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 6) (M := M33) (value := (Table.cmpMax keyLt (eAt
    M33 5) (eAt M33 6)).2) hb33 hL33 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M33 5) (eAt
    M33 6)).1) (select_max_key (eAt M33 5) (eAt M33 6))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 6) (M := (M33.set 6 ((eAt M33 6).1, (Table.cmpMax
    keyLt (eAt M33 5) (eAt M33 6)).2))) (key := (Table.cmpMax keyLt (eAt M33 5)
    (eAt M33 6)).1) (lt_set _ hb33) (len_set _ hL33) hroom rfl (key_store_max
    M33 hb33 (Table.cmpMax keyLt (eAt M33 5) (eAt M33 6)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 5) (M := (M33.set 6 (Table.cmpMax keyLt (eAt M33
    5) (eAt M33 6)))) (lt_set _ ha33) (len_set _ hL33) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M33 6 5 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M33 5) (eAt M33 6)))) (select_min_pair (eAt M33 5) (eAt M33 6))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 5) (M := (M33.set 6 (Table.cmpMax keyLt (eAt M33
    5) (eAt M33 6)))) (q := (Table.cmpMin keyLt (eAt M33 5) (eAt M33 6)))
    (lt_set _ ha33) (len_set _ hL33) hroom rfl (cmpSwap_writes M33 (by decide)
    ha33 hb33)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M33 5 6 ha33 hb33, ← eAt_lo M33 5 6 (by decide) ha33
    hb33, ← eAt_step M33 5 6 1 (by decide) (by decide), ← eAt_step M33 5 6 2
    (by decide) (by decide), ← eAt_step M33 5 6 3 (by decide) (by decide), ←
    eAt_step M33 5 6 4 (by decide) (by decide), ← eAt_step M33 5 6 7
    (by decide) (by decide), ← eAt_step M33 5 6 8 (by decide) (by decide), ←
    eAt_step M33 5 6 9 (by decide) (by decide), ← eAt_step M33 5 6 10
    (by decide) (by decide)]
  set M34 := Table.cmpSwap keyLt M33 (5, 6) with hM34
  have hL34 : M34.length = 13 := by
    rw [hM34, Table.cmpSwap_length]; exact hL33
  -- WAT 8077 to 8104: the comparator of the slots 9 and 10
  have ha34 : (9 : Nat) < M34.length := by omega
  have hb34 : (10 : Nat) < M34.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 9) (j := 10) ha34 hb34 hL34 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 10) (M := M34) (value := (Table.cmpMax keyLt
    (eAt M34 9) (eAt M34 10)).2) hb34 hL34 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M34 9) (eAt
    M34 10)).1) (select_max_key (eAt M34 9) (eAt M34 10))
  iapply twp_key_store (k := 10) (M := (M34.set 10 ((eAt M34 10).1,
    (Table.cmpMax keyLt (eAt M34 9) (eAt M34 10)).2))) (key := (Table.cmpMax
    keyLt (eAt M34 9) (eAt M34 10)).1) (lt_set _ hb34) (len_set _ hL34) hroom
    rfl (key_store_max M34 hb34 (Table.cmpMax keyLt (eAt M34 9) (eAt M34 10)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 9) (M := (M34.set 10 (Table.cmpMax keyLt (eAt M34
    9) (eAt M34 10)))) (lt_set _ ha34) (len_set _ hL34) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M34 10 9 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M34 9) (eAt M34 10)))) (select_min_pair (eAt M34 9) (eAt M34 10))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 9) (M := (M34.set 10 (Table.cmpMax keyLt (eAt M34
    9) (eAt M34 10)))) (q := (Table.cmpMin keyLt (eAt M34 9) (eAt M34 10)))
    (lt_set _ ha34) (len_set _ hL34) hroom rfl (cmpSwap_writes M34 (by decide)
    ha34 hb34)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_lo M34 9 10 (by decide) ha34 hb34, ← eAt_step M34 9 10 1
    (by decide) (by decide), ← eAt_step M34 9 10 2 (by decide) (by decide), ←
    eAt_step M34 9 10 3 (by decide) (by decide), ← eAt_step M34 9 10 4
    (by decide) (by decide), ← eAt_step M34 9 10 5 (by decide) (by decide), ←
    eAt_step M34 9 10 6 (by decide) (by decide), ← eAt_step M34 9 10 7
    (by decide) (by decide), ← eAt_step M34 9 10 8 (by decide) (by decide)]
  set M35 := Table.cmpSwap keyLt M34 (9, 10) with hM35
  have hL35 : M35.length = 13 := by
    rw [hM35, Table.cmpSwap_length]; exact hL34
  iapply (hcont _ _ _ _ _ _ _ _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 7 of the network, WAT 8105 to 8247.  It runs the
comparators 35 to 39 of `Table.sort13Net`. -/
private theorem twp_sort13_chunk7 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r14 r28 r29 : UInt32}
    {r27 : UInt64}
    {r30 r31 r32 r33 r34 r35 r36 r38 : Value}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 13) (hroom : v.toNat + 104 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock7 M)
    (hcont : ∀ (y3 y24 y26 y28 y29 : UInt32) (y12 y27 : UInt64) (y30 y31 y32
      y33 y34 y35 y36 y37 y38 : Value),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) y3 (sAddr v 7) (sAddr v 6)
        (sAddr v 3) (sAddr v 8) (sAddr v 4) y12 (eAt N 3).1 (sAddr v 5)
        (Table.pairWord (eAt N 9)) (Table.pairWord (eAt N 5)) (eAt N 4).1 (eAt
        N 7).1 (eAt N 8).1 y24 (Table.pairWord (eAt N 6)) y26 y27 y28 y29 y30
        y31 y32 y33 y34 y35 y36 y37 y38 [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) (sAddr v 2) (sAddr v 7) (sAddr
        v 6) (sAddr v 3) (sAddr v 8) (sAddr v 4) (Table.pairWord (eAt M 2)) r14
        (sAddr v 5) (Table.pairWord (eAt M 9)) (Table.pairWord (eAt M 5)) (eAt
        M 3).1 (sAddr v 1) (eAt M 6).1 (eAt M 8).1 (Table.pairWord (eAt M 7))
        (eAt M 4).1 r27 r28 r29 r30 r31 r32 r33 r34 r35 r36 (Value.i64
        (Table.pairWord (eAt M 1))) r38 [],
        sort13Part 7 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (1, 2)) (3, 4)) (5, 7)) (6,
      8)) (2, 3)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort13Part7_shape, List.cons_append, List.nil_append]
  -- WAT 8105 to 8133: the comparator of the slots 1 and 2
  have ha35 : (1 : Nat) < M.length := by omega
  have hb35 : (2 : Nat) < M.length := by omega
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
  iapply twp_max_value (i := 1) (j := 2) ha35 hb35 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 2) (M := M) (value := (Table.cmpMax keyLt (eAt M
    1) (eAt M 2)).2) hb35 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 1) (eAt M
    2)).1) (select_max_key (eAt M 1) (eAt M 2))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 2) (M := (M.set 2 ((eAt M 2).1, (Table.cmpMax
    keyLt (eAt M 1) (eAt M 2)).2))) (key := (Table.cmpMax keyLt (eAt M 1) (eAt
    M 2)).1) (lt_set _ hb35) (len_set _ hlen) hroom rfl (key_store_max M hb35
    (Table.cmpMax keyLt (eAt M 1) (eAt M 2)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M 1) (eAt M 2)))) (select_min_pair (eAt M 1) (eAt M 2))
  iapply twp_pair_store (k := 1) (M := (M.set 2 (Table.cmpMax keyLt (eAt M 1)
    (eAt M 2)))) (q := (Table.cmpMin keyLt (eAt M 1) (eAt M 2))) (lt_set _
    ha35) (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha35 hb35)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M 1 2 ha35 hb35, ← eAt_step M 1 2 3 (by decide)
    (by decide), ← eAt_step M 1 2 4 (by decide) (by decide), ← eAt_step M 1 2 5
    (by decide) (by decide), ← eAt_step M 1 2 6 (by decide) (by decide), ←
    eAt_step M 1 2 7 (by decide) (by decide), ← eAt_step M 1 2 8 (by decide)
    (by decide), ← eAt_step M 1 2 9 (by decide) (by decide)]
  set M36 := Table.cmpSwap keyLt M (1, 2) with hM36
  have hL36 : M36.length = 13 := by
    rw [hM36, Table.cmpSwap_length]; exact hlen
  -- WAT 8134 to 8161: the comparator of the slots 3 and 4
  have ha36 : (3 : Nat) < M36.length := by omega
  have hb36 : (4 : Nat) < M36.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 3) (j := 4) ha36 hb36 hL36 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 3) (j := 4) ha36 hb36 hL36 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 4) (M := M36) (value := (Table.cmpMax keyLt (eAt
    M36 3) (eAt M36 4)).2) hb36 hL36 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M36 3) (eAt
    M36 4)).1) (select_max_key (eAt M36 3) (eAt M36 4))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 4) (M := (M36.set 4 ((eAt M36 4).1, (Table.cmpMax
    keyLt (eAt M36 3) (eAt M36 4)).2))) (key := (Table.cmpMax keyLt (eAt M36 3)
    (eAt M36 4)).1) (lt_set _ hb36) (len_set _ hL36) hroom rfl (key_store_max
    M36 hb36 (Table.cmpMax keyLt (eAt M36 3) (eAt M36 4)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 3) (M := (M36.set 4 (Table.cmpMax keyLt (eAt M36
    3) (eAt M36 4)))) (q := (Table.cmpMin keyLt (eAt M36 3) (eAt M36 4)))
    (lt_set _ ha36) (len_set _ hL36) hroom rfl (cmpSwap_writes M36 (by decide)
    ha36 hb36)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M36 3 4 ha36 hb36, ← eAt_lo M36 3 4 (by decide) ha36
    hb36, ← eAt_step M36 3 4 2 (by decide) (by decide), ← eAt_step M36 3 4 5
    (by decide) (by decide), ← eAt_step M36 3 4 6 (by decide) (by decide), ←
    eAt_step M36 3 4 7 (by decide) (by decide), ← eAt_step M36 3 4 8
    (by decide) (by decide), ← eAt_step M36 3 4 9 (by decide) (by decide)]
  set M37 := Table.cmpSwap keyLt M36 (3, 4) with hM37
  have hL37 : M37.length = 13 := by
    rw [hM37, Table.cmpSwap_length]; exact hL36
  -- WAT 8162 to 8191: the comparator of the slots 5 and 7
  have ha37 : (5 : Nat) < M37.length := by omega
  have hb37 : (7 : Nat) < M37.length := by omega
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
  iapply twp_max_value (i := 5) (j := 7) ha37 hb37 hL37 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 7) (M := M37) (value := (Table.cmpMax keyLt (eAt
    M37 5) (eAt M37 7)).2) hb37 hL37 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M37 5) (eAt
    M37 7)).1) (select_max_key (eAt M37 5) (eAt M37 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 7) (M := (M37.set 7 ((eAt M37 7).1, (Table.cmpMax
    keyLt (eAt M37 5) (eAt M37 7)).2))) (key := (Table.cmpMax keyLt (eAt M37 5)
    (eAt M37 7)).1) (lt_set _ hb37) (len_set _ hL37) hroom rfl (key_store_max
    M37 hb37 (Table.cmpMax keyLt (eAt M37 5) (eAt M37 7)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M37 5) (eAt M37 7)))) (select_min_pair (eAt M37 5) (eAt M37 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 5) (M := (M37.set 7 (Table.cmpMax keyLt (eAt M37
    5) (eAt M37 7)))) (q := (Table.cmpMin keyLt (eAt M37 5) (eAt M37 7)))
    (lt_set _ ha37) (len_set _ hL37) hroom rfl (cmpSwap_writes M37 (by decide)
    ha37 hb37)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M37 5 7 ha37 hb37, ← eAt_lo M37 5 7 (by decide) ha37
    hb37, ← eAt_step M37 5 7 2 (by decide) (by decide), ← eAt_step M37 5 7 3
    (by decide) (by decide), ← eAt_step M37 5 7 4 (by decide) (by decide), ←
    eAt_step M37 5 7 6 (by decide) (by decide), ← eAt_step M37 5 7 8
    (by decide) (by decide), ← eAt_step M37 5 7 9 (by decide) (by decide)]
  set M38 := Table.cmpSwap keyLt M37 (5, 7) with hM38
  have hL38 : M38.length = 13 := by
    rw [hM38, Table.cmpSwap_length]; exact hL37
  -- WAT 8192 to 8219: the comparator of the slots 6 and 8
  have ha38 : (6 : Nat) < M38.length := by omega
  have hb38 : (8 : Nat) < M38.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_ltU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_min_addr (i := 6) (j := 8) ha38 hb38 hL38 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_max_value (i := 6) (j := 8) ha38 hb38 hL38 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 8) (M := M38) (value := (Table.cmpMax keyLt (eAt
    M38 6) (eAt M38 8)).2) hb38 hL38 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M38 6) (eAt
    M38 8)).1) (select_max_key (eAt M38 6) (eAt M38 8))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 8) (M := (M38.set 8 ((eAt M38 8).1, (Table.cmpMax
    keyLt (eAt M38 6) (eAt M38 8)).2))) (key := (Table.cmpMax keyLt (eAt M38 6)
    (eAt M38 8)).1) (lt_set _ hb38) (len_set _ hL38) hroom rfl (key_store_max
    M38 hb38 (Table.cmpMax keyLt (eAt M38 6) (eAt M38 8)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_pair_store (k := 6) (M := (M38.set 8 (Table.cmpMax keyLt (eAt M38
    6) (eAt M38 8)))) (q := (Table.cmpMin keyLt (eAt M38 6) (eAt M38 8)))
    (lt_set _ ha38) (len_set _ hL38) hroom rfl (cmpSwap_writes M38 (by decide)
    ha38 hb38)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M38 6 8 ha38 hb38, ← eAt_lo M38 6 8 (by decide) ha38
    hb38, ← eAt_step M38 6 8 2 (by decide) (by decide), ← eAt_step M38 6 8 3
    (by decide) (by decide), ← eAt_step M38 6 8 4 (by decide) (by decide), ←
    eAt_step M38 6 8 5 (by decide) (by decide), ← eAt_step M38 6 8 7
    (by decide) (by decide), ← eAt_step M38 6 8 9 (by decide) (by decide)]
  set M39 := Table.cmpSwap keyLt M38 (6, 8) with hM39
  have hL39 : M39.length = 13 := by
    rw [hM39, Table.cmpSwap_length]; exact hL38
  -- WAT 8220 to 8247: the comparator of the slots 2 and 3
  have ha39 : (2 : Nat) < M39.length := by omega
  have hb39 : (3 : Nat) < M39.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 2) (j := 3) ha39 hb39 hL39 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 3) (M := M39) (value := (Table.cmpMax keyLt (eAt
    M39 2) (eAt M39 3)).2) hb39 hL39 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M39 2) (eAt
    M39 3)).1) (select_max_key (eAt M39 2) (eAt M39 3))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 3) (M := (M39.set 3 ((eAt M39 3).1, (Table.cmpMax
    keyLt (eAt M39 2) (eAt M39 3)).2))) (key := (Table.cmpMax keyLt (eAt M39 2)
    (eAt M39 3)).1) (lt_set _ hb39) (len_set _ hL39) hroom rfl (key_store_max
    M39 hb39 (Table.cmpMax keyLt (eAt M39 2) (eAt M39 3)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 2) (M := (M39.set 3 (Table.cmpMax keyLt (eAt M39
    2) (eAt M39 3)))) (lt_set _ ha39) (len_set _ hL39) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M39 3 2 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M39 2) (eAt M39 3)))) (select_min_pair (eAt M39 2) (eAt M39 3))
  iapply twp_pair_store (k := 2) (M := (M39.set 3 (Table.cmpMax keyLt (eAt M39
    2) (eAt M39 3)))) (q := (Table.cmpMin keyLt (eAt M39 2) (eAt M39 3)))
    (lt_set _ ha39) (len_set _ hL39) hroom rfl (cmpSwap_writes M39 (by decide)
    ha39 hb39)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M39 2 3 ha39 hb39, ← eAt_step M39 2 3 4 (by decide)
    (by decide), ← eAt_step M39 2 3 5 (by decide) (by decide), ← eAt_step M39 2
    3 6 (by decide) (by decide), ← eAt_step M39 2 3 7 (by decide) (by decide),
    ← eAt_step M39 2 3 8 (by decide) (by decide), ← eAt_step M39 2 3 9
    (by decide) (by decide)]
  set M40 := Table.cmpSwap keyLt M39 (2, 3) with hM40
  have hL40 : M40.length = 13 := by
    rw [hM40, Table.cmpSwap_length]; exact hL39
  iapply (hcont _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

set_option maxHeartbeats 2000000 in
/-- Part 8 of the network, WAT 8248 to 8391.  It runs the
comparators 40 to 44 of `Table.sort13Net`. -/
private theorem twp_sort13_chunk8 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r3 r24 r26 r28 r29 : UInt32}
    {r12 r27 : UInt64}
    {r30 r31 r32 r33 r34 r35 r36 r37 r38 : Value}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 13) (hroom : v.toNat + 104 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt netBlock8 M)
    (hcont : ∀ (y2 y3 y4 y9 y10 y11 y14 y15 y21 y22 y23 y24 y26 y28 y29 :
      UInt32) (y12 y19 y20 y25 y27 : UInt64) (y30 y31 y32 y33 y34 y35 y36 y37
      y38 : Value),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v y2 y3 y4 13 y9 y10 y11 y12 y14 y15 y19 y20
        y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 y32 y33 y34 y35 y36 y37 y38
        [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v (sAddr v 9) r3 (sAddr v 7) (sAddr v 6)
        (sAddr v 3) (sAddr v 8) (sAddr v 4) r12 (eAt M 3).1 (sAddr v 5)
        (Table.pairWord (eAt M 9)) (Table.pairWord (eAt M 5)) (eAt M 4).1 (eAt
        M 7).1 (eAt M 8).1 r24 (Table.pairWord (eAt M 6)) r26 r27 r28 r29 r30
        r31 r32 r33 r34 r35 r36 r37 r38 [],
        sort13Part 8 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hNval : N =
    (Table.cmpSwap keyLt (Table.cmpSwap keyLt (Table.cmpSwap keyLt
      (Table.cmpSwap keyLt (Table.cmpSwap keyLt M (4, 5)) (6, 7)) (8, 9)) (3,
      4)) (5, 6)) := by
    rw [hN]; rfl
  subst hNval
  iintro ⟨Hbuf, HRest⟩
  simp only [sort13Part8_shape, List.cons_append, List.nil_append]
  -- WAT 8248 to 8276: the comparator of the slots 4 and 5
  have ha40 : (4 : Nat) < M.length := by omega
  have hb40 : (5 : Nat) < M.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 4) (j := 5) ha40 hb40 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 5) (M := M) (value := (Table.cmpMax keyLt (eAt M
    4) (eAt M 5)).2) hb40 hlen hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M 4) (eAt M
    5)).1) (select_max_key (eAt M 4) (eAt M 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_key_store (k := 5) (M := (M.set 5 ((eAt M 5).1, (Table.cmpMax
    keyLt (eAt M 4) (eAt M 5)).2))) (key := (Table.cmpMax keyLt (eAt M 4) (eAt
    M 5)).1) (lt_set _ hb40) (len_set _ hlen) hroom rfl (key_store_max M hb40
    (Table.cmpMax keyLt (eAt M 4) (eAt M 5)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 4) (M := (M.set 5 (Table.cmpMax keyLt (eAt M 4)
    (eAt M 5)))) (lt_set _ ha40) (len_set _ hlen) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M 5 4 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M 4) (eAt M 5)))) (select_min_pair (eAt M 4) (eAt M 5))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 4) (M := (M.set 5 (Table.cmpMax keyLt (eAt M 4)
    (eAt M 5)))) (q := (Table.cmpMin keyLt (eAt M 4) (eAt M 5))) (lt_set _
    ha40) (len_set _ hlen) hroom rfl (cmpSwap_writes M (by decide) ha40 hb40)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_hi M 4 5 ha40 hb40, ← eAt_lo M 4 5 (by decide) ha40 hb40, ←
    eAt_step M 4 5 3 (by decide) (by decide), ← eAt_step M 4 5 6 (by decide)
    (by decide), ← eAt_step M 4 5 7 (by decide) (by decide), ← eAt_step M 4 5 8
    (by decide) (by decide), ← eAt_step M 4 5 9 (by decide) (by decide)]
  set M41 := Table.cmpSwap keyLt M (4, 5) with hM41
  have hL41 : M41.length = 13 := by
    rw [hM41, Table.cmpSwap_length]; exact hlen
  -- WAT 8277 to 8306: the comparator of the slots 6 and 7
  have ha41 : (6 : Nat) < M41.length := by omega
  have hb41 : (7 : Nat) < M41.length := by omega
  wasm_twp_pures [twp_localGet]
  iapply twp_pair_load (k := 7) (M := M41) hb41 hL41 hroom rfl
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
  iapply twp_max_value (i := 6) (j := 7) ha41 hb41 hL41 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 7) (M := M41) (value := (Table.cmpMax keyLt (eAt
    M41 6) (eAt M41 7)).2) hb41 hL41 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M41 6) (eAt
    M41 7)).1) (select_max_key (eAt M41 6) (eAt M41 7))
  iapply twp_key_store (k := 7) (M := (M41.set 7 ((eAt M41 7).1, (Table.cmpMax
    keyLt (eAt M41 6) (eAt M41 7)).2))) (key := (Table.cmpMax keyLt (eAt M41 6)
    (eAt M41 7)).1) (lt_set _ hb41) (len_set _ hL41) hroom rfl (key_store_max
    M41 hb41 (Table.cmpMax keyLt (eAt M41 6) (eAt M41 7)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M41 6) (eAt M41 7)))) (select_min_pair (eAt M41 6) (eAt M41 7))
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_pair_store (k := 6) (M := (M41.set 7 (Table.cmpMax keyLt (eAt M41
    6) (eAt M41 7)))) (q := (Table.cmpMin keyLt (eAt M41 6) (eAt M41 7)))
    (lt_set _ ha41) (len_set _ hL41) hroom rfl (cmpSwap_writes M41 (by decide)
    ha41 hb41)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_lo M41 6 7 (by decide) ha41 hb41, ← eAt_step M41 6 7 3
    (by decide) (by decide), ← eAt_step M41 6 7 4 (by decide) (by decide), ←
    eAt_step M41 6 7 5 (by decide) (by decide), ← eAt_step M41 6 7 8
    (by decide) (by decide), ← eAt_step M41 6 7 9 (by decide) (by decide)]
  set M42 := Table.cmpSwap keyLt M41 (6, 7) with hM42
  have hL42 : M42.length = 13 := by
    rw [hM42, Table.cmpSwap_length]; exact hL41
  -- WAT 8307 to 8335: the comparator of the slots 8 and 9
  have ha42 : (8 : Nat) < M42.length := by omega
  have hb42 : (9 : Nat) < M42.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 8) (j := 9) ha42 hb42 hL42 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M42 8) (eAt
    M42 9)).1) (select_max_key (eAt M42 8) (eAt M42 9))
  iapply twp_key_store (k := 9) (M := M42) (key := (Table.cmpMax keyLt (eAt M42
    8) (eAt M42 9)).1) hb42 hL42 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply twp_value_store (k := 9) (M := (M42.set 9 ((Table.cmpMax keyLt (eAt
    M42 8) (eAt M42 9)).1, (eAt M42 9).2))) (value := (Table.cmpMax keyLt (eAt
    M42 8) (eAt M42 9)).2) (lt_set _ hb42) (len_set _ hL42) hroom rfl
    (value_store_max M42 hb42 (Table.cmpMax keyLt (eAt M42 8) (eAt M42 9)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 8) (M := (M42.set 9 (Table.cmpMax keyLt (eAt M42
    8) (eAt M42 9)))) (lt_set _ ha42) (len_set _ hL42) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M42 9 8 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M42 8) (eAt M42 9)))) (select_min_pair (eAt M42 8) (eAt M42 9))
  iapply twp_pair_store (k := 8) (M := (M42.set 9 (Table.cmpMax keyLt (eAt M42
    8) (eAt M42 9)))) (q := (Table.cmpMin keyLt (eAt M42 8) (eAt M42 9)))
    (lt_set _ ha42) (len_set _ hL42) hroom rfl (cmpSwap_writes M42 (by decide)
    ha42 hb42)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M42 8 9 3 (by decide) (by decide), ← eAt_step M42 8 9
    4 (by decide) (by decide), ← eAt_step M42 8 9 5 (by decide) (by decide), ←
    eAt_step M42 8 9 6 (by decide) (by decide)]
  set M43 := Table.cmpSwap keyLt M42 (8, 9) with hM43
  have hL43 : M43.length = 13 := by
    rw [hM43, Table.cmpSwap_length]; exact hL42
  -- WAT 8336 to 8362: the comparator of the slots 3 and 4
  have ha43 : (3 : Nat) < M43.length := by omega
  have hb43 : (4 : Nat) < M43.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 3) (j := 4) ha43 hb43 hL43 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 4) (M := M43) (value := (Table.cmpMax keyLt (eAt
    M43 3) (eAt M43 4)).2) hb43 hL43 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M43 3) (eAt
    M43 4)).1) (select_max_key (eAt M43 3) (eAt M43 4))
  iapply twp_key_store (k := 4) (M := (M43.set 4 ((eAt M43 4).1, (Table.cmpMax
    keyLt (eAt M43 3) (eAt M43 4)).2))) (key := (Table.cmpMax keyLt (eAt M43 3)
    (eAt M43 4)).1) (lt_set _ hb43) (len_set _ hL43) hroom rfl (key_store_max
    M43 hb43 (Table.cmpMax keyLt (eAt M43 3) (eAt M43 4)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 3) (M := (M43.set 4 (Table.cmpMax keyLt (eAt M43
    3) (eAt M43 4)))) (lt_set _ ha43) (len_set _ hL43) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M43 4 3 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M43 3) (eAt M43 4)))) (select_min_pair (eAt M43 3) (eAt M43 4))
  iapply twp_pair_store (k := 3) (M := (M43.set 4 (Table.cmpMax keyLt (eAt M43
    3) (eAt M43 4)))) (q := (Table.cmpMin keyLt (eAt M43 3) (eAt M43 4)))
    (lt_set _ ha43) (len_set _ hL43) hroom rfl (cmpSwap_writes M43 (by decide)
    ha43 hb43)
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [← eAt_step M43 3 4 5 (by decide) (by decide), ← eAt_step M43 3 4
    6 (by decide) (by decide)]
  set M44 := Table.cmpSwap keyLt M43 (3, 4) with hM44
  have hL44 : M44.length = 13 := by
    rw [hM44, Table.cmpSwap_length]; exact hL43
  -- WAT 8363 to 8389: the comparator of the slots 5 and 6
  have ha44 : (5 : Nat) < M44.length := by omega
  have hb44 : (6 : Nat) < M44.length := by omega
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_wrapI64]
  isimp only [pairWord_low]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_gtU]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply twp_max_value (i := 5) (j := 6) ha44 hb44 hL44 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  iapply twp_value_store (k := 6) (M := M44) (value := (Table.cmpMax keyLt (eAt
    M44 5) (eAt M44 6)).2) hb44 hL44 hroom rfl rfl
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_localGet twp_gtU]
  iapply twp_select (selected := Value.i32 (Table.cmpMax keyLt (eAt M44 5) (eAt
    M44 6)).1) (select_max_key (eAt M44 5) (eAt M44 6))
  iapply twp_key_store (k := 6) (M := (M44.set 6 ((eAt M44 6).1, (Table.cmpMax
    keyLt (eAt M44 5) (eAt M44 6)).2))) (key := (Table.cmpMax keyLt (eAt M44 5)
    (eAt M44 6)).1) (lt_set _ hb44) (len_set _ hL44) hroom rfl (key_store_max
    M44 hb44 (Table.cmpMax keyLt (eAt M44 5) (eAt M44 6)))
  isplitl_exact Hbuf
  iintro Hbuf
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_pair_load (k := 5) (M := (M44.set 6 (Table.cmpMax keyLt (eAt M44
    5) (eAt M44 6)))) (lt_set _ ha44) (len_set _ hL44) hroom rfl
  isplitl_exact Hbuf
  iintro Hbuf
  isimp only [eAt_set_ne M44 6 5 (by decide)]
  wasm_twp_pures [twp_localGet]
  iapply twp_select (selected := Value.i64 (Table.pairWord (Table.cmpMin keyLt
    (eAt M44 5) (eAt M44 6)))) (select_min_pair (eAt M44 5) (eAt M44 6))
  iapply twp_pair_store (k := 5) (M := (M44.set 6 (Table.cmpMax keyLt (eAt M44
    5) (eAt M44 6)))) (q := (Table.cmpMin keyLt (eAt M44 5) (eAt M44 6)))
    (lt_set _ ha44) (len_set _ hL44) hroom rfl (cmpSwap_writes M44 (by decide)
    ha44 hb44)
  isplitl_exact Hbuf
  iintro Hbuf
  set M45 := Table.cmpSwap keyLt M44 (5, 6) with hM45
  have hL45 : M45.length = 13 := by
    rw [hM45, Table.cmpSwap_length]; exact hL44
  -- WAT 8390 and 8391: the network result
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  iapply (hcont _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  isplitl [Hbuf]
  · iexact Hbuf
  · iexact HRest

/-! ## The whole network -/

/-- A comparator block keeps the length. -/
private theorem applyNetwork_len {blk : List Table.Comparator}
    {L : List (UInt32 × UInt32)} (h : L.length = 13) :
    (Table.applyNetwork keyLt blk L).length = 13 := by
  rw [Table.applyNetwork_length]; exact h

/-- The nine parts, run in a row, are the whole network. -/
private theorem netBlocks_chain (M : List (UInt32 × UInt32)) :
    (Table.applyNetwork keyLt netBlock8 (Table.applyNetwork keyLt netBlock7
      (Table.applyNetwork keyLt netBlock6 (Table.applyNetwork keyLt netBlock5
      (Table.applyNetwork keyLt netBlock4 (Table.applyNetwork keyLt netBlock3
      (Table.applyNetwork keyLt netBlock2 (Table.applyNetwork keyLt netBlock1
      (Table.applyNetwork keyLt netBlock0 M))))))))) =
      Table.applyNetwork keyLt Table.sort13Net M := by
  have hsplit : Table.sort13Net = netBlock0 ++ netBlock1 ++ netBlock2 ++
      netBlock3 ++ netBlock4 ++ netBlock5 ++ netBlock6 ++ netBlock7 ++
      netBlock8 := by rfl
  rw [hsplit, Table.applyNetwork_append, Table.applyNetwork_append,
    Table.applyNetwork_append, Table.applyNetwork_append,
    Table.applyNetwork_append, Table.applyNetwork_append,
    Table.applyNetwork_append, Table.applyNetwork_append]

set_option maxHeartbeats 2000000 in
/-- The thirteen-entry sorting network of the `quicksort` body, WAT
7011 to 8391.  It runs `Table.sort13Net` on the thirteen entries at
the region base and then writes 13 into local 6.  Every other register
that the region writes is dead when the region ends. -/
theorem twp_sort13 [WasmSmallStepGS hlc Universal.State]
    {f : NetRegs} {v : UInt32} {M N : List (UInt32 × UInt32)}
    {r2 r3 r4 r6 r9 r10 r11 r14 r15 r21 r22 r23 r24 r26 r28 r29 : UInt32}
    {r12 r19 r20 r25 r27 : UInt64}
    {Rest : HeapIProp} {rest : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : M.length = 13) (hroom : v.toNat + 104 < UInt32.size)
    (hN : N = Table.applyNetwork keyLt Table.sort13Net M)
    (hcont : ∀ (y2 y3 y4 y9 y10 y11 y14 y15 y21 y22 y23 y24 y26 y28 y29 :
      UInt32) (y12 y19 y20 y25 y27 : UInt64) (y30 y31 y32 y33 y34 y35 y36 y37
      y38 : Value),
      iprop(Table.PairSlice 0 v N ∗ Rest) ⊢
      WP (.running ⟨net13Locals f v y2 y3 y4 13 y9 y10 y11 y12 y14 y15 y19 y20
        y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 y32 y33 y34 y35 y36 y37 y38
        [],
        rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 v M ∗ Rest) ⊢
      WP (.running ⟨netLocals f v r2 r3 r4 r6 r9 r10 r11 r12 r14 r15 r19 r20
        r21 r22 r23 r24 r25 r26 r27 r28 r29 [],
        qsSort13 ++ rest, arity, remainder, controls,
        calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  rw [qsSort13_parts]
  simp only [List.append_assoc]
  refine twp_sort13_chunk0 hlen hroom rfl ?_
  intro a6 a10 a11 a20 a27
  refine twp_sort13_chunk1 (applyNetwork_len hlen) hroom rfl ?_
  intro b25 b29 b34 b35 b36
  refine twp_sort13_chunk2 (applyNetwork_len (applyNetwork_len hlen)) hroom rfl
    ?_
  intro c12 c20 c25 c34 c35 c36
  refine twp_sort13_chunk3 (applyNetwork_len (applyNetwork_len
    (applyNetwork_len hlen))) hroom rfl ?_
  intro d12 d32 d33 d34 d35 d36
  refine twp_sort13_chunk4 (applyNetwork_len (applyNetwork_len
    (applyNetwork_len (applyNetwork_len hlen)))) hroom rfl ?_
  intro e19 e27 e30 e32 e33 e34 e35 e36
  refine twp_sort13_chunk5 (applyNetwork_len (applyNetwork_len
    (applyNetwork_len (applyNetwork_len (applyNetwork_len hlen))))) hroom rfl
    ?_
  intro f19 f26 f32 f33 f34 f35 f36 f37
  refine twp_sort13_chunk6 (applyNetwork_len (applyNetwork_len
    (applyNetwork_len (applyNetwork_len (applyNetwork_len (applyNetwork_len
    hlen)))))) hroom rfl ?_
  intro g14 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g38
  refine twp_sort13_chunk7 (applyNetwork_len (applyNetwork_len
    (applyNetwork_len (applyNetwork_len (applyNetwork_len (applyNetwork_len
    (applyNetwork_len hlen))))))) hroom rfl ?_
  intro h3 h12 h24 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38
  refine twp_sort13_chunk8 (applyNetwork_len (applyNetwork_len
    (applyNetwork_len (applyNetwork_len (applyNetwork_len (applyNetwork_len
    (applyNetwork_len (applyNetwork_len hlen)))))))) hroom rfl ?_
  intro i2 i3 i4 i9 i10 i11 i12 i14 i15 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28
    i29 i30 i31 i32 i33 i34 i35 i36 i37 i38
  rw [netBlocks_chain M, ← hN]
  exact hcont i2 i3 i4 i9 i10 i11 i12 i14 i15 i19 i20 i21 i22 i23 i24 i25 i26
    i27 i28 i29 i30 i31 i32 i33 i34 i35 i36 i37 i38


end Project.RustHashMap.Func21Network13
