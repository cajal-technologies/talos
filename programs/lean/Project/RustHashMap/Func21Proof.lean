import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func21Merge
import Project.RustHashMap.Func21Partition
import Project.RustHashMap.Func20Proof
import Project.RustHashMap.Func22Proof

/-!
# Proof of `quicksort`, absolute `func 24`

Absolute `func 24` is `quicksort`, local `func21`, WAT lines 5670 to 8663
of `programs/rust/build/rust_hash_map/program.wat`.  This module proves
`SortContracts.Func21Spec`.  It is the assembly of the body: the four
regions that `Func21Partition`, `Func21Network9`, `Func21Network13`,
`Func21Region` and `Func21Merge` prove are used as black boxes here.

## The shape of the body

The body takes a frame of 256 bytes at WAT 5672 to 5676 and gives it
back at WAT 8659 to 8662.  Between them stand four blocks.  A length
below 33 leaves block `@4` at once and reaches the small sort.  A length
of 33 or more runs the quicksort loop `@5`.

One turn of the loop does four steps:

1. WAT 5687 to 5693 call the heap sort and leave when the recursion
   limit is zero.  This is the live edge X-F24-HEAP.
2. WAT 5695 to 5757 pick a pivot.  A length of 64 or more calls
   `func 23`, and a shorter one runs an inline median of three.  Both
   answers are an entry address of the buffer, so the pivot index is
   below the length.
3. WAT 5758 to 6151 partition.  The equal-key partition of WAT 5772 to
   5975 is dead, which is the row X-F24-EQUAL; `twp_equal_guard` proves
   the guard false.  The strict partition is `twp_strict_partition`.
4. WAT 6152 to 6185 put the pivot in its place, call `func 24` on the
   left part, and move the buffer, the length and the ancestor to the
   right part.

## The invariant of the loop

The loop keeps two runs.  `done` holds the entries that are already in
key order and in place, and `rest` holds the entries that the buffer
still has to sort.  Every key of `done` is below every key of `rest`, so
a sorted `rest` next to `done` is a sorted whole.  The measure is
`rest.length`, which drops by `numLt + 1` in each turn.

## The ancestor cell

The body carries the address of one entry, the pivot of the parent, and
reads its key at WAT 5763.  The top call carries none.  `ancOwn` is the
one resource that the loop keeps for it:

```
AncestorCell cur ∗ (AncestorCell cur -∗ AncestorCell anc ∗ PairSlice v0 done)
```

In the first turn `cur` is the ancestor of the caller and `done` is
empty, so the wand is the identity.  In a later turn `cur` is the key
cell of the last entry of `done`, which `PairSlice_key` cuts out, and
the wand holds the ancestor of the caller as well.  At the end of the
loop the wand gives both back.

`ancAt` picks the option: an address of zero carries no cell, because
the contract of a child asks for a pointer that is not null and the
guard at WAT 5760 leaves on a null pointer anyway.

## The stack

The frame is the 256 bytes right below the stack pointer of the caller.
`frame_split` cuts it off once, at WAT 5676, and `frame_join` puts it
back, at WAT 8662.  The loop keeps the whole region below the frame,
`256 * limit` bytes, and hands the child the top `256 * cur` bytes of it
at WAT 6173, which is `quicksortDepth (cur - 1)`.  The heap arm fires
when `cur` is zero, so `1 <= cur` holds at every call.

## The induction

`Func21Upto N` is the contract for an input below `N` entries.
`func21_upto` proves it by strong induction on `N`, which is the form
that `Func20Proof.twp_func20_upto` uses.  The child of WAT 6173 gets a
part that is strictly shorter than the input, so the induction closes.
-/

namespace Project.RustHashMap.Func21Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.SortContracts
open Project.RustHashMap.Func21Defs
open Project.RustHashMap.Func21Partition
open Project.RustHashMap.Func21Region
open scoped Wasm.SmallStep.Outcome

set_option maxRecDepth 40000

/-! ## The index of the module -/

private theorem func21_index :
    Project.RustHashMap.«module».funcs[21]? =
      some Project.RustHashMap.func21Def := by rfl


/-! ## Arithmetic bridges

Every lemma of this section is about `UInt32` addresses or about the
`Nat` sizes of the stack region.  They carry no ownership. -/

/-- The frame pointer of the body. -/
private theorem depth_eq (limit : UInt32) :
    quicksortDepth limit.toNat = 256 * limit.toNat + 256 := by
  unfold quicksortDepth
  omega

/-- The region below the frame is the whole region without the frame. -/
private theorem depth_cut (limit : UInt32) :
    quicksortDepth limit.toNat - 256 = 256 * limit.toNat := by
  rw [depth_eq]
  omega

/-- The frame pointer as a subtraction by a literal. -/
private theorem fp_eq (sp : UInt32) : sp - UInt32.ofNat 256 = sp - 256 :=
  rfl

/-- The address of entry `i` of a buffer that starts `k` entries above
another. -/
private theorem addr_add (v : UInt32) (i m : Nat) :
    v + UInt32.ofNat (8 * i) + UInt32.ofNat (8 * m)
      = v + UInt32.ofNat (8 * (i + m)) := by
  rw [show 8 * (i + m) = 8 * i + 8 * m from by omega, UInt32.ofNat_add,
    UInt32.add_assoc]

/-- `i32.add` puts the second operand first. -/
private theorem addr_shift (v : UInt32) (i m : Nat) :
    UInt32.ofNat (8 * m) + (v + UInt32.ofNat (8 * i))
      = v + UInt32.ofNat (8 * (i + m)) := by
  rw [UInt32.add_comm (UInt32.ofNat (8 * m)) (v + UInt32.ofNat (8 * i)),
    addr_add]

/-- The address of entry zero is the base. -/
private theorem addr_zero (v : UInt32) :
    v = v + UInt32.ofNat (8 * 0) := by
  simp

/-- `i32.shr_u` by three is a division by eight. -/
private theorem shr_three (x : UInt32) :
    x >>> ((3 : UInt32) % 32) = UInt32.ofNat (x.toNat / 8) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hx := UInt32.toNat_lt x
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight,
    show ((3 : UInt32) % 32).toNat % 32 = 3 from by decide,
    Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 3 = 8 from by norm_num,
    UInt32.toNat_ofNat_of_lt' (by omega)]

/-- `i32.shl` by three is a multiplication by one entry. -/
private theorem shl_three (x : UInt32)
    (hbound : 8 * x.toNat < UInt32.size) :
    x <<< ((3 : UInt32) % 32) = UInt32.ofNat (8 * x.toNat) := by
  have hsz : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft,
    show ((3 : UInt32) % 32).toNat % 32 = 3 from by decide,
    Nat.shiftLeft_eq, show (2 : Nat) ^ 3 = 8 from by norm_num,
    Nat.mod_eq_of_lt (by omega : x.toNat * 8 < 2 ^ 32),
    UInt32.toNat_ofNat_of_lt' (by omega)]
  omega

/-- `i32.shl` by five is a multiplication by four entries. -/
private theorem shl_five (x : UInt32)
    (hbound : 32 * x.toNat < UInt32.size) :
    x <<< ((5 : UInt32) % 32) = UInt32.ofNat (8 * (4 * x.toNat)) := by
  have hsz : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft,
    show ((5 : UInt32) % 32).toNat % 32 = 5 from by decide,
    Nat.shiftLeft_eq, show (2 : Nat) ^ 5 = 32 from by norm_num,
    Nat.mod_eq_of_lt (by omega : x.toNat * 32 < 2 ^ 32),
    UInt32.toNat_ofNat_of_lt' (by omega)]
  omega

/-- `i32.mul` by fifty-six is a multiplication by seven entries. -/
private theorem mul_fifty_six (x : UInt32)
    (hbound : 56 * x.toNat < UInt32.size) :
    (56 : UInt32) * x = UInt32.ofNat (8 * (7 * x.toNat)) := by
  have hsz : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mul, show (56 : UInt32).toNat = 56 from rfl,
    Nat.mod_eq_of_lt (by omega : 56 * x.toNat < 2 ^ 32),
    UInt32.toNat_ofNat_of_lt' (by omega)]
  omega

/-- A number below the size of a word is the word of its own number. -/
private theorem ofNat_toNat {k : Nat} (h : k < UInt32.size) :
    (UInt32.ofNat k).toNat = k :=
  UInt32.toNat_ofNat_of_lt' h

/-- Push `Value.i32` through a `select`. -/
private theorem ite_i32 (c : Prop) [Decidable c] (x y : UInt32) :
    (if c then Value.i32 x else Value.i32 y)
      = Value.i32 (if c then x else y) := by
  split <;> rfl

/-- Two `select` instructions between three entry addresses answer with
an entry address.  The proof never looks at the two conditions. -/
private theorem select_addr3 (v a b c : UInt32) (i j l : Nat)
    (P : Nat → Prop) (ha : a = v + UInt32.ofNat (8 * i))
    (hb : b = v + UInt32.ofNat (8 * j))
    (hc : c = v + UInt32.ofNat (8 * l))
    (hi : P i) (hj : P j) (hl : P l) (x y : UInt32) :
    ∃ m : Nat, P m ∧
      (if x ≠ 0 then a else if y ≠ 0 then b else c)
        = v + UInt32.ofNat (8 * m) := by
  by_cases hx : x ≠ 0
  · exact ⟨i, hi, by rw [if_pos hx, ha]⟩
  · by_cases hy : y ≠ 0
    · exact ⟨j, hj, by rw [if_neg hx, if_pos hy, hb]⟩
    · exact ⟨l, hl, by rw [if_neg hx, if_neg hy, hc]⟩

/-! ## One memory step on one entry

The five rules below are copies of the private rules of
`Func21Partition`.  They hide the cell arithmetic of one entry. -/

private theorem getElem_entryAt (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : ps[i] = entryAt ps i :=
  (entryAt_eq_getElem ps hi).symm

private theorem set_pair_self (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) :
    ps.set i ((entryAt ps i).1, (entryAt ps i).2) = ps :=
  set_entryAt ps hi

/-- Move an owned word between two names of one address. -/
private theorem wordMove32 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 (α := α) 0 address value ⊢
      pointsTo_u32 0 address' value := by
  rw [haddress]

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

/-- The key cell of entry `k` of a buffer that does not wrap. -/
private theorem cell_facts32 (v : UInt32) (k n : Nat) (hk : k < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    (v + UInt32.ofNat (8 * k) + 1).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + 1 ∧
      (v + UInt32.ofNat (8 * k) + 2).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + 2 ∧
      (v + UInt32.ofNat (8 * k) + 3).toNat
        = (v + UInt32.ofNat (8 * k)).toNat + 3 := by
  have hbase : (v + UInt32.ofNat (8 * k)).toNat = v.toNat + 8 * k :=
    Slices.byteOffset_toNat v (8 * k) (by omega)
  have h := offset_facts64 (v + UInt32.ofNat (8 * k)) 0 0 rfl (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simpa using h.2.1
  · simpa using h.2.2.1
  · simpa using h.2.2.2.1

/-- The whole cell of entry `k` of a buffer that does not wrap. -/
private theorem cell_facts64 (v : UInt32) (k n : Nat) (hk : k < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
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

set_option maxHeartbeats 2000000 in
/-- `i32.load` of the key of entry `k`. -/
private theorem twp_key_read [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i32 (entryAt ps k).1 :: values⟩, code, arity, remainder,
            controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 addr :: values⟩,
          .load32 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k < ps.length := by omega
  have hfacts := cell_facts32 v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_key 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load32_addr (entryAt ps k).1
    hfacts.1 hfacts.2.1 hfacts.2.2 with Hcell
  ihave Hbuf := Hclose $$ %(entryAt ps k).1 Hcell
  isimp only [getElem_entryAt ps hkl, set_pair_self ps hkl] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i64.load` of the whole entry `k`. -/
private theorem twp_entry_read [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i64 (Table.pairWord (entryAt ps k)) :: values⟩, code,
            arity, remainder, controls, calls⟩ : Expr Universal.State) @
          s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues, .i32 addr :: values⟩,
          .load64 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k < ps.length := by omega
  have hfacts := cell_facts64 v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := v + UInt32.ofNat (8 * k)) (offset := 0)
    (Table.pairWord (entryAt ps k)) hfacts.1 hfacts.2.1 hfacts.2.2.1
    hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _) $$ Hcell
  ihave Hbuf := Hclose $$ %(entryAt ps k) Hcell
  isimp only [set_entryAt ps hkl] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i64.store` of a whole entry into slot `k`. -/
private theorem twp_entry_write [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v addr : UInt32} {ps : List (UInt32 × UInt32)}
    {q : UInt32 × UInt32} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (haddr : addr = v + UInt32.ofNat (8 * k)) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v (ps.set k q) -∗
        WP (.running ⟨⟨params, localValues, values⟩, code, arity,
            remainder, controls, calls⟩ : Expr Universal.State) @ s; E
          [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i64 (Table.pairWord q) :: .i32 addr :: values⟩,
          .store64 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  subst haddr
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k < ps.length := by omega
  have hfacts := cell_facts64 v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_focus 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store64
    (address := v + UInt32.ofNat (8 * k)) (offset := 0)
    (Table.pairWord (entryAt ps k)) hfacts.1 hfacts.2.1 hfacts.2.2.1
    hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hcell
  ihave Hcell := wordMove64 (UInt32.add_zero _) $$ Hcell
  ihave Hbuf := Hclose $$ %q Hcell
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

/-! ## The complement of WAT 6176

The tail update of the loop writes `len + (split ^^^ -1)`, which is
`len - split - 1`.  The two lemmas are copies of `Func11Proof`. -/

/-- The complement of a number that fits in `w` bits. -/
private theorem nat_xor_allOnes (w j : Nat) (h : j < 2 ^ w) :
    j ^^^ (2 ^ w - 1) = 2 ^ w - 1 - j := by
  have h1 : (BitVec.ofNat w j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  have h2 : (BitVec.allOnes w).toNat = 2 ^ w - 1 := BitVec.toNat_allOnes
  have h3 := congrArg BitVec.toNat
    (BitVec.xor_allOnes (x := BitVec.ofNat w j))
  rw [BitVec.toNat_xor, BitVec.toNat_not, h1, h2] at h3
  exact h3

/-- The compiled complement. -/
private theorem xor_ones_toNat (x : UInt32) :
    (x ^^^ 4294967295).toNat = 4294967295 - x.toNat := by
  have hx : x.toNat < 2 ^ 32 := UInt32.toNat_lt x
  rw [UInt32.toNat_xor,
    show ((4294967295 : UInt32)).toNat = 2 ^ 32 - 1 from rfl,
    nat_xor_allOnes 32 x.toNat hx]
  norm_num

/-- The new length of WAT 6174 to 6178. -/
private theorem len_after (len split : UInt32)
    (h : split.toNat + 1 ≤ len.toNat) :
    (split ^^^ 4294967295) + len
      = UInt32.ofNat (len.toNat - split.toNat - 1) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hlen := UInt32.toNat_lt len
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, xor_ones_toNat, ofNat_toNat (by omega)]
  omega

/-! ## The ancestor pivot

`ancAt` names the ancestor that a turn of the loop hands to its child.
The address is the address of the pivot that the turn put in place.  A
null address carries no cell, because `AncestorCell none` is `emp` and
`ancestorArg none` is the null address that the guard at WAT 5760
tests. -/

/-- The ancestor of a child, from the address of the pivot and its
key. -/
private def ancAt (a k : UInt32) : Option (UInt32 × UInt32) :=
  if a = 0 then none else some (a, k)

private theorem ancestorArg_ancAt (a k : UInt32) :
    ancestorArg (ancAt a k) = a := by
  unfold ancAt
  by_cases h : a = 0
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h]
    rfl

private theorem ancAt_ne_zero (a k : UInt32) :
    ∀ p q, ancAt a k = some (p, q) → p ≠ 0 := by
  intro p q hsome
  unfold ancAt at hsome
  by_cases h : a = 0
  · rw [if_pos h] at hsome
    exact absurd hsome (by simp)
  · rw [if_neg h] at hsome
    have hp : p = a := by
      have := Option.some.inj hsome
      exact (congrArg Prod.fst this).symm
    rw [hp]
    exact h

private theorem ancestorBelow_ancAt (a k : UInt32)
    (l : List (UInt32 × UInt32)) (h : ∀ x ∈ l, k < x.1) :
    AncestorBelow (ancAt a k) l := by
  intro p q hsome x hx
  unfold ancAt at hsome
  by_cases hz : a = 0
  · rw [if_pos hz] at hsome
    exact absurd hsome (by simp)
  · rw [if_neg hz] at hsome
    have hq : q = k := by
      have := Option.some.inj hsome
      exact (congrArg Prod.snd this).symm
    rw [hq]
    exact h x hx

private theorem ancestorBelow_sub {anc : Option (UInt32 × UInt32)}
    {l m : List (UInt32 × UInt32)} (h : AncestorBelow anc l)
    (hsub : ∀ x ∈ m, x ∈ l) : AncestorBelow anc m := by
  intro p q hsome x hx
  exact h p q hsome x (hsub x hx)

/-! ## The ancestor cell and the address space

The guard at WAT 5763 and 5764 reads the key of the ancestor cell.  A
load of four bytes traps when the address is in the last three bytes of
the address space, which `Wasm.SmallStep.Step.load32Trap` states, and
the rule `Wasm.SmallStep.twp_load32_addr` therefore asks for the three
address facts.  `AncestorCell` is a bare `pointsTo_u32`, which carries
no such fact: a slice carries one, a cell does not.

`SortContracts.Func21Spec` states the missing fact as `AncestorFits`,
because the contract cannot read it out of `AncestorCell`.  Every
recursive call of WAT 6173 passes a cell of its own buffer, which fits,
so the induction carries it. -/

/-- The three address facts of one `i32` cell that does not wrap. -/
private theorem addr_facts (addr : UInt32)
    (h : addr.toNat + 4 ≤ UInt32.size) :
    (addr + 1).toNat = addr.toNat + 1 ∧
      (addr + 2).toNat = addr.toNat + 2 ∧
      (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using Slices.byteOffset_toNat addr 1 (by omega),
    by simpa using Slices.byteOffset_toNat addr 2 (by omega),
    by simpa using Slices.byteOffset_toNat addr 3 (by omega)⟩

/-- A key cell of the buffer fits, because the buffer does not wrap. -/
private theorem ancestorFits_of_slice (v : UInt32) (i n : Nat)
    (hi : i < n) (hroom : v.toNat + 8 * n < UInt32.size) (k : UInt32) :
    AncestorFits (ancAt (v + UInt32.ofNat (8 * i)) k) := by
  intro p q hsome
  have hbase : (v + UInt32.ofNat (8 * i)).toNat = v.toNat + 8 * i :=
    Slices.byteOffset_toNat v (8 * i) (by omega)
  unfold ancAt at hsome
  by_cases hz : v + UInt32.ofNat (8 * i) = 0
  · rw [if_pos hz] at hsome
    exact absurd hsome (by simp)
  · rw [if_neg hz] at hsome
    have hp : p = v + UInt32.ofNat (8 * i) := by
      have := Option.some.inj hsome
      exact (congrArg Prod.fst this).symm
    rw [hp, hbase]
    omega

/-! ## Distinct keys -/

/-- The head key of a run with distinct keys is not a later key. -/
private theorem key_ne_of_nodup {p : UInt32 × UInt32}
    {l : List (UInt32 × UInt32)} (hn : NodupKeys (p :: l))
    {y : UInt32 × UInt32} (hy : y ∈ l) : p.1 ≠ y.1 := by
  unfold NodupKeys at hn
  rw [List.map_cons, List.nodup_cons] at hn
  intro heq
  exact hn.1 (heq ▸ List.mem_map_of_mem hy)

/-! ## The swap of WAT 6153 to 6172

The region exchanges slot 0, which holds the pivot, with slot `numLt`.
The model of the buffer is the pivot and then the two parts, so the
exchange moves the last entry of the first part to the front and puts
the pivot between the parts. -/

/-- The entry of a tail slot, through the head and the second run. -/
private theorem entryAt_cons_append (p : UInt32 × UInt32)
    (l ge : List (UInt32 × UInt32)) (i : Nat) (hi : i < l.length) :
    entryAt (p :: (l ++ ge)) (i + 1) = entryAt l i := by
  unfold entryAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_cons_succ, List.getElem?_append_left hi]

private theorem swap_pivot (p : UInt32 × UInt32)
    (lt ge : List (UInt32 × UInt32)) :
    ∃ lt' : List (UInt32 × UInt32), lt'.Perm lt ∧
      ((p :: (lt ++ ge)).set 0
            (entryAt (p :: (lt ++ ge)) lt.length)).set lt.length
          (entryAt (p :: (lt ++ ge)) 0)
        = lt' ++ p :: ge := by
  match lt with
  | [] =>
      refine ⟨[], List.Perm.refl _, ?_⟩
      simp [entryAt]
  | a :: t =>
      set l := a :: t with hl
      have hne : l ≠ [] := by simp [hl]
      have hlen : l.length = t.length + 1 := by simp [hl]
      have hlast : entryAt (p :: (l ++ ge)) l.length
          = entryAt l t.length := by
        rw [hlen]
        exact entryAt_cons_append p l ge t.length (by omega)
      have hget : entryAt l t.length = l.getLast hne := by
        rw [entryAt_eq_getElem l (by omega), List.getLast_eq_getElem hne]
        simp only [hlen, Nat.add_sub_cancel]
      have hhead : entryAt (p :: (l ++ ge)) 0 = p := rfl
      have hset : l.set t.length p = l.dropLast ++ [p] := by
        rw [List.set_eq_take_append_cons_drop, if_pos (by omega),
          List.dropLast_eq_take, hlen]
        simp [hlen]
      refine ⟨l.getLast hne :: l.dropLast, ?_, ?_⟩
      · have hsplit : l.dropLast ++ [l.getLast hne] = l :=
          List.dropLast_append_getLast hne
        have h1 : List.Perm (l.dropLast ++ [l.getLast hne])
            (l.getLast hne :: l.dropLast) := List.perm_append_comm
        rw [hsplit] at h1
        exact h1.symm
      · rw [hlast, hget, hhead, List.set_cons_zero, hlen,
          List.set_cons_succ, List.set_append_left t.length p (by omega),
          hset]
        simp


/-! ## The ancestor cell and the run that is already in place

`doneOwn` is the one resource that the loop keeps for the two runs that
it does not hold as a plain buffer: the ancestor cell of the caller and
the entries that are already in key order.  The cell that the turn reads
is `cur`.  Giving it back returns the cell of the caller and a way to
put the rest of the buffer back on the front run. -/

private def doneOwn [WasmHeapGS Universal.State] (v0 : UInt32)
    (anc cur : Option (UInt32 × UInt32))
    (done : List (UInt32 × UInt32)) : HeapIProp :=
  iprop(AncestorCell cur ∗
    (AncestorCell cur -∗ AncestorCell anc ∗
      (∀ tail : List (UInt32 × UInt32),
        Table.PairSlice 0 (v0 + UInt32.ofNat (8 * done.length)) tail -∗
          Table.PairSlice 0 v0 (done ++ tail))))

/-- At the head of the first turn nothing is in place yet. -/
private theorem doneOwn_start [WasmHeapGS Universal.State] (v0 : UInt32)
    (anc : Option (UInt32 × UInt32)) :
    AncestorCell anc ⊢ doneOwn v0 anc anc [] := by
  iintro Hanc
  unfold doneOwn
  isplitl_exact Hanc
  · iintro Hcur
    isplitl_exact Hcur
    · iintro %tail Htail
      isimp only [List.length_nil, Nat.mul_zero,
        show UInt32.ofNat 0 = (0 : UInt32) from rfl,
        UInt32.add_zero] at Htail
      rw [show ([] : List (UInt32 × UInt32)) ++ tail = tail from rfl]
      iexact Htail

/-- The end of the loop takes the two runs back. -/
private theorem doneOwn_close [WasmHeapGS Universal.State] (v0 : UInt32)
    (anc cur : Option (UInt32 × UInt32))
    (done tail : List (UInt32 × UInt32)) :
    iprop(doneOwn v0 anc cur done ∗
        Table.PairSlice 0 (v0 + UInt32.ofNat (8 * done.length)) tail) ⊢
      iprop(AncestorCell anc ∗ Table.PairSlice 0 v0 (done ++ tail)) := by
  iintro ⟨Hown, Htail⟩
  isimp only [doneOwn] at Hown
  icases Hown with ⟨Hcur, Hback⟩
  ihave ⟨Hanc, Hjoin⟩ := Hback $$ Hcur
  isplitl_exact Hanc
  · iapply Hjoin $$ %tail Htail

/-! ## The stack epilogue, WAT 8659 to 8662 -/

/-- The region below the frame, named through the stack pointer of the
caller. -/
private theorem below_rebase [WasmHeapGS Universal.State] (sp : UInt32)
    (limit : UInt32) (rem : List UInt8) :
    StackBelow (sp - 256) (256 * limit.toNat) rem ⊢
      StackBelow (sp - UInt32.ofNat 256)
        (quicksortDepth limit.toNat - 256) rem := by
  rw [depth_cut]
  iintro H
  iexact H

set_option maxHeartbeats 2000000 in
/-- The stack epilogue and the return.  The body raises the stack
pointer by 256 and gives the frame, the buffer and the borrowed
resource back to the caller. -/
private theorem twp_qs_epilogue [WasmSmallStepGS hlc Universal.State]
    {sp v b l a li e : UInt32} {ls : List Value}
    {x6 x7 x8 x9 x10 : Value}
    {limit : UInt32} {out pairs : List (UInt32 × UInt32)}
    {rem frame : List UInt8} {kept : HeapIProp}
    {callerLocals : Locals} {stack : List Value} {code : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hperm : out.Perm pairs) (hsorted : Table.SortedByKey out)
    (hframe : frame.length = 256) :
    iprop(
      RuntimeContext ∗
      StackPointer (sp - 256) ∗
      StackBelow (sp - 256) (256 * limit.toNat) rem ∗
      Slices.ByteSlice 0 (sp - 256) frame ∗
      Table.PairSlice 0 v out ∗ kept ∗
      SortPost v pairs sp (quicksortDepth limit.toNat) kept callerLocals
        stack code arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨{ params := [.i32 b, .i32 l, .i32 a, .i32 li, .i32 e],
             locals := .i32 (sp - 256) :: x6 :: x7 :: x8 :: x9 ::
               x10 :: ls,
             values := [] },
            qsEpilogue, 0, [], [],
            { locals := { callerLocals with values := stack },
              continuation := code, resultArity := arity,
              callerRemainder := remainder, control := controls,
              returningInstance := ⟨0⟩ } :: calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hrem, Hframe, Hbuf, Hkept, Hcont⟩
  ihave ⟨Hrem, %hremLength⟩ :=
    StackBelow_length (sp - 256) (256 * limit.toNat) rem $$ Hrem
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  isimp only [StackPointer] at Hsp
  simp only [qsEpilogue_shape]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (256 : UInt32) + (sp - 256) = sp from by
    rw [UInt32.add_comm, UInt32.sub_add_cancel]]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
    with Hmodule
  simp only [List.take_zero, List.nil_append]
  ihave Hsp : StackPointer sp $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  ihave Hframe256 :=
    StackBelow_intro sp (sp - 256) 256 frame hframe rfl $$ Hframe
  ihave Hrem := below_rebase sp limit rem $$ Hrem
  ihave Hbelow :=
    frame_join sp (quicksortDepth limit.toNat) 256 rem frame
      (by rw [depth_cut]; exact hremLength) (by rw [depth_eq]; omega)
      $$ [Hrem Hframe256]
  · isplitl_exact Hrem
    · iexact Hframe256
  iclose_map_runtime Hruntime with Hmodule Henv
  isimp only [SortPost] at Hcont
  ihave Hgo := Hcont $$ %out %(rem ++ frame) Hruntime Hsp Hbelow Hbuf
    Hkept %⟨hperm, hsorted⟩
  isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
  iexact Hgo

/-! ## Joining the two runs -/

private theorem sorted_join {done out : List (UInt32 × UInt32)}
    (hdone : Table.SortedByKey done) (hout : Table.SortedByKey out)
    (hcross : ∀ x ∈ done, ∀ y ∈ out, x.1 ≤ y.1) :
    Table.SortedByKey (done ++ out) :=
  (Table.sortedByKey_append done out).mpr ⟨hdone, hout, hcross⟩

private theorem nodupKeys_right {a b : List (UInt32 × UInt32)}
    (h : NodupKeys (a ++ b)) : NodupKeys b := by
  unfold NodupKeys at h ⊢
  rw [List.map_append] at h
  exact h.of_append_right

private theorem nodupKeys_left {a b : List (UInt32 × UInt32)}
    (h : NodupKeys (a ++ b)) : NodupKeys a := by
  unfold NodupKeys at h ⊢
  rw [List.map_append] at h
  exact h.of_append_left

/-! ## The small sort and the return, WAT 6193 to 8662 -/

set_option maxHeartbeats 2000000 in
/-- The end of the body.  The buffer holds `rest`, the run that is not
sorted yet, and `done` holds the entries that are already in place.  The
small sort puts `rest` in key order and the epilogue returns. -/
private theorem twp_qs_finish [WasmSmallStepGS hlc Universal.State]
    {sp v0 v len limit : UInt32} {nt : NetScratch}
    {r6 r7 r8 r9 r10 r11 r13 r15 r16 r17 r18 : UInt32} {r12 : UInt64}
    {anc cur : Option (UInt32 × UInt32)}
    {done rest pairs : List (UInt32 × UInt32)}
    {rem frame : List UInt8}
    {callerLocals : Locals} {stack : List Value} {code : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hv : v = v0 + UInt32.ofNat (8 * done.length))
    (hrest : rest.length = len.toNat) (hsmall : len.toNat ≤ 32)
    (hperm : (done ++ rest).Perm pairs)
    (hdone : Table.SortedByKey done)
    (hcross : ∀ x ∈ done, ∀ y ∈ rest, x.1 < y.1)
    (hnodup : NodupKeys pairs)
    (hroom : v.toNat + 8 * len.toNat < UInt32.size)
    (hfp : (sp - 256).toNat + 256 < UInt32.size)
    (hframe : frame.length = 256) :
    iprop(
      RuntimeContext ∗
      StackPointer (sp - 256) ∗
      StackBelow (sp - 256) (256 * limit.toNat) rem ∗
      Slices.ByteSlice 0 (sp - 256) frame ∗
      Table.PairSlice 0 v rest ∗
      doneOwn v0 anc cur done ∗
      SortPost v0 pairs sp (quicksortDepth limit.toNat)
        (AncestorCell anc) callerLocals stack code arity remainder
        controls calls s E Φ) ⊢
      WP (.running ⟨rLoc v len (sp - 256) nt r6 r7 r8 r9 r10 r11 r12 r13
            r15 r16 r17 r18 [], qsAfter4, 0, [],
          regBlocks qsEpilogue [],
          { locals := { callerLocals with values := stack },
            continuation := code, resultArity := arity,
            callerRemainder := remainder, control := controls,
            returningInstance := ⟨0⟩ } :: calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  have hnodupAll : NodupKeys (done ++ rest) :=
    Table.nodupKeys_of_perm hperm hnodup
  have hnodupRest : NodupKeys rest := nodupKeys_right hnodupAll
  iintro ⟨Hruntime, Hsp, Hrem, Hframe, Hbuf, Hown, Hcont⟩
  iapply (Func21Merge.twp_small_sort
    (Rest := iprop(RuntimeContext ∗ StackPointer (sp - 256) ∗
      StackBelow (sp - 256) (256 * limit.toNat) rem ∗
      doneOwn v0 anc cur done ∗
      SortPost v0 pairs sp (quicksortDepth limit.toNat)
        (AncestorCell anc) callerLocals stack code arity remainder
        controls calls s E Φ))
    hrest hsmall hnodupRest hroom hfp hframe ?_)
  · intro out frame' nt' y6 y7 y8 y9 y10 y11 y12 y13 y15 y16 y17 y18
      hout hsorted hframe'
    iintro ⟨Hout, Hf, Hruntime, Hsp, Hrem, Hown, Hcont⟩
    ihave ⟨Hanc, Hwhole⟩ :=
      doneOwn_close v0 anc cur done out $$ [Hown Hout]
    · isplitl_exact Hown
      · irw_exact [hv] with Hout
    iapply (twp_qs_epilogue (pairs := pairs) (kept := AncestorCell anc)
      ((hout.append_left done).trans hperm)
      (sorted_join hdone hsorted (by
        intro x hx y hy
        exact UInt32.le_of_lt (hcross x hx y (hout.subset hy))))
      hframe')
    isplitl_exact Hruntime
    · isplitl_exact Hsp
      · isplitl_exact Hrem
        · isplitl_exact Hf
          · isplitl_exact Hwhole
            · isplitl_exact Hanc
              · iexact Hcont
  · isplitl_exact Hbuf
    · isplitl_exact Hframe
      · isplitl_exact Hruntime
        · isplitl_exact Hsp
          · isplitl_exact Hrem
            · isplitl_exact Hown
              · iexact Hcont

/-! ## Two fragments that `Func21Defs` does not write out

A proof that steps through a straight-line run needs the instruction
list.  Both lemmas are `rfl`, so they carry no new content. -/

/-- The inline median of three, WAT 5724 to 5748. -/
private theorem qsMedianInline_shape :
    qsMedianInline =
      [.localGet 0, .localGet 7, .localGet 8, .localGet 0, .load32 0,
        .localTee 6, .localGet 8, .load32 0, .localTee 9, .ltU,
        .localTee 10, .localGet 9, .localGet 7, .load32 0, .localTee 11,
        .ltU, .xor, .select, .localGet 10, .localGet 6, .localGet 11,
        .ltU, .xor, .select, .localSet 6] := by
  rfl

/-- The recursion and the tail update, WAT 6152 to 6185. -/
private theorem qsRecurse_shape :
    qsRecurse =
      [.br_if 3, .localGet 0, .load64 0, .localSet 12, .localGet 0,
        .localGet 0, .localGet 6, .const 3, .shl, .add, .localTee 7,
        .load64 0, .store64 0, .localGet 7, .localGet 12, .store64 0,
        .localGet 0, .localGet 6, .localGet 2, .localGet 3, .localGet 4,
        .call 24, .localGet 1, .localGet 6, .const 4294967295, .xor,
        .add, .localSet 1, .localGet 7, .const 8, .add, .localSet 0,
        .localGet 7, .localSet 2] := by
  rfl

/-! ## More arithmetic bridges -/

/-- `.const 4294967295` is minus one. -/
private theorem add_neg_one (x : UInt32) :
    (4294967295 : UInt32) + x = x - 1 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967295 : UInt32).toNat = 4294967295 from rfl,
    show (1 : UInt32).toNat = 1 from rfl] at *

/-- The offset of an address above a base. -/
private theorem add_sub_self (v a : UInt32) : v + a - v = a := by
  apply UInt32.toNat_inj.mp
  have hv := UInt32.toNat_lt v
  have ha := UInt32.toNat_lt a
  simp only [UInt32.toNat_add, UInt32.toNat_sub] at *
  omega

/-- `i32.add` of a base and an offset, with the offset on top. -/
private theorem addr_base (v : UInt32) (m : Nat) :
    UInt32.ofNat (8 * m) + v = v + UInt32.ofNat (8 * m) :=
  UInt32.add_comm _ _

/-- The word of the recursion limit that is one below. -/
private theorem limit_dec (x : UInt32) (h : x ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have hx := UInt32.toNat_lt x
  have hne : x.toNat ≠ 0 := by
    intro h0
    exact h (UInt32.toNat_inj.mp (by rw [h0]; rfl))
  simp only [UInt32.toNat_sub, show (1 : UInt32).toNat = 1 from rfl]
  omega

/-! ## The two register maps of the body

`Func21Region.rLoc` names the locals of the small sort and
`Func21Partition.qsRegs` names the locals of the strict partition.  They
are the same 39 locals, so one `rfl` carries a proof from one map to the
other. -/

/-- The registers that the strict partition does not touch, read off the
register map of the small sort. -/
private def partRegs (buf len fp : UInt32) (nt : NetScratch)
    (r16 r17 r18 : UInt32) : Regs :=
  { buf := buf, len := len, anc := nt.r2, limit := nt.r3, env := nt.r4,
    fp := fp, pad16 := .i32 r16, pad17 := .i32 r17, pad18 := .i32 r18,
    pad19 := .i64 nt.r19, pad20 := .i64 nt.r20,
    tail := [.i32 nt.r21, .i32 nt.r22, .i32 nt.r23, .i32 nt.r24,
      .i64 nt.r25, .i32 nt.r26, .i64 nt.r27, .i32 nt.r28, .i32 nt.r29,
      nt.p30, nt.p31, nt.p32, nt.p33, nt.p34, nt.p35, nt.p36, nt.p37,
      nt.p38] }

private theorem rLoc_qsRegs (buf len fp : UInt32) (nt : NetScratch)
    (r6 r7 r8 r9 r10 r11 : UInt32) (r12 : UInt64)
    (r13 r14 r15 r16 r17 r18 : UInt32) (values : List Value) :
    rLoc buf len fp { nt with r14 := r14 } r6 r7 r8 r9 r10 r11 r12 r13
        r15 r16 r17 r18 values =
      qsRegs (partRegs buf len fp nt r16 r17 r18) r6 r7 r8 r9 r10 r11
        r12 r13 r14 r15 values :=
  rfl

/-- The 34 declared locals at the head of the body, as a register
record of the small sort. -/
@[reducible] private def zeroNet (a li e : UInt32) : NetScratch :=
  { r2 := a, r3 := li, r4 := e, r14 := 0, r19 := 0, r20 := 0, r21 := 0,
    r22 := 0, r23 := 0, r24 := 0, r25 := 0, r26 := 0, r27 := 0,
    r28 := 0, r29 := 0, p30 := .i32 0, p31 := .i32 0, p32 := .i32 0,
    p33 := .i32 0, p34 := .i32 0, p35 := .i32 0, p36 := .i32 0,
    p37 := .i64 0, p38 := .i64 0 }

private theorem initialLocals_rLoc (buf len a li e fp : UInt32) :
    func21_initialLocals buf len a li e fp =
      rLoc buf len fp (zeroNet a li e) 0 0 0 0 0 0 0 0 0 0 0 0 [] :=
  rfl

/-! ## The contract for a bounded input

`Func21Upto N` is `Func21Spec` for an input below `N` entries.  The
recursion of WAT 6173 runs on a part that is strictly shorter than the
input, so a strong induction on `N` closes the body. -/

private def Func21Upto [WasmSmallStepGS hlc Universal.State]
    (N : Nat) : Prop :=
  ∀ (sp v len limit env : UInt32) (anc : Option (UInt32 × UInt32))
    (pairs : List (UInt32 × UInt32)) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    pairs.length < N → AncestorFits anc →
    CallContract 24
      [.i32 env, .i32 limit, .i32 (ancestorArg anc), .i32 len, .i32 v]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp (quicksortDepth limit.toNat) below ∗
        Table.PairSlice 0 v pairs ∗
        AncestorCell anc ∗
        ⌜pairs.length = len.toNat ∧ len.toNat ≤ 2 ^ 27 ∧
          NodupKeys pairs ∧ AncestorBelow anc pairs ∧
          v.toNat + 8 * len.toNat < UInt32.size ∧
          quicksortDepth limit.toNat ≤ sp.toNat ∧
          (∀ p k, anc = some (p, k) → p ≠ 0)⌝ ∗
        SortPost v pairs sp (quicksortDepth limit.toNat)
          (AncestorCell anc) callerLocals stack code arity remainder
          controls calls s E Φ)

/-! ## The index of the quicksort loop

The loop keeps two runs and ten scratch registers.  `done` is the run
that is already in key order and in place, and `rest` is the run that
the buffer still has to sort. -/

private structure LoopIdx where
  done : List (UInt32 × UInt32)
  rest : List (UInt32 × UInt32)
  cur : Option (UInt32 × UInt32)
  lim : UInt32
  r6 : UInt32
  r7 : UInt32
  r8 : UInt32
  r9 : UInt32
  r10 : UInt32
  r11 : UInt32
  r12 : UInt64
  r13 : UInt32
  r14 : UInt32
  r15 : UInt32

/-- The registers that one turn of the loop does not touch. -/
@[reducible] private def loopRegs (v0 fp : UInt32) (nt : NetScratch)
    (r16 r17 r18 : UInt32) (i : LoopIdx) : Regs :=
  { buf := v0 + UInt32.ofNat (8 * i.done.length),
    len := UInt32.ofNat i.rest.length,
    anc := ancestorArg i.cur, limit := i.lim, env := nt.r4, fp := fp,
    pad16 := .i32 r16, pad17 := .i32 r17, pad18 := .i32 r18,
    pad19 := .i64 nt.r19, pad20 := .i64 nt.r20,
    tail := [.i32 nt.r21, .i32 nt.r22, .i32 nt.r23, .i32 nt.r24,
      .i64 nt.r25, .i32 nt.r26, .i64 nt.r27, .i32 nt.r28, .i32 nt.r29,
      nt.p30, nt.p31, nt.p32, nt.p33, nt.p34, nt.p35, nt.p36, nt.p37,
      nt.p38] }

/-- The locals at the head of one turn. -/
@[reducible] private def loopLocals (v0 fp : UInt32) (nt : NetScratch)
    (r16 r17 r18 : UInt32) (i : LoopIdx) : Locals :=
  qsRegs (loopRegs v0 fp nt r16 r17 r18 i) i.r6 i.r7 i.r8 i.r9 i.r10
    i.r11 i.r12 i.r13 i.r14 i.r15 []

/-- The locals of one turn in the vocabulary of the partition. -/
private theorem loopLocals_shape (v0 fp : UInt32) (nt : NetScratch)
    (r16 r17 r18 : UInt32) (i : LoopIdx) :
    loopLocals v0 fp nt r16 r17 r18 i =
      qsRegs (loopRegs v0 fp nt r16 r17 r18 i) i.r6 i.r7 i.r8 i.r9
        i.r10 i.r11 i.r12 i.r13 i.r14 i.r15 [] :=
  rfl

private theorem loopLocals_rLoc (v0 fp : UInt32) (nt : NetScratch)
    (r16 r17 r18 : UInt32) (i : LoopIdx) :
    loopLocals v0 fp nt r16 r17 r18 i =
      rLoc (v0 + UInt32.ofNat (8 * i.done.length))
        (UInt32.ofNat i.rest.length) fp
        { nt with r2 := ancestorArg i.cur, r3 := i.lim, r14 := i.r14 }
        i.r6 i.r7 i.r8 i.r9 i.r10 i.r11 i.r12 i.r13 i.r15 r16 r17 r18
        [] :=
  rfl

/-- The control frames of the body below the loop. -/
private def qsBlocks : List ControlFrame :=
  [qsFrame qsBlock4Body qsAfter4, qsFrame qsBlock3Body qsAfter3,
    qsFrame qsBlock2Body qsAfter2, qsFrame qsBlock1Body qsEpilogue]

/-- A block frame of the body, folded from the record that `twp_block`
leaves. -/
private theorem qsFrame_fold (body cont : Program) :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := body, continuation := cont,
       belowStack := ([] : List Value) } : ControlFrame)
      = qsFrame body cont :=
  rfl

/-- The four frames of the body, folded. -/
private theorem qsBlocks_fold :
    [qsFrame qsBlock4Body qsAfter4, qsFrame qsBlock3Body qsAfter3,
      qsFrame qsBlock2Body qsAfter2, qsFrame qsBlock1Body qsAfter1]
      = qsBlocks :=
  rfl

/-- The three frames that the small sort keeps, folded. -/
private theorem regBlocks_fold :
    [qsFrame qsBlock3Body qsAfter3, qsFrame qsBlock2Body qsAfter2,
      qsFrame qsBlock1Body qsEpilogue]
      = regBlocks qsEpilogue [] :=
  rfl

/-- The locals at the head of the body, folded. -/
private theorem initialLocals_fold (b l a li e fp : UInt32) :
    ({ params := [.i32 b, .i32 l, .i32 a, .i32 li, .i32 e],
       locals := [.i32 fp, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
         .i32 0, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
         .i32 0, .i64 0, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0,
         .i64 0, .i32 0, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0,
         .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i64 0],
       values := ([] : List Value) } : Locals)
      = rLoc b l fp (zeroNet a li e) 0 0 0 0 0 0 0 0 0 0 0 0 [] :=
  rfl

/-- The four frames, with the three that the small sort keeps named as
the small sort names them. -/
private theorem qsBlocks_split :
    qsBlocks
      = qsFrame qsBlock4Body qsAfter4 :: regBlocks qsEpilogue [] :=
  rfl

/-- The invariant of the quicksort loop. -/
private def loopInv [WasmSmallStepGS hlc Universal.State]
    (sp v0 limit : UInt32) (anc : Option (UInt32 × UInt32))
    (pairs : List (UInt32 × UInt32))
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) (i : LoopIdx) : HeapIProp :=
  iprop(
    ⌜(i.done ++ i.rest).Perm pairs ∧ Table.SortedByKey i.done ∧
      (∀ x ∈ i.done, ∀ y ∈ i.rest, x.1 < y.1) ∧
      AncestorBelow i.cur i.rest ∧
      (∀ p k, i.cur = some (p, k) → p ≠ 0) ∧ AncestorFits i.cur ∧
      33 ≤ i.rest.length ∧ i.lim.toNat ≤ limit.toNat⌝ ∗
    RuntimeContext ∗
    StackPointer (sp - 256) ∗
    (∃ rem : List UInt8,
      StackBelow (sp - 256) (256 * limit.toNat) rem) ∗
    (∃ frame : List UInt8, ⌜frame.length = 256⌝ ∗
      Slices.ByteSlice 0 (sp - 256) frame) ∗
    Table.PairSlice 0 (v0 + UInt32.ofNat (8 * i.done.length)) i.rest ∗
    doneOwn v0 anc i.cur i.done ∗
    SortPost v0 pairs sp (quicksortDepth limit.toNat) (AncestorCell anc)
      callerLocals stack code arity remainder controls calls s E Φ)

/-! ## The pivot, WAT 5695 to 5757

The three candidates are the entries 0, `4 * k` and `7 * k`, where `k`
is the length divided by eight.  A length of 64 or more calls `func 23`
and a shorter one runs an inline median of three.  Both answers are an
entry address of the buffer, which is all that the partition needs. -/

set_option maxHeartbeats 4000000 in
private theorem twp_pivot [WasmSmallStepGS hlc Universal.State]
    {f : Regs} {r6 r7 r8 r9 r10 r11 r13 r14 r15 : UInt32}
    {r12 : UInt64} {rest : List (UInt32 × UInt32)} {Rest : HeapIProp}
    {arity : Nat} {remainder : List Value}
    {cs : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : rest.length = f.len.toNat) (hbig : 33 ≤ f.len.toNat)
    (hroom : f.buf.toNat + 8 * f.len.toNat < UInt32.size)
    (hcont : ∀ (ip : Nat) (k6 k7 k8 k9 k10 k11 : UInt32),
      ip < f.len.toNat → k6 = f.buf + UInt32.ofNat (8 * ip) →
      iprop(Table.PairSlice 0 f.buf rest ∗ RuntimeContext ∗ Rest) ⊢
        WP (.running ⟨qsRegs f k6 k7 k8 k9 k10 k11 r12 r13 r14 r15 [],
            qsAfterMedian, arity, remainder, cs, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 f.buf rest ∗ RuntimeContext ∗ Rest) ⊢
      WP (.running ⟨qsRegs f r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 [],
          qsAfterHeap, arity, remainder, cs, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  set k : Nat := f.len.toNat / 8 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hk8 : 8 * k ≤ f.len.toNat := by omega
  have hkfit : k < UInt32.size := by omega
  have hkto : (UInt32.ofNat k).toNat = k := ofNat_toNat hkfit
  have h7k : 7 * k < f.len.toNat := by omega
  have h4k : 4 * k < f.len.toNat := by omega
  have hshr : f.len >>> ((3 : UInt32) % 32) = UInt32.ofNat k := by
    rw [shr_three]
  have hs7 : (56 : UInt32) * UInt32.ofNat k
      = UInt32.ofNat (8 * (7 * k)) := by
    rw [mul_fifty_six _ (by rw [hkto]; omega), hkto]
  have hs4 : (UInt32.ofNat k) <<< ((5 : UInt32) % 32)
      = UInt32.ofNat (8 * (4 * k)) := by
    rw [shl_five _ (by rw [hkto]; omega), hkto]
  iintro ⟨Hbuf, Hruntime, HRest⟩
  simp only [qsAfterHeap_split, qsPivotSetup_shape, List.cons_append,
    List.nil_append, qsRegs, qsLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shrU]
  simp only [hshr]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const twp_mul]
  simp only [hs7]
  wasm_twp_pures [twp_add]
  simp only [addr_base]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
  simp only [hs4]
  wasm_twp_pures [twp_add]
  simp only [addr_base]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_block]
  simp only [qsMedianBlock_shape]
  wasm_twp_pures [twp_block]
  simp only [qsMedianCall_shape]
  wasm_twp_pures [twp_localGet twp_const]
  by_cases hshort : f.len.toNat < 64
  · -- WAT 5724 to 5748: the inline median of three
    have hlt : f.len < (64 : UInt32) := by
      rw [UInt32.lt_iff_toNat_lt, show (64 : UInt32).toNat = 64 from rfl]
      exact hshort
    iapply Wasm.SmallStep.twp_ltU (result := 1) (by rw [if_pos hlt])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero,
      qsMedianInline_shape]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
    iapply twp_key_read (k := 0) (n := f.len.toNat) (by omega)
      hlen (by omega) (addr_zero f.buf)
    isplitl_exact Hbuf
    iintro Hbuf
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet]
    iapply twp_key_read (k := 4 * k) (n := f.len.toNat) h4k hlen
      (by omega) rfl
    isplitl_exact Hbuf
    iintro Hbuf
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_ltU]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply twp_key_read (k := 7 * k) (n := f.len.toNat) h7k hlen
      (by omega) rfl
    isplitl_exact Hbuf
    iintro Hbuf
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_ltU]
    iapply Wasm.SmallStep.twp_xor
    iapply Wasm.SmallStep.twp_select rfl
    simp only [ite_i32]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_ltU]
    iapply Wasm.SmallStep.twp_xor
    iapply Wasm.SmallStep.twp_select rfl
    simp only [ite_i32]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_exitControl rfl
    simp only [List.take_zero, List.nil_append]
    obtain ⟨ip, hip, hpivot⟩ :=
      select_addr3 f.buf f.buf (f.buf + UInt32.ofNat (8 * (7 * k)))
        (f.buf + UInt32.ofNat (8 * (4 * k))) 0 (7 * k) (4 * k)
        (fun i => i < f.len.toNat) (addr_zero f.buf) rfl rfl
        (by omega) h7k h4k _ _
    iapply (hcont ip _ _ _ _ _ _ hip hpivot)
    isplitl_exact Hbuf
    · isplitl_exact Hruntime
      · iexact HRest
  · -- WAT 5712 to 5722: the median of medians
    have hnlt : ¬ f.len < (64 : UInt32) := by
      rw [UInt32.lt_iff_toNat_lt, show (64 : UInt32).toNat = 64 from rfl]
      omega
    iapply Wasm.SmallStep.twp_ltU (result := 0) (by rw [if_neg hnlt])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
    have H23 := Func20Proof.func20_correct (hlc := hlc)
    unfold Func20Spec CallContract callExpr at H23
    simp only [List.cons_append, List.nil_append] at H23
    iapply H23 f.buf f.buf (f.buf + UInt32.ofNat (8 * (4 * k)))
      (f.buf + UInt32.ofNat (8 * (7 * k))) (UInt32.ofNat k)
      0 (4 * k) (7 * k) rest
      (callerLocals := qsRegs f (UInt32.ofNat k)
        (f.buf + UInt32.ofNat (8 * (7 * k)))
        (f.buf + UInt32.ofNat (8 * (4 * k))) r9 r10 r11 r12 r13 r14 r15
        [])
      (stack := [])
    isplitl_exact Hruntime
    · isplitl_exact Hbuf
      · isplitl_pureexact ⟨addr_zero f.buf, rfl, rfl,
          by rw [hkto]; omega, by rw [hkto]; omega,
          by rw [hkto]; omega, by rw [hkto]; omega, by omega⟩
        · iintro %r Hruntime Hbuf %hr
          obtain ⟨ip, hip, hpivot⟩ := hr
          isimp only [ResumeWP, resumeExpr, List.nil_append,
            List.append_nil]
          wasm_twp_localSet [List.set, List.length_cons,
            List.length_nil, Nat.reduceAdd, Nat.reduceSub]
          iapply Wasm.SmallStep.twp_br rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          iapply (hcont ip _ _ _ _ _ _ (by omega) hpivot)
          isplitl_exact Hbuf
          · isplitl_exact Hruntime
            · iexact HRest

/-! ## The guards of WAT 5750 to 5771

The limit drops by one, the pivot address becomes the pivot offset, and
both guards of the equal-key partition leave the block.  A null ancestor
leaves at WAT 5762 and an ancestor key below the pivot key leaves at WAT
5771, and `AncestorBelow` gives the second one, so the equal-key
partition of WAT 5772 to 5975 never runs.  That is the dead row
X-F24-EQUAL. -/

/-- The two guards of the equal-key partition, WAT 5760 to 5771. -/
private theorem qsEqualGuard_shape :
    qsEqualGuard =
      [.localGet 2, .eqz, .br_if 0, .localGet 2, .load32 0, .localGet 0,
        .localGet 6, .add, .localTee 7, .load32 0, .ltU, .br_if 0] := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The two guards of the equal-key partition.  The block leaves on the
first guard when the ancestor is null and on the second guard
otherwise, so the code between WAT 5772 and 5975 never runs.  Local 7
is the one register that the second guard writes. -/
private theorem twp_equal_guard [WasmSmallStepGS hlc Universal.State]
    {f : Regs} {ip : Nat} {k7 k8 k9 k10 k11 k13 k14 k15 : UInt32}
    {k12 : UInt64} {cur : Option (UInt32 × UInt32)}
    {rest : List (UInt32 × UInt32)} {Rest : HeapIProp}
    {arity : Nat} {remainder : List Value}
    {cs : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : rest.length = f.len.toNat) (hip : ip < f.len.toNat)
    (hroom : f.buf.toNat + 8 * f.len.toNat < UInt32.size)
    (hanc : f.anc = ancestorArg cur) (hbelow : AncestorBelow cur rest)
    (hzero : ∀ p k, cur = some (p, k) → p ≠ 0) (hfits : AncestorFits cur)
    (hcont : ∀ j7 : UInt32,
      iprop(Table.PairSlice 0 f.buf rest ∗ AncestorCell cur ∗ Rest) ⊢
        WP (.running ⟨qsRegs f (UInt32.ofNat (8 * ip)) j7 k8 k9 k10 k11
              k12 k13 k14 k15 [], qsAfterEqual, arity, remainder, cs,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) :
    iprop(Table.PairSlice 0 f.buf rest ∗ AncestorCell cur ∗ Rest) ⊢
      WP (.running ⟨qsRegs f (UInt32.ofNat (8 * ip)) k7 k8 k9 k10 k11
            k12 k13 k14 k15 [],
          .block 0 0 qsEqualPartition :: qsAfterEqual, arity, remainder,
          cs, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hanc, HRest⟩
  wasm_twp_pures [twp_block]
  simp only [qsEqualPartition_split, qsEqualGuard_shape,
    List.cons_append, List.nil_append, qsRegs, qsLocals]
  wasm_twp_pures [twp_localGet]
  match hcur : cur with
  | none =>
      have hzero' : f.anc = 0 := by rw [hanc]; rfl
      iapply Wasm.SmallStep.twp_eqz (result := 1) (by rw [if_pos hzero'])
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      iapply (hcont k7)
      isplitl_exact Hbuf
      · isplitl_exact Hanc
        · iexact HRest
  | some pk =>
      obtain ⟨p, key⟩ := pk
      have hp : f.anc ≠ 0 := by
        rw [hanc]
        exact hzero p key rfl
      have hpfits : p.toNat + 4 ≤ UInt32.size := by
        exact hfits p key rfl
      have hkey : key < (entryAt rest ip).1 := by
        have hmem : entryAt rest ip ∈ rest := by
          rw [entryAt_eq_getElem rest (by omega)]
          exact List.getElem_mem _
        exact hbelow p key rfl _ hmem
      have hancp : f.anc = p := by rw [hanc]; rfl
      obtain ⟨h1, h2, h3⟩ :=
        addr_facts f.anc (by rw [hancp]; exact hpfits)
      isimp only [AncestorCell] at Hanc
      ihave Hanc := wordMove32 hancp.symm $$ Hanc
      iapply Wasm.SmallStep.twp_eqz (result := 0) (by rw [if_neg hp])
      iapply Wasm.SmallStep.twp_brIfZero
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind Wasm.SmallStep.twp_load32_addr key h1 h2 h3
        with Hanc
      wasm_twp_pures [twp_localGet twp_localGet twp_add]
      simp only [addr_base]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply twp_key_read (k := ip) (n := f.len.toNat) hip hlen
        (by omega) rfl
      isplitl_exact Hbuf
      iintro Hbuf
      iapply Wasm.SmallStep.twp_ltU (result := 1) (by rw [if_pos hkey])
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      iapply (hcont (f.buf + UInt32.ofNat (8 * ip)))
      isplitl_exact Hbuf
      · isplitl [Hanc]
        · isimp only [AncestorCell]
          ihave Hanc := wordMove32 hancp $$ Hanc
          iexact Hanc
        · iexact HRest


/-! ## Growing the run that is already in place -/

private theorem ancestorCell_ancAt [WasmHeapGS Universal.State]
    (a k : UInt32) (h : a ≠ 0) :
    AncestorCell (ancAt a k) = iprop(pointsTo_u32 0 a k) := by
  unfold ancAt
  rw [if_neg h]
  rfl

private theorem ancestorCell_ancAt_zero [WasmHeapGS Universal.State]
    (a k : UInt32) (h : a = 0) :
    AncestorCell (ancAt a k) = iprop(emp) := by
  unfold ancAt
  rw [if_pos h]
  rfl

/-- Writing the key that a slot already holds changes nothing. -/
private theorem set_key_self (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) :
    ps.set i ((entryAt ps i).1, ps[i].2) = ps := by
  rw [entryAt_eq_getElem ps hi]
  simp

/-- Two neighbouring buffers are one buffer. -/
private theorem pairSlice_join [WasmHeapGS Universal.State] (v : UInt32)
    (a b : List (UInt32 × UInt32)) :
    iprop(Table.PairSlice 0 v a ∗
        Table.PairSlice 0 (v + UInt32.ofNat (8 * a.length)) b) ⊢
      Table.PairSlice 0 v (a ++ b) := by
  have ht : List.take a.length (a ++ b) = a := List.take_left
  have hd : List.drop a.length (a ++ b) = b := List.drop_left
  iintro ⟨Ha, Hb⟩
  iapply (Table.PairSlice_split 0 v (a ++ b) a.length (by simp)).mpr
  isimp only [ht, hd]
  isplitl_exact Ha
  · iexact Hb

/-- One buffer is two neighbouring buffers. -/
private theorem pairSlice_cut [WasmHeapGS Universal.State] (v : UInt32)
    (a b : List (UInt32 × UInt32)) :
    Table.PairSlice 0 v (a ++ b) ⊢
      iprop(Table.PairSlice 0 v a ∗
        Table.PairSlice 0 (v + UInt32.ofNat (8 * a.length)) b) := by
  have ht : List.take a.length (a ++ b) = a := List.take_left
  have hd : List.drop a.length (a ++ b) = b := List.drop_left
  iintro H
  ihave Hsplit :=
    (Table.PairSlice_split 0 v (a ++ b) a.length (by simp)).mp $$ H
  isimp only [ht, hd] at Hsplit
  iexact Hsplit

set_option maxHeartbeats 1000000 in
/-- One turn of the loop puts `add` in place after `done`.  The new
ancestor is the key cell of the last entry of `add`, which is the pivot
that the turn moved. -/
private theorem doneOwn_grow [WasmHeapGS Universal.State]
    (v0 : UInt32) (anc cur : Option (UInt32 × UInt32))
    (done add : List (UInt32 × UInt32)) (m : Nat)
    (hm : add.length = m + 1) :
    iprop(doneOwn v0 anc cur done ∗
        Table.PairSlice 0 (v0 + UInt32.ofNat (8 * done.length)) add) ⊢
      doneOwn v0 anc
        (ancAt (v0 + UInt32.ofNat (8 * done.length)
          + UInt32.ofNat (8 * m)) (entryAt add m).1) (done ++ add) := by
  have hmlt : m < add.length := by omega
  have hlen : (done ++ add).length = done.length + add.length :=
    List.length_append
  iintro ⟨Hown, Hadd⟩
  isimp only [doneOwn] at Hown
  icases Hown with ⟨Hcur, Hback⟩
  ihave ⟨Hanc, Hjoin⟩ := Hback $$ Hcur
  unfold doneOwn
  by_cases hz : v0 + UInt32.ofNat (8 * done.length)
      + UInt32.ofNat (8 * m) = 0
  · rw [ancestorCell_ancAt_zero _ _ hz]
    iapply BI.emp_sep.mpr
    iintro Hemp
    iclear Hemp
    isplitl_exact Hanc
    · iintro %tail Htail
      isimp only [hlen, ← addr_add v0 done.length add.length] at Htail
      ihave Hwhole :=
        pairSlice_join (v0 + UInt32.ofNat (8 * done.length)) add tail $$
          [Hadd Htail]
      · isplitl_exact Hadd
        · iexact Htail
      ihave Hres := Hjoin $$ %(add ++ tail) Hwhole
      isimp only [← List.append_assoc] at Hres
      iexact Hres
  · rw [ancestorCell_ancAt _ _ hz]
    ihave ⟨Hcell, Hclose⟩ :=
      Table.PairSlice_key 0 (v0 + UInt32.ofNat (8 * done.length)) add
        hmlt $$ Hadd
    isimp only [getElem_entryAt add hmlt] at Hcell
    isplitl_exact Hcell
    · iintro Hcell
      ihave Hadd := Hclose $$ %(entryAt add m).1 Hcell
      isimp only [set_key_self add hmlt] at Hadd
      isplitl_exact Hanc
      · iintro %tail Htail
        isimp only [hlen, ← addr_add v0 done.length add.length] at Htail
        ihave Hwhole :=
          pairSlice_join (v0 + UInt32.ofNat (8 * done.length)) add tail
            $$ [Hadd Htail]
        · isplitl_exact Hadd
          · iexact Htail
        ihave Hres := Hjoin $$ %(add ++ tail) Hwhole
        isimp only [← List.append_assoc] at Hres
        iexact Hres


/-- The depth of a child of a turn that still has a limit. -/
private theorem depth_child (x : UInt32) (h : x ≠ 0) :
    quicksortDepth (x - 1).toNat = 256 * x.toNat := by
  have hne : x.toNat ≠ 0 := by
    intro h0
    exact h (UInt32.toNat_inj.mp (by rw [h0]; rfl))
  unfold quicksortDepth
  rw [limit_dec x h]
  omega

/-- The region of a child, named by the depth of the child. -/
private theorem below_child [WasmHeapGS Universal.State] (sp x : UInt32)
    (bs : List UInt8) (h : x ≠ 0) :
    StackBelow sp (256 * x.toNat) bs ⊢
      StackBelow sp (quicksortDepth (x - 1).toNat) bs := by
  rw [depth_child x h]

/-- The region of a child, named by the limit of the turn. -/
private theorem below_parent [WasmHeapGS Universal.State]
    (sp x : UInt32) (bs : List UInt8) (h : x ≠ 0) :
    StackBelow sp (quicksortDepth (x - 1).toNat) bs ⊢
      StackBelow sp (256 * x.toNat) bs := by
  rw [depth_child x h]

/-- A run of distinct keys without its head has distinct keys. -/
private theorem nodupKeys_tail {p : UInt32 × UInt32}
    {l : List (UInt32 × UInt32)} (h : NodupKeys (p :: l)) :
    NodupKeys l := by
  unfold NodupKeys at h ⊢
  rw [List.map_cons, List.nodup_cons] at h
  exact h.2

/-- The address of the entry after the pivot. -/
private theorem addr_succ8 (v : UInt32) (i : Nat) :
    (8 : UInt32) + (v + UInt32.ofNat (8 * i))
      = v + UInt32.ofNat (8 * (i + 1)) := by
  rw [show (8 : UInt32) = UInt32.ofNat (8 * 1) from rfl, addr_shift]

/-- A key that is not below and not equal is above. -/
private theorem key_lt_of_le_of_ne {a b : UInt32} (hle : a ≤ b)
    (hne : a ≠ b) : a < b := by
  have h1 : a.toNat ≤ b.toNat := hle
  have h2 : a.toNat ≠ b.toNat := fun hc => hne (UInt32.toNat_inj.mp hc)
  exact UInt32.lt_iff_toNat_lt.mpr (by omega)

/-- The last entry of a run that ends with one entry. -/
private theorem entryAt_append_last (l : List (UInt32 × UInt32))
    (p : UInt32 × UInt32) : entryAt (l ++ [p]) l.length = p := by
  have hlen : l.length < (l ++ [p]).length := by
    rw [List.length_append, List.length_singleton]
    omega
  rw [entryAt_eq_getElem _ hlen]
  simp

/-- The two pieces of `doneOwn` make `doneOwn`. -/
private theorem doneOwn_pack [WasmHeapGS Universal.State] (v0 : UInt32)
    (anc cur : Option (UInt32 × UInt32))
    (done : List (UInt32 × UInt32)) :
    iprop(AncestorCell cur ∗
        (AncestorCell cur -∗ AncestorCell anc ∗
          (∀ tail : List (UInt32 × UInt32),
            Table.PairSlice 0 (v0 + UInt32.ofNat (8 * done.length))
                tail -∗
              Table.PairSlice 0 v0 (done ++ tail)))) ⊢
      doneOwn v0 anc cur done := by
  iintro H
  unfold doneOwn
  iexact H

/-! ## Folding the locals

`wasm_twp_pures` leaves the locals of a step as a record.  The lemma
below puts the record back in the vocabulary of `qsRegs`, which every
stage lemma of the body uses.  The five parameters are explicit, so one
lemma folds a record that a `local.set` of a parameter changed. -/

private theorem qsRegs_fold (b l a li fp : UInt32) (nt : NetScratch)
    (x16 x17 x18 : UInt32) (l6 l7 l8 l9 l10 l11 : UInt32)
    (l12 : UInt64) (l13 l14 l15 : UInt32) (vs : List Value) :
    ({ params := [.i32 b, .i32 l, .i32 a, .i32 li, .i32 nt.r4],
       locals := [.i32 fp, .i32 l6, .i32 l7, .i32 l8, .i32 l9,
         .i32 l10, .i32 l11, .i64 l12, .i32 l13, .i32 l14, .i32 l15,
         .i32 x16, .i32 x17, .i32 x18, .i64 nt.r19, .i64 nt.r20,
         .i32 nt.r21, .i32 nt.r22, .i32 nt.r23, .i32 nt.r24,
         .i64 nt.r25, .i32 nt.r26, .i64 nt.r27, .i32 nt.r28,
         .i32 nt.r29, nt.p30, nt.p31, nt.p32, nt.p33, nt.p34, nt.p35,
         nt.p36, nt.p37, nt.p38],
       values := vs } : Locals)
      = qsRegs (partRegs b l fp { nt with r2 := a, r3 := li } x16 x17
          x18) l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 vs :=
  rfl

/-! ## Bridges for the tail of one turn

The five lemmas below serve the back edge at WAT 6187 to 6190 and the
exit of the loop.  They move a buffer between two names of one address,
cut the pivot off the front run, and fold the register record that
`qsRegs_fold` leaves into the vocabulary of the loop index. -/

/-- The order of three keys. -/
private theorem key_lt_trans {a b c : UInt32} (h1 : a < b) (h2 : b < c) :
    a < c := by
  rw [UInt32.lt_iff_toNat_lt] at h1 h2 ⊢
  omega

/-- A number of 33 or more is a word of 33 or more. -/
private theorem word_ge_33 (n : Nat) (hn : n < UInt32.size)
    (h : 33 ≤ n) : UInt32.ofNat n ≥ (33 : UInt32) := by
  rw [ge_iff_le, UInt32.le_iff_toNat_le,
    show (33 : UInt32).toNat = 33 from rfl, ofNat_toNat hn]
  exact h

/-- A number below 33 is a word below 33. -/
private theorem word_lt_33 (n : Nat) (hn : n < UInt32.size)
    (h : ¬ 33 ≤ n) : ¬ UInt32.ofNat n ≥ (33 : UInt32) := by
  rw [ge_iff_le, UInt32.le_iff_toNat_le,
    show (33 : UInt32).toNat = 33 from rfl, ofNat_toNat hn]
  exact h

/-- Move an owned buffer between two names of one address. -/
private theorem pairSliceMove [WasmHeapGS Universal.State]
    {v w : UInt32} {l : List (UInt32 × UInt32)} (h : v = w) :
    Table.PairSlice 0 v l ⊢ Table.PairSlice 0 w l := by
  rw [h]

/-- Cut the head entry off a buffer. -/
private theorem pairSlice_head [WasmHeapGS Universal.State] (v : UInt32)
    (a : UInt32 × UInt32) (b : List (UInt32 × UInt32)) :
    Table.PairSlice 0 v (a :: b) ⊢
      iprop(Table.PairSlice 0 v [a] ∗
        Table.PairSlice 0 (v + UInt32.ofNat (8 * 1)) b) :=
  pairSlice_cut v [a] b

/-- Two neighbouring buffers are one buffer, with the second address
given by name. -/
private theorem pairSlice_join_at [WasmHeapGS Universal.State]
    (v w : UInt32) (a b : List (UInt32 × UInt32))
    (haddr : w = v + UInt32.ofNat (8 * a.length)) :
    iprop(Table.PairSlice 0 v a ∗ Table.PairSlice 0 w b) ⊢
      Table.PairSlice 0 v (a ++ b) := by
  subst haddr
  exact pairSlice_join v a b

/-- The locals of one turn, folded from the record that a `local.set`
leaves. -/
private theorem loopLocals_fold (v0 fp : UInt32) (nt : NetScratch)
    (x16 x17 x18 : UInt32) (i : LoopIdx) (b l a li : UInt32)
    (hb : b = v0 + UInt32.ofNat (8 * i.done.length))
    (hl : l = UInt32.ofNat i.rest.length)
    (ha : a = ancestorArg i.cur) (hli : li = i.lim) :
    ({ params := [.i32 b, .i32 l, .i32 a, .i32 li, .i32 nt.r4],
       locals := [.i32 fp, .i32 i.r6, .i32 i.r7, .i32 i.r8, .i32 i.r9,
         .i32 i.r10, .i32 i.r11, .i64 i.r12, .i32 i.r13, .i32 i.r14,
         .i32 i.r15, .i32 x16, .i32 x17, .i32 x18, .i64 nt.r19,
         .i64 nt.r20, .i32 nt.r21, .i32 nt.r22, .i32 nt.r23,
         .i32 nt.r24, .i64 nt.r25, .i32 nt.r26, .i64 nt.r27,
         .i32 nt.r28, .i32 nt.r29, nt.p30, nt.p31, nt.p32, nt.p33,
         nt.p34, nt.p35, nt.p36, nt.p37, nt.p38],
       values := [] } : Locals)
      = loopLocals v0 fp nt x16 x17 x18 i := by
  subst hb
  subst hl
  subst ha
  subst hli
  rfl

/-- The locals of the small sort, folded from the record that a
`local.set` leaves. -/
private theorem rLoc_fold (b l a li fp : UInt32) (nt : NetScratch)
    (x16 x17 x18 : UInt32) (l6 l7 l8 l9 l10 l11 : UInt32)
    (l12 : UInt64) (l13 l14 l15 : UInt32) (vs : List Value) :
    ({ params := [.i32 b, .i32 l, .i32 a, .i32 li, .i32 nt.r4],
       locals := [.i32 fp, .i32 l6, .i32 l7, .i32 l8, .i32 l9,
         .i32 l10, .i32 l11, .i64 l12, .i32 l13, .i32 l14, .i32 l15,
         .i32 x16, .i32 x17, .i32 x18, .i64 nt.r19, .i64 nt.r20,
         .i32 nt.r21, .i32 nt.r22, .i32 nt.r23, .i32 nt.r24,
         .i64 nt.r25, .i32 nt.r26, .i64 nt.r27, .i32 nt.r28,
         .i32 nt.r29, nt.p30, nt.p31, nt.p32, nt.p33, nt.p34, nt.p35,
         nt.p36, nt.p37, nt.p38],
       values := vs } : Locals)
      = rLoc b l fp { nt with r2 := a, r3 := li, r14 := l14 }
          l6 l7 l8 l9 l10 l11 l12 l13 l15 x16 x17 x18 vs :=
  rfl

/-! ## The quicksort loop, WAT 5685 to 6191 -/

set_option maxHeartbeats 4000000 in
private theorem twp_qs_loop [WasmSmallStepGS hlc Universal.State]
    {M : Nat} (hrec : Func21Upto (hlc := hlc) M)
    {sp v0 limit : UInt32} {anc : Option (UInt32 × UInt32)}
    {pairs : List (UInt32 × UInt32)} {nt : NetScratch}
    {r16 r17 r18 : UInt32}
    {callerLocals : Locals} {stack : List Value} {code : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hbound : pairs.length ≤ M) (h27 : pairs.length ≤ 2 ^ 27)
    (hnodup : NodupKeys pairs)
    (hroom : v0.toNat + 8 * pairs.length < UInt32.size)
    (hsp : quicksortDepth limit.toNat ≤ sp.toNat) (i : LoopIdx) :
    loopInv sp v0 limit anc pairs callerLocals stack code arity
        remainder controls calls s E Φ i ⊢
      WP (.running ⟨loopLocals v0 (sp - 256) nt r16 r17 r18 i,
          [.loop 0 0 qsLoopBody], 0, [], qsBlocks,
          { locals := { callerLocals with values := stack },
            continuation := code, resultArity := arity,
            callerRemainder := remainder, control := controls,
            returningInstance := ⟨0⟩ } :: calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  have hsz : UInt32.size = 4294967296 := rfl
  have hdepth : quicksortDepth limit.toNat = 256 * limit.toNat + 256 :=
    depth_eq limit
  have hspLow : 256 ≤ sp.toNat := by omega
  have hfpNat : (sp - 256).toNat = sp.toNat - 256 := by
    rw [UInt32.toNat_sub, show (256 : UInt32).toNat = 256 from rfl]
    have := UInt32.toNat_lt sp
    omega
  iintro Hinv
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := LoopIdx) (measure := fun j => j.rest.length)
    (locals := fun j => loopLocals v0 (sp - 256) nt r16 r17 r18 j)
    (I := fun j => loopInv sp v0 limit anc pairs callerLocals stack code
      arity remainder controls calls s E Φ j)
    (initial := i)
    (initialLocals := loopLocals v0 (sp - 256) nt r16 r17 r18 i)
    rfl rfl
  · intro j
    obtain ⟨jdone, jrest, jcur, jlim, j6, j7, j8, j9, j10, j11, j12,
      j13, j14, j15⟩ := j
    iintro Hrec2 Hinv
    isimp only [loopInv] at Hinv
    icases Hinv with ⟨%hpure, Hruntime, Hsp, Hrem, Hframe, Hbuf, Hown,
      Hcont⟩
    obtain ⟨hperm, hsorted, hcross, hbel, hzero, hfits, hbig, hlim⟩ :=
      hpure
    icases Hrem with ⟨%rem, Hrem⟩
    icases Hframe with ⟨%frame, %hframeLen, Hframe⟩
    have hlenSum : jdone.length + jrest.length = pairs.length := by
      have hl := hperm.length_eq
      rw [List.length_append] at hl
      omega
    have hrestFit : jrest.length < UInt32.size := by omega
    have hlenTo : (UInt32.ofNat jrest.length).toNat = jrest.length :=
      ofNat_toNat hrestFit
    have hbufTo : (v0 + UInt32.ofNat (8 * jdone.length)).toNat
        = v0.toNat + 8 * jdone.length :=
      Slices.byteOffset_toNat v0 (8 * jdone.length) (by omega)
    have hroomj : (v0 + UInt32.ofNat (8 * jdone.length)).toNat
        + 8 * jrest.length < UInt32.size := by omega
    simp only [Wasm.SmallStep.loopBodyExpr, qsLoopBody_shape,
      loopLocals_shape]
    wasm_twp_pures [twp_block]
    simp only [qsHeapArm_shape]
    wasm_twp_pures [twp_localGet]
    by_cases hlim0 : jlim = 0
    · -- WAT 5689 to 5693: the heap sort and the exit of the body
      subst hlim0
      simp only [qsRegs]
      iapply Wasm.SmallStep.twp_brIfZero
      wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
      have H25 := Func22Proof.func22_correct (hlc := hlc)
      unfold Func22Spec CallContract callExpr at H25
      simp only [List.cons_append, List.nil_append] at H25
      iapply H25 (v0 + UInt32.ofNat (8 * jdone.length))
        (UInt32.ofNat jrest.length) j6 jrest
        (callerLocals := qsRegs (loopRegs v0 (sp - 256) nt r16 r17 r18
            ⟨jdone, jrest, jcur, 0, j6, j7, j8, j9, j10, j11, j12, j13,
              j14, j15⟩) j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 [])
        (stack := [])
      isplitl_exact Hruntime
      · isplitl_exact Hbuf
        · isplitl_pureexact ⟨hlenTo.symm, by omega⟩
          · isimp only [SortPostFrameless]
            iintro %out Hruntime Hbuf %hfacts
            obtain ⟨hpout, hsout⟩ := hfacts
            isimp only [ResumeWP, resumeExpr, List.nil_append,
              List.append_nil]
            iapply Wasm.SmallStep.twp_br rfl
            simp only [qsFrame, List.take_zero, List.nil_append,
              List.drop_zero]
            ihave ⟨Hanc, Hwhole⟩ :=
              doneOwn_close v0 anc jcur jdone out $$ [Hown Hbuf]
            · isplitl_exact Hown
              · iexact Hbuf
            iapply (twp_qs_epilogue (pairs := pairs)
              (kept := AncestorCell anc) (limit := limit)
              ((hpout.append_left jdone).trans hperm)
              (sorted_join hsorted hsout (fun x hx y hy =>
                UInt32.le_of_lt (hcross x hx y (hpout.subset hy))))
              hframeLen)
            isplitl_exact Hruntime
            · isplitl_exact Hsp
              · isplitl_exact Hrem
                · isplitl_exact Hframe
                  · isplitl_exact Hwhole
                    · isplitl_exact Hanc
                      · iexact Hcont
    · -- WAT 5689: the limit is not spent, so the turn partitions
      iapply Wasm.SmallStep.twp_brIf hlim0 rfl
      simp only [List.take_zero, List.nil_append, List.drop_zero,
        qsRegs_fold]
      set G : Regs := partRegs (v0 + UInt32.ofNat (8 * jdone.length))
        (UInt32.ofNat jrest.length) (sp - 256)
        { nt with r2 := ancestorArg jcur, r3 := jlim } r16 r17 r18
        with hG
      have hGbuf : G.buf = v0 + UInt32.ofNat (8 * jdone.length) := rfl
      have hGlen : G.len.toNat = jrest.length := hlenTo
      iapply (twp_pivot (rest := jrest) ?_ ?_ ?_)
      on_goal 5 =>
        isimp only [hGbuf]
        isplitl_exact Hbuf
        · isplitl_exact Hruntime
          · exact BI.BIBase.Entails.rfl
      on_goal 4 => rw [hGbuf, hGlen]; exact hroomj
      on_goal 3 => rw [hGlen]; omega
      on_goal 2 => rw [hGlen]
      intro ip k6 k7 k8 k9 k10 k11 hip hk6
      rw [hGbuf] at hk6
      subst hk6
      iintro ⟨Hbuf, Hruntime, HRest⟩
      simp only [hG, partRegs, qsAfterMedian_split, qsLimitDec_shape,
        List.cons_append, List.nil_append, qsRegs, qsLocals]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      simp only [add_neg_one]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_localGet twp_sub]
      simp only [add_sub_self]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      -- WAT 5758: the block of the two partitions
      wasm_twp_pures [twp_block]
      simp only [qsPartitionBody_shape, qsRegs_fold]
      set H : Regs := partRegs (v0 + UInt32.ofNat (8 * jdone.length))
        (UInt32.ofNat jrest.length) (sp - 256)
        { nt with r2 := ancestorArg jcur, r3 := jlim - 1 } r16 r17 r18
        with hH
      have hHbuf : H.buf = v0 + UInt32.ofNat (8 * jdone.length) := rfl
      icases HRest with
        ⟨⟨⟨⟨⟨Hrec2, Hsp⟩, Hown⟩, Hcont⟩, Hrem⟩, Hframe⟩
      isimp only [doneOwn] at Hown
      icases Hown with ⟨Hcur, Hback⟩
      have hroomG : (v0 + UInt32.ofNat (8 * jdone.length)).toNat
          + 8 * (UInt32.ofNat jrest.length).toNat < UInt32.size := by
        rw [hlenTo]
        exact hroomj
      iapply (twp_equal_guard (cur := jcur) (rest := jrest) (f := H)
        hlenTo.symm hip hroomG rfl hbel hzero hfits ?_)
      on_goal 2 =>
        isimp only [hHbuf]
        isplitl_exact Hbuf
        · isplitl_exact Hcur
          · exact BI.BIBase.Entails.rfl
      intro j7
      iintro ⟨Hbuf, Hcur, HRest⟩
      simp only [qsAfterEqual_split]
      iapply (twp_strict_partition (ip := ip) (pairs := jrest)
        (rest := qsRecurse) (f := H) hlenTo.symm
        (by rw [show H.len.toNat = jrest.length from hlenTo]; omega)
        hip hroomG ?_)
      on_goal 2 =>
        isplitl_exact Hbuf
        · exact BI.BIBase.Entails.rfl
      intro lt ge numLt m7 m8 m9 m10 m11 m13 m14 m15 m12 hltlen hnumLt
        hpermPart hlow hhigh
      iintro ⟨Hbuf, Hcur, HRest⟩
      subst hltlen
      have hpsLen : (entryAt jrest ip :: (lt ++ ge)).length
          = jrest.length := hpermPart.length_eq
      have hltLt : lt.length < jrest.length := by
        rw [← hlenTo]
        exact hnumLt
      have hgeLen : ge.length = jrest.length - lt.length - 1 := by
        rw [List.length_cons, List.length_append] at hpsLen
        omega
      -- WAT 6152: the split index is below the length, so no panic
      simp only [qsRecurse_shape, hH, partRegs, qsRegs, qsLocals]
      iapply Wasm.SmallStep.twp_brIfZero
      wasm_twp_pures [twp_localGet]
      iapply twp_entry_read (k := 0) (n := jrest.length) (by omega)
        hpsLen hroomj (addr_zero _)
      isplitl_exact Hbuf
      iintro Hbuf
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      -- WAT 6155 to 6172: the pivot goes between the two parts
      have hltTo : (UInt32.ofNat lt.length).toNat = lt.length :=
        ofNat_toNat (by omega)
      have hshl : (UInt32.ofNat lt.length) <<< ((3 : UInt32) % 32)
          = UInt32.ofNat (8 * lt.length) := by
        rw [shl_three _ (by rw [hltTo]; omega), hltTo]
      wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const
        twp_shl]
      simp only [hshl]
      wasm_twp_pures [twp_add]
      simp only [addr_base]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply twp_entry_read (k := lt.length) (n := jrest.length)
        (by omega) hpsLen hroomj rfl
      isplitl_exact Hbuf
      iintro Hbuf
      iapply twp_entry_write (k := 0) (n := jrest.length)
        (q := entryAt (entryAt jrest ip :: (lt ++ ge)) lt.length)
        (by omega) hpsLen hroomj (addr_zero _)
      isplitl_exact Hbuf
      iintro Hbuf
      wasm_twp_pures [twp_localGet twp_localGet]
      have hpsLen2 : ((entryAt jrest ip :: (lt ++ ge)).set 0
          (entryAt (entryAt jrest ip :: (lt ++ ge)) lt.length)).length
            = jrest.length := by
        rw [List.length_set]
        exact hpsLen
      iapply twp_entry_write (k := lt.length) (n := jrest.length)
        (q := entryAt (entryAt jrest ip :: (lt ++ ge)) 0) (by omega)
        hpsLen2 hroomj rfl
      isplitl_exact Hbuf
      iintro Hbuf
      obtain ⟨lt', hltPerm, hswap⟩ :=
        swap_pivot (entryAt jrest ip) lt ge
      isimp only [hswap] at Hbuf
      icases HRest with
        ⟨⟨⟨⟨⟨⟨Hruntime, Hrec2⟩, Hsp⟩, Hcont⟩, Hrem⟩, Hframe⟩, Hback⟩
      -- WAT 6173: the recursion on the part below the pivot
      have hltLen' : lt'.length = lt.length := hltPerm.length_eq
      have hnodupJ : NodupKeys (jdone ++ jrest) :=
        Table.nodupKeys_of_perm hperm hnodup
      have hnodupRest : NodupKeys jrest := nodupKeys_right hnodupJ
      have hnodupPs : NodupKeys (entryAt jrest ip :: (lt ++ ge)) :=
        Table.nodupKeys_of_perm hpermPart hnodupRest
      have hsubLt : ∀ x ∈ lt', x ∈ jrest := fun x hx =>
        hpermPart.subset (List.mem_cons_of_mem _
          (List.mem_append_left _ (hltPerm.subset hx)))
      ihave ⟨Hrem, %hremLen⟩ :=
        StackBelow_length (sp - 256) (256 * limit.toNat) rem $$ Hrem
      ihave ⟨Hleft, Hright⟩ :=
        pairSlice_cut (v0 + UInt32.ofNat (8 * jdone.length)) lt'
          (entryAt jrest ip :: ge) $$ Hbuf
      isimp only [hltLen'] at Hright
      ihave ⟨Hlow, Hchild⟩ :=
        frame_split (sp - 256) (256 * limit.toNat) (256 * jlim.toNat)
          rem (by omega) $$ Hrem
      ihave Hchild :=
        below_child (sp - 256) jlim
          (rem.drop (256 * limit.toNat - 256 * jlim.toNat)) hlim0 $$
          Hchild
      wasm_twp_pures [twp_localGet twp_localGet twp_localGet
        twp_localGet twp_localGet]
      simp only [qsRegs_fold, ← hH]
      have H24 := hrec
      unfold Func21Upto CallContract callExpr at H24
      simp only [List.cons_append, List.nil_append] at H24
      iapply H24 (sp - 256) (v0 + UInt32.ofNat (8 * jdone.length))
        (UInt32.ofNat lt.length) (jlim - 1) nt.r4 jcur lt'
        (rem.drop (256 * limit.toNat - 256 * jlim.toNat))
        (callerLocals := qsRegs H (UInt32.ofNat lt.length)
          (v0 + UInt32.ofNat (8 * jdone.length)
            + UInt32.ofNat (8 * lt.length)) m8 m9 m10 m11
          (Table.pairWord (entryAt (entryAt jrest ip :: (lt ++ ge)) 0))
          m13 m14 m15 [])
        (stack := []) (by omega) hfits
      isplitl_exact Hruntime
      · isplitl_exact Hsp
        · isplitl_exact Hchild
          · isplitl_exact Hleft
            · isplitl_exact Hcur
              · isplitl_pureexact ⟨by rw [hltLen', hltTo],
                  by rw [hltTo]; omega,
                  Table.nodupKeys_of_perm hltPerm
                    (nodupKeys_left (nodupKeys_tail hnodupPs)),
                  ancestorBelow_sub hbel hsubLt,
                  by rw [hltTo]; omega,
                  by rw [depth_child jlim hlim0, hfpNat]; omega,
                  hzero⟩
                · isimp only [SortPost]
                  iintro %out %below' Hruntime Hsp Hbelow Hbuf Hcur
                    %hfacts
                  obtain ⟨houtPerm, houtSorted⟩ := hfacts
                  isimp only [ResumeWP, resumeExpr, List.nil_append,
                    List.append_nil]
                  have hlenNew :
                      (UInt32.ofNat lt.length ^^^ 4294967295)
                          + UInt32.ofNat jrest.length
                        = UInt32.ofNat ge.length := by
                    rw [len_after _ _ (by rw [hltTo, hlenTo]; omega),
                      hlenTo, hltTo, ← hgeLen]
                  simp only [hH, partRegs]
                  wasm_twp_pures [twp_localGet twp_localGet twp_const]
                  iapply Wasm.SmallStep.twp_xor
                  wasm_twp_pures [twp_add]
                  simp only [hlenNew]
                  wasm_twp_localSet [List.set, List.length_cons,
                    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
                  wasm_twp_pures [twp_localGet twp_const twp_add]
                  simp only [addr_succ8]
                  wasm_twp_localSet [List.set, List.length_cons,
                    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
                  wasm_twp_pures [twp_localGet]
                  wasm_twp_localSet [List.set, List.length_cons,
                    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
                  wasm_twp_pures [twp_exitControl] using
                    [List.take_zero, List.nil_append, List.drop_zero]
                  simp only [qsLoopGuard_shape]
                  wasm_twp_pures [twp_localGet twp_const]
                  -- the two runs after one turn of the loop
                  have hspLt := UInt32.toNat_lt sp
                  have houtLen : out.length = lt.length := by
                    rw [houtPerm.length_eq, hltLen']
                  have houtSub : ∀ x ∈ out, x ∈ lt := fun x hx =>
                    hltPerm.subset (houtPerm.subset hx)
                  have hpMem : entryAt jrest ip ∈ jrest :=
                    hpermPart.subset (by simp)
                  have hgeSub : ∀ y ∈ ge, y ∈ jrest := fun y hy =>
                    hpermPart.subset (List.mem_cons_of_mem _
                      (List.mem_append_right _ hy))
                  have hpLtGe :
                      ∀ y ∈ ge, (entryAt jrest ip).1 < y.1 := by
                    intro y hy
                    exact key_lt_of_le_of_ne (hhigh y hy)
                      (key_ne_of_nodup hnodupPs
                        (List.mem_append_right _ hy))
                  have hDlen :
                      (jdone ++ (out ++ [entryAt jrest ip])).length
                        = jdone.length + lt.length + 1 := by
                    have h := houtLen
                    simp only [List.length_append, List.length_cons,
                      List.length_nil]
                    omega
                  have hnewPerm :
                      (out ++ entryAt jrest ip :: ge).Perm jrest :=
                    (((houtPerm.trans hltPerm).append_right
                        (entryAt jrest ip :: ge)).trans
                      List.perm_middle).trans hpermPart
                  have hpermD :
                      (jdone ++ (out ++ [entryAt jrest ip])
                          ++ ge).Perm pairs := by
                    simp only [List.append_assoc, List.singleton_append]
                    exact (hnewPerm.append_left jdone).trans hperm
                  have hsortAdd :
                      Table.SortedByKey
                        (out ++ [entryAt jrest ip]) := by
                    refine sorted_join houtSorted
                      (Table.sortedByKey_singleton _) ?_
                    intro x hx y hy
                    have hy' : y = entryAt jrest ip := by simpa using hy
                    subst hy'
                    exact UInt32.le_of_lt (hlow x (houtSub x hx))
                  have hsortD : Table.SortedByKey
                      (jdone ++ (out ++ [entryAt jrest ip])) := by
                    refine sorted_join hsorted hsortAdd ?_
                    intro x hx y hy
                    rcases List.mem_append.mp hy with h | h
                    · exact UInt32.le_of_lt (hcross x hx y
                        (hpermPart.subset (List.mem_cons_of_mem _
                          (List.mem_append_left _ (houtSub y h)))))
                    · have hy' : y = entryAt jrest ip := by
                        simpa using h
                      subst hy'
                      exact UInt32.le_of_lt (hcross x hx _ hpMem)
                  have hcrossD : ∀ x ∈ jdone ++ (out ++
                      [entryAt jrest ip]), ∀ y ∈ ge, x.1 < y.1 := by
                    intro x hx y hy
                    rcases List.mem_append.mp hx with h | h
                    · exact hcross x h y (hgeSub y hy)
                    · rcases List.mem_append.mp h with h2 | h2
                      · exact key_lt_trans (hlow x (houtSub x h2))
                          (hpLtGe y hy)
                      · have hx' : x = entryAt jrest ip := by
                          simpa using h2
                        subst hx'
                        exact hpLtGe y hy
                  have hfitsD : AncestorFits
                      (ancAt (v0 + UInt32.ofNat (8 * jdone.length)
                          + UInt32.ofNat (8 * lt.length))
                        (entryAt jrest ip).1) := by
                    rw [addr_add]
                    exact ancestorFits_of_slice v0
                      (jdone.length + lt.length) pairs.length
                      (by omega) hroom _
                  have hlast : entryAt (out ++ [entryAt jrest ip])
                      lt.length = entryAt jrest ip := by
                    rw [← houtLen]
                    exact entryAt_append_last out _
                  have hvNew :
                      v0 + UInt32.ofNat (8 * jdone.length)
                          + UInt32.ofNat (8 * (lt.length + 1))
                        = v0 + UInt32.ofNat (8 *
                            (jdone ++ (out
                              ++ [entryAt jrest ip])).length) := by
                    rw [hDlen, addr_add, Nat.add_assoc]
                  have haddrN :
                      v0 + UInt32.ofNat (8 * jdone.length)
                          + UInt32.ofNat (8 * lt.length)
                          + UInt32.ofNat (8 * 1)
                        = v0 + UInt32.ofNat (8 *
                            (jdone ++ (out
                              ++ [entryAt jrest ip])).length) := by
                    rw [hDlen, addr_add, addr_add, Nat.add_assoc]
                  have hgeFit : ge.length < UInt32.size := by omega
                  have hlimD : (jlim - 1).toNat ≤ limit.toNat := by
                    rw [limit_dec jlim hlim0]
                    omega
                  have hzeroD : ∀ p k,
                      ancAt (v0 + UInt32.ofNat (8 * jdone.length)
                          + UInt32.ofNat (8 * lt.length))
                        (entryAt jrest ip).1 = some (p, k) → p ≠ 0 :=
                    ancAt_ne_zero _ _
                  have hbelD : AncestorBelow
                      (ancAt (v0 + UInt32.ofNat (8 * jdone.length)
                          + UInt32.ofNat (8 * lt.length))
                        (entryAt jrest ip).1) ge :=
                    ancestorBelow_ancAt _ _ ge hpLtGe
                  -- the region below the frame is whole again
                  ihave Hbelow :=
                    below_parent (sp - 256) jlim below' hlim0 $$ Hbelow
                  ihave ⟨Hbelow, %hbelowLen⟩ :=
                    StackBelow_length (sp - 256) (256 * jlim.toNat)
                      below' $$ Hbelow
                  ihave Hrem :=
                    frame_join (sp - 256) (256 * limit.toNat)
                      (256 * jlim.toNat)
                      (rem.take (256 * limit.toNat - 256 * jlim.toNat))
                      below'
                      (by rw [List.length_take, hremLen]; omega)
                      (by omega) $$ [Hlow Hbelow]
                  · isplitl_exact Hlow
                    · iexact Hbelow
                  -- the pivot joins the run that is in place
                  ihave ⟨Hpivot, Hrest⟩ :=
                    pairSlice_head (v0 + UInt32.ofNat (8 * jdone.length)
                        + UInt32.ofNat (8 * lt.length))
                      (entryAt jrest ip) ge $$ Hright
                  ihave Hadd :=
                    pairSlice_join_at
                      (v0 + UInt32.ofNat (8 * jdone.length))
                      (v0 + UInt32.ofNat (8 * jdone.length)
                        + UInt32.ofNat (8 * lt.length))
                      out [entryAt jrest ip] (by rw [houtLen])
                      $$ [Hbuf Hpivot]
                  · isplitl_exact Hbuf
                    · iexact Hpivot
                  ihave Hrest := pairSliceMove haddrN $$ Hrest
                  ihave Hown :=
                    doneOwn_pack v0 anc jcur jdone $$ [Hcur Hback]
                  · isplitl_exact Hcur
                    · iexact Hback
                  ihave Hown :=
                    doneOwn_grow v0 anc jcur jdone
                      (out ++ [entryAt jrest ip]) lt.length
                      (by simp [houtLen]) $$ [Hown Hadd]
                  · isplitl_exact Hown
                    · iexact Hadd
                  isimp only [hlast] at Hown
                  by_cases hge : 33 ≤ ge.length
                  · -- WAT 6190: the run is long, so the loop turns
                    iapply Wasm.SmallStep.twp_geU (result := 1)
                      (by rw [if_pos (word_ge_33 ge.length hgeFit hge)])
                    iapply Wasm.SmallStep.twp_brIf
                      (by decide : (1 : UInt32) ≠ 0) rfl
                    simp only [List.take_zero, List.nil_append]
                    rw [loopLocals_fold v0 (sp - 256) nt r16 r17 r18
                      (⟨jdone ++ (out ++ [entryAt jrest ip]), ge,
                        ancAt (v0 + UInt32.ofNat (8 * jdone.length)
                            + UInt32.ofNat (8 * lt.length))
                          (entryAt jrest ip).1,
                        jlim - 1, UInt32.ofNat lt.length,
                        v0 + UInt32.ofNat (8 * jdone.length)
                          + UInt32.ofNat (8 * lt.length),
                        m8, m9, m10, m11,
                        Table.pairWord
                          (entryAt (entryAt jrest ip :: (lt ++ ge)) 0),
                        m13, m14, m15⟩ : LoopIdx)
                      (v0 + UInt32.ofNat (8 * jdone.length)
                        + UInt32.ofNat (8 * (lt.length + 1)))
                      (UInt32.ofNat ge.length)
                      (v0 + UInt32.ofNat (8 * jdone.length)
                        + UInt32.ofNat (8 * lt.length)) (jlim - 1)
                      hvNew rfl (ancestorArg_ancAt _ _).symm rfl]
                    ihave Hgo := Hrec2
                      $$ %(⟨jdone ++ (out ++ [entryAt jrest ip]), ge,
                        ancAt (v0 + UInt32.ofNat (8 * jdone.length)
                            + UInt32.ofNat (8 * lt.length))
                          (entryAt jrest ip).1,
                        jlim - 1, UInt32.ofNat lt.length,
                        v0 + UInt32.ofNat (8 * jdone.length)
                          + UInt32.ofNat (8 * lt.length),
                        m8, m9, m10, m11,
                        Table.pairWord
                          (entryAt (entryAt jrest ip :: (lt ++ ge)) 0),
                        m13, m14, m15⟩ : LoopIdx)
                      %(show ge.length < jrest.length by omega)
                    iapply Hgo
                    isimp only [loopInv]
                    isplitl_pureexact ⟨hpermD, hsortD, hcrossD, hbelD,
                      hzeroD, hfitsD, hge, hlimD⟩
                    · isplitl_exact Hruntime
                      · isplitl_exact Hsp
                        · isplitl [Hrem]
                          · iexists (rem.take (256 * limit.toNat
                              - 256 * jlim.toNat) ++ below')
                            iexact Hrem
                          · isplitl [Hframe]
                            · iexists frame
                              isplitl_pureexact hframeLen
                              · iexact Hframe
                            · isplitl_exact Hrest
                              · isplitl_exact Hown
                                · iexact Hcont
                  · -- WAT 6190: the run is short, so the loop leaves
                    iapply Wasm.SmallStep.twp_geU (result := 0)
                      (by rw [if_neg (word_lt_33 ge.length hgeFit hge)])
                    iapply Wasm.SmallStep.twp_brIfZero
                    iapply Wasm.SmallStep.twp_exitControl rfl
                    simp only [List.take_zero, List.nil_append,
                      qsBlocks_split]
                    iapply Wasm.SmallStep.twp_exitControl rfl
                    simp only [qsFrame, List.take_zero,
                      List.nil_append, rLoc_fold]
                    ihave Hrest := pairSliceMove hvNew.symm $$ Hrest
                    iapply (twp_qs_finish (v0 := v0) (pairs := pairs)
                      (anc := anc) (limit := limit)
                      (done := jdone ++ (out ++ [entryAt jrest ip]))
                      (rest := ge)
                      (cur := ancAt (v0
                          + UInt32.ofNat (8 * jdone.length)
                          + UInt32.ofNat (8 * lt.length))
                        (entryAt jrest ip).1)
                      hvNew (ofNat_toNat hgeFit).symm
                      (by rw [ofNat_toNat hgeFit]; omega)
                      hpermD hsortD hcrossD hnodup
                      (by
                        rw [hvNew, hDlen, ofNat_toNat hgeFit,
                          Slices.byteOffset_toNat v0
                            (8 * (jdone.length + lt.length + 1))
                            (by omega)]
                        omega)
                      (by omega) hframeLen)
                    isplitl_exact Hruntime
                    · isplitl_exact Hsp
                      · isplitl_exact Hrem
                        · isplitl_exact Hframe
                          · isplitl_exact Hrest
                            · isplitl_exact Hown
                              · iexact Hcont
  · iexact Hinv
/-! ## The body, WAT 5670 to 8663 -/

set_option maxHeartbeats 2000000 in
/-- The whole body, for an input below `N` entries.  `N` carries the
induction that the recursion of WAT 6173 needs. -/
private theorem twp_func21_upto [WasmSmallStepGS hlc Universal.State]
    (N : Nat) : Func21Upto (hlc := hlc) N := by
  induction N with
  | zero =>
      intro sp v len limit env anc pairs below callerLocals stack code
        arity remainder controls calls s E Φ hN hfits
      exact absurd hN (by omega)
  | succ N ih =>
      intro sp v len limit env anc pairs below callerLocals stack code
        arity remainder controls calls s E Φ hN hfits
      unfold CallContract callExpr
      iintro ⟨Hruntime, Hsp, Hbelow, Hbuf, Hanc, %hpure, Hcont⟩
      obtain ⟨hlen, h27, hnodup, hbel, hroom, hspDeep, hzero⟩ := hpure
      have hsz : UInt32.size = 4294967296 := rfl
      have hspLt := UInt32.toNat_lt sp
      have hdepth : quicksortDepth limit.toNat
          = 256 * limit.toNat + 256 := depth_eq limit
      have hspLow : 256 ≤ sp.toNat := by omega
      have hfpNat : (sp - 256).toNat = sp.toNat - 256 := by
        rw [UInt32.toNat_sub, show (256 : UInt32).toNat = 256 from rfl]
        omega
      iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
      simp only [List.cons_append, List.nil_append]
      wasm_twp_rebind Wasm.SmallStep.twp_call
          Project.RustHashMap.«module» 24
          Project.RustHashMap.func21Def (by decide)
          func21_index with Hmodule
      simp only [Project.RustHashMap.func21Def, Function.toLocals,
        Function.numParams, List.length_cons, List.length_nil,
        List.take, List.drop, List.reverse_cons, List.reverse_nil,
        List.map, List.nil_append, List.cons_append, ValueType.zero,
        func21_shape, Nat.reduceAdd]
      iclose_map_runtime Hruntime with Hmodule Henv
      isimp only [StackPointer] at Hsp
      wasm_twp_rebind twp_globalGet with Hsp
      wasm_twp_pures [twp_const twp_sub]
      wasm_twp_localTee [List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub, List.set]
      wasm_twp_rebind twp_globalSet with Hsp
      ihave Hsp : StackPointer (sp - 256) $$ [Hsp]
      · unfold StackPointer
        iexact Hsp
      ihave ⟨Hlower, Hframe⟩ :=
        frame_split sp (quicksortDepth limit.toNat) 256 below
          (by omega) $$ Hbelow
      isimp only [fp_eq, depth_cut] at Hlower
      ihave ⟨%hframeLen, Hframe⟩ :=
        StackBelow_base sp (sp - 256) 256
          (below.drop (quicksortDepth limit.toNat - 256)) (fp_eq sp)
          $$ Hframe
      wasm_twp_pures [twp_block]
      simp only [qsBlock1Body_shape]
      wasm_twp_pures [twp_block]
      simp only [qsBlock2Body_shape]
      wasm_twp_pures [twp_block]
      simp only [qsBlock3Body_shape]
      wasm_twp_pures [twp_block]
      simp only [← qsBlock3Body_shape, ← qsBlock2Body_shape,
        ← qsBlock1Body_shape, List.drop_zero, qsFrame_fold,
        qsBlocks_fold]
      simp only [qsBlock4Body_shape]
      wasm_twp_pures [twp_localGet twp_const]
      by_cases hsmall : len.toNat < 33
      · -- WAT 5684: a short buffer skips the loop
        have hlt : len < (33 : UInt32) := by
          rw [UInt32.lt_iff_toNat_lt,
            show (33 : UInt32).toNat = 33 from rfl]
          exact hsmall
        iapply Wasm.SmallStep.twp_ltU (result := 1) (by rw [if_pos hlt])
        iapply Wasm.SmallStep.twp_brIf
          (by decide : (1 : UInt32) ≠ 0) rfl
        simp only [regBlocks_fold]
        simp only [qsFrame, List.take_zero, List.nil_append,
          initialLocals_fold]
        ihave Hown := doneOwn_start v anc $$ Hanc
        iapply (twp_qs_finish (v0 := v) (anc := anc) (cur := anc)
          (pairs := pairs) (done := []) (rest := pairs)
          (limit := limit) (addr_zero v) hlen (by omega)
          (List.Perm.refl _) Table.SortedByKey.nil (by simp) hnodup
          hroom (by omega) hframeLen)
        isplitl_exact Hruntime
        · isplitl_exact Hsp
          · isplitl_exact Hlower
            · isplitl_exact Hframe
              · isplitl [Hbuf]
                · iexact Hbuf
                · isplitl_exact Hown
                  · iexact Hcont
      · -- WAT 5684: a long buffer runs the loop
        have hnlt : ¬ len < (33 : UInt32) := by
          rw [UInt32.lt_iff_toNat_lt,
            show (33 : UInt32).toNat = 33 from rfl]
          omega
        iapply Wasm.SmallStep.twp_ltU (result := 0)
          (by rw [if_neg hnlt])
        iapply Wasm.SmallStep.twp_brIfZero
        have hlenWord : len = UInt32.ofNat pairs.length := by
          rw [hlen]
          exact (UInt32.toNat_inj.mp (ofNat_toNat (by omega))).symm
        rw [loopLocals_fold v (sp - 256)
          (zeroNet (ancestorArg anc) limit env) 0 0 0
          ⟨[], pairs, anc, limit, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
          v len (ancestorArg anc) limit (addr_zero v) hlenWord rfl rfl]
        ihave Hown := doneOwn_start v anc $$ Hanc
        ihave Hbuf := pairSliceMove (addr_zero v) $$ Hbuf
        iapply (twp_qs_loop (M := N) ih (by omega) (by omega) hnodup
          (by omega) hspDeep
          ⟨[], pairs, anc, limit, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)
        isimp only [loopInv]
        isplitl_pureexact ⟨List.Perm.refl _, Table.SortedByKey.nil,
          by simp, hbel, hzero, hfits, by omega, le_rfl⟩
        · isplitl_exact Hruntime
          · isplitl_exact Hsp
            · isplitl [Hlower]
              · iexists (List.take (256 * limit.toNat) below)
                iexact Hlower
              · isplitl [Hframe]
                · iexists
                    (List.drop (quicksortDepth limit.toNat - 256) below)
                  isplitl_pureexact hframeLen
                  · iexact Hframe
                · isplitl [Hbuf]
                  · iexact Hbuf
                  · isplitl_exact Hown
                    · iexact Hcont


/-! ## The contract

`Func21Upto` proves the body for an input below `N` entries, so the
whole input needs `N = pairs.length + 1`.

The first theorem below takes `AncestorFits anc` as a hypothesis.  The
load at WAT 5764 reads four bytes at the ancestor address, and
`Wasm.SmallStep.twp_load32_addr` asks that those four bytes do not run
over the end of the address space.  `AncestorCell` carries no bound of
its own, because a cell is four owned bytes and nothing more, and a
load of four bytes at address `2 ^ 32 - 1` traps.
`SortContracts.Func21Spec` therefore states the fact in its pure part,
and `func21_correct` is the contract itself.

Every call site of the program has it.  The top call, absolute `func 14`
at WAT 2839, passes the null ancestor, and `ancestorFits_none` covers
it.  Every recursive call of WAT 6173 passes a key cell of its own
buffer, and `PairSlice` bounds that buffer, so the induction carries the
fact down. -/

/-- A call that carries no ancestor fits. -/
theorem ancestorFits_none : AncestorFits none := by
  intro p k h
  exact absurd h (by simp)

/-- Absolute `func 24` sorts its buffer.  This is
`SortContracts.Func21Spec` with `AncestorFits anc` as a separate
hypothesis; read the note above for why the contract states it. -/
theorem func21_correct_of_ancestorFits
    [WasmSmallStepGS hlc Universal.State]
    (sp v len limit env : UInt32) (anc : Option (UInt32 × UInt32))
    (pairs : List (UInt32 × UInt32)) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hfits : AncestorFits anc) :
    CallContract 24
      [.i32 env, .i32 limit, .i32 (ancestorArg anc), .i32 len, .i32 v]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp (quicksortDepth limit.toNat) below ∗
        Table.PairSlice 0 v pairs ∗
        AncestorCell anc ∗
        ⌜pairs.length = len.toNat ∧ len.toNat ≤ 2 ^ 27 ∧
          NodupKeys pairs ∧ AncestorBelow anc pairs ∧
          v.toNat + 8 * len.toNat < UInt32.size ∧
          quicksortDepth limit.toNat ≤ sp.toNat ∧
          (∀ p k, anc = some (p, k) → p ≠ 0)⌝ ∗
        SortPost v pairs sp (quicksortDepth limit.toNat)
          (AncestorCell anc) callerLocals stack code arity remainder
          controls calls s E Φ) :=
  twp_func21_upto (pairs.length + 1) sp v len limit env anc pairs below
    (by omega) hfits

set_option maxHeartbeats 2000000 in
/-- `SortContracts.Func21Spec` holds: absolute `func 24` sorts its
buffer.  The pure part of the contract now carries `AncestorFits anc`,
so the hypothesis of `func21_correct_of_ancestorFits` comes out of the
precondition. -/
theorem func21_correct [WasmSmallStepGS hlc Universal.State] :
    Func21Spec (hlc := hlc) := by
  unfold Func21Spec CallContract callExpr
  intro sp v len limit env anc pairs below callerLocals stack code
    arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hbuf, Hanc, %hpure, Hcont⟩
  obtain ⟨hplen, hlen27, hnodup, hbelow, hroom, hdepth, hzero,
    hfits⟩ := hpure
  have Hcall := func21_correct_of_ancestorFits sp v len limit env anc
    pairs below (callerLocals := callerLocals) (stack := stack)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls) (s := s) (E := E) (Φ := Φ)
    hfits
  unfold CallContract callExpr at Hcall
  iapply Hcall
  isplitl_exacts [Hruntime Hsp Hbelow Hbuf Hanc]
  · isplitl_pureexact (⟨hplen, hlen27, hnodup, hbelow, hroom, hdepth,
      hzero⟩ : pairs.length = len.toNat ∧ len.toNat ≤ 2 ^ 27 ∧
        NodupKeys pairs ∧ AncestorBelow anc pairs ∧
        v.toNat + 8 * len.toNat < UInt32.size ∧
        quicksortDepth limit.toNat ≤ sp.toNat ∧
        (∀ p k, anc = some (p, k) → p ≠ 0))
    · iexact Hcont

end Project.RustHashMap.Func21Proof
