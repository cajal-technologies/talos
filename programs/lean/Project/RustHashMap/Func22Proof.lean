import Project.RustHashMap.HeapModel

/-!
# Proof of `heapsort`, absolute `func 25`

Absolute `func 25` is `heapsort`, local `func22`, WAT lines 8664 to 8809
of `programs/rust/build/rust_hash_map/program.wat`.  This module proves
`SortContracts.Func22Spec`.

## The register map

The body has three parameters and eight more registers.

| Register | Meaning |
| --- | --- |
| 0 | the buffer address, never written |
| 1 | the length, never written |
| 2 | the comparison closure, never read |
| 3 | the loop counter `i` |
| 4 | the node index, and the node address inside one sift step |
| 5 | the entry that the exchange of the sort phase holds |
| 6 | the first child index, then the chosen child index |
| 7 | twice the node index, then the second child index |
| 8 | the bound of the sift |
| 9 | the key and then the value of the node |
| 10 | the key of the chosen child |

## The six regions

| Name | WAT | What it does |
| --- | --- | --- |
| `guardBody` | 8667 to 8807 | the early exit and the whole sort |
| `outerBody` | 8676 to 8806 | one step of the merged loop |
| `phaseIndex` | 8678 to 8689 | the counter step and the phase test |
| `phaseBody` | 8677 to 8707 | the phase split and the root exchange |
| `siftBlock` | 8710 to 8803 | the bound, the childless exit and the sift |
| `siftStep` | 8727 to 8802 | one step of the sift loop |
| `pickBody` | 8728 to 8755 | the choice of the greater child |
| `childBody` | 8729 to 8738 | the test for a second child |

## The two loops

The outer loop counts register 3 down from `len + len / 2` to `0`.  The
buffer holds `HeapModel.heapsortUpto pairs len c`, where `c` is the
counter value at the top of the body.  The measure is `c`.

The sift loop walks the node down the heap.  The buffer holds a list
`cur` whose remaining sift work is the whole sift of the entry state:
`siftDownAux bound cur bound node = siftDown ps0 bound node0`.  The
measure is `bound - node`.  One swap step of the compiled body is one
step of `siftDownAux`, and each of the three exits makes the remaining
work empty, so the buffer holds `siftDown ps0 bound node0`.
-/

namespace Project.RustHashMap.Func22Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.SortContracts
open Project.RustHashMap.SortModels
open Project.RustHashMap.SortPures
open Project.RustHashMap.HeapModel
open scoped Wasm.SmallStep.Outcome

/-! ## Word arithmetic -/

/-- Setting the low bit of an even number adds one. -/
private theorem two_mul_lor_one (m : Nat) : 2 * m ||| 1 = 2 * m + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    have h1 : 2 * m / 2 = m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    simp [Nat.testBit_succ, h1, h2]

private theorem ofNat_toNat {k : Nat} (h : k < UInt32.size) :
    (UInt32.ofNat k).toNat = k := UInt32.toNat_ofNat_of_lt' h

/-- `i32.shl` masks the shift count. -/
private theorem shl_three (x : UInt32) :
    x <<< ((3 : UInt32) % 32) = x <<< 3 := rfl

private theorem shl_one (x : UInt32) :
    x <<< ((1 : UInt32) % 32) = x <<< 1 := rfl

private theorem shr_one (x : UInt32) :
    x >>> ((1 : UInt32) % 32) = x >>> 1 := rfl

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

/-- `i32.shl` by one is a multiplication by two. -/
private theorem shift_one (x : UInt32)
    (hbound : 2 * x.toNat < UInt32.size) :
    x <<< (1 : UInt32) = UInt32.ofNat (2 * x.toNat) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have h2 : (2 : Nat) ^ 1 = 2 := by norm_num
  have hlt : x.toNat * 2 < 2 ^ 32 := by omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft, show (1 : UInt32).toNat % 32 = 1 by decide,
    Nat.shiftLeft_eq, h2, Nat.mod_eq_of_lt hlt,
    UInt32.toNat_ofNat_of_lt' hbound]
  omega

/-- `i32.shr_u` by one is a division by two. -/
private theorem shift_right_one (x : UInt32) :
    x >>> (1 : UInt32) = UInt32.ofNat (x.toNat / 2) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hx := UInt32.toNat_lt x
  have hlt : x.toNat / 2 < UInt32.size := by omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight, show (1 : UInt32).toNat % 32 = 1 by decide,
    UInt32.toNat_ofNat_of_lt' hlt, Nat.shiftRight_eq_div_pow, pow_one]

/-- The index of the double of a node. -/
private theorem index_shl_one (m : Nat) (h : 2 * m < UInt32.size) :
    UInt32.ofNat m <<< ((1 : UInt32) % 32) = UInt32.ofNat (2 * m) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hm : m < UInt32.size := by omega
  have hto : (UInt32.ofNat m).toNat = m := ofNat_toNat hm
  rw [shl_one, shift_one _ (by rw [hto]; exact h), hto]

/-- The index of the first child. -/
private theorem index_or_one (m : Nat) (h : 2 * m + 1 < UInt32.size) :
    UInt32.ofNat (2 * m) ||| 1 = UInt32.ofNat (2 * m + 1) := by
  have hs : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_or, ofNat_toNat (show 2 * m < UInt32.size by omega),
    ofNat_toNat h, show (1 : UInt32).toNat = 1 from rfl, two_mul_lor_one]

/-- The address of entry `k`.  `i32.add` puts the second operand first,
so every compiled address of this body has the index on the left. -/
private theorem index_addr (v : UInt32) (k n : Nat) (hk : k ≤ n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    UInt32.ofNat k <<< ((3 : UInt32) % 32) + v
      = v + UInt32.ofNat (8 * k) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hkn : k < UInt32.size := by omega
  have hto : (UInt32.ofNat k).toNat = k := ofNat_toNat hkn
  rw [shl_three, shift_three _ (by rw [hto]; omega), hto]
  exact UInt32.add_comm _ _

/-- Adding a small literal to an index. -/
private theorem index_add (c m : Nat) (hc : c < UInt32.size)
    (h : m + c < UInt32.size) :
    UInt32.ofNat c + UInt32.ofNat m = UInt32.ofNat (m + c) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hpow : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, ofNat_toNat hc,
    ofNat_toNat (show m < UInt32.size by omega), ofNat_toNat h, hpow]
  omega

/-- The counter step of the outer loop: `i32.const -1` is minus one. -/
private theorem index_pred (c : Nat) (h1 : 1 ≤ c)
    (h : c < UInt32.size) :
    (4294967295 : UInt32) + UInt32.ofNat c = UInt32.ofNat (c - 1) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hpow : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, ofNat_toNat h,
    ofNat_toNat (show c - 1 < UInt32.size by omega),
    show (4294967295 : UInt32).toNat = 4294967295 from rfl, hpow]
  omega

/-- The node index of the build phase. -/
private theorem index_sub (a b : UInt32) (h : b.toNat ≤ a.toNat) :
    a - b = UInt32.ofNat (a.toNat - b.toNat) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hpow : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have ha := UInt32.toNat_lt a
  have hb := UInt32.toNat_lt b
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_sub,
    ofNat_toNat (show a.toNat - b.toNat < UInt32.size by omega), hpow]
  omega

/-- Adding the literal two to an index. -/
private theorem index_add_two (m : Nat) (h : m + 2 < UInt32.size) :
    (2 : UInt32) + UInt32.ofNat m = UInt32.ofNat (m + 2) := by
  have hlit : (2 : UInt32) = UInt32.ofNat 2 := rfl
  rw [hlit]
  exact index_add 2 m (by omega) h

/-- Adding the literal one to an index. -/
private theorem index_add_one (m : Nat) (h : m + 1 < UInt32.size) :
    (1 : UInt32) + UInt32.ofNat m = UInt32.ofNat (m + 1) := by
  have hlit : (1 : UInt32) = UInt32.ofNat 1 := rfl
  rw [hlit]
  exact index_add 1 m (by omega) h

/-- Adding the literal zero to an index. -/
private theorem index_add_zero (m : Nat) (h : m < UInt32.size) :
    (0 : UInt32) + UInt32.ofNat m = UInt32.ofNat m := by
  have hlit : (0 : UInt32) = UInt32.ofNat 0 := rfl
  rw [hlit, index_add 0 m (by omega) (by omega), Nat.add_zero]

/-- The counter step, written on the value before the step. -/
private theorem index_pred_succ (i : Nat) (h : i + 1 < UInt32.size) :
    (4294967295 : UInt32) + UInt32.ofNat (i + 1) = UInt32.ofNat i := by
  rw [index_pred (i + 1) (by omega) h, Nat.add_sub_cancel]

/-- The node index of the build phase. -/
private theorem index_sub_len (i : Nat) (len : UInt32) (n : Nat)
    (hn : len.toNat = n) (hni : n ≤ i) (hi : i < UInt32.size) :
    UInt32.ofNat i - len = UInt32.ofNat (i - n) := by
  rw [index_sub _ _ (by rw [ofNat_toNat hi, hn]; exact hni),
    ofNat_toNat hi, hn]

private theorem ofNat_lt_iff {a b : Nat} (ha : a < UInt32.size)
    (hb : b < UInt32.size) :
    UInt32.ofNat a < UInt32.ofNat b ↔ a < b := by
  rw [UInt32.lt_iff_toNat_lt, ofNat_toNat ha, ofNat_toNat hb]

private theorem ofNat_le_iff {a b : Nat} (ha : a < UInt32.size)
    (hb : b < UInt32.size) :
    UInt32.ofNat a ≤ UInt32.ofNat b ↔ a ≤ b := by
  rw [UInt32.le_iff_toNat_le, ofNat_toNat ha, ofNat_toNat hb]

private theorem ofNat_ne_zero {a : Nat} (h1 : 0 < a)
    (h : a < UInt32.size) : UInt32.ofNat a ≠ 0 := by
  intro hc
  have := congrArg UInt32.toNat hc
  rw [ofNat_toNat h, show (0 : UInt32).toNat = 0 from rfl] at this
  omega

private theorem ofNat_zero : UInt32.ofNat 0 = 0 := rfl

/-! ## The model steps of one sift -/

/-- `greaterChild` below a node that has a first child. -/
private theorem greaterChild_eq (cur : List (UInt32 × UInt32))
    {bound node : Nat} (h1 : 2 * node + 1 < bound) :
    greaterChild cur bound node
      = if 2 * node + 2 < bound ∧
          keyAt cur (2 * node + 1) < keyAt cur (2 * node + 2) then
          2 * node + 2 else 2 * node + 1 := by
  rw [greaterChild, if_neg (by omega)]

/-- A node with no child below the bound answers itself. -/
private theorem greaterChild_childless (cur : List (UInt32 × UInt32))
    {bound node : Nat} (h : bound ≤ 2 * node + 1) :
    greaterChild cur bound node = node := by
  rw [greaterChild, if_pos h]

/-- One exchange of the compiled sift loop is one step of the model.
The fuel stays at `bound`, which is always enough. -/
private theorem sift_swap (cur : List (UInt32 × UInt32))
    {bound node child : Nat} (hb : 0 < bound)
    (hchild : greaterChild cur bound node = child) (hne : child ≠ node)
    (hlt : keyAt cur node < keyAt cur child) :
    siftDownAux bound cur bound node
      = siftDownAux bound (Table.swapAt cur node child) bound child := by
  have hne' : greaterChild cur bound node ≠ node := by
    rw [hchild]; exact hne
  have hc1 : 1 ≤ child := by
    obtain ⟨_, hor⟩ := greaterChild_ne_imp hne'
    rw [hchild] at hor
    rcases hor with h | h <;> omega
  obtain ⟨b, rfl⟩ : ∃ b, bound = b + 1 := ⟨bound - 1, by omega⟩
  rw [siftDownAux, hchild, if_neg hne, if_pos hlt]
  exact (siftDownAux_fuel _ _ _ (show b + 1 ≤ child + b by omega)
    (Nat.le_succ b)).symm

/-- The compiled sift stops where the model stops. -/
private theorem sift_stop (cur : List (UInt32 × UInt32))
    {bound node child : Nat}
    (hchild : greaterChild cur bound node = child)
    (hstop : ¬ keyAt cur node < keyAt cur child) :
    siftDownAux bound cur bound node = cur := by
  cases bound with
  | zero => rfl
  | succ b =>
    rw [siftDownAux, hchild]
    by_cases hcn : child = node
    · rw [if_pos hcn]
    · rw [if_neg hcn, if_neg hstop]

/-! ## The regions of the body -/

/-- The registers of the body.  Registers 0 to 2 are the parameters. -/
@[reducible] private def regs (l0 l1 l2 l3 l4 : UInt32) (l5 : UInt64)
    (l6 l7 l8 l9 l10 : UInt32) (vs : List Value) : Locals :=
  { params := [.i32 l0, .i32 l1, .i32 l2],
    locals := [.i32 l3, .i32 l4, .i64 l5, .i32 l6, .i32 l7, .i32 l8,
      .i32 l9, .i32 l10],
    values := vs }

/-- The test for a second child, WAT 8729 to 8738. -/
@[reducible] private def childBody : Program :=
  [.localGet 7, .const 2, .add, .localTee 7, .localGet 8, .ltU,
    .br_if 0, .localGet 6, .localSet 6, .br 1]

/-- The choice of the greater child, WAT 8728 to 8755. -/
@[reducible] private def pickBody : Program :=
  .block 0 0 childBody ::
    [.localGet 6, .localGet 0, .localGet 6, .const 3, .shl, .add,
      .load32 0, .localGet 0, .localGet 7, .const 3, .shl, .add,
      .load32 0, .ltU, .add, .localSet 6]

/-- One step of the sift loop, WAT 8727 to 8802. -/
@[reducible] private def siftStep : Program :=
  .block 0 0 pickBody ::
    [.localGet 0, .localGet 4, .const 3, .shl, .add, .localTee 4,
      .load32 0, .localTee 9, .localGet 0, .localGet 6, .const 3, .shl,
      .add, .localTee 7, .load32 0, .localTee 10, .geU, .br_if 1,
      .localGet 7, .localGet 9, .store32 0,
      .localGet 4, .localGet 10, .store32 0,
      .localGet 4, .load32 4, .localSet 9,
      .localGet 4, .localGet 7, .load32 4, .store32 4,
      .localGet 7, .localGet 9, .store32 4,
      .localGet 6, .localSet 4,
      .localGet 6, .const 1, .shl, .localTee 7, .const 1, .or,
      .localTee 6, .localGet 8, .ltU, .br_if 0]

/-- The bound, the childless exit and the sift loop, WAT 8710 to
8803. -/
@[reducible] private def siftBlock : Program :=
  [.localGet 4, .const 1, .shl, .localTee 7, .const 1, .or, .localTee 6,
    .localGet 1, .localGet 3, .localGet 1, .localGet 3, .ltU, .select,
    .localTee 8, .geU, .br_if 0, .loop 0 0 siftStep]

/-- The counter step and the phase test, WAT 8678 to 8689. -/
@[reducible] private def phaseIndex : Program :=
  [.localGet 3, .const 4294967295, .add, .localTee 3, .localGet 1, .ltU,
    .br_if 0, .localGet 3, .localGet 1, .sub, .localSet 4, .br 1]

/-- The phase split and the exchange of the root, WAT 8677 to 8707. -/
@[reducible] private def phaseBody : Program :=
  .block 0 0 phaseIndex ::
    [.localGet 0, .load64 0, .localSet 5, .localGet 0, .localGet 0,
      .localGet 3, .const 3, .shl, .add, .localTee 6, .load64 0,
      .store64 0, .localGet 6, .localGet 5, .store64 0, .const 0,
      .localSet 4]

/-- The back edge of the outer loop, WAT 8805 to 8806. -/
@[reducible] private def outerTail : Program :=
  [.localGet 3, .br_if 0]

/-- One step of the outer loop, WAT 8676 to 8806. -/
@[reducible] private def outerBody : Program :=
  .block 0 0 phaseBody :: .block 0 0 siftBlock :: outerTail

/-- The early exit and the whole sort, WAT 8667 to 8807. -/
@[reducible] private def guardBody : Program :=
  [.localGet 1, .const 1, .shrU, .localGet 1, .add, .localTee 3, .eqz,
    .br_if 0, .loop 0 0 outerBody]

set_option maxRecDepth 1048576 in
/-- The generated body is the one guard block. -/
private theorem func22_shape :
    Project.RustHashMap.func22 = [Instruction.block 0 0 guardBody] := rfl

private theorem func22_index :
    Project.RustHashMap.«module».funcs[22]? =
      some Project.RustHashMap.func22Def := by rfl

/-! ## One entry of the buffer -/

/-- Entry `i` of a list, with no proof that `i` is in range.  Out of
range the model reads the entry `(0, 0)`, exactly as `keyAt` does. -/
private def entryAt (ps : List (UInt32 × UInt32)) (i : Nat) :
    UInt32 × UInt32 :=
  ps.getD i (0, 0)

private theorem keyAt_entryAt (ps : List (UInt32 × UInt32)) (i : Nat) :
    keyAt ps i = (entryAt ps i).1 := rfl

private theorem entryAt_eq_getElem (ps : List (UInt32 × UInt32))
    {i : Nat} (hi : i < ps.length) : entryAt ps i = ps[i] :=
  List.getD_eq_getElem _ _ hi

private theorem set_entryAt (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : ps.set i (entryAt ps i) = ps := by
  rw [entryAt_eq_getElem ps hi, List.set_getElem_self hi]

/-! ## Address facts of one entry cell -/

/-- Move an owned word between two names of one address. -/
private theorem wordMove32 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 (α := α) 0 address value ⊢
      pointsTo_u32 0 address' value := by
  rw [haddress]

/-- Move an owned double word between two names of one address.  Copy of
`LookupProbe.lean:106`, which is private there. -/
private theorem wordMove64 {α : Type} [WasmHeapGS α]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 (α := α) 0 address value ⊢
      pointsTo_u64 0 address' value := by
  rw [haddress]

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
  have h := offset_facts (v + UInt32.ofNat (8 * k)) 0 0 rfl (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simpa using h.2.1
  · simpa using h.2.2.1
  · simpa using h.2.2.2

/-- The value cell of entry `k` of a buffer that does not wrap. -/
private theorem value_facts (v : UInt32) (k n : Nat) (hk : k < n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
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

/-! ## One memory step on one entry

The five rules below hide the cell arithmetic of one entry.  Each one
takes the buffer, does the compiled load or store, and gives the buffer
back.  Lean's eta rule for structures makes `(keyAt ps k, valAt ps k)`
the entry itself, so the rewrites below close by the same proof.
-/

private def valAt (ps : List (UInt32 × UInt32)) (i : Nat) : UInt32 :=
  (ps.getD i (0, 0)).2

private theorem valAt_entryAt (ps : List (UInt32 × UInt32)) (i : Nat) :
    valAt ps i = (entryAt ps i).2 := rfl

private theorem getElem_entryAt (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : ps[i] = entryAt ps i :=
  (entryAt_eq_getElem ps hi).symm

private theorem set_pair_self (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) :
    ps.set i ((entryAt ps i).1, (entryAt ps i).2) = ps :=
  set_entryAt ps hi

set_option maxHeartbeats 2000000 in
/-- `i32.load` of the key of entry `k`. -/
private theorem twp_key_read [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i32 (entryAt ps k).1 :: values⟩, code, arity, remainder,
            controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i32 (v + UInt32.ofNat (8 * k)) :: values⟩,
          .load32 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
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
/-- `i32.store` of the key of entry `k`. -/
private theorem twp_key_write [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v key : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v (ps.set k (key, (entryAt ps k).2)) -∗
        WP (.running ⟨⟨params, localValues, values⟩, code, arity,
            remainder, controls, calls⟩ : Expr Universal.State) @ s; E
          [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i32 key :: .i32 (v + UInt32.ofNat (8 * k)) :: values⟩,
          .store32 0 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k < ps.length := by omega
  have hfacts := cell_facts64 v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_key 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  ihave Hcell := wordMove32 (UInt32.add_zero _).symm $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store32
    (address := v + UInt32.ofNat (8 * k)) (offset := 0)
    (entryAt ps k).1 hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1
    with Hcell
  ihave Hcell := wordMove32 (UInt32.add_zero _) $$ Hcell
  ihave Hbuf := Hclose $$ %key Hcell
  isimp only [getElem_entryAt ps hkl] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i32.load offset=4` of the value of entry `k`. -/
private theorem twp_value_read [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v ps -∗
        WP (.running ⟨⟨params, localValues,
              .i32 (entryAt ps k).2 :: values⟩, code, arity, remainder,
            controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i32 (v + UInt32.ofNat (8 * k)) :: values⟩,
          .load32 4 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k < ps.length := by omega
  have hfacts := value_facts v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_value 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_load32
    (address := v + UInt32.ofNat (8 * k)) (offset := 4)
    (entryAt ps k).2 hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2
    with Hcell
  ihave Hbuf := Hclose $$ %(entryAt ps k).2 Hcell
  isimp only [getElem_entryAt ps hkl, set_pair_self ps hkl] at Hbuf
  ihave Hgo := Hcont $$ Hbuf
  iexact Hgo

set_option maxHeartbeats 2000000 in
/-- `i32.store offset=4` of the value of entry `k`. -/
private theorem twp_value_write [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {v value : UInt32} {ps : List (UInt32 × UInt32)} {k n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hk : k < n) (hlen : ps.length = n)
    (hroom : v.toNat + 8 * n < UInt32.size) :
    iprop(Table.PairSlice 0 v ps ∗
      (Table.PairSlice 0 v (ps.set k ((entryAt ps k).1, value)) -∗
        WP (.running ⟨⟨params, localValues, values⟩, code, arity,
            remainder, controls, calls⟩ : Expr Universal.State) @ s; E
          [{ Φ }])) ⊢
      WP (.running ⟨⟨params, localValues,
            .i32 value :: .i32 (v + UInt32.ofNat (8 * k)) :: values⟩,
          .store32 4 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbuf, Hcont⟩
  have hkl : k < ps.length := by omega
  have hfacts := value_facts v k n hk hroom
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_value 0 v ps hkl $$ Hbuf
  isimp only [getElem_entryAt ps hkl] at Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store32
    (address := v + UInt32.ofNat (8 * k)) (offset := 4)
    (entryAt ps k).2 hfacts.1 hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2
    with Hcell
  ihave Hbuf := Hclose $$ %value Hcell
  isimp only [getElem_entryAt ps hkl] at Hbuf
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

/-! ## The choice of the greater child -/

private theorem entryAt_set_self (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) (q : UInt32 × UInt32) :
    entryAt (ps.set i q) i = q := by
  have hi' : i < (ps.set i q).length := by rw [List.length_set]; exact hi
  rw [entryAt_eq_getElem _ hi', List.getElem_set_self]

private theorem entryAt_set_ne (ps : List (UInt32 × UInt32)) {i j : Nat}
    (h : i ≠ j) (q : UInt32 × UInt32) :
    entryAt (ps.set i q) j = entryAt ps j := by
  rw [entryAt, entryAt, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

set_option maxHeartbeats 2000000 in
/-- The choice of the greater child, WAT 8727 to 8756.  The block leaves
register 6 holding `greaterChild` and register 7 holding the second
child index.  It reads two keys and writes nothing. -/
private theorem twp_pick [WasmSmallStepGS hlc Universal.State]
    {v len env l3 l9 l10 : UInt32} {l5 : UInt64}
    {cur : List (UInt32 × UInt32)} {node bound n : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : cur.length = n) (hbn : bound ≤ n)
    (hroom : v.toNat + 8 * n < UInt32.size)
    (hchild1 : 2 * node + 1 < bound) :
    iprop(Table.PairSlice 0 v cur ∗
      (Table.PairSlice 0 v cur -∗
        WP (.running ⟨regs v len env l3 (UInt32.ofNat node) l5
              (UInt32.ofNat (greaterChild cur bound node))
              (UInt32.ofNat (2 * node + 2)) (UInt32.ofNat bound) l9 l10
              [], code, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨regs v len env l3 (UInt32.ofNat node) l5
            (UInt32.ofNat (2 * node + 1)) (UInt32.ofNat (2 * node))
            (UInt32.ofNat bound) l9 l10 [],
          .block 0 0 pickBody :: code, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hs : UInt32.size = 4294967296 := rfl
  iintro ⟨Hbuf, Hcont⟩
  simp only [pickBody, childBody, regs]
  wasm_twp_pures [twp_block twp_block twp_localGet twp_const twp_add]
  isimp only [index_add_two (2 * node) (by omega)]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  by_cases hright : 2 * node + 2 < bound
  · -- WAT 8739 to 8755: the node has a second child
    iapply Wasm.SmallStep.twp_ltU (result := 1)
      (by rw [if_pos ((ofNat_lt_iff (by omega) (by omega)).mpr hright)])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const
      twp_shl twp_add]
    isimp only [index_addr v (2 * node + 1) n (by omega) hroom]
    iapply twp_key_read (k := 2 * node + 1) (n := n) (by omega) hlen
      hroom
    isplitl_exact Hbuf
    · iintro Hbuf
      wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl
        twp_add]
      isimp only [index_addr v (2 * node + 2) n (by omega) hroom]
      iapply twp_key_read (k := 2 * node + 2) (n := n) (by omega) hlen
        hroom
      isplitl_exact Hbuf
      · iintro Hbuf
        wasm_twp_pures [twp_ltU twp_add]
        have hpick : (if (entryAt cur (2 * node + 1)).1
                < (entryAt cur (2 * node + 2)).1 then (1 : UInt32)
              else 0) + UInt32.ofNat (2 * node + 1)
            = UInt32.ofNat (greaterChild cur bound node) := by
          rw [greaterChild_eq cur hchild1]
          by_cases hk : (entryAt cur (2 * node + 1)).1
              < (entryAt cur (2 * node + 2)).1
          · rw [if_pos hk, if_pos ⟨hright, hk⟩,
              index_add_one (2 * node + 1) (by omega)]
          · rw [if_neg hk, if_neg (fun hc => hk hc.2),
              index_add_zero (2 * node + 1) (by omega)]
        isimp only [hpick]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_exitControl]
        simp only [List.take_zero, List.nil_append]
        ihave Hgo := Hcont $$ Hbuf
        iexact Hgo
  · -- WAT 8736 to 8738: the node has one child only
    iapply Wasm.SmallStep.twp_ltU (result := 0)
      (by
        rw [if_neg (fun hc =>
          hright ((ofNat_lt_iff (by omega) (by omega)).mp hc))])
    iapply Wasm.SmallStep.twp_brIfZero
    have hgc : greaterChild cur bound node = 2 * node + 1 := by
      rw [greaterChild_eq cur hchild1, if_neg (fun hc => hright hc.1)]
    isimp only [hgc] at Hcont
    wasm_twp_pures [twp_localGet]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_br rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    ihave Hgo := Hcont $$ Hbuf
    iexact Hgo

/-! ## The exchange of one sift step -/

/-- The four half stores of one sift step exchange the two entries. -/
private theorem swap_four (cur : List (UInt32 × UInt32))
    {node child : Nat} (hne : node ≠ child)
    (hn : node < cur.length) (hc : child < cur.length) :
    (((cur.set child ((entryAt cur node).1, (entryAt cur child).2)).set
        node ((entryAt cur child).1, (entryAt cur node).2)).set
        node ((entryAt cur child).1, (entryAt cur child).2)).set
        child ((entryAt cur node).1, (entryAt cur node).2)
      = Table.swapAt cur node child := by
  rw [List.set_set,
    List.set_comm _ _ (show child ≠ node from fun h => hne h.symm),
    List.set_set, Table.swapAt_eq_set_set cur hn hc,
    getElem_entryAt cur hn, getElem_entryAt cur hc]

/-! ## The sift -/

/-- Where the sift leaves the machine: at the back edge of the outer
loop, with the buffer holding the whole sift of the entry state.  Every
register that the sift writes is free. -/
private def siftExit [WasmSmallStepGS hlc Universal.State]
    (v len env l3 : UInt32) (res : List (UInt32 × UInt32))
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ r4 : UInt32, ∀ r5 : UInt64, ∀ r6 : UInt32, ∀ r7 : UInt32,
    ∀ r8 : UInt32, ∀ r9 : UInt32, ∀ r10 : UInt32,
    Table.PairSlice 0 v res -∗
    WP (.running ⟨regs v len env l3 r4 r5 r6 r7 r8 r9 r10 [],
          outerTail, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }])

set_option maxHeartbeats 2000000 in
/-- The bound, the childless exit and the sift loop, WAT 8709 to 8804.
The loop walks the node down the heap.  Its invariant is that the
remaining sift work of the buffer is the whole sift of the entry
state. -/
private theorem twp_sift [WasmSmallStepGS hlc Universal.State]
    {v len env l6 l7 l8 l9 l10 : UInt32} {l5 : UInt64}
    {ps0 : List (UInt32 × UInt32)} {node0 bound n i : Nat}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : ps0.length = n) (hn : len.toNat = n)
    (hroom : v.toNat + 8 * n < UInt32.size) (hi : i < UInt32.size)
    (hnode0 : node0 ≤ n) (hbound : bound = min n i) :
    iprop(Table.PairSlice 0 v ps0 ∗
      siftExit v len env (UInt32.ofNat i) (siftDown ps0 bound node0)
        arity remainder controls calls s E Φ) ⊢
      WP (.running ⟨regs v len env (UInt32.ofNat i)
            (UInt32.ofNat node0) l5 l6 l7 l8 l9 l10 [],
          .block 0 0 siftBlock :: outerTail, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hs : UInt32.size = 4294967296 := rfl
  have hbn : bound ≤ n := by rw [hbound]; exact Nat.min_le_left n i
  have hnsz : n < UInt32.size := by omega
  have hlenv : len = UInt32.ofNat n := by rw [← hn, UInt32.ofNat_toNat]
  iintro ⟨Hbuf, Hexit⟩
  simp only [siftBlock, regs]
  wasm_twp_pures [twp_block twp_localGet twp_const twp_shl]
  isimp only [index_shl_one node0 (by omega)]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const twp_or]
  isimp only [index_or_one node0 (by omega)]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  iapply Wasm.SmallStep.twp_ltU (result := if n < i then 1 else 0)
    (by
      rw [hlenv]
      by_cases hphase : n < i
      · rw [if_pos hphase, if_pos ((ofNat_lt_iff hnsz hi).mpr hphase)]
      · rw [if_neg hphase,
          if_neg (fun hc => hphase ((ofNat_lt_iff hnsz hi).mp hc))])
  iapply Wasm.SmallStep.twp_select
    (selected := Value.i32 (UInt32.ofNat bound))
    (by
      by_cases hphase : n < i
      · rw [if_pos hphase, if_pos (by decide : (1 : UInt32) ≠ 0), hlenv,
          hbound, Nat.min_eq_left (Nat.le_of_lt hphase)]
      · rw [if_neg hphase,
          if_neg (show ¬ ((0 : UInt32) ≠ 0) from by decide), hbound,
          Nat.min_eq_right (Nat.not_lt.mp hphase)])
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  by_cases hentry : 2 * node0 + 1 < bound
  · -- WAT 8726 to 8803: the node has a child, so the sift loop runs
    iapply Wasm.SmallStep.twp_geU (result := 0)
      (by
        rw [if_neg (fun hc =>
          absurd ((ofNat_le_iff (by omega) (by omega)).mp hc)
            (by omega))])
    iapply Wasm.SmallStep.twp_brIfZero
    iapply Wasm.SmallStep.twp_loop_wf_family
      (ι := Nat × UInt64 × UInt32 × UInt32)
      (measure := fun p => bound - p.1)
      (locals := fun p => regs v len env (UInt32.ofNat i)
        (UInt32.ofNat p.1) p.2.1 (UInt32.ofNat (2 * p.1 + 1))
        (UInt32.ofNat (2 * p.1)) (UInt32.ofNat bound) p.2.2.1 p.2.2.2 [])
      (I := fun p => iprop(
        (∃ cur : List (UInt32 × UInt32),
          ⌜cur.length = n ∧ 2 * p.1 + 1 < bound ∧
            siftDownAux bound cur bound p.1
              = siftDown ps0 bound node0⌝ ∗
          Table.PairSlice 0 v cur) ∗
        siftExit v len env (UInt32.ofNat i) (siftDown ps0 bound node0)
          arity remainder controls calls s E Φ))
      (initial := (node0, l5, l9, l10))
      (initialLocals := regs v len env (UInt32.ofNat i)
        (UInt32.ofNat node0) l5 (UInt32.ofNat (2 * node0 + 1))
        (UInt32.ofNat (2 * node0)) (UInt32.ofNat bound) l9 l10 [])
      rfl rfl
    · intro p
      obtain ⟨node, s5, s9, s10⟩ := p
      iintro Hrec ⟨Hstate, Hexit⟩
      icases Hstate with ⟨%cur, %hinv, Hbuf⟩
      obtain ⟨hcurlen, hchild1, heq⟩ := hinv
      have hnb : node < bound := by omega
      simp only [Wasm.SmallStep.loopBodyExpr, siftStep]
      iapply twp_pick hcurlen hbn hroom hchild1
      isplitl_exact Hbuf
      · iintro Hbuf
        obtain ⟨child, hchild⟩ :
            ∃ c, greaterChild cur bound node = c := ⟨_, rfl⟩
        have hcne : child ≠ node := by
          rw [← hchild]
          intro hc
          exact absurd (greaterChild_eq_imp hc) (by omega)
        have hcb : child < bound := by
          rw [← hchild]
          exact greaterChild_lt (by rw [hchild]; exact hcne)
        have hcgt : node < child := by
          rw [← hchild]
          exact greaterChild_gt (by rw [hchild]; exact hcne)
        isimp only [hchild]
        simp only [regs]
        wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl
          twp_add]
        isimp only [index_addr v node n (by omega) hroom]
        wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        iapply twp_key_read (k := node) (n := n) (by omega) hcurlen hroom
        isplitl_exact Hbuf
        · iintro Hbuf
          wasm_twp_localTee [List.set, List.length_cons,
            List.length_nil, Nat.reduceAdd, Nat.reduceSub]
          wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl
            twp_add]
          isimp only [index_addr v child n (by omega) hroom]
          wasm_twp_localTee [List.set, List.length_cons,
            List.length_nil, Nat.reduceAdd, Nat.reduceSub]
          iapply twp_key_read (k := child) (n := n) (by omega) hcurlen
            hroom
          isplitl_exact Hbuf
          · iintro Hbuf
            wasm_twp_localTee [List.set, List.length_cons,
              List.length_nil, Nat.reduceAdd, Nat.reduceSub]
            by_cases hgo : (entryAt cur node).1 < (entryAt cur child).1
            · -- WAT 8775 to 8802: the node sinks one level
              iapply Wasm.SmallStep.twp_geU (result := 0)
                (by rw [if_neg (UInt32.not_le.mpr hgo)])
              iapply Wasm.SmallStep.twp_brIfZero
              have hne' : node ≠ child := fun hc => hcne hc.symm
              have hnl : node < cur.length := by omega
              have hcl : child < cur.length := by omega
              obtain ⟨b1, hb1⟩ : ∃ l, cur.set child
                  ((entryAt cur node).1, (entryAt cur child).2) = l :=
                ⟨_, rfl⟩
              have hb1len : b1.length = n := by
                rw [← hb1, List.length_set]; exact hcurlen
              have e1v : (entryAt b1 node).2 = (entryAt cur node).2 := by
                rw [← hb1, entryAt_set_ne cur hcne]
              have e1c : entryAt b1 child
                  = ((entryAt cur node).1, (entryAt cur child).2) := by
                rw [← hb1]; exact entryAt_set_self cur hcl _
              wasm_twp_pures [twp_localGet twp_localGet]
              iapply twp_key_write (k := child) (n := n) (by omega)
                hcurlen hroom
              isplitl_exact Hbuf
              · iintro Hbuf
                isimp only [hb1] at Hbuf
                wasm_twp_pures [twp_localGet twp_localGet]
                iapply twp_key_write (k := node) (n := n) (by omega)
                  hb1len hroom
                isplitl_exact Hbuf
                · iintro Hbuf
                  isimp only [e1v] at Hbuf
                  obtain ⟨b2, hb2⟩ : ∃ l, b1.set node
                      ((entryAt cur child).1, (entryAt cur node).2)
                      = l := ⟨_, rfl⟩
                  have hb2len : b2.length = n := by
                    rw [← hb2, List.length_set]; exact hb1len
                  have e2 : entryAt b2 node
                      = ((entryAt cur child).1,
                        (entryAt cur node).2) := by
                    rw [← hb2]
                    exact entryAt_set_self b1 (by omega) _
                  have e2c : entryAt b2 child
                      = ((entryAt cur node).1,
                        (entryAt cur child).2) := by
                    rw [← hb2, entryAt_set_ne b1 hne', e1c]
                  have e2k : (entryAt b2 node).1
                      = (entryAt cur child).1 := by rw [e2]
                  have e2v : (entryAt b2 node).2
                      = (entryAt cur node).2 := by rw [e2]
                  have e2cv : (entryAt b2 child).2
                      = (entryAt cur child).2 := by rw [e2c]
                  isimp only [hb2] at Hbuf
                  wasm_twp_pures [twp_localGet]
                  iapply twp_value_read (k := node) (n := n) (by omega)
                    hb2len hroom
                  isplitl_exact Hbuf
                  · iintro Hbuf
                    isimp only [e2v]
                    wasm_twp_localSet [List.set, List.length_cons,
                      List.length_nil, Nat.reduceAdd, Nat.reduceSub]
                    wasm_twp_pures [twp_localGet twp_localGet]
                    iapply twp_value_read (k := child) (n := n)
                      (by omega) hb2len hroom
                    isplitl_exact Hbuf
                    · iintro Hbuf
                      isimp only [e2cv]
                      iapply twp_value_write (k := node) (n := n)
                        (by omega) hb2len hroom
                      isplitl_exact Hbuf
                      · iintro Hbuf
                        isimp only [e2k] at Hbuf
                        obtain ⟨b3, hb3⟩ : ∃ l, b2.set node
                            ((entryAt cur child).1,
                              (entryAt cur child).2) = l := ⟨_, rfl⟩
                        have hb3len : b3.length = n := by
                          rw [← hb3, List.length_set]; exact hb2len
                        have e3ck : (entryAt b3 child).1
                            = (entryAt cur node).1 := by
                          rw [← hb3, entryAt_set_ne b2 hne', e2c]
                        have hswap : b3.set child
                              ((entryAt cur node).1,
                                (entryAt cur node).2)
                            = Table.swapAt cur node child := by
                          rw [← hb3, ← hb2, ← hb1]
                          exact swap_four cur hne' hnl hcl
                        isimp only [hb3] at Hbuf
                        wasm_twp_pures [twp_localGet twp_localGet]
                        iapply twp_value_write (k := child) (n := n)
                          (by omega) hb3len hroom
                        isplitl_exact Hbuf
                        · iintro Hbuf
                          isimp only [e3ck, hswap] at Hbuf
                          wasm_twp_pures [twp_localGet]
                          wasm_twp_localSet [List.set, List.length_cons,
                            List.length_nil, Nat.reduceAdd,
                            Nat.reduceSub]
                          wasm_twp_pures [twp_localGet twp_const
                            twp_shl]
                          isimp only [index_shl_one child (by omega)]
                          wasm_twp_localTee [List.set,
                            List.length_cons, List.length_nil,
                            Nat.reduceAdd, Nat.reduceSub]
                          wasm_twp_pures [twp_const twp_or]
                          isimp only [index_or_one child (by omega)]
                          wasm_twp_localTee [List.set,
                            List.length_cons, List.length_nil,
                            Nat.reduceAdd, Nat.reduceSub]
                          wasm_twp_pures [twp_localGet]
                          have hstep : siftDownAux bound
                                (Table.swapAt cur node child) bound child
                              = siftDown ps0 bound node0 := by
                            rw [← sift_swap cur (by omega) hchild hcne
                              hgo]
                            exact heq
                          by_cases hback : 2 * child + 1 < bound
                          · -- WAT 8802: one more level to sink
                            iapply Wasm.SmallStep.twp_ltU (result := 1)
                              (by
                                rw [if_pos ((ofNat_lt_iff (by omega)
                                  (by omega)).mpr hback)])
                            iapply Wasm.SmallStep.twp_brIf
                              (by decide : (1 : UInt32) ≠ 0) rfl
                            simp only [List.take_zero, List.nil_append,
                              List.drop_zero]
                            ihave Hgo := Hrec
                              $$ %((child, s5, (entryAt cur node).2,
                                    (entryAt cur child).1) :
                                  Nat × UInt64 × UInt32 × UInt32)
                              %(show bound - child < bound - node by
                                  omega)
                            iapply Hgo
                            isplitl [Hbuf]
                            · iexists Table.swapAt cur node child
                              have hnext :
                                  (Table.swapAt cur node
                                      child).length = n ∧
                                    2 * child + 1 < bound ∧
                                    siftDownAux bound
                                        (Table.swapAt cur node child)
                                        bound child
                                      = siftDown ps0 bound node0 :=
                                ⟨by rw [Table.swapAt_length]
                                    exact hcurlen, hback, hstep⟩
                              isplitl_pureexact hnext
                              · iexact Hbuf
                            · iexact Hexit
                          · -- WAT 8802: the node reached the bottom
                            iapply Wasm.SmallStep.twp_ltU (result := 0)
                              (by
                                rw [if_neg (fun hc => hback
                                  ((ofNat_lt_iff (by omega)
                                    (by omega)).mp hc))])
                            iapply Wasm.SmallStep.twp_brIfZero
                            wasm_twp_pures [twp_exitControl
                              twp_exitControl]
                            simp only [List.take_zero, List.drop_zero,
                              List.append_nil]
                            have hres : Table.swapAt cur node child
                                = siftDown ps0 bound node0 := by
                              rw [← hstep]
                              exact (siftDownAux_eq_self bound _ bound
                                child (greaterChild_childless _
                                  (by omega))).symm
                            isimp only [hres] at Hbuf
                            isimp only [siftExit] at Hexit
                            ihave Hgo := Hexit
                              $$ %(UInt32.ofNat child) %s5
                              %(UInt32.ofNat (2 * child + 1))
                              %(UInt32.ofNat (2 * child))
                              %(UInt32.ofNat bound)
                              %(entryAt cur node).2
                              %(entryAt cur child).1 Hbuf
                            iexact Hgo
            · -- WAT 8774: the node is already above its greater child
              iapply Wasm.SmallStep.twp_geU (result := 1)
                (by rw [if_pos (UInt32.not_lt.mp hgo)])
              iapply Wasm.SmallStep.twp_brIf
                (by decide : (1 : UInt32) ≠ 0) rfl
              simp only [List.take_zero, List.nil_append, List.drop_zero]
              have hres : cur = siftDown ps0 bound node0 := by
                rw [← heq]
                exact (sift_stop cur hchild (by
                  rw [keyAt_entryAt, keyAt_entryAt]; exact hgo)).symm
              isimp only [hres] at Hbuf
              isimp only [siftExit] at Hexit
              ihave Hgo := Hexit $$ %(v + UInt32.ofNat (8 * node)) %s5
                %(UInt32.ofNat child) %(v + UInt32.ofNat (8 * child))
                %(UInt32.ofNat bound) %(entryAt cur node).1
                %(entryAt cur child).1 Hbuf
              iexact Hgo
    · isplitl [Hbuf]
      · iexists ps0
        have hinit : ps0.length = n ∧ 2 * node0 + 1 < bound ∧
            siftDownAux bound ps0 bound node0
              = siftDown ps0 bound node0 := by
          refine ⟨hlen, hentry, rfl⟩
        isplitl_pureexact hinit
        · iexact Hbuf
      · iexact Hexit
  · -- WAT 8725: the node has no child below the bound
    iapply Wasm.SmallStep.twp_geU (result := 1)
      (by
        rw [if_pos ((ofNat_le_iff (by omega) (by omega)).mpr
          (by omega))])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    have hres : siftDown ps0 bound node0 = ps0 :=
      siftDownAux_eq_self bound ps0 bound node0
        (greaterChild_childless ps0 (by omega))
    isimp only [siftExit, hres] at Hexit
    ihave Hgo := Hexit $$ %(UInt32.ofNat node0) %l5
      %(UInt32.ofNat (2 * node0 + 1)) %(UInt32.ofNat (2 * node0))
      %(UInt32.ofNat bound) %l9 %l10 Hbuf
    iexact Hgo

/-! ## The phase split -/

/-- The node that the merged loop sifts at counter value `i`. -/
private def phaseNode (n i : Nat) : Nat := if i < n then 0 else i - n

/-- The buffer that the merged loop sifts at counter value `i`. -/
private def phaseBuf (ps : List (UInt32 × UInt32)) (n i : Nat) :
    List (UInt32 × UInt32) :=
  if i < n then Table.swapAt ps 0 i else ps

/-- One step of the model, split the way the compiled body splits it. -/
private theorem heapsortStep_phase (ps : List (UInt32 × UInt32))
    (n i : Nat) :
    heapsortStep ps n i
      = siftDown (phaseBuf ps n i) (min n i) (phaseNode n i) := by
  by_cases h : i < n
  · rw [heapsortStep, if_neg (show ¬ (n ≤ i) by omega), phaseBuf,
      phaseNode, if_pos h, if_pos h, Nat.min_eq_right (Nat.le_of_lt h)]
  · rw [heapsortStep, if_pos (show n ≤ i by omega), phaseBuf, phaseNode,
      if_neg h, if_neg h, Nat.min_eq_left (by omega)]

set_option maxHeartbeats 2000000 in
/-- The counter step, the phase split and the exchange of the root, WAT
8676 to 8708.  The block leaves register 3 holding the new counter value
and register 4 holding the node that the sift starts from. -/
private theorem twp_phase [WasmSmallStepGS hlc Universal.State]
    {v len env l4 l6 l7 l8 l9 l10 : UInt32} {l5 : UInt64}
    {ps : List (UInt32 × UInt32)} {n i : Nat}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlen : ps.length = n) (hn : len.toNat = n)
    (hroom : v.toNat + 8 * n < UInt32.size) (hi : i + 1 < UInt32.size) :
    iprop(Table.PairSlice 0 v ps ∗
      (∀ r5 : UInt64, ∀ r6 : UInt32,
        Table.PairSlice 0 v (phaseBuf ps n i) -∗
        WP (.running ⟨regs v len env (UInt32.ofNat i)
              (UInt32.ofNat (phaseNode n i)) r5 r6 l7 l8 l9 l10 [],
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running ⟨regs v len env (UInt32.ofNat (i + 1)) l4 l5 l6 l7 l8
            l9 l10 [],
          .block 0 0 phaseBody :: code, arity, remainder, controls,
          calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  have hs : UInt32.size = 4294967296 := rfl
  have hlenv : len = UInt32.ofNat n := by rw [← hn, UInt32.ofNat_toNat]
  iintro ⟨Hbuf, Hcont⟩
  simp only [phaseBody, phaseIndex, regs]
  wasm_twp_pures [twp_block twp_block twp_localGet twp_const twp_add]
  isimp only [index_pred_succ i hi]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  isimp only [phaseBuf, phaseNode] at Hcont
  by_cases hsort : i < n
  · -- WAT 8691 to 8707: the sort phase exchanges the root with entry `i`
    isimp only [if_pos hsort] at Hcont
    iapply Wasm.SmallStep.twp_ltU (result := 1)
      (by
        rw [hlenv,
          if_pos ((ofNat_lt_iff (by omega) (by omega)).mpr hsort)])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    have hswap0 : (ps.set 0 (entryAt ps i)).set i (entryAt ps 0)
        = Table.swapAt ps 0 i := by
      rw [Table.swapAt_eq_set_set ps (by omega) (by omega),
        getElem_entryAt ps (show 0 < ps.length by omega),
        getElem_entryAt ps (show i < ps.length by omega)]
    wasm_twp_pures [twp_localGet]
    iapply twp_entry_read (k := 0) (n := n) (by omega) hlen hroom
      (by rw [Nat.mul_zero, ofNat_zero, UInt32.add_zero])
    isplitl_exact Hbuf
    · iintro Hbuf
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const
        twp_shl twp_add]
      isimp only [index_addr v i n (by omega) hroom]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply twp_entry_read (k := i) (n := n) (by omega) hlen hroom rfl
      isplitl_exact Hbuf
      · iintro Hbuf
        iapply twp_entry_write (k := 0) (n := n) (by omega) hlen hroom
          (by rw [Nat.mul_zero, ofNat_zero, UInt32.add_zero])
        isplitl_exact Hbuf
        · iintro Hbuf
          wasm_twp_pures [twp_localGet twp_localGet]
          iapply twp_entry_write (k := i) (n := n)
            (ps := ps.set 0 (entryAt ps i)) (by omega)
            (by rw [List.length_set]; exact hlen) hroom rfl
          isplitl_exact Hbuf
          · iintro Hbuf
            isimp only [hswap0] at Hbuf
            wasm_twp_pures [twp_const]
            wasm_twp_localSet [List.set, List.length_cons,
              List.length_nil, Nat.reduceAdd, Nat.reduceSub]
            wasm_twp_pures [twp_exitControl]
            simp only [List.take_zero, List.nil_append]
            isimp only [ofNat_zero] at Hcont
            ihave Hgo := Hcont $$ %(Table.pairWord (entryAt ps 0))
              %(v + UInt32.ofNat (8 * i)) Hbuf
            iexact Hgo
  · -- WAT 8685 to 8689: the build phase sifts the node `i - len`
    isimp only [if_neg hsort] at Hcont
    iapply Wasm.SmallStep.twp_ltU (result := 0)
      (by
        rw [hlenv,
          if_neg (fun hc =>
            hsort ((ofNat_lt_iff (by omega) (by omega)).mp hc))])
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet twp_localGet twp_sub]
    isimp only [index_sub_len i len n hn (by omega) (by omega)]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_br rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    ihave Hgo := Hcont $$ %l5 %l6 Hbuf
    iexact Hgo

/-! ## The body -/

/-- The top counter value of the merged loop. -/
private theorem index_add_half (len : UInt32) (n : Nat)
    (hn : len.toNat = n) (h : n + n / 2 < UInt32.size) :
    len + UInt32.ofNat (n / 2) = UInt32.ofNat (n + n / 2) := by
  have hs : UInt32.size = 4294967296 := rfl
  have hpow : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, hn, ofNat_toNat (by omega), ofNat_toNat h, hpow]
  omega

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
/-- Absolute `func 25` puts the entries in key order.  It moves the
entries only. -/
theorem func22_correct [WasmSmallStepGS hlc Universal.State] :
    Func22Spec (hlc := hlc) := by
  unfold Func22Spec CallContract callExpr
  intro v len env pairs callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, Hbuf, %hpure, Hcont⟩
  obtain ⟨hpairs, hroom⟩ := hpure
  have hs : UInt32.size = 4294967296 := rfl
  have hplen : pairs.length = len.toNat := hpairs
  have hn : len.toNat = len.toNat := rfl
  have hnsz : len.toNat < UInt32.size := UInt32.toNat_lt len
  have htop : len.toNat + len.toNat / 2 < UInt32.size := by omega
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 25
      Project.RustHashMap.func22Def (by decide) func22_index with Hmodule
  simp only [Project.RustHashMap.func22Def, Function.toLocals,
    Function.numParams, List.length_cons, List.length_nil, List.take,
    List.drop, List.reverse_cons, List.reverse_nil, List.map,
    List.nil_append, List.cons_append, ValueType.zero, func22_shape,
    Nat.reduceAdd]
  simp only [guardBody]
  wasm_twp_pures [twp_block twp_localGet twp_const twp_shrU]
  isimp only [shr_one, shift_right_one len]
  wasm_twp_pures [twp_localGet twp_add]
  isimp only [index_add_half len len.toNat rfl htop]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  by_cases hempty : len.toNat = 0
  · -- WAT 8674: an empty buffer leaves the block at once
    have hzero : len.toNat + len.toNat / 2 = 0 := by omega
    iapply Wasm.SmallStep.twp_eqz (result := 1)
      (by rw [if_pos (by rw [hzero, ofNat_zero])])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
    simp only [List.take_zero, List.nil_append, List.drop_zero]
    wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
      with Hmodule
    simp only [List.take, List.nil_append]
    iclose_map_runtime Hruntime with Hmodule Henv
    isimp only [SortPostFrameless] at Hcont
    have hnil : pairs = [] :=
      List.eq_nil_of_length_eq_zero (by rw [hplen, hempty])
    have hsorted : Table.SortedByKey pairs := by
      rw [hnil]; exact Table.SortedByKey.nil
    ihave Hgo := Hcont $$ %pairs Hruntime Hbuf
      %(⟨List.Perm.refl pairs, hsorted⟩ :
        pairs.Perm pairs ∧ Table.SortedByKey pairs)
    isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
    iexact Hgo
  · -- WAT 8675 to 8807: the merged loop
    iapply Wasm.SmallStep.twp_eqz (result := 0)
      (by
        rw [if_neg (ofNat_ne_zero (by omega) htop)])
    iapply Wasm.SmallStep.twp_brIfZero
    iapply Wasm.SmallStep.twp_loop_wf_family
      (ι := Nat × UInt32 × UInt64 × UInt32 × UInt32 × UInt32 × UInt32 ×
        UInt32)
      (measure := fun p => p.1)
      (locals := fun p => regs v len env (UInt32.ofNat p.1) p.2.1
        p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1
        p.2.2.2.2.2.2.2 [])
      (I := fun p => iprop(
        ⌜1 ≤ p.1 ∧ p.1 ≤ len.toNat + len.toNat / 2⌝ ∗
        Table.PairSlice 0 v (heapsortUpto pairs len.toNat p.1) ∗
        runtimeModuleOwn ⟨0⟩ Project.RustHashMap.«module» ∗
        hostEnvOwn 0 (Universal.envFor Project.RustHashMap.«module») ∗
        SortPostFrameless v pairs callerLocals stack code arity
          remainder controls calls s E Φ))
      (initial := (len.toNat + len.toNat / 2, 0, 0, 0, 0, 0, 0, 0))
      (initialLocals := regs v len env
        (UInt32.ofNat (len.toNat + len.toNat / 2)) 0 0 0 0 0 0 0 [])
      rfl rfl
    · intro p
      obtain ⟨c, r4, r5, r6, r7, r8, r9, r10⟩ := p
      iintro Hrec ⟨%hinv, Hbuf, Hmodule, Henv, Hcont⟩
      obtain ⟨hc1, hctop⟩ := hinv
      replace hc1 : 1 ≤ c := hc1
      replace hctop : c ≤ len.toNat + len.toNat / 2 := hctop
      obtain ⟨i, rfl⟩ : ∃ i, c = i + 1 := ⟨c - 1, by omega⟩
      have hupto : (heapsortUpto pairs len.toNat (i + 1)).length
          = len.toNat := by rw [heapsortUpto_length]; exact hplen
      simp only [Wasm.SmallStep.loopBodyExpr, outerBody]
      iapply twp_phase (n := len.toNat) (i := i)
        (ps := heapsortUpto pairs len.toNat (i + 1)) hupto rfl hroom
        (by omega)
      isplitl [Hbuf]
      · iexact Hbuf
      · iintro %q5 %q6 Hbuf
        iapply twp_sift (n := len.toNat) (i := i)
          (node0 := phaseNode len.toNat i)
          (bound := min len.toNat i)
          (ps0 := phaseBuf (heapsortUpto pairs len.toNat (i + 1))
            len.toNat i)
          (by
            rw [phaseBuf]
            split
            · rw [Table.swapAt_length]; exact hupto
            · exact hupto)
          rfl hroom (by omega)
          (by rw [phaseNode]; split <;> omega) rfl
        isplitl [Hbuf]
        · iexact Hbuf
        · isimp only [siftExit]
          iintro %t4 %t5 %t6 %t7 %t8 %t9 %t10 Hbuf
          have hstep : siftDown
                (phaseBuf (heapsortUpto pairs len.toNat (i + 1))
                  len.toNat i)
                (min len.toNat i) (phaseNode len.toNat i)
              = heapsortUpto pairs len.toNat i := by
            rw [← heapsortStep_phase,
              ← heapsortUpto_succ pairs len.toNat i (by omega)]
          isimp only [hstep] at Hbuf
          simp only [outerTail, regs]
          wasm_twp_pures [twp_localGet]
          by_cases hlast : i = 0
          · -- WAT 8806: the counter reached zero
            subst hlast
            isimp only [ofNat_zero]
            iapply Wasm.SmallStep.twp_brIfZero
            wasm_twp_pures [twp_exitControl twp_exitControl]
            simp only [List.take_zero, List.nil_append, List.drop_zero]
            wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
              with Hmodule
            simp only [List.take, List.nil_append]
            iclose_map_runtime Hruntime with Hmodule Henv
            isimp only [SortPostFrameless] at Hcont
            have hfin : heapsortUpto pairs len.toNat 0
                = heapsortModel pairs := by
              rw [← hplen]; exact heapsortUpto_zero pairs
            isimp only [hfin] at Hbuf
            ihave Hgo := Hcont $$ %(heapsortModel pairs) Hruntime Hbuf
              %(⟨heapsortModel_perm pairs, heapsortModel_sorted pairs⟩ :
                (heapsortModel pairs).Perm pairs ∧
                  Table.SortedByKey (heapsortModel pairs))
            isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
            iexact Hgo
          · -- WAT 8806: one more step of the merged loop
            iapply Wasm.SmallStep.twp_brIf
              (ofNat_ne_zero (by omega) (by omega)) rfl
            simp only [List.take_zero, List.nil_append, List.drop_zero]
            ihave Hgo := Hrec
              $$ %((i, t4, t5, t6, t7, t8, t9, t10) :
                  Nat × UInt32 × UInt64 × UInt32 × UInt32 × UInt32 ×
                    UInt32 × UInt32)
              %(show i < i + 1 by omega)
            iapply Hgo
            isplitl_pureexact (⟨by omega, by omega⟩ :
              1 ≤ i ∧ i ≤ len.toNat + len.toNat / 2)
            · isplitl [Hbuf]
              · iexact Hbuf
              · iframe Hmodule Henv Hcont
    · isplitl_pureexact (⟨by omega, Nat.le_refl _⟩ :
        1 ≤ len.toNat + len.toNat / 2 ∧
          len.toNat + len.toNat / 2 ≤ len.toNat + len.toNat / 2)
      · isplitl [Hbuf]
        · isimp only [heapsortUpto_top pairs len.toNat]
          iexact Hbuf
        · iframe Hmodule Henv Hcont

end Project.RustHashMap.Func22Proof
