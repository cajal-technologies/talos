import Project.RustHashMap.MapOpContracts
import Project.RustHashMap.LookupProbe
import CodeLib.RustStd.HashMap.EraseWasm
import CodeLib.RustStd.HashMap.CtrlWrite

/-!
# Proof of the `remove` kernel of the map

Absolute `func 11` is `HashMap::remove`, WAT lines 1925 to 2285 of
`programs/rust/build/rust_hash_map/program.wat`.  This module composes the
regions of the body into `MapOpContracts.Func8Spec`.

* The mask read, WAT 1927 to 1929.  Register 3 takes `bucket_mask`.
* The inline hash, WAT 1930 to 2103.  It is the same 174 instructions as
  the hash of absolute `func 20` under the same register names, so this
  module reuses the program `LookupHash.func17Hash` and repeats the
  stepping script for a body with one more register.
* The probe loop, WAT 2104 to 2188.  It is the loop of absolute `func 20`
  with two changes: the walk keeps the bucket index in register 13 and the
  bucket base in register 14, and the miss arm clears register 13.
* The erase, WAT 2189 to 2261.  It reads the group at the bucket and the
  group one width below it, decides `DELETED` against `EMPTY`, writes the
  control byte and its mirror, moves the two counters and reads the value.
* The tail, WAT 2263 to 2284.  It writes the `Option<u32>` at `out` and
  copies the whole 32-byte map value to `out + 8`.

## There is no item guard

Absolute `func 12` and absolute `func 20` both start with a guard on the
item count.  Absolute `func 11` has none, so the static singleton runs the
hash and the probe loop as well.  Its one group is eight `EMPTY` bytes, so
the loop leaves through the miss arm on the first window.

## The register map

Fifteen registers.  Register 0 is the output slot, register 1 the map
value, register 2 the key and then the address of the control byte,
register 3 the bucket mask, register 4 the match mask, register 5 the tag
lanes, register 6 the group word, registers 7 to 9 dead, register 10 the
probe position and then the control byte to write, register 11 the control
pointer and then the address of the mirror group, register 12 the stride,
register 13 the bucket index and then the discriminant, and register 14
the bucket base and then the value.
-/

namespace Project.RustHashMap.Func8Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.LookupPures
open Project.RustHashMap.LookupHash
open Project.RustHashMap.LookupProbe
open Project.RustHashMap.MapOpContracts
open scoped Wasm.SmallStep.Outcome

/-! ## The shape of the body -/

/-- The walk over the match mask, WAT 2133 to 2162. -/
@[reducible] private def func8WalkBody : Program :=
  [.localGet 2, .localGet 11, .localGet 4, .ctzI64, .wrapI64, .const 3,
    .shrU, .localGet 10, .add, .localGet 3, .and, .localTee 13, .const 3,
    .shl, .sub, .localTee 14, .const 4294967288, .add, .load32 0, .eq,
    .br_if 3, .localGet 4, .constI64 18446744073709551615, .addI64,
    .localGet 4, .andI64, .localTee 4, .eqzI64, .eqz, .br_if 0]

/-- The body of the probe loop, WAT 2112 to 2186. -/
@[reducible] private def func8LoopBody : Program :=
  [.block 0 0
      [.localGet 11, .localGet 10, .add, .load64 0, .localTee 6,
        .localGet 5, .xorI64, .localTee 4,
        .constI64 18446744073709551615, .xorI64, .localGet 4,
        .constI64 18374403900871474943, .addI64, .andI64,
        .constI64 9259542123273814144, .andI64, .localTee 4, .eqzI64,
        .br_if 0, .loop 0 0 func8WalkBody],
    .const 0, .localSet 13, .localGet 6, .localGet 6, .constI64 1,
    .shlI64, .andI64, .constI64 9259542123273814144, .andI64, .eqzI64,
    .eqz, .br_if 2, .localGet 10, .localGet 12, .const 8, .add,
    .localTee 12, .add, .localGet 3, .and, .localSet 10, .br 0]

/-- The probe loop with its block, WAT 2109 to 2188. -/
@[reducible] private def func8Probe : Program :=
  [.block 0 0 [.loop 0 0 func8LoopBody]]

/-- The block that decides `DELETED` against `EMPTY`, WAT 2192 to 2239. -/
@[reducible] private def func8EraseTest : Program :=
  [.localGet 11, .localGet 13, .add, .localTee 2, .load64 0, .localTee 4,
    .localGet 4, .constI64 1, .shlI64, .andI64,
    .constI64 9259542123273814144, .andI64, .ctzI64, .wrapI64, .const 3,
    .shrU, .localGet 11, .localGet 13, .const 4294967288, .add,
    .localGet 3, .and, .add, .localTee 11, .load64 0, .localTee 4,
    .localGet 4, .constI64 1, .shlI64, .andI64,
    .constI64 9259542123273814144, .andI64, .clzI64, .wrapI64, .const 3,
    .shrU, .add, .const 7, .gtU, .br_if 0, .localGet 1, .localGet 1,
    .load32 8, .const 1, .add, .store32 8, .const 255, .localSet 10]

/-- The erase, WAT 2189 to 2261. -/
@[reducible] private def func8Erase : Program :=
  [.const 128, .localSet 10, .block 0 0 func8EraseTest,
    .localGet 2, .localGet 10, .store8 0, .localGet 11, .const 8, .add,
    .localGet 10, .store8 0, .localGet 1, .localGet 1, .load32 12,
    .const 4294967295, .add, .store32 12, .localGet 14,
    .const 4294967292, .add, .load32 0, .localSet 14, .const 1,
    .localSet 13]

/-- The answer, WAT 2263 to 2284. -/
@[reducible] private def func8Tail : Program :=
  [.localGet 0, .localGet 14, .store32 4, .localGet 0, .localGet 13,
    .store32 0, .localGet 0, .localGet 1, .load64 24, .store64 32,
    .localGet 0, .localGet 1, .load64 16, .store64 24, .localGet 0,
    .localGet 1, .load64 8, .store64 16, .localGet 0, .localGet 1,
    .load64 0, .store64 8]

set_option maxRecDepth 1048576 in
/-- The mask read, the inline hash, the probe loop with the erase inside
one block, and the answer. -/
private theorem func8_body_shape :
    Project.RustHashMap.func8 =
      ([Instruction.localGet 1, .load32 4, .localTee 3] ++ func17Hash ++
        [Instruction.localGet 1, .load32 0, .localSet 11, .const 0,
          .localSet 12,
          .block 0 0 (Instruction.block 0 0 [.loop 0 0 func8LoopBody]
            :: func8Erase)])
      ++ func8Tail := rfl

/-! ## The two bridges that the flat hash term needs

Private copies of `LookupHash.lean:44` and `LookupHash.lean:57`. -/

/-- The `i64.extend_i32_u` of the key, as the model writes it. -/
private theorem ofNat_toNat_toUInt64 (x : UInt32) :
    UInt64.ofNat x.toNat = x.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64,
    UInt64.toNat_ofNat_of_lt' (by
      have h := x.toNat_lt
      change x.toNat < 18446744073709551616
      omega)]

/-- The compiled hash and the model hash have the same low word. -/
private theorem toUInt32_hashU32Low (k0 k1 : UInt64) (key : UInt32) :
    (SipHash.hashU32Low k0 k1 key).toUInt32
      = (SipHash.hashU32 k0 k1 key).toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32]
  exact (Table.h1_hashU32Low k0 k1 key).symm

/-! ## The inline hash -/

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
/-- The inline hash of `remove`, WAT lines 1930 to 2103.  It is the same
program as the hash of absolute `func 20`, and the body has one more
register, so the script repeats.  Register 4 takes the compiled hash,
register 5 takes the tag lanes and register 10 takes the start position.
Registers 6 to 9 keep values that no later instruction reads. -/
private theorem twp_func8_hash [WasmSmallStepGS hlc Universal.State]
    (out map key mask : UInt32) (k0 k1 : UInt64)
    (l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hmap : map.toNat + 32 < UInt32.size) :
    iprop(
      pointsTo_u64 0 (map + 16) k0 ∗
      pointsTo_u64 0 (map + 24) k1 ∗
      (∀ (w6 w7 w8 w9 : UInt64),
        pointsTo_u64 0 (map + 16) k0 -∗
        pointsTo_u64 0 (map + 24) k1 -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 map, .i32 key],
                [l3, .i64 (SipHash.hashU32Low k0 k1 key),
                  .i64 (Table.repeatByte
                    (Table.h2 (SipHash.hashU32 k0 k1 key))),
                  .i64 w6, .i64 w7, .i64 w8, .i64 w9,
                  .i32 (mask &&& (SipHash.hashU32 k0 k1 key).toUInt32),
                  l11, l12, l13, l14],
                stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 map, .i32 key],
              [l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13,
                l14],
              .i32 mask :: stack⟩,
            func17Hash ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hk0, Hk1, Hcont⟩
  have hka0 := offset_facts64 map 16 16 rfl (by omega)
  have hka1 := offset_facts64 map 24 24 rfl (by omega)
  simp only [func17Hash, List.cons_append, List.nil_append]

  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := map)
    (offset := 24) k1
    hka1.1 hka1.2.1 hka1.2.2.1 hka1.2.2.2.1 hka1.2.2.2.2.1
    hka1.2.2.2.2.2.1 hka1.2.2.2.2.2.2.1 hka1.2.2.2.2.2.2.2 with Hk1
  wasm_twp_pures [twp_localTee twp_localGet twp_extendUI32 twp_localTee
    twp_xorI64 twp_constI64 twp_xorI64 twp_localTee twp_constI64 twp_rotlI64
    twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := map)
    (offset := 16) k0
    hka0.1 hka0.2.1 hka0.2.2.1 hka0.2.2.2.1 hka0.2.2.2.2.1
    hka0.2.2.2.2.2.1 hka0.2.2.2.2.2.2.1 hka0.2.2.2.2.2.2.2 with Hk0
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_xorI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_xorI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_orI64 twp_xorI64 twp_localGet
    twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_constI64 twp_xorI64
    twp_localGet twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_constI64
    twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64 twp_constI64 twp_rotlI64 twp_xorI64 twp_localGet
    twp_localGet twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_shrUI64 twp_xorI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  -- the flat term is the compiled hash of the key
  have hflat : SipHash.hashU32Low k0 k1 key = inlineHash k0 k1 key :=
    (inlineHash_eq_hashU32Low k0 k1 key).symm
  simp only [inlineHash, compressWasm, roundWasm1, roundWasm2,
    finalWasm] at hflat
  isimp only [ofNat_toNat_toUInt64, rotlWasm13, rotlWasm16, rotlWasm17,
    rotlWasm21, rotlWasm32, shrU64Wasm32, ← hflat]
  -- the mask, the wrap and the tag lanes
  have htag : ((SipHash.hashU32Low k0 k1 key >>> 25) &&& 127) *
      72340172838076673
      = Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)) := by
    rw [show (72340172838076673 : UInt64) = Table.REP01 from rfl,
      Table.repeatByte_h2_of_wasm, Table.h2_hashU32Low]
  wasm_twp_pures [twp_wrapI64 twp_and]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_shrUI64 twp_constI64
    twp_andI64 twp_constI64 twp_mulI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  isimp only [wrapWasm, toUInt32_hashU32Low, shrU64Wasm25, htag]
  iapply Hcont $$ Hk0 Hk1


/-! ## Private copies from the lookup probe

`Project.RustHashMap.LookupProbe` keeps these four private. -/

/-- The index of the probe-loop family.  Copy of `LookupProbe.lean:83`. -/
private structure LookupIdx where
  step : Nat
  pos : UInt32
  stride : UInt32
  wmask : UInt64
  wgroup : UInt64

/-- The invariant of the probe loop.  Copy of `LookupProbe.lean:93`. -/
private def lookupInv (t : Table UInt32 UInt32) (h : UInt64) (key : UInt32)
    (N : Nat) (i : LookupIdx) : Prop :=
  i.step ≤ N ∧
  i.pos = UInt32.ofNat (Table.probeSeq t h i.step).pos ∧
  i.stride = UInt32.ofNat (8 * i.step) ∧
  ∀ m, m < i.step →
    Table.matchEmpty (Table.window t h m) = false ∧
    (Table.matchTag (Table.h2 h) (Table.window t h m)).find?
        (fun j => t.keyIs (Table.probeIdx t h m j) key) = none

/-- Move an owned double word between two names of one address.  Copy of
`LookupProbe.lean:107`. -/
private theorem wordMove64 [WasmSmallStepGS hlc Universal.State]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 0 address value ⊢ pointsTo_u64 0 address' value := by
  rw [haddress]

/-- `Group::match_empty` in the operand order of the compiled test.  Copy
of `LookupProbe.lean:120`. -/
private theorem swarMatchEmpty_wasm (x : UInt64) :
    (x &&& (x <<< 1)) &&& 9259542123273814144 = Table.swarMatchEmpty x :=
  rfl

/-- The walk covers every window up to `N`.  Copy of
`LookupProbe.lean:126`. -/
private theorem find_none_of_inv {t : Table UInt32 UInt32} {h : UInt64}
    {key : UInt32} {N : Nat} {i : LookupIdx}
    (hN : N < Table.probeFuel t)
    (hNmin : ∀ m, m < N → Table.matchEmpty (Table.window t h m) = false)
    (hinv : lookupInv t h key N i)
    (hcur : Table.matchEmpty (Table.window t h i.step) = true)
    (hfind : (Table.matchTag (Table.h2 h) (Table.window t h i.step)).find?
        (fun j => t.keyIs (Table.probeIdx t h i.step j) key) = none) :
    Table.find t h key = none := by
  obtain ⟨hstep, -, -, hhist⟩ := hinv
  have hEq : i.step = N := by
    rcases Nat.lt_or_ge i.step N with hlt | hge
    · rw [hNmin i.step hlt] at hcur
      exact absurd hcur (by decide)
    · omega
  subst hEq
  refine find_none_of_walk t h key i.step hN hcur (fun m hm => ?_)
  rcases Nat.lt_or_ge m i.step with hlt | hge
  · exact (hhist m hlt).2
  · have hme : m = i.step := by omega
    subst hme
    exact hfind

/-- The next stride register, as a number.  Copy of
`LookupProbe.lean:151`. -/
private theorem stride_step (n : Nat) (hn : 8 * n < UInt32.size) :
    (8 : UInt32) + UInt32.ofNat (8 * n) = UInt32.ofNat (8 * (n + 1)) := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
    show (8 : UInt32).toNat = 8 from rfl]
  have hlt : 8 * n % UInt32.size = 8 * n := Nat.mod_eq_of_lt hn
  change (8 + 8 * n % 4294967296) % 4294967296 = 8 * (n + 1) % 4294967296
  omega

/-! ## The probe loop -/

/-- The registers of `remove` inside the probe loop. -/
@[reducible] private def func8Locals (out map key ctrl : UInt32)
    (t : Table UInt32 UInt32) (wmask splat wgroup w7 w8 w9 : UInt64)
    (pos stride v13 v14 : UInt32) : Locals :=
  { params := [.i32 out, .i32 map, .i32 key],
    locals := [.i32 (UInt32.ofNat (t.buckets - 1)), .i64 wmask, .i64 splat,
      .i64 wgroup, .i64 w7, .i64 w8, .i64 w9, .i32 pos, .i32 ctrl,
      .i32 stride, .i32 v13, .i32 v14],
    values := [] }

/-- Where the walk of WAT 2130 to 2163 leaves the machine.  With no match
it leaves the block of WAT 2112, with register 4 at zero.  With a match it
leaves the block of WAT 2110, with register 13 at the bucket and register
14 at the bucket base. -/
private def func8WalkExit (out map key ctrl : UInt32)
    (t : Table UInt32 UInt32) (splat wgroup w7 w8 w9 : UInt64) (P : Nat)
    (stride : UInt32)
    (noneCode : Program) (noneControls : List ControlFrame)
    (noneValues : List Value)
    (hitCode : Program) (hitControls : List ControlFrame)
    (hitValues : List Value) (arity : Nat) (remainder : List Value)
    (calls : List CallFrame) (r : Option Nat) (q : UInt64)
    (v13 v14 : UInt32) : Expr Universal.State :=
  match r with
  | none =>
      .running ⟨{ func8Locals out map key ctrl t 0 splat wgroup w7 w8 w9
            (UInt32.ofNat P) stride v13 v14 with values := noneValues },
          noneCode, arity, remainder, noneControls, calls⟩
  | some j =>
      .running ⟨{ func8Locals out map key ctrl t q splat wgroup w7 w8 w9
            (UInt32.ofNat P) stride
            (UInt32.ofNat ((P + j) % t.buckets))
            (ctrl - (UInt32.ofNat ((P + j) % t.buckets) <<<
              (3 : UInt32))) with values := hitValues },
          hitCode, arity, remainder, hitControls, calls⟩

set_option maxHeartbeats 2000000 in
/-- The walk over the match mask of `remove`, WAT 2130 to 2163.  It reads
one key for each set byte of the mask.  With a match it leaves the block
of WAT 2110 through the branch of WAT 2153. -/
private theorem twp_func8_walk [WasmSmallStepGS hlc Universal.State]
    {out map key ctrl stride v13 v14 : UInt32}
    {splat wgroup w7 w8 w9 : UInt64}
    {t : Table UInt32 UInt32} {hashf : UInt32 → UInt64}
    {m P : Nat} {msk : UInt64}
    {arity : Nat} {remainder : List Value}
    {b3 : ControlFrame} {rest : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    {noneCode : Program} {noneControls : List ControlFrame}
    {noneValues : List Value}
    {hitCode : Program} {hitControls : List ControlFrame}
    {hitValues : List Value}
    (hlayout : Table.Layout hashf t)
    (hm32 : m ≤ 32) (hbShape : t.buckets = 2 ^ m)
    (hP : P < t.buckets) (hroom : 8 * t.buckets ≤ ctrl.toNat)
    (hb3Kind : b3.kind = ControlKind.block)
    (hnoneTarget : branchTarget? arity 0 (b3 :: rest) ([] : List Value) =
      some (noneCode, noneControls, noneValues))
    (hhitTarget : ∀ wf : ControlFrame,
      branchTarget? arity 3 (wf :: b3 :: rest) ([] : List Value) =
        some (hitCode, hitControls, hitValues))
    (hmsk : msk &&& Table.REP80 = msk)
    (hfull : ∀ j ∈ Table.setBytes msk,
      (t.slotAt ((P + j) % t.buckets)).isSome = true) :
    iprop(
      Table.slotsBefore 0 ctrl t.slots ∗
      (∀ (r : Option Nat) (q : UInt64) (u13 u14 : UInt32),
        ⌜(Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) = r⌝ -∗
        Table.slotsBefore 0 ctrl t.slots -∗
        WP (func8WalkExit out map key ctrl t splat wgroup w7 w8 w9 P stride
              noneCode noneControls noneValues hitCode hitControls
              hitValues arity remainder calls r q u13 u14)
          @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨{ func8Locals out map key ctrl t msk splat wgroup w7 w8 w9
              (UInt32.ofNat P) stride v13 v14 with
              values := [Value.i64 msk] },
            [Instruction.eqzI64, Instruction.br_if 0,
              Instruction.loop 0 0 func8WalkBody], arity, remainder,
            b3 :: rest, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hslots, Hexit⟩
  have hnone3 : noneCode = b3.continuation ∧ noneControls = rest ∧
      noneValues = b3.belowStack := by
    have hplain : branchTarget? arity 0 (b3 :: rest) ([] : List Value) =
        some (b3.continuation, rest, b3.belowStack) := by
      simp [branchTarget?, hb3Kind]
    have h := Option.some.inj (hnoneTarget.symm.trans hplain)
    simp only [Prod.mk.injEq] at h
    exact h
  by_cases hmne : msk = 0
  · subst hmne
    iapply Wasm.SmallStep.twp_eqzI64 (result := 1) (by rw [if_pos rfl])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) hnoneTarget
    have hnone0 : (Table.setBytes (0 : UInt64)).find?
        (fun j => t.keyIs ((P + j) % t.buckets) key) = none := by
      rw [show Table.setBytes (0 : UInt64) = [] from by decide]
      rfl
    ihave Hgo := Hexit $$ %(none : Option Nat) %(0 : UInt64) %v13 %v14
      %hnone0 Hslots
    isimp only [func8WalkExit] at Hgo
    iexact Hgo
  iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hmne])
  iapply Wasm.SmallStep.twp_brIfZero
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := UInt64 × UInt32 × UInt32)
    (measure := fun p => (Table.setBytes p.1).length)
    (locals := fun p => func8Locals out map key ctrl t p.1 splat wgroup
      w7 w8 w9 (UInt32.ofNat P) stride p.2.1 p.2.2)
    (I := fun p => iprop(
      ⌜p.1 &&& Table.REP80 = p.1 ∧ p.1 ≠ 0 ∧
        (∀ j, Table.hasBit p.1 j = true → Table.hasBit msk j = true) ∧
        (Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) =
          (Table.setBytes p.1).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key)⌝ ∗
      Table.slotsBefore 0 ctrl t.slots ∗
      (∀ (r : Option Nat) (q : UInt64) (u13 u14 : UInt32),
        ⌜(Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) = r⌝ -∗
        Table.slotsBefore 0 ctrl t.slots -∗
        WP (func8WalkExit out map key ctrl t splat wgroup w7 w8 w9 P stride
              noneCode noneControls noneValues hitCode hitControls
              hitValues arity remainder calls r q u13 u14)
          @ s; E [{ Φ }])))
    (initial := (msk, v13, v14))
    (initialLocals := { func8Locals out map key ctrl t msk splat wgroup
      w7 w8 w9 (UInt32.ofNat P) stride v13 v14 with values := [] })
    rfl rfl
  · intro p
    iintro Hrec ⟨%hq, Hslots, Hexit⟩
    obtain ⟨hqmask, hqne, hqsub, hqfind⟩ := hq
    simp only [Wasm.SmallStep.loopBodyExpr, func8WalkBody, func8Locals]
    have hlow : Table.lowestSetByte p.1 = some (ctz64 64 p.1 / 8) :=
      Table.lowestSetByte_eq_ctz hqmask hqne
    have hnext : Table.setBytes p.1 =
        ctz64 64 p.1 / 8 ::
          Table.setBytes (p.1 &&& (p.1 + 18446744073709551615)) :=
      Table.setBytes_iterNext hqmask hlow
    have hidx := Table.matchIndex_of_wasm t hm32 hbShape hqmask hlow P
    have hbpos : 0 < t.buckets := hlayout.pos
    have hctrlLt : ctrl.toNat < 4294967296 := ctrl.toBitVec.isLt
    have hsize32 : UInt32.size = 4294967296 := rfl
    have hsz : (8 : Nat) * t.buckets ≤ ctrl.toNat := hroom
    have hIlt : (P + ctz64 64 p.1 / 8) % t.buckets < t.buckets :=
      Nat.mod_lt _ hbpos
    have hIlen : (P + ctz64 64 p.1 / 8) % t.buckets < t.slots.length := by
      rw [hlayout.slots_len]; exact hIlt
    have hidxEq : (UInt32.ofNat P +
        (UInt64.ofNat (ctz64 64 p.1)).toUInt32 >>> 3) &&&
        UInt32.ofNat (t.buckets - 1)
        = UInt32.ofNat ((P + ctz64 64 p.1 / 8) % t.buckets) := by
      rw [UInt32.add_comm, ← hidx, UInt32.ofNat_toNat]
    have hbaddrNat :
        (Table.bucketAddr ctrl ((P + ctz64 64 p.1 / 8) % t.buckets)).toNat
          = ctrl.toNat - 8 * ((P + ctz64 64 p.1 / 8) % t.buckets + 1) :=
      Table.bucketAddr_toNat ctrl hIlt hroom
    have haddr : (4294967288 : UInt32) +
        (ctrl - (UInt32.ofNat ((P + ctz64 64 p.1 / 8) % t.buckets) <<< 3))
        = Table.bucketAddr ctrl ((P + ctz64 64 p.1 / 8) % t.buckets) := by
      rw [UInt32.add_comm, Table.bucketAddr_of_wasm,
        UInt32.toNat_ofNat_of_lt'
          (by omega : (P + ctz64 64 p.1 / 8) % t.buckets < UInt32.size)]
      rfl
    obtain ⟨ha1, ha2, ha3⟩ := addr3
      (Table.bucketAddr ctrl ((P + ctz64 64 p.1 / 8) % t.buckets))
      (by omega)
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_ctzI64
      twp_wrapI64 twp_const twp_shrU twp_localGet twp_add twp_localGet
      twp_and]
    isimp only [wrapWasm, shrU32Wasm3, hidxEq]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_const twp_shl twp_sub]
    isimp only [shl32Wasm3]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_const twp_add]
    isimp only [haddr]
    have hj0q : ctz64 64 p.1 / 8 ∈ Table.setBytes p.1 := by
      rw [hnext]; exact List.mem_cons_self
    have hj0msk : ctz64 64 p.1 / 8 ∈ Table.setBytes msk := by
      simp only [Table.setBytes, List.mem_filter, List.mem_range] at hj0q ⊢
      exact ⟨hj0q.1, hqsub _ hj0q.2⟩
    have hslotSome := hfull _ hj0msk
    obtain ⟨k', v', hslotEq⟩ :
        ∃ k' v', t.slotAt ((P + ctz64 64 p.1 / 8) % t.buckets)
          = some (k', v') := by
      cases hc : t.slotAt ((P + ctz64 64 p.1 / 8) % t.buckets) with
      | none => rw [hc] at hslotSome; exact absurd hslotSome (by decide)
      | some kv => exact ⟨kv.1, kv.2, rfl⟩
    have hslotsGet :
        t.slots[(P + ctz64 64 p.1 / 8) % t.buckets]'hIlen
          = some (k', v') := by
      rw [← hslotEq, Table.slotAt, List.getD_eq_getElem]
    ihave ⟨Hpre, Hcell, Hpost⟩ :=
      (Table.slotsBefore_focus 0 ctrl t.slots hIlen).mp $$ Hslots
    isimp only [hslotsGet, Table.slotCell] at Hcell
    ihave ⟨Hkey, Hval⟩ := Hcell
    wasm_twp_rebind Wasm.SmallStep.twp_load32_addr k' ha1 ha2 ha3 with Hkey
    wasm_twp_pures [twp_eq]
    ihave Hslots : Table.slotsBefore 0 ctrl t.slots $$
      [Hpre Hkey Hval Hpost]
    · iapply (Table.slotsBefore_focus 0 ctrl t.slots hIlen).mpr
      isimp only [hslotsGet, Table.slotCell]
      iframe Hpre Hkey Hval Hpost
    by_cases hkey : key = k'
    · have hkeyIs :
          t.keyIs ((P + ctz64 64 p.1 / 8) % t.buckets) key = true := by
        simp only [Table.keyIs, hslotEq, beq_iff_eq]
        exact hkey.symm
      have hfindq : (Table.setBytes p.1).find?
          (fun j => t.keyIs ((P + j) % t.buckets) key)
            = some (ctz64 64 p.1 / 8) := by
        rw [hnext]
        exact List.find?_cons_of_pos (by simpa using hkeyIs)
      isimp only [if_pos hkey]
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
        (hhitTarget _)
      ihave Hgo := Hexit $$ %(some (ctz64 64 p.1 / 8)) %p.1
        %(UInt32.ofNat ((P + ctz64 64 p.1 / 8) % t.buckets))
        %(ctrl - (UInt32.ofNat
          ((P + ctz64 64 p.1 / 8) % t.buckets) <<< (3 : UInt32)))
        %(hqfind.trans hfindq) Hslots
      isimp only [func8WalkExit] at Hgo
      iexact Hgo
    · have hkeyIs :
          t.keyIs ((P + ctz64 64 p.1 / 8) % t.buckets) key = false := by
        simp only [Table.keyIs, hslotEq, beq_eq_false_iff_ne, ne_eq]
        exact fun h => hkey h.symm
      have hfindq : (Table.setBytes p.1).find?
          (fun j => t.keyIs ((P + j) % t.buckets) key) =
            (Table.setBytes (p.1 &&& (p.1 + 18446744073709551615))).find?
              (fun j => t.keyIs ((P + j) % t.buckets) key) := by
        rw [hnext, List.find?_cons_of_neg (by simpa using hkeyIs)]
      have hcomm : (p.1 + 18446744073709551615) &&& p.1
          = p.1 &&& (p.1 + 18446744073709551615) := UInt64.and_comm _ _
      have hnextMask :
          (p.1 &&& (p.1 + 18446744073709551615)) &&& Table.REP80
            = p.1 &&& (p.1 + 18446744073709551615) := by
        rw [UInt64.and_assoc, UInt64.and_comm (p.1 + 18446744073709551615),
          ← UInt64.and_assoc, hqmask]
      have hnextSub : ∀ j,
          Table.hasBit (p.1 &&& (p.1 + 18446744073709551615)) j = true →
            Table.hasBit msk j = true := by
        intro j hj
        rw [Table.hasBit_iterNext hqmask hlow j, Bool.and_eq_true] at hj
        exact hqsub _ hj.1
      isimp only [if_neg hkey]
      iapply Wasm.SmallStep.twp_brIfZero
      wasm_twp_pures [twp_localGet twp_constI64 twp_addI64 twp_localGet
        twp_andI64]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      isimp only [hcomm]
      by_cases hzero : p.1 &&& (p.1 + 18446744073709551615) = 0
      · iapply Wasm.SmallStep.twp_eqzI64 (result := 1) (by rw [if_pos hzero])
        iapply Wasm.SmallStep.twp_eqz (result := 0) (by decide)
        iapply Wasm.SmallStep.twp_brIfZero
        iapply Wasm.SmallStep.twp_exitControl (by decide)
        isimp only [List.take_zero, List.drop_zero, List.nil_append]
        iapply Wasm.SmallStep.twp_exitControl (by rw [hb3Kind]; rfl)
        isimp only [List.take_nil, List.nil_append]
        isimp only [hzero]
        have hsetZero : Table.setBytes 0 = [] := by decide
        have hnone : (Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) = none := by
          rw [hqfind, hfindq, hzero, hsetZero]
          rfl
        ihave Hgo := Hexit $$ %(none : Option Nat) %(0 : UInt64)
          %(UInt32.ofNat ((P + ctz64 64 p.1 / 8) % t.buckets))
          %(ctrl - (UInt32.ofNat
            ((P + ctz64 64 p.1 / 8) % t.buckets) <<< (3 : UInt32)))
          %hnone Hslots
        isimp only [func8WalkExit, func8Locals, hnone3.1, hnone3.2.1,
          hnone3.2.2] at Hgo
        iexact Hgo
      · iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hzero])
        iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
          (by rfl)
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        ihave Hback := Hrec $$
          %((p.1 &&& (p.1 + 18446744073709551615),
            UInt32.ofNat ((P + ctz64 64 p.1 / 8) % t.buckets),
            ctrl - (UInt32.ofNat
              ((P + ctz64 64 p.1 / 8) % t.buckets) <<< (3 : UInt32)))
            : UInt64 × UInt32 × UInt32)
          %(show (Table.setBytes
              (p.1 &&& (p.1 + 18446744073709551615))).length
                < (Table.setBytes p.1).length by rw [hnext]; simp)
        iapply Hback
        isplitl_pureexact (show
          (p.1 &&& (p.1 + 18446744073709551615)) &&& Table.REP80
              = p.1 &&& (p.1 + 18446744073709551615) ∧
            p.1 &&& (p.1 + 18446744073709551615) ≠ 0 ∧
            (∀ j, Table.hasBit
                (p.1 &&& (p.1 + 18446744073709551615)) j = true →
              Table.hasBit msk j = true) ∧
            (Table.setBytes msk).find?
                (fun j => t.keyIs ((P + j) % t.buckets) key) =
              (Table.setBytes
                (p.1 &&& (p.1 + 18446744073709551615))).find?
                (fun j => t.keyIs ((P + j) % t.buckets) key) from
          ⟨hnextMask, hzero, hnextSub, hqfind.trans hfindq⟩)
        iframe Hslots Hexit
  · isplitl_pureexact (show
      msk &&& Table.REP80 = msk ∧ msk ≠ 0 ∧
        (∀ j, Table.hasBit msk j = true → Table.hasBit msk j = true) ∧
        (Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) =
          (Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) from
      ⟨hmsk, hmne, fun _ h => h, rfl⟩)
    iframe Hslots Hexit


set_option maxHeartbeats 2000000 in
/-- The probe loop of `remove`, WAT 2109 to 2188.  The theorem starts at
the block of WAT 2110 and ends at one of the two exits.  The hit exit
leaves that block with register 13 at the bucket and register 14 at the
bucket base.  The miss exit leaves the block of WAT 2109 with register 13
at zero. -/
private theorem twp_func8_probe [WasmSmallStepGS hlc Universal.State]
    (out map key ctrl : UInt32) (k0 k1 : UInt64) (t : Table UInt32 UInt32)
    (w6 w7 w8 w9 : UInt64) (l13 l14 : UInt32)
    {cont : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {missCode : Program} {missControls : List ControlFrame}
    {missValues : List Value}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hwf : Table.WF (SipHash.hashU32 k0 k1) t) (hclean : Table.Clean t)
    (hmiss : ∀ f g : ControlFrame,
      branchTarget? arity 2 (f :: g :: controls) ([] : List Value) =
        some (missCode, missControls, missValues)) :
    iprop(
      Table.TableBody 0 map ctrl t ∗
      (∀ (i : Nat) (wmask wgroup : UInt64) (pos stride : UInt32),
        ⌜i < t.buckets ∧
          Table.find t (SipHash.hashU32 k0 k1 key) key = some i⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running
            ⟨func8Locals out map key ctrl t wmask
                (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
                wgroup w7 w8 w9 pos stride (UInt32.ofNat i)
                (ctrl - (UInt32.ofNat i <<< (3 : UInt32))),
              cont, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }]) ∗
      (∀ (wmask wgroup : UInt64) (pos stride u14 : UInt32),
        ⌜Table.find t (SipHash.hashU32 k0 k1 key) key = none⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running
            ⟨{ func8Locals out map key ctrl t wmask
                  (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
                  wgroup w7 w8 w9 pos stride 0 u14 with
                values := missValues },
              missCode, arity, remainder, missControls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 map, .i32 key],
              [.i32 (UInt32.ofNat (t.buckets - 1)),
                .i64 (SipHash.hashU32Low k0 k1 key),
                .i64 (Table.repeatByte
                  (Table.h2 (SipHash.hashU32 k0 k1 key))),
                .i64 w6, .i64 w7, .i64 w8, .i64 w9,
                .i32 (UInt32.ofNat (t.buckets - 1) &&&
                  (SipHash.hashU32 k0 k1 key).toUInt32),
                .i32 ctrl, .i32 0, .i32 l13, .i32 l14],
              []⟩,
            func8Probe ++ cont, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbody, Hhit, Hmiss⟩
  have hlayout : Table.Layout (SipHash.hashU32 k0 k1) t := hwf.toLayout
  obtain ⟨m, hm32, hmne, hbShape⟩ := hlayout.shape
  obtain ⟨N, hNfuel, hNempty, hNmin⟩ :=
    exists_first_empty_window_of_clean hwf hclean (SipHash.hashU32 k0 k1 key)
  have hNemp' : Table.matchEmpty (Table.groupAt t
      (Table.probeSeq t (SipHash.hashU32 k0 k1 key) N).pos) = true := hNempty
  have hprobe : UInt32.ofNat (t.buckets - 1) &&&
      (SipHash.hashU32 k0 k1 key).toUInt32
      = UInt32.ofNat
          (Table.probeStart t (SipHash.hashU32 k0 k1 key)).pos := by
    rw [UInt32.and_comm, ← Table.probeStart_pos_of_wasm t hm32 hbShape,
      UInt32.ofNat_toNat]
  simp only [func8Probe, List.cons_append, List.nil_append]
  isimp only [hprobe]
  wasm_twp_pures [twp_block]
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := LookupIdx × UInt32 × UInt32)
    (measure := fun i => N - i.1.step)
    (locals := fun i =>
      func8Locals out map key ctrl t i.1.wmask
        (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
        i.1.wgroup w7 w8 w9 i.1.pos i.1.stride i.2.1 i.2.2)
    (I := fun i => iprop(
      ⌜lookupInv t (SipHash.hashU32 k0 k1 key) key N i.1⌝ ∗
      Table.TableBody 0 map ctrl t ∗
      (∀ (i : Nat) (wmask wgroup : UInt64) (pos stride : UInt32),
        ⌜i < t.buckets ∧
          Table.find t (SipHash.hashU32 k0 k1 key) key = some i⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running
            ⟨func8Locals out map key ctrl t wmask
                (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
                wgroup w7 w8 w9 pos stride (UInt32.ofNat i)
                (ctrl - (UInt32.ofNat i <<< (3 : UInt32))),
              cont, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }]) ∗
      (∀ (wmask wgroup : UInt64) (pos stride u14 : UInt32),
        ⌜Table.find t (SipHash.hashU32 k0 k1 key) key = none⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running
            ⟨{ func8Locals out map key ctrl t wmask
                  (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
                  wgroup w7 w8 w9 pos stride 0 u14 with
                values := missValues },
              missCode, arity, remainder, missControls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])))
    (initial := (⟨0, UInt32.ofNat
        (Table.probeStart t (SipHash.hashU32 k0 k1 key)).pos, 0,
      SipHash.hashU32Low k0 k1 key, w6⟩, l13, l14))
    (initialLocals :=
      { params := [Value.i32 out, Value.i32 map, Value.i32 key],
        locals :=
          [Value.i32 (UInt32.ofNat (t.buckets - 1)),
            Value.i64 (SipHash.hashU32Low k0 k1 key),
            Value.i64 (Table.repeatByte
              (Table.h2 (SipHash.hashU32 k0 k1 key))),
            Value.i64 w6, Value.i64 w7, Value.i64 w8, Value.i64 w9,
            Value.i32 (UInt32.ofNat
              (Table.probeStart t (SipHash.hashU32 k0 k1 key)).pos),
            Value.i32 ctrl, Value.i32 0, .i32 l13, .i32 l14],
        values := [] })
    rfl rfl
  · intro i
    iintro Hrec ⟨%hinv, Hbody, Hhit, Hmiss⟩
    obtain ⟨histep, hipos, histride, hihist⟩ := hinv
    have hposLt :
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos
          < t.buckets := hlayout.probe_lt _ _
    simp only [Wasm.SmallStep.loopBodyExpr, func8LoopBody, func8Locals]
    ihave ⟨%hctrlB2, Hheader,
        ⟨Hpre, ⟨%hgbound, Hgroup⟩, Hpost⟩, Hslots⟩ :=
      (Table.TableBody_groupAt 0 map ctrl t hlayout hposLt).mp $$ Hbody
    have hgroupAddr : ctrl + UInt32.ofNat
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos
          = i.1.pos + ctrl + 0 := by
      rw [UInt32.add_zero, hipos, UInt32.add_comm]
    have hgf := FrameCells.offset_facts64 (i.1.pos + ctrl) 0 0 rfl
      (by rw [← UInt32.add_zero (i.1.pos + ctrl), ← hgroupAddr]; omega)
    ihave Hgroup := wordMove64 hgroupAddr $$ Hgroup
    wasm_twp_pures [twp_block twp_localGet twp_localGet twp_add]
    wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := i.1.pos + ctrl)
      (offset := 0)
      (Table.groupWord (Table.groupAt t
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos))
      hgf.1 hgf.2.1 hgf.2.2.1 hgf.2.2.2.1 hgf.2.2.2.2.1
      hgf.2.2.2.2.2.1 hgf.2.2.2.2.2.2.1 hgf.2.2.2.2.2.2.2 with Hgroup
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_xorI64]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_constI64 twp_xorI64 twp_localGet twp_constI64
      twp_addI64 twp_andI64 twp_constI64 twp_andI64]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    isimp only [swarMatchTag_wasm, hipos]
    iapply twp_func8_walk (hashf := SipHash.hashU32 k0 k1) (m := m)
      (out := out) (map := map) (key := key) (ctrl := ctrl) (t := t)
      (splat := Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
      (wgroup := Table.groupWord (Table.groupAt t
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos))
      (w7 := w7) (w8 := w8) (w9 := w9) (stride := i.1.stride)
      (v13 := i.2.1) (v14 := i.2.2)
      (P := (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos)
      (msk := Table.swarMatchTag (Table.h2 (SipHash.hashU32 k0 k1 key))
        (Table.groupWord (Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos)))
      (hitCode := cont) (hitControls := controls) (hitValues := [])
    case hlayout => exact hlayout
    case hm32 => exact hm32
    case hbShape => exact hbShape
    case hP => exact hposLt
    case hroom => exact hctrlB2
    case hb3Kind => rfl
    case hnoneTarget => rfl
    case hhitTarget => intro wf; rfl
    case hmsk => exact Table.swarMatchTag_and_REP80 _ _
    case hfull =>
      exact fun j hj =>
        slotAt_isSome_of_mem_matchTag hlayout _ i.1.step hj
    isplitl_exacts [Hslots]
    iintro %r %q %u13 %u14 %hfind Hslots
    have hctrlLen :
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos + 8
          ≤ t.ctrl.length := by rw [hlayout.ctrl_len]; omega
    ihave Hctrl : Slices.ByteSlice 0 ctrl t.ctrl $$ [Hpre Hgroup Hpost]
    · iapply (Table.ByteSlice_groupAt 0 ctrl t hctrlLen).mpr
      isplitl [Hpre]
      · iexact Hpre
      · isplitl [Hgroup]
        · isplitl_pureexact hgbound
          iapply wordMove64 hgroupAddr.symm
          iexact Hgroup
        · iexact Hpost
    ihave Hbody : Table.TableBody 0 map ctrl t $$
      [Hheader Hctrl Hslots]
    · isimp only [Table.TableBody]
      isplitl_pureexact hctrlB2
      iframe Hheader Hctrl Hslots
    cases r with
    | some j =>
      simp only [func8WalkExit]
      have hmodelFind : (Table.matchTag
          (Table.h2 (SipHash.hashU32 k0 k1 key))
          (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
              i.1.step).pos)).find?
            (fun j => t.keyIs
              (((Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                i.1.step).pos + j) % t.buckets) key) = some j :=
        (hlayout.find?_setBytes_eq hposLt key).symm.trans hfind
      obtain ⟨v, hslot⟩ :=
        (Table.keyIs_iff t _ key).mp (Table.tagFind_some hmodelFind).2.2
      have hbpos : 0 < t.buckets := hlayout.pos
      have hjLt :
          ((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos + j)
            % t.buckets < t.buckets := Nat.mod_lt _ hbpos
      have hfindSome :
          Table.find t (SipHash.hashU32 k0 k1 key) key
            = some (((Table.probeSeq t (SipHash.hashU32 k0 k1 key)
              i.1.step).pos + j) % t.buckets) :=
        hlayout.find_of_slot hjLt hslot
      ihave Hgo := Hhit
        $$ %(((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos
              + j) % t.buckets)
        %q
        %(Table.groupWord (Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos))
        %(UInt32.ofNat
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos)
        %i.1.stride %⟨hjLt, hfindSome⟩ Hbody
      iexact Hgo
    | none =>
      simp only [func8WalkExit]
      have hmodelFind : (Table.matchTag
          (Table.h2 (SipHash.hashU32 k0 k1 key))
          (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
              i.1.step).pos)).find?
            (fun j => t.keyIs
              (((Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                i.1.step).pos + j) % t.buckets) key) = none :=
        (hlayout.find?_setBytes_eq hposLt key).symm.trans hfind
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      have hg8 : (Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
            i.1.step).pos).length = 8 := Table.groupAt_length t _
      have hctrls : ∀ b ∈ Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos,
            Table.IsCtrl b := hlayout.isCtrl_groupAt hclean hposLt
      wasm_twp_pures [twp_const]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_localGet twp_constI64 twp_shlI64
        twp_andI64 twp_constI64 twp_andI64]
      isimp only [shl64Wasm1, swarMatchEmpty_wasm]
      by_cases hemp : Table.matchEmpty (Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos)
            = true
      · have hne0 : Table.swarMatchEmpty (Table.groupWord (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos))
              ≠ 0 := by
          intro hc
          rw [(Table.swarMatchEmpty_eq_zero_iff hg8 hctrls).mp hc] at hemp
          exact absurd hemp (by decide)
        iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hne0])
        iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
          (hmiss _ _)
        have hfindNone : Table.find t (SipHash.hashU32 k0 k1 key) key
            = none :=
          find_none_of_inv hNfuel hNmin
            ⟨histep, hipos, histride, hihist⟩ hemp hmodelFind
        ihave Hgo := Hmiss $$ %(0 : UInt64)
          %(Table.groupWord (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos))
          %(UInt32.ofNat
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos)
          %i.1.stride %u14 %hfindNone Hbody
        iexact Hgo
      · rw [Bool.not_eq_true] at hemp
        have hzero : Table.swarMatchEmpty (Table.groupWord (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos))
              = 0 := (Table.swarMatchEmpty_eq_zero_iff hg8 hctrls).mpr hemp
        have hstepLt : i.1.step < N := by
          rcases Nat.eq_or_lt_of_le histep with heq | hlt
          · rw [heq] at hemp
            rw [hNemp'] at hemp
            exact absurd hemp (by decide)
          · exact hlt
        have hclt : ctrl.toNat < 4294967296 := ctrl.toBitVec.isLt
        have hsize32 : UInt32.size = 4294967296 := rfl
        have hsz : (8 : Nat) * t.buckets ≤ ctrl.toNat := hctrlB2
        have hfuelEq : Table.probeFuel t = t.buckets / 8 + 1 := rfl
        have hstrideB : 8 * (i.1.step + 1) < UInt32.size := by
          change 8 * (i.1.step + 1) < 4294967296
          omega
        have hnextStride : (8 : UInt32) + i.1.stride
            = UInt32.ofNat (8 * (i.1.step + 1)) := by
          rw [histride]
          exact stride_step i.1.step (by omega)
        have hstrideSum : UInt32.ofNat
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).stride
              + 8 = UInt32.ofNat (8 * (i.1.step + 1)) := by
          rw [probeSeq_stride, UInt32.add_comm]
          exact stride_step i.1.step (by omega)
        have hnextPos : (UInt32.ofNat (8 * (i.1.step + 1)) +
            UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
              i.1.step).pos) &&& UInt32.ofNat (t.buckets - 1)
            = UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                (i.1.step + 1)).pos := by
          rw [UInt32.add_comm, ← hstrideSum,
            show Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                (i.1.step + 1)
              = (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                  i.1.step).next t from rfl,
            ← Table.probeNext_pos_of_wasm t hm32 hbShape, UInt32.ofNat_toNat]
        iapply Wasm.SmallStep.twp_eqzI64 (result := 1) (by rw [if_pos hzero])
        iapply Wasm.SmallStep.twp_eqz (result := 0) (by decide)
        iapply Wasm.SmallStep.twp_brIfZero
        wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
        wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_add twp_localGet twp_and]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        isimp only [hnextStride, hnextPos]
        iapply Wasm.SmallStep.twp_br (by rfl)
        simp only [List.take_zero, List.nil_append]
        ihave Hback := Hrec $$
          %((⟨i.1.step + 1,
              UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                (i.1.step + 1)).pos,
              UInt32.ofNat (8 * (i.1.step + 1)), 0,
              Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                  i.1.step).pos)⟩, 0, u14)
            : LookupIdx × UInt32 × UInt32)
          %(show N - (i.1.step + 1) < N - i.1.step by omega)
        iapply Hback
        have hnextInv : lookupInv t (SipHash.hashU32 k0 k1 key) key N
            ⟨i.1.step + 1,
              UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                (i.1.step + 1)).pos,
              UInt32.ofNat (8 * (i.1.step + 1)), 0,
              Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                  i.1.step).pos)⟩ := by
          refine ⟨show i.1.step + 1 ≤ N by omega, rfl, rfl, ?_⟩
          intro mm hmm
          have hmm' : mm < i.1.step + 1 := hmm
          rcases Nat.lt_or_ge mm i.1.step with hlt | hge
          · exact hihist mm hlt
          · have hme : mm = i.1.step := by omega
            subst hme
            exact ⟨hemp, hmodelFind⟩
        isplitl_pureexact hnextInv
        iframe Hbody Hhit Hmiss
  · isplitl_pureexact (⟨Nat.zero_le _, rfl, rfl, by
      intro mm hmm
      exact absurd hmm (Nat.not_lt_zero mm)⟩ :
      lookupInv t (SipHash.hashU32 k0 k1 key) key N
        ⟨0, UInt32.ofNat
            (Table.probeStart t (SipHash.hashU32 k0 k1 key)).pos, 0,
          SipHash.hashU32Low k0 k1 key, w6⟩)
    iframe Hbody Hhit Hmiss


/-! ## The bit counts and the small word bridges of the erase -/

/-- The interpreter never reports more than 64 trailing clear bits. -/
private theorem ctz64_le : ∀ (k : Nat) (a : UInt64), ctz64 k a ≤ 64
  | 0, _ => Nat.le_refl 64
  | k + 1, a => by
      rw [ctz64]
      split
      · omega
      · exact ctz64_le k _

/-- The interpreter never reports more than 64 leading clear bits. -/
private theorem clz64_le : ∀ (k : Nat) (a : UInt64), clz64 k a ≤ 64
  | 0, _ => Nat.le_refl 64
  | k + 1, a => by
      rw [clz64]
      split
      · omega
      · exact clz64_le k _

/-- `i64.ctz` or `i64.clz` wrapped to `i32` and shifted by three is the
byte count that `BitMask` reports. -/
private theorem shrU3_ofNat (c : Nat) (hc : c ≤ 64) :
    (UInt64.ofNat c).toUInt32 >>> (3 : UInt32) = UInt32.ofNat (c / 8) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight, UInt64.toNat_toUInt32, UInt64.toNat_ofNat',
    show (3 : UInt32).toNat % 32 = 3 from rfl, Nat.shiftRight_eq_div_pow,
    UInt32.toNat_ofNat']
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have h3 : (2 : Nat) ^ 3 = 8 := by norm_num
  rw [h64, h32, h3]
  omega

/-- The two byte counts add without a wrap, and the compiled test is the
model test. -/
private theorem sum_gt_seven (a b : Nat) (ha : a ≤ 8) (hb : b ≤ 8) :
    (if UInt32.ofNat a + UInt32.ofNat b > 7 then (1 : UInt32) else 0)
      = if 8 ≤ a + b then 1 else 0 := by
  have hsum : (UInt32.ofNat a + UInt32.ofNat b).toNat = a + b := by
    rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat']
    change (a % 4294967296 + b % 4294967296) % 4294967296 = a + b
    omega
  have h7 : (7 : UInt32).toNat = 7 := rfl
  by_cases hge : 8 ≤ a + b
  · rw [if_pos hge, if_pos]
    rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hsum, h7]
    omega
  · rw [if_neg hge, if_neg]
    rw [gt_iff_lt, UInt32.lt_iff_toNat_lt, hsum, h7]
    omega

/-- `x + (-1)` on a word is one less, with no wrap. -/
private theorem addNegOne (n : Nat) (h1 : 1 ≤ n) (h2 : n < UInt32.size) :
    (4294967295 : UInt32) + UInt32.ofNat n = UInt32.ofNat (n - 1) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    show (4294967295 : UInt32).toNat = 4294967295 from rfl]
  change (4294967295 + n % 4294967296) % 4294967296 = (n - 1) % 4294967296
  change n < 4294967296 at h2
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (by omega : n - 1 < 4294967296)]
  omega

/-- `1 + x` on a word is one more, with no wrap. -/
private theorem oneAdd (n : Nat) (h2 : n + 1 < UInt32.size) :
    (1 : UInt32) + UInt32.ofNat n = UInt32.ofNat (n + 1) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    show (1 : UInt32).toNat = 1 from rfl]
  change n + 1 < 4294967296 at h2
  change (1 + n % 4294967296) % 4294967296 = (n + 1) % 4294967296
  rw [Nat.mod_eq_of_lt (by omega : n < 4294967296),
    Nat.mod_eq_of_lt (by omega : n + 1 < 4294967296)]
  omega

/-- The byte at index `i` of an owned range, with the wand that writes a
new byte back. -/
private theorem ByteSlice_focus_byte {α : Type} [WasmHeapGS α]
    (memId : Nat) (ptr : UInt32) (bytes : List UInt8) {i : Nat}
    (hi : i < bytes.length) (c : UInt8) :
    Slices.ByteSlice (α := α) memId ptr bytes ⊢
      iprop(⌜(ptr + UInt32.ofNat i).toNat + 1 < UInt32.size⌝ ∗
        (⟨memId, ptr + UInt32.ofNat i⟩ ↦w bytes.getD i 0) ∗
        ((⟨memId, ptr + UInt32.ofNat i⟩ ↦w c) -∗
          Slices.ByteSlice memId ptr (bytes.set i c))) := by
  have hbyte : (bytes.drop i).take 1 = [bytes.getD i 0] := by
    rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.take_zero,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  have hwin :=
    (Table.ByteSlice_window (α := α) memId ptr bytes i 1 (by omega)).mp
  rw [hbyte] at hwin
  iintro Hslice
  ihave ⟨Hleft, Hmid, Hright⟩ := hwin $$ Hslice
  ihave ⟨%hb, Hcell⟩ :=
    (Slices.ByteSlice_singleton memId (ptr + UInt32.ofNat i)
      (bytes.getD i 0)).mp $$ Hmid
  isplitl_pureexact hb
  isplitl [Hcell]
  · iexact Hcell
  · iintro Hnew
    iapply (Table.ByteSlice_set memId ptr bytes hi c).mpr
    isplitl [Hleft]
    · iexact Hleft
    · isplitl [Hnew]
      · isplitl_pureexact hb
        iexact Hnew
      · iexact Hright


/-- The mirror address that `set_ctrl` writes, in the operand order the
compiled code leaves on the stack. -/
private theorem mirror_addr (ctrl : UInt32) (b i : Nat) :
    (8 : UInt32) + (UInt32.ofNat (Table.wrapSub i 8 b) + ctrl)
      = ctrl + UInt32.ofNat (Table.index2 b i) := by
  rw [Table.index2, UInt32.ofNat_add,
    show (UInt32.ofNat 8 : UInt32) = 8 from rfl, ← UInt32.add_assoc,
    UInt32.add_comm (8 + UInt32.ofNat (Table.wrapSub i 8 b)) ctrl,
    UInt32.add_comm (8 : UInt32) (UInt32.ofNat (Table.wrapSub i 8 b))]

/-- The backward window of the erase, as the compiled code names it. -/
private theorem before_addr_of_wasm (t : Table UInt32 UInt32)
    (hs : Table.Shape t.buckets) {i : Nat} (hi : i < t.buckets) :
    (4294967288 + UInt32.ofNat i) &&& UInt32.ofNat (t.buckets - 1)
      = UInt32.ofNat (Table.wrapSub i 8 t.buckets) := by
  rw [negEightAdd, ← Table.wrapSub_of_wasm hs hi, UInt32.ofNat_toNat]

set_option maxHeartbeats 2000000 in
/-- The two control-byte stores, the item count and the value read, WAT
2241 to 2261.  Register 10 already holds the byte to write and the header
already holds the new `growth_left`. -/
private theorem twp_func8_erase_writes [WasmSmallStepGS hlc Universal.State]
    {out map key ctrl : UInt32} {t : Table UInt32 UInt32}
    {hashf : UInt32 → UInt64}
    {m4 splat g6 w7 w8 w9 : UInt64} {stride cw : UInt32}
    {i gl : Nat} {v : UInt32} {c : UInt8} {cont : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlayout : Table.Layout hashf t)
    (hi : i < t.buckets) (hslot : t.slotAt i = some (key, v))
    (hmap : map.toNat + 32 < UInt32.size)
    (hroom : 8 * t.buckets ≤ ctrl.toNat)
    (hitems : 1 ≤ t.items) (hitemsLt : t.items < UInt32.size)
    (hbyte : cw.toUInt8 = c) :
    iprop(
      Table.tableHeader 0 map ctrl (UInt32.ofNat (t.buckets - 1))
        (UInt32.ofNat gl) (UInt32.ofNat t.items) ∗
      Slices.ByteSlice 0 ctrl t.ctrl ∗
      Table.slotsBefore 0 ctrl t.slots ∗
      (∀ (c2 c11 : UInt32),
        Table.tableHeader 0 map ctrl (UInt32.ofNat (t.buckets - 1))
          (UInt32.ofNat gl) (UInt32.ofNat (t.items - 1)) -∗
        Slices.ByteSlice 0 ctrl
          ((t.ctrl.set i c).set (Table.index2 t.buckets i) c) -∗
        Table.slotsBefore 0 ctrl (t.slots.set i none) -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 map, .i32 c2],
                [.i32 (UInt32.ofNat (t.buckets - 1)), .i64 m4, .i64 splat,
                  .i64 g6, .i64 w7, .i64 w8, .i64 w9, .i32 cw, .i32 c11,
                  .i32 stride, .i32 1, .i32 v], []⟩,
              cont, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 map, .i32 (UInt32.ofNat i + ctrl)],
              [.i32 (UInt32.ofNat (t.buckets - 1)), .i64 m4, .i64 splat,
                .i64 g6, .i64 w7, .i64 w8, .i64 w9, .i32 cw,
                .i32 (UInt32.ofNat (Table.wrapSub i 8 t.buckets) + ctrl),
                .i32 stride, .i32 (UInt32.ofNat i),
                .i32 (ctrl - (UInt32.ofNat i <<< (3 : UInt32)))], []⟩,
            Instruction.localGet 2 :: .localGet 10 :: .store8 0 ::
              .localGet 11 :: .const 8 :: .add :: .localGet 10 ::
              .store8 0 :: .localGet 1 :: .localGet 1 :: .load32 12 ::
              .const 4294967295 :: .add :: .store32 12 :: .localGet 14 ::
              .const 4294967292 :: .add :: .load32 0 :: .localSet 14 ::
              .const 1 :: .localSet 13 :: cont,
            arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hheader, Hctrl, Hslots, Hcont⟩
  have hbpos : 0 < t.buckets := hlayout.pos
  have hclen : t.ctrl.length = t.buckets + 8 := hlayout.ctrl_len
  have hslen : t.slots.length = t.buckets := hlayout.slots_len
  have hiCtrl : i < t.ctrl.length := by omega
  have hbefore : Table.wrapSub i 8 t.buckets < t.buckets :=
    Nat.mod_lt _ hbpos
  have hi2lt : Table.index2 t.buckets i < t.ctrl.length := by
    unfold Table.index2
    omega
  have hi2set : Table.index2 t.buckets i < (t.ctrl.set i c).length := by
    rw [List.length_set]; exact hi2lt
  have hiSlots : i < t.slots.length := by omega
  have hctrlLt := UInt32.toNat_lt ctrl
  have hbucketNat := Table.bucketAddr_toNat ctrl hi hroom
  have hslotRoom : (Table.bucketAddr ctrl i).toNat + 8 ≤ UInt32.size := by
    simp only [UInt32.size] at *
    omega
  have hslotStep : (Table.bucketAddr ctrl i + 4).toNat
      = (Table.bucketAddr ctrl i).toNat + 4 := by
    simpa using Slices.byteOffset_toNat (Table.bucketAddr ctrl i) 4
      (by omega)
  have hh12 := FrameCells.offset_facts map 12 12 rfl (by omega)
  isimp only [Table.tableHeader] at Hheader
  icases Hheader with ⟨H0, H4, H8, H12⟩
  -- the control byte at the bucket
  wasm_twp_pures [twp_localGet twp_localGet]
    rewriting [UInt32.add_comm (UInt32.ofNat i) ctrl]
  ihave ⟨%hb1, Hbyte, Hclose⟩ :=
    ByteSlice_focus_byte 0 ctrl t.ctrl hiCtrl c $$ Hctrl
  wasm_twp_rebind twp_store8_addr_gen (t.ctrl.getD i 0) with Hbyte
  isimp only [hbyte] at Hbyte
  ihave Hctrl := Hclose $$ Hbyte
  -- the control byte at the mirror
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet]
    rewriting [mirror_addr ctrl t.buckets i]
  ihave ⟨%hb2, Hbyte, Hclose⟩ :=
    ByteSlice_focus_byte 0 ctrl (t.ctrl.set i c) hi2set c $$ Hctrl
  wasm_twp_rebind twp_store8_addr_gen
    ((t.ctrl.set i c).getD (Table.index2 t.buckets i) 0) with Hbyte
  isimp only [hbyte] at Hbyte
  ihave Hctrl := Hclose $$ Hbyte
  -- the item count drops by one
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := map) (offset := 12)
    (UInt32.ofNat t.items) hh12.1 hh12.2.1 hh12.2.2.1 hh12.2.2.2 with H12
  wasm_twp_pures [twp_const twp_add]
  isimp only [addNegOne t.items hitems hitemsLt]
  wasm_twp_rebind twp_store32 (address := map) (offset := 12)
    (UInt32.ofNat t.items) hh12.1 hh12.2.1 hh12.2.2.1 hh12.2.2.2 with H12
  -- the value of the bucket
  have hslotsGet : t.slots[i]'hiSlots = some (key, v) := by
    rw [← hslot, Table.slotAt, List.getD_eq_getElem]
  ihave ⟨Hpre, Hcell, Hpost⟩ :=
    (Table.slotsBefore_focus 0 ctrl t.slots hiSlots).mp $$ Hslots
  isimp only [hslotsGet, Table.slotCell] at Hcell
  ihave ⟨Hkey, Hval⟩ := Hcell
  obtain ⟨ha1, ha2, ha3⟩ := addr3 (Table.bucketAddr ctrl i + 4) (by omega)
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [negFourAdd (ctrl - (UInt32.ofNat i <<< (3 : UInt32))),
      slotValueAddr_of_wasm ctrl i]
  wasm_twp_rebind Wasm.SmallStep.twp_load32_addr v ha1 ha2 ha3 with Hval
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave Hslots : Table.slotsBefore 0 ctrl (t.slots.set i none) $$
    [Hpre Hkey Hval Hpost]
  · iapply (Table.slotsBefore_set 0 ctrl t.slots hiSlots none).mpr
    isplitl [Hpre]
    · iexact Hpre
    · isplitl [Hkey Hval]
      · iapply Table.slotCell_forget 0 (Table.bucketAddr ctrl i) key v
        isimp only [Table.slotCell]
        iframe Hkey Hval
      · iexact Hpost
  ihave Hheader : Table.tableHeader 0 map ctrl
      (UInt32.ofNat (t.buckets - 1)) (UInt32.ofNat gl)
      (UInt32.ofNat (t.items - 1)) $$ [H0 H4 H8 H12]
  · isimp only [Table.tableHeader]
    iframe H0 H4 H8 H12
  ihave Hgo := Hcont $$ %(ctrl + UInt32.ofNat i)
    %(UInt32.ofNat (Table.wrapSub i 8 t.buckets) + ctrl)
    Hheader Hctrl Hslots
  iexact Hgo


/-! ## The erase -/

/-- The control byte that `erase` writes. -/
private def eraseByte (t : Table UInt32 UInt32) (i : Nat) : UInt8 :=
  if 8 ≤ Table.leadNonEmpty (Table.groupAt t (Table.wrapSub i 8 t.buckets))
      + Table.trailNonEmpty (Table.groupAt t i)
    then Table.DELETED else Table.EMPTY

private theorem erase_buckets (t : Table UInt32 UInt32) (i : Nat) :
    (Table.erase t i).buckets = t.buckets := rfl

private theorem erase_ctrl (t : Table UInt32 UInt32) (i : Nat) :
    (Table.erase t i).ctrl =
      (t.ctrl.set i (eraseByte t i)).set (Table.index2 t.buckets i)
        (eraseByte t i) := rfl

private theorem erase_slots (t : Table UInt32 UInt32) (i : Nat) :
    (Table.erase t i).slots = t.slots.set i none := rfl

private theorem erase_items (t : Table UInt32 UInt32) (i : Nat) :
    (Table.erase t i).items = t.items - 1 := rfl

private theorem erase_growth (t : Table UInt32 UInt32) (i : Nat) :
    (Table.erase t i).growthLeft =
      if 8 ≤ Table.leadNonEmpty
          (Table.groupAt t (Table.wrapSub i 8 t.buckets))
          + Table.trailNonEmpty (Table.groupAt t i)
        then t.growthLeft else t.growthLeft + 1 := rfl

set_option maxHeartbeats 2000000 in
/-- The erase, WAT 2189 to 2261.  It reads the group at the bucket and the
group one width below it, writes the control byte and its mirror, moves
the two counters and reads the value out of the bucket. -/
private theorem twp_func8_erase [WasmSmallStepGS hlc Universal.State]
    {out map key ctrl : UInt32} {t : Table UInt32 UInt32}
    {hashf : UInt32 → UInt64}
    {wmask splat wgroup w7 w8 w9 : UInt64} {pos stride : UInt32}
    {i : Nat} {v : UInt32} {cont : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hwf : Table.WF hashf t) (hclean : Table.Clean t)
    (hi : i < t.buckets) (hslot : t.slotAt i = some (key, v))
    (hmap : map.toNat + 32 < UInt32.size) :
    iprop(
      Table.TableBody 0 map ctrl t ∗
      (∀ (c2 c10 c11 : UInt32) (m4 g6 : UInt64),
        Table.TableBody 0 map ctrl (Table.erase t i) -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 map, .i32 c2],
                [.i32 (UInt32.ofNat (t.buckets - 1)), .i64 m4, .i64 splat,
                  .i64 g6, .i64 w7, .i64 w8, .i64 w9, .i32 c10, .i32 c11,
                  .i32 stride, .i32 1, .i32 v], []⟩,
              cont, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨func8Locals out map key ctrl t wmask splat wgroup w7 w8 w9 pos
              stride (UInt32.ofNat i)
              (ctrl - (UInt32.ofNat i <<< (3 : UInt32))),
            func8Erase ++ cont, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hbody, Hcont⟩
  simp only [func8Erase, func8EraseTest, func8Locals, List.cons_append,
    List.nil_append]
  have hlayout : Table.Layout hashf t := hwf.toLayout
  have hbpos : 0 < t.buckets := hlayout.pos
  have hclen : t.ctrl.length = t.buckets + 8 := hlayout.ctrl_len
  have hbefore : Table.wrapSub i 8 t.buckets < t.buckets :=
    Nat.mod_lt _ hbpos
  have hci : i + 8 ≤ t.ctrl.length := by omega
  have hcb : Table.wrapSub i 8 t.buckets + 8 ≤ t.ctrl.length := by omega
  have hitemsLe : t.items ≤ t.buckets := by
    rw [hwf.items_eq, Table.toList]
    exact Nat.le_trans (List.length_filterMap_le _ _)
      (Nat.le_of_eq List.length_range)
  have hitems : 1 ≤ t.items := by
    rw [hwf.items_eq]
    have hmem : (key, v) ∈ Table.toList t := by
      unfold Table.toList
      rw [List.mem_filterMap]
      exact ⟨i, List.mem_range.mpr hi, hslot⟩
    exact List.length_pos_of_mem hmem
  have hcap := hlayout.shape.cap_lt
  have hglSum : t.growthLeft + t.items
      = Table.bucketMaskToCapacity (t.buckets - 1) := hclean.2
  have hctrlLt : ctrl.toNat < UInt32.size := ctrl.toNat_lt
  have hsize : UInt32.size = 4294967296 := rfl
  isimp only [Table.TableBody, Table.tableHeader] at Hbody
  icases Hbody with ⟨%hroom, ⟨H0, H4, H8, H12⟩, Hctrl, Hslots⟩
  have hitemsLt : t.items < UInt32.size := by omega
  have hglLt : t.growthLeft + 1 < UInt32.size := by omega
  have hgi8 : (Table.groupAt t i).length = 8 := Table.groupAt_length t i
  have hgb8 : (Table.groupAt t (Table.wrapSub i 8 t.buckets)).length = 8 :=
    Table.groupAt_length t _
  have hcti : ∀ b ∈ Table.groupAt t i, Table.IsCtrl b :=
    hlayout.isCtrl_groupAt hclean hi
  have hctb : ∀ b ∈ Table.groupAt t (Table.wrapSub i 8 t.buckets),
      Table.IsCtrl b := hlayout.isCtrl_groupAt hclean hbefore
  have htrailU : (UInt64.ofNat (ctz64 64 (Table.swarMatchEmpty
        (Table.groupWord (Table.groupAt t i))))).toUInt32 >>> (3 : UInt32)
      = UInt32.ofNat (Table.trailNonEmpty (Table.groupAt t i)) := by
    rw [shrU3_ofNat _ (ctz64_le 64 _),
      ← Table.trailingClear_eq_ctz (Table.swarMatchEmpty_and_REP80 _),
      Table.trailingClear_swarMatchEmpty hgi8 hcti]
  have hleadU : (UInt64.ofNat (clz64 64 (Table.swarMatchEmpty
        (Table.groupWord (Table.groupAt t
          (Table.wrapSub i 8 t.buckets)))))).toUInt32 >>> (3 : UInt32)
      = UInt32.ofNat (Table.leadNonEmpty (Table.groupAt t
          (Table.wrapSub i 8 t.buckets))) := by
    rw [shrU3_ofNat _ (clz64_le 64 _),
      ← Table.leadingClear_eq_clz (Table.swarMatchEmpty_and_REP80 _),
      Table.leadingClear_swarMatchEmpty hgb8 hctb]
  have htrailLe : Table.trailNonEmpty (Table.groupAt t i) ≤ 8 := by
    rw [← Table.trailingClear_swarMatchEmpty hgi8 hcti,
      Table.trailingClear_eq_ctz (Table.swarMatchEmpty_and_REP80 _)]
    have := ctz64_le 64 (Table.swarMatchEmpty
      (Table.groupWord (Table.groupAt t i)))
    omega
  have hleadLe : Table.leadNonEmpty (Table.groupAt t
      (Table.wrapSub i 8 t.buckets)) ≤ 8 := by
    rw [← Table.leadingClear_swarMatchEmpty hgb8 hctb,
      Table.leadingClear_eq_clz (Table.swarMatchEmpty_and_REP80 _)]
    have := clz64_le 64 (Table.swarMatchEmpty (Table.groupWord
      (Table.groupAt t (Table.wrapSub i 8 t.buckets))))
    omega
  have hh8 := FrameCells.offset_facts map 8 8 rfl (by omega)
  -- register 10 takes the tombstone byte
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  -- the group at the bucket
  wasm_twp_pures [twp_block twp_localGet twp_localGet twp_add]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave ⟨Hp1, ⟨%hg1b, Hg1⟩, Hs1⟩ :=
    (Table.ByteSlice_groupAt 0 ctrl t hci).mp $$ Hctrl
  have haddr1 : ctrl + UInt32.ofNat i = UInt32.ofNat i + ctrl + 0 := by
    rw [UInt32.add_zero, UInt32.add_comm]
  have hgf1 := FrameCells.offset_facts64 (UInt32.ofNat i + ctrl) 0 0 rfl
    (by rw [← UInt32.add_zero (UInt32.ofNat i + ctrl), ← haddr1]; omega)
  ihave Hg1 := wordMove64 haddr1 $$ Hg1
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := UInt32.ofNat i + ctrl) (offset := 0)
    (Table.groupWord (Table.groupAt t i))
    hgf1.1 hgf1.2.1 hgf1.2.2.1 hgf1.2.2.2.1 hgf1.2.2.2.2.1
    hgf1.2.2.2.2.2.1 hgf1.2.2.2.2.2.2.1 hgf1.2.2.2.2.2.2.2 with Hg1
  ihave Hctrl : Slices.ByteSlice 0 ctrl t.ctrl $$ [Hp1 Hg1 Hs1]
  · iapply (Table.ByteSlice_groupAt 0 ctrl t hci).mpr
    isplitl [Hp1]
    · iexact Hp1
    · isplitl [Hg1]
      · isplitl_pureexact hg1b
        iapply wordMove64 haddr1.symm
        iexact Hg1
      · iexact Hs1
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_shlI64 twp_andI64
    twp_constI64 twp_andI64 twp_ctzI64 twp_wrapI64 twp_const twp_shrU]
  isimp only [shl64Wasm1, swarMatchEmpty_wasm, wrapWasm, shrU32Wasm3,
    htrailU]
  -- the group one width below the bucket
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add twp_localGet
    twp_and twp_add]
    rewriting [before_addr_of_wasm t hlayout.shape hi]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave ⟨Hp2, ⟨%hg2b, Hg2⟩, Hs2⟩ :=
    (Table.ByteSlice_groupAt 0 ctrl t hcb).mp $$ Hctrl
  have haddr2 : ctrl + UInt32.ofNat (Table.wrapSub i 8 t.buckets)
      = UInt32.ofNat (Table.wrapSub i 8 t.buckets) + ctrl + 0 := by
    rw [UInt32.add_zero, UInt32.add_comm]
  have hgf2 := FrameCells.offset_facts64
    (UInt32.ofNat (Table.wrapSub i 8 t.buckets) + ctrl) 0 0 rfl
    (by rw [← UInt32.add_zero
        (UInt32.ofNat (Table.wrapSub i 8 t.buckets) + ctrl), ← haddr2]
        omega)
  ihave Hg2 := wordMove64 haddr2 $$ Hg2
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := UInt32.ofNat (Table.wrapSub i 8 t.buckets) + ctrl)
    (offset := 0)
    (Table.groupWord (Table.groupAt t (Table.wrapSub i 8 t.buckets)))
    hgf2.1 hgf2.2.1 hgf2.2.2.1 hgf2.2.2.2.1 hgf2.2.2.2.2.1
    hgf2.2.2.2.2.2.1 hgf2.2.2.2.2.2.2.1 hgf2.2.2.2.2.2.2.2 with Hg2
  ihave Hctrl : Slices.ByteSlice 0 ctrl t.ctrl $$ [Hp2 Hg2 Hs2]
  · iapply (Table.ByteSlice_groupAt 0 ctrl t hcb).mpr
    isplitl [Hp2]
    · iexact Hp2
    · isplitl [Hg2]
      · isplitl_pureexact hg2b
        iapply wordMove64 haddr2.symm
        iexact Hg2
      · iexact Hs2
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_shlI64 twp_andI64
    twp_constI64 twp_andI64 twp_clzI64 twp_wrapI64 twp_const twp_shrU]
  isimp only [shl64Wasm1, swarMatchEmpty_wasm, wrapWasm, shrU32Wasm3,
    hleadU]
  wasm_twp_pures [twp_add twp_const]
  by_cases htomb : 8 ≤ Table.leadNonEmpty (Table.groupAt t
      (Table.wrapSub i 8 t.buckets)) + Table.trailNonEmpty
      (Table.groupAt t i)
  · -- the run is at least eight bytes long: a tombstone
    iapply Wasm.SmallStep.twp_gtU (result := 1)
      ((sum_gt_seven _ _ hleadLe htrailLe).trans (if_pos htomb)).symm
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_nil, List.drop_zero, List.nil_append]
    iapply twp_func8_erase_writes (hlayout := hlayout) (hi := hi)
      (hslot := hslot) (hmap := hmap) (hroom := hroom) (hitems := hitems)
      (hitemsLt := hitemsLt) (c := Table.DELETED) (gl := t.growthLeft)
      (cw := 128) (v := v) (hbyte := rfl)
    isplitl [H0 H4 H8 H12]
    · isimp only [Table.tableHeader]
      iframe H0 H4 H8 H12
    · isplitl [Hctrl]
      · iexact Hctrl
      · isplitl [Hslots]
        · iexact Hslots
        · iintro %c2 %c11 Hheader Hctrl Hslots
          ihave Hbody : Table.TableBody 0 map ctrl (Table.erase t i) $$
            [Hheader Hctrl Hslots]
          · isimp only [Table.TableBody, erase_buckets, erase_ctrl,
              erase_slots, erase_items, erase_growth, eraseByte,
              if_pos htomb]
            isplitl_pureexact hroom
            iframe Hheader Hctrl Hslots
          ihave Hgo := Hcont $$ %c2 %(128 : UInt32) %c11
            %(Table.groupWord (Table.groupAt t
              (Table.wrapSub i 8 t.buckets))) %wgroup Hbody
          iexact Hgo
  · -- the run is shorter: the byte becomes `EMPTY` and `growth_left` grows
    iapply Wasm.SmallStep.twp_gtU (result := 0)
      ((sum_gt_seven _ _ hleadLe htrailLe).trans (if_neg htomb)).symm
    iapply Wasm.SmallStep.twp_brIfZero
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_load32 (address := map) (offset := 8)
      (UInt32.ofNat t.growthLeft) hh8.1 hh8.2.1 hh8.2.2.1 hh8.2.2.2 with H8
    wasm_twp_pures [twp_const twp_add]
    isimp only [oneAdd t.growthLeft hglLt]
    wasm_twp_rebind twp_store32 (address := map) (offset := 8)
      (UInt32.ofNat t.growthLeft) hh8.1 hh8.2.1 hh8.2.2.1 hh8.2.2.2 with H8
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_exitControl (by rfl)
    isimp only [List.take_nil, List.drop_zero, List.nil_append]
    iapply twp_func8_erase_writes (hlayout := hlayout) (hi := hi)
      (hslot := hslot) (hmap := hmap) (hroom := hroom) (hitems := hitems)
      (hitemsLt := hitemsLt) (c := Table.EMPTY)
      (gl := t.growthLeft + 1) (cw := 255) (v := v) (hbyte := rfl)
    isplitl [H0 H4 H8 H12]
    · isimp only [Table.tableHeader]
      iframe H0 H4 H8 H12
    · isplitl [Hctrl]
      · iexact Hctrl
      · isplitl [Hslots]
        · iexact Hslots
        · iintro %c2 %c11 Hheader Hctrl Hslots
          ihave Hbody : Table.TableBody 0 map ctrl (Table.erase t i) $$
            [Hheader Hctrl Hslots]
          · isimp only [Table.TableBody, erase_buckets, erase_ctrl,
              erase_slots, erase_items, erase_growth, eraseByte,
              if_neg htomb]
            isplitl_pureexact hroom
            iframe Hheader Hctrl Hslots
          ihave Hgo := Hcont $$ %c2 %(255 : UInt32) %c11
            %(Table.groupWord (Table.groupAt t
              (Table.wrapSub i 8 t.buckets))) %wgroup Hbody
          iexact Hgo


/-! ## The answer -/

/-- The eight little-endian bytes of a double word. -/
private def u64Bytes (v : UInt64) : List UInt8 :=
  [u64Byte v 0, u64Byte v 1, u64Byte v 2, u64Byte v 3,
    u64Byte v 4, u64Byte v 5, u64Byte v 6, u64Byte v 7]

/-- One owned double word is its eight owned bytes. -/
private theorem u64_as_bytes {α : Type} [WasmHeapGS α] (memId : Nat)
    (addr : UInt32) (v : UInt64) :
    pointsTo_u64 (α := α) memId addr v ⊣⊢
      pointsToBytes memId addr (u64Bytes v) := by
  have e2 : addr + 1 + 1 = addr + 2 := by rw [UInt32.add_assoc]; rfl
  have e3 : addr + 2 + 1 = addr + 3 := by rw [UInt32.add_assoc]; rfl
  have e4 : addr + 3 + 1 = addr + 4 := by rw [UInt32.add_assoc]; rfl
  have e5 : addr + 4 + 1 = addr + 5 := by rw [UInt32.add_assoc]; rfl
  have e6 : addr + 5 + 1 = addr + 6 := by rw [UInt32.add_assoc]; rfl
  have e7 : addr + 6 + 1 = addr + 7 := by rw [UInt32.add_assoc]; rfl
  simp only [pointsToBytes, pointsTo_u64, u64Bytes, e2, e3, e4, e5, e6, e7,
    (BI.sep_emp (PROP := IProp (WasmHeapGF α))).to_eq]
  exact .rfl

/-- Four owned double words in a row are one owned 32-byte range. -/
private theorem cells_as_slice {α : Type} [WasmHeapGS α] (memId : Nat)
    (addr : UInt32) (v0 v1 v2 v3 : UInt64)
    (hbound : addr.toNat + 32 < UInt32.size) :
    iprop(pointsTo_u64 (α := α) memId addr v0 ∗
      pointsTo_u64 memId (addr + 8) v1 ∗
      pointsTo_u64 memId (addr + 16) v2 ∗
      pointsTo_u64 memId (addr + 24) v3) ⊢
      Slices.ByteSlice memId addr
        (u64Bytes v0 ++ (u64Bytes v1 ++ (u64Bytes v2
          ++ u64Bytes v3))) := by
  have e16 : addr + 8 + 8 = addr + 16 := by rw [UInt32.add_assoc]; rfl
  have e24 : addr + 16 + 8 = addr + 24 := by rw [UInt32.add_assoc]; rfl
  have e8 : (UInt32.ofNat (u64Bytes v0).length : UInt32) = 8 := rfl
  have e8' : (UInt32.ofNat (u64Bytes v1).length : UInt32) = 8 := rfl
  have e8'' : (UInt32.ofNat (u64Bytes v2).length : UInt32) = 8 := rfl
  have hlen : (u64Bytes v0 ++ (u64Bytes v1 ++ (u64Bytes v2
      ++ u64Bytes v3))).length = 32 := rfl
  iintro ⟨H0, H1, H2, H3⟩
  isimp only [Slices.ByteSlice, hlen]
  isplitl_pureexact hbound
  iapply (pointsToBytes_append memId addr (u64Bytes v0)
    (u64Bytes v1 ++ (u64Bytes v2 ++ u64Bytes v3))).mpr
  isimp only [e8]
  isplitl [H0]
  · iapply (u64_as_bytes memId addr v0).mp
    iexact H0
  · iapply (pointsToBytes_append memId (addr + 8) (u64Bytes v1)
      (u64Bytes v2 ++ u64Bytes v3)).mpr
    isimp only [e8', e16]
    isplitl [H1]
    · iapply (u64_as_bytes memId (addr + 8) v1).mp
      iexact H1
    · iapply (pointsToBytes_append memId (addr + 16) (u64Bytes v2)
        (u64Bytes v3)).mpr
      isimp only [e8'', e24]
      isplitl [H2]
      · iapply (u64_as_bytes memId (addr + 16) v2).mp
        iexact H2
      · iapply (u64_as_bytes memId (addr + 24) v3).mp
        iexact H3


set_option maxHeartbeats 8000000 in
/-- The answer, WAT 2263 to 2284.  Register 13 is the discriminant and
register 14 the payload of the `Option<u32>` at `out`, and the whole
32-byte map value moves to `out + 8`. -/
private theorem twp_func8_tail [WasmSmallStepGS hlc Universal.State]
    {params localValues : List Value} {out map disc payload : UInt32}
    {k0 k1 : UInt64} {tf : Table UInt32 UInt32}
    {o : Option UInt32} {outBefore : List UInt8} {cont : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hout0 : ∀ vs : List Value,
      Locals.get ⟨params, localValues, vs⟩ 0 = some (.i32 out))
    (hmap1 : ∀ vs : List Value,
      Locals.get ⟨params, localValues, vs⟩ 1 = some (.i32 map))
    (hdisc : ∀ vs : List Value,
      Locals.get ⟨params, localValues, vs⟩ 13 = some (.i32 disc))
    (hpay : ∀ vs : List Value,
      Locals.get ⟨params, localValues, vs⟩ 14 = some (.i32 payload))
    (hlength : outBefore.length = 40)
    (houtBound : out.toNat + 40 < UInt32.size)
    (hmapBound : map.toNat + 32 < UInt32.size)
    (hdiscValue : disc = if o.isSome then 1 else 0)
    (hpayValue : ∀ v : UInt32, o = some v → payload = v) :
    iprop(
      Slices.ByteSlice 0 out outBefore ∗
      Table.HashMapAt 0 map k0 k1 tf ∗
      (∀ mapBytes : List UInt8,
        ⌜mapBytes.length = 32⌝ -∗
        Table.optionU32At 0 out o -∗
        Table.HashMapAt 0 (out + 8) k0 k1 tf -∗
        Slices.ByteSlice 0 map mapBytes -∗
        WP (.running ⟨⟨params, localValues, []⟩, cont, arity, remainder,
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨params, localValues, []⟩, func8Tail ++ cont, arity,
            remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  iintro ⟨Hout, Hmap, Hcont⟩
  simp only [func8Tail, List.cons_append, List.nil_append]
  have hsize : UInt32.size = 4294967296 := rfl
  have e16 : out + 8 + 8 = out + 16 := by rw [UInt32.add_assoc]; rfl
  have e24 : out + 8 + 16 = out + 24 := by rw [UInt32.add_assoc]; rfl
  have e32 : out + 8 + 24 = out + 32 := by rw [UInt32.add_assoc]; rfl
  have hout8 : (out + 8).toNat = out.toNat + 8 := by
    simpa using Slices.byteOffset_toNat out 8 (by omega)
  have ho0 := FrameCells.offset_facts out 0 0 rfl (by omega)
  have ho4 := FrameCells.offset_facts out 4 4 rfl (by omega)
  have hs8 := FrameCells.offset_facts64 out 8 8 rfl (by omega)
  have hs16 := FrameCells.offset_facts64 out 16 16 rfl (by omega)
  have hs24 := FrameCells.offset_facts64 out 24 24 rfl (by omega)
  have hs32 := FrameCells.offset_facts64 out 32 32 rfl (by omega)
  have hm0 := FrameCells.offset_facts64 map 0 0 rfl (by omega)
  have hm8 := FrameCells.offset_facts64 map 8 8 rfl (by omega)
  have hm16 := FrameCells.offset_facts64 map 16 16 rfl (by omega)
  have hm24 := FrameCells.offset_facts64 map 24 24 rfl (by omega)
  -- the output slot splits into the option and the map value
  have hhead : (outBefore.take 8).length = 8 := by
    rw [List.length_take]; omega
  have htail : (outBefore.drop 8).length = 32 := by
    rw [List.length_drop]; omega
  have happ :=
    (Slices.ByteSlice_append (α := Universal.State) 0 out
      (outBefore.take 8) (outBefore.drop 8)).mp
  rw [List.take_append_drop, hhead,
    show (UInt32.ofNat 8 : UInt32) = 8 from rfl] at happ
  ihave ⟨Hlow, Hhigh⟩ := happ $$ Hout
  ihave ⟨%w0, %w1, Hw0, Hw1⟩ :=
    outWords 0 out (outBefore.take 8) hhead (by omega) $$ Hlow
  ihave ⟨%d0, %d1, %d2, %d3, Hd0, Hd1, Hd2, Hd3⟩ :=
    ByteSlice_thirtyTwo_as_cells 0 (out + 8) (outBefore.drop 8) htail
      $$ Hhigh
  isimp only [e16, e24, e32] at Hd1 Hd2 Hd3
  -- the map value splits into four cells
  ihave ⟨%v0, %v1, Hv0, Hv1, Hk0, Hk1, Hback⟩ :=
    HashMapAt_move 0 map (out + 8) k0 k1 tf $$ Hmap
  isimp only [e16, e24, e32] at Hback
  -- the discriminant and the payload
  iapply Wasm.SmallStep.twp_localGet (hout0 _)
  iapply Wasm.SmallStep.twp_localGet (hpay _)
  wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := out) (offset := 4)
    w1 ho4.1 ho4.2.1 ho4.2.2.1 ho4.2.2.2 with Hw1
  iapply Wasm.SmallStep.twp_localGet (hout0 _)
  iapply Wasm.SmallStep.twp_localGet (hdisc _)
  ihave Hw0 : pointsTo_u32 0 (out + 0) w0 $$ [Hw0]
  · irw_exact [UInt32.add_zero] with Hw0
  wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := out) (offset := 0)
    w0 ho0.1 ho0.2.1 ho0.2.2.1 ho0.2.2.2 with Hw0
  isimp only [UInt32.add_zero] at Hw0
  -- the second seed
  iapply Wasm.SmallStep.twp_localGet (hout0 _)
  iapply Wasm.SmallStep.twp_localGet (hmap1 _)
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := map) (offset := 24)
    k1 hm24.1 hm24.2.1 hm24.2.2.1 hm24.2.2.2.1 hm24.2.2.2.2.1
    hm24.2.2.2.2.2.1 hm24.2.2.2.2.2.2.1 hm24.2.2.2.2.2.2.2 with Hk1
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out) (offset := 32)
    d3 hs32.1 hs32.2.1 hs32.2.2.1 hs32.2.2.2.1 hs32.2.2.2.2.1
    hs32.2.2.2.2.2.1 hs32.2.2.2.2.2.2.1 hs32.2.2.2.2.2.2.2 with Hd3
  -- the first seed
  iapply Wasm.SmallStep.twp_localGet (hout0 _)
  iapply Wasm.SmallStep.twp_localGet (hmap1 _)
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := map) (offset := 16)
    k0 hm16.1 hm16.2.1 hm16.2.2.1 hm16.2.2.2.1 hm16.2.2.2.2.1
    hm16.2.2.2.2.2.1 hm16.2.2.2.2.2.2.1 hm16.2.2.2.2.2.2.2 with Hk0
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out) (offset := 24)
    d2 hs24.1 hs24.2.1 hs24.2.2.1 hs24.2.2.2.1 hs24.2.2.2.2.1
    hs24.2.2.2.2.2.1 hs24.2.2.2.2.2.2.1 hs24.2.2.2.2.2.2.2 with Hd2
  -- the two counters
  iapply Wasm.SmallStep.twp_localGet (hout0 _)
  iapply Wasm.SmallStep.twp_localGet (hmap1 _)
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := map) (offset := 8)
    v1 hm8.1 hm8.2.1 hm8.2.2.1 hm8.2.2.2.1 hm8.2.2.2.2.1
    hm8.2.2.2.2.2.1 hm8.2.2.2.2.2.2.1 hm8.2.2.2.2.2.2.2 with Hv1
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out) (offset := 16)
    d1 hs16.1 hs16.2.1 hs16.2.2.1 hs16.2.2.2.1 hs16.2.2.2.2.1
    hs16.2.2.2.2.2.1 hs16.2.2.2.2.2.2.1 hs16.2.2.2.2.2.2.2 with Hd1
  -- the control pointer and the bucket mask
  iapply Wasm.SmallStep.twp_localGet (hout0 _)
  iapply Wasm.SmallStep.twp_localGet (hmap1 _)
  ihave Hv0 : pointsTo_u64 0 (map + 0) v0 $$ [Hv0]
  · irw_exact [UInt32.add_zero] with Hv0
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := map) (offset := 0)
    v0 hm0.1 hm0.2.1 hm0.2.2.1 hm0.2.2.2.1 hm0.2.2.2.2.1
    hm0.2.2.2.2.2.1 hm0.2.2.2.2.2.2.1 hm0.2.2.2.2.2.2.2 with Hv0
  isimp only [UInt32.add_zero] at Hv0
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out) (offset := 8)
    d0 hs8.1 hs8.2.1 hs8.2.2.1 hs8.2.2.2.1 hs8.2.2.2.2.1
    hs8.2.2.2.2.2.1 hs8.2.2.2.2.2.2.1 hs8.2.2.2.2.2.2.2 with Hd0
  -- the answer
  ihave Hopt : Table.optionU32At 0 out o $$ [Hw0 Hw1]
  · iapply Table.optionU32At_of_words 0 out o payload hpayValue
    isplitl [Hw0]
    · irw_exact [← hdiscValue] with Hw0
    · iexact Hw1
  ihave Hnew := Hback $$ Hd0 Hd1 Hd2 Hd3
  ihave Hslice : Slices.ByteSlice 0 map
      (u64Bytes v0 ++ (u64Bytes v1 ++ (u64Bytes k0 ++ u64Bytes k1)))
      $$ [Hv0 Hv1 Hk0 Hk1]
  · iapply cells_as_slice 0 map v0 v1 k0 k1 (by omega)
    isplitl [Hv0]
    · iexact Hv0
    · isplitl [Hv1]
      · iexact Hv1
      · isplitl [Hk0]
        · iexact Hk0
        · iexact Hk1
  ihave Hgo := Hcont
    $$ %(u64Bytes v0 ++ (u64Bytes v1 ++ (u64Bytes k0 ++ u64Bytes k1)))
    %(rfl : (u64Bytes v0 ++ (u64Bytes v1
      ++ (u64Bytes k0 ++ u64Bytes k1))).length = 32)
    Hopt Hnew Hslice
  iexact Hgo

/-! ## The probe loop of the static singleton

Absolute `func 11` has no item guard, so the static singleton of
`RawTableInner::NEW` runs the hash and the probe loop as well.  Its one
bucket is empty and its eight other control bytes are pads, so the group
at zero is eight `EMPTY` bytes.  The tag mask is then zero and the empty
mask is not zero, so the loop leaves through the miss arm of WAT 2176 on
the first window. -/

set_option maxHeartbeats 2000000 in
private theorem twp_func8_singleton_probe
    [WasmSmallStepGS hlc Universal.State]
    (out map key ctrl : UInt32) (k0 k1 : UInt64) (t : Table UInt32 UInt32)
    (w6 w7 w8 w9 : UInt64) (l13 l14 : UInt32)
    {cont : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {missCode : Program} {missControls : List ControlFrame}
    {missValues : List Value}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hwf : Table.WF (SipHash.hashU32 k0 k1) t) (hclean : Table.Clean t)
    (hbuckets : t.buckets = 1) (hitems : t.items = 0)
    (hmiss : ∀ f g : ControlFrame,
      branchTarget? arity 2 (f :: g :: controls) ([] : List Value) =
        some (missCode, missControls, missValues)) :
    iprop(
      Slices.ByteSlice 0 ctrl (t.ctrl.take 8) ∗
      (Slices.ByteSlice 0 ctrl (t.ctrl.take 8) -∗
        WP (.running
            ⟨{ func8Locals out map key ctrl t 0
                  (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
                  (Table.groupWord (Table.groupAt t 0)) w7 w8 w9 0 0 0 l14
                with values := missValues },
              missCode, arity, remainder, missControls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 map, .i32 key],
              [.i32 (UInt32.ofNat (t.buckets - 1)),
                .i64 (SipHash.hashU32Low k0 k1 key),
                .i64 (Table.repeatByte
                  (Table.h2 (SipHash.hashU32 k0 k1 key))),
                .i64 w6, .i64 w7, .i64 w8, .i64 w9,
                .i32 (UInt32.ofNat (t.buckets - 1) &&&
                  (SipHash.hashU32 k0 k1 key).toUInt32),
                .i32 ctrl, .i32 0, .i32 l13, .i32 l14],
              []⟩,
            func8Probe ++ cont, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hctrl, Hmiss⟩
  have hlayout : Table.Layout (SipHash.hashU32 k0 k1) t := hwf.toLayout
  have hbpos : 0 < t.buckets := hlayout.pos
  -- the table has no item, so every bucket is empty
  have hslotnone : ∀ i, i < t.buckets → t.slotAt i = none := by
    intro i hi
    rcases hsl : t.slotAt i with _ | ⟨kk, vv⟩
    · rfl
    · exfalso
      have hmem : (kk, vv) ∈ Table.toList t := by
        unfold Table.toList
        simp only [List.mem_filterMap, List.mem_range]
        exact ⟨i, hi, hsl⟩
      have hlen : (Table.toList t).length = 0 := by
        rw [← hwf.items_eq, hitems]
      have hpos := List.length_pos_of_mem hmem
      omega
  have hctrlEmpty : ∀ i, i < t.buckets → t.ctrlAt i = Table.EMPTY := by
    intro i hi
    refine hclean.1 i hi (Table.isSpecial_iff.2 ?_)
    intro hf
    have hsome := (hlayout.full_iff i hi).1 hf
    rw [hslotnone i hi] at hsome
    simp at hsome
  have hall : ∀ p, p < t.buckets + 8 → t.ctrlAt p = Table.EMPTY := by
    intro p hp
    rw [hlayout.mirror p hp]
    split
    · rfl
    · exact hctrlEmpty _ (Nat.mod_lt _ hbpos)
  have hg8 : (Table.groupAt t 0).length = 8 := Table.groupAt_length t 0
  have hgj : ∀ j, j < 8 →
      (Table.groupAt t 0).getD j Table.EMPTY = Table.EMPTY := by
    intro j hj
    rw [Table.groupAt_getD t 0 j hj, Nat.zero_add]
    exact hall j (by omega)
  have hctrls : ∀ b ∈ Table.groupAt t 0, Table.IsCtrl b :=
    hlayout.isCtrl_groupAt hclean hbpos
  -- the tag mask is zero and the empty mask is not zero
  have hand := Table.swarMatchTag_and_REP80
    (Table.h2 (SipHash.hashU32 k0 k1 key))
    (Table.groupWord (Table.groupAt t 0))
  have htag0 : Table.swarMatchTag (Table.h2 (SipHash.hashU32 k0 k1 key))
      (Table.groupWord (Table.groupAt t 0)) = 0 := by
    have hzero : Table.swarMatchTag
        (Table.h2 (SipHash.hashU32 k0 k1 key))
        (Table.groupWord (Table.groupAt t 0)) &&& Table.REP80 = 0 := by
      refine (Table.eq_zero_iff_hasBit _).2 ?_
      intro j hj
      rw [hand]
      by_contra hc
      rw [Bool.not_eq_false] at hc
      have hfull := Table.isFull_of_hasBit_swarMatchTag hg8 hj
        (Table.isFull_h2 _) hc
      rw [hgj j hj] at hfull
      exact absurd hfull (by decide)
    rw [hand] at hzero
    exact hzero
  have hme : Table.matchEmpty (Table.groupAt t 0) = true := by
    rw [Table.matchEmpty_iff]
    exact ⟨0, by omega, by rw [Nat.add_zero]; exact hall 0 (by omega)⟩
  have hne0 : Table.swarMatchEmpty
      (Table.groupWord (Table.groupAt t 0)) ≠ 0 := by
    intro hc
    rw [(Table.swarMatchEmpty_eq_zero_iff hg8 hctrls).mp hc] at hme
    exact absurd hme (by decide)
  -- the mask is zero, so the one window starts at bucket zero
  have hmaskNat : (UInt32.ofNat (t.buckets - 1)).toNat = 0 := by
    rw [hbuckets]; rfl
  have hstart : UInt32.ofNat (t.buckets - 1) &&&
      (SipHash.hashU32 k0 k1 key).toUInt32 = 0 := by
    rw [← UInt32.toNat_inj, UInt32.toNat_and, hmaskNat, UInt32.toNat_zero,
      Nat.zero_and]
  -- the group at bucket zero, as one owned word
  have hctrlLen : 8 ≤ t.ctrl.length := by
    rw [hlayout.ctrl_len]; omega
  ihave ⟨%hgbound, Hgroup⟩ :=
    (Table.ByteSlice_singleton_group 0 ctrl t hctrlLen).mp $$ Hctrl
  have hgroupAddr : ctrl = (0 : UInt32) + ctrl + 0 := by
    rw [UInt32.add_zero, UInt32.add_comm, UInt32.add_zero]
  have hgf := FrameCells.offset_facts64 ((0 : UInt32) + ctrl) 0 0 rfl
    (by rw [← UInt32.add_zero ((0 : UInt32) + ctrl), ← hgroupAddr]; omega)
  ihave Hgroup := wordMove64 hgroupAddr $$ Hgroup
  simp only [func8Probe, List.cons_append, List.nil_append]
  isimp only [hstart]
  wasm_twp_pures [twp_block]
  iapply Wasm.SmallStep.twp_loop
  simp only [List.drop_zero, func8LoopBody]
  wasm_twp_pures [twp_block twp_localGet twp_localGet twp_add]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := (0 : UInt32) + ctrl)
    (offset := 0) (Table.groupWord (Table.groupAt t 0))
    hgf.1 hgf.2.1 hgf.2.2.1 hgf.2.2.2.1 hgf.2.2.2.2.1
    hgf.2.2.2.2.2.1 hgf.2.2.2.2.2.2.1 hgf.2.2.2.2.2.2.2 with Hgroup
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_xorI64 twp_localGet twp_constI64
    twp_addI64 twp_andI64 twp_constI64 twp_andI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  isimp only [swarMatchTag_wasm, htag0]
  iapply Wasm.SmallStep.twp_eqzI64 (result := 1) (by rw [if_pos rfl])
  iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
  simp only [List.drop_zero, List.nil_append,
    List.take_nil]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_localGet twp_constI64 twp_shlI64
    twp_andI64 twp_constI64 twp_andI64]
  isimp only [shl64Wasm1, swarMatchEmpty_wasm]
  iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hne0])
  iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
  iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (hmiss _ _)
  ihave Hctrl : Slices.ByteSlice 0 ctrl (t.ctrl.take 8) $$ [Hgroup]
  · iapply (Table.ByteSlice_singleton_group 0 ctrl t hctrlLen).mpr
    isplitl_pureexact hgbound
    iapply wordMove64 hgroupAddr.symm
    iexact Hgroup
  ihave Hgo := Hmiss $$ Hctrl
  iexact Hgo

/-! ## The whole body -/

/-- The block of the probe loop and the erase, as the fragment that
`twp_func8_probe` reads.  Copy of the idiom of `Func9Proof.lean:186`. -/
private theorem func8Probe_slice :
    func8Probe ++ func8Erase =
      Instruction.block 0 0 [Instruction.loop 0 0 func8LoopBody]
        :: func8Erase := rfl

/-- The erase, as the fragment that `twp_func8_erase` reads. -/
private theorem func8Erase_slice :
    func8Erase ++ ([] : Program) = func8Erase := List.append_nil _

/-- The answer, as the fragment that `twp_func8_tail` reads. -/
private theorem func8Tail_slice :
    func8Tail ++ ([] : Program) = func8Tail := List.append_nil _

private theorem func8_index :
    Project.RustHashMap.«module».funcs[8]? =
      some Project.RustHashMap.func8Def := by rfl

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 4000000 in
/-- `HashMap::remove`, absolute `func 11`.  The three arms are the static
singleton, an allocated table with no entry for the key, and an allocated
table with an entry for the key. -/
theorem func8_correct [WasmSmallStepGS hlc Universal.State] :
    Func8Spec (hlc := hlc) := by
  unfold Func8Spec CallContract callExpr
  intro out map key k0 k1 t outBefore callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hout, Hmap, %hpure, Hcont⟩
  obtain ⟨hlength, hwf, hclean, houtBound, hmapBound⟩ := hpure
  have hlayout : Table.Layout (SipHash.hashU32 k0 k1) t := hwf.toLayout
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 11
      Project.RustHashMap.func8Def (by decide) func8_index with Hmodule
  simp only [Project.RustHashMap.func8Def, Function.toLocals,
    Function.numParams, List.length_cons, List.length_nil, List.take,
    List.drop, List.reverse_cons, List.reverse_nil, List.map,
    List.nil_append, List.cons_append, List.append_assoc,
    ValueType.zero, func8_body_shape, Nat.reduceAdd]
  have hm1 : (map + 1).toNat = map.toNat + 1 := by
    simpa using Slices.byteOffset_toNat map 1 (by omega)
  have hm2 : (map + 2).toNat = map.toNat + 2 := by
    simpa using Slices.byteOffset_toNat map 2 (by omega)
  have hm3 : (map + 3).toNat = map.toNat + 3 := by
    simpa using Slices.byteOffset_toNat map 3 (by omega)
  have hh4 := offset_facts map 4 4 rfl (by omega)
  wasm_twp_pures [twp_localGet]
  isimp only [Table.HashMapAt] at Hmap
  icases Hmap with ⟨Htable, Hk0, Hk1⟩
  isimp only [Table.TableAt] at Htable
  icases Htable with ⟨%ctrl, Harm⟩
  icases Harm with (Hsing | ⟨%hbuckets, Hbody⟩)
  · -- the static singleton: the probe loop leaves on the first window
    isimp only [Table.SingletonBody, Table.tableHeader] at Hsing
    icases Hsing with ⟨%hsing, ⟨H0, H4, H8, H12⟩, Hctrl⟩
    have hmask0 : UInt32.ofNat (t.buckets - 1) = (0 : UInt32) := by
      rw [hsing.1]; rfl
    ihave H4 :
      pointsTo_u32 0 (map + 4) (UInt32.ofNat (t.buckets - 1)) $$ [H4]
    · rw [hmask0]
      iexact H4
    wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := map)
      (offset := 4) (UInt32.ofNat (t.buckets - 1)) hh4.1 hh4.2.1
      hh4.2.2.1 hh4.2.2.2 with H4
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_func8_hash (out := out) (map := map) (key := key)
      (mask := UInt32.ofNat (t.buckets - 1)) (k0 := k0) (k1 := k1)
      (hmap := hmapBound)
    isplitl_exacts [Hk0 Hk1]
    iintro %w6 %w7 %w8 %w9 Hk0 Hk1
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_load32_addr ctrl hm1 hm2 hm3
      with H0
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_block]
    rw [← func8Probe_slice]
    iapply twp_func8_singleton_probe out map key ctrl k0 k1 t w6 w7 w8 w9
      0 0 hwf hclean hsing.1 hsing.2.1 (by intro f g; rfl)
    isplitl_exact Hctrl
    iintro Hctrl
    have hfind : Table.find t (SipHash.hashU32 k0 k1 key) key = none :=
      find_eq_none_of_items_zero hwf hsing.2.1 key
    have hrem1 :
        (Table.remove (SipHash.hashU32 k0 k1) t key).1 = none := by
      simp only [Table.remove, hfind]
    have hrem2 : (Table.remove (SipHash.hashU32 k0 k1) t key).2 = t := by
      simp only [Table.remove, hfind]
    isimp only [hrem1, hrem2] at Hcont
    ihave Hmapv : Table.HashMapAt 0 map k0 k1 t $$
      [H0 H4 H8 H12 Hctrl Hk0 Hk1]
    · isimp only [Table.HashMapAt]
      isplitl [H0 H4 H8 H12 Hctrl]
      · isimp only [Table.TableAt]
        iexists ctrl
        ileft
        isimp only [Table.SingletonBody, Table.tableHeader]
        isplitl_pureexact hsing
        ihave H4 : pointsTo_u32 0 (map + 4) (0 : UInt32) $$ [H4]
        · rw [← hmask0]
          iexact H4
        iframe H0 H4 H8 H12 Hctrl
      · iframe Hk0 Hk1
    isimp only [func8Locals, List.take_zero, List.drop_zero,
      List.nil_append]
    rw [← func8Tail_slice]
    iapply twp_func8_tail (out := out) (map := map) (disc := 0)
      (payload := 0) (o := none) (tf := t) (k0 := k0) (k1 := k1)
      (outBefore := outBefore)
    case hout0 => intro vs; rfl
    case hmap1 => intro vs; rfl
    case hdisc => intro vs; rfl
    case hpay => intro vs; rfl
    case hlength => exact hlength
    case houtBound => exact houtBound
    case hmapBound => exact hmapBound
    case hdiscValue => rfl
    case hpayValue => intro v hv; exact absurd hv (by simp)
    isplitl_exacts [Hout Hmapv]
    iintro %mapBytes %hmapLen Hopt Hnew Hraw
    wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
      with Hmodule
    simp only [List.take, List.nil_append]
    iclose_map_runtime Hruntime with Hmodule Henv
    ihave Hgo := Hcont $$ %mapBytes Hruntime Hopt Hnew Hraw %hmapLen
    isimp only [ResumeWP, resumeExpr, List.cons_append,
      List.nil_append] at Hgo
    iexact Hgo
  · -- an allocated table
    isimp only [Table.TableBody, Table.tableHeader] at Hbody
    icases Hbody with ⟨%hctrlBound, ⟨H0, H4, H8, H12⟩, Hctrl, Hslots⟩
    wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := map)
      (offset := 4) (UInt32.ofNat (t.buckets - 1)) hh4.1 hh4.2.1
      hh4.2.2.1 hh4.2.2.2 with H4
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_func8_hash (out := out) (map := map) (key := key)
      (mask := UInt32.ofNat (t.buckets - 1)) (k0 := k0) (k1 := k1)
      (hmap := hmapBound)
    isplitl_exacts [Hk0 Hk1]
    iintro %w6 %w7 %w8 %w9 Hk0 Hk1
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_load32_addr ctrl hm1 hm2 hm3
      with H0
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_block]
    ihave Hbody : Table.TableBody 0 map ctrl t $$
      [H0 H4 H8 H12 Hctrl Hslots]
    · isimp only [Table.TableBody, Table.tableHeader]
      isplitl_pureexact hctrlBound
      iframe H0 H4 H8 H12 Hctrl Hslots
    rw [← func8Probe_slice]
    iapply twp_func8_probe out map key ctrl k0 k1 t w6 w7 w8 w9 0 0
      hwf hclean (by intro f g; rfl)
    isplitl_exact Hbody
    by_cases hck :
      (Table.find t (SipHash.hashU32 k0 k1 key) key).isSome = true
    · -- the key has an entry: the erase runs
      isplitl [Hmodule Henv Hcont Hout Hk0 Hk1]
      · iintro %i %wmask %wgroup %pos %stride %hi Hbody
        obtain ⟨hiLt, v, hslot⟩ := hlayout.slot_of_find hi.2
        have hrem1 : (Table.remove (SipHash.hashU32 k0 k1) t key).1
            = some v := by
          simp only [Table.remove, hi.2, hslot, Option.map_some]
        have hrem2 : (Table.remove (SipHash.hashU32 k0 k1) t key).2
            = Table.erase t i := by
          simp only [Table.remove, hi.2]
        isimp only [hrem1, hrem2] at Hcont
        rw [← func8Erase_slice]
        iapply twp_func8_erase (hwf := hwf) (hclean := hclean)
          (hi := hiLt) (hslot := hslot) (hmap := hmapBound)
        isplitl_exact Hbody
        iintro %c2 %c10 %c11 %m4 %g6 Hbody
        iapply Wasm.SmallStep.twp_exitControl (by rfl)
        simp only [List.take, List.nil_append, List.drop_zero]
        ihave Hmapv : Table.HashMapAt 0 map k0 k1 (Table.erase t i) $$
          [Hbody Hk0 Hk1]
        · isimp only [Table.HashMapAt]
          isplitl [Hbody]
          · isimp only [Table.TableAt]
            iexists ctrl
            iright
            isplitl_pureexact (show 1 < (Table.erase t i).buckets by
              rw [erase_buckets]; exact hbuckets)
            iexact Hbody
          · iframe Hk0 Hk1
        rw [← func8Tail_slice]
        iapply twp_func8_tail (out := out) (map := map) (disc := 1)
          (payload := v) (o := some v) (tf := Table.erase t i)
          (k0 := k0) (k1 := k1) (outBefore := outBefore)
        case hout0 => intro vs; rfl
        case hmap1 => intro vs; rfl
        case hdisc => intro vs; rfl
        case hpay => intro vs; rfl
        case hlength => exact hlength
        case houtBound => exact houtBound
        case hmapBound => exact hmapBound
        case hdiscValue => rfl
        case hpayValue => intro w hw; exact Option.some.inj hw
        isplitl_exacts [Hout Hmapv]
        iintro %mapBytes %hmapLen Hopt Hnew Hraw
        wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
          with Hmodule
        simp only [List.take, List.nil_append]
        iclose_map_runtime Hruntime with Hmodule Henv
        ihave Hgo := Hcont $$ %mapBytes Hruntime Hopt Hnew Hraw %hmapLen
        isimp only [ResumeWP, resumeExpr, List.cons_append,
          List.nil_append] at Hgo
        iexact Hgo
      · iintro %wmask %wgroup %pos %stride %u14 %hmissed Hbody
        rw [hmissed] at hck
        exact absurd hck (by simp)
    · -- the key has no entry: the loop leaves the outer block
      isplitl []
      · iintro %i %wmask %wgroup %pos %stride %hi Hbody
        rw [hi.2] at hck
        exact absurd hck (by simp)
      · iintro %wmask %wgroup %pos %stride %u14 %hmissed Hbody
        have hrem1 : (Table.remove (SipHash.hashU32 k0 k1) t key).1
            = none := by
          simp only [Table.remove, hmissed]
        have hrem2 : (Table.remove (SipHash.hashU32 k0 k1) t key).2
            = t := by
          simp only [Table.remove, hmissed]
        isimp only [hrem1, hrem2] at Hcont
        ihave Hmapv : Table.HashMapAt 0 map k0 k1 t $$ [Hbody Hk0 Hk1]
        · isimp only [Table.HashMapAt]
          isplitl [Hbody]
          · isimp only [Table.TableAt]
            iexists ctrl
            iright
            isplitl_pureexact hbuckets
            iexact Hbody
          · iframe Hk0 Hk1
        isimp only [func8Locals, List.take_zero, List.drop_zero,
          List.nil_append]
        rw [← func8Tail_slice]
        iapply twp_func8_tail (out := out) (map := map) (disc := 0)
          (payload := u14) (o := none) (tf := t) (k0 := k0) (k1 := k1)
          (outBefore := outBefore)
        case hout0 => intro vs; rfl
        case hmap1 => intro vs; rfl
        case hdisc => intro vs; rfl
        case hpay => intro vs; rfl
        case hlength => exact hlength
        case houtBound => exact houtBound
        case hmapBound => exact hmapBound
        case hdiscValue => rfl
        case hpayValue => intro w hw; exact absurd hw (by simp)
        isplitl_exacts [Hout Hmapv]
        iintro %mapBytes %hmapLen Hopt Hnew Hraw
        wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
          with Hmodule
        simp only [List.take, List.nil_append]
        iclose_map_runtime Hruntime with Hmodule Henv
        ihave Hgo := Hcont $$ %mapBytes Hruntime Hopt Hnew Hraw %hmapLen
        isimp only [ResumeWP, resumeExpr, List.cons_append,
          List.nil_append] at Hgo
        iexact Hgo

end Project.RustHashMap.Func8Proof
