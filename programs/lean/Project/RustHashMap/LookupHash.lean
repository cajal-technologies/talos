import Project.RustHashMap.LookupPures
import Project.RustHashMap.FrameCells

/-!
# The inline SipHash of the two lookup kernels

Absolute `func 12` is `HashMap::contains_key` and absolute `func 20` is
`HashMap::get`.  Both bodies inline the same SipHash-1-3 run over the four
key bytes.  This module proves the straight-line hash region of each body
as one step.

* `twp_func9_hash` runs `func9Hash`, WAT lines 2296 to 2469.
* `twp_func17_hash` runs `func17Hash`, WAT lines 4785 to 4958.

The region starts after the compiler loads the bucket mask, so the mask is
already on the operand stack and in a register.  The region ends after the
two stores that the probe loop reads: the start position and the tag lanes.

## What the region computes

The hash itself is `SipHash.hashU32Low`, the low-word run that
`CodeLib.RustStd.HashMap.HashLowWord` defines.
`LookupPures.inlineHash_eq_hashU32Low` identifies it with the compiled
order of the operands.  The model hash is `SipHash.hashU32`, and the two
agree on the low 32 bits only.  That is enough for both consumers:
`Table.h1_hashU32Low` gives the same start position and
`Table.h2_hashU32Low` gives the same control byte.  The exit state
therefore names the model hash in the position register and in the tag
register, and the low-word hash in the hash register.

## The four temporaries

The hash run leaves four `i64` registers that no later instruction of
either body reads.  The probe loop writes each of them before it reads it.
The continuation is universal in those four values, so a caller names them
and never has to unfold the flat hash term.

## The register maps

Absolute `func 12`, eleven registers: `map 0`, `key 1`, `mask 2`,
`hash 3`, `splat 4`, and the temporaries `5` to `8`, then `pos 9` and
`stride 10`.  Absolute `func 20`, fourteen registers: `out 0`, `map 1`,
`key 2`, `mask 3`, `hash 4`, `splat 5`, the temporaries `6` to `9`, then
`pos 10`, `ctrl 11`, `stride 12` and `value 13`.  The two regions are the
same 174 instructions with every register index raised by one.
-/

namespace Project.RustHashMap.LookupHash

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.LookupPures
open scoped Wasm.SmallStep.Outcome

/-! ## The two bridges that the flat term needs -/

/-- The `i64.extend_i32_u` of the key, as the model writes it.  Copy of
`Func15Proof.lean:92`, which is private there. -/
private theorem ofNat_toNat_toUInt64 (x : UInt32) :
    UInt64.ofNat x.toNat = x.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64,
    UInt64.toNat_ofNat_of_lt' (by
      have h := x.toNat_lt
      change x.toNat < 18446744073709551616
      omega)]

/-- The compiled hash and the model hash have the same low word, so
`i32.wrap_i64` gives the same `i32`.  This is `Table.h1_hashU32Low` in the
shape the compiled `i32.and` needs. -/
private theorem toUInt32_hashU32Low (k0 k1 : UInt64) (key : UInt32) :
    (SipHash.hashU32Low k0 k1 key).toUInt32
      = (SipHash.hashU32 k0 k1 key).toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32]
  exact (Table.h1_hashU32Low k0 k1 key).symm

/-! ## Absolute `func 12`, local `func9`: `contains_key` -/

/-- The instructions inside the one block of absolute `func 12`, WAT lines
2288 to 2553. -/
def func9Block : Program :=
  match Project.RustHashMap.func9 with
  | .block _ _ body _ _ :: _ => body
  | _ => []

set_option maxRecDepth 1048576 in
/-- The block and the fall-through `0` are the whole body. -/
theorem func9_shape :
    Project.RustHashMap.func9 = .block 0 0 func9Block :: [.const 0] := rfl

/-- The inline hash of absolute `func 12`, WAT lines 2296 to 2469.  The
region reads the two seeds, computes the hash, masks it into the start
position and builds the tag lanes. -/
def func9Hash : Program :=
  [.localGet 0, .load64 24, .localTee 3, .localGet 1, .extendUI32,
    .localTee 4, .xorI64, .constI64 8098989879002948979, .xorI64, .localTee 5,
    .constI64 16, .rotlI64, .localGet 5, .localGet 0, .load64 16, .localTee 6,
    .constI64 7816392313619706465, .xorI64, .addI64, .localTee 5, .xorI64,
    .localTee 7, .localGet 3, .constI64 7237128888997146477, .xorI64,
    .localTee 3, .localGet 6, .constI64 8317987319222330741, .xorI64, .addI64,
    .localTee 6, .constI64 32, .rotlI64, .addI64, .localTee 8, .localGet 4,
    .constI64 288230376151711744, .orI64, .xorI64, .localGet 3, .constI64 13,
    .rotlI64, .localGet 6, .xorI64, .localTee 3, .localGet 5, .addI64,
    .localTee 4, .localGet 3, .constI64 17, .rotlI64, .xorI64, .localTee 3,
    .addI64, .localTee 5, .localGet 3, .constI64 13, .rotlI64, .xorI64,
    .localTee 3, .localGet 4, .constI64 32, .rotlI64, .constI64 255, .xorI64,
    .localGet 7, .constI64 21, .rotlI64, .localGet 8, .xorI64, .localTee 4,
    .addI64, .localTee 6, .addI64, .localTee 7, .localGet 3, .constI64 17,
    .rotlI64, .xorI64, .localTee 3, .constI64 13, .rotlI64, .localGet 3,
    .localGet 6, .localGet 4, .constI64 16, .rotlI64, .xorI64, .localTee 4,
    .localGet 5, .constI64 32, .rotlI64, .addI64, .localTee 5, .addI64,
    .localTee 3, .xorI64, .localTee 6, .constI64 17, .rotlI64, .localGet 6,
    .localGet 4, .constI64 21, .rotlI64, .localGet 5, .xorI64, .localTee 4,
    .localGet 7, .constI64 32, .rotlI64, .addI64, .localTee 5, .addI64,
    .localTee 6, .xorI64, .localTee 7, .constI64 13, .rotlI64, .localGet 7,
    .localGet 4, .constI64 16, .rotlI64, .localGet 5, .xorI64, .localTee 4,
    .localGet 3, .constI64 32, .rotlI64, .addI64, .localTee 3, .addI64,
    .xorI64, .localTee 5, .constI64 17, .rotlI64, .localGet 4, .constI64 21,
    .rotlI64, .localGet 3, .xorI64, .localTee 3, .constI64 16, .rotlI64,
    .localGet 3, .localGet 6, .constI64 32, .rotlI64, .addI64, .localTee 3,
    .xorI64, .constI64 21, .rotlI64, .xorI64, .localGet 5, .localGet 3,
    .addI64, .localTee 3, .constI64 32, .shrUI64, .xorI64, .localGet 3,
    .xorI64, .localTee 3, .wrapI64, .and, .localSet 9, .localGet 3,
    .constI64 25, .shrUI64, .constI64 127, .andI64,
    .constI64 72340172838076673, .mulI64, .localSet 4]

set_option maxRecDepth 1048576 in
/-- The region is the slice of the block that `func9_shape` names. -/
theorem func9Hash_slice : func9Hash = (func9Block.drop 7).take 174 := rfl

set_option maxRecDepth 1048576 in
/-- The block is the guard, the hash and the probe loop. -/
theorem func9Block_shape :
    func9Block = func9Block.take 7 ++ func9Hash ++ func9Block.drop 181 :=
  rfl

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
/-- The inline hash of `contains_key`, WAT lines 2296 to 2469.  Register 3
takes the compiled hash, register 4 takes the tag lanes and register 9
takes the start position.  Registers 5 to 8 keep values that no later
instruction reads. -/
theorem twp_func9_hash [WasmSmallStepGS hlc Universal.State]
    (map key mask : UInt32) (k0 k1 : UInt64)
    (l2 l3 l4 l5 l6 l7 l8 l9 l10 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hmap : map.toNat + 32 < UInt32.size) :
    iprop(
      pointsTo_u64 0 (map + 16) k0 ∗
      pointsTo_u64 0 (map + 24) k1 ∗
      (∀ (w5 w6 w7 w8 : UInt64),
        pointsTo_u64 0 (map + 16) k0 -∗
        pointsTo_u64 0 (map + 24) k1 -∗
        WP (.running
            ⟨⟨[.i32 map, .i32 key],
                [l2, .i64 (SipHash.hashU32Low k0 k1 key),
                  .i64 (Table.repeatByte
                    (Table.h2 (SipHash.hashU32 k0 k1 key))),
                  .i64 w5, .i64 w6, .i64 w7, .i64 w8,
                  .i32 (mask &&& (SipHash.hashU32 k0 k1 key).toUInt32),
                  l10],
                stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 map, .i32 key],
              [l2, l3, l4, l5, l6, l7, l8, l9, l10], .i32 mask :: stack⟩,
            func9Hash ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hk0, Hk1, Hcont⟩
  have hka0 := offset_facts64 map 16 16 rfl (by omega)
  have hka1 := offset_facts64 map 24 24 rfl (by omega)
  simp only [func9Hash, List.cons_append, List.nil_append]

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
    twp_andI64_bits twp_constI64 twp_mulI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  isimp only [wrapWasm, toUInt32_hashU32Low, shrU64Wasm25, htag]
  iapply Hcont $$ Hk0 Hk1

/-! ## Absolute `func 20`, local `func17`: `get` -/

/-- The instructions inside the outer block of absolute `func 20`, WAT
lines 4773 to 5049. -/
def func17Block : Program :=
  match Project.RustHashMap.func17 with
  | .block _ _ body _ _ :: _ => body
  | _ => []

set_option maxRecDepth 1048576 in
/-- The outer block and the two stores are the whole body. -/
theorem func17_shape :
    Project.RustHashMap.func17 = .block 0 0 func17Block ::
      [.localGet 0, .localGet 13, .store32 4, .localGet 0, .localGet 1,
        .store32 0] := rfl

/-- The inline hash of absolute `func 20`, WAT lines 4785 to 4958.  It is
the region of absolute `func 12` with every register index raised by one. -/
def func17Hash : Program :=
  [.localGet 1, .load64 24, .localTee 4, .localGet 2, .extendUI32,
    .localTee 5, .xorI64, .constI64 8098989879002948979, .xorI64, .localTee 6,
    .constI64 16, .rotlI64, .localGet 6, .localGet 1, .load64 16, .localTee 7,
    .constI64 7816392313619706465, .xorI64, .addI64, .localTee 6, .xorI64,
    .localTee 8, .localGet 4, .constI64 7237128888997146477, .xorI64,
    .localTee 4, .localGet 7, .constI64 8317987319222330741, .xorI64, .addI64,
    .localTee 7, .constI64 32, .rotlI64, .addI64, .localTee 9, .localGet 5,
    .constI64 288230376151711744, .orI64, .xorI64, .localGet 4, .constI64 13,
    .rotlI64, .localGet 7, .xorI64, .localTee 4, .localGet 6, .addI64,
    .localTee 5, .localGet 4, .constI64 17, .rotlI64, .xorI64, .localTee 4,
    .addI64, .localTee 6, .localGet 4, .constI64 13, .rotlI64, .xorI64,
    .localTee 4, .localGet 5, .constI64 32, .rotlI64, .constI64 255, .xorI64,
    .localGet 8, .constI64 21, .rotlI64, .localGet 9, .xorI64, .localTee 5,
    .addI64, .localTee 7, .addI64, .localTee 8, .localGet 4, .constI64 17,
    .rotlI64, .xorI64, .localTee 4, .constI64 13, .rotlI64, .localGet 4,
    .localGet 7, .localGet 5, .constI64 16, .rotlI64, .xorI64, .localTee 5,
    .localGet 6, .constI64 32, .rotlI64, .addI64, .localTee 6, .addI64,
    .localTee 4, .xorI64, .localTee 7, .constI64 17, .rotlI64, .localGet 7,
    .localGet 5, .constI64 21, .rotlI64, .localGet 6, .xorI64, .localTee 5,
    .localGet 8, .constI64 32, .rotlI64, .addI64, .localTee 6, .addI64,
    .localTee 7, .xorI64, .localTee 8, .constI64 13, .rotlI64, .localGet 8,
    .localGet 5, .constI64 16, .rotlI64, .localGet 6, .xorI64, .localTee 5,
    .localGet 4, .constI64 32, .rotlI64, .addI64, .localTee 4, .addI64,
    .xorI64, .localTee 6, .constI64 17, .rotlI64, .localGet 5, .constI64 21,
    .rotlI64, .localGet 4, .xorI64, .localTee 4, .constI64 16, .rotlI64,
    .localGet 4, .localGet 7, .constI64 32, .rotlI64, .addI64, .localTee 4,
    .xorI64, .constI64 21, .rotlI64, .xorI64, .localGet 6, .localGet 4,
    .addI64, .localTee 4, .constI64 32, .shrUI64, .xorI64, .localGet 4,
    .xorI64, .localTee 4, .wrapI64, .and, .localSet 10, .localGet 4,
    .constI64 25, .shrUI64, .constI64 127, .andI64,
    .constI64 72340172838076673, .mulI64, .localSet 5]

set_option maxRecDepth 1048576 in
/-- The region is the slice of the block that `func17_shape` names. -/
theorem func17Hash_slice :
    func17Hash = (func17Block.drop 4).take 174 := rfl

set_option maxRecDepth 1048576 in
/-- The block is the guard, the hash and the probe loop. -/
theorem func17Block_shape :
    func17Block = func17Block.take 4 ++ func17Hash ++ func17Block.drop 178 :=
  rfl

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
/-- The inline hash of `get`, WAT lines 4785 to 4958.  Register 4 takes the
compiled hash, register 5 takes the tag lanes and register 10 takes the
start position.  Registers 6 to 9 keep values that no later instruction
reads. -/
theorem twp_func17_hash [WasmSmallStepGS hlc Universal.State]
    (out map key mask : UInt32) (k0 k1 : UInt64)
    (l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 : Value)
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
                  l11, l12, l13],
                stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 map, .i32 key],
              [l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13],
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
    twp_andI64_bits twp_constI64 twp_mulI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  isimp only [wrapWasm, toUInt32_hashU32Low, shrU64Wasm25, htag]
  iapply Hcont $$ Hk0 Hk1

end Project.RustHashMap.LookupHash
