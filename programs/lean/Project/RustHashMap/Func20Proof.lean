import Project.RustHashMap.SortContracts

/-!
# Proof of `median3_rec`, absolute `func 23`

Absolute `func 23` is `median3_rec`, local `func20`, WAT lines 5598 to
5669 of `programs/rust/build/rust_hash_map/program.wat`.  This module
proves `SortContracts.Func20Spec`.

## The register map

The body has four parameters and three more registers.

| Register | Meaning |
| --- | --- |
| 0 | the first entry address, then the first answer |
| 1 | the second entry address, then the second answer |
| 2 | the third entry address, then the third answer |
| 3 | the length, then `length >>> 3`, then the first key |
| 4 | the byte stride `(length >>> 3) * 32`, then the second key |
| 5 | the first comparison flag, and before it `(length >>> 3) * 56` |
| 6 | the third key |

## The two regions

| Name | WAT | What it does |
| --- | --- | --- |
| `recBody` | 5600 to 5648 | the short exit and the three self-calls |
| `tailBody` | 5650 to 5668 | the three key loads and the two selects |

## The recursion

Below eight entries the block exits at once and the three addresses stay
as they came in.  At eight entries or more the body calls itself three
times, once per address, with the length `k = length >>> 3` and the
addresses `p`, `p + 32 * k` and `p + 56 * k`.  Thirty-two bytes are four
entries and fifty-six bytes are seven entries, so the three arguments of
one self-call span the entries `i`, `i + 4 * k` and `i + 7 * k`, and the
highest one that the call may read is entry `i + 8 * k - 1`.  The caller
promises `i + length <= pairs.length` and `8 * k <= length`, so every
self-call keeps the promise.

The proof is an induction on a bound `N` of `length`.  The helper
`twp_func20_upto` takes `n.toNat <= N` and closes the three self-calls
with the induction hypothesis, because `k <= length / 8 < length`.

## The answer

The contract promises only that the answer is an entry address of the
same buffer.  The tail reads three keys and picks one of the three
addresses with two `select` instructions.  The proof never splits on a
comparison: `select_addr` carries the promise through an `if` whatever
the condition is.
-/

namespace Project.RustHashMap.Func20Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.SortContracts
open scoped Wasm.SmallStep.Outcome

/-! ## Address and word bridges -/

/-- The three address facts that `twp_load32_addr` asks for.  Copy of
`Func12Proof.lean:457`, which is private there. -/
private theorem addr_facts (addr : UInt32)
    (h : addr.toNat + 4 ≤ UInt32.size) :
    (addr + 1).toNat = addr.toNat + 1 ∧
      (addr + 2).toNat = addr.toNat + 2 ∧
      (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using Slices.byteOffset_toNat addr 1 (by omega),
    by simpa using Slices.byteOffset_toNat addr 2 (by omega),
    by simpa using Slices.byteOffset_toNat addr 3 (by omega)⟩

/-- The key cell of entry `i` of a buffer that does not wrap.  Copy of
`Func12Proof.lean:490`, which is private there. -/
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

/-- Move an entry address up by `m` entries. -/
private theorem addr_add (v : UInt32) (i m : Nat) :
    v + UInt32.ofNat (8 * i) + UInt32.ofNat (8 * m)
      = v + UInt32.ofNat (8 * (i + m)) := by
  rw [show 8 * (i + m) = 8 * i + 8 * m from by omega, UInt32.ofNat_add,
    UInt32.add_assoc]

/-- `i32.add` puts the second operand first, so the compiled address has
the stride on the left. -/
private theorem addr_shift (v : UInt32) (i m : Nat) :
    UInt32.ofNat (8 * m) + (v + UInt32.ofNat (8 * i))
      = v + UInt32.ofNat (8 * (i + m)) := by
  rw [UInt32.add_comm (UInt32.ofNat (8 * m)) (v + UInt32.ofNat (8 * i)),
    addr_add]

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

/-- `i32.mul` by fifty-six is a multiplication by seven entries.  The
constant is the second operand, so it is the left factor. -/
private theorem mul_fifty_six (x : UInt32)
    (hbound : 56 * x.toNat < UInt32.size) :
    (56 : UInt32) * x = UInt32.ofNat (8 * (7 * x.toNat)) := by
  have hsz : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mul, show (56 : UInt32).toNat = 56 from rfl,
    Nat.mod_eq_of_lt (by omega : 56 * x.toNat < 2 ^ 32),
    UInt32.toNat_ofNat_of_lt' (by omega)]
  omega

/-- Push `Value.i32` through a `select`. -/
private theorem ite_i32 (c : Prop) [Decidable c] (x y : UInt32) :
    (if c then Value.i32 x else Value.i32 y)
      = Value.i32 (if c then x else y) := by
  split <;> rfl

/-- A `select` between two entry addresses is an entry address.  The
proof never looks at the condition. -/
private theorem select_addr {v : UInt32} {P : Nat → Prop} {c : Prop}
    [Decidable c] {x y : UInt32}
    (hx : ∃ i : Nat, P i ∧ x = v + UInt32.ofNat (8 * i))
    (hy : ∃ i : Nat, P i ∧ y = v + UInt32.ofNat (8 * i)) :
    ∃ i : Nat, P i ∧ (if c then x else y) = v + UInt32.ofNat (8 * i) := by
  split
  · exact hx
  · exact hy

/-- Open the key of entry `i` for a read.  The buffer comes back
unchanged, because the body writes nothing. -/
private theorem slice_key_at {α : Type} [WasmHeapGS α] (v : UInt32)
    (ps : List (UInt32 × UInt32)) {i : Nat} (hi : i < ps.length) :
    Table.PairSlice (α := α) 0 v ps ⊢
      iprop(pointsTo_u32 0 (v + UInt32.ofNat (8 * i)) ps[i].1 ∗
        (pointsTo_u32 0 (v + UInt32.ofNat (8 * i)) ps[i].1 -∗
          Table.PairSlice 0 v ps)) := by
  iintro Hs
  ihave ⟨Hcell, Hclose⟩ := Table.PairSlice_key 0 v ps hi $$ Hs
  isplitl_exact Hcell
  · iintro Hnew
    ihave Hdone := Hclose $$ %ps[i].1 Hnew
    isimp only [show ps.set i (ps[i].1, ps[i].2) = ps from by simp]
      at Hdone
    iexact Hdone

/-! ## The regions of the body -/

/-- The registers of the body.  Registers 0 to 3 are the parameters. -/
@[reducible] private def regs (l0 l1 l2 l3 l4 l5 l6 : UInt32)
    (vs : List Value) : Locals :=
  { params := [.i32 l0, .i32 l1, .i32 l2, .i32 l3],
    locals := [.i32 l4, .i32 l5, .i32 l6],
    values := vs }

/-- The short exit and the three self-calls, WAT 5600 to 5648. -/
@[reducible] private def recBody : Program :=
  [.localGet 3, .const 8, .ltU, .br_if 0,
    .localGet 0, .localGet 0, .localGet 3, .const 3, .shrU,
    .localTee 3, .const 5, .shl, .localTee 4, .add,
    .localGet 0, .localGet 3, .const 56, .mul, .localTee 5, .add,
    .localGet 3, .call 23, .localSet 0,
    .localGet 1, .localGet 1, .localGet 4, .add,
    .localGet 1, .localGet 5, .add,
    .localGet 3, .call 23, .localSet 1,
    .localGet 2, .localGet 2, .localGet 4, .add,
    .localGet 2, .localGet 5, .add,
    .localGet 3, .call 23, .localSet 2]

/-- The three key loads and the two selects, WAT 5650 to 5668. -/
@[reducible] private def tailBody : Program :=
  [.localGet 0, .localGet 2, .localGet 1,
    .localGet 0, .load32 0, .localTee 3,
    .localGet 1, .load32 0, .localTee 4, .ltU, .localTee 5,
    .localGet 4, .localGet 2, .load32 0, .localTee 6, .ltU, .xor,
    .select,
    .localGet 5, .localGet 3, .localGet 6, .ltU, .xor, .select]

set_option maxRecDepth 1048576 in
/-- The generated body is the recursion block and the tail. -/
private theorem func20_shape :
    Project.RustHashMap.func20
      = Instruction.block 0 0 recBody :: tailBody := rfl

private theorem func20_index :
    Project.RustHashMap.«module».funcs[20]? =
      some Project.RustHashMap.func20Def := by rfl

/-! ## The tail -/

set_option maxHeartbeats 2000000 in
/-- The tail, WAT 5650 to 5668.  It reads the key of each of the three
addresses and returns one of the three addresses. -/
private theorem twp_func20_tail [WasmSmallStepGS hlc Universal.State]
    {v r0 r1 r2 l3 l4 l5 l6 : UInt32} {i0 i1 i2 : Nat}
    {pairs : List (UInt32 × UInt32)}
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (h0 : r0 = v + UInt32.ofNat (8 * i0)) (hi0 : i0 < pairs.length)
    (h1 : r1 = v + UInt32.ofNat (8 * i1)) (hi1 : i1 < pairs.length)
    (h2 : r2 = v + UInt32.ofNat (8 * i2)) (hi2 : i2 < pairs.length)
    (hroom : v.toNat + 8 * pairs.length < UInt32.size) :
    iprop(
      Table.PairSlice 0 v pairs ∗
      runtimeModuleOwn ⟨0⟩ Project.RustHashMap.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.RustHashMap.«module») ∗
      (∀ r : UInt32,
        RuntimeContext -∗
        Table.PairSlice 0 v pairs -∗
        ⌜∃ ir : Nat, ir < pairs.length ∧
          r = v + UInt32.ofNat (8 * ir)⌝ -∗
        ResumeWP [.i32 r] callerLocals stack code arity remainder
          controls calls s E Φ)) ⊢
    WP (.running
        ⟨regs r0 r1 r2 l3 l4 l5 l6 [], tailBody, 1, [], [],
          { locals := { callerLocals with values := stack }
            continuation := code, resultArity := arity
            callerRemainder := remainder, control := controls
            returningInstance := ⟨0⟩ } :: calls⟩
        : Expr Universal.State) @ s; E [{ Φ }] := by
  subst h0; subst h1; subst h2
  iintro ⟨Hbuf, Hmodule, Henv, Hcont⟩
  have hf0 := cell_facts32 v i0 pairs.length hi0 hroom
  have hf1 := cell_facts32 v i1 pairs.length hi1 hroom
  have hf2 := cell_facts32 v i2 pairs.length hi2 hroom
  isimp only [tailBody, regs]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
  ihave ⟨Hcell, Hclose⟩ := slice_key_at v pairs hi0 $$ Hbuf
  wasm_twp_rebind Wasm.SmallStep.twp_load32_addr pairs[i0].1
    hf0.1 hf0.2.1 hf0.2.2 with Hcell
  ihave Hbuf := Hclose $$ Hcell
  wasm_twp_pures [twp_localTee twp_localGet]
  ihave ⟨Hcell, Hclose⟩ := slice_key_at v pairs hi1 $$ Hbuf
  wasm_twp_rebind Wasm.SmallStep.twp_load32_addr pairs[i1].1
    hf1.1 hf1.2.1 hf1.2.2 with Hcell
  ihave Hbuf := Hclose $$ Hcell
  wasm_twp_pures [twp_localTee twp_ltU twp_localTee twp_localGet
    twp_localGet]
  ihave ⟨Hcell, Hclose⟩ := slice_key_at v pairs hi2 $$ Hbuf
  wasm_twp_rebind Wasm.SmallStep.twp_load32_addr pairs[i2].1
    hf2.1 hf2.2.1 hf2.2.2 with Hcell
  ihave Hbuf := Hclose $$ Hcell
  wasm_twp_pures [twp_localTee twp_ltU]
  iapply Wasm.SmallStep.twp_xor
  iapply Wasm.SmallStep.twp_select rfl
  simp only [ite_i32]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_ltU]
  iapply Wasm.SmallStep.twp_xor
  iapply Wasm.SmallStep.twp_select rfl
  simp only [ite_i32]
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
    with Hmodule
  simp only [List.take, List.nil_append, List.cons_append]
  iclose_map_runtime Hruntime with Hmodule Henv
  ihave Hgo := Hcont $$ %_ Hruntime Hbuf
    %(select_addr (P := fun i => i < pairs.length)
        ⟨i0, hi0, rfl⟩
        (select_addr (P := fun i => i < pairs.length)
          ⟨i2, hi2, rfl⟩ ⟨i1, hi1, rfl⟩))
  isimp only [ResumeWP, resumeExpr, List.cons_append,
    List.nil_append] at Hgo
  iexact Hgo

/-! ## The body -/

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
/-- Absolute `func 23` returns an entry address of the buffer.  The
bound `N` carries the induction; the body calls itself with the length
`n >>> 3`, which is below `n`. -/
private theorem twp_func20_upto [WasmSmallStepGS hlc Universal.State]
    (N : Nat) :
    ∀ (v a b c n : UInt32) (ia ib ic : Nat)
      (pairs : List (UInt32 × UInt32))
      {callerLocals : Locals} {stack : List Value}
      {code : Program} {arity : Nat} {remainder : List Value}
      {controls : List ControlFrame} {calls : List CallFrame}
      {s : Stuckness} {E : CoPset}
      {Φ : ObservableOutcome → HeapIProp},
      n.toNat ≤ N →
      CallContract 23 [.i32 n, .i32 c, .i32 b, .i32 a]
        callerLocals stack code arity remainder controls calls s E Φ
        iprop(
          RuntimeContext ∗
          Table.PairSlice 0 v pairs ∗
          ⌜a = v + UInt32.ofNat (8 * ia) ∧ b = v + UInt32.ofNat (8 * ib) ∧
            c = v + UInt32.ofNat (8 * ic) ∧ 1 ≤ n.toNat ∧
            ia + n.toNat ≤ pairs.length ∧ ib + n.toNat ≤ pairs.length ∧
            ic + n.toNat ≤ pairs.length ∧
            v.toNat + 8 * pairs.length < UInt32.size⌝ ∗
          (∀ r : UInt32,
            RuntimeContext -∗
            Table.PairSlice 0 v pairs -∗
            ⌜∃ ir : Nat, ir < pairs.length ∧
              r = v + UInt32.ofNat (8 * ir)⌝ -∗
            ResumeWP [.i32 r] callerLocals stack code arity remainder
              controls calls s E Φ)) := by
  induction N with
  | zero =>
      intro v a b c n ia ib ic pairs callerLocals stack code arity
        remainder controls calls s E Φ hN
      unfold CallContract callExpr
      iintro ⟨Hruntime, Hbuf, %hpure, Hcont⟩
      exact absurd hpure.2.2.2.1 (by omega)
  | succ N ih =>
      intro v a b c n ia ib ic pairs callerLocals stack code arity
        remainder controls calls s E Φ hN
      unfold CallContract callExpr
      iintro ⟨Hruntime, Hbuf, %hpure, Hcont⟩
      obtain ⟨ha, hb, hc, hn1, hia, hib, hic, hroom⟩ := hpure
      subst ha; subst hb; subst hc
      iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
      simp only [List.cons_append, List.nil_append]
      wasm_twp_rebind Wasm.SmallStep.twp_call
          Project.RustHashMap.«module» 23
          Project.RustHashMap.func20Def (by decide)
          func20_index with Hmodule
      simp only [Project.RustHashMap.func20Def, Function.toLocals,
        Function.numParams, List.length_cons, List.length_nil, List.take,
        List.drop, List.reverse_cons, List.reverse_nil, List.map,
        List.nil_append, List.cons_append, ValueType.zero, func20_shape,
        Nat.reduceAdd]
      wasm_twp_pures [twp_block twp_localGet twp_const]
      by_cases hsmall : n.toNat < 8
      · -- WAT 5601 to 5604: below eight entries the block exits
        have hlt : n < (8 : UInt32) := by
          rw [UInt32.lt_iff_toNat_lt,
            show (8 : UInt32).toNat = 8 from rfl]
          exact hsmall
        iapply Wasm.SmallStep.twp_ltU (result := 1) (by rw [if_pos hlt])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) rfl
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        iapply twp_func20_tail (v := v) (i0 := ia) (i1 := ib) (i2 := ic)
          rfl (by omega) rfl (by omega) rfl (by omega) hroom
        isplitl_exacts [Hbuf Hmodule Henv]
        iintro %r Hruntime Hbuf %hr
        iapply Hcont $$ %r Hruntime Hbuf %hr
      · -- WAT 5605 to 5647: three self-calls, one per address
        have hge : 8 ≤ n.toNat := by omega
        have hnlt : ¬ n < (8 : UInt32) := by
          rw [UInt32.lt_iff_toNat_lt,
            show (8 : UInt32).toNat = 8 from rfl]
          omega
        iapply Wasm.SmallStep.twp_ltU (result := 0) (by rw [if_neg hnlt])
        iapply Wasm.SmallStep.twp_brIfZero
        set kk : Nat := n.toNat / 8 with hkk
        have hsize : UInt32.size = 4294967296 := rfl
        have hk1 : 1 ≤ kk := by omega
        have hk8 : 8 * kk ≤ n.toNat := by omega
        have hlen : n.toNat ≤ pairs.length := by omega
        have hkN : kk ≤ N := by omega
        have hkfit : kk < UInt32.size := by omega
        have hktoNat : (UInt32.ofNat kk).toNat = kk :=
          UInt32.toNat_ofNat_of_lt' hkfit
        have hshr : n >>> ((3 : UInt32) % 32) = UInt32.ofNat kk := by
          rw [shr_three]
        have hs4 : (UInt32.ofNat kk) <<< ((5 : UInt32) % 32)
            = UInt32.ofNat (8 * (4 * kk)) := by
          rw [shl_five _ (by rw [hktoNat]; omega), hktoNat]
        have hs7 : (56 : UInt32) * UInt32.ofNat kk
            = UInt32.ofNat (8 * (7 * kk)) := by
          rw [mul_fifty_six _ (by rw [hktoNat]; omega), hktoNat]
        wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const
          twp_shrU]
        simp only [hshr]
        wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_const twp_shl]
        simp only [hs4]
        wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_add]
        simp only [addr_shift]
        wasm_twp_pures [twp_localGet twp_localGet twp_const twp_mul]
        simp only [hs7]
        wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_add]
        simp only [addr_shift]
        wasm_twp_pures [twp_localGet]
        have Hrec : _ := ih
        unfold CallContract callExpr at Hrec
        simp only [List.cons_append, List.nil_append] at Hrec
        -- WAT 5621: the self-call on the first address
        iapply Hrec v (v + UInt32.ofNat (8 * ia))
          (v + UInt32.ofNat (8 * (ia + 4 * kk)))
          (v + UInt32.ofNat (8 * (ia + 7 * kk))) (UInt32.ofNat kk)
          ia (ia + 4 * kk) (ia + 7 * kk) pairs
          (callerLocals := regs (v + UInt32.ofNat (8 * ia))
            (v + UInt32.ofNat (8 * ib)) (v + UInt32.ofNat (8 * ic))
            (UInt32.ofNat kk) (UInt32.ofNat (8 * (4 * kk)))
            (UInt32.ofNat (8 * (7 * kk))) 0 [])
          (stack := []) (by omega)
        isplitl [Hmodule Henv]
        · unfold RuntimeContext
          iframe Hmodule Henv
        isplitl_exacts [Hbuf]
        isplitl_pureexact ⟨rfl, rfl, rfl, by omega, by omega, by omega,
          by omega, hroom⟩
        iintro %ra Hruntime Hbuf %hra
        iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
        isimp only [ResumeWP, resumeExpr, List.nil_append,
          List.append_nil]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_add]
        simp only [addr_shift]
        wasm_twp_pures [twp_localGet twp_localGet twp_add]
        simp only [addr_shift]
        wasm_twp_pures [twp_localGet]
        -- WAT 5634: the self-call on the second address
        iapply Hrec v (v + UInt32.ofNat (8 * ib))
          (v + UInt32.ofNat (8 * (ib + 4 * kk)))
          (v + UInt32.ofNat (8 * (ib + 7 * kk))) (UInt32.ofNat kk)
          ib (ib + 4 * kk) (ib + 7 * kk) pairs
          (callerLocals := regs ra (v + UInt32.ofNat (8 * ib))
            (v + UInt32.ofNat (8 * ic))
            (UInt32.ofNat kk) (UInt32.ofNat (8 * (4 * kk)))
            (UInt32.ofNat (8 * (7 * kk))) 0 [])
          (stack := []) (by omega)
        isplitl [Hmodule Henv]
        · unfold RuntimeContext
          iframe Hmodule Henv
        isplitl_exacts [Hbuf]
        isplitl_pureexact ⟨rfl, rfl, rfl, by omega, by omega, by omega,
          by omega, hroom⟩
        iintro %rb Hruntime Hbuf %hrb
        iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
        isimp only [ResumeWP, resumeExpr, List.nil_append,
          List.append_nil]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_add]
        simp only [addr_shift]
        wasm_twp_pures [twp_localGet twp_localGet twp_add]
        simp only [addr_shift]
        wasm_twp_pures [twp_localGet]
        -- WAT 5647: the self-call on the third address
        iapply Hrec v (v + UInt32.ofNat (8 * ic))
          (v + UInt32.ofNat (8 * (ic + 4 * kk)))
          (v + UInt32.ofNat (8 * (ic + 7 * kk))) (UInt32.ofNat kk)
          ic (ic + 4 * kk) (ic + 7 * kk) pairs
          (callerLocals := regs ra rb (v + UInt32.ofNat (8 * ic))
            (UInt32.ofNat kk) (UInt32.ofNat (8 * (4 * kk)))
            (UInt32.ofNat (8 * (7 * kk))) 0 [])
          (stack := []) (by omega)
        isplitl [Hmodule Henv]
        · unfold RuntimeContext
          iframe Hmodule Henv
        isplitl_exacts [Hbuf]
        isplitl_pureexact ⟨rfl, rfl, rfl, by omega, by omega, by omega,
          by omega, hroom⟩
        iintro %rc Hruntime Hbuf %hrc
        iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
        isimp only [ResumeWP, resumeExpr, List.nil_append,
          List.append_nil]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_exitControl]
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        obtain ⟨j0, hj0, hra⟩ := hra
        obtain ⟨j1, hj1, hrb⟩ := hrb
        obtain ⟨j2, hj2, hrc⟩ := hrc
        iapply twp_func20_tail (v := v) (i0 := j0) (i1 := j1) (i2 := j2)
          hra hj0 hrb hj1 hrc hj2 hroom
        isplitl_exacts [Hbuf Hmodule Henv]
        iintro %r Hruntime Hbuf %hr
        iapply Hcont $$ %r Hruntime Hbuf %hr

/-- Absolute `func 23` answers with an entry address of the buffer. -/
theorem func20_correct [WasmSmallStepGS hlc Universal.State] :
    Func20Spec (hlc := hlc) := by
  unfold Func20Spec
  intro v a b c n ia ib ic pairs callerLocals stack code arity remainder
    controls calls s E Φ
  exact twp_func20_upto n.toNat v a b c n ia ib ic pairs (Nat.le_refl _)

end Project.RustHashMap.Func20Proof
