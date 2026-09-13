import Project.RustHashMap.CollectBodyContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func15Hash
import Project.RustHashMap.BitPures
import Project.RustHashMap.ProbeStop
import Project.RustHashMap.Func15Insert

/-!
# Proof of the insert of `collect_entries`

This file proves local `func15`, absolute index 18, WAT lines 4131 to
4546.  The body is `HashMap::insert` with the hash inlined.  It hashes the
key, walks the probe sequence, and then either replaces the value of the
bucket that already holds the key or writes the pair into the first free
bucket.

`Func15Spec` gives `1 <= t.growthLeft`, so the `call 17` at WAT 4314 is
dead and the body allocates nothing.  The theorem rests on `Func15Hash`,
`Func15Insert`, `ProbeStop` and `BitPures`, all of which are
unconditional, so this one is unconditional too.

## The probe loop

WAT 4339 to 4545 is the probe loop.  `twp_loop_wf_family` runs it with the
measure `N - step`, where `N` is the first window that holds an `EMPTY`
byte (`ProbeStop.exists_first_empty_window`).  The family index carries
the model step and the candidate bucket beside the nine machine words that
the loop writes.

One iteration reads one group of eight control bytes, matches the tag, and
walks the matched bytes with the inner loop of WAT 4364 to 4394
(`twp_tag_walk`).  A match ends the body at WAT 4508.  No match falls
through to WAT 4396, which records the lowest special byte of the group as
the insert candidate the first time that it sees one, and then stops on an
`EMPTY` byte or goes to the next window.

## The candidate

The invariant carries `isSpecial (t.ctrlAt c) = true` or `t.buckets <= 8`
beside `c < t.buckets`, because `Func15Insert.twp_fix_insert` and
`ProbeStop.fixInsertIndex_spec` both ask for it.  The disjunct holds at the
moment that the loop records the candidate:
`Table.lowestSpecial_groupAt_some` gives the special byte of the group, and
`Layout.mirror` turns it into the byte of the bucket when the table has 8
buckets or more.

WAT 4419 has two entry paths that differ only in local 17.  A candidate
stands from an earlier window, or this window records one.  The tail after
WAT 4419 is written twice for that reason, because each branch of the
`rcases` must close on its own.
-/
namespace Project.RustHashMap.Func15Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.CollectBodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.BitPures
open Project.RustHashMap.ProbeStop
open Project.RustHashMap.Func15Insert
open scoped Wasm.SmallStep.Outcome

/-- The index of the probe loop family.  `step` and `cand` carry the model
state; the other nine fields are the machine words of the locals that the
loop changes.  Locals 5, 7, 9, 10 and 16 are dead at the loop head, so the
family carries them and the invariant says nothing about them. -/
private structure ProbeIdx where
  step : Nat
  cand : Option Nat
  w5 : UInt64
  w7 : UInt64
  w9 : UInt64
  w10 : UInt64
  pos : UInt32
  flag : UInt32
  stride : UInt32
  w16 : UInt32
  w17 : UInt32

private theorem func15_index :
    Project.RustHashMap.«module».funcs[15]? =
      some Project.RustHashMap.func15Def := by rfl

private theorem ofNat_toNat_toUInt64 (x : UInt32) :
    UInt64.ofNat x.toNat = x.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64,
    UInt64.toNat_ofNat_of_lt' (by
      have h := x.toNat_lt
      change x.toNat < 18446744073709551616
      omega)]

/-- The three address facts that `twp_load32_addr` and `twp_store32_addr`
ask for at one address. -/
private theorem addr_facts (addr : UInt32) (h : addr.toNat + 4 ≤ UInt32.size) :
    (addr + 1).toNat = addr.toNat + 1 ∧ (addr + 2).toNat = addr.toNat + 2 ∧
      (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using Slices.byteOffset_toNat addr 1 (by omega),
    by simpa using Slices.byteOffset_toNat addr 2 (by omega),
    by simpa using Slices.byteOffset_toNat addr 3 (by omega)⟩

private theorem ofNat_ne_zero {n : Nat} (h1 : 1 ≤ n) (h2 : n < UInt32.size) :
    UInt32.ofNat n ≠ (0 : UInt32) := by
  intro hc
  have hnat := congrArg UInt32.toNat hc
  rw [UInt32.toNat_ofNat_of_lt' h2, UInt32.toNat_zero] at hnat
  omega

/-- The body of the `BitMaskIter` walk, WAT 4364 to 4394. -/
@[reducible] private def tagWalkBody : Program :=
  [.localGet 2, .localGet 13, .localGet 5, .ctzI64, .wrapI64, .const 3, .shrU,
    .localGet 12, .add, .localGet 11, .and, .const 3, .shl, .sub, .localTee 16,
    .const 4294967288, .add, .load32 0, .eq, .br_if 2, .localGet 5,
    .constI64 18446744073709551615, .addI64, .localGet 5, .andI64, .localTee 5,
    .eqzI64, .eqz, .br_if 0]

/-- Where the walk of WAT 4358 to 4394 leaves the machine.  With no match it
leaves the block of WAT 4344, with local 5 at zero and local 16 at whatever
the last turn wrote.  With a match it branches two blocks out, with local 16
at the address of the bucket that matched. -/
private def tagWalkExit (out mapBase key value l4 : UInt32)
    (w6 w7 w8 w9 w10 : UInt64) (buckets P : Nat) (ctrl l14 l15 l17 : UInt32)
    (noneCode foundCode : Program)
    (noneControls foundControls : List ControlFrame)
    (noneValues foundValues : List Value)
    (arity : Nat) (remainder : List Value) (calls : List CallFrame)
    (r : Option Nat) (w5' : UInt64) (l16' : UInt32) : Expr Universal.State :=
  match r with
  | none =>
      .running ⟨{ walkLocals out mapBase key value l4 0 w6 w7 w8 w9 w10
            (UInt32.ofNat (buckets - 1)) (UInt32.ofNat P) ctrl l14 l15 l16'
            l17 with values := noneValues },
          noneCode, arity, remainder, noneControls, calls⟩
  | some j0 =>
      .running ⟨{ walkLocals out mapBase key value l4 w5' w6 w7 w8 w9 w10
            (UInt32.ofNat (buckets - 1)) (UInt32.ofNat P) ctrl l14 l15
            (ctrl - (UInt32.ofNat ((P + j0) % buckets) <<< 3)) l17 with
            values := foundValues },
          foundCode, arity, remainder, foundControls, calls⟩

set_option maxHeartbeats 2000000 in
/-- The `BitMaskIter` walk of WAT 4364 to 4394.  It tests the key of every
byte that `match_tag` flags, in ascending order.  The walk either leaves the
block with no match, or branches to the found arm with the address of the
bucket it matched. -/
private theorem twp_tag_walk [WasmSmallStepGS hlc Universal.State]
    {out mapBase key value l4 : UInt32}
    {w6 w7 w8 w9 w10 : UInt64} {l14 l15 l16 l17 : UInt32}
    {ctrl : UInt32} {t : Table UInt32 UInt32} {hashf : UInt32 -> UInt64}
    {m P : Nat} {msk : UInt64}
    {arity : Nat} {remainder : List Value}
    {b6f : ControlFrame} {rest : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    {noneCode foundCode : Program}
    {noneControls foundControls : List ControlFrame}
    {noneValues foundValues : List Value}
    (hlayout : Table.Layout hashf t)
    (hm32 : m ≤ 32) (hbShape : t.buckets = 2 ^ m)
    (hP : P < t.buckets) (hroom : 8 * t.buckets ≤ ctrl.toNat)
    (htarget : ∀ f : ControlFrame,
      branchTarget? arity 2 (f :: b6f :: rest) [] =
        some (foundCode, foundControls, foundValues))
    (hb6fKind : b6f.kind = ControlKind.block)
    (hnoneTarget : branchTarget? arity 0 (b6f :: rest) ([] : List Value) =
      some (noneCode, noneControls, noneValues))
    (hmsk : msk &&& Table.REP80 = msk)
    (hfull : ∀ j ∈ Table.setBytes msk, (t.slotAt ((P + j) % t.buckets)).isSome = true) :
    iprop(
      Table.slotsBefore 0 ctrl t.slots ∗
      (∀ (r : Option Nat) (w5' : UInt64) (l16' : UInt32),
        ⌜(Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) = r⌝ -∗
        Table.slotsBefore 0 ctrl t.slots -∗
        WP (tagWalkExit out mapBase key value l4 w6 w7 w8 w9 w10 t.buckets P
              ctrl l14 l15 l17 noneCode foundCode noneControls foundControls
              noneValues foundValues arity remainder calls r w5' l16') @
          s; E [{ Φ }])) ⊢
      WP (.running
          ⟨{ walkLocals out mapBase key value l4 msk w6 w7 w8 w9 w10
              (UInt32.ofNat (t.buckets - 1)) (UInt32.ofNat P) ctrl l14 l15 l16
              l17 with values := [Value.i64 msk] },
            [Instruction.eqzI64, Instruction.br_if 0,
              Instruction.loop 0 0 tagWalkBody], arity, remainder,
            b6f :: rest, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hslots, Hexit⟩
  have hnone3 : noneCode = b6f.continuation ∧ noneControls = rest ∧
      noneValues = b6f.belowStack := by
    have hplain : branchTarget? arity 0 (b6f :: rest) ([] : List Value) =
        some (b6f.continuation, rest, b6f.belowStack) := by
      simp [branchTarget?, hb6fKind]
    have h := Option.some.inj (hnoneTarget.symm.trans hplain)
    simp only [Prod.mk.injEq] at h
    exact h
  by_cases hmne : msk = 0
  · -- no byte carries the tag: leave the block at once
    subst hmne
    iapply Wasm.SmallStep.twp_eqzI64 (result := 1) (by rw [if_pos rfl])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) hnoneTarget
    have hnone0 : (Table.setBytes (0 : UInt64)).find?
        (fun j => t.keyIs ((P + j) % t.buckets) key) = none := by
      rw [show Table.setBytes (0 : UInt64) = [] from by decide]
      rfl
    ihave Hgo := Hexit $$ %(none : Option Nat) %(0 : UInt64) %l16 %hnone0 Hslots
    isimp only [tagWalkExit] at Hgo
    iexact Hgo
  iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hmne])
  iapply Wasm.SmallStep.twp_brIfZero
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := UInt64 × UInt32)
    (measure := fun q => (Table.setBytes q.1).length)
    (locals := fun q => walkLocals out mapBase key value l4 q.1 w6 w7 w8 w9 w10
      (UInt32.ofNat (t.buckets - 1)) (UInt32.ofNat P) ctrl l14 l15 q.2 l17)
    (I := fun q => iprop(
      ⌜q.1 &&& Table.REP80 = q.1 ∧ q.1 ≠ 0 ∧
        (∀ j, Table.hasBit q.1 j = true → Table.hasBit msk j = true) ∧
        (Table.setBytes msk).find? (fun j => t.keyIs ((P + j) % t.buckets) key) =
          (Table.setBytes q.1).find? (fun j => t.keyIs ((P + j) % t.buckets) key)⌝ ∗
      Table.slotsBefore 0 ctrl t.slots ∗
      (∀ (r : Option Nat) (w5' : UInt64) (l16' : UInt32),
        ⌜(Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) = r⌝ -∗
        Table.slotsBefore 0 ctrl t.slots -∗
        WP (tagWalkExit out mapBase key value l4 w6 w7 w8 w9 w10 t.buckets P
              ctrl l14 l15 l17 noneCode foundCode noneControls foundControls
              noneValues foundValues arity remainder calls r w5' l16') @
          s; E [{ Φ }])))
    (initial := (msk, l16))
    (initialLocals := { walkLocals out mapBase key value l4 msk w6 w7 w8 w9 w10
      (UInt32.ofNat (t.buckets - 1)) (UInt32.ofNat P) ctrl l14 l15 l16 l17 with
      values := [] })
    rfl rfl
  · intro q
    iintro Hrec ⟨%hq, Hslots, Hexit⟩
    obtain ⟨hqmask, hqne, hqsub, hqfind⟩ := hq
    simp only [Wasm.SmallStep.loopBodyExpr, tagWalkBody, walkLocals]
    have hlow : Table.lowestSetByte q.1 = some (ctz64 64 q.1 / 8) :=
      Table.lowestSetByte_eq_ctz hqmask hqne
    have hnext : Table.setBytes q.1 =
        ctz64 64 q.1 / 8 :: Table.setBytes (q.1 &&& (q.1 + 18446744073709551615)) :=
      Table.setBytes_iterNext hqmask hlow
    have hidx := Table.matchIndex_of_wasm t hm32 hbShape hqmask hlow P
    have hbpos : 0 < t.buckets := hlayout.pos
    have hsize32 : UInt32.size = 4294967296 := rfl
    have hctrlLt : ctrl.toNat < 4294967296 := ctrl.toBitVec.isLt
    have hsz : (8 : Nat) * t.buckets ≤ ctrl.toNat := hroom
    have hIlt : (P + ctz64 64 q.1 / 8) % t.buckets < t.buckets := Nat.mod_lt _ hbpos
    have hIlen : (P + ctz64 64 q.1 / 8) % t.buckets < t.slots.length := by
      rw [hlayout.slots_len]; exact hIlt
    have hidxEq : (UInt32.ofNat P + (UInt64.ofNat (ctz64 64 q.1)).toUInt32 >>> 3) &&&
        UInt32.ofNat (t.buckets - 1)
        = UInt32.ofNat ((P + ctz64 64 q.1 / 8) % t.buckets) := by
      rw [UInt32.add_comm, ← hidx, UInt32.ofNat_toNat]
    have hbaddrNat : (Table.bucketAddr ctrl ((P + ctz64 64 q.1 / 8) % t.buckets)).toNat
        = ctrl.toNat - 8 * ((P + ctz64 64 q.1 / 8) % t.buckets + 1) :=
      Table.bucketAddr_toNat ctrl hIlt hroom
    have haddr : (4294967288 : UInt32) +
        (ctrl - (UInt32.ofNat ((P + ctz64 64 q.1 / 8) % t.buckets) <<< 3))
        = Table.bucketAddr ctrl ((P + ctz64 64 q.1 / 8) % t.buckets) := by
      rw [UInt32.add_comm, Table.bucketAddr_of_wasm,
        UInt32.toNat_ofNat_of_lt' (by omega : (P + ctz64 64 q.1 / 8) % t.buckets < UInt32.size)]
      rfl
    obtain ⟨ha1, ha2, ha3⟩ := addr_facts
      (Table.bucketAddr ctrl ((P + ctz64 64 q.1 / 8) % t.buckets)) (by omega)
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_ctzI64 twp_wrapI64
      twp_const twp_shrU twp_localGet twp_add twp_localGet twp_and twp_const twp_shl
      twp_sub]
    isimp only [wrapWasm, shrU32Wasm3, hidxEq, shl32Wasm3]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub]
    wasm_twp_pures [twp_const twp_add]
    isimp only [haddr]
    have hj0q : ctz64 64 q.1 / 8 ∈ Table.setBytes q.1 := by
      rw [hnext]; exact List.mem_cons_self
    have hj0msk : ctz64 64 q.1 / 8 ∈ Table.setBytes msk := by
      simp only [Table.setBytes, List.mem_filter, List.mem_range] at hj0q ⊢
      exact ⟨hj0q.1, hqsub _ hj0q.2⟩
    have hslotSome := hfull _ hj0msk
    obtain ⟨k', v', hslotEq⟩ :
        ∃ k' v', t.slotAt ((P + ctz64 64 q.1 / 8) % t.buckets) = some (k', v') := by
      cases hc : t.slotAt ((P + ctz64 64 q.1 / 8) % t.buckets) with
      | none => rw [hc] at hslotSome; exact absurd hslotSome (by decide)
      | some kv => exact ⟨kv.1, kv.2, rfl⟩
    have hslotsGet : t.slots[(P + ctz64 64 q.1 / 8) % t.buckets]'hIlen = some (k', v') := by
      rw [← hslotEq, Table.slotAt, List.getD_eq_getElem]
    ihave ⟨Hpre, Hcell, Hpost⟩ :=
      (Table.slotsBefore_focus 0 ctrl t.slots hIlen).mp $$ Hslots
    isimp only [hslotsGet, Table.slotCell] at Hcell
    ihave ⟨Hkey, Hval⟩ := Hcell
    wasm_twp_rebind Wasm.SmallStep.twp_load32_addr k' ha1 ha2 ha3 with Hkey
    wasm_twp_pures [twp_eq]
    ihave Hslots : Table.slotsBefore 0 ctrl t.slots $$ [Hpre Hkey Hval Hpost]
    · iapply (Table.slotsBefore_focus 0 ctrl t.slots hIlen).mpr
      isimp only [hslotsGet, Table.slotCell]
      iframe Hpre Hkey Hval Hpost
    by_cases hkey : key = k'
    · -- the bucket holds the key: leave through the found arm
      have hkeyIs : t.keyIs ((P + ctz64 64 q.1 / 8) % t.buckets) key = true := by
        simp only [Table.keyIs, hslotEq, beq_iff_eq]
        exact hkey.symm
      have hfindq : (Table.setBytes q.1).find?
          (fun j => t.keyIs ((P + j) % t.buckets) key) = some (ctz64 64 q.1 / 8) := by
        rw [hnext]
        exact List.find?_cons_of_pos (by simpa using hkeyIs)
      isimp only [if_pos hkey]
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (htarget _)
      ihave Hgo := Hexit $$ %(some (ctz64 64 q.1 / 8)) %q.1
        %(ctrl - UInt32.ofNat ((P + ctz64 64 q.1 / 8) % t.buckets) <<< 3)
        %(hqfind.trans hfindq) Hslots
      isimp only [tagWalkExit, walkLocals] at Hgo
      iexact Hgo
    · -- the bucket holds another key: drop the byte and go on
      have hkeyIs : t.keyIs ((P + ctz64 64 q.1 / 8) % t.buckets) key = false := by
        simp only [Table.keyIs, hslotEq, beq_eq_false_iff_ne, ne_eq]
        exact fun h => hkey h.symm
      have hfindq : (Table.setBytes q.1).find?
          (fun j => t.keyIs ((P + j) % t.buckets) key) =
            (Table.setBytes (q.1 &&& (q.1 + 18446744073709551615))).find?
              (fun j => t.keyIs ((P + j) % t.buckets) key) := by
        rw [hnext, List.find?_cons_of_neg (by simpa using hkeyIs)]
      have hcomm : (q.1 + 18446744073709551615) &&& q.1
          = q.1 &&& (q.1 + 18446744073709551615) := UInt64.and_comm _ _
      have hnextMask : (q.1 &&& (q.1 + 18446744073709551615)) &&& Table.REP80
          = q.1 &&& (q.1 + 18446744073709551615) := by
        rw [UInt64.and_assoc, UInt64.and_comm (q.1 + 18446744073709551615),
          ← UInt64.and_assoc, hqmask]
      have hnextSub : ∀ j, Table.hasBit (q.1 &&& (q.1 + 18446744073709551615)) j
          = true → Table.hasBit msk j = true := by
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
      by_cases hzero : q.1 &&& (q.1 + 18446744073709551615) = 0
      · -- no flagged byte is left: leave the loop and the block
        iapply Wasm.SmallStep.twp_eqzI64 (result := 1) (by rw [if_pos hzero])
        iapply Wasm.SmallStep.twp_eqz (result := 0) (by decide)
        iapply Wasm.SmallStep.twp_brIfZero
        iapply Wasm.SmallStep.twp_exitControl (by decide)
        isimp only [List.take_zero, List.drop_zero, List.nil_append]
        iapply Wasm.SmallStep.twp_exitControl (by rw [hb6fKind]; rfl)
        isimp only [List.take_nil, List.nil_append]
        isimp only [hzero]
        have hsetZero : Table.setBytes 0 = [] := by decide
        have hnone : (Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) = none := by
          rw [hqfind, hfindq, hzero, hsetZero]
          rfl
        ihave Hgo := Hexit $$ %(none : Option Nat) %(0 : UInt64)
          %(ctrl - UInt32.ofNat ((P + ctz64 64 q.1 / 8) % t.buckets) <<< 3)
          %hnone Hslots
        isimp only [tagWalkExit, hnone3.1, hnone3.2.1, hnone3.2.2,
          walkLocals] at Hgo
        iexact Hgo
      · -- one flagged byte is left: take the back edge
        iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hzero])
        iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        ihave Hback := Hrec $$
          %((q.1 &&& (q.1 + 18446744073709551615),
            ctrl - UInt32.ofNat ((P + ctz64 64 q.1 / 8) % t.buckets) <<< 3))
          %(by rw [hnext]; simp)
        iapply Hback
        isplitl_pureexact ⟨hnextMask, hzero, hnextSub, hqfind.trans hfindq⟩
        iframe Hslots Hexit
  · isplitl_pureexact ⟨hmsk, hmne, fun _ h => h, rfl⟩
    iframe Hslots Hexit

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
theorem func15_correct [WasmSmallStepGS hlc Universal.State] :
    Func15Spec (hlc := hlc) := by
  unfold Func15Spec CallContract callExpr
  intro sp out mapBase key value k0 k1 t outBefore below
    callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmap, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtBound, hmapBound, hwf, hclean, hgrowth,
    hgrowthWord⟩ := hfacts
  have hlayout : Table.Layout (SipHash.hashU32 k0 k1) t := hwf.toLayout
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 18
      Project.RustHashMap.func15Def (by decide) func15_index with Hmodule
  simp [Project.RustHashMap.func15Def, Project.RustHashMap.func15,
    Function.toLocals, Function.numParams]
  -- arithmetic on the frame base and on the map value
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hdepth : insertDepth = 144 := rfl
  have hspNat : (144 : Nat) ≤ sp.toNat := by
    rw [hdepth] at hspLow; exact hspLow
  have hmapNat : mapBase.toNat + 32 < 4294967296 := hmapBound
  have hka0 := offset_facts64 mapBase 16 16 rfl (by omega)
  have hka1 := offset_facts64 mapBase 24 24 rfl (by omega)
  -- the frame, committed
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  -- the table and the two seeds
  isimp only [Table.HashMapAt] at Hmap
  icases Hmap with ⟨Htable, Hk0, Hk1⟩
  -- `local 5 := k1`, the start of the inlined hash
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := mapBase)
    (offset := 24) k1
    hka1.1 hka1.2.1 hka1.2.2.1 hka1.2.2.2.1 hka1.2.2.2.2.1
    hka1.2.2.2.2.2.1 hka1.2.2.2.2.2.2.1 hka1.2.2.2.2.2.2.2 with Hk1
  wasm_twp_pures [twp_localTee twp_localGet twp_extendUI32 twp_localTee
    twp_xorI64 twp_constI64 twp_xorI64 twp_localTee twp_constI64
    twp_rotlI64 twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := mapBase)
    (offset := 16) k0
    hka0.1 hka0.2.1 hka0.2.2.1 hka0.2.2.2.1 hka0.2.2.2.2.1
    hka0.2.2.2.2.2.1 hka0.2.2.2.2.2.2.1 hka0.2.2.2.2.2.2.2 with Hk0
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_xorI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_xorI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_orI64 twp_xorI64 twp_localGet
    twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_constI64 twp_xorI64
    twp_localGet twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_constI64 twp_rotlI64
    twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64 twp_constI64 twp_rotlI64 twp_xorI64 twp_localGet
    twp_localGet twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_shrUI64 twp_xorI64 twp_localGet twp_xorI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]

  -- the flat hash term is the model hash of the key
  have hflat : SipHash.hashU32Low k0 k1 key
      = Project.RustHashMap.Func15Hash.inlineHash k0 k1 key :=
    (Project.RustHashMap.Func15Hash.inlineHash_eq_hashU32Low k0 k1 key).symm
  simp only [Project.RustHashMap.Func15Hash.inlineHash,
    Project.RustHashMap.Func15Hash.compressWasm,
    Project.RustHashMap.Func15Hash.roundWasm1,
    Project.RustHashMap.Func15Hash.roundWasm2,
    Project.RustHashMap.Func15Hash.finalWasm] at hflat
  isimp only [ofNat_toNat_toUInt64, rotlWasm13, rotlWasm16, rotlWasm17,
    rotlWasm21, rotlWasm32, shrU64Wasm32, ← hflat]
  -- the table is allocated, because the static singleton has no growth left
  have hh4 := offset_facts mapBase 4 4 rfl (by omega)
  have hh8 := offset_facts mapBase 8 8 rfl (by omega)
  have hh12 := offset_facts mapBase 12 12 rfl (by omega)
  isimp only [Table.TableAt] at Htable
  icases Htable with ⟨%ctrl, Hbody⟩
  icases Hbody with (Hsingleton | ⟨%hbuckets, Hbody⟩)
  · isimp only [Table.SingletonBody] at Hsingleton
    icases Hsingleton with ⟨%hsing, Hheader, Hctrl⟩
    exact absurd hsing.2.2 (by omega)
  isimp only [Table.TableBody, Table.tableHeader] at Hbody
  icases Hbody with ⟨%hctrlBound, ⟨H0, H4, H8, H12⟩, Hctrl, Hslots⟩
  -- the `call 17` is dead: `growth_left` is not zero
  wasm_twp_pures [twp_block twp_localGet]
  wasm_twp_rebind twp_load32 (address := mapBase) (offset := 8)
    (UInt32.ofNat t.growthLeft) hh8.1 hh8.2.1 hh8.2.2.1 hh8.2.2.2 with H8
  iapply twp_brIf (ofNat_ne_zero hgrowth hgrowthWord) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  clear hflat
  have hc1 : (mapBase + 1 : UInt32).toNat = mapBase.toNat + 1 := by
    simpa using Slices.byteOffset_toNat mapBase 1 (by omega)
  have hc2 : (mapBase + 2 : UInt32).toNat = mapBase.toNat + 2 := by
    simpa using Slices.byteOffset_toNat mapBase 2 (by omega)
  have hc3 : (mapBase + 3 : UInt32).toNat = mapBase.toNat + 3 := by
    simpa using Slices.byteOffset_toNat mapBase 3 (by omega)
  -- `local 11 := bucket_mask`, then `local 12 := mask & wrap(hash)`
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := mapBase) (offset := 4)
    (UInt32.ofNat (t.buckets - 1)) hh4.1 hh4.2.1 hh4.2.2.1 hh4.2.2.2 with H4
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_wrapI64 twp_and]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  -- `local 8 := hash >>> 25`, then `local 6 := the tag in every lane`
  wasm_twp_pures [twp_localGet twp_constI64 twp_shrUI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_andI64 twp_constI64 twp_mulI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  -- `local 13 := ctrl`, `local 14 := 0`, `local 15 := 0`
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32_addr ctrl hc1 hc2 hc3 with H0
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub]
  obtain ⟨m, hm32, hmne, hbShape⟩ := hlayout.shape
  have hprobe : UInt32.ofNat (t.buckets - 1) &&& (SipHash.hashU32Low k0 k1 key).toUInt32
      = UInt32.ofNat (Table.probeStart t (SipHash.hashU32 k0 k1 key)).pos := by
    have hlow : Table.probeStart t (SipHash.hashU32 k0 k1 key)
        = Table.probeStart t (SipHash.hashU32Low k0 k1 key) := by
      simp only [Table.probeStart, Table.h1_hashU32Low]
    rw [hlow, UInt32.and_comm, ← Table.probeStart_pos_of_wasm t hm32 hbShape,
      UInt32.ofNat_toNat]
  have htag : ((SipHash.hashU32Low k0 k1 key >>> 25) &&& 127) * 72340172838076673
      = Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)) := by
    rw [show (72340172838076673 : UInt64) = Table.REP01 from rfl,
      Table.repeatByte_h2_of_wasm, Table.h2_hashU32Low]
  isimp only [wrapWasm, hprobe, shrU64Wasm25, htag]
  -- the loop of WAT 4339 to 4545
  iclose_map_runtime Hruntime with Hmodule Henv
  ihave Hsp2 : StackPointer (sp - 16) $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  ihave Hbody : Table.TableBody 0 mapBase ctrl t $$ [H0 H4 H8 H12 Hctrl Hslots]
  · unfold Table.TableBody Table.tableHeader
    isplitl_pureexact hctrlBound
    iframe H0 H4 H8 H12 Hctrl Hslots
  obtain ⟨N, hNfuel, hNempty, hNmin⟩ :=
    ProbeStop.exists_first_empty_window hwf hclean hgrowth (SipHash.hashU32 k0 k1 key)
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := ProbeIdx)
    (measure := fun i => N - i.step)
    (locals := fun i =>
      { params := [.i32 out, .i32 mapBase, .i32 key, .i32 value],
        locals := [.i32 (sp - 16), .i64 i.w5,
          .i64 (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key))),
          .i64 i.w7, .i64 (SipHash.hashU32Low k0 k1 key >>> 25),
          .i64 i.w9, .i64 i.w10,
          .i32 (UInt32.ofNat (t.buckets - 1)), .i32 i.pos, .i32 ctrl,
          .i32 i.flag, .i32 i.stride, .i32 i.w16, .i32 i.w17],
        values := [] })
    (I := fun i => iprop(
      ⌜i.pos = UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos ∧
        i.stride = UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).stride ∧
        i.flag = (if i.cand.isSome then 1 else 0) ∧
        (∀ c, i.cand = some c → i.w17 = UInt32.ofNat c ∧ c < t.buckets ∧
          (Table.isSpecial (t.ctrlAt c) = true ∨ t.buckets ≤ 8)) ∧
        i.step ≤ N ∧
        Table.findOrFindInsertLoop t (Table.h2 (SipHash.hashU32 k0 k1 key)) key
            (Table.probeFuel t - i.step)
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step) i.cand =
          Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key⌝ ∗
      RuntimeContext ∗
      StackPointer (sp - 16) ∗
      StackBelow sp insertDepth below ∗
      Slices.ByteSlice 0 out outBefore ∗
      Table.TableBody 0 mapBase ctrl t ∗
      pointsTo_u64 0 (mapBase + 16) k0 ∗
      pointsTo_u64 0 (mapBase + 24) k1 ∗
      (∀ below' : List UInt8,
          RuntimeContext -∗ StackPointer sp -∗
          StackBelow sp insertDepth below' -∗
          Table.optionU32At 0 out
            (Table.insert (SipHash.hashU32 k0 k1) t key value).1 -∗
          Table.HashMapAt 0 mapBase k0 k1
            (Table.insert (SipHash.hashU32 k0 k1) t key value).2 -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls s E Φ)))
    (initial := ⟨0, none, _, _, _, _, _, _, _, _, _⟩)
    (initialLocals := _)
  · rfl
  · rfl
  · intro i
    iintro Hrec ⟨%hinv, Hruntime, Hsp, Hbelow, Hout, Hbody, Hk0, Hk1, Hcont⟩
    obtain ⟨hipos, histride, hiflag, hicand, histep, hiloop⟩ := hinv
    have hposLt : (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos < t.buckets :=
      hlayout.probe_lt _ _
    simp only [Wasm.SmallStep.loopBodyExpr]
    ihave ⟨%hctrlB2, Hheader, ⟨Hpre, ⟨%hgbound, Hgroup⟩, Hpost⟩, Hslots⟩ :=
      (Table.TableBody_groupAt 0 mapBase ctrl t hlayout hposLt).mp $$ Hbody
    wasm_twp_pures [twp_block twp_block twp_block twp_block twp_block
      twp_localGet twp_localGet twp_add]
    -- `local 7 := load64 (ctrl + pos)`, the group word
    have hgroupAddr : ctrl +
        UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos
          = i.pos + ctrl + 0 := by
      rw [UInt32.add_zero, hipos, UInt32.add_comm]
    have hgf := FrameCells.offset_facts64 (i.pos + ctrl) 0 0 rfl
      (by rw [← UInt32.add_zero (i.pos + ctrl), ← hgroupAddr]; omega)
    ihave Hgroup := wordMove64 hgroupAddr $$ Hgroup
    wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := i.pos + ctrl) (offset := 0)
      (Table.groupWord
        (Table.groupAt t (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos))
      hgf.1 hgf.2.1 hgf.2.2.1 hgf.2.2.2.1 hgf.2.2.2.2.1
      hgf.2.2.2.2.2.1 hgf.2.2.2.2.2.2.1 hgf.2.2.2.2.2.2.2 with Hgroup
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_xorI64]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_constI64 twp_xorI64 twp_localGet twp_constI64 twp_addI64
      twp_andI64 twp_constI64 twp_andI64]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
    isimp only [ProbeStop.swarMatchTag_wasm, hipos]
    iapply twp_tag_walk (hashf := SipHash.hashU32 k0 k1) (m := m)
    case hlayout => exact hlayout
    case hm32 => exact hm32
    case hbShape => exact hbShape
    case hP => exact hposLt
    case hroom => exact hctrlB2
    case hb6fKind => rfl
    case hnoneTarget => rfl
    case htarget => exact fun _ => rfl
    case hmsk => exact ProbeStop.swarMatchTag_and_REP80 _ _
    case hfull =>
      exact fun j hj =>
        ProbeStop.slotAt_isSome_of_mem_matchTag hlayout _ i.step hj
    isplitl_exacts [Hslots]
    iintro %r %w5' %l16' %hfind Hslots
    cases r with
    | none =>
      simp only [tagWalkExit]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      -- the walk read the key of every tagged byte and matched none of them, so
      -- the model step takes its `none` arm
      have hbpos : 0 < t.buckets := hlayout.pos
      have hctrlLen : (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + 8
          ≤ t.ctrl.length := by rw [hlayout.ctrl_len]; omega
      have hg8 : (Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos).length = 8 :=
        Table.groupAt_length t _
      have hctrls : ∀ b ∈ Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos, Table.IsCtrl b :=
        hlayout.isCtrl_groupAt hclean hposLt
      have hmodelFind : (Table.matchTag (Table.h2 (SipHash.hashU32 k0 k1 key))
            (t.groupAt (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos)).find?
              (fun j => t.keyIs
                (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j) %
                  t.buckets) key) = none :=
        (hlayout.find?_setBytes_eq hposLt key).symm.trans hfind
      have hfuel : Table.probeFuel t - i.step
          = (Table.probeFuel t - i.step - 1) + 1 := by omega
      have hnextStride : (8 : UInt32) + i.stride
          = UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
              (i.step + 1)).stride := by
        rw [histride, ProbeStop.probeSeq_stride, ProbeStop.probeSeq_stride]
        apply UInt32.toNat_inj.mp
        simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
          show (8 : UInt32).toNat = 8 from rfl]
        omega
      have hnextPos : (UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
              i.step).pos + ((8 : UInt32) + i.stride)) &&& UInt32.ofNat (t.buckets - 1)
          = UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
              (i.step + 1)).pos := by
        rw [histride, UInt32.add_comm (8 : UInt32),
          show Table.probeSeq t (SipHash.hashU32 k0 k1 key) (i.step + 1)
            = (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).next t from rfl,
          ← Table.probeNext_pos_of_wasm t hm32 hbShape, UInt32.ofNat_toNat]
      -- the walk only read the control bytes, so they go back together
      ihave Hctrl : Slices.ByteSlice 0 ctrl t.ctrl $$ [Hpre Hgroup Hpost]
      · iapply (Table.ByteSlice_groupAt 0 ctrl t hctrlLen).mpr
        isplitl [Hpre]
        · iexact Hpre
        · isplitl [Hgroup]
          · isplitl_pureexact hgbound
            iapply Func15Insert.wordMove64 hgroupAddr.symm
            iexact Hgroup
          · iexact Hpost
      -- WAT 4396 to 4399: `local 5 := match_empty_or_deleted`
      wasm_twp_pures [twp_localGet twp_constI64 twp_andI64]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub]
      -- WAT 4400 to 4404: a candidate is recorded on the first special group only
      wasm_twp_pures [twp_block twp_localGet twp_const]
      rcases hcase : i.cand with _ | c
      · -- no candidate yet
        have hflag0 : i.flag = 0 := by simp [hiflag, hcase]
        iapply Wasm.SmallStep.twp_eq (result := 0) (by simp [hflag0])
        iapply Wasm.SmallStep.twp_brIfZero
        by_cases hls : Table.lowestSpecial (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) = none
        · -- WAT 4405 to 4407: the group has no special byte, so nothing is recorded
          have hzeroSpecial : Table.groupWord (Table.groupAt t
              (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) &&&
              9259542123273814144 = 0 := by
            rw [ProbeStop.swarMatchEmptyOrDeleted_wasm,
              ProbeStop.swarMatchEmptyOrDeleted_eq_zero_iff hg8]
            exact hls
          have hmeF : Table.matchEmpty (Table.groupAt t
              (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) = false :=
            Table.matchEmpty_eq_false_of_lowestSpecial_none hls
          have hwinF : Table.matchEmpty (t.window (SipHash.hashU32 k0 k1 key) i.step)
              = false := hmeF
          have hstepLt : i.step < N := by
            rcases Nat.eq_or_lt_of_le histep with heq | hlt
            · rw [heq, hNempty] at hwinF
              exact Bool.noConfusion hwinF
            · exact hlt
          have hunfold := hiloop
          rw [hfuel] at hunfold
          simp only [Table.findOrFindInsertLoop, hmodelFind, hcase, hls,
            Option.map_none] at hunfold
          have hlookupN : Table.findOrFindInsertLoop t
              (Table.h2 (SipHash.hashU32 k0 k1 key)) key
              (Table.probeFuel t - i.step - 1)
              ((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).next t) none
              = Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key := by
            rw [← hunfold, if_neg (Bool.eq_false_iff.mp hmeF)]
          have hlookupN2 : Table.findOrFindInsertLoop t
              (Table.h2 (SipHash.hashU32 k0 k1 key)) key
              (Table.probeFuel t - (i.step + 1))
              (Table.probeSeq t (SipHash.hashU32 k0 k1 key) (i.step + 1)) none
              = Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key := hlookupN
          wasm_twp_pures [twp_localGet]
          iapply Wasm.SmallStep.twp_eqzI64 (result := 1) (by rw [if_pos hzeroSpecial])
          iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
          simp only [List.take_zero, List.nil_append]
          -- WAT 4532 to 4533: the flag goes back to zero
          wasm_twp_pures [twp_const]
          wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub]
          iapply Wasm.SmallStep.twp_exitControl (by rfl)
          simp only [List.take_zero, List.nil_append]
          -- WAT 4535 to 4544: `ProbeSeq::move_next` and the back edge
          wasm_twp_pures [twp_localGet twp_const twp_add]
          wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub]
          wasm_twp_pures [twp_localGet twp_add twp_localGet twp_and]
          wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub]
          isimp only [hnextPos]
          ihave Hbody : Table.TableBody 0 mapBase ctrl t $$ [Hheader Hctrl Hslots]
          · isimp only [Table.TableBody]
            isplitl_pureexact hctrlB2
            iframe Hheader Hctrl Hslots
          iapply Wasm.SmallStep.twp_br (by rfl)
          simp only [List.take_zero, List.nil_append]
          ihave Hback := Hrec $$ %(⟨i.step + 1, none,
              Table.groupWord (Table.groupAt t
                  (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) &&&
                9259542123273814144,
              Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos),
              i.w9, i.w10,
              UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key) (i.step + 1)).pos,
              0, (8 : UInt32) + i.stride, l16', i.w17⟩ : ProbeIdx)
            %(by omega : N - (i.step + 1) < N - i.step)
          iapply Hback
          isplitl_pureexact ⟨rfl, hnextStride, rfl, by simp,
            (by omega : i.step + 1 ≤ N), hlookupN2⟩
          iframe Hruntime Hsp Hbelow Hout Hbody Hk0 Hk1 Hcont
        · -- WAT 4408 to 4417: the lowest special byte becomes the candidate
          have hneSpecial : Table.groupWord (Table.groupAt t
              (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) &&&
              9259542123273814144 ≠ 0 := by
            intro hz
            rw [ProbeStop.swarMatchEmptyOrDeleted_wasm,
              ProbeStop.swarMatchEmptyOrDeleted_eq_zero_iff hg8] at hz
            exact hls hz
          obtain ⟨j0, hj0⟩ := Option.ne_none_iff_exists'.mp hls
          obtain ⟨c, hcdef⟩ : ∃ c : Nat,
              ((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j0) %
                t.buckets = c := ⟨_, rfl⟩
          have hcLt : c < t.buckets := by rw [← hcdef]; exact Nat.mod_lt _ hbpos
          obtain ⟨hj8, hspj, -⟩ := Table.lowestSpecial_groupAt_some hj0
          have hcSp : Table.isSpecial (t.ctrlAt c) = true ∨ t.buckets ≤ 8 := by
            rcases Nat.lt_or_ge t.buckets 8 with hb | hb
            · exact Or.inr (Nat.le_of_lt hb)
            · left
              have hmir := hlayout.mirror
                ((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j0) (by omega)
              rw [if_neg (by unfold Table.IsPad; omega)] at hmir
              rw [← hcdef, ← hmir]
              exact hspj
          have hlowByte : Table.lowestSetByte (Table.swarMatchEmptyOrDeleted
              (Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos))) = some j0 := by
            rw [Table.lowestSetByte_swarMatchEmptyOrDeleted hg8]
            exact hj0
          have hmskMask : Table.swarMatchEmptyOrDeleted (Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos)) &&& Table.REP80
              = Table.swarMatchEmptyOrDeleted (Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos)) := by
            unfold Table.swarMatchEmptyOrDeleted
            rw [UInt64.and_assoc, UInt64.and_self]
          have hidx := Table.matchIndex_of_wasm t hm32 hbShape hmskMask hlowByte
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos
          rw [← ProbeStop.swarMatchEmptyOrDeleted_wasm] at hidx
          have hidxEq : (UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                  i.step).pos +
                (UInt64.ofNat (ctz64 64 (Table.groupWord (Table.groupAt t
                  (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) &&&
                  9259542123273814144))).toUInt32 >>> 3) &&& UInt32.ofNat (t.buckets - 1)
              = UInt32.ofNat c := by
            rw [← hcdef, UInt32.add_comm, ← hidx, UInt32.ofNat_toNat]
          have hunfold := hiloop
          rw [hfuel] at hunfold
          simp only [Table.findOrFindInsertLoop, hmodelFind, hcase, hj0, Option.map_some,
            hcdef, Option.getD_some] at hunfold
          wasm_twp_pures [twp_localGet]
          iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hneSpecial])
          iapply Wasm.SmallStep.twp_brIfZero
          wasm_twp_pures [twp_localGet twp_ctzI64 twp_wrapI64 twp_const twp_shrU
            twp_localGet twp_add twp_localGet twp_and]
          isimp only [wrapWasm, shrU32Wasm3, hidxEq]
          wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub]
          iapply Wasm.SmallStep.twp_exitControl (by rfl)
          simp only [List.take_zero, List.drop_zero, List.nil_append]

          -- WAT 4419 to 4427: `match_empty` decides between the write and the next window
          wasm_twp_pures [twp_block twp_localGet twp_localGet twp_constI64 twp_shlI64
            twp_andI64 twp_constI64]
          isimp only [shl64Wasm1]
          by_cases hme : Table.matchEmpty (Table.groupAt t
              (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) = true
          · -- the group has an `EMPTY` byte, so the probe stops and the bucket is written
            have hneZero : (Table.groupWord (Table.groupAt t
                  (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) &&&
                (9259542123273814144 : UInt64)) &&&
                (Table.groupWord (Table.groupAt t
                  (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) <<< 1) ≠ 0 := by
              intro hz
              rw [ProbeStop.swarMatchEmpty_wasm,
                Table.swarMatchEmpty_eq_zero_iff hg8 hctrls, hme] at hz
              exact Bool.noConfusion hz
            have hlookup : Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key
                = Table.Lookup.insertAt (Table.fixInsertIndex t c) := by
              rw [← hunfold, if_pos hme]
            have hins1 : (Table.insert (SipHash.hashU32 k0 k1) t key value).1 = none := by
              simp only [Table.insert, Table.reserve, if_pos hgrowth, hlookup]
            have hins2 : (Table.insert (SipHash.hashU32 k0 k1) t key value).2
                = Table.insertAt t (Table.fixInsertIndex t c)
                    (Table.h2 (SipHash.hashU32 k0 k1 key)) (key, value) := by
              simp only [Table.insert, Table.reserve, if_pos hgrowth, hlookup]
            obtain ⟨hfixLt, hfixEmpty⟩ :=
              ProbeStop.fixInsertIndex_spec hwf hclean hgrowth hcLt hcSp
            have htagB : ((SipHash.hashU32Low k0 k1 key >>> 25).toUInt32 &&& 127).toUInt8
                = Table.h2 (SipHash.hashU32 k0 k1 key) := by
              rw [ProbeStop.tagByte_of_wasm, Table.h2_hashU32Low]
            isimp only [hins1, hins2] at Hcont
            iapply Wasm.SmallStep.twp_neI64 (result := 1) (by rw [if_pos hneZero])
            iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            -- WAT 4432 to 4433: the group of `fix_insert_index` is the first one
            wasm_twp_pures [twp_const]
            wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
              Nat.reduceSub]
            -- WAT 4434 to 4456: `fix_insert_index`
            iapply Func15Insert.twp_fix_insert hwf hclean hgrowth hcLt hcSp
            isplitl_exacts [Hctrl]
            iintro %w14 %hw14 Hctrl
            ihave Hbody : Table.TableBody 0 mapBase ctrl t $$ [Hheader Hctrl Hslots]
            · isimp only [Table.TableBody]
              isplitl_pureexact hctrlB2
              iframe Hheader Hctrl Hslots
            -- WAT 4457 to 4505: the tag, the two counters and the pair
            iapply Func15Insert.twp_insert_tail hlayout hm32 hbShape hfixLt hfixEmpty hw14
              hgrowth hmapBound htagB
            isplitl_exacts [Hbody]
            iintro Hbody
            -- WAT 4506: leave the block of WAT 4342 and take the shared return
            iapply Wasm.SmallStep.twp_br (by rfl)
            simp only [List.take_zero, List.nil_append]
            iapply Func15Insert.twp_option_return (o := none) houtLength houtBound
              (by simp) (by simp)
            isplitl_exacts [Hout Hsp]
            iintro Hopt Hsp
            iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
            wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
            iclose_map_runtime Hruntime with Hmodule Henv
            ihave Hmap : Table.HashMapAt 0 mapBase k0 k1
                (Table.insertAt t (Table.fixInsertIndex t c)
                  (Table.h2 (SipHash.hashU32 k0 k1 key)) (key, value)) $$ [Hbody Hk0 Hk1]
            · isimp only [Table.HashMapAt]
              isplitl [Hbody]
              · isimp only [Table.TableAt]
                iexists ctrl
                iright
                isplitl_pureexact (show 1 < (Table.insertAt t (Table.fixInsertIndex t c)
                    (Table.h2 (SipHash.hashU32 k0 k1 key)) (key, value)).buckets from hbuckets)
                iexact Hbody
              · iframe Hk0 Hk1
            ihave Hgo := Hcont $$ %below Hruntime Hsp Hbelow Hopt Hmap
            isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
            iexact Hgo
          · -- no `EMPTY` byte: raise the flag and go to the next window
            have hmeF : Table.matchEmpty (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) = false :=
              Bool.eq_false_iff.mpr hme
            have hzeroEmpty : (Table.groupWord (Table.groupAt t
                  (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) &&&
                (9259542123273814144 : UInt64)) &&&
                (Table.groupWord (Table.groupAt t
                  (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) <<< 1) = 0 := by
              rw [ProbeStop.swarMatchEmpty_wasm, Table.swarMatchEmpty_eq_zero_iff hg8 hctrls]
              exact hmeF
            have hwinF : Table.matchEmpty (t.window (SipHash.hashU32 k0 k1 key) i.step)
                = false := hmeF
            have hstepLt : i.step < N := by
              rcases Nat.eq_or_lt_of_le histep with heq | hlt
              · rw [heq, hNempty] at hwinF
                exact Bool.noConfusion hwinF
              · exact hlt
            have hlookupN : Table.findOrFindInsertLoop t (Table.h2 (SipHash.hashU32 k0 k1 key))
                key (Table.probeFuel t - i.step - 1)
                ((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).next t) (some c)
                = Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key := by
              rw [← hunfold, if_neg hme]
            have hlookupN2 : Table.findOrFindInsertLoop t (Table.h2 (SipHash.hashU32 k0 k1 key))
                key (Table.probeFuel t - (i.step + 1))
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) (i.step + 1)) (some c)
                = Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key := hlookupN
            iapply Wasm.SmallStep.twp_neI64 (result := 0)
              (by rw [if_neg (fun hne => hne hzeroEmpty)])
            iapply Wasm.SmallStep.twp_brIfZero
            -- WAT 4428 to 4430: the flag records that a candidate stands
            wasm_twp_pures [twp_const]
            wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
              Nat.reduceSub]
            iapply Wasm.SmallStep.twp_br (by rfl)
            simp only [List.take_zero, List.nil_append]
            -- WAT 4535 to 4544: `ProbeSeq::move_next` and the back edge
            wasm_twp_pures [twp_localGet twp_const twp_add]
            wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
              Nat.reduceSub]
            wasm_twp_pures [twp_localGet twp_add twp_localGet twp_and]
            wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
              Nat.reduceSub]
            isimp only [hnextPos]
            ihave Hbody : Table.TableBody 0 mapBase ctrl t $$ [Hheader Hctrl Hslots]
            · isimp only [Table.TableBody]
              isplitl_pureexact hctrlB2
              iframe Hheader Hctrl Hslots
            iapply Wasm.SmallStep.twp_br (by rfl)
            simp only [List.take_zero, List.nil_append]
            ihave Hback := Hrec $$ %(⟨i.step + 1, some c,
                Table.groupWord (Table.groupAt t
                    (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) &&&
                  9259542123273814144,
                Table.groupWord (Table.groupAt t
                  (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos),
                i.w9, i.w10,
                UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key) (i.step + 1)).pos,
                1, (8 : UInt32) + i.stride, l16', UInt32.ofNat c⟩ : ProbeIdx)
              %(by omega : N - (i.step + 1) < N - i.step)
            iapply Hback
            isplitl_pureexact ⟨rfl, hnextStride, rfl,
              (fun c' hc' => by obtain rfl := Option.some.inj hc'; exact ⟨rfl, hcLt, hcSp⟩),
              (by omega : i.step + 1 ≤ N), hlookupN2⟩
            iframe Hruntime Hsp Hbelow Hout Hbody Hk0 Hk1 Hcont
      · -- a candidate already stands, so WAT 4400 to 4418 is skipped
        obtain ⟨hl17, hcLt, hcSp⟩ := hicand c hcase
        have hflag1 : i.flag = 1 := by simp [hiflag, hcase]
        iapply Wasm.SmallStep.twp_eq (result := 1) (by simp [hflag1])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        simp only [hl17]
        have hunfold := hiloop
        rw [hfuel] at hunfold
        simp only [Table.findOrFindInsertLoop, hmodelFind, hcase, Option.getD_some] at hunfold

        -- WAT 4419 to 4427: `match_empty` decides between the write and the next window
        wasm_twp_pures [twp_block twp_localGet twp_localGet twp_constI64 twp_shlI64
          twp_andI64 twp_constI64]
        isimp only [shl64Wasm1]
        by_cases hme : Table.matchEmpty (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) = true
        · -- the group has an `EMPTY` byte, so the probe stops and the bucket is written
          have hneZero : (Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) &&&
              (9259542123273814144 : UInt64)) &&&
              (Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) <<< 1) ≠ 0 := by
            intro hz
            rw [ProbeStop.swarMatchEmpty_wasm,
              Table.swarMatchEmpty_eq_zero_iff hg8 hctrls, hme] at hz
            exact Bool.noConfusion hz
          have hlookup : Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key
              = Table.Lookup.insertAt (Table.fixInsertIndex t c) := by
            rw [← hunfold, if_pos hme]
          have hins1 : (Table.insert (SipHash.hashU32 k0 k1) t key value).1 = none := by
            simp only [Table.insert, Table.reserve, if_pos hgrowth, hlookup]
          have hins2 : (Table.insert (SipHash.hashU32 k0 k1) t key value).2
              = Table.insertAt t (Table.fixInsertIndex t c)
                  (Table.h2 (SipHash.hashU32 k0 k1 key)) (key, value) := by
            simp only [Table.insert, Table.reserve, if_pos hgrowth, hlookup]
          obtain ⟨hfixLt, hfixEmpty⟩ :=
            ProbeStop.fixInsertIndex_spec hwf hclean hgrowth hcLt hcSp
          have htagB : ((SipHash.hashU32Low k0 k1 key >>> 25).toUInt32 &&& 127).toUInt8
              = Table.h2 (SipHash.hashU32 k0 k1 key) := by
            rw [ProbeStop.tagByte_of_wasm, Table.h2_hashU32Low]
          isimp only [hins1, hins2] at Hcont
          iapply Wasm.SmallStep.twp_neI64 (result := 1) (by rw [if_pos hneZero])
          iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
          simp only [List.take_zero, List.drop_zero, List.nil_append]
          -- WAT 4432 to 4433: the group of `fix_insert_index` is the first one
          wasm_twp_pures [twp_const]
          wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub]
          -- WAT 4434 to 4456: `fix_insert_index`
          iapply Func15Insert.twp_fix_insert hwf hclean hgrowth hcLt hcSp
          isplitl_exacts [Hctrl]
          iintro %w14 %hw14 Hctrl
          ihave Hbody : Table.TableBody 0 mapBase ctrl t $$ [Hheader Hctrl Hslots]
          · isimp only [Table.TableBody]
            isplitl_pureexact hctrlB2
            iframe Hheader Hctrl Hslots
          -- WAT 4457 to 4505: the tag, the two counters and the pair
          iapply Func15Insert.twp_insert_tail hlayout hm32 hbShape hfixLt hfixEmpty hw14
            hgrowth hmapBound htagB
          isplitl_exacts [Hbody]
          iintro Hbody
          -- WAT 4506: leave the block of WAT 4342 and take the shared return
          iapply Wasm.SmallStep.twp_br (by rfl)
          simp only [List.take_zero, List.nil_append]
          iapply Func15Insert.twp_option_return (o := none) houtLength houtBound
            (by simp) (by simp)
          isplitl_exacts [Hout Hsp]
          iintro Hopt Hsp
          iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
          wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
          iclose_map_runtime Hruntime with Hmodule Henv
          ihave Hmap : Table.HashMapAt 0 mapBase k0 k1
              (Table.insertAt t (Table.fixInsertIndex t c)
                (Table.h2 (SipHash.hashU32 k0 k1 key)) (key, value)) $$ [Hbody Hk0 Hk1]
          · isimp only [Table.HashMapAt]
            isplitl [Hbody]
            · isimp only [Table.TableAt]
              iexists ctrl
              iright
              isplitl_pureexact (show 1 < (Table.insertAt t (Table.fixInsertIndex t c)
                  (Table.h2 (SipHash.hashU32 k0 k1 key)) (key, value)).buckets from hbuckets)
              iexact Hbody
            · iframe Hk0 Hk1
          ihave Hgo := Hcont $$ %below Hruntime Hsp Hbelow Hopt Hmap
          isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
          iexact Hgo
        · -- no `EMPTY` byte: raise the flag and go to the next window
          have hmeF : Table.matchEmpty (Table.groupAt t
              (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) = false :=
            Bool.eq_false_iff.mpr hme
          have hzeroEmpty : (Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) &&&
              (9259542123273814144 : UInt64)) &&&
              (Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) <<< 1) = 0 := by
            rw [ProbeStop.swarMatchEmpty_wasm, Table.swarMatchEmpty_eq_zero_iff hg8 hctrls]
            exact hmeF
          have hwinF : Table.matchEmpty (t.window (SipHash.hashU32 k0 k1 key) i.step)
              = false := hmeF
          have hstepLt : i.step < N := by
            rcases Nat.eq_or_lt_of_le histep with heq | hlt
            · rw [heq, hNempty] at hwinF
              exact Bool.noConfusion hwinF
            · exact hlt
          have hlookupN : Table.findOrFindInsertLoop t (Table.h2 (SipHash.hashU32 k0 k1 key))
              key (Table.probeFuel t - i.step - 1)
              ((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).next t) (some c)
              = Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key := by
            rw [← hunfold, if_neg hme]
          have hlookupN2 : Table.findOrFindInsertLoop t (Table.h2 (SipHash.hashU32 k0 k1 key))
              key (Table.probeFuel t - (i.step + 1))
              (Table.probeSeq t (SipHash.hashU32 k0 k1 key) (i.step + 1)) (some c)
              = Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key := hlookupN
          iapply Wasm.SmallStep.twp_neI64 (result := 0)
            (by rw [if_neg (fun hne => hne hzeroEmpty)])
          iapply Wasm.SmallStep.twp_brIfZero
          -- WAT 4428 to 4430: the flag records that a candidate stands
          wasm_twp_pures [twp_const]
          wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub]
          iapply Wasm.SmallStep.twp_br (by rfl)
          simp only [List.take_zero, List.nil_append]
          -- WAT 4535 to 4544: `ProbeSeq::move_next` and the back edge
          wasm_twp_pures [twp_localGet twp_const twp_add]
          wasm_twp_localTee [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub]
          wasm_twp_pures [twp_localGet twp_add twp_localGet twp_and]
          wasm_twp_localSet [List.set, List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub]
          isimp only [hnextPos]
          ihave Hbody : Table.TableBody 0 mapBase ctrl t $$ [Hheader Hctrl Hslots]
          · isimp only [Table.TableBody]
            isplitl_pureexact hctrlB2
            iframe Hheader Hctrl Hslots
          iapply Wasm.SmallStep.twp_br (by rfl)
          simp only [List.take_zero, List.nil_append]
          ihave Hback := Hrec $$ %(⟨i.step + 1, some c,
              Table.groupWord (Table.groupAt t
                  (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) &&&
                9259542123273814144,
              Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos),
              i.w9, i.w10,
              UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key) (i.step + 1)).pos,
              1, (8 : UInt32) + i.stride, l16', UInt32.ofNat c⟩ : ProbeIdx)
            %(by omega : N - (i.step + 1) < N - i.step)
          iapply Hback
          isplitl_pureexact ⟨rfl, hnextStride, rfl,
            (fun c' hc' => by obtain rfl := Option.some.inj hc'; exact ⟨rfl, hcLt, hcSp⟩),
            (by omega : i.step + 1 ≤ N), hlookupN2⟩
          iframe Hruntime Hsp Hbelow Hout Hbody Hk0 Hk1 Hcont
    | some j0 =>
      simp only [tagWalkExit]
      -- the walk found the bucket, so the model lookup is `found` at the same
      -- index, and `insert` takes its replacement arm
      have hmodelFind : (Table.matchTag (Table.h2 (SipHash.hashU32 k0 k1 key))
            (t.groupAt (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos)).find?
              (fun j => t.keyIs
                (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j) %
                  t.buckets) key) = some j0 :=
        (hlayout.find?_setBytes_eq hposLt key).symm.trans hfind
      obtain ⟨oldValue, hslot⟩ :=
        (Table.keyIs_iff t _ key).mp (Table.tagFind_some hmodelFind).2.2
      have hbpos : 0 < t.buckets := hlayout.pos
      have hjLt : ((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j0) %
          t.buckets < t.buckets := Nat.mod_lt _ hbpos
      have hjLen : ((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j0) %
          t.buckets < t.slots.length := by rw [hlayout.slots_len]; exact hjLt
      have hctrlLt : ctrl.toNat < UInt32.size := ctrl.toBitVec.isLt
      have hbaddr := Table.bucketAddr_toNat ctrl hjLt hctrlB2
      have hroom8 : (Table.bucketAddr ctrl
          (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j0) %
            t.buckets)).toNat + 8 ≤ UInt32.size := by
        change _ + 8 ≤ 4294967296
        omega
      have hctrlLen : (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + 8
          ≤ t.ctrl.length := by rw [hlayout.ctrl_len]; omega
      have hfuel : Table.probeFuel t - i.step
          = (Table.probeFuel t - i.step - 1) + 1 := by omega
      have hlookup : Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key =
          .found (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j0) %
            t.buckets) := by
        rw [← hiloop, hfuel]
        simp only [Table.findOrFindInsertLoop, hmodelFind]
      have hins1 : (Table.insert (SipHash.hashU32 k0 k1) t key value).1
          = some oldValue := by
        simp only [Table.insert, Table.reserve, if_pos hgrowth, hlookup, hslot]
      have hins2 : (Table.insert (SipHash.hashU32 k0 k1) t key value).2 =
          { t with
            slots :=
              t.slots.set
                (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j0) %
                  t.buckets)
                (some (key, value)) } := by
        simp only [Table.insert, Table.reserve, if_pos hgrowth, hlookup, hslot]
      isimp only [hins1, hins2] at Hcont
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      -- WAT 4508 to 4518: read the old value, write the new one
      iapply Func15Insert.twp_found_arm hjLen hslot hroom8
      isplitl_exacts [Hslots]
      iintro Hslots
      -- leave the block of WAT 4342 and take the shared return
      iapply Wasm.SmallStep.twp_exitControl (by rfl)
      isimp only [List.take_zero, List.drop_zero, List.nil_append]
      iapply Func15Insert.twp_option_return (o := some oldValue) houtLength houtBound
        (by simp) (fun v hv => Option.some.inj hv)
      isplitl_exacts [Hout Hsp]
      iintro Hopt Hsp
      iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
      wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
      iclose_map_runtime Hruntime with Hmodule Henv
      -- the control bytes did not change, so the map value is the model one
      ihave Hctrl : Slices.ByteSlice 0 ctrl t.ctrl $$ [Hpre Hgroup Hpost]
      · iapply (Table.ByteSlice_groupAt 0 ctrl t hctrlLen).mpr
        isplitl [Hpre]
        · iexact Hpre
        · isplitl [Hgroup]
          · isplitl_pureexact hgbound
            iapply Func15Insert.wordMove64 hgroupAddr.symm
            iexact Hgroup
          · iexact Hpost
      ihave Hmap : Table.HashMapAt 0 mapBase k0 k1
          { t with
            slots :=
              t.slots.set
                (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j0) %
                  t.buckets)
                (some (key, value)) } $$ [Hheader Hctrl Hslots Hk0 Hk1]
      · isimp only [Table.HashMapAt]
        isplitl [Hheader Hctrl Hslots]
        · isimp only [Table.TableAt]
          iexists ctrl
          iright
          isplitl_pureexact hbuckets
          isimp only [Table.TableBody]
          isplitl_pureexact hctrlB2
          iframe Hheader Hctrl Hslots
        · iframe Hk0 Hk1
      ihave Hgo := Hcont $$ %below Hruntime Hsp Hbelow Hopt Hmap
      isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
      iexact Hgo
  · -- the invariant holds at the first window
    isplitl_pureexact (⟨rfl, rfl, rfl, by simp, Nat.zero_le _, rfl⟩ :
      UInt32.ofNat (Table.probeStart t (SipHash.hashU32 k0 k1 key)).pos =
          UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key) 0).pos ∧
        (0 : UInt32) = UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key) 0).stride ∧
        (0 : UInt32) = (if (none : Option Nat).isSome then 1 else 0) ∧
        (∀ c, (none : Option Nat) = some c →
          (0 : UInt32) = UInt32.ofNat c ∧ c < t.buckets ∧
          (Table.isSpecial (t.ctrlAt c) = true ∨ t.buckets ≤ 8)) ∧
        0 ≤ N ∧
        Table.findOrFindInsertLoop t (Table.h2 (SipHash.hashU32 k0 k1 key)) key
            (Table.probeFuel t - 0)
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) 0) none =
          Table.findOrFindInsertIndex t (SipHash.hashU32 k0 k1 key) key)
    iframe Hruntime Hsp2 Hbelow Hout Hbody Hk0 Hk1 Hcont
