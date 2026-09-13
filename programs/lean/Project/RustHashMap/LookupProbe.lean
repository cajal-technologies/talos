import Project.RustHashMap.LookupHash

/-!
# The probe loops of the two lookup kernels

Absolute `func 12` is `HashMap::contains_key` and absolute `func 20` is
`HashMap::get`.  Both bodies walk the same probe sequence after the inline
hash.  This module proves the two loops.

* `twp_func9_probe` runs `func9Probe`, WAT lines 2470 to 2551 of
  `programs/rust/build/rust_hash_map/program.wat`.
* `twp_func17_probe` runs `func17Probe`, WAT lines 4959 to 5048.

Each theorem starts at the instruction that loads the control pointer out
of header word 0, which is the first instruction after the hash region.
Each theorem ends at one of the two exits of the loop.

## The register maps

Absolute `func 12` has eleven registers.  Register 0 is the map value on
entry and the control pointer after WAT 2472.  Register 1 is the key,
register 2 is the bucket mask, register 3 is the match mask, register 4
holds the tag lanes, register 5 holds the group word, registers 6 to 8 are
dead, register 9 is the probe position and register 10 is the stride.

Absolute `func 20` has fourteen registers.  Register 0 is the output slot.
Register 1 is the map value on entry, then the address of the bucket that
matched, then the discriminant of the answer.  Register 2 is the key,
register 3 is the bucket mask, register 4 is the match mask, register 5
holds the tag lanes, register 6 holds the group word, registers 7 to 9 are
dead, register 10 is the probe position, register 11 is the control
pointer, register 12 is the stride and register 13 is the value.

The brief of this task says that absolute `func 12` keeps no control
pointer.  That is wrong.  WAT 2470 to 2472 loads header word 0 into
register 0, over the map value, and WAT 2477 and WAT 2499 read it back.
The body loads the header word one time only.

## The two exits

Absolute `func 12` leaves through `i32.const 1` and `return` at WAT 2517,
or through `br_if 1` at WAT 2540.  The first exit is a return from the
whole function, so the hit continuation of `twp_func9_probe` takes the
machine at the `return` and the caller of the theorem does the return.
The second exit leaves the block of the body, so the theorem asks for the
branch target of that block.

Absolute `func 20` leaves through `br_if 3` at WAT 5006 into the value
read of WAT 5042 to 5046, or through `br_if 2` at WAT 5029.  Both exits
set register 1 to the discriminant, so the two continuations differ in the
value of that register and in the code that follows.

## The measure

`exists_first_empty_window_of_clean` gives the first window `N` that holds
an `EMPTY` byte.  The loop stops at or before window `N`, so `N - step` is
the measure of `twp_loop_wf_family`.  The invariant `lookupInv` carries the
step, the two machine registers that hold the position and the stride, and
the history: no earlier window holds an `EMPTY` byte and no earlier window
holds the key.  `find_none_of_inv` turns that history into
`Table.find ... = none` at the miss exit.
-/

namespace Project.RustHashMap.LookupProbe

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.LookupPures
open Project.RustHashMap.LookupHash
open scoped Wasm.SmallStep.Outcome

/-! ## The index and the invariant of both loops -/

/-- The index of the probe-loop family.  `step` is the window number of the
model.  The other four fields are the machine registers that the loop
writes.  The match mask and the group word are dead at the loop head, so
the invariant says nothing about them. -/
private structure LookupIdx where
  step : Nat
  pos : UInt32
  stride : UInt32
  wmask : UInt64
  wgroup : UInt64

/-- The invariant of both probe loops.  The position register and the
stride register track window `step`, and no earlier window holds an
`EMPTY` byte or the key. -/
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
`Func15Insert.lean:639`. -/
private theorem wordMove64 [WasmSmallStepGS hlc Universal.State]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 0 address value ⊢ pointsTo_u64 0 address' value := by
  rw [haddress]

/-- The three address facts that the offset-free `twp_load32_addr` asks
for.  Copy of `Func15Proof.lean:104`. -/
private theorem addr_facts (addr : UInt32)
    (h : addr.toNat + 4 ≤ UInt32.size) :
    (addr + 1).toNat = addr.toNat + 1 ∧ (addr + 2).toNat = addr.toNat + 2 ∧
      (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using Slices.byteOffset_toNat addr 1 (by omega),
    by simpa using Slices.byteOffset_toNat addr 2 (by omega),
    by simpa using Slices.byteOffset_toNat addr 3 (by omega)⟩

/-- `Group::match_empty` in the operand order of the compiled test. -/
private theorem swarMatchEmpty_wasm (x : UInt64) :
    (x &&& (x <<< 1)) &&& 9259542123273814144 = Table.swarMatchEmpty x :=
  rfl

/-- The loop stops at the first window with an `EMPTY` byte, so the walk
that the invariant records covers every window up to `N`. -/
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

/-- The next stride register, as a number. -/
private theorem stride_step (n : Nat) (hn : 8 * n < UInt32.size) :
    (8 : UInt32) + UInt32.ofNat (8 * n) = UInt32.ofNat (8 * (n + 1)) := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
    show (8 : UInt32).toNat = 8 from rfl]
  have hlt : 8 * n % UInt32.size = 8 * n := Nat.mod_eq_of_lt hn
  change (8 + 8 * n % 4294967296) % 4294967296 = 8 * (n + 1) % 4294967296
  omega

/-! ## Absolute `func 12`, local `func9`: `contains_key` -/

/-- The body of the `BitMaskIter` walk of `contains_key`, WAT 2497 to
2528. -/
@[reducible] private def func9WalkBody : Program :=
  [.block 0 0
      [.localGet 1, .localGet 0, .localGet 3, .ctzI64, .wrapI64, .const 3,
        .shrU, .localGet 9, .add, .localGet 2, .and, .const 3, .shl, .sub,
        .const 4294967288, .add, .load32 0, .ne, .br_if 0, .const 1, .ret],
    .localGet 3, .constI64 18446744073709551615, .addI64, .localGet 3,
    .andI64, .localTee 3, .eqzI64, .eqz, .br_if 0]

/-- The body of the probe loop of `contains_key`, WAT 2476 to 2550. -/
@[reducible] private def func9LoopBody : Program :=
  [.block 0 0
      [.localGet 0, .localGet 9, .add, .load64 0, .localTee 5, .localGet 4,
        .xorI64, .localTee 3, .constI64 18446744073709551615, .xorI64,
        .localGet 3, .constI64 18374403900871474943, .addI64, .andI64,
        .constI64 9259542123273814144, .andI64, .localTee 3, .eqzI64,
        .br_if 0, .loop 0 0 func9WalkBody],
    .localGet 5, .localGet 5, .constI64 1, .shlI64, .andI64,
    .constI64 9259542123273814144, .andI64, .eqzI64, .eqz, .br_if 1,
    .localGet 9, .localGet 10, .const 8, .add, .localTee 10, .add,
    .localGet 2, .and, .localSet 9, .br 0]

/-- The control load and the probe loop of `contains_key`, WAT 2470 to
2551. -/
@[reducible] private def func9Probe : Program :=
  [.localGet 0, .load32 0, .localSet 0, .const 0, .localSet 10,
    .loop 0 0 func9LoopBody]

set_option maxRecDepth 1048576 in
/-- The region is the tail of the block that `func9Block_shape` names. -/
theorem func9Probe_slice : func9Probe = func9Block.drop 181 := rfl

/-- The registers of `contains_key` inside the probe loop. -/
@[reducible] private def func9Locals (ctrl key : UInt32)
    (t : Table UInt32 UInt32) (wmask splat wgroup w6 w7 w8 : UInt64)
    (pos stride : UInt32) : Locals :=
  { params := [.i32 ctrl, .i32 key],
    locals := [.i32 (UInt32.ofNat (t.buckets - 1)), .i64 wmask, .i64 splat,
      .i64 wgroup, .i64 w6, .i64 w7, .i64 w8, .i32 pos, .i32 stride],
    values := [] }

/-- Where the walk of WAT 2494 to 2529 leaves the machine.  With no match
it leaves the block of WAT 2476, with register 3 at zero.  With a match it
stands at the `return` of WAT 2518, with `1` on the operand stack. -/
private def func9WalkExit (ctrl key : UInt32) (t : Table UInt32 UInt32)
    (splat wgroup w6 w7 w8 : UInt64) (P : Nat) (stride : UInt32)
    (noneCode : Program) (noneControls : List ControlFrame)
    (noneValues : List Value) (arity : Nat) (remainder : List Value)
    (calls : List CallFrame) (r : Option Nat)
    (params localValues : List Value) (cs : List ControlFrame) :
    Expr Universal.State :=
  match r with
  | none =>
      .running ⟨{ func9Locals ctrl key t 0 splat wgroup w6 w7 w8
            (UInt32.ofNat P) stride with values := noneValues },
          noneCode, arity, remainder, noneControls, calls⟩
  | some _ =>
      .running ⟨⟨params, localValues, [.i32 1]⟩, [Instruction.ret],
          arity, remainder, cs, calls⟩

set_option maxHeartbeats 2000000 in
/-- The `BitMaskIter` walk of `contains_key`, WAT 2494 to 2529.  It tests
the key of every byte that `match_tag` flags, in ascending order.  The walk
either leaves the block with no match, or stands at the `return` of the
found arm. -/
private theorem twp_func9_walk [WasmSmallStepGS hlc Universal.State]
    {ctrl key : UInt32} {splat wgroup w6 w7 w8 : UInt64} {stride : UInt32}
    {t : Table UInt32 UInt32} {hashf : UInt32 → UInt64}
    {m P : Nat} {msk : UInt64}
    {arity : Nat} {remainder : List Value}
    {b3 : ControlFrame} {rest : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    {noneCode : Program} {noneControls : List ControlFrame}
    {noneValues : List Value}
    (hlayout : Table.Layout hashf t)
    (hm32 : m ≤ 32) (hbShape : t.buckets = 2 ^ m)
    (hP : P < t.buckets) (hroom : 8 * t.buckets ≤ ctrl.toNat)
    (hb3Kind : b3.kind = ControlKind.block)
    (hnoneTarget : branchTarget? arity 0 (b3 :: rest) ([] : List Value) =
      some (noneCode, noneControls, noneValues))
    (hmsk : msk &&& Table.REP80 = msk)
    (hfull : ∀ j ∈ Table.setBytes msk,
      (t.slotAt ((P + j) % t.buckets)).isSome = true) :
    iprop(
      Table.slotsBefore 0 ctrl t.slots ∗
      (∀ (r : Option Nat) (params localValues : List Value)
          (cs : List ControlFrame),
        ⌜(Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) = r⌝ -∗
        Table.slotsBefore 0 ctrl t.slots -∗
        WP (func9WalkExit ctrl key t splat wgroup w6 w7 w8 P stride
              noneCode noneControls noneValues arity remainder calls r
              params localValues cs) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨{ func9Locals ctrl key t msk splat wgroup w6 w7 w8
              (UInt32.ofNat P) stride with values := [Value.i64 msk] },
            [Instruction.eqzI64, Instruction.br_if 0,
              Instruction.loop 0 0 func9WalkBody], arity, remainder,
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
    ihave Hgo := Hexit $$ %(none : Option Nat) %([] : List Value)
      %([] : List Value) %rest %hnone0 Hslots
    isimp only [func9WalkExit] at Hgo
    iexact Hgo
  iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hmne])
  iapply Wasm.SmallStep.twp_brIfZero
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := UInt64)
    (measure := fun q => (Table.setBytes q).length)
    (locals := fun q => func9Locals ctrl key t q splat wgroup w6 w7 w8
      (UInt32.ofNat P) stride)
    (I := fun q => iprop(
      ⌜q &&& Table.REP80 = q ∧ q ≠ 0 ∧
        (∀ j, Table.hasBit q j = true → Table.hasBit msk j = true) ∧
        (Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) =
          (Table.setBytes q).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key)⌝ ∗
      Table.slotsBefore 0 ctrl t.slots ∗
      (∀ (r : Option Nat) (params localValues : List Value)
          (cs : List ControlFrame),
        ⌜(Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) = r⌝ -∗
        Table.slotsBefore 0 ctrl t.slots -∗
        WP (func9WalkExit ctrl key t splat wgroup w6 w7 w8 P stride
              noneCode noneControls noneValues arity remainder calls r
              params localValues cs) @ s; E [{ Φ }])))
    (initial := msk)
    (initialLocals := { func9Locals ctrl key t msk splat wgroup w6 w7 w8
      (UInt32.ofNat P) stride with values := [] })
    rfl rfl
  · intro q
    iintro Hrec ⟨%hq, Hslots, Hexit⟩
    obtain ⟨hqmask, hqne, hqsub, hqfind⟩ := hq
    simp only [Wasm.SmallStep.loopBodyExpr, func9WalkBody, func9Locals]
    have hlow : Table.lowestSetByte q = some (ctz64 64 q / 8) :=
      Table.lowestSetByte_eq_ctz hqmask hqne
    have hnext : Table.setBytes q =
        ctz64 64 q / 8 ::
          Table.setBytes (q &&& (q + 18446744073709551615)) :=
      Table.setBytes_iterNext hqmask hlow
    have hidx := Table.matchIndex_of_wasm t hm32 hbShape hqmask hlow P
    have hbpos : 0 < t.buckets := hlayout.pos
    have hctrlLt : ctrl.toNat < 4294967296 := ctrl.toBitVec.isLt
    have hsize32 : UInt32.size = 4294967296 := rfl
    have hsz : (8 : Nat) * t.buckets ≤ ctrl.toNat := hroom
    have hIlt : (P + ctz64 64 q / 8) % t.buckets < t.buckets :=
      Nat.mod_lt _ hbpos
    have hIlen : (P + ctz64 64 q / 8) % t.buckets < t.slots.length := by
      rw [hlayout.slots_len]; exact hIlt
    have hidxEq : (UInt32.ofNat P +
        (UInt64.ofNat (ctz64 64 q)).toUInt32 >>> 3) &&&
        UInt32.ofNat (t.buckets - 1)
        = UInt32.ofNat ((P + ctz64 64 q / 8) % t.buckets) := by
      rw [UInt32.add_comm, ← hidx, UInt32.ofNat_toNat]
    have hbaddrNat :
        (Table.bucketAddr ctrl ((P + ctz64 64 q / 8) % t.buckets)).toNat
          = ctrl.toNat - 8 * ((P + ctz64 64 q / 8) % t.buckets + 1) :=
      Table.bucketAddr_toNat ctrl hIlt hroom
    have haddr : (4294967288 : UInt32) +
        (ctrl - (UInt32.ofNat ((P + ctz64 64 q / 8) % t.buckets) <<< 3))
        = Table.bucketAddr ctrl ((P + ctz64 64 q / 8) % t.buckets) := by
      rw [UInt32.add_comm, Table.bucketAddr_of_wasm,
        UInt32.toNat_ofNat_of_lt'
          (by omega : (P + ctz64 64 q / 8) % t.buckets < UInt32.size)]
      rfl
    obtain ⟨ha1, ha2, ha3⟩ := addr_facts
      (Table.bucketAddr ctrl ((P + ctz64 64 q / 8) % t.buckets)) (by omega)
    wasm_twp_pures [twp_block twp_localGet twp_localGet twp_localGet
      twp_ctzI64 twp_wrapI64 twp_const twp_shrU twp_localGet twp_add
      twp_localGet twp_and twp_const twp_shl twp_sub twp_const twp_add]
    isimp only [wrapWasm, shrU32Wasm3, hidxEq, shl32Wasm3, haddr]
    have hj0q : ctz64 64 q / 8 ∈ Table.setBytes q := by
      rw [hnext]; exact List.mem_cons_self
    have hj0msk : ctz64 64 q / 8 ∈ Table.setBytes msk := by
      simp only [Table.setBytes, List.mem_filter, List.mem_range] at hj0q ⊢
      exact ⟨hj0q.1, hqsub _ hj0q.2⟩
    have hslotSome := hfull _ hj0msk
    obtain ⟨k', v', hslotEq⟩ :
        ∃ k' v', t.slotAt ((P + ctz64 64 q / 8) % t.buckets)
          = some (k', v') := by
      cases hc : t.slotAt ((P + ctz64 64 q / 8) % t.buckets) with
      | none => rw [hc] at hslotSome; exact absurd hslotSome (by decide)
      | some kv => exact ⟨kv.1, kv.2, rfl⟩
    have hslotsGet :
        t.slots[(P + ctz64 64 q / 8) % t.buckets]'hIlen = some (k', v') := by
      rw [← hslotEq, Table.slotAt, List.getD_eq_getElem]
    ihave ⟨Hpre, Hcell, Hpost⟩ :=
      (Table.slotsBefore_focus 0 ctrl t.slots hIlen).mp $$ Hslots
    isimp only [hslotsGet, Table.slotCell] at Hcell
    ihave ⟨Hkey, Hval⟩ := Hcell
    wasm_twp_rebind Wasm.SmallStep.twp_load32_addr k' ha1 ha2 ha3 with Hkey
    wasm_twp_pures [twp_ne]
    ihave Hslots : Table.slotsBefore 0 ctrl t.slots $$
      [Hpre Hkey Hval Hpost]
    · iapply (Table.slotsBefore_focus 0 ctrl t.slots hIlen).mpr
      isimp only [hslotsGet, Table.slotCell]
      iframe Hpre Hkey Hval Hpost
    by_cases hkey : key = k'
    · have hkeyIs : t.keyIs ((P + ctz64 64 q / 8) % t.buckets) key = true := by
        simp only [Table.keyIs, hslotEq, beq_iff_eq]
        exact hkey.symm
      have hfindq : (Table.setBytes q).find?
          (fun j => t.keyIs ((P + j) % t.buckets) key)
            = some (ctz64 64 q / 8) := by
        rw [hnext]
        exact List.find?_cons_of_pos (by simpa using hkeyIs)
      isimp only [if_neg (by simpa using hkey : ¬ key ≠ k')]
      iapply Wasm.SmallStep.twp_brIfZero
      wasm_twp_pures [twp_const]
      ihave Hgo := Hexit $$ %(some (ctz64 64 q / 8)) %_ %_ %_
        %(hqfind.trans hfindq) Hslots
      isimp only [func9WalkExit] at Hgo
      iexact Hgo
    · have hkeyIs :
          t.keyIs ((P + ctz64 64 q / 8) % t.buckets) key = false := by
        simp only [Table.keyIs, hslotEq, beq_eq_false_iff_ne, ne_eq]
        exact fun h => hkey h.symm
      have hfindq : (Table.setBytes q).find?
          (fun j => t.keyIs ((P + j) % t.buckets) key) =
            (Table.setBytes (q &&& (q + 18446744073709551615))).find?
              (fun j => t.keyIs ((P + j) % t.buckets) key) := by
        rw [hnext, List.find?_cons_of_neg (by simpa using hkeyIs)]
      have hcomm : (q + 18446744073709551615) &&& q
          = q &&& (q + 18446744073709551615) := UInt64.and_comm _ _
      have hnextMask : (q &&& (q + 18446744073709551615)) &&& Table.REP80
          = q &&& (q + 18446744073709551615) := by
        rw [UInt64.and_assoc, UInt64.and_comm (q + 18446744073709551615),
          ← UInt64.and_assoc, hqmask]
      have hnextSub : ∀ j,
          Table.hasBit (q &&& (q + 18446744073709551615)) j = true →
            Table.hasBit msk j = true := by
        intro j hj
        rw [Table.hasBit_iterNext hqmask hlow j, Bool.and_eq_true] at hj
        exact hqsub _ hj.1
      isimp only [if_pos (by simpa using hkey : key ≠ k')]
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      wasm_twp_pures [twp_localGet twp_constI64 twp_addI64 twp_localGet
        twp_andI64]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      isimp only [hcomm]
      by_cases hzero : q &&& (q + 18446744073709551615) = 0
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
        ihave Hgo := Hexit $$ %(none : Option Nat) %([] : List Value)
          %([] : List Value) %rest %hnone Hslots
        isimp only [func9WalkExit, func9Locals, hnone3.1, hnone3.2.1,
          hnone3.2.2] at Hgo
        iexact Hgo
      · iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hzero])
        iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
        simp only [List.take_zero, List.nil_append]
        ihave Hback := Hrec $$ %(q &&& (q + 18446744073709551615))
          %(by rw [hnext]; simp)
        iapply Hback
        isplitl_pureexact ⟨hnextMask, hzero, hnextSub, hqfind.trans hfindq⟩
        iframe Hslots Hexit
  · isplitl_pureexact ⟨hmsk, hmne, fun _ h => h, rfl⟩
    iframe Hslots Hexit

set_option maxHeartbeats 2000000 in
/-- The probe loop of `contains_key`, WAT 2470 to 2551.  The theorem starts
at the load of header word 0 and ends at one of the two exits.  The hit
exit stands at the `return` of WAT 2518 with `1` on the operand stack.  The
miss exit leaves the block of the body, which pushes `0` at WAT 2553. -/
theorem twp_func9_probe [WasmSmallStepGS hlc Universal.State]
    (map key ctrl : UInt32) (k0 k1 : UInt64) (t : Table UInt32 UInt32)
    (w5 w6 w7 w8 : UInt64) (l10 : Value)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {missCode : Program} {missControls : List ControlFrame}
    {missValues : List Value}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hwf : Table.WF (SipHash.hashU32 k0 k1) t) (hclean : Table.Clean t)
    (hmap : map.toNat + 32 < UInt32.size)
    (hmiss : ∀ f : ControlFrame,
      branchTarget? arity 1 (f :: controls) ([] : List Value) =
        some (missCode, missControls, missValues)) :
    iprop(
      Table.TableBody 0 map ctrl t ∗
      (∀ (params localValues : List Value) (cs : List ControlFrame),
        ⌜Table.containsKey (SipHash.hashU32 k0 k1) t key = true⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running ⟨⟨params, localValues, [.i32 1]⟩, [Instruction.ret],
              arity, remainder, cs, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) ∗
      (∀ (params localValues : List Value),
        ⌜Table.containsKey (SipHash.hashU32 k0 k1) t key = false⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running ⟨⟨params, localValues, missValues⟩, missCode,
              arity, remainder, missControls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 map, .i32 key],
              [.i32 (UInt32.ofNat (t.buckets - 1)),
                .i64 (SipHash.hashU32Low k0 k1 key),
                .i64 (Table.repeatByte
                  (Table.h2 (SipHash.hashU32 k0 k1 key))),
                .i64 w5, .i64 w6, .i64 w7, .i64 w8,
                .i32 (UInt32.ofNat (t.buckets - 1) &&&
                  (SipHash.hashU32 k0 k1 key).toUInt32), l10],
              []⟩,
            func9Probe, arity, remainder, controls, calls⟩
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
  have hc1 : (map + 1 : UInt32).toNat = map.toNat + 1 := by
    simpa using Slices.byteOffset_toNat map 1 (by omega)
  have hc2 : (map + 2 : UInt32).toNat = map.toNat + 2 := by
    simpa using Slices.byteOffset_toNat map 2 (by omega)
  have hc3 : (map + 3 : UInt32).toNat = map.toNat + 3 := by
    simpa using Slices.byteOffset_toNat map 3 (by omega)
  simp only [func9Probe]
  isimp only [Table.TableBody, Table.tableHeader] at Hbody
  icases Hbody with ⟨%hctrlBound, ⟨H0, H4, H8, H12⟩, Hctrl, Hslots⟩
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32_addr ctrl hc1 hc2 hc3 with H0
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave Hbody : Table.TableBody 0 map ctrl t $$
    [H0 H4 H8 H12 Hctrl Hslots]
  · unfold Table.TableBody Table.tableHeader
    isplitl_pureexact hctrlBound
    iframe H0 H4 H8 H12 Hctrl Hslots
  isimp only [hprobe]
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := LookupIdx)
    (measure := fun i => N - i.step)
    (locals := fun i =>
      func9Locals ctrl key t i.wmask
        (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
        i.wgroup w6 w7 w8 i.pos i.stride)
    (I := fun i => iprop(
      ⌜lookupInv t (SipHash.hashU32 k0 k1 key) key N i⌝ ∗
      Table.TableBody 0 map ctrl t ∗
      (∀ (params localValues : List Value) (cs : List ControlFrame),
        ⌜Table.containsKey (SipHash.hashU32 k0 k1) t key = true⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running ⟨⟨params, localValues, [.i32 1]⟩, [Instruction.ret],
              arity, remainder, cs, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) ∗
      (∀ (params localValues : List Value),
        ⌜Table.containsKey (SipHash.hashU32 k0 k1) t key = false⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running ⟨⟨params, localValues, missValues⟩, missCode,
              arity, remainder, missControls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }])))
    (initial := ⟨0, UInt32.ofNat
        (Table.probeStart t (SipHash.hashU32 k0 k1 key)).pos, 0,
      SipHash.hashU32Low k0 k1 key, w5⟩)
    (initialLocals :=
      { params := [Value.i32 ctrl, Value.i32 key],
        locals :=
          [Value.i32 (UInt32.ofNat (t.buckets - 1)),
            Value.i64 (SipHash.hashU32Low k0 k1 key),
            Value.i64 (Table.repeatByte
              (Table.h2 (SipHash.hashU32 k0 k1 key))),
            Value.i64 w5, Value.i64 w6, Value.i64 w7, Value.i64 w8,
            Value.i32 (UInt32.ofNat
              (Table.probeStart t (SipHash.hashU32 k0 k1 key)).pos),
            Value.i32 0],
        values := [] })
    rfl rfl
  · intro i
    iintro Hrec ⟨%hinv, Hbody, Hhit, Hmiss⟩
    obtain ⟨histep, hipos, histride, hihist⟩ := hinv
    have hposLt :
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos
          < t.buckets := hlayout.probe_lt _ _
    simp only [Wasm.SmallStep.loopBodyExpr, func9LoopBody, func9Locals]
    ihave ⟨%hctrlB2, Hheader, ⟨Hpre, ⟨%hgbound, Hgroup⟩, Hpost⟩, Hslots⟩ :=
      (Table.TableBody_groupAt 0 map ctrl t hlayout hposLt).mp $$ Hbody
    have hgroupAddr : ctrl + UInt32.ofNat
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos
          = i.pos + ctrl + 0 := by
      rw [UInt32.add_zero, hipos, UInt32.add_comm]
    have hgf := FrameCells.offset_facts64 (i.pos + ctrl) 0 0 rfl
      (by rw [← UInt32.add_zero (i.pos + ctrl), ← hgroupAddr]; omega)
    ihave Hgroup := wordMove64 hgroupAddr $$ Hgroup
    wasm_twp_pures [twp_block twp_localGet twp_localGet twp_add]
    wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := i.pos + ctrl)
      (offset := 0)
      (Table.groupWord (Table.groupAt t
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos))
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
    iapply twp_func9_walk (hashf := SipHash.hashU32 k0 k1) (m := m)
      (ctrl := ctrl) (key := key) (t := t)
      (splat := Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
      (wgroup := Table.groupWord (Table.groupAt t
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos))
      (w6 := w6) (w7 := w7) (w8 := w8) (stride := i.stride)
      (P := (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos)
      (msk := Table.swarMatchTag (Table.h2 (SipHash.hashU32 k0 k1 key))
        (Table.groupWord (Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos)))
    case hlayout => exact hlayout
    case hm32 => exact hm32
    case hbShape => exact hbShape
    case hP => exact hposLt
    case hroom => exact hctrlB2
    case hb3Kind => rfl
    case hnoneTarget => rfl
    case hmsk => exact Table.swarMatchTag_and_REP80 _ _
    case hfull =>
      exact fun j hj =>
        slotAt_isSome_of_mem_matchTag hlayout _ i.step hj
    isplitl_exacts [Hslots]
    iintro %r %params %localValues %cs %hfind Hslots
    have hctrlLen :
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + 8
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
    | some j0 =>
      simp only [func9WalkExit]
      have hmodelFind : (Table.matchTag
          (Table.h2 (SipHash.hashU32 k0 k1 key))
          (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos)).find?
            (fun j => t.keyIs
              (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j)
                % t.buckets) key) = some j0 :=
        (hlayout.find?_setBytes_eq hposLt key).symm.trans hfind
      obtain ⟨v, hslot⟩ :=
        (Table.keyIs_iff t _ key).mp (Table.tagFind_some hmodelFind).2.2
      have hjLt :
          ((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j0)
            % t.buckets < t.buckets := Nat.mod_lt _ hlayout.pos
      have hck : Table.containsKey (SipHash.hashU32 k0 k1) t key = true := by
        simp only [Table.containsKey, hlayout.find_of_slot hjLt hslot,
          Option.isSome_some]
      ihave Hgo := Hhit $$ %params %localValues %cs %hck Hbody
      iexact Hgo
    | none =>
      simp only [func9WalkExit, List.take_zero,
        List.drop_zero, List.nil_append]
      have hmodelFind : (Table.matchTag
          (Table.h2 (SipHash.hashU32 k0 k1 key))
          (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos)).find?
            (fun j => t.keyIs
              (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos + j)
                % t.buckets) key) = none :=
        (hlayout.find?_setBytes_eq hposLt key).symm.trans hfind
      have hg8 : (Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos).length
            = 8 := Table.groupAt_length t _
      have hctrls : ∀ b ∈ Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos,
            Table.IsCtrl b := hlayout.isCtrl_groupAt hclean hposLt
      wasm_twp_pures [twp_localGet twp_localGet twp_constI64 twp_shlI64
        twp_andI64 twp_constI64 twp_andI64]
      isimp only [shl64Wasm1, swarMatchEmpty_wasm]
      by_cases hemp : Table.matchEmpty (Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos) = true
      · have hne0 : Table.swarMatchEmpty (Table.groupWord (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos))
              ≠ 0 := by
          intro hc
          rw [(Table.swarMatchEmpty_eq_zero_iff hg8 hctrls).mp hc] at hemp
          exact absurd hemp (by decide)
        iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hne0])
        iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
          (hmiss _)
        have hfindNone : Table.find t (SipHash.hashU32 k0 k1 key) key
            = none :=
          find_none_of_inv hNfuel hNmin
            ⟨histep, hipos, histride, hihist⟩ hemp hmodelFind
        have hck : Table.containsKey (SipHash.hashU32 k0 k1) t key
            = false := by
          simp only [Table.containsKey, hfindNone, Option.isSome_none]
        ihave Hgo := Hmiss $$ %_ %_ %hck Hbody
        iexact Hgo
      · rw [Bool.not_eq_true] at hemp
        have hzero : Table.swarMatchEmpty (Table.groupWord (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos))
              = 0 := (Table.swarMatchEmpty_eq_zero_iff hg8 hctrls).mpr hemp
        have hstepLt : i.step < N := by
          rcases Nat.eq_or_lt_of_le histep with heq | hlt
          · rw [heq] at hemp
            rw [hNemp'] at hemp
            exact absurd hemp (by decide)
          · exact hlt
        have hclt : ctrl.toNat < 4294967296 := ctrl.toBitVec.isLt
        have hfuelEq : Table.probeFuel t = t.buckets / 8 + 1 := rfl
        have hstrideB : 8 * (i.step + 1) < UInt32.size := by
          change 8 * (i.step + 1) < 4294967296
          omega
        have hnextStride : (8 : UInt32) + i.stride
            = UInt32.ofNat (8 * (i.step + 1)) := by
          rw [histride]
          exact stride_step i.step (by omega)
        have hstrideSum : UInt32.ofNat
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).stride
              + 8 = UInt32.ofNat (8 * (i.step + 1)) := by
          rw [probeSeq_stride, UInt32.add_comm]
          exact stride_step i.step (by omega)
        have hnextPos : (UInt32.ofNat (8 * (i.step + 1)) +
            UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
              i.step).pos) &&& UInt32.ofNat (t.buckets - 1)
            = UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                (i.step + 1)).pos := by
          rw [UInt32.add_comm, ← hstrideSum,
            show Table.probeSeq t (SipHash.hashU32 k0 k1 key) (i.step + 1)
              = (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).next t
              from rfl,
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
          %((⟨i.step + 1,
              UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                (i.step + 1)).pos,
              UInt32.ofNat (8 * (i.step + 1)), 0,
              Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.step).pos)⟩
            : LookupIdx))
          %(show N - (i.step + 1) < N - i.step by omega)
        iapply Hback
        have hnextInv : lookupInv t (SipHash.hashU32 k0 k1 key) key N
            ⟨i.step + 1,
              UInt32.ofNat (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                (i.step + 1)).pos,
              UInt32.ofNat (8 * (i.step + 1)), 0,
              Table.groupWord (Table.groupAt t
                (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                  i.step).pos)⟩ := by
          refine ⟨show i.step + 1 ≤ N by omega, rfl, rfl, ?_⟩
          intro mm hmm
          have hmm' : mm < i.step + 1 := hmm
          rcases Nat.lt_or_ge mm i.step with hlt | hge
          · exact hihist mm hlt
          · have hme : mm = i.step := by omega
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
          SipHash.hashU32Low k0 k1 key, w5⟩)
    iframe Hbody Hhit Hmiss

/-! ## The `get` kernel, absolute `func 20` -/

/-- The body of the walk over the match mask of `get`, WAT 4987 to
5015. -/
@[reducible] private def func17WalkBody : Program :=
  [.localGet 2, .localGet 11, .localGet 4, .ctzI64, .wrapI64, .const 3,
    .shrU, .localGet 10, .add, .localGet 3, .and, .const 3, .shl, .sub,
    .localTee 1, .const 4294967288, .add, .load32 0, .eq, .br_if 3,
    .localGet 4, .constI64 18446744073709551615, .addI64, .localGet 4,
    .andI64, .localTee 4, .eqzI64, .eqz, .br_if 0]

/-- The body of the probe loop of `get`, WAT 4966 to 5039. -/
@[reducible] private def func17LoopBody : Program :=
  [.block 0 0
      [.localGet 11, .localGet 10, .add, .load64 0, .localTee 6,
        .localGet 5, .xorI64, .localTee 4,
        .constI64 18446744073709551615, .xorI64, .localGet 4,
        .constI64 18374403900871474943, .addI64, .andI64,
        .constI64 9259542123273814144, .andI64, .localTee 4, .eqzI64,
        .br_if 0, .loop 0 0 func17WalkBody],
    .const 0, .localSet 1, .localGet 6, .localGet 6, .constI64 1,
    .shlI64, .andI64, .constI64 9259542123273814144, .andI64, .eqzI64,
    .eqz, .br_if 2, .localGet 10, .localGet 12, .const 8, .add,
    .localTee 12, .add, .localGet 3, .and, .localSet 10, .br 0]

/-- The control load, the probe loop and the value load of `get`, WAT
4959 to 5048. -/
@[reducible] private def func17Probe : Program :=
  [.localGet 1, .load32 0, .localSet 11, .const 0, .localSet 12,
    .block 0 0 [.loop 0 0 func17LoopBody],
    .localGet 1, .const 4294967292, .add, .load32 0, .localSet 13,
    .const 1, .localSet 1]

set_option maxRecDepth 1048576 in
/-- The region is the tail of the block that `func17Block_shape` names. -/
theorem func17Probe_slice : func17Probe = func17Block.drop 178 := rfl

/-- The registers of `get` inside the probe loop. -/
@[reducible] private def func17Locals (out base key ctrl : UInt32)
    (t : Table UInt32 UInt32) (wmask splat wgroup w7 w8 w9 : UInt64)
    (pos stride : UInt32) (v13 : Value) : Locals :=
  { params := [.i32 out, .i32 base, .i32 key],
    locals := [.i32 (UInt32.ofNat (t.buckets - 1)), .i64 wmask, .i64 splat,
      .i64 wgroup, .i64 w7, .i64 w8, .i64 w9, .i32 pos, .i32 ctrl,
      .i32 stride, v13],
    values := [] }

/-- Where the walk of WAT 4984 to 5016 leaves the machine.  With no match
it leaves the block of WAT 4966, with register 4 at zero.  With a match it
leaves the block of WAT 4964, with register 1 at the bucket base. -/
private def func17WalkExit (out key ctrl : UInt32)
    (t : Table UInt32 UInt32) (splat wgroup w7 w8 w9 : UInt64) (P : Nat)
    (stride : UInt32) (v13 : Value)
    (noneCode : Program) (noneControls : List ControlFrame)
    (noneValues : List Value)
    (hitCode : Program) (hitControls : List ControlFrame)
    (hitValues : List Value) (arity : Nat) (remainder : List Value)
    (calls : List CallFrame) (r : Option Nat) (q : UInt64)
    (base' : UInt32) : Expr Universal.State :=
  match r with
  | none =>
      .running ⟨{ func17Locals out base' key ctrl t 0 splat wgroup w7 w8 w9
            (UInt32.ofNat P) stride v13 with values := noneValues },
          noneCode, arity, remainder, noneControls, calls⟩
  | some j =>
      .running ⟨{ func17Locals out
            (ctrl - (UInt32.ofNat ((P + j) % t.buckets) <<< (3 : UInt32)))
            key ctrl t q splat wgroup w7 w8 w9 (UInt32.ofNat P) stride v13
            with values := hitValues },
          hitCode, arity, remainder, hitControls, calls⟩

set_option maxHeartbeats 2000000 in
/-- The walk over the match mask of `get`, WAT 4984 to 5016.  The walk
reads one key for each set byte of the mask.  With a match it leaves the
block of WAT 4964 through the branch of WAT 5006, and register 1 holds the
bucket base.  With no match it leaves the block of WAT 4966 with register
4 at zero. -/
private theorem twp_func17_walk [WasmSmallStepGS hlc Universal.State]
    {out base key ctrl stride : UInt32} {v13 : Value}
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
      (∀ (r : Option Nat) (q : UInt64) (base' : UInt32),
        ⌜(Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) = r⌝ -∗
        Table.slotsBefore 0 ctrl t.slots -∗
        WP (func17WalkExit out key ctrl t splat wgroup w7 w8 w9 P stride
              v13 noneCode noneControls noneValues hitCode hitControls
              hitValues arity remainder calls r q base')
          @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨{ func17Locals out base key ctrl t msk splat wgroup w7 w8 w9
              (UInt32.ofNat P) stride v13 with values := [Value.i64 msk] },
            [Instruction.eqzI64, Instruction.br_if 0,
              Instruction.loop 0 0 func17WalkBody], arity, remainder,
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
    ihave Hgo := Hexit $$ %(none : Option Nat) %(0 : UInt64) %base
      %hnone0 Hslots
    isimp only [func17WalkExit] at Hgo
    iexact Hgo
  iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hmne])
  iapply Wasm.SmallStep.twp_brIfZero
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := UInt64 × UInt32)
    (measure := fun p => (Table.setBytes p.1).length)
    (locals := fun p => func17Locals out p.2 key ctrl t p.1 splat wgroup
      w7 w8 w9 (UInt32.ofNat P) stride v13)
    (I := fun p => iprop(
      ⌜p.1 &&& Table.REP80 = p.1 ∧ p.1 ≠ 0 ∧
        (∀ j, Table.hasBit p.1 j = true → Table.hasBit msk j = true) ∧
        (Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) =
          (Table.setBytes p.1).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key)⌝ ∗
      Table.slotsBefore 0 ctrl t.slots ∗
      (∀ (r : Option Nat) (q : UInt64) (base' : UInt32),
        ⌜(Table.setBytes msk).find?
            (fun j => t.keyIs ((P + j) % t.buckets) key) = r⌝ -∗
        Table.slotsBefore 0 ctrl t.slots -∗
        WP (func17WalkExit out key ctrl t splat wgroup w7 w8 w9 P stride
              v13 noneCode noneControls noneValues hitCode hitControls
              hitValues arity remainder calls r q base')
          @ s; E [{ Φ }])))
    (initial := (msk, base))
    (initialLocals := { func17Locals out base key ctrl t msk splat wgroup
      w7 w8 w9 (UInt32.ofNat P) stride v13 with values := [] })
    rfl rfl
  · intro p
    iintro Hrec ⟨%hq, Hslots, Hexit⟩
    obtain ⟨hqmask, hqne, hqsub, hqfind⟩ := hq
    simp only [Wasm.SmallStep.loopBodyExpr, func17WalkBody, func17Locals]
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
    obtain ⟨ha1, ha2, ha3⟩ := addr_facts
      (Table.bucketAddr ctrl ((P + ctz64 64 p.1 / 8) % t.buckets))
      (by omega)
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_ctzI64
      twp_wrapI64 twp_const twp_shrU twp_localGet twp_add twp_localGet
      twp_and twp_const twp_shl twp_sub]
    isimp only [wrapWasm, shrU32Wasm3, hidxEq, shl32Wasm3]
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
      ihave Hgo := Hexit $$ %(some (ctz64 64 p.1 / 8)) %p.1 %(0 : UInt32)
        %(hqfind.trans hfindq) Hslots
      isimp only [func17WalkExit] at Hgo
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
          %(ctrl - (UInt32.ofNat ((P + ctz64 64 p.1 / 8) % t.buckets) <<<
            (3 : UInt32))) %hnone Hslots
        isimp only [func17WalkExit, func17Locals, hnone3.1, hnone3.2.1,
          hnone3.2.2] at Hgo
        iexact Hgo
      · iapply Wasm.SmallStep.twp_eqzI64 (result := 0) (by rw [if_neg hzero])
        iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        ihave Hback := Hrec $$
          %((p.1 &&& (p.1 + 18446744073709551615),
            ctrl - (UInt32.ofNat ((P + ctz64 64 p.1 / 8) % t.buckets) <<<
              (3 : UInt32))) : UInt64 × UInt32)
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
/-- The probe loop of `get`, WAT 4959 to 5048.  The theorem starts at the
load of header word 0 and ends at one of the two exits.  The hit exit
falls through the value read of WAT 5042 to 5048, so register 1 holds 1
and register 13 holds the value.  The miss exit leaves the block of the
body with register 1 at zero. -/
theorem twp_func17_probe [WasmSmallStepGS hlc Universal.State]
    (out map key ctrl : UInt32) (k0 k1 : UInt64) (t : Table UInt32 UInt32)
    (w6 w7 w8 w9 : UInt64) (l11 l12 l13 : Value)
    {cont : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {missCode : Program} {missControls : List ControlFrame}
    {missValues : List Value}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hwf : Table.WF (SipHash.hashU32 k0 k1) t) (hclean : Table.Clean t)
    (hmap : map.toNat + 32 < UInt32.size)
    (hmiss : ∀ f g : ControlFrame,
      branchTarget? arity 2 (f :: g :: controls) ([] : List Value) =
        some (missCode, missControls, missValues)) :
    iprop(
      Table.TableBody 0 map ctrl t ∗
      (∀ (v : UInt32) (wmask wgroup : UInt64) (pos stride : UInt32),
        ⌜Table.get (SipHash.hashU32 k0 k1) t key = some v⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running
            ⟨func17Locals out 1 key ctrl t wmask
                (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
                wgroup w7 w8 w9 pos stride (.i32 v),
              cont, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }]) ∗
      (∀ (wmask wgroup : UInt64) (pos stride : UInt32),
        ⌜Table.get (SipHash.hashU32 k0 k1) t key = none⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running
            ⟨{ func17Locals out 0 key ctrl t wmask
                  (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
                  wgroup w7 w8 w9 pos stride l13 with
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
                l11, l12, l13],
              []⟩,
            func17Probe ++ cont, arity, remainder, controls, calls⟩
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
  have hc1 : (map + 1 : UInt32).toNat = map.toNat + 1 := by
    simpa using Slices.byteOffset_toNat map 1 (by omega)
  have hc2 : (map + 2 : UInt32).toNat = map.toNat + 2 := by
    simpa using Slices.byteOffset_toNat map 2 (by omega)
  have hc3 : (map + 3 : UInt32).toNat = map.toNat + 3 := by
    simpa using Slices.byteOffset_toNat map 3 (by omega)
  simp only [func17Probe, List.cons_append, List.nil_append]
  isimp only [Table.TableBody, Table.tableHeader] at Hbody
  icases Hbody with ⟨%hctrlBound, ⟨H0, H4, H8, H12⟩, Hctrl, Hslots⟩
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32_addr ctrl hc1 hc2 hc3 with H0
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave Hbody : Table.TableBody 0 map ctrl t $$
    [H0 H4 H8 H12 Hctrl Hslots]
  · unfold Table.TableBody Table.tableHeader
    isplitl_pureexact hctrlBound
    iframe H0 H4 H8 H12 Hctrl Hslots
  isimp only [hprobe]
  wasm_twp_pures [twp_block]
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := LookupIdx × UInt32)
    (measure := fun i => N - i.1.step)
    (locals := fun i =>
      func17Locals out i.2 key ctrl t i.1.wmask
        (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
        i.1.wgroup w7 w8 w9 i.1.pos i.1.stride l13)
    (I := fun i => iprop(
      ⌜lookupInv t (SipHash.hashU32 k0 k1 key) key N i.1⌝ ∗
      Table.TableBody 0 map ctrl t ∗
      (∀ (v : UInt32) (wmask wgroup : UInt64) (pos stride : UInt32),
        ⌜Table.get (SipHash.hashU32 k0 k1) t key = some v⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running
            ⟨func17Locals out 1 key ctrl t wmask
                (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
                wgroup w7 w8 w9 pos stride (.i32 v),
              cont, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }]) ∗
      (∀ (wmask wgroup : UInt64) (pos stride : UInt32),
        ⌜Table.get (SipHash.hashU32 k0 k1) t key = none⌝ -∗
        Table.TableBody 0 map ctrl t -∗
        WP (.running
            ⟨{ func17Locals out 0 key ctrl t wmask
                  (Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
                  wgroup w7 w8 w9 pos stride l13 with
                values := missValues },
              missCode, arity, remainder, missControls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])))
    (initial := (⟨0, UInt32.ofNat
        (Table.probeStart t (SipHash.hashU32 k0 k1 key)).pos, 0,
      SipHash.hashU32Low k0 k1 key, w6⟩, map))
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
            Value.i32 ctrl, Value.i32 0, l13],
        values := [] })
    rfl rfl
  · intro i
    iintro Hrec ⟨%hinv, Hbody, Hhit, Hmiss⟩
    obtain ⟨histep, hipos, histride, hihist⟩ := hinv
    have hposLt :
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos
          < t.buckets := hlayout.probe_lt _ _
    simp only [Wasm.SmallStep.loopBodyExpr, func17LoopBody, func17Locals]
    ihave ⟨%hctrlB2, Hheader, ⟨Hpre, ⟨%hgbound, Hgroup⟩, Hpost⟩, Hslots⟩ :=
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
    iapply twp_func17_walk (hashf := SipHash.hashU32 k0 k1) (m := m)
      (out := out) (base := i.2) (key := key) (ctrl := ctrl) (t := t)
      (splat := Table.repeatByte (Table.h2 (SipHash.hashU32 k0 k1 key)))
      (wgroup := Table.groupWord (Table.groupAt t
        (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos))
      (w7 := w7) (w8 := w8) (w9 := w9) (stride := i.1.stride) (v13 := l13)
      (P := (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos)
      (msk := Table.swarMatchTag (Table.h2 (SipHash.hashU32 k0 k1 key))
        (Table.groupWord (Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos)))
      (hitCode := Instruction.localGet 1 ::
        Instruction.const 4294967292 :: Instruction.add ::
        Instruction.load32 0 :: Instruction.localSet 13 ::
        Instruction.const 1 :: Instruction.localSet 1 :: cont)
      (hitControls := controls) (hitValues := [])
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
    iintro %r %q %base' %hfind Hslots
    cases r with
    | some j =>
      simp only [func17WalkExit]
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
      have hjLen :
          ((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos + j)
            % t.buckets < t.slots.length := by
        rw [hlayout.slots_len]; exact hjLt
      have hget : Table.get (SipHash.hashU32 k0 k1) t key = some v := by
        simp only [Table.get, hlayout.find_of_slot hjLt hslot, hslot,
          Option.bind_some, Option.map_some]
      have hslotsGet :
          t.slots[((Table.probeSeq t (SipHash.hashU32 k0 k1 key)
            i.1.step).pos + j) % t.buckets]'hjLen = some (key, v) := by
        rw [← hslot, Table.slotAt, List.getD_eq_getElem]
      have hctrlLt : ctrl.toNat < 4294967296 := ctrl.toBitVec.isLt
      have hsize32 : UInt32.size = 4294967296 := rfl
      have hsz : (8 : Nat) * t.buckets ≤ ctrl.toNat := hctrlB2
      have hbaddrNat : (Table.bucketAddr ctrl
          (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos + j)
            % t.buckets)).toNat
          = ctrl.toNat - 8 * ((((Table.probeSeq t
              (SipHash.hashU32 k0 k1 key) i.1.step).pos + j) % t.buckets)
                + 1) := Table.bucketAddr_toNat ctrl hjLt hctrlB2
      have hval4 : (Table.bucketAddr ctrl
          (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos + j)
            % t.buckets) + 4).toNat
          = (Table.bucketAddr ctrl
              (((Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                i.1.step).pos + j) % t.buckets)).toNat + 4 := by
        simpa using Slices.byteOffset_toNat (Table.bucketAddr ctrl
          (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos + j)
            % t.buckets)) 4 (by omega)
      obtain ⟨ha1, ha2, ha3⟩ := addr_facts
        (Table.bucketAddr ctrl
          (((Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos + j)
            % t.buckets) + 4) (by omega)
      ihave ⟨Hsp, Hcell, Hsq⟩ :=
        (Table.slotsBefore_focus 0 ctrl t.slots hjLen).mp $$ Hslots
      isimp only [hslotsGet, Table.slotCell] at Hcell
      ihave ⟨Hkey, Hval⟩ := Hcell
      wasm_twp_pures [twp_localGet twp_const twp_add]
      isimp only [negFourAdd, slotValueAddr_of_wasm]
      wasm_twp_rebind Wasm.SmallStep.twp_load32_addr v ha1 ha2 ha3 with Hval
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_const]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      ihave Hslots : Table.slotsBefore 0 ctrl t.slots $$
        [Hsp Hkey Hval Hsq]
      · iapply (Table.slotsBefore_focus 0 ctrl t.slots hjLen).mpr
        isimp only [hslotsGet, Table.slotCell]
        iframe Hsp Hkey Hval Hsq
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
      ihave Hgo := Hhit $$ %v %q
        %(Table.groupWord (Table.groupAt t
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos))
        %(UInt32.ofNat
          (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos)
        %i.1.stride %hget Hbody
      iexact Hgo
    | none =>
      simp only [func17WalkExit]
      have hmodelFind : (Table.matchTag
          (Table.h2 (SipHash.hashU32 k0 k1 key))
          (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key)
              i.1.step).pos)).find?
            (fun j => t.keyIs
              (((Table.probeSeq t (SipHash.hashU32 k0 k1 key)
                i.1.step).pos + j) % t.buckets) key) = none :=
        (hlayout.find?_setBytes_eq hposLt key).symm.trans hfind
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
        have hget : Table.get (SipHash.hashU32 k0 k1) t key = none := by
          simp only [Table.get, hfindNone, Option.bind_none]
        ihave Hgo := Hmiss $$ %(0 : UInt64)
          %(Table.groupWord (Table.groupAt t
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos))
          %(UInt32.ofNat
            (Table.probeSeq t (SipHash.hashU32 k0 k1 key) i.1.step).pos)
          %i.1.stride %hget Hbody
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
                  i.1.step).pos)⟩, (0 : UInt32))
            : LookupIdx × UInt32)
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

end Project.RustHashMap.LookupProbe
