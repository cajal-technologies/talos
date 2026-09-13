import Project.RustHashMap.LookupContracts
import Project.RustHashMap.LookupProbe

/-!
# Proof of the `get` kernel

Absolute `func 20` is `HashMap::get`, WAT lines 4771 to 5056 of
`programs/rust/build/rust_hash_map/program.wat`.  This module composes the
regions of the body into `LookupContracts.Func17Spec`.

* The guard, WAT 4774 to 4780.  It reads the item count at `map + 12`.
  With no item it sets register 1 to zero and leaves the outer block for
  the two stores.
* The inline hash, WAT 4785 to 4958.  `LookupHash.twp_func17_hash` runs it.
* The probe loop, WAT 4959 to 5048.  `LookupProbe.twp_func17_probe` runs
  it.  The hit exit reads the value at `bucket - 4` and sets register 1 to
  one.  The miss exit leaves the loop with register 1 at zero.
* The two stores, WAT 5050 to 5055.  They write the payload at `out + 4`
  and the discriminant at `out`, which is `Table.optionU32At`.

## The three arms

The map value is a `TableAt`, which has two physical forms.  The static
singleton has no bucket, so its item count is zero and the body takes the
guard.  An allocated table takes the guard when its item count is zero and
runs the hash and the loop when it is not.  `find_eq_none_of_items_zero`
gives the model answer on the first two arms.

On the `none` arm register 13 keeps the zero that the call left there, so
the payload word of the answer is that zero.  `optionU32At` leaves the
payload of `none` free, which is why the arm agrees with the model.
-/

namespace Project.RustHashMap.Func17Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.LookupPures
open Project.RustHashMap.LookupHash
open Project.RustHashMap.LookupProbe
open Project.RustHashMap.LookupContracts
open scoped Wasm.SmallStep.Outcome

private theorem func17_index :
    Project.RustHashMap.«module».funcs[17]? =
      some Project.RustHashMap.func17Def := by rfl

set_option maxRecDepth 1048576 in
/-- The body is one outer block and the two stores.  The outer block is the
guard block, the mask read, the inline hash and the probe loop. -/
private theorem func17_body_shape :
    Project.RustHashMap.func17 =
      Instruction.block 0 0
          (Instruction.block 0 0
              [Instruction.localGet 1, .load32 12, .br_if 0, .const 0,
                .localSet 1, .br 1]
            :: ([Instruction.localGet 1, .load32 4, .localTee 3]
              ++ (func17Hash ++ func17Block.drop 178)))
        :: [Instruction.localGet 0, .localGet 13, .store32 4,
            .localGet 0, .localGet 1, .store32 0] := rfl

/-- Copy of `Func15Proof.lean:111`, which is private there. -/
private theorem ofNat_ne_zero {n : Nat} (h1 : 1 ≤ n) (h2 : n < UInt32.size) :
    UInt32.ofNat n ≠ (0 : UInt32) := by
  intro hc
  have hnat := congrArg UInt32.toNat hc
  rw [UInt32.toNat_ofNat_of_lt' h2, UInt32.toNat_zero] at hnat
  omega

/-- A well-formed table holds no more items than it has buckets. -/
private theorem items_le_buckets {hash : UInt32 → UInt64}
    {t : Table UInt32 UInt32} (hw : Table.WF hash t) :
    t.items ≤ t.buckets := by
  rw [hw.items_eq, Table.toList]
  exact Nat.le_trans (List.length_filterMap_le _ _)
    (Nat.le_of_eq List.length_range)

set_option maxHeartbeats 2000000 in
/-- The two stores of WAT 5050 to 5055.  Register 13 is the payload and
register 1 is the discriminant.  The pair is `Table.optionU32At`, so the
payload matters on the `some` arm only. -/
private theorem twp_get_stores [WasmSmallStepGS hlc Universal.State]
    {params localValues : List Value} {out disc payload : UInt32}
    {o : Option UInt32} {outBefore : List UInt8}
    {callerLocals : Locals} {stack : List Value} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hslot : ∀ vs : List Value,
      Locals.get ⟨params, localValues, vs⟩ 0 = some (.i32 out))
    (hdisc : ∀ vs : List Value,
      Locals.get ⟨params, localValues, vs⟩ 1 = some (.i32 disc))
    (hpay : ∀ vs : List Value,
      Locals.get ⟨params, localValues, vs⟩ 13 = some (.i32 payload))
    (hlength : outBefore.length = 8)
    (hbound : out.toNat + 8 < UInt32.size)
    (hdiscValue : disc = if o.isSome then 1 else 0)
    (hpayValue : ∀ v : UInt32, o = some v → payload = v) :
    iprop(
      Slices.ByteSlice 0 out outBefore ∗
      runtimeModuleOwn ⟨0⟩ Project.RustHashMap.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.RustHashMap.«module») ∗
      (RuntimeContext -∗
        Table.optionU32At 0 out o -∗
        ResumeWP [] callerLocals stack code arity remainder controls calls
          s E Φ)) ⊢
    WP (.running
        ⟨⟨params, localValues, []⟩,
          [Instruction.localGet 0, .localGet 13, .store32 4,
            .localGet 0, .localGet 1, .store32 0],
          0, [], [],
          { locals := { callerLocals with values := stack },
            continuation := code, resultArity := arity,
            callerRemainder := remainder, control := controls,
            returningInstance := ⟨0⟩ } :: calls⟩
        : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hout, Hmodule, Henv, Hcont⟩
  have ho0 := offset_facts out 0 0 rfl (by omega)
  have ho4 := offset_facts out 4 4 rfl (by omega)
  ihave Hwords := outWords 0 out outBefore hlength (by omega) $$ Hout
  icases Hwords with ⟨%w0, %w1, Hw0, Hw1⟩
  iapply Wasm.SmallStep.twp_localGet (hslot _)
  iapply Wasm.SmallStep.twp_localGet (hpay _)
  wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := out) (offset := 4)
    w1 ho4.1 ho4.2.1 ho4.2.2.1 ho4.2.2.2 with Hw1
  iapply Wasm.SmallStep.twp_localGet (hslot _)
  iapply Wasm.SmallStep.twp_localGet (hdisc _)
  ihave Hw0 : pointsTo_u32 0 (out + 0) w0 $$ [Hw0]
  · irw_exact [UInt32.add_zero] with Hw0
  wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := out) (offset := 0)
    w0 ho0.1 ho0.2.1 ho0.2.2.1 ho0.2.2.2 with Hw0
  isimp only [UInt32.add_zero] at Hw0
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  ihave Hopt : Table.optionU32At 0 out o $$ [Hw0 Hw1]
  · iapply Table.optionU32At_of_words 0 out o payload hpayValue
    isplitl [Hw0]
    · irw_exact [← hdiscValue] with Hw0
    · iexact Hw1
  iclose_map_runtime Hruntime with Hmodule Henv
  ihave Hgo := Hcont $$ Hruntime Hopt
  isimp only [ResumeWP, resumeExpr, List.nil_append] at Hgo
  iexact Hgo

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
/-- `get` writes the model answer into the eight-byte output slot. -/
theorem func17_correct [WasmSmallStepGS hlc Universal.State] :
    Func17Spec (hlc := hlc) := by
  unfold Func17Spec CallContract callExpr
  intro out map key k0 k1 t outBefore callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hout, Hmap, %hpure, Hcont⟩
  obtain ⟨houtLength, houtBound, hmapBound, hwf, hclean⟩ := hpure
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 20
      Project.RustHashMap.func17Def (by decide) func17_index with Hmodule
  simp only [Project.RustHashMap.func17Def, Function.toLocals,
    Function.numParams, List.length_cons, List.length_nil, List.take,
    List.drop, List.reverse_cons, List.reverse_nil, List.map,
    List.nil_append, List.cons_append, ValueType.zero, func17_body_shape,
    Nat.reduceAdd]
  have hh4 := offset_facts map 4 4 rfl (by omega)
  have hh12 := offset_facts map 12 12 rfl (by omega)
  wasm_twp_pures [twp_block twp_block twp_localGet]
  isimp only [Table.HashMapAt] at Hmap
  icases Hmap with ⟨Htable, Hk0, Hk1⟩
  isimp only [Table.TableAt] at Htable
  icases Htable with ⟨%ctrl, Harm⟩
  icases Harm with (Hsing | ⟨%hbuckets, Hbody⟩)
  · -- the static singleton of `RawTableInner::NEW`: no item, no bucket
    isimp only [Table.SingletonBody, Table.tableHeader] at Hsing
    icases Hsing with ⟨%hsing, ⟨H0, H4, H8, H12⟩, Hctrl⟩
    wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := map)
      (offset := 12) 0 hh12.1 hh12.2.1 hh12.2.2.1 hh12.2.2.2 with H12
    wasm_twp_pures [twp_brIfZero twp_const]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_br (by rfl)
    simp only [List.take_nil, List.nil_append, List.drop]
    have hget : Table.get (SipHash.hashU32 k0 k1) t key = none :=
      get_eq_none_of_items_zero hwf hsing.2.1 key
    ihave Hmap : Table.HashMapAt 0 map k0 k1 t $$
      [H0 H4 H8 H12 Hctrl Hk0 Hk1]
    · isimp only [Table.HashMapAt]
      isplitl [H0 H4 H8 H12 Hctrl]
      · isimp only [Table.TableAt]
        iexists ctrl
        ileft
        isimp only [Table.SingletonBody, Table.tableHeader]
        isplitl_pureexact hsing
        iframe H0 H4 H8 H12 Hctrl
      · iframe Hk0 Hk1
    iapply twp_get_stores (out := out) (disc := 0) (payload := 0)
      (o := Table.get (SipHash.hashU32 k0 k1) t key)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) houtLength houtBound
      (by rw [hget]; rfl) (by rw [hget]; simp)
    isplitl_exacts [Hout Hmodule Henv]
    iintro Hruntime Hopt
    ihave Hgo := Hcont $$ Hruntime Hopt Hmap
    iexact Hgo
  · -- an allocated table
    isimp only [Table.TableBody, Table.tableHeader] at Hbody
    icases Hbody with ⟨%hctrlBound, ⟨H0, H4, H8, H12⟩, Hctrl, Hslots⟩
    wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := map)
      (offset := 12) (UInt32.ofNat t.items) hh12.1 hh12.2.1 hh12.2.2.1
      hh12.2.2.2 with H12
    by_cases hitems : t.items = 0
    · -- no item: the guard leaves the outer block for the two stores
      have hzero : UInt32.ofNat t.items = 0 := by rw [hitems]; rfl
      have hget : Table.get (SipHash.hashU32 k0 k1) t key = none :=
        get_eq_none_of_items_zero hwf hitems key
      simp only [hzero]
      wasm_twp_pures [twp_brIfZero twp_const]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply Wasm.SmallStep.twp_br (by rfl)
      simp only [List.take_nil, List.nil_append, List.drop]
      ihave Hmap : Table.HashMapAt 0 map k0 k1 t $$
        [H0 H4 H8 H12 Hctrl Hslots Hk0 Hk1]
      · isimp only [Table.HashMapAt]
        isplitl [H0 H4 H8 H12 Hctrl Hslots]
        · isimp only [Table.TableAt]
          iexists ctrl
          iright
          isplitl_pureexact hbuckets
          isimp only [Table.TableBody, Table.tableHeader, hzero]
          isplitl_pureexact hctrlBound
          iframe H0 H4 H8 H12 Hctrl Hslots
        · iframe Hk0 Hk1
      iapply twp_get_stores (out := out) (disc := 0) (payload := 0)
        (o := Table.get (SipHash.hashU32 k0 k1) t key)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) houtLength houtBound
        (by rw [hget]; rfl) (by rw [hget]; simp)
      isplitl_exacts [Hout Hmodule Henv]
      iintro Hruntime Hopt
      ihave Hgo := Hcont $$ Hruntime Hopt Hmap
      iexact Hgo
    · -- the table has an item: run the hash and the probe loop
      have hsize : UInt32.size = 4294967296 := rfl
      have hctrlLt : ctrl.toNat < UInt32.size := ctrl.toNat_lt
      have hitemsLt : t.items < UInt32.size := by
        have hle := items_le_buckets hwf
        omega
      iapply Wasm.SmallStep.twp_brIf
        (ofNat_ne_zero (by omega) hitemsLt) (by rfl)
      simp only [List.take_nil, List.nil_append]
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := map)
        (offset := 4) (UInt32.ofNat (t.buckets - 1)) hh4.1 hh4.2.1
        hh4.2.2.1 hh4.2.2.2 with H4
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      ihave Hbody : Table.TableBody 0 map ctrl t $$
        [H0 H4 H8 H12 Hctrl Hslots]
      · isimp only [Table.TableBody, Table.tableHeader]
        isplitl_pureexact hctrlBound
        iframe H0 H4 H8 H12 Hctrl Hslots
      simp only [List.drop]
      iapply twp_func17_hash (out := out) (map := map) (key := key)
        (mask := UInt32.ofNat (t.buckets - 1)) (k0 := k0) (k1 := k1)
        (hmap := hmapBound)
      isplitl_exacts [Hk0 Hk1]
      iintro %w6 %w7 %w8 %w9 Hk0 Hk1
      rw [← List.append_nil (List.drop 178 func17Block),
        ← func17Probe_slice]
      iapply twp_func17_probe out map key ctrl k0 k1 t w6 w7 w8 w9
        (.i32 0) (.i32 0) (.i32 0) (cont := []) (arity := 0)
        (missCode := [Instruction.localGet 0, .localGet 13, .store32 4,
          .localGet 0, .localGet 1, .store32 0])
        (missControls := []) (missValues := [])
        hwf hclean hmapBound (fun _ _ => rfl)
      isplitl_exact Hbody
      by_cases hnone : Table.get (SipHash.hashU32 k0 k1) t key = none
      · -- the loop found an `EMPTY` byte: the answer is `none`
        isplitl []
        · iintro %v %wmask %wgroup %pos %stride %hsome Hbody
          rw [hnone] at hsome
          exact absurd hsome (by simp)
        · iintro %wmask %wgroup %pos %stride %hmissv Hbody
          ihave Hmap : Table.HashMapAt 0 map k0 k1 t $$ [Hbody Hk0 Hk1]
          · isimp only [Table.HashMapAt]
            isplitl [Hbody]
            · isimp only [Table.TableAt]
              iexists ctrl
              iright
              isplitl_pureexact hbuckets
              iexact Hbody
            · iframe Hk0 Hk1
          iapply twp_get_stores (out := out) (disc := 0) (payload := 0)
            (o := Table.get (SipHash.hashU32 k0 k1) t key)
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) houtLength
            houtBound (by rw [hmissv]; rfl) (by rw [hmissv]; simp)
          isplitl_exacts [Hout Hmodule Henv]
          iintro Hruntime Hopt
          ihave Hgo := Hcont $$ Hruntime Hopt Hmap
          iexact Hgo
      · -- the loop matched the key: the answer is `some`
        isplitl [Hout Hmodule Henv Hcont Hk0 Hk1]
        · iintro %v %wmask %wgroup %pos %stride %hsome Hbody
          iapply Wasm.SmallStep.twp_exitControl (by rfl)
          simp only [List.take_nil, List.nil_append]
          ihave Hmap : Table.HashMapAt 0 map k0 k1 t $$ [Hbody Hk0 Hk1]
          · isimp only [Table.HashMapAt]
            isplitl [Hbody]
            · isimp only [Table.TableAt]
              iexists ctrl
              iright
              isplitl_pureexact hbuckets
              iexact Hbody
            · iframe Hk0 Hk1
          iapply twp_get_stores (out := out) (disc := 1) (payload := v)
            (o := Table.get (SipHash.hashU32 k0 k1) t key)
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) houtLength
            houtBound (by rw [hsome]; rfl)
            (fun v' hv' => Option.some.inj (hsome.symm.trans hv'))
          isplitl_exacts [Hout Hmodule Henv]
          iintro Hruntime Hopt
          ihave Hgo := Hcont $$ Hruntime Hopt Hmap
          iexact Hgo
        · iintro %wmask %wgroup %pos %stride %hmissv Hbody
          exact absurd hmissv hnone

end Project.RustHashMap.Func17Proof
