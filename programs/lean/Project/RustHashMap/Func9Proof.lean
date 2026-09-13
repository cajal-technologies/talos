import Project.RustHashMap.LookupContracts
import Project.RustHashMap.LookupProbe

/-!
# Proof of the `contains_key` kernel

Absolute `func 12` is `HashMap::contains_key`, WAT lines 2286 to 2554 of
`programs/rust/build/rust_hash_map/program.wat`.  This module composes the
four regions of the body into `LookupContracts.Func9Spec`.

* The guard, WAT 2288 to 2294.  It reads the item count at `map + 12` and
  leaves the block when the count is zero.
* The inline hash, WAT 2296 to 2469.  `LookupHash.twp_func9_hash` runs it.
* The probe loop, WAT 2470 to 2551.  `LookupProbe.twp_func9_probe` runs it.
* The two exits.  The hit exit stands at the `return` of WAT 2518 with `1`
  on the operand stack.  The miss exit leaves the block and falls into the
  `i32.const 0` of WAT 2553.

## The three arms

The map value is a `TableAt`, which has two physical forms.  The static
singleton has no bucket, so its item count is zero and the body takes the
guard.  An allocated table takes the guard when its item count is zero and
runs the hash and the loop when it is not.  `find_eq_none_of_items_zero`
gives the model answer on the first two arms.

The item count fits in a word, because `TableBody` bounds `8 * buckets` by
the control pointer and a well-formed table has no more items than
buckets.
-/

namespace Project.RustHashMap.Func9Proof

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

private theorem func9_index :
    Project.RustHashMap.«module».funcs[9]? =
      some Project.RustHashMap.func9Def := by rfl

set_option maxRecDepth 1048576 in
/-- The body is one block and the fall-through `0`.  The block is the
guard, the inline hash and the probe loop. -/
private theorem func9_body_shape :
    Project.RustHashMap.func9 =
      Instruction.block 0 0
          ([Instruction.localGet 0, .load32 12, .eqz, .br_if 0,
              .localGet 0, .load32 4, .localTee 2]
            ++ (func9Hash ++ func9Block.drop 181))
        :: [Instruction.const 0] := rfl

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

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
/-- `contains_key` returns `1` exactly when the model finds the key. -/
theorem func9_correct [WasmSmallStepGS hlc Universal.State] :
    Func9Spec (hlc := hlc) := by
  unfold Func9Spec CallContract callExpr
  intro map key k0 k1 t callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, Hmap, %hpure, Hcont⟩
  obtain ⟨hwf, hclean, hmapBound⟩ := hpure
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 12
      Project.RustHashMap.func9Def (by decide) func9_index with Hmodule
  simp only [Project.RustHashMap.func9Def, Function.toLocals,
    Function.numParams, List.length_cons, List.length_nil, List.take,
    List.drop, List.reverse_cons, List.reverse_nil, List.map,
    List.nil_append, List.cons_append, ValueType.zero, func9_body_shape,
    Nat.reduceAdd]
  have hh4 := offset_facts map 4 4 rfl (by omega)
  have hh12 := offset_facts map 12 12 rfl (by omega)
  wasm_twp_pures [twp_block twp_localGet]
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
    iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_nil, List.nil_append]
    wasm_twp_pures [twp_const]
    wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
    simp only [List.take, List.nil_append, List.cons_append]
    iclose_map_runtime Hruntime with Hmodule Henv
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
    simp only [containsKey_eq_false_of_items_zero hwf hsing.2.1 key,
      Bool.false_eq_true, if_false]
    ihave Hgo := Hcont $$ Hruntime Hmap
    isimp only [ResumeWP, resumeExpr, List.cons_append,
      List.nil_append] at Hgo
    iexact Hgo
  · -- an allocated table
    isimp only [Table.TableBody, Table.tableHeader] at Hbody
    icases Hbody with ⟨%hctrlBound, ⟨H0, H4, H8, H12⟩, Hctrl, Hslots⟩
    wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := map)
      (offset := 12) (UInt32.ofNat t.items) hh12.1 hh12.2.1 hh12.2.2.1
      hh12.2.2.2 with H12
    by_cases hitems : t.items = 0
    · -- no item: the guard leaves the block at once
      iapply Wasm.SmallStep.twp_eqz (result := 1) (by simp [hitems])
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
      simp only [List.take_nil, List.nil_append]
      wasm_twp_pures [twp_const]
      wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
        with Hmodule
      simp only [List.take, List.nil_append, List.cons_append]
      iclose_map_runtime Hruntime with Hmodule Henv
      ihave Hbody : Table.TableBody 0 map ctrl t $$
        [H0 H4 H8 H12 Hctrl Hslots]
      · isimp only [Table.TableBody, Table.tableHeader]
        isplitl_pureexact hctrlBound
        iframe H0 H4 H8 H12 Hctrl Hslots
      ihave Hmap : Table.HashMapAt 0 map k0 k1 t $$ [Hbody Hk0 Hk1]
      · isimp only [Table.HashMapAt]
        isplitl [Hbody]
        · isimp only [Table.TableAt]
          iexists ctrl
          iright
          isplitl_pureexact hbuckets
          iexact Hbody
        · iframe Hk0 Hk1
      simp only [containsKey_eq_false_of_items_zero hwf hitems key,
        Bool.false_eq_true, if_false]
      ihave Hgo := Hcont $$ Hruntime Hmap
      isimp only [ResumeWP, resumeExpr, List.cons_append,
        List.nil_append] at Hgo
      iexact Hgo
    · -- the table has an item: run the hash and the probe loop
      have hsize : UInt32.size = 4294967296 := rfl
      have hctrlLt : ctrl.toNat < UInt32.size := ctrl.toNat_lt
      have hitemsLt : t.items < UInt32.size := by
        have hle := items_le_buckets hwf
        omega
      iapply Wasm.SmallStep.twp_eqz (result := 0)
        (by rw [if_neg (ofNat_ne_zero (by omega) hitemsLt)])
      wasm_twp_pures [twp_brIfZero twp_localGet]
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
      iapply twp_func9_hash (map := map) (key := key)
        (mask := UInt32.ofNat (t.buckets - 1)) (k0 := k0) (k1 := k1)
        (hmap := hmapBound)
      isplitl_exacts [Hk0 Hk1]
      iintro %w5 %w6 %w7 %w8 Hk0 Hk1
      rw [← func9Probe_slice]
      iapply twp_func9_probe map key ctrl k0 k1 t w5 w6 w7 w8 (.i32 0)
        (missCode := [Instruction.const 0]) (missControls := [])
        (missValues := []) hwf hclean hmapBound (fun _ => rfl)
      isplitl_exact Hbody
      by_cases hck : Table.containsKey (SipHash.hashU32 k0 k1) t key = true
      · -- the key has an entry: the loop stands at the `return` of WAT 2518
        isplitl [Hmodule Henv Hcont Hk0 Hk1]
        · iintro %params %localValues %cs %hhit Hbody
          wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallExplicit
            with Hmodule
          simp only [List.take, List.nil_append, List.cons_append]
          iclose_map_runtime Hruntime with Hmodule Henv
          ihave Hmap : Table.HashMapAt 0 map k0 k1 t $$ [Hbody Hk0 Hk1]
          · isimp only [Table.HashMapAt]
            isplitl [Hbody]
            · isimp only [Table.TableAt]
              iexists ctrl
              iright
              isplitl_pureexact hbuckets
              iexact Hbody
            · iframe Hk0 Hk1
          simp only [hck, if_true]
          ihave Hgo := Hcont $$ Hruntime Hmap
          isimp only [ResumeWP, resumeExpr, List.cons_append,
            List.nil_append] at Hgo
          iexact Hgo
        · iintro %params %localValues %hmissed Hbody
          rw [hck] at hmissed
          exact absurd hmissed (by decide)
      · -- the key has no entry: the loop leaves the block for WAT 2553
        isplitl []
        · iintro %params %localValues %cs %hhit Hbody
          exact absurd hhit hck
        · iintro %params %localValues %hmissed Hbody
          wasm_twp_pures [twp_const]
          wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
            with Hmodule
          simp only [List.take, List.nil_append, List.cons_append]
          iclose_map_runtime Hruntime with Hmodule Henv
          ihave Hmap : Table.HashMapAt 0 map k0 k1 t $$ [Hbody Hk0 Hk1]
          · isimp only [Table.HashMapAt]
            isplitl [Hbody]
            · isimp only [Table.TableAt]
              iexists ctrl
              iright
              isplitl_pureexact hbuckets
              iexact Hbody
            · iframe Hk0 Hk1
          simp only [hmissed, Bool.false_eq_true, if_false]
          ihave Hgo := Hcont $$ Hruntime Hmap
          isimp only [ResumeWP, resumeExpr, List.cons_append,
            List.nil_append] at Hgo
          iexact Hgo

end Project.RustHashMap.Func9Proof
