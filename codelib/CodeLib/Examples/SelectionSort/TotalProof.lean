import CodeLib.Examples.SelectionSort.Pure
import CodeLib.SepLogic.SmallStepAdequacy
import CodeLib.SepLogic.SmallStepTotalLoop

/-!
# Total Iris proofs for the two selection-sort implementations

The recursive proof follows recursive calls by induction.  The loop proof
uses `MinScan` for the inner loop and `OuterInvariant` for the outer loop.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic

variable [WasmSmallStepGS hlc α]
local instance instSelectionSortWasmTotalIrisGS :
    IrisGS_gen hlc (Expr α) (WasmHeapGF α) :=
  instIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : List Value → IProp (WasmHeapGF α)}

/- These i64 rules are the direct total-WP counterparts of `wp_ltUI64`,
`wp_load64`, and `wp_store64`.  They are kept here because the generic total
lifting library currently only exposes the i32 memory rules. -/

theorem twp_ltUI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs < rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .ltUI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.ltUI64 hresult)


end Wasm.SmallStep

namespace Wasm.Examples.SelectionSort

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic
open Wasm.SmallStep

private theorem arrayAddress64_toNat (base : UInt32) {index length : Nat}
    (hfit : base.toNat + 8 * length ≤ UInt32.size)
    (hindex : index < length) :
    (base + UInt32.ofNat index * 8).toNat = base.toNat + 8 * index := by
  have hi : index < UInt32.size := by omega
  have hp : index * 8 < UInt32.size := by omega
  rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat_of_lt' hi]
  have height : (8 : UInt32).toNat = 8 := by decide
  rw [height, Nat.mod_eq_of_lt hp, Nat.mul_comm index 8]
  apply Nat.mod_eq_of_lt
  simp only [UInt32.size] at hfit ⊢
  omega

theorem twp_address64
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {baseIndex elementIndex : Nat} {base element : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 element)) :
    WP (.running
      ⟨⟨params, localValues, .i32 (8 * element + base) :: stack⟩,
        code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        addressAt baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  iintro Hwp
  simp only [addressAt, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_localGet hbase
  iapply Wasm.SmallStep.twp_localGet (by simpa using helement)
  iapply Wasm.SmallStep.twp_const
  iapply Wasm.SmallStep.twp_mul
  iapply Wasm.SmallStep.twp_add
  iexact Hwp

private theorem address64_steps (address : UInt32)
    (hroom : address.toNat + 8 ≤ UInt32.size) :
    ((address + 1).toNat = address.toNat + 1) ∧
    ((address + 2).toNat = address.toNat + 2) ∧
    ((address + 3).toNat = address.toNat + 3) ∧
    ((address + 4).toNat = address.toNat + 4) ∧
    ((address + 5).toNat = address.toNat + 5) ∧
    ((address + 6).toNat = address.toNat + 6) ∧
    ((address + 7).toNat = address.toNat + 7) := by
  have hroom' : address.toNat + 8 ≤ 4294967296 := by
    simpa only [UInt32.size] using hroom
  constructor
  · simpa using UInt32.add_ofNat_toNat_noWrap address 1 (by decide) (by omega)
  constructor
  · simpa using UInt32.add_ofNat_toNat_noWrap address 2 (by decide) (by omega)
  constructor
  · simpa using UInt32.add_ofNat_toNat_noWrap address 3 (by decide) (by omega)
  constructor
  · simpa using UInt32.add_ofNat_toNat_noWrap address 4 (by decide) (by omega)
  constructor
  · simpa using UInt32.add_ofNat_toNat_noWrap address 5 (by decide) (by omega)
  constructor
  · simpa using UInt32.add_ofNat_toNat_noWrap address 6 (by decide) (by omega)
  · simpa using UInt32.add_ofNat_toNat_noWrap address 7 (by decide) (by omega)

set_option maxHeartbeats 2000000 in
theorem twp_loadAt64
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {baseIndex elementIndex : Nat} {base : UInt32}
    {input : List UInt64} {k : Nat} (hk : k < input.length)
    (hfit : base.toNat + 8 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 (UInt32.ofNat k))) :
    array64At 0 base input ∗
      (array64At 0 base input -∗
        WP (.running
          ⟨⟨params, localValues, .i64 input[k] :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        loadAt baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  let address : UInt32 := base + 8 * UInt32.ofNat k
  have hslot : address.toNat = base.toNat + 8 * k := by
    dsimp [address]
    simpa [UInt32.mul_comm] using arrayAddress64_toNat base hfit hk
  have hroom : address.toNat + 8 ≤ UInt32.size := by rw [hslot]; omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := address64_steps address hroom
  iintro ⟨Harray, Hcont⟩
  ihave Hfocus := array64At_get 0 base input k hk $$ Harray
  icases Hfocus with ⟨Hword, Hclose⟩
  simp only [loadAt, List.append_assoc, List.cons_append, List.nil_append]
  iapply twp_address64 hbase helement
  have haddress : 8 * UInt32.ofNat k + base = address := by
    dsimp [address]; exact UInt32.add_comm _ _
  rw [haddress]
  ihave Hword' : pointsTo_u64 0 (address + 0) input[k] $$ [Hword]
  · rw [UInt32.add_zero]
    iexact Hword
  iapply Wasm.SmallStep.twp_load64 (address := address) (offset := 0)
    input[k] (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hword'
  iintro Hword
  iapply Hcont
  iapply Hclose
  rw [UInt32.add_zero]
  iexact Hword

private theorem twp_store64_cell
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {address : UInt32} {oldWord newWord : UInt64}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hroom : address.toNat + 8 ≤ UInt32.size) :
    pointsTo_u64 0 address oldWord ∗
      (pointsTo_u64 0 address newWord -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 newWord :: .i32 address :: stack⟩,
        .store64 0 :: code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := address64_steps address hroom
  iintro ⟨Hword, Hcont⟩
  ihave Hword' : pointsTo_u64 0 (address + 0) oldWord $$ [Hword]
  · rw [UInt32.add_zero]
    iexact Hword
  iapply Wasm.SmallStep.twp_store64 (address := address) (offset := 0)
    (value := newWord) oldWord (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hword'
  iintro Hword
  iapply Hcont
  rw [UInt32.add_zero]
  iexact Hword

set_option maxHeartbeats 4000000 in
theorem twp_swapAt64
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {baseIndex aIndex bIndex tmpIndex : Nat}
    {base : UInt32} {input : List UInt64} {a b : Nat}
    {updated : Locals}
    (ha : a < input.length) (hb : b < input.length)
    (hfit : base.toNat + 8 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex = some (.i32 base))
    (ha_local : (⟨params, localValues, stack⟩ : Locals).get aIndex =
      some (.i32 (UInt32.ofNat a)))
    (htmp_set : (⟨params, localValues, .i64 input[a] :: stack⟩ : Locals).set?
      tmpIndex (.i64 input[a]) = some updated)
    (hbase_after : updated.get baseIndex = some (.i32 base))
    (ha_after : updated.get aIndex = some (.i32 (UInt32.ofNat a)))
    (hb_after : updated.get bIndex = some (.i32 (UInt32.ofNat b)))
    (htmp_after : updated.get tmpIndex = some (.i64 input[a])) :
    array64At 0 base input ∗
      (array64At 0 base (swapElems input a b) -∗
        WP (.running ⟨{ updated with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨⟨params, localValues, stack⟩,
      swapAt baseIndex aIndex bIndex tmpIndex ++ code,
      arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  let addrA : UInt32 := 8 * UInt32.ofNat a + base
  let addrB : UInt32 := 8 * UInt32.ofNat b + base
  have hslotA : addrA.toNat = base.toNat + 8 * a := by
    dsimp [addrA]; rw [UInt32.add_comm]
    simpa [UInt32.mul_comm] using arrayAddress64_toNat base hfit ha
  have hslotB : addrB.toNat = base.toNat + 8 * b := by
    dsimp [addrB]; rw [UInt32.add_comm]
    simpa [UInt32.mul_comm] using arrayAddress64_toNat base hfit hb
  have hroomA : addrA.toNat + 8 ≤ UInt32.size := by rw [hslotA]; omega
  have hroomB : addrB.toNat + 8 ≤ UInt32.size := by rw [hslotB]; omega
  have hswap : swapElems input a b =
      (input.set a input[b]).set b input[a] := by
    unfold swapElems
    rw [getElem!_pos input b hb, getElem!_pos input a ha]
  iintro ⟨Harray, Hcont⟩
  simp only [swapAt, storeAt, List.append_assoc, List.cons_append, List.nil_append]
  iapply twp_loadAt64 ha hfit hbase ha_local
  isplitl [Harray]
  · iexact Harray
  iintro Harray
  iapply Wasm.SmallStep.twp_localSet htmp_set
  iapply twp_address64 (by simpa using hbase_after) (by simpa using ha_after)
  iapply twp_loadAt64 hb hfit (by simpa using hbase_after) (by simpa using hb_after)
  isplitl [Harray]
  · iexact Harray
  iintro Harray
  ihave HfocusA := array64At_set 0 base input a input[b] ha $$ Harray
  icases HfocusA with ⟨HcellA, HcloseA⟩
  iapply twp_store64_cell hroomA
  isplitl [HcellA]
  · dsimp [addrA]
    rw [UInt32.add_comm]
    iexact HcellA
  iintro HcellA
  ihave Harray2 : array64At 0 base (input.set a input[b]) $$ [HcellA HcloseA]
  · iapply HcloseA
    dsimp [addrA]
    rw [UInt32.add_comm]
    iexact HcellA
  iapply twp_address64 (by simpa using hbase_after) (by simpa using hb_after)
  iapply Wasm.SmallStep.twp_localGet (by simpa using htmp_after)
  have hb2 : b < (input.set a input[b]).length := by simpa
  ihave HfocusB := array64At_set 0 base (input.set a input[b]) b input[a] hb2 $$ Harray2
  icases HfocusB with ⟨HcellB, HcloseB⟩
  iapply twp_store64_cell hroomB
  isplitl [HcellB]
  · dsimp [addrB]
    rw [UInt32.add_comm]
    iexact HcellB
  iintro HcellB
  iapply Hcont
  rw [hswap]
  iapply HcloseB
  dsimp [addrB]
  rw [UInt32.add_comm]
  iexact HcellB

def findMinLocals (arr : UInt32) (length best scan : Nat)
    (stack : List Value) : Locals :=
  ⟨[.i32 arr, .i32 (UInt32.ofNat length), .i32 (UInt32.ofNat best),
      .i32 (UInt32.ofNat scan)], [], stack⟩

private theorem nat_lt_u32_iff {left right : Nat}
    (hl : left < UInt32.size) (hr : right < UInt32.size) :
    (UInt32.ofNat left < UInt32.ofNat right) ↔ left < right := by
  change (UInt32.ofNat left).toNat < (UInt32.ofNat right).toNat ↔ _
  rw [UInt32.toNat_ofNat_of_lt' hl, UInt32.toNat_ofNat_of_lt' hr]

set_option maxHeartbeats 8000000 in
private theorem twp_findMin_aux
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (findIndex : Nat)
    (himports : ¬findIndex < runtimeModule.imports.length)
    (hfunction : runtimeModule.funcs[findIndex - runtimeModule.imports.length]? =
      some (findMinRecursiveFunction findIndex))
    (arr : UInt32) (input : List UInt64) (start best scan : Nat)
    (hinv : MinScan input start best scan)
    (hfit : arr.toNat + 8 * input.length ≤ UInt32.size)
    (n : Nat) (hn : input.length - scan ≤ n)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗ array64At 0 arr input ∗
      (∀ finalBest : Nat,
        ⌜start ≤ finalBest ∧ finalBest < input.length ∧
          ∀ k, start ≤ k → k < input.length →
            input[finalBest]! ≤ input[k]!⌝ -∗
        runtimeModuleOwn ⟨0⟩ runtimeModule -∗ array64At 0 arr input -∗
        WP (.running ⟨{ callerLocals with
          values := .i32 (UInt32.ofNat finalBest) :: stack },
          code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
        (.i32 (UInt32.ofNat scan) :: .i32 (UInt32.ofNat best) ::
        .i32 (UInt32.ofNat input.length) :: .i32 arr :: stack) },
      .call findIndex :: code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  induction n generalizing best scan callerLocals stack code arity remainder controls calls with
  | zero =>
      have hscan : input.length ≤ scan := by omega
      iintro ⟨Hruntime, Harray, Hcont⟩
      ihave HruntimeLater : runtimeModuleOwn ⟨0⟩ runtimeModule $$ [Hruntime]
      · iexact Hruntime
      iapply Wasm.SmallStep.twp_call runtimeModule findIndex
        (findMinRecursiveFunction findIndex) himports hfunction $$ HruntimeLater
      iintro Hruntime
      simp [findMinRecursiveFunction, Function.toLocals, Function.numParams]
      simp only [findMinRecursiveBody, List.cons_append, List.nil_append,
        List.append_assoc]
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_localGet rfl
      have hlengthSize : input.length < UInt32.size := by
        simp only [UInt32.size] at hfit ⊢; omega
      have hscanSize : scan < UInt32.size := by
        have := hinv.2.2.1
        omega
      have hnotlt : ¬ UInt32.ofNat scan < UInt32.ofNat input.length :=
        mt (nat_lt_u32_iff hscanSize hlengthSize).mp (by omega)
      iapply Wasm.SmallStep.twp_ltU rfl
      simp only [if_neg hnotlt]
      iapply Wasm.SmallStep.twp_eqz rfl
      simp only
      iapply Wasm.SmallStep.twp_iff
        (selectedBody := [.localGet 2, .ret]) (by simp)
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_returnFromCallExplicit $$ Hruntime
      iintro Hruntime
      simp only [List.take_succ_cons, List.take_zero, List.singleton_append]
      have hpure : start ≤ best ∧ best < input.length ∧
          ∀ k, start ≤ k → k < input.length →
            input[best]?.getD default ≤ input[k]?.getD default := by
        refine ⟨hinv.1,
          _root_.lt_of_lt_of_le hinv.2.1 hinv.2.2.1, ?_⟩
        intro k hk hklen
        simpa only [List.getElem!_eq_getElem?_getD] using
          hinv.2.2.2 k hk (by omega)
      iapply Hcont $$ %best %hpure Hruntime Harray
  | succ n ih =>
      iintro ⟨Hruntime, Harray, Hcont⟩
      let callerFrame : CallFrame :=
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := ⟨0⟩ }
      ihave HruntimeLater : runtimeModuleOwn ⟨0⟩ runtimeModule $$ [Hruntime]
      · iexact Hruntime
      iapply Wasm.SmallStep.twp_call runtimeModule findIndex
        (findMinRecursiveFunction findIndex) himports hfunction $$ HruntimeLater
      iintro Hruntime
      simp [findMinRecursiveFunction, Function.toLocals, Function.numParams]
      simp only [findMinRecursiveBody, List.cons_append, List.nil_append,
        List.append_assoc]
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_localGet rfl
      have hlengthSize : input.length < UInt32.size := by
        simp only [UInt32.size] at hfit ⊢; omega
      have hscanSize : scan < UInt32.size := by
        by_cases hs : scan < input.length
        · omega
        · have := hinv.2.2.1
          omega
      have hcmp := nat_lt_u32_iff hscanSize hlengthSize
      iapply Wasm.SmallStep.twp_ltU rfl
      by_cases hs : scan < input.length
      · simp only [if_pos (hcmp.mpr hs)]
        iapply Wasm.SmallStep.twp_eqz rfl
        simp only [if_neg (by decide : ¬(1 : UInt32) = 0)]
        iapply Wasm.SmallStep.twp_iff (selectedBody := []) (by simp)
        iapply Wasm.SmallStep.twp_exitControl rfl
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        have hbestLen : best < input.length :=
          _root_.lt_of_lt_of_le hinv.2.1 hinv.2.2.1
        iapply twp_loadAt64 hs hfit rfl rfl
        isplitl [Harray]
        · iexact Harray
        iintro Harray
        iapply twp_loadAt64 hbestLen hfit rfl rfl
        isplitl [Harray]
        · iexact Harray
        iintro Harray
        iapply Wasm.SmallStep.twp_ltUI64 rfl
        by_cases hlt : input[scan] < input[best]
        · simp only [if_pos hlt]
          iapply Wasm.SmallStep.twp_iff rfl
          simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localSet rfl
          iapply Wasm.SmallStep.twp_exitControl rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_const
          iapply Wasm.SmallStep.twp_add
          rw [show 1 + UInt32.ofNat scan = UInt32.ofNat (scan + 1) by
            rw [UInt32.add_comm]
            change UInt32.ofNat scan + UInt32.ofNat 1 = _
            rw [← UInt32.ofNat_add]]
          simp only [List.set_cons_succ, List.set_cons_zero]
          have hnext : MinScan input start scan (scan + 1) := by
            have hstep := MinScan.step input hinv hs
            have hlt' : input[scan]! < input[best]! := by
              rw [getElem!_pos input scan hs, getElem!_pos input best hbestLen]
              exact hlt
            rw [if_pos hlt'] at hstep
            exact hstep
          iapply ih scan (scan + 1)
            hnext
            (by omega)
            (callerLocals :=
              ⟨[.i32 arr, .i32 (UInt32.ofNat input.length),
                .i32 (UInt32.ofNat scan), .i32 (UInt32.ofNat scan)], [], []⟩)
            (stack := []) (code := [.ret]) (arity := 1) (remainder := [])
            (controls := [])
            (calls := callerFrame :: calls)
          isplitl [Hruntime]
          · iexact Hruntime
          isplitl [Harray]
          · iexact Harray
          iintro %finalBest %hpure Hruntime Harray
          iapply Wasm.SmallStep.twp_returnFromCallExplicit $$ Hruntime
          iintro Hruntime
          simp only [List.take_succ_cons, List.take_zero, List.nil_append, List.cons_append]
          have hpure' : start ≤ finalBest ∧ finalBest < input.length ∧
              ∀ k, start ≤ k → k < input.length →
                input[finalBest]?.getD default ≤ input[k]?.getD default := by
            simpa only [List.getElem!_eq_getElem?_getD] using hpure
          iapply Hcont $$ %finalBest %hpure' Hruntime Harray
        · simp only [if_neg hlt]
          iapply Wasm.SmallStep.twp_iff rfl
          simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
          iapply Wasm.SmallStep.twp_exitControl rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_const
          iapply Wasm.SmallStep.twp_add
          rw [show 1 + UInt32.ofNat scan = UInt32.ofNat (scan + 1) by
            rw [UInt32.add_comm]
            change UInt32.ofNat scan + UInt32.ofNat 1 = _
            rw [← UInt32.ofNat_add]]
          have hnext : MinScan input start best (scan + 1) := by
            have hstep := MinScan.step input hinv hs
            have hlt' : ¬ input[scan]! < input[best]! := by
              rw [getElem!_pos input scan hs, getElem!_pos input best hbestLen]
              exact hlt
            rw [if_neg hlt'] at hstep
            exact hstep
          iapply ih best (scan + 1)
            hnext
            (by omega)
            (callerLocals :=
              ⟨[.i32 arr, .i32 (UInt32.ofNat input.length),
                .i32 (UInt32.ofNat best), .i32 (UInt32.ofNat scan)], [], []⟩)
            (stack := []) (code := [.ret]) (arity := 1) (remainder := [])
            (controls := [])
            (calls := callerFrame :: calls)
          isplitl [Hruntime]
          · iexact Hruntime
          isplitl [Harray]
          · iexact Harray
          iintro %finalBest %hpure Hruntime Harray
          iapply Wasm.SmallStep.twp_returnFromCallExplicit $$ Hruntime
          iintro Hruntime
          simp only [List.take_succ_cons, List.take_zero, List.nil_append, List.cons_append]
          have hpure' : start ≤ finalBest ∧ finalBest < input.length ∧
              ∀ k, start ≤ k → k < input.length →
                input[finalBest]?.getD default ≤ input[k]?.getD default := by
            simpa only [List.getElem!_eq_getElem?_getD] using hpure
          iapply Hcont $$ %finalBest %hpure' Hruntime Harray
      · have hnotlt := mt hcmp.mp hs
        simp only [if_neg hnotlt]
        iapply Wasm.SmallStep.twp_eqz rfl
        simp only
        iapply Wasm.SmallStep.twp_iff
          (selectedBody := [.localGet 2, .ret]) (by simp)
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_returnFromCallExplicit $$ Hruntime
        iintro Hruntime
        simp only [List.take_succ_cons, List.take_zero, List.singleton_append]
        have hpure : start ≤ best ∧ best < input.length ∧
            ∀ k, start ≤ k → k < input.length →
              input[best]?.getD default ≤ input[k]?.getD default := by
          refine ⟨hinv.1,
            _root_.lt_of_lt_of_le hinv.2.1 hinv.2.2.1, ?_⟩
          intro k hk hklen
          simpa only [List.getElem!_eq_getElem?_getD] using
            hinv.2.2.2 k hk (by omega)
        iapply Hcont $$ %best %hpure Hruntime Harray

theorem twp_findMin
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (findIndex : Nat)
    (himports : ¬findIndex < runtimeModule.imports.length)
    (hfunction : runtimeModule.funcs[findIndex - runtimeModule.imports.length]? =
      some (findMinRecursiveFunction findIndex))
    (arr : UInt32) (input : List UInt64) (start best scan : Nat)
    (hinv : MinScan input start best scan)
    (hfit : arr.toNat + 8 * input.length ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗ array64At 0 arr input ∗
      (∀ finalBest : Nat,
        ⌜start ≤ finalBest ∧ finalBest < input.length ∧
          ∀ k, start ≤ k → k < input.length →
            input[finalBest]! ≤ input[k]!⌝ -∗
        runtimeModuleOwn ⟨0⟩ runtimeModule -∗ array64At 0 arr input -∗
        WP (.running ⟨{ callerLocals with
          values := .i32 (UInt32.ofNat finalBest) :: stack },
          code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
        (.i32 (UInt32.ofNat scan) :: .i32 (UInt32.ofNat best) ::
        .i32 (UInt32.ofNat input.length) :: .i32 arr :: stack) },
      .call findIndex :: code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] :=
  twp_findMin_aux runtimeModule findIndex himports hfunction arr input
    start best scan hinv hfit input.length (Nat.sub_le _ _)

private theorem sorted_of_length_lt_two (values : List UInt64)
    (h : values.length < 2) : Sorted values := by
  match values with
  | [] => exact List.Pairwise.nil
  | [value] => exact List.pairwise_singleton _ _
  | _ :: _ :: _ =>
      simp only [List.length_cons] at h
      omega

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 10000 in
private theorem twp_recursiveSort_aux
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (findIndex sortIndex : Nat)
    (himportsFind : ¬findIndex < runtimeModule.imports.length)
    (hfunctionFind : runtimeModule.funcs[findIndex - runtimeModule.imports.length]? =
      some (findMinRecursiveFunction findIndex))
    (himportsSort : ¬sortIndex < runtimeModule.imports.length)
    (hfunctionSort : runtimeModule.funcs[sortIndex - runtimeModule.imports.length]? =
      some (recursiveSelectionSortFunction findIndex sortIndex))
    (arr : UInt32) (input : List UInt64)
    (hfit : arr.toNat + 8 * input.length ≤ UInt32.size)
    (n : Nat) (hn : input.length ≤ n)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗ array64At 0 arr input ∗
      (∀ output : List UInt64,
        ⌜List.Perm input output ∧ Sorted output⌝ -∗
        runtimeModuleOwn ⟨0⟩ runtimeModule -∗ array64At 0 arr output -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
        (.i32 (UInt32.ofNat input.length) :: .i32 arr :: stack) },
      .call sortIndex :: code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  induction n generalizing arr input callerLocals stack code arity remainder controls calls with
  | zero =>
      have hinput : input = [] := by
        apply List.eq_nil_of_length_eq_zero
        omega
      subst input
      iintro ⟨Hruntime, Harray, Hcont⟩
      ihave HruntimeLater : runtimeModuleOwn ⟨0⟩ runtimeModule $$ [Hruntime]
      · iexact Hruntime
      iapply Wasm.SmallStep.twp_call runtimeModule sortIndex
        (recursiveSelectionSortFunction findIndex sortIndex)
        himportsSort hfunctionSort $$ HruntimeLater
      iintro Hruntime
      simp [recursiveSelectionSortFunction, Function.toLocals,
        Function.numParams, ValueType.zero]
      simp only [recursiveSelectionSortBody, List.cons_append, List.nil_append]
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_const
      iapply Wasm.SmallStep.twp_ltU (result := 1) (by simp)
      iapply Wasm.SmallStep.twp_iff (selectedBody := [.ret]) (by simp)
      iapply Wasm.SmallStep.twp_returnFromCallExplicit $$ Hruntime
      iintro Hruntime
      simp only [List.take_zero, List.nil_append]
      have hpure : ([] : List UInt64) = [] ∧ Sorted [] :=
        ⟨rfl, List.Pairwise.nil⟩
      iapply Hcont $$ %([] : List UInt64) %hpure Hruntime Harray
  | succ n ih =>
      iintro ⟨Hruntime, Harray, Hcont⟩
      let callerFrame : CallFrame :=
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := ⟨0⟩ }
      ihave HruntimeLater : runtimeModuleOwn ⟨0⟩ runtimeModule $$ [Hruntime]
      · iexact Hruntime
      iapply Wasm.SmallStep.twp_call runtimeModule sortIndex
        (recursiveSelectionSortFunction findIndex sortIndex)
        himportsSort hfunctionSort $$ HruntimeLater
      iintro Hruntime
      simp [recursiveSelectionSortFunction, Function.toLocals,
        Function.numParams, ValueType.zero]
      simp only [recursiveSelectionSortBody, List.cons_append, List.nil_append]
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_const
      have hlengthSize : input.length < UInt32.size := by
        simp only [UInt32.size] at hfit ⊢; omega
      have htwoSize : 2 < UInt32.size := by decide
      have hcmp := nat_lt_u32_iff hlengthSize htwoSize
      by_cases hbase : input.length < 2
      · iapply Wasm.SmallStep.twp_ltU (result := 1) (by
          have hlt : UInt32.ofNat input.length < (2 : UInt32) := by
            simpa using hcmp.mpr hbase
          simp [hlt])
        iapply Wasm.SmallStep.twp_iff
          (selectedBody := [.ret]) (by simp)
        iapply Wasm.SmallStep.twp_returnFromCallExplicit $$ Hruntime
        iintro Hruntime
        simp only [List.take_zero, List.nil_append]
        have hpure : List.Perm input input ∧ Sorted input :=
          ⟨List.Perm.refl _, sorted_of_length_lt_two input hbase⟩
        iapply Hcont $$ %input %hpure Hruntime Harray
      · have hnotlt := mt hcmp.mp hbase
        iapply Wasm.SmallStep.twp_ltU (result := 0) (by
          have hnlt : ¬UInt32.ofNat input.length < (2 : UInt32) := by
            simpa using hnotlt
          simp [hnlt])
        iapply Wasm.SmallStep.twp_iff (selectedBody := []) (by simp)
        iapply Wasm.SmallStep.twp_exitControl rfl
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        have hlen : 0 < input.length := by omega
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_const
        iapply Wasm.SmallStep.twp_const
        iapply twp_findMin runtimeModule findIndex himportsFind hfunctionFind
          arr input 0 0 1 (minScan_start input hlen) hfit
          (callerLocals :=
            { params := [.i32 arr, .i32 (UInt32.ofNat input.length)]
              locals := [.i32 0, .i32 0, .i64 0]
              values := [] })
          (stack := [])
          (code := Instruction.localSet 2 :: (swapAt 0 3 2 4 ++
            [Instruction.localGet 0, Instruction.const 8, Instruction.add,
              Instruction.localGet 1, Instruction.const 1, Instruction.sub,
              Instruction.call sortIndex, Instruction.ret]))
          (arity := 0) (remainder := []) (controls := [])
          (calls := callerFrame :: calls) (s := s) (E := E) (Φ := Φ)
        isplitl [Hruntime]
        · iexact Hruntime
        isplitl [Harray]
        · iexact Harray
        iintro %best %hminimum Hruntime Harray
        have hbest : best < input.length := hminimum.2.1
        iapply Wasm.SmallStep.twp_localSet rfl
        simp only
        iapply twp_swapAt64 (a := 0) (b := best)
          hlen hbest hfit rfl rfl rfl rfl rfl rfl rfl
        isplitl [Harray]
        · iexact Harray
        iintro Hupdated
        let updated := swapElems input 0 best
        have hupdatedLength : updated.length = input.length :=
          swapElems_length input 0 best
        have hupdatedNonempty : 0 < updated.length := by omega
        have hdecomp : updated = updated[0]! :: updated.drop 1 := by
          cases hUpdated : updated with
          | nil =>
              have hlength := congrArg List.length hUpdated
              simp only [List.length_nil] at hlength
              omega
          | cons head tail => simp
        ihave Hupdated' :
            array64At 0 arr (updated[0]! :: updated.drop 1) $$ [Hupdated]
        · rw [← hdecomp]
          iexact Hupdated
        isimp only [array64At] at Hupdated'
        icases Hupdated' with ⟨Hhead, Htail⟩
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_const
        iapply Wasm.SmallStep.twp_add
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_const
        iapply Wasm.SmallStep.twp_sub
        have harrStep : (arr + 8).toNat = arr.toNat + 8 := by
          simpa using UInt32.add_ofNat_toNat_noWrap arr 8 (by decide) (by
            simp only [UInt32.size] at hfit ⊢
            omega)
        have htailLength : (updated.drop 1).length = input.length - 1 := by
          simp only [List.length_drop, hupdatedLength]
        have hfitTail : (arr + 8).toNat + 8 * (updated.drop 1).length ≤
            UInt32.size := by
          rw [harrStep, htailLength]
          omega
        have hpred : UInt32.ofNat input.length - 1 =
            UInt32.ofNat (input.length - 1) := by
          apply UInt32.toNat.inj
          rw [UInt32.toNat_sub, show (1 : UInt32).toNat = 1 from rfl,
            UInt32.toNat_ofNat_of_lt' hlengthSize,
            UInt32.toNat_ofNat_of_lt' (by omega : input.length - 1 < UInt32.size)]
          have hbound := (UInt32.ofNat input.length).toNat_lt
          rw [UInt32.toNat_ofNat_of_lt' hlengthSize] at hbound
          omega
        rw [hpred]
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        rw [UInt32.add_comm 8 arr, ← htailLength]
        iapply ih (arr + 8) (updated.drop 1) hfitTail (by
          rw [htailLength]
          omega)
          (callerLocals :=
            { params := [.i32 arr, .i32 (UInt32.ofNat input.length)]
              locals := [.i32 (UInt32.ofNat best), .i32 0, .i64 input[0]]
              values := [] })
          (stack := []) (code := [.ret]) (arity := 0) (remainder := [])
          (controls := []) (calls := callerFrame :: calls)
        isplitl [Hruntime]
        · iexact Hruntime
        isplitl [Htail]
        · iexact Htail
        iintro %tailOutput %htailPure Hruntime HtailOutput
        iapply Wasm.SmallStep.twp_returnFromCallExplicit $$ Hruntime
        iintro Hruntime
        simp only [List.take_zero, List.nil_append]
        let output := updated[0]! :: tailOutput
        have hpure : List.Perm input output ∧ Sorted output := by
          dsimp only [output, updated]
          apply recursive_compose hlen hbest
          · intro k hk
            exact hminimum.2.2 k (Nat.zero_le _) hk
          · simpa only [updated] using htailPure.1
          · exact htailPure.2
        ihave Houtput : array64At 0 arr output $$ [Hhead HtailOutput]
        · dsimp only [output]
          simp only [array64At]
          isplitl [Hhead]
          · iexact Hhead
          · iexact HtailOutput
        iapply Hcont $$ %output %hpure Hruntime Houtput

theorem twp_recursiveSort
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (findIndex sortIndex : Nat)
    (himportsFind : ¬findIndex < runtimeModule.imports.length)
    (hfunctionFind : runtimeModule.funcs[findIndex - runtimeModule.imports.length]? =
      some (findMinRecursiveFunction findIndex))
    (himportsSort : ¬sortIndex < runtimeModule.imports.length)
    (hfunctionSort : runtimeModule.funcs[sortIndex - runtimeModule.imports.length]? =
      some (recursiveSelectionSortFunction findIndex sortIndex))
    (arr : UInt32) (input : List UInt64)
    (hfit : arr.toNat + 8 * input.length ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗ array64At 0 arr input ∗
      (∀ output : List UInt64,
        ⌜List.Perm input output ∧ Sorted output⌝ -∗
        runtimeModuleOwn ⟨0⟩ runtimeModule -∗ array64At 0 arr output -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
        (.i32 (UInt32.ofNat input.length) :: .i32 arr :: stack) },
      .call sortIndex :: code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] :=
  twp_recursiveSort_aux runtimeModule findIndex sortIndex himportsFind
    hfunctionFind himportsSort hfunctionSort arr input hfit input.length
    (Nat.le_refl _)

/-! ## Loop implementation -/

def loopSortLocals (arr : UInt32) (length outer best scan : Nat)
    (temporary : UInt64) (stack : List Value) : Locals :=
  ⟨[.i32 arr, .i32 (UInt32.ofNat length)],
    [.i32 (UInt32.ofNat outer), .i32 (UInt32.ofNat best),
      .i32 (UInt32.ofNat scan), .i64 temporary], stack⟩

private structure InnerState where
  best : Nat
  scan : Nat

set_option maxHeartbeats 8000000 in
private theorem twp_innerLoop
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (arr : UInt32) (current : List UInt64) (length : Nat)
    (hlength : current.length = length)
    (outer best scan : Nat) (temporary : UInt64)
    (hinv : MinScan current outer best scan)
    (hfit : arr.toNat + 8 * current.length ≤ UInt32.size)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    array64At 0 arr current ∗
      (∀ finalBest : Nat,
        ⌜outer ≤ finalBest ∧ finalBest < current.length ∧
          ∀ k, outer ≤ k → k < current.length →
            current[finalBest]! ≤ current[k]!⌝ -∗
        array64At 0 arr current -∗
        WP (.running ⟨loopSortLocals arr length outer finalBest
            length temporary stack,
          code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨loopSortLocals arr length outer best scan
        temporary stack,
      whileDo loopSelectionSortInnerCondition loopSelectionSortInnerStep ++ code,
      arity, remainder, controls, calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  let Finish : IProp (WasmHeapGF Unit) := iprop%
    ∀ finalBest : Nat,
      ⌜outer ≤ finalBest ∧ finalBest < current.length ∧
        ∀ k, outer ≤ k → k < current.length →
          current[finalBest]! ≤ current[k]!⌝ -∗
      array64At 0 arr current -∗
      WP (.running ⟨loopSortLocals arr length outer finalBest
          length temporary stack,
        code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E [{ Φ }]
  let Inv : InnerState → IProp (WasmHeapGF Unit) := fun state => iprop%
    ⌜MinScan current outer state.best state.scan⌝ ∗
      array64At 0 arr current ∗ Finish
  iintro ⟨Harray, Hfinish⟩
  simp only [whileDo, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_block
  iapply Wasm.SmallStep.twp_loop_wf_family
    (measure := fun state : InnerState => current.length - state.scan)
    (locals := fun state => loopSortLocals arr length outer
      state.best state.scan temporary stack)
    (I := Inv) (initial := ⟨best, scan⟩)
    (initialLocals := loopSortLocals arr length outer best scan
      temporary stack)
    (body := whileLoopCode loopSelectionSortInnerCondition
      loopSelectionSortInnerStep)
    (code := []) (belowStack := stack) rfl rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with ⟨%hstate, Harray, Hfinish⟩
    unfold MinScan at hstate
    have hlengthSize : current.length < UInt32.size := by
      simp only [UInt32.size] at hfit ⊢
      omega
    have hdeclaredSize : length < UInt32.size := by
      rwa [← hlength]
    have hscanSize : state.scan < UInt32.size := by
      omega
    have hcmp := nat_lt_u32_iff hscanSize hdeclaredSize
    simp only [whileLoopCode, loopSelectionSortInnerCondition,
      loopSelectionSortInnerStep, List.append_assoc, List.cons_append,
      List.nil_append]
    iapply Wasm.SmallStep.twp_localGet rfl
    iapply Wasm.SmallStep.twp_localGet rfl
    iapply Wasm.SmallStep.twp_ltU rfl
    iapply Wasm.SmallStep.twp_eqz rfl
    by_cases hs : state.scan < current.length
    · have hs' : state.scan < length := by rwa [← hlength]
      simp only [if_pos (hcmp.mpr hs'),
        if_neg (by decide : ¬(1 : UInt32) = 0)]
      iapply Wasm.SmallStep.twp_brIfZero
      have hbestLen : state.best < current.length := by
        exact _root_.lt_of_lt_of_le hstate.2.1 hstate.2.2.1
      iapply twp_loadAt64 hs hfit rfl rfl
      isplitl [Harray]
      · iexact Harray
      iintro Harray
      iapply twp_loadAt64 hbestLen hfit rfl rfl
      isplitl [Harray]
      · iexact Harray
      iintro Harray
      iapply Wasm.SmallStep.twp_ltUI64 rfl
      by_cases hlt : current[state.scan] < current[state.best]
      · simp only [if_pos hlt]
        iapply Wasm.SmallStep.twp_iff rfl
        simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localSet rfl
        iapply Wasm.SmallStep.twp_exitControl rfl
        simp only [List.take_zero, List.nil_append, List.drop_zero,
          incrementLocal, List.cons_append]
        simp only [loopSortLocals, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub, List.set]
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_const
        iapply Wasm.SmallStep.twp_add
        iapply Wasm.SmallStep.twp_localSet rfl
        iapply Wasm.SmallStep.twp_br rfl
        rw [show 1 + UInt32.ofNat state.scan =
            UInt32.ofNat (state.scan + 1) by
          rw [UInt32.add_comm]
          change UInt32.ofNat state.scan + UInt32.ofNat 1 = _
          rw [← UInt32.ofNat_add]]
        simp only [List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub, List.set, List.take_zero,
          List.nil_append]
        have hnext : MinScan current outer state.scan (state.scan + 1) := by
          have hstep := MinScan.step current hstate hs
          have hlt' : current[state.scan]! < current[state.best]! := by
            rw [getElem!_pos current state.scan hs,
              getElem!_pos current state.best hbestLen]
            exact hlt
          simpa only [if_pos hlt'] using hstep
        ispecialize Hrec $$ %(⟨state.scan, state.scan + 1⟩ : InnerState)
        iapply Hrec
        · ipureintro
          change current.length - (state.scan + 1) <
            current.length - state.scan
          omega
        isplitr
        · ipureintro
          exact hnext
        iframe
      · simp only [if_neg hlt]
        iapply Wasm.SmallStep.twp_iff rfl
        simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
        iapply Wasm.SmallStep.twp_exitControl rfl
        simp only [List.take_zero, List.nil_append, List.drop_zero,
          incrementLocal, List.cons_append]
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_const
        iapply Wasm.SmallStep.twp_add
        iapply Wasm.SmallStep.twp_localSet rfl
        iapply Wasm.SmallStep.twp_br rfl
        rw [show 1 + UInt32.ofNat state.scan =
            UInt32.ofNat (state.scan + 1) by
          rw [UInt32.add_comm]
          change UInt32.ofNat state.scan + UInt32.ofNat 1 = _
          rw [← UInt32.ofNat_add]]
        simp only [loopSortLocals, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub, List.set, List.take_zero,
          List.nil_append]
        have hnext : MinScan current outer state.best (state.scan + 1) := by
          have hstep := MinScan.step current hstate hs
          have hlt' : ¬ current[state.scan]! < current[state.best]! := by
            rw [getElem!_pos current state.scan hs,
              getElem!_pos current state.best hbestLen]
            exact hlt
          simpa only [if_neg hlt'] using hstep
        ispecialize Hrec $$ %(⟨state.best, state.scan + 1⟩ : InnerState)
        iapply Hrec
        · ipureintro
          change current.length - (state.scan + 1) <
            current.length - state.scan
          omega
        isplitr
        · ipureintro
          exact hnext
        iframe
    · have hnlt : ¬UInt32.ofNat state.scan < UInt32.ofNat length := by
        apply mt hcmp.mp
        rwa [← hlength]
      simp only [if_neg hnlt]
      iapply Wasm.SmallStep.twp_brIf (by decide) rfl
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      have hscanEq : state.scan = current.length := by omega
      rw [hscanEq, hlength]
      simp only [loopSortLocals]
      have hpure : outer ≤ state.best ∧ state.best < current.length ∧
          ∀ k, outer ≤ k → k < current.length →
            current[state.best]! ≤ current[k]! := by
        refine ⟨hstate.1,
          _root_.lt_of_lt_of_le hstate.2.1 hstate.2.2.1, ?_⟩
        intro k hk hklen
        exact hstate.2.2.2 k hk (by simpa [hscanEq] using hklen)
      ispecialize Hfinish $$ %state.best %hpure Harray
      isimp only [loopSortLocals] at Hfinish
      iexact Hfinish
  · simp only [Inv]
    isplitr
    · ipureintro
      exact hinv
    iframe

private structure OuterState where
  current : List UInt64
  outer : Nat
  best : Nat
  scan : Nat
  temporary : UInt64

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 10000 in
private theorem twp_outerLoop
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (arr : UInt32) (input current : List UInt64)
    (outer best scan : Nat) (temporary : UInt64)
    (hinv : OuterInvariant input current outer)
    (hfit : arr.toNat + 8 * input.length ≤ UInt32.size)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    array64At 0 arr current ∗
      (∀ (output : List UInt64) (outer' best' scan' : Nat)
          (temporary' : UInt64),
        ⌜List.Perm input output ∧ Sorted output⌝ -∗
        array64At 0 arr output -∗
        WP (.running ⟨loopSortLocals arr input.length outer' best' scan'
            temporary' stack,
          code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨loopSortLocals arr input.length outer best scan
        temporary stack,
      whileDo loopSelectionSortOuterCondition loopSelectionSortOuterStep ++ code,
      arity, remainder, controls, calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  let Finish : IProp (WasmHeapGF Unit) := iprop%
    ∀ (output : List UInt64) (outer' best' scan' : Nat)
        (temporary' : UInt64),
      ⌜List.Perm input output ∧ Sorted output⌝ -∗
      array64At 0 arr output -∗
      WP (.running ⟨loopSortLocals arr input.length outer' best' scan'
          temporary' stack,
        code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E [{ Φ }]
  let Inv : OuterState → IProp (WasmHeapGF Unit) := fun state => iprop%
    ⌜OuterInvariant input state.current state.outer⌝ ∗
      array64At 0 arr state.current ∗ Finish
  iintro ⟨Harray, Hfinish⟩
  simp only [whileDo, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_block
  iapply Wasm.SmallStep.twp_loop_wf_family
    (measure := fun state : OuterState => input.length - state.outer)
    (locals := fun state => loopSortLocals arr input.length state.outer
      state.best state.scan state.temporary stack)
    (I := Inv)
    (initial := ⟨current, outer, best, scan, temporary⟩)
    (initialLocals := loopSortLocals arr input.length outer best scan
      temporary stack)
    (body := whileLoopCode loopSelectionSortOuterCondition
      loopSelectionSortOuterStep)
    (code := []) (belowStack := stack) rfl rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with ⟨%houter, Harray, Hfinish⟩
    have hlength : state.current.length = input.length := houter.1
    have hfitCurrent : arr.toNat + 8 * state.current.length ≤
        UInt32.size := by rwa [hlength]
    have hlengthSize : state.current.length < UInt32.size := by
      simp only [UInt32.size] at hfitCurrent ⊢
      omega
    have houterSize : state.outer + 1 < UInt32.size := by
      unfold OuterInvariant at houter
      simp only [UInt32.size] at hfitCurrent ⊢
      omega
    have hinputSize : input.length < UInt32.size := by
      rwa [← hlength]
    have hcmp := nat_lt_u32_iff houterSize hinputSize
    simp only [whileLoopCode, loopSelectionSortOuterCondition,
      loopSelectionSortOuterStep, List.append_assoc, List.cons_append,
      List.nil_append]
    iapply Wasm.SmallStep.twp_localGet rfl
    iapply Wasm.SmallStep.twp_const
    iapply Wasm.SmallStep.twp_add
    rw [show 1 + UInt32.ofNat state.outer =
        UInt32.ofNat (state.outer + 1) by
      rw [UInt32.add_comm]
      change UInt32.ofNat state.outer + UInt32.ofNat 1 = _
      rw [← UInt32.ofNat_add]]
    iapply Wasm.SmallStep.twp_localGet rfl
    iapply Wasm.SmallStep.twp_ltU rfl
    iapply Wasm.SmallStep.twp_eqz rfl
    by_cases hmore : state.outer + 1 < state.current.length
    · have hmore' : state.outer + 1 < input.length := by
        rwa [← hlength]
      simp only [if_pos (hcmp.mpr hmore'),
        if_neg (by decide : ¬(1 : UInt32) = 0)]
      iapply Wasm.SmallStep.twp_brIfZero
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_localSet rfl
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_const
      iapply Wasm.SmallStep.twp_add
      rw [show 1 + UInt32.ofNat state.outer =
          UInt32.ofNat (state.outer + 1) by
        rw [UInt32.add_comm]
        change UInt32.ofNat state.outer + UInt32.ofNat 1 = _
        rw [← UInt32.ofNat_add]]
      iapply Wasm.SmallStep.twp_localSet rfl
      simp only [loopSortLocals, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub, List.set]
      have hlocals :
          ({ params := [.i32 arr, .i32 (UInt32.ofNat input.length)]
             locals := [.i32 (UInt32.ofNat state.outer),
               .i32 (UInt32.ofNat state.outer),
               .i32 (UInt32.ofNat (state.outer + 1)),
               .i64 state.temporary]
             values := stack } : Locals) =
            loopSortLocals arr input.length state.outer state.outer
              (state.outer + 1) state.temporary stack := rfl
      rw [hlocals]
      have houterLen : state.outer < state.current.length := by omega
      iapply twp_innerLoop arr state.current input.length hlength
        state.outer state.outer
        (state.outer + 1) state.temporary
        (minScan_start state.current houterLen) hfitCurrent
        (stack := stack)
        (code := swapAt 0 2 3 5 ++
          (incrementLocal 2 ++ [Instruction.br 0]))
        (arity := arity) (remainder := remainder)
        (controls :=
          { kind := .loop, paramArity := 0, resultArity := 0
            body :=
              .localGet 2 :: .const 1 :: .add :: .localGet 1 :: .ltU ::
                .eqz :: .br_if 1 :: .localGet 2 :: .localSet 3 ::
                .localGet 2 :: .const 1 :: .add :: .localSet 4 ::
                (whileDo loopSelectionSortInnerCondition
                  loopSelectionSortInnerStep ++
                  (swapAt 0 2 3 5 ++
                    (incrementLocal 2 ++ [Instruction.br 0])))
            continuation := [], belowStack := stack } ::
          { kind := .block, paramArity := 0, resultArity := 0
            body := [.loop 0 0
              (.localGet 2 :: .const 1 :: .add :: .localGet 1 :: .ltU ::
                .eqz :: .br_if 1 :: .localGet 2 :: .localSet 3 ::
                .localGet 2 :: .const 1 :: .add :: .localSet 4 ::
                (whileDo loopSelectionSortInnerCondition
                  loopSelectionSortInnerStep ++
                  (swapAt 0 2 3 5 ++
                    (incrementLocal 2 ++ [Instruction.br 0]))))]
            continuation := code, belowStack := List.drop 0 stack } :: controls)
        (calls := calls) (s := s) (E := E) (Φ := Φ)
      isplitl [Harray]
      · iexact Harray
      iintro %finalBest %hminimum Harray
      have hbest : finalBest < state.current.length := hminimum.2.1
      iapply twp_swapAt64 (a := state.outer) (b := finalBest)
        houterLen hbest hfitCurrent rfl rfl rfl rfl rfl rfl rfl
      isplitl [Harray]
      · iexact Harray
      iintro Hupdated
      simp only [incrementLocal, List.cons_append,
        List.nil_append]
      simp only [loopSortLocals, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub, List.set]
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_const
      iapply Wasm.SmallStep.twp_add
      iapply Wasm.SmallStep.twp_localSet rfl
      iapply Wasm.SmallStep.twp_br rfl
      rw [show 1 + UInt32.ofNat state.outer =
          UInt32.ofNat (state.outer + 1) by
        rw [UInt32.add_comm]
        change UInt32.ofNat state.outer + UInt32.ofNat 1 = _
        rw [← UInt32.ofNat_add]]
      simp only [List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub, List.set, List.take_zero,
        List.nil_append]
      let updated := swapElems state.current state.outer finalBest
      have hnext : OuterInvariant input updated (state.outer + 1) := by
        dsimp only [updated]
        apply OuterInvariant.step houter houterLen
        · exact ⟨hminimum.1, hminimum.2.1⟩
        · exact hminimum.2.2
      ispecialize Hrec $$
        %(⟨updated, state.outer + 1, finalBest,
          input.length, state.current[state.outer]⟩ : OuterState)
      iapply Hrec
      · ipureintro
        change input.length - (state.outer + 1) <
          input.length - state.outer
        omega
      isplitr
      · ipureintro
        exact hnext
      isplitl [Hupdated]
      · rw [show updated =
          swapElems state.current state.outer finalBest from rfl]
        iexact Hupdated
      · iexact Hfinish
    · have hnlt : ¬UInt32.ofNat (state.outer + 1) <
          UInt32.ofNat input.length := by
        apply mt hcmp.mp
        rwa [← hlength]
      simp only [if_neg hnlt]
      iapply Wasm.SmallStep.twp_brIf (by decide) rfl
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      have hfinished : state.current.length ≤ state.outer + 1 := by omega
      have hpure : List.Perm input state.current ∧ Sorted state.current :=
        ⟨OuterInvariant.perm houter,
          OuterInvariant.sorted houter hfinished⟩
      ispecialize Hfinish $$ %state.current %state.outer %state.best
        %state.scan %state.temporary %hpure Harray
      isimp only [loopSortLocals] at Hfinish
      simp only [loopSortLocals]
      iexact Hfinish
  · simp only [Inv]
    isplitr
    · ipureintro
      exact hinv
    isplitl [Harray]
    · iexact Harray
    · iexact Hfinish

theorem twp_loopSort
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (sortIndex : Nat)
    (himports : ¬sortIndex < runtimeModule.imports.length)
    (hfunction : runtimeModule.funcs[sortIndex - runtimeModule.imports.length]? =
      some loopSelectionSortFunction)
    (arr : UInt32) (input : List UInt64)
    (hfit : arr.toNat + 8 * input.length ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗ array64At 0 arr input ∗
      (∀ output : List UInt64,
        ⌜List.Perm input output ∧ Sorted output⌝ -∗
        runtimeModuleOwn ⟨0⟩ runtimeModule -∗ array64At 0 arr output -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
        (.i32 (UInt32.ofNat input.length) :: .i32 arr :: stack) },
      .call sortIndex :: code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Harray, Hcont⟩
  let callerFrame : CallFrame :=
    { locals := { callerLocals with values := stack }
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls
      returningInstance := ⟨0⟩ }
  ihave HruntimeLater : runtimeModuleOwn ⟨0⟩ runtimeModule $$ [Hruntime]
  · iexact Hruntime
  iapply Wasm.SmallStep.twp_call runtimeModule sortIndex
    loopSelectionSortFunction himports hfunction $$ HruntimeLater
  iintro Hruntime
  simp [loopSelectionSortFunction, Function.toLocals, Function.numParams,
    ValueType.zero]
  simp only [loopSelectionSortBody, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_const
  iapply Wasm.SmallStep.twp_localSet rfl
  simp only [List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  have hlocals :
      ({ params := [.i32 arr, .i32 (UInt32.ofNat input.length)]
         locals := [.i32 0, .i32 0, .i32 0, .i64 0]
         values := [] } : Locals) =
        loopSortLocals arr input.length 0 0 0 0 [] := rfl
  rw [hlocals]
  iapply twp_outerLoop arr input input 0 0 0 0
    (outerInvariant_start input) hfit
    (stack := []) (code := [.ret]) (arity := 0) (remainder := [])
    (controls := []) (calls := callerFrame :: calls)
    (s := s) (E := E) (Φ := Φ)
  isplitl [Harray]
  · iexact Harray
  iintro %output %outer %best %scan %temporary %hpure Harray
  iapply Wasm.SmallStep.twp_returnFromCallExplicit $$ Hruntime
  iintro Hruntime
  simp only [List.take_zero, List.nil_append]
  iapply Hcont $$ %output %hpure Hruntime Harray

end Wasm.Examples.SelectionSort
