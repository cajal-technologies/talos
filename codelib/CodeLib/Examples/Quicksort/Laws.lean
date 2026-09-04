import CodeLib.Examples.Quicksort.Pure
import CodeLib.SepLogic.SmallStepTotalLifting
import CodeLib.UInt32

/-!
# Derived laws for the quicksort proof

Compact contextual WP rule for the swapAt instruction sequence.
-/

namespace Wasm.Examples.Quicksort

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open Wasm.SmallStep

-- address arithmetic (same proof as MergeSort.Laws.arrayAddress_toNat)
private theorem arrayAddress_toNat (base : UInt32) {index length : Nat}
    (hfit : base.toNat + 4 * length ≤ UInt32.size)
    (hindex : index < length) :
    (base + UInt32.ofNat index * 4).toNat = base.toNat + 4 * index := by
  have hi : index < UInt32.size := by omega
  have hp : index * 4 < UInt32.size := by omega
  rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat_of_lt' hi]
  have hfour : (4 : UInt32).toNat = 4 := by decide
  rw [hfour, Nat.mod_eq_of_lt hp, Nat.mul_comm index 4]
  apply Nat.mod_eq_of_lt
  change base.toNat + 4 * index < UInt32.size
  omega

theorem twp_address
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
      ⟨⟨params, localValues, .i32 (4 * element + base) :: stack⟩,
        code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        address baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  iintro Hwp
  simp only [address, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_localGet hbase
  iapply Wasm.SmallStep.twp_localGet (by simpa using helement)
  wasm_twp_pures [twp_const twp_mul twp_add]
  iexact Hwp

theorem twp_loadAt_cell
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {baseIndex elementIndex : Nat} {base element addr word : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 element))
    (haddress : 4 * element + base = addr)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h2 : (addr + 2).toNat = addr.toNat + 2)
    (h3 : (addr + 3).toNat = addr.toNat + 3) :
    pointsTo_u32 0 addr word ∗
      (pointsTo_u32 0 addr word -∗
        WP (.running
          ⟨⟨params, localValues, .i32 word :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        loadAt baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  have h1' : ((addr + 0) + 1).toNat = (addr + 0).toNat + 1 := by simpa using h1
  have h2' : ((addr + 0) + 2).toNat = (addr + 0).toNat + 2 := by simpa using h2
  have h3' : ((addr + 0) + 3).toNat = (addr + 0).toNat + 3 := by simpa using h3
  iintro ⟨Hword, Hcont⟩
  simp only [loadAt, List.append_assoc, List.cons_append, List.nil_append]
  iapply twp_address hbase helement
  rw [haddress]
  ihave HwordLater : pointsTo_u32 0 (addr + 0) word $$ [Hword]
  · irw_exact [UInt32.add_zero] with Hword
  wasm_twp_bind Wasm.SmallStep.twp_load32
    (address := addr) (offset := 0)
    word (by simp) h1' h2' h3' with HwordLater => Hword
  iapply Hcont
  irw_exact [UInt32.add_zero] with Hword

set_option maxHeartbeats 2000000 in
theorem twp_loadAt
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {baseIndex elementIndex : Nat} {base : UInt32}
    {input : List UInt32} {k : Nat} (hk : k < input.length)
    (hfit : base.toNat + 4 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 (UInt32.ofNat k))) :
    arrayAt 0 base input ∗
      (arrayAt 0 base input -∗
        WP (.running
          ⟨⟨params, localValues, .i32 input[k] :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        loadAt baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  have hslot : (base + 4 * UInt32.ofNat k).toNat = base.toNat + 4 * k := by
    simpa [UInt32.mul_comm] using arrayAddress_toNat base hfit hk
  have hroom : (base + 4 * UInt32.ofNat k).toNat + 4 ≤ UInt32.size := by
    rw [hslot]; omega
  have hroom' : (base + 4 * UInt32.ofNat k).toNat + 4 ≤ 4294967296 := by
    simpa only [UInt32.size] using hroom
  obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 (base + 4 * UInt32.ofNat k) hroom'
  iintro ⟨Harray, Hcont⟩
  ihave ⟨Hword, Hclose⟩ := arrayAt_get 0 base input k hk $$ Harray
  iapply twp_loadAt_cell hbase helement
    (by rw [UInt32.add_comm])
    h1 h2 h3
  iframe; iintro Hword
  iapply Hcont
  iapply_exact Hclose with Hword

private theorem twp_store32_cell
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {address oldWord newWord : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    pointsTo_u32 0 address oldWord ∗
      (pointsTo_u32 0 address newWord -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 newWord :: .i32 address :: stack⟩,
        .store32 0 :: code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  have h1' : ((address + 0) + 1).toNat = (address + 0).toNat + 1 := by simpa using h1
  have h2' : ((address + 0) + 2).toNat = (address + 0).toNat + 2 := by simpa using h2
  have h3' : ((address + 0) + 3).toNat = (address + 0).toNat + 3 := by simpa using h3
  iintro ⟨Hword, Hcont⟩
  ihave HwordLater : pointsTo_u32 0 (address + 0) oldWord $$ [Hword]
  · irw_exact [UInt32.add_zero] with Hword
  wasm_twp_bind Wasm.SmallStep.twp_store32
    (address := address) (offset := 0) oldWord
    (by simp) h1' h2' h3' with HwordLater => Hword
  ihave Hword' : pointsTo_u32 0 address newWord $$ [Hword]
  · irw_exact [UInt32.add_zero] with Hword
  iapply_exact Hcont with Hword'

set_option maxHeartbeats 2000000 in
theorem twp_swapAt
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {baseIndex aIndex bIndex tmpIndex : Nat}
    {base : UInt32} {input : List UInt32} {a b : Nat}
    {updated : Locals}
    (ha : a < input.length) (hb : b < input.length)
    (hfit : base.toNat + 4 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (ha_local : (⟨params, localValues, stack⟩ : Locals).get aIndex =
      some (.i32 (UInt32.ofNat a)))
    (htmp_set : (⟨params, localValues, .i32 input[a] :: stack⟩ : Locals).set?
      tmpIndex (.i32 input[a]) = some updated)
    (hbase_after : updated.get baseIndex = some (.i32 base))
    (ha_after : updated.get aIndex = some (.i32 (UInt32.ofNat a)))
    (hb_after : updated.get bIndex = some (.i32 (UInt32.ofNat b)))
    (htmp_after : updated.get tmpIndex = some (.i32 input[a])) :
    arrayAt 0 base input ∗
      (arrayAt 0 base (swapElems input a b) -∗
        WP (.running
          ⟨{ updated with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        swapAt baseIndex aIndex bIndex tmpIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  let addr_a : UInt32 := 4 * UInt32.ofNat a + base
  have hslot_a : addr_a.toNat = base.toNat + 4 * a := by
    dsimp [addr_a]; rw [UInt32.add_comm]
    simpa [UInt32.mul_comm] using arrayAddress_toNat base hfit ha
  have hroom_a : addr_a.toNat + 4 ≤ UInt32.size := by rw [hslot_a]; omega
  obtain ⟨h1_a, h2_a, h3_a⟩ := UInt32.addSteps4 addr_a (by
    simpa only [UInt32.size] using hroom_a)
  let addr_b : UInt32 := 4 * UInt32.ofNat b + base
  have hslot_b : addr_b.toNat = base.toNat + 4 * b := by
    dsimp [addr_b]; rw [UInt32.add_comm]
    simpa [UInt32.mul_comm] using arrayAddress_toNat base hfit hb
  have hroom_b : addr_b.toNat + 4 ≤ UInt32.size := by rw [hslot_b]; omega
  obtain ⟨h1_b, h2_b, h3_b⟩ := UInt32.addSteps4 addr_b (by
    simpa only [UInt32.size] using hroom_b)
  have hswap : swapElems input a b = (input.set a input[b]).set b input[a] :=
    List.swapElems_eq_set input ha hb
  iintro ⟨Harray, Hcont⟩
  simp only [swapAt, storeAt, List.append_assoc,
    List.cons_append, List.nil_append]
  -- step 1: load arr[a] onto stack
  iapply_frame_intro twp_loadAt ha hfit hbase ha_local as Harray
  -- step 2: save arr[a] in tmp local
  iapply Wasm.SmallStep.twp_localSet htmp_set
  -- step 3: compute address of arr[a]
  iapply twp_address (by exact hbase_after) (by exact ha_after)
  -- step 4: load arr[b] onto stack
  iapply_frame_intro twp_loadAt hb hfit (by exact hbase_after) (by exact hb_after) as Harray
  -- focus on cell a for the first store
  ihave ⟨Hcell_a, Hclose_a⟩ := arrayAt_set 0 base input a input[b] ha $$ Harray
  ihave Hcell_a' : pointsTo_u32 0 addr_a input[a] $$ [Hcell_a]
  · dsimp [addr_a]
    irw_exact [UInt32.add_comm] with Hcell_a
  -- step 5: store arr[b] at arr[a]
  iapply_splitl_exact twp_store32_cell h1_a h2_a h3_a with Hcell_a'
  iintro Hcell_a
  -- rebuild intermediate array
  ihave Harray2 : arrayAt 0 base (input.set a input[b]) $$ [Hcell_a Hclose_a]
  · iapply Hclose_a
    irw_exact [UInt32.add_comm] with Hcell_a
  -- step 6: compute address of arr[b]
  iapply twp_address (by exact hbase_after) (by exact hb_after)
  -- step 7: push tmp (= original arr[a]) onto stack
  iapply Wasm.SmallStep.twp_localGet (by exact htmp_after)
  -- focus on cell b for the second store
  have hb' : b < (input.set a input[b]).length := by rw [List.length_set]; exact hb
  ihave ⟨Hcell_b, Hclose_b⟩ := arrayAt_set 0 base (input.set a input[b]) b input[a] hb' $$ Harray2
  ihave Hcell_b' : pointsTo_u32 0 addr_b (input.set a input[b])[b] $$ [Hcell_b]
  · dsimp [addr_b]
    irw_exact [UInt32.add_comm] with Hcell_b
  -- step 8: store original arr[a] at arr[b]
  iapply_splitl_exact twp_store32_cell h1_b h2_b h3_b with Hcell_b'
  iintro Hcell_b
  -- apply continuation with swapped array
  iapply Hcont
  rw [hswap]
  iapply Hclose_b
  irw_exact [UInt32.add_comm] with Hcell_b

theorem twp_lessLocal
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {lhsIndex rhsIndex : Nat} {lhs rhs : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hlhs : (⟨params, localValues, stack⟩ : Locals).get lhsIndex = some (.i32 lhs))
    (hrhs : (⟨params, localValues, stack⟩ : Locals).get rhsIndex = some (.i32 rhs)) :
    WP (.running
        ⟨⟨params, localValues, .i32 (if lhs < rhs then 1 else 0) :: stack⟩,
          code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        lessLocal lhsIndex rhsIndex ++ code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  iintro Hwp
  simp only [lessLocal, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_localGet hlhs
  iapply Wasm.SmallStep.twp_localGet (by simpa using hrhs)
  wasm_twp_pures [twp_ltU]
  iexact Hwp

theorem twp_increment
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {index : Nat} {value : UInt32} {updated : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hget : (⟨params, localValues, stack⟩ : Locals).get index = some (.i32 value))
    (hset : (⟨params, localValues, .i32 (1 + value) :: stack⟩ : Locals).set?
        index (.i32 (1 + value)) = some updated) :
    WP (.running
        ⟨{ updated with values := stack }, code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        increment index ++ code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  iintro Hwp
  simp only [increment, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_localGet hget
  wasm_twp_pures [twp_const twp_add]
  iapply_exact Wasm.SmallStep.twp_localSet hset with Hwp

theorem twp_increment_nil
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues stack : List Value}
    {index : Nat} {value : UInt32} {updated : Locals}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hget : (⟨params, localValues, stack⟩ : Locals).get index = some (.i32 value))
    (hset : (⟨params, localValues, .i32 (1 + value) :: stack⟩ : Locals).set?
        index (.i32 (1 + value)) = some updated) :
    WP (.running
        ⟨{ updated with values := stack }, [], arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        increment index, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E [{ Φ }] := by
  simpa only [List.append_nil] using (twp_increment (s := s) (E := E) (Φ := Φ) (code := []) hget hset)

theorem twp_loop_wf_family_from
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {ι : Type} (measure : ι → Nat)
    (locals : ι → Locals) (I : ι → IProp (WasmHeapGF Unit))
    (initial : ι) (initialLocals : Locals)
    {paramArity resultArity arity : Nat}
    {body code : Program} {remainder belowStack : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hinitial : locals initial = initialLocals)
    (hbelow : belowStack = (locals initial).values.drop paramArity)
    (body_closes : ∀ i,
      ⊢@{IProp (WasmHeapGF Unit)} (iprop%
        (∀ (j : ι), ⌜measure j < measure i⌝ -∗ I j -∗
          WP (loopBodyExpr (α := Unit) (locals j)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E [{ Φ }]) -∗
        I i -∗
          WP (loopBodyExpr (α := Unit) (locals i)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E [{ Φ }])) :
    I initial ⊢
      WP (.running
        ⟨initialLocals, .loop paramArity resultArity body :: code,
          arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E [{ Φ }] := by
  have closes : ∀ i,
      I i ⊢
        WP (loopBodyExpr (α := Unit) (locals i)
          paramArity resultArity arity body code remainder belowStack
          controls calls) @ s; E [{ Φ }] := by
    intro current
    induction hmeasure : measure current using Nat.strongRecOn
        generalizing current with
    | ind n ih =>
      subst n
      iintro HI
      iapply body_closes current
      · iintro %j %hji Hj
        ihave Hih := ih (measure j) hji j rfl $$ Hj
        iexact Hih
      · iexact HI
  simp only [loopBodyExpr] at closes
  subst initialLocals
  iintro HI
  iapply twp_loop
  rw [← hbelow]
  ihave Hbody := closes initial $$ HI
  iexact Hbody

theorem u32_ofNat_sub_eq {a b : Nat} (hle : b ≤ a) (ha : a < UInt32.size) :
    UInt32.ofNat a - UInt32.ofNat b = UInt32.ofNat (a - b) := by
  have hb : b < UInt32.size := Nat.lt_of_le_of_lt hle ha
  have hab : a - b < UInt32.size := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  apply UInt32.toNat.inj
  rw [UInt32.toNat_sub, UInt32.toNat_ofNat_of_lt' ha, UInt32.toNat_ofNat_of_lt' hb,
      UInt32.toNat_ofNat_of_lt' hab]
  have := (UInt32.ofNat a).toNat_lt
  rw [UInt32.toNat_ofNat_of_lt' ha] at this; omega

end Wasm.Examples.Quicksort
