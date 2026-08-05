import CodeLib.Examples.Quicksort.Pure

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

theorem wp_address
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {baseIndex elementIndex : Nat} {base element : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 element)) :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 (4 * element + base) :: stack⟩,
        code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        address baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  iintro Hwp
  simp only [address, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet hbase
  inext
  iapply Wasm.SmallStep.wp_localGet (by simpa using helement)
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_mul
  inext
  iapply Wasm.SmallStep.wp_add
  iexact Hwp

theorem wp_loadAt_cell
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
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
    pointsTo_u32 addr word ∗
      (pointsTo_u32 addr word -∗
        WP (.running
          ⟨⟨params, localValues, .i32 word :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        loadAt baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  have h1' : ((addr + 0) + 1).toNat = (addr + 0).toNat + 1 := by simpa using h1
  have h2' : ((addr + 0) + 2).toNat = (addr + 0).toNat + 2 := by simpa using h2
  have h3' : ((addr + 0) + 3).toNat = (addr + 0).toNat + 3 := by simpa using h3
  iintro ⟨Hword, Hcont⟩
  simp only [loadAt, List.append_assoc, List.cons_append, List.nil_append]
  iapply wp_address hbase helement
  inext
  rw [haddress]
  ihave HwordLater : ▷ pointsTo_u32 (addr + 0) word $$ [Hword]
  · inext
    rw [UInt32.add_zero]
    iexact Hword
  iapply Wasm.SmallStep.wp_load32
    (address := addr) (offset := 0)
    word (by simp) h1' h2' h3' $$ HwordLater
  inext
  iintro Hword
  iapply Hcont
  rw [UInt32.add_zero]
  iexact Hword

set_option maxHeartbeats 2000000 in
theorem wp_loadAt
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
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
    arrayAt base input ∗
      (arrayAt base input -∗
        WP (.running
          ⟨⟨params, localValues, .i32 input[k] :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        loadAt baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  have hslot : (base + 4 * UInt32.ofNat k).toNat = base.toNat + 4 * k := by
    simpa [UInt32.mul_comm] using arrayAddress_toNat base hfit hk
  have hroom : (base + 4 * UInt32.ofNat k).toNat + 4 ≤ UInt32.size := by
    rw [hslot]; omega
  have hroom' : (base + 4 * UInt32.ofNat k).toNat + 4 ≤ 4294967296 := by
    simpa only [UInt32.size] using hroom
  have h1 : ((base + 4 * UInt32.ofNat k) + 1).toNat =
      (base + 4 * UInt32.ofNat k).toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap
      (base + 4 * UInt32.ofNat k) 1 (by decide) (by omega)
  have h2 : ((base + 4 * UInt32.ofNat k) + 2).toNat =
      (base + 4 * UInt32.ofNat k).toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap
      (base + 4 * UInt32.ofNat k) 2 (by decide) (by omega)
  have h3 : ((base + 4 * UInt32.ofNat k) + 3).toNat =
      (base + 4 * UInt32.ofNat k).toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap
      (base + 4 * UInt32.ofNat k) 3 (by decide) (by omega)
  iintro ⟨Harray, Hcont⟩
  ihave Hfocus := arrayAt_get base input k hk $$ Harray
  icases Hfocus with ⟨Hword, Hclose⟩
  iapply wp_loadAt_cell hbase helement
    (by rw [UInt32.add_comm])
    h1 h2 h3
  isplitl [Hword]
  · iexact Hword
  iintro Hword
  iapply Hcont
  iapply Hclose
  iexact Hword

private theorem wp_store32_cell
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {address oldWord newWord : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    pointsTo_u32 address oldWord ∗
      (pointsTo_u32 address newWord -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 newWord :: .i32 address :: stack⟩,
        .store32 0 :: code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  have h1' : ((address + 0) + 1).toNat = (address + 0).toNat + 1 := by simpa using h1
  have h2' : ((address + 0) + 2).toNat = (address + 0).toNat + 2 := by simpa using h2
  have h3' : ((address + 0) + 3).toNat = (address + 0).toNat + 3 := by simpa using h3
  iintro ⟨Hword, Hcont⟩
  ihave HwordLater : ▷ pointsTo_u32 (address + 0) oldWord $$ [Hword]
  · inext
    rw [UInt32.add_zero]
    iexact Hword
  iapply Wasm.SmallStep.wp_store32
    (address := address) (offset := 0) oldWord
    (by simp) h1' h2' h3' $$ HwordLater
  inext
  iintro Hword
  ihave Hword' : pointsTo_u32 address newWord $$ [Hword]
  · rw [UInt32.add_zero]
    iexact Hword
  iapply Hcont
  iexact Hword'

set_option maxHeartbeats 2000000 in
theorem wp_swapAt
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
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
    arrayAt base input ∗
      (arrayAt base (swapElems input a b) -∗
        WP (.running
          ⟨{ updated with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        swapAt baseIndex aIndex bIndex tmpIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  let addr_a : UInt32 := 4 * UInt32.ofNat a + base
  have hslot_a : addr_a.toNat = base.toNat + 4 * a := by
    dsimp [addr_a]; rw [UInt32.add_comm]
    simpa [UInt32.mul_comm] using arrayAddress_toNat base hfit ha
  have hroom_a : addr_a.toNat + 4 ≤ UInt32.size := by rw [hslot_a]; omega
  have h1_a : (addr_a + 1).toNat = addr_a.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addr_a 1
      (by decide) (by
        have : addr_a.toNat + 4 ≤ 4294967296 := by
          simpa only [UInt32.size] using hroom_a
        omega)
  have h2_a : (addr_a + 2).toNat = addr_a.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addr_a 2
      (by decide) (by
        have : addr_a.toNat + 4 ≤ 4294967296 := by
          simpa only [UInt32.size] using hroom_a
        omega)
  have h3_a : (addr_a + 3).toNat = addr_a.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addr_a 3
      (by decide) (by
        have : addr_a.toNat + 4 ≤ 4294967296 := by
          simpa only [UInt32.size] using hroom_a
        omega)
  let addr_b : UInt32 := 4 * UInt32.ofNat b + base
  have hslot_b : addr_b.toNat = base.toNat + 4 * b := by
    dsimp [addr_b]; rw [UInt32.add_comm]
    simpa [UInt32.mul_comm] using arrayAddress_toNat base hfit hb
  have hroom_b : addr_b.toNat + 4 ≤ UInt32.size := by rw [hslot_b]; omega
  have h1_b : (addr_b + 1).toNat = addr_b.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addr_b 1
      (by decide) (by
        have : addr_b.toNat + 4 ≤ 4294967296 := by
          simpa only [UInt32.size] using hroom_b
        omega)
  have h2_b : (addr_b + 2).toNat = addr_b.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addr_b 2
      (by decide) (by
        have : addr_b.toNat + 4 ≤ 4294967296 := by
          simpa only [UInt32.size] using hroom_b
        omega)
  have h3_b : (addr_b + 3).toNat = addr_b.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addr_b 3
      (by decide) (by
        have : addr_b.toNat + 4 ≤ 4294967296 := by
          simpa only [UInt32.size] using hroom_b
        omega)
  have hswap : swapElems input a b = (input.set a input[b]).set b input[a] := by
    unfold swapElems
    rw [getElem!_pos input b hb, getElem!_pos input a ha]
  iintro ⟨Harray, Hcont⟩
  simp only [swapAt, storeAt, List.append_assoc,
    List.cons_append, List.nil_append]
  -- step 1: load arr[a] onto stack
  iapply wp_loadAt ha hfit hbase ha_local
  isplitl [Harray]
  · iexact Harray
  iintro Harray
  -- step 2: save arr[a] in tmp local
  iapply Wasm.SmallStep.wp_localSet htmp_set
  inext
  -- step 3: compute address of arr[a]
  iapply wp_address (by exact hbase_after) (by exact ha_after)
  inext
  -- step 4: load arr[b] onto stack
  iapply wp_loadAt hb hfit (by exact hbase_after) (by exact hb_after)
  isplitl [Harray]
  · iexact Harray
  iintro Harray
  -- focus on cell a for the first store
  ihave Hfocus := arrayAt_set base input a input[b] ha $$ Harray
  icases Hfocus with ⟨Hcell_a, Hclose_a⟩
  ihave Hcell_a' : pointsTo_u32 addr_a input[a] $$ [Hcell_a]
  · dsimp [addr_a]
    rw [UInt32.add_comm]
    iexact Hcell_a
  -- step 5: store arr[b] at arr[a]
  iapply wp_store32_cell h1_a h2_a h3_a
  isplitl [Hcell_a']
  · iexact Hcell_a'
  iintro Hcell_a
  -- rebuild intermediate array
  ihave Harray2 : arrayAt base (input.set a input[b]) $$ [Hcell_a Hclose_a]
  · iapply Hclose_a
    rw [UInt32.add_comm]
    iexact Hcell_a
  -- step 6: compute address of arr[b]
  iapply wp_address (by exact hbase_after) (by exact hb_after)
  inext
  -- step 7: push tmp (= original arr[a]) onto stack
  iapply Wasm.SmallStep.wp_localGet (by exact htmp_after)
  inext
  -- focus on cell b for the second store
  have hb' : b < (input.set a input[b]).length := by rw [List.length_set]; exact hb
  ihave Hfocus := arrayAt_set base (input.set a input[b]) b input[a] hb' $$ Harray2
  icases Hfocus with ⟨Hcell_b, Hclose_b⟩
  ihave Hcell_b' : pointsTo_u32 addr_b (input.set a input[b])[b] $$ [Hcell_b]
  · dsimp [addr_b]
    rw [UInt32.add_comm]
    iexact Hcell_b
  -- step 8: store original arr[a] at arr[b]
  iapply wp_store32_cell h1_b h2_b h3_b
  isplitl [Hcell_b']
  · iexact Hcell_b'
  iintro Hcell_b
  -- apply continuation with swapped array
  iapply Hcont
  rw [hswap]
  iapply Hclose_b
  rw [UInt32.add_comm]
  iexact Hcell_b

theorem u32_ofNat_succ {n : Nat} (h : n + 1 < UInt32.size) :
    UInt32.ofNat n + 1 = UInt32.ofNat (n + 1) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_add]
  have hn : n < UInt32.size := by omega
  rw [UInt32.toNat_ofNat_of_lt' hn]
  have hone : (1 : UInt32).toNat = 1 := by decide
  rw [hone, Nat.mod_eq_of_lt]
  · symm; exact UInt32.toNat_ofNat_of_lt' h
  · simpa only [UInt32.size] using h

theorem wp_lessLocal
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {lhsIndex rhsIndex : Nat} {lhs rhs : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hlhs : (⟨params, localValues, stack⟩ : Locals).get lhsIndex = some (.i32 lhs))
    (hrhs : (⟨params, localValues, stack⟩ : Locals).get rhsIndex = some (.i32 rhs)) :
    ▷ WP (.running
        ⟨⟨params, localValues, .i32 (if lhs < rhs then 1 else 0) :: stack⟩,
          code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        lessLocal lhsIndex rhsIndex ++ code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  iintro Hwp
  simp only [lessLocal, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet hlhs
  inext
  iapply Wasm.SmallStep.wp_localGet (by simpa using hrhs)
  inext
  iapply Wasm.SmallStep.wp_ltU rfl
  iexact Hwp

theorem wp_increment
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {index : Nat} {value : UInt32} {updated : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hget : (⟨params, localValues, stack⟩ : Locals).get index = some (.i32 value))
    (hset : (⟨params, localValues, .i32 (1 + value) :: stack⟩ : Locals).set?
        index (.i32 (1 + value)) = some updated) :
    ▷ WP (.running
        ⟨{ updated with values := stack }, code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        increment index ++ code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  iintro Hwp
  simp only [increment, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet hget
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_add
  inext
  iapply Wasm.SmallStep.wp_localSet hset
  iexact Hwp

theorem wp_increment_nil
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {index : Nat} {value : UInt32} {updated : Locals}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hget : (⟨params, localValues, stack⟩ : Locals).get index = some (.i32 value))
    (hset : (⟨params, localValues, .i32 (1 + value) :: stack⟩ : Locals).set?
        index (.i32 (1 + value)) = some updated) :
    ▷ WP (.running
        ⟨{ updated with values := stack }, [], arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        increment index, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  simpa only [List.append_nil] using (wp_increment (s := s) (E := E) (Φ := Φ) (code := []) hget hset)

theorem wp_loop_löb_family_from
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {ι : Type} (locals : ι → Locals) (I : ι → IProp WasmHeapGF)
    (initial : ι) (initialLocals : Locals)
    {paramArity resultArity arity : Nat}
    {body code : Program} {remainder belowStack : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hinitial : locals initial = initialLocals)
    (hbelow : belowStack = (locals initial).values.drop paramArity)
    (body_closes : ∀ i,
      ⊢@{IProp WasmHeapGF} (iprop%
        ▷ (∀ (j : ι), I j -∗
          WP (loopBodyExpr (α := Unit) (locals j)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E {{ Φ }}) -∗
        I i -∗
          WP (loopBodyExpr (α := Unit) (locals i)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E {{ Φ }})) :
    I initial ⊢
      WP (.running
        ⟨initialLocals, .loop paramArity resultArity body :: code,
          arity, remainder, controls, calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  subst initialLocals
  exact wp_loop_löb_family locals I initial hbelow body_closes

theorem u32_ofNat_sub_eq {a b : Nat} (hle : b ≤ a) (ha : a < UInt32.size) :
    UInt32.ofNat a - UInt32.ofNat b = UInt32.ofNat (a - b) := by
  have hb : b < UInt32.size := Nat.lt_of_le_of_lt hle ha
  have hab : a - b < UInt32.size := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  apply UInt32.toNat.inj
  rw [UInt32.toNat_sub, UInt32.toNat_ofNat_of_lt' ha, UInt32.toNat_ofNat_of_lt' hb,
      UInt32.toNat_ofNat_of_lt' hab]
  have := (UInt32.ofNat a).toNat_lt
  rw [UInt32.toNat_ofNat_of_lt' ha] at this
  omega

end Wasm.Examples.Quicksort
