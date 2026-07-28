import CodeLib.Examples.MergeSort.Pure

/-!
# Derived laws for the merge-sort proof

Address arithmetic and compact contextual WP rules for the instruction
sequences used by the handwritten implementation.
-/

namespace Wasm.Examples.MergeSort

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open Wasm.SmallStep

theorem ValidLayout.source_fits
    {source temporary : UInt32} {length : Nat}
    (h : ValidLayout source temporary length) :
    source.toNat + 4 * length ≤ UInt32.size := h.1

theorem ValidLayout.temporary_fits
    {source temporary : UInt32} {length : Nat}
    (h : ValidLayout source temporary length) :
    temporary.toNat + 4 * length ≤ UInt32.size := h.2.1

theorem ValidLayout.length_lt
    {source temporary : UInt32} {length : Nat}
    (h : ValidLayout source temporary length) :
    length < UInt32.size := by
  have hfit := h.source_fits
  have hsize : UInt32.size = 4294967296 := rfl
  rw [hsize] at hfit ⊢
  omega

theorem u32_ofNat_succ {n : Nat} (h : n + 1 < UInt32.size) :
    UInt32.ofNat n + 1 = UInt32.ofNat (n + 1) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_add]
  have hn : n < UInt32.size := by omega
  rw [UInt32.toNat_ofNat_of_lt' hn]
  have hone : (1 : UInt32).toNat = 1 := by decide
  rw [hone, Nat.mod_eq_of_lt]
  · symm
    exact UInt32.toNat_ofNat_of_lt' h
  · simpa only [UInt32.size] using h

theorem u32_ofNat_add {a b : Nat} (h : a + b < UInt32.size) :
    UInt32.ofNat a + UInt32.ofNat b = UInt32.ofNat (a + b) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_add,
    UInt32.toNat_ofNat_of_lt' (by omega),
    UInt32.toNat_ofNat_of_lt' (by omega),
    Nat.mod_eq_of_lt h,
    UInt32.toNat_ofNat_of_lt' h]

theorem u32_ofNat_mul {a b : Nat} (h : a * b < UInt32.size) :
    UInt32.ofNat a * UInt32.ofNat b = UInt32.ofNat (a * b) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have haSize : a < UInt32.size :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right a hb) h
  have hbSize : b < UInt32.size :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left b ha) h
  apply UInt32.toNat.inj
  rw [UInt32.toNat_mul, UInt32.toNat_ofNat_of_lt' haSize,
    UInt32.toNat_ofNat_of_lt' hbSize, Nat.mod_eq_of_lt h,
    UInt32.toNat_ofNat_of_lt' h]

theorem arrayAddress_toNat (base : UInt32) {index length : Nat}
    (hfit : base.toNat + 4 * length ≤ UInt32.size)
    (hindex : index < length) :
    (base + UInt32.ofNat index * 4).toNat =
      base.toNat + 4 * index := by
  have hi : index < UInt32.size := by omega
  have hp : index * 4 < UInt32.size := by omega
  rw [UInt32.toNat_add, UInt32.toNat_mul,
    UInt32.toNat_ofNat_of_lt' hi]
  have hfour : (4 : UInt32).toNat = 4 := by decide
  rw [hfour, Nat.mod_eq_of_lt hp, Nat.mul_comm index 4]
  apply Nat.mod_eq_of_lt
  change base.toNat + 4 * index < UInt32.size
  omega

theorem wp_lessLocal
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {lhsIndex rhsIndex : Nat} {lhs rhs : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hlhs : (⟨params, localValues, stack⟩ : Locals).get lhsIndex =
      some (.i32 lhs))
    (hrhs : (⟨params, localValues, stack⟩ : Locals).get rhsIndex =
      some (.i32 rhs)) :
    ▷ WP (.running
      ⟨⟨params, localValues,
          .i32 (if lhs < rhs then 1 else 0) :: stack⟩,
        code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        lessLocal lhsIndex rhsIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} := by
  iintro Hwp
  simp only [lessLocal, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet hlhs
  inext
  iapply Wasm.SmallStep.wp_localGet (by simpa using hrhs)
  inext
  iapply Wasm.SmallStep.wp_ltU rfl
  iexact Hwp

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

theorem wp_increment
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {index : Nat} {value : UInt32} {updated : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hget : (⟨params, localValues, stack⟩ : Locals).get index =
      some (.i32 value))
    (hset : (⟨params, localValues, .i32 (1 + value) :: stack⟩ :
      Locals).set? index (.i32 (1 + value)) = some updated) :
    ▷ WP (.running
      ⟨{ updated with values := stack }, code, arity, remainder,
        controls, calls⟩ : Expr Unit) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩, increment index ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
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
    (hget : (⟨params, localValues, stack⟩ : Locals).get index =
      some (.i32 value))
    (hset : (⟨params, localValues, .i32 (1 + value) :: stack⟩ :
      Locals).set? index (.i32 (1 + value)) = some updated) :
    ▷ WP (.running
      ⟨{ updated with values := stack }, [], arity, remainder,
        controls, calls⟩ : Expr Unit) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩, increment index,
        arity, remainder, controls, calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  simpa only [List.append_nil] using
    (wp_increment (s := s) (E := E) (Φ := Φ)
      (code := []) hget hset)

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
          arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} := by
  subst initialLocals
  exact wp_loop_löb_family locals I initial hbelow body_closes

theorem wp_loadAt_cell
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {baseIndex elementIndex : Nat} {base element address word : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 element))
    (haddress : 4 * element + base = address)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    pointsTo_u32 address word ∗
      (pointsTo_u32 address word -∗
        WP (.running
          ⟨⟨params, localValues, .i32 word :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        loadAt baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  have h1' : ((address + 0) + 1).toNat =
      (address + 0).toNat + 1 := by simpa using h1
  have h2' : ((address + 0) + 2).toNat =
      (address + 0).toNat + 2 := by simpa using h2
  have h3' : ((address + 0) + 3).toNat =
      (address + 0).toNat + 3 := by simpa using h3
  iintro ⟨Hword, Hcont⟩
  simp only [loadAt, List.append_assoc, List.cons_append,
    List.nil_append]
  iapply wp_address hbase helement
  inext
  rw [haddress]
  ihave HwordLater : ▷ pointsTo_u32 (address + 0) word $$ [Hword]
  · inext
    rw [UInt32.add_zero]
    iexact Hword
  iapply Wasm.SmallStep.wp_load32
    (address := address) (offset := 0)
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
  have hslot :
      (base + 4 * UInt32.ofNat k).toNat = base.toNat + 4 * k := by
    simpa [UInt32.mul_comm] using arrayAddress_toNat base hfit hk
  have hroom : (base + 4 * UInt32.ofNat k).toNat + 4 ≤ UInt32.size := by
    rw [hslot]
    omega
  have hroom' :
      (base + 4 * UInt32.ofNat k).toNat + 4 ≤ 4294967296 := by
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

theorem wp_store32_cell
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
  have h1' : ((address + 0) + 1).toNat = (address + 0).toNat + 1 := by
    simpa using h1
  have h2' : ((address + 0) + 2).toNat = (address + 0).toNat + 2 := by
    simpa using h2
  have h3' : ((address + 0) + 3).toNat = (address + 0).toNat + 3 := by
    simpa using h3
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
theorem wp_copyAt
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {sourceIndex sourceElement temporaryIndex temporaryElement : Nat}
    {source temporary : UInt32}
    {input scratch : List UInt32} {i k : Nat}
    (hi : i < input.length) (hk : k < scratch.length)
    (hsourceFit : source.toNat + 4 * input.length ≤ UInt32.size)
    (htemporaryFit :
      temporary.toNat + 4 * scratch.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hsource :
      (⟨params, localValues, stack⟩ : Locals).get sourceIndex =
        some (.i32 source))
    (hsourceElement :
      (⟨params, localValues, stack⟩ : Locals).get sourceElement =
        some (.i32 (UInt32.ofNat i)))
    (htemporary :
      (⟨params, localValues, stack⟩ : Locals).get temporaryIndex =
        some (.i32 temporary))
    (htemporaryElement :
      (⟨params, localValues, stack⟩ : Locals).get temporaryElement =
        some (.i32 (UInt32.ofNat k))) :
    arrayAt source input ∗ arrayAt temporary scratch ∗
      (arrayAt source input ∗
        arrayAt temporary (scratch.set k input[i]) -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        storeAt temporaryIndex temporaryElement
          (loadAt sourceIndex sourceElement) ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  let destination := 4 * UInt32.ofNat k + temporary
  have hslot :
      destination.toNat = temporary.toNat + 4 * k := by
    dsimp [destination]
    rw [UInt32.add_comm]
    simpa [UInt32.mul_comm] using
      arrayAddress_toNat temporary htemporaryFit hk
  have hroom : destination.toNat + 4 ≤ UInt32.size := by
    rw [hslot]
    omega
  have h1 : (destination + 1).toNat = destination.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap destination 1
      (by decide) (by
        have : destination.toNat + 4 ≤ 4294967296 := by
          simpa only [UInt32.size] using hroom
        omega)
  have h2 : (destination + 2).toNat = destination.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap destination 2
      (by decide) (by
        have : destination.toNat + 4 ≤ 4294967296 := by
          simpa only [UInt32.size] using hroom
        omega)
  have h3 : (destination + 3).toNat = destination.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap destination 3
      (by decide) (by
        have : destination.toNat + 4 ≤ 4294967296 := by
          simpa only [UInt32.size] using hroom
        omega)
  iintro ⟨Hsource, Htemporary, Hcont⟩
  simp only [storeAt, List.append_assoc]
  iapply wp_address htemporary htemporaryElement
  inext
  iapply wp_loadAt hi hsourceFit
    (by simpa using hsource)
    (by simpa using hsourceElement)
  isplitl [Hsource]
  · iexact Hsource
  iintro Hsource
  ihave Hfocus := arrayAt_set temporary scratch k input[i] hk $$ Htemporary
  icases Hfocus with ⟨Hcell, Hclose⟩
  simp only [List.cons_append, List.nil_append]
  ihave Hcell' : pointsTo_u32 destination scratch[k] $$ [Hcell]
  · dsimp [destination]
    rw [UInt32.add_comm]
    iexact Hcell
  iapply wp_store32_cell h1 h2 h3
  isplitl [Hcell']
  · iexact Hcell'
  iintro Hcell
  iapply Hcont
  isplitl [Hsource]
  · iexact Hsource
  iapply Hclose
  ihave Hcell' :
      pointsTo_u32
        (temporary + 4 * UInt32.ofNat k) input[i] $$ [Hcell]
  · dsimp [destination]
    rw [UInt32.add_comm]
    iexact Hcell
  iexact Hcell'

end Wasm.Examples.MergeSort
