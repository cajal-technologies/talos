import CodeLib.Examples.MergeSort.Pure
import CodeLib.SepLogic.SmallStepTotalLifting

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
  rw [hsize] at hfit ⊢; omega

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

/-! ## Total-WP derived laws -/

theorem twp_lessLocal
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues stack : List Value}
    {lhsIndex rhsIndex : Nat} {lhs rhs : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hlhs : (⟨params, localValues, stack⟩ : Locals).get lhsIndex =
      some (.i32 lhs))
    (hrhs : (⟨params, localValues, stack⟩ : Locals).get rhsIndex =
      some (.i32 rhs)) :
    WP (.running
      ⟨⟨params, localValues,
          .i32 (if lhs < rhs then 1 else 0) :: stack⟩,
        code, arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        lessLocal lhsIndex rhsIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }] := by
  iintro Hwp
  simp only [lessLocal, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_localGet hlhs
  iapply Wasm.SmallStep.twp_localGet (by simpa using hrhs)
  wasm_twp_pures [twp_ltU]
  iexact Hwp

theorem twp_address
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
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
        code, arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        address baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }] := by
  iintro Hwp
  simp only [address, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_localGet hbase
  iapply Wasm.SmallStep.twp_localGet (by simpa using helement)
  wasm_twp_pures [twp_const twp_mul twp_add]
  iexact Hwp

theorem twp_increment
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues stack : List Value}
    {index : Nat} {value : UInt32} {updated : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hget : (⟨params, localValues, stack⟩ : Locals).get index =
      some (.i32 value))
    (hset : (⟨params, localValues, .i32 (1 + value) :: stack⟩ :
      Locals).set? index (.i32 (1 + value)) = some updated) :
    WP (.running
      ⟨{ updated with values := stack }, code, arity, remainder,
        controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩, increment index ++ code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hwp
  simp only [increment, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_localGet hget
  wasm_twp_pures [twp_const twp_add]
  iapply_exact Wasm.SmallStep.twp_localSet hset with Hwp

theorem twp_increment_nil
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues stack : List Value}
    {index : Nat} {value : UInt32} {updated : Locals}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hget : (⟨params, localValues, stack⟩ : Locals).get index =
      some (.i32 value))
    (hset : (⟨params, localValues, .i32 (1 + value) :: stack⟩ :
      Locals).set? index (.i32 (1 + value)) = some updated) :
    WP (.running
      ⟨{ updated with values := stack }, [], arity, remainder,
        controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩, increment index,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  simpa only [List.append_nil] using
    (twp_increment (s := s) (E := E) (Φ := Φ)
      (code := []) hget hset)

theorem twp_loadAt_cell
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
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
    pointsTo_u32 0 address word ∗
      (pointsTo_u32 0 address word -∗
        WP (.running
          ⟨⟨params, localValues, .i32 word :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        loadAt baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have h1' : ((address + 0) + 1).toNat =
      (address + 0).toNat + 1 := by simpa using h1
  have h2' : ((address + 0) + 2).toNat =
      (address + 0).toNat + 2 := by simpa using h2
  have h3' : ((address + 0) + 3).toNat =
      (address + 0).toNat + 3 := by simpa using h3
  iintro ⟨Hword, Hcont⟩
  simp only [loadAt, List.append_assoc, List.cons_append,
    List.nil_append]
  iapply twp_address hbase helement
  rw [haddress]
  ihave HwordLater : pointsTo_u32 0 (address + 0) word $$ [Hword]
  ·
    irw_exact [UInt32.add_zero] with Hword
  wasm_twp_bind Wasm.SmallStep.twp_load32
    (address := address) (offset := 0)
    word (by simp) h1' h2' h3' with HwordLater => Hword
  iapply Hcont
  irw_exact [UInt32.add_zero] with Hword

set_option maxHeartbeats 2000000 in
theorem twp_loadAt
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
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
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        loadAt baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hslot :
      (base + 4 * UInt32.ofNat k).toNat = base.toNat + 4 * k := by
    simpa [UInt32.mul_comm] using arrayAddress_toNat base hfit hk
  have hroom : (base + 4 * UInt32.ofNat k).toNat + 4 ≤ UInt32.size := by
    omega
  have hroom' :
      (base + 4 * UInt32.ofNat k).toNat + 4 ≤ 4294967296 := by
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

theorem twp_store32_cell
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
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
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 newWord :: .i32 address :: stack⟩,
        .store32 0 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have h1' : ((address + 0) + 1).toNat = (address + 0).toNat + 1 := by
    simpa using h1
  have h2' : ((address + 0) + 2).toNat = (address + 0).toNat + 2 := by
    simpa using h2
  have h3' : ((address + 0) + 3).toNat = (address + 0).toNat + 3 := by
    simpa using h3
  iintro ⟨Hword, Hcont⟩
  ihave HwordLater : pointsTo_u32 0 (address + 0) oldWord $$ [Hword]
  ·
    irw_exact [UInt32.add_zero] with Hword
  wasm_twp_bind Wasm.SmallStep.twp_store32
    (address := address) (offset := 0) oldWord
    (by simp) h1' h2' h3' with HwordLater => Hword
  ihave Hword' : pointsTo_u32 0 address newWord $$ [Hword]
  · irw_exact [UInt32.add_zero] with Hword
  iapply_exact Hcont with Hword'

set_option maxHeartbeats 2000000 in
theorem twp_copyAt
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
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
    arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
      (arrayAt 0 source input ∗
        arrayAt 0 temporary (scratch.set k input[i]) -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        storeAt temporaryIndex temporaryElement
          (loadAt sourceIndex sourceElement) ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let destination := 4 * UInt32.ofNat k + temporary
  have hslot :
      destination.toNat = temporary.toNat + 4 * k := by
    dsimp [destination]
    rw [UInt32.add_comm]
    simpa [UInt32.mul_comm] using
      arrayAddress_toNat temporary htemporaryFit hk
  have hroom : destination.toNat + 4 ≤ UInt32.size := by
    omega
  obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 destination (by
    simpa only [UInt32.size] using hroom)
  iintro ⟨Hsource, Htemporary, Hcont⟩
  simp only [storeAt, List.append_assoc]
  iapply twp_address htemporary htemporaryElement
  iapply twp_loadAt hi hsourceFit
    (by simpa using hsource)
    (by simpa using hsourceElement)
  iframe; iintro Hsource
  ihave ⟨Hcell, Hclose⟩ := arrayAt_set 0 temporary scratch k input[i] hk $$ Htemporary
  simp only [List.cons_append, List.nil_append]
  ihave Hcell' : pointsTo_u32 0 destination scratch[k] $$ [Hcell]
  · dsimp [destination]
    irw_exact [UInt32.add_comm] with Hcell
  iapply_splitl_exact twp_store32_cell h1 h2 h3 with Hcell'
  iintro Hcell
  iapply_splitl_exact Hcont with Hsource
  iapply Hclose
  ihave Hcell' :
      pointsTo_u32 0
        (temporary + 4 * UInt32.ofNat k) input[i] $$ [Hcell]
  · dsimp [destination]
    irw_exact [UInt32.add_comm] with Hcell
  iexact Hcell'


end Wasm.Examples.MergeSort
