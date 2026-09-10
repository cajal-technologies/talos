import CodeLib.Examples.UInt32Array
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Total-WP laws for UInt32 array combinators
-/

namespace Wasm.Examples.UInt32Array

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open Wasm.SmallStep


theorem arrayAddress_toNat (base : UInt32) {index length : Nat}
    (hfit : base.toNat + 4 * length ≤ UInt32.size)
    (hindex : index < length) :
    (base + UInt32.ofNat index * 4).toNat =
      base.toNat + 4 * index := by
  simpa [UInt32.mul_comm] using Mem.words32_slotAddr_toNat base index (by
    simpa only [UInt32.size] using Nat.lt_of_lt_of_le (by omega) hfit)

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
  have hroom : (base + 4 * UInt32.ofNat k).toNat + 4 ≤ UInt32.size := by omega
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
  have h1' : ((address + 0) + 1).toNat = (address + 0).toNat + 1 := by simpa using h1
  have h2' : ((address + 0) + 2).toNat = (address + 0).toNat + 2 := by simpa using h2
  have h3' : ((address + 0) + 3).toNat = (address + 0).toNat + 3 := by simpa using h3
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

end Wasm.Examples.UInt32Array
