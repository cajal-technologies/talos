import Project.Mergesort.FunctionSpecs

/-!
# Reusable u64-array instruction rules

Rust lowers `base.add(index)` to `base + (index << 3)`.  CodeLib's existing
u64 rules use multiplication by eight, so this file provides the shift-shaped
counterparts shared by merge, copy, parse, and driver proofs.
-/

namespace Project.Mergesort.Machine

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic
open Wasm.SmallStep

def address64AtShift (baseIndex elementIndex : Nat) : Program :=
  [ .localGet baseIndex, .localGet elementIndex, .const 3, .shl, .add ]

def load64AtShift (baseIndex elementIndex : Nat) : Program :=
  address64AtShift baseIndex elementIndex ++ [.load64 0]

def store64AtShift (baseIndex elementIndex valueIndex : Nat) : Program :=
  address64AtShift baseIndex elementIndex ++ [.localGet valueIndex, .store64 0]

/-- Split a u64 array at a logical index while exposing the Rust pointer
offset used for the suffix. -/
theorem array64At_splitAt [WasmSmallStepGS hlc]
    (base : UInt32) (values : List UInt64) (index : Nat)
    (hindex : index ≤ values.length) :
    array64At base values ⊣⊢
      array64At base (values.take index) ∗
        array64At (base + 8 * UInt32.ofNat index) (values.drop index) := by
  rw [← List.take_append_drop index values]
  simpa [List.length_take, Nat.min_eq_left hindex] using
    array64At_append base (values.take index) (values.drop index)

/-- A suffix pointer does not wrap when it lies strictly inside a fitting
u64 array. -/
theorem offset64_toNat (base : UInt32) (length index : Nat)
    (hfit : base.toNat + 8 * length ≤ UInt32.size)
    (hindex : index < length) :
    (base + 8 * UInt32.ofNat index).toNat = base.toNat + 8 * index := by
  apply Mem.words64_slotAddr_toNat
  simp only [UInt32.size] at hfit ⊢
  omega

/-- Rust's shift-based address calculation is the standard u64 offset. -/
theorem shiftAddress64_eq (base : UInt32) (index : Nat) :
    (UInt32.ofNat index <<< (3 % 32)) + base =
      base + 8 * UInt32.ofNat index := by
  have hshift : UInt32.ofNat index <<< (3 % 32) =
      8 * UInt32.ofNat index := by
    bv_decide
  rw [hshift, UInt32.add_comm]

private theorem shift_eq_mul_eight (index : UInt32) :
    index <<< (3 % 32) = 8 * index := by
  bv_decide

private theorem arrayAddress64_toNat (base : UInt32) {index length : Nat}
    (hfit : base.toNat + 8 * length ≤ UInt32.size)
    (hindex : index < length) :
    (base + (UInt32.ofNat index <<< (3 % 32))).toNat =
      base.toNat + 8 * index := by
  rw [shift_eq_mul_eight]
  apply Mem.words64_slotAddr_toNat
  simp only [UInt32.size] at hfit ⊢
  omega

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

theorem twp_address64AtShift
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
    WP (.running
      ⟨⟨params, localValues,
          .i32 ((element <<< (3 % 32)) + base) :: stack⟩,
        code, arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        address64AtShift baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro Hwp
  simp only [address64AtShift, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_localGet hbase
  iapply Wasm.SmallStep.twp_localGet (by simpa using helement)
  iapply Wasm.SmallStep.twp_const
  iapply Wasm.SmallStep.twp_shl
  iapply Wasm.SmallStep.twp_add
  iexact Hwp

set_option maxHeartbeats 2000000 in
theorem twp_load64AtShift
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {baseIndex elementIndex : Nat} {base : UInt32}
    {input : List UInt64} {index : Nat} (hindex : index < input.length)
    (hfit : base.toNat + 8 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 (UInt32.ofNat index))) :
    array64At base input ∗
      (array64At base input -∗
        WP (.running
          ⟨⟨params, localValues, .i64 input[index] :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        load64AtShift baseIndex elementIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let address : UInt32 := base + (UInt32.ofNat index <<< (3 % 32))
  have hslot : address.toNat = base.toNat + 8 * index := by
    exact arrayAddress64_toNat base hfit hindex
  have hroom : address.toNat + 8 ≤ UInt32.size := by
    rw [hslot]
    omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := address64_steps address hroom
  have haddress :
      address = base + 8 * UInt32.ofNat index := by
    dsimp only [address]
    rw [shift_eq_mul_eight]
  have hsum :
      (UInt32.ofNat index <<< (3 % 32)) + base = address := by
    dsimp only [address]
    rw [UInt32.add_comm]
  iintro ⟨Harray, Hcont⟩
  ihave Hfocus := array64At_get base input index hindex $$ Harray
  icases Hfocus with ⟨Hword, Hclose⟩
  simp only [load64AtShift, List.append_assoc, List.cons_append,
    List.nil_append]
  iapply twp_address64AtShift hbase helement
  rw [hsum]
  ihave Hword' : pointsTo_u64 (address + 0) input[index] $$ [Hword]
  · rw [UInt32.add_zero]
    rw [haddress]
    iexact Hword
  iapply Wasm.SmallStep.twp_load64 (address := address) (offset := 0)
    input[index] (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hword'
  iintro Hword
  iapply Hcont
  iapply Hclose
  rw [UInt32.add_zero]
  rw [haddress]
  iexact Hword

/-- Raw instruction-shaped form of `twp_load64AtShift`, for generated code. -/
theorem twp_load64AtShift_raw
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {baseIndex elementIndex : Nat} {base : UInt32}
    {input : List UInt64} {index : Nat} (hindex : index < input.length)
    (hfit : base.toNat + 8 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 (UInt32.ofNat index))) :
    array64At base input ∗
      (array64At base input -∗
        WP (.running
          ⟨⟨params, localValues, .i64 input[index] :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        .localGet baseIndex :: .localGet elementIndex :: .const 3 :: .shl ::
          .add :: .load64 0 :: code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simpa only [load64AtShift, address64AtShift, List.append_assoc,
    List.cons_append, List.nil_append] using
    (twp_load64AtShift (hlc := hlc) (s := s) (E := E) (Φ := Φ)
      (baseIndex := baseIndex) (elementIndex := elementIndex) (base := base)
      (input := input) (index := index) hindex hfit hbase helement)

set_option maxHeartbeats 2000000 in
theorem twp_store64AtShift
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {baseIndex elementIndex valueIndex : Nat} {base : UInt32}
    {input : List UInt64} {index : Nat} {value : UInt64}
    (hindex : index < input.length)
    (hfit : base.toNat + 8 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 (UInt32.ofNat index)))
    (hvalue : (⟨params, localValues, stack⟩ : Locals).get valueIndex =
      some (.i64 value)) :
    array64At base input ∗
      (array64At base (input.set index value) -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        store64AtShift baseIndex elementIndex valueIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let address : UInt32 := base + (UInt32.ofNat index <<< (3 % 32))
  have hslot : address.toNat = base.toNat + 8 * index := by
    exact arrayAddress64_toNat base hfit hindex
  have hroom : address.toNat + 8 ≤ UInt32.size := by
    rw [hslot]
    omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := address64_steps address hroom
  have haddress :
      address = base + 8 * UInt32.ofNat index := by
    dsimp only [address]
    rw [shift_eq_mul_eight]
  have hsum :
      (UInt32.ofNat index <<< (3 % 32)) + base = address := by
    dsimp only [address]
    rw [UInt32.add_comm]
  iintro ⟨Harray, Hcont⟩
  ihave Hfocus := array64At_set base input index value hindex $$ Harray
  icases Hfocus with ⟨Hword, Hclose⟩
  simp only [store64AtShift, List.append_assoc, List.cons_append,
    List.nil_append]
  iapply twp_address64AtShift hbase helement
  rw [hsum]
  iapply Wasm.SmallStep.twp_localGet (by simpa using hvalue)
  ihave Hword' : pointsTo_u64 (address + 0) input[index] $$ [Hword]
  · rw [UInt32.add_zero]
    rw [haddress]
    iexact Hword
  iapply Wasm.SmallStep.twp_store64 (address := address) (offset := 0)
    (value := value) input[index] (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hword'
  iintro Hword
  iapply Hcont
  iapply Hclose
  rw [UInt32.add_zero]
  rw [haddress]
  iexact Hword

/-- Raw instruction-shaped form of `twp_store64AtShift`, for generated code. -/
theorem twp_store64AtShift_raw
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues stack : List Value}
    {baseIndex elementIndex valueIndex : Nat} {base : UInt32}
    {input : List UInt64} {index : Nat} {value : UInt64}
    (hindex : index < input.length)
    (hfit : base.toNat + 8 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 base))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 (UInt32.ofNat index)))
    (hvalue : (⟨params, localValues, stack⟩ : Locals).get valueIndex =
      some (.i64 value)) :
    array64At base input ∗
      (array64At base (input.set index value) -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        .localGet baseIndex :: .localGet elementIndex :: .const 3 :: .shl ::
          .add :: .localGet valueIndex :: .store64 0 :: code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  simpa only [store64AtShift, address64AtShift, List.append_assoc,
    List.cons_append, List.nil_append] using
    (twp_store64AtShift (hlc := hlc) (s := s) (E := E) (Φ := Φ)
      (baseIndex := baseIndex) (elementIndex := elementIndex)
      (valueIndex := valueIndex) (base := base) (input := input)
      (index := index) (value := value) hindex hfit hbase helement hvalue)

end Project.Mergesort.Machine
