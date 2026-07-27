import CodeLib.SepLogic.SmallStepLifting

/-!
# Contextual Iris chunks for fixed-width unsigned operations

An integer chunk states that a Wasm fragment transforms operands already on
the value stack and then continues with arbitrary code.  These are iris-lean
WP entailments over the authoritative small-step language; they replace the
former equivalences over Talos's fuel-bounded custom WP.
-/

namespace Wasm.RustStd

open Wasm
open Iris Iris.ProgramLogic Language.Notation

/-- A fixed-width unsigned integer type carried as a Wasm value. -/
class UIntWasm (T : Type) where
  toV : T → Value

open UIntWasm

instance instUIntWasmUInt32 : UIntWasm UInt32 where
  toV a := .i32 a

@[simp] theorem toV_u32 (a : UInt32) :
    (UIntWasm.toV a : Value) = .i32 a := rfl

/-- Contextual binary stack fragment.  The fragment may assume `pre`; after
computing `op a b`, it resumes an arbitrary small-step continuation. -/
abbrev BinChunk {A B C : Type}
    [UIntWasm A] [UIntWasm B] [UIntWasm C]
    (frag : Program) (op : A → B → C)
    (pre : A → B → Prop := fun _ _ => True) : Prop :=
  ∀ {α : Type} {hlc : HasLC} [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp Wasm.SepLogic.WasmHeapGF}
    {params localValues : List Value}
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List Wasm.SmallStep.ControlFrame}
    {calls : List Wasm.SmallStep.CallFrame}
    (a : A) (b : B) (vs : List Value) (_hpre : pre a b),
    ▷ WP (Wasm.SmallStep.Expr.running
      ⟨⟨params, localValues, toV (op a b) :: vs⟩,
        rest, arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨params, localValues, toV b :: toV a :: vs⟩,
        frag ++ rest, arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }}

/-- Contextual unary stack fragment. -/
abbrev UnChunk {T : Type} [UIntWasm T]
    (frag : Program) (op : T → T) : Prop :=
  ∀ {α : Type} {hlc : HasLC} [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp Wasm.SepLogic.WasmHeapGF}
    {params localValues : List Value}
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List Wasm.SmallStep.ControlFrame}
    {calls : List Wasm.SmallStep.CallFrame}
    (a : T) (vs : List Value),
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨params, localValues, toV (op a) :: vs⟩,
        rest, arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨params, localValues, toV a :: vs⟩,
        frag ++ rest, arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }}

end Wasm.RustStd
