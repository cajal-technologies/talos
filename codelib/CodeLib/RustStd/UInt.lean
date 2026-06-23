import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `CodeLib.RustStd.UInt` — the type-agnostic trunk

Common reasoning shared by Rust-style integer operations compiled to Wasm. A
`UIntWasm T` instance only fixes how a Lean type `T` is carried as a wasm
`Value` (`toV`); algebraic structure stays with the concrete operation theorem.
That keeps this trunk usable for homogeneous operations (`UInt64 → UInt64 →
UInt64`) and heterogeneous ones (`A → B → C`) whose operands/results have
different wasm encodings.

The reusable unit is a **chunk theorem**: "this instruction fragment, fed by
operands read from locals, computes this Lean operation". `HBinChunk` is the
general binary shape: if locals `i` and `j` contain encoded `a` and `b`, then
`[localGet i, localGet j] ++ frag` followed by any `rest` is equivalent to
running `rest` with the encoded result on top of the existing operand stack.
`BinChunk` is the homogeneous specialization of that shape, and `UnChunk` is
the unary variant. The body helpers produce `Continuation.Fallthrough`
postconditions for reusable instruction sequences; they deliberately do not
append or reason about `.ret`.
-/

namespace Wasm.RustStd

open Wasm

/-- A fixed-width unsigned integer type carried as a wasm `Value`. -/
class UIntWasm (T : Type) where
  /-- The wasm value carrying a `T`. -/
  toV : T → Value

section
variable {T : Type} [UIntWasm T]

open UIntWasm

/-- Frame post shared by every export body: globals + page count preserved. -/
abbrev framePost {α} (st : Store α) : Store α → Prop :=
  fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages

/-- Heterogeneous binary chunk shape. The operands are read from arbitrary
locals `i` and `j`, not preloaded onto the operand stack. -/
abbrev HBinChunk {A B C : Type} [UIntWasm A] [UIntWasm B] [UIntWasm C]
    (frag : Program) (op : A → B → C) : Prop :=
  ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α} {st : Store α}
    {P L : List Value} {rest : Program} (i j : Nat) (a : A) (b : B) (vs : List Value)
    (_ha : (⟨P, L, vs⟩ : Locals).get i = some (toV a))
    (_hb : (⟨P, L, vs⟩ : Locals).get j = some (toV b)),
    wp m ([.localGet i, .localGet j] ++ frag ++ rest) Q st ⟨P, L, vs⟩ env ↔
    wp m rest Q st ⟨P, L, toV (op a b) :: vs⟩ env

/-- Homogeneous binary chunk shape, defined from the heterogeneous one. -/
abbrev BinChunk (frag : Program) (op : T → T → T) : Prop :=
  HBinChunk frag op

/-- Chunk shape for a unary op (`not`), with the operand read from local `i`. -/
abbrev UnChunk (frag : Program) (op : T → T) : Prop :=
  ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α} {st : Store α}
    {P L : List Value} {rest : Program} (i : Nat) (a : T) (vs : List Value)
    (_ha : (⟨P, L, vs⟩ : Locals).get i = some (toV a)),
    wp m ([.localGet i] ++ frag ++ rest) Q st ⟨P, L, vs⟩ env ↔
    wp m rest Q st ⟨P, L, toV (op a) :: vs⟩ env

/-- Turn a binary chunk into a fallthrough theorem for any local frame. -/
theorem binBodyWp {frag : Program} {op : T → T → T} (chunk : BinChunk frag op)
    {α : Type} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i j : Nat) (a b : T) (vs : List Value)
    (ha : (⟨P, L, vs⟩ : Locals).get i = some (toV a))
    (hb : (⟨P, L, vs⟩ : Locals).get j = some (toV b)) :
    wp m ([.localGet i, .localGet j] ++ frag)
      (fun c => ∃ st',
        c = .Fallthrough st' ⟨P, L, toV (op a b) :: vs⟩ ∧ framePost st st')
      st ⟨P, L, vs⟩ env := by
  have h :
      wp m ([.localGet i, .localGet j] ++ frag ++ [])
        (fun c => ∃ st',
          c = .Fallthrough st' ⟨P, L, toV (op a b) :: vs⟩ ∧ framePost st st')
        st ⟨P, L, vs⟩ env := by
    rw [chunk i j a b vs ha hb]
    unfold framePost
    simp
  simpa only [List.append_nil] using h

/-- Turn a unary chunk into a fallthrough theorem for any local frame. -/
theorem unBodyWp {frag : Program} {op : T → T} (chunk : UnChunk frag op)
    {α : Type} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i : Nat) (a : T) (vs : List Value)
    (ha : (⟨P, L, vs⟩ : Locals).get i = some (toV a)) :
    wp m ([.localGet i] ++ frag)
      (fun c => ∃ st',
        c = .Fallthrough st' ⟨P, L, toV (op a) :: vs⟩ ∧ framePost st st')
      st ⟨P, L, vs⟩ env := by
  have h :
      wp m ([.localGet i] ++ frag ++ [])
        (fun c => ∃ st',
          c = .Fallthrough st' ⟨P, L, toV (op a) :: vs⟩ ∧ framePost st st')
        st ⟨P, L, vs⟩ env := by
    rw [chunk i a vs ha]
    unfold framePost
    simp
  simpa only [List.append_nil] using h

end

end Wasm.RustStd
