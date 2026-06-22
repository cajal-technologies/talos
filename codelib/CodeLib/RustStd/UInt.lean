import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `CodeLib.RustStd.UInt` — the type-agnostic trunk

Common reasoning shared by every fixed-width unsigned integer type. A
`UIntWasm T` instance just fixes how a `T` is carried as a wasm `Value`
(`toV`); everything reusable is proven once here, over an arbitrary instance,
and each per-type / per-function file (`U64/Add.lean`, `U32/Add.lean`, …) plugs
in its concrete instruction fragment.

The reusable unit is a **chunk theorem**: "this inlined instruction sequence,
run on stack operands, computes this Lean operation". A `BinChunk` is stated
with the operands on the value stack (`⟨P, L, toV b :: toV a :: vs⟩`) so it
`rw`s directly onto an inlined occurrence — no `.call`, no shim, exactly what
`opt-0`'s "same inlined sequence everywhere" buys us. The chunk for a given
`(type, op)` lives in that op's file and is discharged by reusing the
interpreter's atomic `wp_*` lemma; `binBodyWp`/`unBodyWp` here turn any chunk
into the function-body theorem the per-crate `TerminatesWith` spec bridges via
`of_returns_wp` (so the *same* chunk serves a called export and an inlined use).
-/

namespace Wasm.RustStd

open Wasm

/-- A fixed-width unsigned integer type carried as a wasm `Value`. The algebraic
operations come from `T`'s existing instances; only the wasm encoding is new. -/
class UIntWasm (T : Type)
    [Add T] [Sub T] [Mul T] [AndOp T] [OrOp T] [HXor T T T] [Complement T]
    [Div T] [Mod T] [OfNat T 0] [DecidableEq T] where
  /-- The wasm value carrying a `T`. -/
  toV : T → Value

section
variable {T : Type} [Add T] [Sub T] [Mul T] [AndOp T] [OrOp T] [HXor T T T]
  [Complement T] [Div T] [Mod T] [OfNat T 0] [DecidableEq T] [UIntWasm T]

open UIntWasm

/-- Frame post shared by every export body: globals + page count preserved. -/
abbrev framePost {α} (st : Store α) : Store α → Prop :=
  fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages

/-- Chunk shape for a binary op: with `toV b :: toV a :: vs` on the stack,
running `frag` then `rest` equals running `rest` with `toV (op a b)` on the
stack. The reusable inline-sequence theorem. -/
abbrev BinChunk (frag : Program) (op : T → T → T) : Prop :=
  ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α} {st : Store α}
    {P L : List Value} {rest : Program} (a b : T) (vs : List Value),
    wp m (frag ++ rest) Q st ⟨P, L, toV b :: toV a :: vs⟩ env ↔
    wp m rest Q st ⟨P, L, toV (op a b) :: vs⟩ env

/-- Chunk shape for a unary op (`not`). -/
abbrev UnChunk (frag : Program) (op : T → T) : Prop :=
  ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α} {st : Store α}
    {P L : List Value} {rest : Program} (a : T) (vs : List Value),
    wp m (frag ++ rest) Q st ⟨P, L, toV a :: vs⟩ env ↔
    wp m rest Q st ⟨P, L, toV (op a) :: vs⟩ env

/-- Turn a binary chunk into the opt-0 export-body theorem
`[localGet 0, localGet 1] ++ frag ++ [ret]` — by **reusing the chunk** (the
opaque `frag` means `wp_run` can't bypass it). The per-crate spec feeds this to
`of_returns_wp`. -/
theorem binBodyWp {frag : Program} {op : T → T → T} (chunk : BinChunk frag op)
    {α : Type} {m : Module} {env : HostEnv α} (st : Store α) (a b : T) (vs : List Value) :
    wp m ([.localGet 0, .localGet 1] ++ frag ++ [.ret])
      (Returns (toV (op a b) :: vs) (framePost st))
      st ⟨[toV a, toV b], [], vs⟩ env := by
  unfold Returns framePost
  simp only [List.cons_append, List.nil_append]
  wp_run
  simp
  rw [chunk a b vs]
  simp

/-- Turn a unary chunk into the opt-0 export-body theorem
`[localGet 0] ++ frag ++ [ret]`. -/
theorem unBodyWp {frag : Program} {op : T → T} (chunk : UnChunk frag op)
    {α : Type} {m : Module} {env : HostEnv α} (st : Store α) (a : T) (vs : List Value) :
    wp m ([.localGet 0] ++ frag ++ [.ret])
      (Returns (toV (op a) :: vs) (framePost st))
      st ⟨[toV a], [], vs⟩ env := by
  unfold Returns framePost
  simp only [List.cons_append, List.nil_append]
  wp_run
  simp
  rw [chunk a vs]
  simp

end

end Wasm.RustStd
