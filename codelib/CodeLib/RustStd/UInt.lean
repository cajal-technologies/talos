import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `CodeLib.RustStd.UInt` — the type-agnostic trunk

Common reasoning shared by every fixed-width unsigned integer operation compiled
to Wasm. The trunk is fully generic: it fixes *nothing* about a concrete width.
A `UIntWasm T` instance (defined per width in `U8/Basic.lean`, `U32/Basic.lean`,
`U64/Basic.lean`, …) only says how a Lean `T` is carried as a wasm `Value`
(`toV`); all algebraic structure stays with the concrete operation theorem. The
same trunk therefore serves homogeneous operations (`UInt64 → UInt64 → UInt64`)
and heterogeneous ones (`A → B → C`, e.g. a `u64` shift by a `u32`).

## The one reusable unit: a chunk

A **chunk** is the fact "this instruction fragment computes this Lean operation,
with the operands on the value stack". There is exactly one binary shape
(`BinChunk`) and one unary shape (`UnChunk`); both are stated in *stack* form
(operands already pushed), which is what you `rw` at an inlined occurrence. A
chunk that can trap on some inputs carries a precondition `pre` (default `True`,
so total ops never mention it).

## From a chunk to an export body

The compiler may instead emit the operation as a *called* function whose body
reads its operands from parameter locals. The body helpers bridge the gap once:
`wp_localGetPair` turns the two `localGet`s into the stack form, and
`binBodyReturnsWp` / `unBodyReturnsWp` / `checkedBinBodyReturnsWp` package that
plus the trailing `.ret` (and, for trapping ops, the guard `block`) into the
`Returns` fact the per-crate `TerminatesWith` spec bridges via `of_returns_wp`.
Because the body helpers consume the *same* chunk an inlined site uses, one chunk
proof serves both "inlined" and "called" — and we never need to know in advance
which the compiler chose.

## Concrete widths

The chunk algebra is width-generic; a `UIntWasm` instance supplies the carrier
for each concrete width. `u32` (carried as `.i32`) is provided just below — it is
the shift-count operand of a `u64` shift — and `u64` (carried as `.i64`) lives in
`U64/Basic`. Width-specific algebraic facts (a `u64` shift count modulo 64, …) are
ordinary Lean theorems proven in that width's files and fed to the chunk proof;
the trunk never sees them.

`UInt128` is intentionally absent: Lean core has no `UInt128`, and a wasm `Value`
carries only `i32`/`i64` (no `i128`), so a `u128` is not a single value — it would
need a `v128` or an `i64` pair, an encoding outside what `UIntWasm` models.
-/

namespace Wasm.RustStd

open Wasm

/-- A fixed-width unsigned integer type carried as a wasm `Value`. The chunk
algebra below is generic over the instance; each concrete width provides one. -/
class UIntWasm (T : Type) where
  /-- The wasm value carrying a `T`. -/
  toV : T → Value

open UIntWasm

/-- `u32` is carried as `Value.i32`, including as a mixed-width operand to a wider
operation such as a `u64` shift (whose count is a `u32`). -/
instance instUIntWasmUInt32 : UIntWasm UInt32 where
  toV a := .i32 a

@[simp] theorem toV_u32 (a : UInt32) : (UIntWasm.toV a : Value) = .i32 a := rfl

/-- Frame post shared by every export body: globals + page count preserved. -/
abbrev framePost {α} (st : Store α) : Store α → Prop :=
  fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages

/-! ## Chunks (the reusable stack-form facts) -/

/-- Binary chunk: with `toV b` on top of `toV a`, running `frag` then `rest`
equals running `rest` with `toV (op a b)` on the stack, provided the operands
satisfy `pre` (default `True`, dropped for total ops). Heterogeneous in the
operand/result encodings, so it covers both `T → T → T` and `A → B → C`. -/
abbrev BinChunk {A B C : Type} [UIntWasm A] [UIntWasm B] [UIntWasm C]
    (frag : Program) (op : A → B → C) (pre : A → B → Prop := fun _ _ => True) : Prop :=
  ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α} {st : Store α}
    {P L : List Value} {rest : Program} (a : A) (b : B) (vs : List Value)
    (_hpre : pre a b),
    wp m (frag ++ rest) Q st ⟨P, L, toV b :: toV a :: vs⟩ env ↔
    wp m rest Q st ⟨P, L, toV (op a b) :: vs⟩ env

/-- Unary chunk (`not`): with `toV a` on the stack, `frag` computes `toV (op a)`. -/
abbrev UnChunk {T : Type} [UIntWasm T] (frag : Program) (op : T → T) : Prop :=
  ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α} {st : Store α}
    {P L : List Value} {rest : Program} (a : T) (vs : List Value),
    wp m (frag ++ rest) Q st ⟨P, L, toV a :: vs⟩ env ↔
    wp m rest Q st ⟨P, L, toV (op a) :: vs⟩ env

/-! ## Reading operands from locals -/

/-- Two `localGet`s push the operands read from locals `i`, `j` (`b` on top of
`a`), turning a local-read body into the stack form a chunk consumes. The second
read ignores the value the first pushed — `Locals.get` indexes only
params/locals — which is why `hb` retypes to the pushed frame by `rfl`. This is
the whole `localGet`/`Locals.get` plumbing, in one place. -/
theorem wp_localGetPair {A B : Type} [UIntWasm A] [UIntWasm B]
    {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α} {st : Store α}
    {P L : List Value} {rest : Program} (i j : Nat) (a : A) (b : B) (vs : List Value)
    (ha : (⟨P, L, vs⟩ : Locals).get i = some (toV a))
    (hb : (⟨P, L, vs⟩ : Locals).get j = some (toV b)) :
    wp m (.localGet i :: .localGet j :: rest) Q st ⟨P, L, vs⟩ env ↔
    wp m rest Q st ⟨P, L, toV b :: toV a :: vs⟩ env := by
  have hb' : (⟨P, L, toV a :: vs⟩ : Locals).get j = some (toV b) := hb
  simp only [wp_localGet_cons, ha, hb']

/-! ## Export-body theorems

An opt-0 export body reads its operands from the parameter locals and returns:
`[localGet i, localGet j] ++ frag ++ [.ret]` (binary), `[localGet i] ++ frag ++
[.ret]` (unary), or that binary body wrapped in a trap-guard `block`. -/

/-- Discharge a (total) binary export body by reusing the chunk. -/
theorem binBodyReturnsWp {A B C : Type} [UIntWasm A] [UIntWasm B] [UIntWasm C]
    {frag : Program} {op : A → B → C} (chunk : BinChunk frag op)
    {α : Type} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i j : Nat) (a : A) (b : B) (vs : List Value)
    (ha : (⟨P, L, vs⟩ : Locals).get i = some (toV a))
    (hb : (⟨P, L, vs⟩ : Locals).get j = some (toV b)) :
    wp m ([.localGet i, .localGet j] ++ frag ++ [.ret])
      (Returns (toV (op a b) :: vs) (framePost st)) st ⟨P, L, vs⟩ env := by
  rw [show [.localGet i, .localGet j] ++ frag ++ [.ret]
        = .localGet i :: .localGet j :: (frag ++ [.ret]) from by simp,
      wp_localGetPair i j a b vs ha hb, chunk a b vs trivial]
  unfold Returns framePost
  simp

/-- Discharge a unary export body by reusing the chunk. -/
theorem unBodyReturnsWp {T : Type} [UIntWasm T]
    {frag : Program} {op : T → T} (chunk : UnChunk frag op)
    {α : Type} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i : Nat) (a : T) (vs : List Value)
    (ha : (⟨P, L, vs⟩ : Locals).get i = some (toV a)) :
    wp m ([.localGet i] ++ frag ++ [.ret])
      (Returns (toV (op a) :: vs) (framePost st)) st ⟨P, L, vs⟩ env := by
  rw [show [.localGet i] ++ frag ++ [.ret] = .localGet i :: (frag ++ [.ret]) from by simp]
  simp only [wp_localGet_cons, ha]
  rw [chunk a vs]
  unfold Returns framePost
  simp

/-! ## Guarded (trapping) export bodies

A trapping op compiles to its chunk wrapped in a zero-or-bounds-check `block`:
the guard falls through when the side condition holds and otherwise breaks out of
the block to a panic tail. One template covers them all — give it the chunk and a
proof that the guard falls through; it discharges the whole body for an arbitrary
panic `tail` (unreachable on the falling-through path, hence left to the call
site). -/

/-- Opt-0 guarded body: a `block` wrapping `guard ++ [localGet i, localGet j] ++
frag ++ [.ret]`. -/
abbrev checkedBinBody (guard frag : Program) (i j : Nat) : Program :=
  [.block 0 0 (guard ++ [.localGet i, .localGet j] ++ frag ++ [.ret])]

set_option maxRecDepth 4096 in
/-- Discharge a guarded binary export body by reusing the chunk. `guardWp` is the
guard's fall-through fact (e.g. `nonzeroGuardWp`), polymorphic in the block
continuation; the panic `tail` is arbitrary because the guarded path returns
before reaching it. -/
theorem checkedBinBodyReturnsWp {A B C : Type} [UIntWasm A] [UIntWasm B] [UIntWasm C]
    {frag guard : Program} {op : A → B → C} {pre : A → B → Prop}
    (chunk : BinChunk frag op pre)
    {α : Type} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i j : Nat) (a : A) (b : B) (vs : List Value) (tail : Program)
    (guardWp : ∀ {Q : Assertion α} {rest : Program},
        wp m (guard ++ rest) Q st ⟨P, L, vs⟩ env ↔ wp m rest Q st ⟨P, L, vs⟩ env)
    (ha : (⟨P, L, vs⟩ : Locals).get i = some (toV a))
    (hb : (⟨P, L, vs⟩ : Locals).get j = some (toV b))
    (hpre : pre a b) :
    wp m (checkedBinBody guard frag i j ++ tail)
      (Returns (toV (op a b) :: vs) (framePost st)) st ⟨P, L, vs⟩ env := by
  unfold checkedBinBody Returns framePost
  apply wp_block_cons
  rw [show guard ++ [.localGet i, .localGet j] ++ frag ++ [.ret]
        = guard ++ (.localGet i :: .localGet j :: (frag ++ [.ret])) from by simp,
      guardWp, wp_localGetPair i j a b vs ha hb, chunk a b vs hpre]
  simp

end Wasm.RustStd
