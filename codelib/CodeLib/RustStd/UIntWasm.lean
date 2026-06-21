import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `UIntWasm` — polymorphic reuse of inlined-instruction-chunk proofs

A `UIntWasm T` instance records, for a fixed-width unsigned integer type `T`,
the inlined wasm instruction *fragments* its operators compile to at
`opt-level = 0`, paired with the proof that each fragment computes the
corresponding Lean operation on `T`. These **chunk facts** are the reusable
theorems: any client wasm body containing the fragment inline rewrites it to
clean math, with no `.call` and no shim — exactly what `opt-0` guarantees (the
same inlined sequence everywhere).

Each chunk fact is discharged per instance by reusing the interpreter's atomic
`wp_*` lemmas (one line each). The generic export-body helpers are proven once
over the class and reused by every width (`UInt64` now; `UInt32`, … are just
new instances). Width-specific shapes (the shift-count `extend`) live in the
per-type modules.

A chunk fact is phrased with the operands already on the value stack
(`⟨P, L, toV b :: toV a :: vs⟩`), so a client discharges an inline occurrence by
`rw [add_chunk …]` — no stack side-condition to thread.
-/

namespace Wasm.RustStd

open Wasm

/-- Sequencing shape shared by every binary chunk fact: with operands
`toV b :: toV a :: vs` on the stack, running `frag` then `rest` equals running
`rest` with `toV (op a b)` on the stack. -/
abbrev BinChunk {T : Type} (toV : T → Value) (frag : Program) (op : T → T → T) : Prop :=
  ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α} {st : Store α}
    {P L : List Value} {rest : Program} (a b : T) (vs : List Value),
    wp m (frag ++ rest) Q st ⟨P, L, toV b :: toV a :: vs⟩ env ↔
    wp m rest Q st ⟨P, L, toV (op a b) :: vs⟩ env

/-- A fixed-width unsigned integer type and the inlined fragments + chunk facts
its operators compile to. -/
class UIntWasm (T : Type)
    [Add T] [Sub T] [Mul T] [AndOp T] [OrOp T] [HXor T T T] [Complement T]
    [Div T] [Mod T] [OfNat T 0] [DecidableEq T] where
  /-- The wasm value carrying a `T`. -/
  toV : T → Value
  -- straight-line binary ops (single wasm instruction each)
  addFrag : Program
  add_chunk : BinChunk toV addFrag (· + ·)
  subFrag : Program
  sub_chunk : BinChunk toV subFrag (· - ·)
  mulFrag : Program
  mul_chunk : BinChunk toV mulFrag (· * ·)
  andFrag : Program
  and_chunk : BinChunk toV andFrag (· &&& ·)
  orFrag : Program
  or_chunk : BinChunk toV orFrag (· ||| ·)
  xorFrag : Program
  xor_chunk : BinChunk toV xorFrag (· ^^^ ·)
  /-- Inlined fragment for `!` (bitwise complement): `const allOnes; xor`. -/
  notFrag : Program
  not_chunk : ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
      {st : Store α} {P L : List Value} {rest : Program} (a : T) (vs : List Value),
      wp m (notFrag ++ rest) Q st ⟨P, L, toV a :: vs⟩ env ↔
        wp m rest Q st ⟨P, L, toV (~~~a) :: vs⟩ env
  /-- Zero-test fragment used by the div/rem guard: pops the divisor, pushes the
  i32 boolean `b == 0`. -/
  isZeroFrag : Program
  isZero_chunk : ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
      {st : Store α} {P L : List Value} {rest : Program} (b : T) (vs : List Value),
      wp m (isZeroFrag ++ rest) Q st ⟨P, L, toV b :: vs⟩ env ↔
        wp m rest Q st ⟨P, L, .i32 (if b = 0 then 1 else 0) :: vs⟩ env
  /-- Bare inlined fragment for `/` (the zero-divisor guard `block` is peeled
  with `wp_block_cons`). Requires `b ≠ 0`. -/
  divFrag : Program
  div_chunk : ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
      {st : Store α} {P L : List Value} {rest : Program} (a b : T) (vs : List Value), b ≠ 0 →
      (wp m (divFrag ++ rest) Q st ⟨P, L, toV b :: toV a :: vs⟩ env ↔
        wp m rest Q st ⟨P, L, toV (a / b) :: vs⟩ env)
  /-- Bare inlined fragment for `%`. Requires `b ≠ 0`. -/
  remFrag : Program
  rem_chunk : ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
      {st : Store α} {P L : List Value} {rest : Program} (a b : T) (vs : List Value), b ≠ 0 →
      (wp m (remFrag ++ rest) Q st ⟨P, L, toV b :: toV a :: vs⟩ env ↔
        wp m rest Q st ⟨P, L, toV (a % b) :: vs⟩ env)

/-! ## Generic export-body helpers

`opt-0` compiles each inlining binary operator export to
`[localGet 0, localGet 1] ++ frag ++ [ret]`. These prove the body returns the
clean Lean result by **reusing the chunk fact** — `frag` is opaque here, so
`wp_run` cannot step it and the chunk theorem is the only way through. Stated in
the fuel-free `wp`/`Returns` form the per-crate specs bridge via
`of_returns_wp`. Polymorphic over the `UIntWasm` instance. -/

section Helpers
variable {T : Type} [Add T] [Sub T] [Mul T] [AndOp T] [OrOp T] [HXor T T T]
  [Complement T] [Div T] [Mod T] [OfNat T 0] [DecidableEq T] [UIntWasm T]
  {α : Type} {m : Module} {env : HostEnv α}

open UIntWasm

/-- Frame post shared by every export body (globals + page count preserved). -/
abbrev framePost (st : Store α) : Store α → Prop :=
  fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages

/-- Export body of a binary inlining op, discharged by reusing its chunk fact. -/
theorem binBodyWp {frag : Program} {op : T → T → T} (chunk : BinChunk (toV) frag op)
    (st : Store α) (a b : T) (vs : List Value) :
    wp m ([.localGet 0, .localGet 1] ++ frag ++ [.ret])
      (Returns (toV (op a b) :: vs) (framePost st))
      st ⟨[toV a, toV b], [], vs⟩ env := by
  unfold Returns framePost
  simp only [List.cons_append, List.nil_append]
  wp_run
  simp
  rw [chunk a b vs]
  simp

/-- Export body of `not` (`[localGet 0] ++ notFrag ++ [ret]`). -/
theorem notBodyWp (st : Store α) (a : T) (vs : List Value) :
    wp m ([.localGet 0] ++ notFrag (T := T) ++ [.ret])
      (Returns (toV (~~~a) :: vs) (framePost st))
      st ⟨[toV a], [], vs⟩ env := by
  unfold Returns framePost
  simp only [List.cons_append, List.nil_append]
  wp_run
  simp
  rw [not_chunk a vs]
  simp

end Helpers

/-- `UInt64` ⇒ wasm `i64`; operators compile to the `i64.*` opcodes. -/
instance : UIntWasm UInt64 where
  toV a := .i64 a
  addFrag := [.addI64]
  add_chunk := by intro α m env Q st P L rest a b vs
                  simp only [List.cons_append, List.nil_append, wp_addI64_cons]
  subFrag := [.subI64]
  sub_chunk := by intro α m env Q st P L rest a b vs
                  simp only [List.cons_append, List.nil_append, wp_subI64_cons]
  mulFrag := [.mulI64]
  mul_chunk := by intro α m env Q st P L rest a b vs
                  simp only [List.cons_append, List.nil_append, wp_mulI64_cons]
  andFrag := [.andI64]
  and_chunk := by intro α m env Q st P L rest a b vs
                  simp only [List.cons_append, List.nil_append, wp_andI64_cons]
  orFrag := [.orI64]
  or_chunk := by intro α m env Q st P L rest a b vs
                 simp only [List.cons_append, List.nil_append, wp_orI64_cons]
  xorFrag := [.xorI64]
  xor_chunk := by intro α m env Q st P L rest a b vs
                  simp only [List.cons_append, List.nil_append, wp_xorI64_cons]
  notFrag := [.constI64 18446744073709551615, .xorI64]
  not_chunk := by
    intro α m env Q st P L rest a vs
    simp only [List.cons_append, List.nil_append, wp_constI64_cons, wp_xorI64_cons]
    rw [show a ^^^ 18446744073709551615 = ~~~a from by bv_decide]
  isZeroFrag := [.constI64 0, .eqI64]
  isZero_chunk := by
    intro α m env Q st P L rest b vs
    simp only [List.cons_append, List.nil_append, wp_constI64_cons, wp_eqI64_cons]
  divFrag := [.divUI64]
  div_chunk := by intro α m env Q st P L rest a b vs hb
                  simp only [List.cons_append, List.nil_append, wp_divUI64_cons, hb, ↓reduceIte]
  remFrag := [.remUI64]
  rem_chunk := by intro α m env Q st P L rest a b vs hb
                  simp only [List.cons_append, List.nil_append, wp_remUI64_cons, hb, ↓reduceIte]

end Wasm.RustStd
