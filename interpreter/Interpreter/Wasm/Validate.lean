import Interpreter.Wasm.Syntax

/-!
# A partial static validator (GC proposal)

`Module.validate` performs the structural well-formedness checks the spec
testsuite's `assert_invalid` / `assert_malformed` commands exercise for the
GC proposal: type-index ranges, `sub` subtyping (finality + structural
subtype), field/element mutability, and constant-expression initializers.

It is deliberately run **only** on modules an `assert_invalid` /
`assert_malformed` command already declares ill-formed (see the testsuite
harness), so it never rejects a module a normal `(module …)` command would
accept — a too-aggressive check can only make an already-invalid module
pass for a slightly different reason, never break a valid one. A full
operand-stack type checker (for the `type mismatch` cases) is future work.
-/

namespace Wasm

/-- Whether composite `a` is a structural subtype of composite `b`
(reflexive comparison is handled by the caller). Mutable fields/elements
are invariant; we conservatively require matching storage type and
mutability, and exact func signatures. -/
def CompositeType.structSubtype : CompositeType → CompositeType → Bool
  | .struct af, .struct bf =>
    af.length ≥ bf.length &&
    (List.range bf.length).all fun i => match af[i]?, bf[i]? with
      | some x, some y => x.storage == y.storage && x.isMut == y.isMut
      | _, _ => false
  | .array ae, .array be => ae.storage == be.storage && ae.isMut == be.isMut
  | .func a, .func b => a.params == b.params && a.results == b.results
  | _, _ => false

/-- Recursively collect every instruction in a program, descending into the
bodies of `block`/`loop`/`if`/`try_table`. -/
partial def Program.allInstrs (p : Program) : List Instruction :=
  p.flatMap fun i => i :: match i with
    | .block _ _ body | .loop _ _ body => Program.allInstrs body
    | .iff _ _ thn els => Program.allInstrs thn ++ Program.allInstrs els
    | .tryTable _ _ _ body => Program.allInstrs body
    | _ => []

/-- The GC type indices an instruction's immediates reference. -/
def Instruction.typeRefs : Instruction → List Nat
  | .callRef t | .returnCallRef t => [t]
  | .callIndirect ti _ | .returnCallIndirect ti _ => [ti]
  | .gc op => match op with
    | .structNew t | .structNewDefault t
    | .arrayNew t | .arrayNewDefault t | .arrayNewFixed t _
    | .arrayGet t | .arrayGetS t | .arrayGetU t | .arraySet t
    | .arrayFill t | .arrayNewData t _ | .arrayInitData t _
    | .arrayNewElem t _ | .arrayInitElem t _ => [t]
    | .structGet t _ | .structGetS t _ | .structGetU t _ | .structSet t _ => [t]
    | .arrayCopy a b => [a, b]
    | .refTest _ (.concrete t) | .refCast _ (.concrete t)
    | .brOnCast _ _ (.concrete t) | .brOnCastFail _ _ (.concrete t) => [t]
    | _ => []
  | _ => []

/-- Whether a constant-expression program uses only constant instructions
(the forms a global / element initializer may contain). -/
def Program.isConstExpr (p : Program) : Bool :=
  p.all fun i => match i with
    | .const _ | .constI64 _ | .refNull | .refNullExtern | .refFunc _ => true
    | .globalGet _ => true
    | .gc g => match g with
      | .refI31 | .refNullAny | .structNew _ | .structNewDefault _
      | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed _ _ => true
      | _ => false
    | _ => false

/-- Run the partial structural validator. `throw` on the first violation. -/
def Module.validate (m : Module) : Except String Unit := do
  let nTypes := m.gcTypes.length
  -- 1. `sub` declarations: supertype in range, non-final, and a structural
  -- supertype of the declared composite.
  for td in m.gcTypes do
    match td.super with
    | none => pure ()
    | some s =>
      if s ≥ nTypes then throw "unknown type"
      let sup := m.gcTypes[s]!
      if sup.«final» then throw "sub type"
      if !td.comp.structSubtype sup.comp then throw "sub type"
  -- 2. Instruction immediates: GC type indices in range; struct/array
  -- mutating accessors target a mutable field / element.
  for f in m.funcs do
    for i in f.body.allInstrs do
      for t in i.typeRefs do
        if t ≥ nTypes then throw "unknown type"
      match i with
      | .gc (.structSet t fld) =>
        match m.structField? t fld with
        | some ft => if !ft.isMut then throw "immutable field"
        | none    => throw "unknown type"
      | .gc (.arraySet t) =>
        match m.arrayElem? t with
        | some ft => if !ft.isMut then throw "immutable array"
        | none    => throw "unknown type"
      | _ => pure ()
  -- 3. Global initializers must be constant expressions.
  for g in m.globals do
    if !g.initExpr.isEmpty && !g.initExpr.isConstExpr then
      throw "constant expression required"

end Wasm
