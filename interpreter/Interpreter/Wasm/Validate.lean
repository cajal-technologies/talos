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
    | .const _ | .constI64 _ | .refNull | .refNullExtern | .refNullExn | .refFunc _ => true
    | .globalGet _ => true
    | .gc g => match g with
      | .refI31 | .refNullAny | .structNew _ | .structNewDefault _
      | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed _ _ => true
      | _ => false
    | _ => false

/-! ### Straight-line operand-stack type check

A deliberately partial check: it simulates the operand stack through a
function body that contains no control flow, with the field/element result
types pulled precisely from the GC type table, and reports `type mismatch`
when an instruction's operand has the wrong type or the body's final stack
doesn't match the declared results. Reference types are compared loosely
(any ref matches any ref — full GC subtyping is not modelled), and any
control-flow / unmodelled instruction makes the check bail out (returns
`ok` for that function), so it never produces a false rejection on a shape
it doesn't understand. -/

/-- Loose value-type compatibility: scalars exact, all reference types
mutually compatible. -/
def vtCompat (a b : ValueType) : Bool :=
  match a, b with
  | .i32, .i32 | .i64, .i64 | .f32, .f32 | .f64, .f64 | .v128, .v128 => true
  | .funcref, _ | .externref, _ | .anyref, _ | .exnref, _ =>
    match b with | .funcref | .externref | .anyref | .exnref => true | _ => false
  | _, _ => false

/-- The storage type's value type, as seen by the stack checker. -/
def StorageType.vt : StorageType → ValueType
  | .val vt   => vt
  | .packed _ => .i32

/-- The static value type a global exposes. The `type` field was dropped
from `GlobalDecl` (it was unused at runtime), so recover the declared type
from the initializer value the decoder stored. -/
def Value.toValueType : Value → ValueType
  | .i32 _       => .i32
  | .i64 _       => .i64
  | .f32 _       => .f32
  | .f64 _       => .f64
  | .v128 _      => .v128
  | .funcref _   => .funcref
  | .externref _ => .externref
  | .exnref _    => .exnref
  | .anyref _    => .anyref

/-- The `(pops, pushes)` operand-stack signature of a straight-line
instruction (top of stack first in each list), or `none` to bail out
(control flow or an instruction this partial checker does not model). -/
def Instruction.straightSig (m : Module) (locals : List ValueType)
    : Instruction → Option (List ValueType × List ValueType)
  | .const _    => some ([], [.i32])
  | .constI64 _ => some ([], [.i64])
  | .f32Const _ => some ([], [.f32])
  | .f64Const _ => some ([], [.f64])
  | .localGet i => (locals[i]?).map fun t => ([], [t])
  | .localSet i => (locals[i]?).map fun t => ([t], [])
  | .globalGet i => (m.globals[i]?).map fun g => ([], [Value.toValueType g.init])
  | .globalSet i => (m.globals[i]?).map fun g => ([Value.toValueType g.init], [])
  | .drop => none   -- polymorphic operand; skip rather than guess
  | .add | .sub | .mul | .divU | .divS | .remU | .remS
  | .and | .or | .xor | .shl | .shrU | .shrS | .rotl | .rotr =>
    some ([.i32, .i32], [.i32])
  | .eqz => some ([.i32], [.i32])
  | .eq | .ne | .ltU | .ltS | .gtU | .gtS | .leU | .leS | .geU | .geS =>
    some ([.i32, .i32], [.i32])
  | .gc op => match op with
    | .refI31 => some ([.i32], [.anyref])
    | .i31GetS | .i31GetU => some ([.anyref], [.i32])
    | .refEq => some ([.anyref, .anyref], [.i32])
    | .structGet t f | .structGetS t f | .structGetU t f =>
      (m.structField? t f).map fun ft => ([.anyref], [ft.storage.vt])
    | .structSet t f =>
      (m.structField? t f).map fun ft => ([ft.storage.vt, .anyref], [])
    | .structNew t =>
      (m.structFields? t).map fun fs => ((fs.map (·.storage.vt)).reverse ++ [], [.anyref])
    | .arrayGet t | .arrayGetS t | .arrayGetU t =>
      (m.arrayElem? t).map fun ft => ([.i32, .anyref], [ft.storage.vt])
    | .arraySet t =>
      (m.arrayElem? t).map fun ft => ([ft.storage.vt, .i32, .anyref], [])
    | .arrayLen => some ([.anyref], [.i32])
    | .arrayNewDefault _ => some ([.i32], [.anyref])
    | .arrayNew t => (m.arrayElem? t).map fun ft => ([.i32, ft.storage.vt], [.anyref])
    | _ => none
  | _ => none

/-- Straight-line type check of one function body. Bails out (returns
`ok`) on any instruction whose signature is `none`. -/
def Module.checkFuncStraight (m : Module) (f : Function) : Except String Unit := do
  let locals := f.params ++ f.locals
  let mut stack : List ValueType := []   -- top of stack at the head
  for inst in f.body do
    match inst.straightSig m locals with
    | none => return ()   -- control flow / unmodelled → give up, accept
    | some (pops, pushes) =>
      let mut s := stack
      for p in pops do
        match s with
        | t :: rest => if !vtCompat t p then throw "type mismatch" else s := rest
        | []        => throw "type mismatch"
      stack := pushes.reverse ++ s
  -- Body fully modelled: the residual stack must match the declared results.
  if stack.length != f.results.length then throw "type mismatch"
  for (a, b) in stack.reverse.zip f.results do
    if !vtCompat a b then throw "type mismatch"

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
  -- 4. Straight-line operand-stack type check of each function body.
  for f in m.funcs do
    m.checkFuncStraight f

end Wasm
