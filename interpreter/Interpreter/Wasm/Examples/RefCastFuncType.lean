import Interpreter.Wasm.Examples.Harness

/-! ## Example: `ref.test`/`ref.cast` against concrete (function) types

    Issue #96: `ref.test`/`ref.cast` against a *concrete* function type
    always failed — a non-null funcref only matched the abstract `func`
    heap type — so "downcast a funcref, then `call_ref` it" trapped where
    wasmtime/V8 succeed. The issue's follow-up comments add the struct
    counterpart: two *separately declared but structurally identical*
    types must be one type (the spec compares defined types up to
    iso-recursive equivalence), yet `gcTypeSubtype` only walked the
    declared `sub $super` chain by literal index, so `ref.test (ref $b)`
    of a `struct.new $a` twin returned `0`.

    The fix (this PR):

    * `Module.gcTypeEquiv` — iso-recursive equivalence of type indices,
      comparing whole recursion groups (composite types, finality, and
      `sub` edges, with in-group supers compared by relative position);
    * `Module.gcTypeSubtype` now tests each type on the `sub $super`
      chain for *equivalence* with the target instead of index equality;
    * the funcref arm of `gcRefMatches` handles `.concrete t` by checking
      the function's declared type (`funcTypeIdx?`) against `t` with
      `gcTypeSubtype` (falling back to the structural signature when the
      declared type is unrecorded), and a null funcref matches every
      *nullable* concrete function type;
    * the WAT decoder records each function's declared `(type N)` in
      `Function.typeIdx` and tags multi-member `(rec …)` groups so the
      equivalence can see recursion-group boundaries.

    The theorems below pin all of it down with `native_decide`, both on
    hand-built modules and end-to-end through the decoder on the issue's
    exact WAT. -/

namespace Wasm

open Wasm.Examples

namespace RefCastFuncType

/-! ### Hand-built module: concrete function types

    Type table: index 0 = `$ft` (open for subtyping), index 1 = a
    structurally identical twin of `$ft`, index 2 = `$sub` declaring
    `$ft` as its supertype. Function 0 (`impl : $ft`) is `x ↦ x + 1`;
    function 1 (`subImpl : $sub`) likewise. -/

def Impl : Program := [.localGet 0, .const 1, .add]

/-- `ref.test (ref $ft) (ref.func $impl)` — the issue's first module. -/
def TestSame : Program := [.refFunc 0, .gc (.refTest false (.concrete 0))]

/-- `ref.test` against the structurally identical *twin* declaration. -/
def TestTwin : Program := [.refFunc 0, .gc (.refTest false (.concrete 1))]

/-- `ref.test (ref $ft)` of a funcref whose type is `$sub <: $ft`. -/
def TestSub : Program := [.refFunc 1, .gc (.refTest false (.concrete 0))]

/-- `ref.test (ref $sub)` of a funcref of the *supertype* `$ft` — the one
direction that must still fail. -/
def TestSuper : Program := [.refFunc 0, .gc (.refTest false (.concrete 2))]

/-- The issue's second module: `(call_ref $ft (i32.const 5)
(ref.cast (ref $ft) (ref.func $impl)))`. -/
def CastCall : Program :=
  [.const 5, .refFunc 0, .gc (.refCast false (.concrete 0)), .callRef 0]

/-- `ref.cast (ref $sub)` of a funcref of the supertype `$ft` — traps. -/
def CastSuper : Program := [.refFunc 0, .gc (.refCast false (.concrete 2))]

/-- Null funcref against a nullable / non-nullable concrete func type. -/
def TestNullOk  : Program := [.refNull, .gc (.refTest true  (.concrete 0))]
def TestNullNot : Program := [.refNull, .gc (.refTest false (.concrete 0))]

def m : Module :=
  { types   := [{ params := [.i32], results := [.i32] },
                { params := [.i32], results := [.i32] },
                { params := [.i32], results := [.i32] }]
    gcTypes := [{ comp := .func { params := [.i32], results := [.i32] }, «final» := false },  -- 0: $ft
                { comp := .func { params := [.i32], results := [.i32] }, «final» := false },  -- 1: twin of $ft
                { comp := .func { params := [.i32], results := [.i32] }, super := some 0 }]   -- 2: $sub <: $ft
    funcs   := [{ params := [.i32], body := Impl, results := [.i32], typeIdx := some 0 },  -- 0: impl : $ft
                { params := [.i32], body := Impl, results := [.i32], typeIdx := some 2 },  -- 1: subImpl : $sub
                { body := TestSame,    results := [.i32] },   -- 2
                { body := TestTwin,    results := [.i32] },   -- 3
                { body := TestSub,     results := [.i32] },   -- 4
                { body := TestSuper,   results := [.i32] },   -- 5
                { body := CastCall,    results := [.i32] },   -- 6
                { body := CastSuper,   results := [.funcref] },  -- 7
                { body := TestNullOk,  results := [.i32] },   -- 8
                { body := TestNullNot, results := [.i32] }] } -- 9

/-- The twin declarations of `$ft` are one defined type. -/
theorem twin_equiv : m.gcTypeEquiv 0 1 = true := by native_decide

/-- Equivalence sees through the `sub` chain too: `$sub <: twin-of-$ft`. -/
theorem sub_subtype_twin : m.gcTypeSubtype 2 1 = true := by native_decide

/-- …but a supertype is still not a subtype of its subtype. -/
theorem super_not_subtype_sub : m.gcTypeSubtype 0 2 = false := by native_decide

/-- `ref.test (ref $ft) (ref.func $impl)` is `1` (the issue's first
module; previously `0`). -/
theorem test_same :
    runValues 20 m 2 (m.initialStore (α := Unit)) [] = [.i32 1] := by native_decide

/-- The structurally identical twin target also tests `1`. -/
theorem test_twin :
    runValues 20 m 3 (m.initialStore (α := Unit)) [] = [.i32 1] := by native_decide

/-- A funcref of type `$sub` tests `1` against the supertype `$ft`. -/
theorem test_sub :
    runValues 20 m 4 (m.initialStore (α := Unit)) [] = [.i32 1] := by native_decide

/-- A funcref of type `$ft` tests `0` against the subtype `$sub`. -/
theorem test_super :
    runValues 20 m 5 (m.initialStore (α := Unit)) [] = [.i32 0] := by native_decide

/-- The issue's second module: cast-then-`call_ref` returns `5 + 1 = 6`
(previously trapped with a cast failure). -/
theorem cast_call :
    runValues 20 m 6 (m.initialStore (α := Unit)) [] = [.i32 6] := by native_decide

/-- Casting a `$ft` funcref *down* to `$sub` still traps. -/
theorem cast_super_traps :
    runTrapMsg 20 m 7 (m.initialStore (α := Unit)) [] = some "cast failure" := by
  native_decide

/-- The null funcref inhabits the nullable concrete type `(ref null $ft)`… -/
theorem test_null_nullable :
    runValues 20 m 8 (m.initialStore (α := Unit)) [] = [.i32 1] := by native_decide

/-- …but not the non-nullable `(ref $ft)`. -/
theorem test_null_nonnullable :
    runValues 20 m 9 (m.initialStore (α := Unit)) [] = [.i32 0] := by native_decide

/-! ### Hand-built module: struct twins and recursion groups -/

/-- `ref.test (ref $b) (struct.new $a (i32.const 7))` with `$a`/`$b`
separately declared but structurally identical. -/
def StructTwin : Program :=
  [.const 7, .gc (.structNew 0), .gc (.refTest false (.concrete 1))]

/-- Same test against a struct type with a *different* field type — must
stay `0`. -/
def StructOther : Program :=
  [.const 7, .gc (.structNew 0), .gc (.refTest false (.concrete 2))]

def structM : Module :=
  { gcTypes := [{ comp := .struct [{ storage := .val .i32 }] },              -- 0: $a
                { comp := .struct [{ storage := .val .i32 }] },              -- 1: $b, twin of $a
                { comp := .struct [{ storage := .val .i64 }] },              -- 2: different shape
                -- 3–4: a two-member `(rec …)` group of the same shape as 0
                { comp := .struct [{ storage := .val .i32 }], recGroup := some 3 },
                { comp := .struct [{ storage := .val .i32 }], recGroup := some 3 }]
    funcs   := [{ body := StructTwin,  results := [.i32] },   -- 0
                { body := StructOther, results := [.i32] }] } -- 1

/-- The comment's struct-twin case: a `$a` value tests `1` against `$b`. -/
theorem struct_twin :
    runValues 20 structM 0 (structM.initialStore (α := Unit)) [] = [.i32 1] := by
  native_decide

/-- A structurally *different* struct type still tests `0`. -/
theorem struct_other :
    runValues 20 structM 1 (structM.initialStore (α := Unit)) [] = [.i32 0] := by
  native_decide

/-- Iso-recursive equivalence respects recursion-group boundaries: a
member of a two-member `(rec …)` group is *not* equivalent to the same
shape declared as a singleton group. -/
theorem rec_group_not_equiv : structM.gcTypeEquiv 0 3 = false := by native_decide

/-- Distinct members of one recursion group stay distinct types even when
they share a shape, while separately declared singleton groups of the same
shape are one type. -/
theorem rec_group_members_distinct : structM.gcTypeEquiv 3 4 = false ∧
    structM.gcTypeEquiv 0 1 = true := by native_decide

/-! ### End-to-end through the decoder, on the issue's exact WAT -/

def refTestWat : String :=
  "(module
     (type $ft (func (param i32) (result i32)))
     (func $impl (type $ft) (local.get 0))
     (elem declare func $impl)
     (func (export \"f\") (result i32)
       (ref.test (ref $ft) (ref.func $impl))))"

def castCallWat : String :=
  "(module
     (type $ft (func (param i32) (result i32)))
     (func $impl (type $ft) (i32.add (local.get 0) (i32.const 1)))
     (elem declare func $impl)
     (func (export \"f\") (result i32)
       (call_ref $ft (i32.const 5) (ref.cast (ref $ft) (ref.func $impl)))))"

def structTwinWat : String :=
  "(module
     (type $a (struct (field i32)))
     (type $b (struct (field i32)))
     (func (export \"f\") (result i32)
       (ref.test (ref $b) (struct.new $a (i32.const 7)))))"

private def refTestM    : Module := decodeOrDefault refTestWat
private def castCallM   : Module := decodeOrDefault castCallWat
private def structTwinM : Module := decodeOrDefault structTwinWat

/-- The decoder records `$impl`'s declared `(type $ft)`. -/
theorem decoded_typeIdx : refTestM.funcs.map (·.typeIdx) = [some 0, none] := by
  native_decide

/-- wasmtime/V8 return `1`; Talos previously returned `0`. -/
theorem decoded_ref_test :
    runValues 20 refTestM ((refTestM.findExport "f").getD 99)
      (refTestM.initialStore (α := Unit)) [] = [.i32 1] := by native_decide

/-- wasmtime/V8 return `6`; Talos previously trapped on the cast. -/
theorem decoded_cast_call :
    runValues 20 castCallM ((castCallM.findExport "f").getD 99)
      (castCallM.initialStore (α := Unit)) [] = [.i32 6] := by native_decide

/-- The comment's struct-twin module returns `1` end-to-end. -/
theorem decoded_struct_twin :
    runValues 20 structTwinM ((structTwinM.findExport "f").getD 99)
      (structTwinM.initialStore (α := Unit)) [] = [.i32 1] := by native_decide

end RefCastFuncType
end Wasm
