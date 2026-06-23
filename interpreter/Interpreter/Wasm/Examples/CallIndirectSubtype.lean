import Interpreter.Wasm.Semantics

/-! ## Example: `call_indirect` accepts a *supertype* (issue #95)

    This file *reproduces* a known unsoundness; it does not fix it. See
    https://github.com/cajal-technologies/talos/issues/95.

    `call_indirect (type N)` is supposed to trap unless the stored
    function's type is a **subtype** of the call-site type `N`. The
    interpreter instead checks structural equality of `params`/`results`
    (`Semantics.lean`, the `.callIndirect` arm):

    ```
    if fn.params = ty.params ∧ fn.results = ty.results then … else .Trap …
    ```

    Two *distinct* nominal types in a `rec`/`sub` hierarchy can share the
    same params/results while **not** standing in the required subtype
    relation — and then the equality check wrongly passes.

    The module below is the one from the issue:

    ```wat
    (module
      (rec
        (type $super (sub (func (param i32) (result i32))))
        (type $sub   (sub $super (func (param i32) (result i32)))))
      (func $impl (type $super) (i32.add (local.get 0) (i32.const 1000)))
      (table 1 funcref)
      (elem (i32.const 0) $impl)
      (func (export "f") (result i32)
        (i32.const 7) (i32.const 0) (call_indirect (type $sub))))
    ```

    `$super` and `$sub` are distinct types with identical
    `(param i32) (result i32)` shapes, and `$sub <: $super` — crucially
    **not** `$super <: $sub`. The table holds `$impl : $super`; the call
    site asks for `$sub`. Since `$super` is not a subtype of `$sub`, a
    conformant engine must trap:

    * wasmtime 43 → `indirect call type mismatch`
    * V8 (Node 26) → `function signature mismatch`

    Talos runs `$impl` anyway and returns `1007` (= `7 + 1000`). The
    `native_decide` theorem below pins down that wrong result, so it will
    start failing the day the relation is tightened from `=` to `<:` — at
    which point this example should flip to asserting a trap.

    Built by hand rather than through the `.wat` decoder: the unsoundness
    lives in the semantics, and the decoder does not currently accept the
    `(func (type $super) …)` header form used in the issue. -/

namespace Wasm

namespace CallIndirectSubtype

/-- `$impl : $super` — the function the table holds. -/
def Impl : Program := [.localGet 0, .const 1000, .add]

/-- The exported `f`: push the argument `7` and the table index `0`, then
`call_indirect (type $sub)` — i.e. `typeIdx = 1` (the `$sub` slot),
`tableIdx = 0`. -/
def F : Program := [.const 7, .const 0, .callIndirect 1 0]

/-- The issue's module, by hand. `types`/`gcTypes` carry the two nominal
types in source order: index 0 = `$super` (open for subtyping), index 1 =
`$sub` declaring `$super` as its immediate supertype. The two `FuncType`s
are structurally identical, which is exactly what fools the equality
check. -/
def m : Module :=
  { types    := [{ params := [.i32], results := [.i32] },   -- 0: $super
                 { params := [.i32], results := [.i32] }]    -- 1: $sub
    gcTypes  := [{ comp := .func { params := [.i32], results := [.i32] }, super := none,   «final» := false },
                 { comp := .func { params := [.i32], results := [.i32] }, super := some 0, «final» := true }]
    funcs    := [{ params := [.i32], body := Impl, results := [.i32] },   -- 0: $impl
                 { params := [],     body := F,    results := [.i32] }]    -- 1: f
    tables   := [{ min := 1 }]
    elements := [{ tableIdx := some 0, offset := some 0, funcs := [some 0] }] }

/-- `$sub <: $super` holds (the legitimate direction). -/
theorem sub_subtype_super : m.gcTypeSubtype 1 0 = true := by native_decide

/-- `$super <: $sub` does **not** hold. This is the relation `call_indirect`
*should* require of the stored function's type (`$super`) against the
call-site type (`$sub`) — and it fails, so the call must trap. -/
theorem super_not_subtype_sub : m.gcTypeSubtype 0 1 = false := by native_decide

private def runResult : Result Unit :=
  run 20 m 1 (m.initialStore (α := Unit)) []

/-- **The bug.** Because `super_not_subtype_sub`, calling `$impl : $super`
through `call_indirect (type $sub)` must trap. Instead the interpreter runs
`$impl` and returns `7 + 1000 = 1007`. When the type check is tightened from
`=` to `<:`, this theorem should be replaced by one asserting a trap, e.g.
`∃ st, runResult = .Trap st "indirect call type mismatch"`. -/
theorem reproduces_unsound_call :
    (match runResult with | .Success vs _ => vs | _ => []) = [.i32 1007] := by
  native_decide

end CallIndirectSubtype
end Wasm
