import Interpreter.Wasm.Semantics

/-! ## Example: `(return_)call_indirect` rejects a non-subtype (issue #95)

    `call_indirect (type N)` (and its tail-call sibling
    `return_call_indirect`) must trap unless the stored function's type is a
    **subtype** of the call-site type `N`. Issue #95 reported that the
    interpreter checked only structural equality of `params`/`results`, so a
    function whose type is a strict *supertype* of the call site was run
    instead of trapping.

    The module below is the one from the issue. `$super` and `$sub` are
    distinct types with identical `(param i32) (result i32)` shapes, and
    `$sub <: $super` — crucially **not** `$super <: $sub`. The table holds
    `$impl : $super`; the call sites ask for `$sub`. Since `$super` is not a
    subtype of `$sub`, a conformant engine must trap (wasmtime: `indirect
    call type mismatch`; V8: `function signature mismatch`).

    ```wat
    (module
      (rec
        (type $super (sub (func (param i32) (result i32))))
        (type $sub   (sub $super (func (param i32) (result i32)))))
      (func $impl (type $super) (i32.add (local.get 0) (i32.const 1000)))
      (table 1 funcref)
      (elem (i32.const 0) $impl)
      (func (export "f") (result i32) (i32.const 7) (i32.const 0) (call_indirect        (type $sub)))
      (func (export "g") (result i32) (i32.const 7) (i32.const 0) (return_call_indirect (type $sub))))
    ```

    The fix (this PR) records each function's declared `(type N)` in
    `Function.typeIdx` and routes all four `(return_)call_indirect` arms
    through `Module.indirectCallTypeOk`, which — when the declared type is
    known — additionally requires `gcTypeSubtype` to hold. The theorems
    below pin down that **both** instructions now trap. The companion
    `Examples/CallIndirect.lean` covers the legitimate same-type case that
    still succeeds.

    Built by hand rather than through the `.wat` decoder: the soundness fix
    lives in the semantics, the decoder does not currently accept the
    `(func (type $super) …)` header form, and — pending structural
    type-equality in `gcTypeSubtype` — the decoder still leaves `typeIdx`
    unset (so decoded modules keep the pre-#95 structural-only behaviour). -/

namespace Wasm

namespace CallIndirectSubtype

/-- `$impl : $super` — the function the table holds. Its declared type is
type index 0 (`$super`); this is the nominal information the fixed check
consults. -/
def Impl : Program := [.localGet 0, .const 1000, .add]

/-- Exported `f`: push the argument `7` and the table index `0`, then
`call_indirect (type $sub)` — i.e. `typeIdx = 1` (the `$sub` slot),
`tableIdx = 0`. -/
def F : Program := [.const 7, .const 0, .callIndirect 1 0]

/-- Exported `g`: the tail-call sibling, `return_call_indirect (type $sub)`,
exercising the second pair of arms flagged in the issue's comment. -/
def G : Program := [.const 7, .const 0, .returnCallIndirect 1 0]

/-- The issue's module, by hand. `types`/`gcTypes` carry the two nominal
types in source order: index 0 = `$super` (open for subtyping), index 1 =
`$sub` declaring `$super` as its immediate supertype. `$impl` records its
declared type (`typeIdx := some 0`); the call sites use type index 1. -/
def m : Module :=
  { types    := [{ params := [.i32], results := [.i32] },   -- 0: $super
                 { params := [.i32], results := [.i32] }]    -- 1: $sub
    gcTypes  := [{ comp := .func { params := [.i32], results := [.i32] }, super := none,   «final» := false },
                 { comp := .func { params := [.i32], results := [.i32] }, super := some 0, «final» := true }]
    funcs    := [{ params := [.i32], body := Impl, results := [.i32], typeIdx := some 0 },   -- 0: $impl : $super
                 { params := [],     body := F,    results := [.i32] },                       -- 1: f
                 { params := [],     body := G,    results := [.i32] }]                        -- 2: g
    tables   := [{ min := 1 }]
    elements := [{ tableIdx := some 0, offset := some 0, funcs := [some 0] }] }

/-- `$sub <: $super` holds (the legitimate direction). -/
theorem sub_subtype_super : m.gcTypeSubtype 1 0 = true := by native_decide

/-- `$super <: $sub` does **not** hold. This is the relation the call sites
require of the stored function's type (`$super`) against the call-site type
(`$sub`); it fails, so the calls must trap. -/
theorem super_not_subtype_sub : m.gcTypeSubtype 0 1 = false := by native_decide

private def trapMsg (r : Result Unit) : Option String :=
  match r with | .Trap _ msg => some msg | _ => none

/-- `call_indirect (type $sub)` against `$impl : $super` traps: `$super` is
not a subtype of `$sub` (`super_not_subtype_sub`). Before #95 this returned
`7 + 1000 = 1007`. -/
theorem call_indirect_traps :
    trapMsg (run 20 m 1 (m.initialStore (α := Unit)) []) =
      some "indirect call type mismatch" := by native_decide

/-- `return_call_indirect (type $sub)` traps for the same reason — the
issue's comment noted the bug was duplicated in the tail-call arms. -/
theorem return_call_indirect_traps :
    trapMsg (run 20 m 2 (m.initialStore (α := Unit)) []) =
      some "indirect call type mismatch" := by native_decide

end CallIndirectSubtype
end Wasm
