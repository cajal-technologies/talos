import Project.DynDispatch.Program

/-! # Specifications for the `dyn_dispatch` crate

The crate exists as a small Rust source that compiles to wasm using
`call_indirect` through a `&dyn Trait` vtable — the simplest shape we
could find that exercises the indirect-call machinery in
`Interpreter.Wasm` end-to-end.

This file proves the spec of the *callee* end of that dispatch:
`func1` is the wasm function emitted from `<Add as Op>::apply` and is
called indirectly through `table[1]` whenever `dispatch(sel, x)` is
invoked with an even `sel`. Verifying the full dispatch chain
(memory-backed vtable read + table lookup + chained call) on top of
this spec is a follow-up. -/

namespace Project.DynDispatch.Spec

open Wasm

/-- `func1` is `<Add as Op>::apply`: it loads the boxed inner value at
`*self` and adds the i32 argument.

In wasm terms the function body is

    local.get 0    ;; self (a pointer into memory)
    i32.load
    local.get 1    ;; the i32 argument
    i32.add

so for any initial store whose memory contains at least 4 bytes
starting at `p`, calling this function with the stack
`[.i32 x, .i32 p]` (top = `x`; calling convention assigns
`local 0 := p`, `local 1 := x`) returns `[.i32 (mem.read32 p + x)]`
and leaves the store unchanged. -/
@[spec_of "rust-exported" "dyn_dispatch::Add::apply"]
def AddApplySpec : Prop :=
  ∀ (initial : Store) (p x : UInt32),
    p.toNat + 4 ≤ initial.mem.pages * 65536 →
    TerminatesWith «module» 1 initial [.i32 x, .i32 p]
      (fun st rs => rs = [.i32 (initial.mem.read32 p + x)] ∧ st = initial)

@[proves Project.DynDispatch.Spec.AddApplySpec]
theorem add_apply_correct : AddApplySpec := by
  intro initial p x hMem
  apply TerminatesWith.of_wp_entry_for
    (f := { params := [.i32, .i32], locals := [], body := func1, results := [.i32] }) rfl
  unfold func1
  wp_run
  -- Symbolic execution lands on three conjuncts: the load32 bounds
  -- check (discharged by `hMem`), the value equality (UInt32
  -- commutativity of addition), and the store-equality (rfl).
  simp [UInt32.add_comm]
  exact hMem

end Project.DynDispatch.Spec
