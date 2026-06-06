import Project.DynDispatch.Program

/-! # Specification for the `dyn_dispatch` crate

The exported `check(sel, x)` runs two implementations of the same
dispatcher and traps via `unreachable` iff they disagree:

* `dispatch_dyn`: looks up `OPS[sel % 2]` (a static array of `&dyn Op`)
  and calls `.apply(x)` through the vtable. Compiles to
  `call_indirect (type N)` — exactly the wasm instruction this crate
  exists to exercise.
* `dispatch_naive`: an inline `match` that names the concrete `Add(1)`
  / `Mul(2)` impls directly.

Proving the wasm export terminates without trapping for every `(sel, x)`
is therefore the same as proving the indirect dispatch agrees with the
direct one — a property of `call_indirect`-through-a-vtable. -/

namespace Project.DynDispatch.Spec

open Wasm

/-- The exported `check` terminates without trapping (and returns no
values) on every `(sel, x)` input.

Informal spec:
For any `sel x : UInt32` (the wasm value carrier; both interpreted as
`i32` by the host), the wasm export `check` terminates and leaves an
empty value stack. Termination-without-trapping is the whole content
of the spec — the body traps via `unreachable` iff the dynamic
(`OPS[sel % 2].apply(x)` via the vtable) and direct (`match`) dispatchers
disagree, so this property *is* the equivalence claim between the two. -/
@[spec_of "rust-exported" "dyn_dispatch::check"]
def CheckSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (sel x : UInt32),
    TerminatesWith env «module» 5 initial [.i32 x, .i32 sel]
      (fun _ rs => rs = [])

end Project.DynDispatch.Spec
