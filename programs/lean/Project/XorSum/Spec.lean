import Project.XorSum.Program

/-!
# Specification for `xor_sum`

The exported `check(seed, len)` seeds a length-`len` buffer from `seed`,
XOR-folds it both ways — left-to-right (the implementation under test)
and right-to-left (the obviously-correct oracle) — and traps via
`unreachable` iff they disagree. Proving the wasm export terminates
without trapping for every `(seed, len)` is therefore the same as
proving the forward and backward XOR-folds agree on every seeded
buffer, which is the associativity-and-commutativity content of `xor`.
-/

namespace Project.XorSum.Spec

open Wasm

/-- The exported `check` terminates without trapping (and returns no
values) on every `(seed, len)` input.

Informal spec:
For any `seed len : UInt32`, the wasm export `check` terminates and
leaves an empty value stack. Termination-without-trapping is the whole
content of the spec — the body traps via `unreachable` iff the forward
and backward XOR-folds disagree, so this property *is* the
associativity-and-commutativity claim for `xor` over the seeded
buffer. -/
@[spec_of "rust-exported" "xor_sum::check"]
def CheckSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (seed len : UInt32),
    TerminatesWith env «module» 3 initial [.i32 len, .i32 seed]
      (fun _ rs => rs = [])

end Project.XorSum.Spec
