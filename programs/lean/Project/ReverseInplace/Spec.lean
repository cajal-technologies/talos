import Project.ReverseInplace.Program

/-!
# Specification for `reverse_inplace`

The exported `check(seed, len)` runs two in-place reversers on
identically-seeded buffers — one via the swap-from-both-ends pattern,
one via copy-reversed-into-scratch-then-back — and traps via
`unreachable` iff they disagree on any element. Proving the wasm
export terminates without trapping for every input is therefore the
same as proving the two reversers compute the same permutation on
every seeded buffer.
-/

namespace Project.ReverseInplace.Spec

open Wasm

/-- The exported `check` terminates without trapping (and returns no
values) on every `(seed, len)` input.

Informal spec:
For any `seed len : UInt32`, the wasm export `check` terminates and
leaves an empty value stack. Termination-without-trapping is the whole
content of the spec — the body traps via `unreachable` iff the
swap-from-both-ends and copy-reversed reversers disagree, so this
property *is* the equivalence claim between the two implementations. -/
@[spec_of "rust-exported" "reverse_inplace::check"]
def CheckSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (seed len : UInt32),
    TerminatesWith env «module» 3 initial [.i32 len, .i32 seed]
      (fun _ rs => rs = [])

end Project.ReverseInplace.Spec
