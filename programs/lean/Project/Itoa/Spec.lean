import Project.Itoa.Program

/-!
# Specifications for `itoa::check_i64` and `itoa::check_u64`

Each exported `check_*(n, cap)` runs two decimal formatters on `n` — the
`itoa` crate (fast) and a hand-written digit-by-digit oracle (naive) —
into separate on-stack buffers and traps via `unreachable` iff they
disagree on either the returned length or the written bytes. Proving
the wasm export terminates without trapping for every input is therefore
the same as proving the two formatters agree on every `(n, cap)` pair
within the buffer capacity.
-/

namespace Project.Itoa.Spec

open Wasm

/-- The exported `check_i64` terminates without trapping (and returns no
values) on every `(n, cap)` input.

Informal spec:
For any signed 64-bit input `n : UInt64` (the wasm value carrier; the
host interprets it as `i64`) and any capacity `cap : UInt32`, the wasm
export `check_i64` terminates and leaves an empty value stack.
Termination-without-trapping is the whole content of the spec — the
body traps via `unreachable` iff the `itoa`-crate formatter and the
hand-written naive oracle disagree, so this property *is* the
equivalence claim between the two implementations. -/
@[spec_of "rust-exported" "itoa::check_i64"]
def CheckI64Spec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n : UInt64) (cap : UInt32),
    TerminatesWith env «module» 7 initial [.i64 n, .i32 cap]
      (fun _ rs => rs = [])

/-- The exported `check_u64` terminates without trapping (and returns no
values) on every `(n, cap)` input.

Informal spec:
Same shape as [`CheckI64Spec`], but for the unsigned formatter export.
`n : UInt64` is the wasm value carrier (interpreted as `u64` by the
host) and `cap : UInt32` is the buffer capacity. Termination-without-
trapping is equivalent to the `itoa`-crate and naive formatters
agreeing on every `(n, cap)` input. -/
@[spec_of "rust-exported" "itoa::check_u64"]
def CheckU64Spec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n : UInt64) (cap : UInt32),
    TerminatesWith env «module» 8 initial [.i64 n, .i32 cap]
      (fun _ rs => rs = [])

end Project.Itoa.Spec
