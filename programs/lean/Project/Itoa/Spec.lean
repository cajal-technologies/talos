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
export `check_i64` terminates and leaves an empty value stack. The
`TerminatesWith` argument list is in wasm operand-stack order (head =
top), so the second ABI argument, `cap`, appears before `n`.
Termination-without-trapping is the whole content of the spec — the
body traps via `unreachable` iff the `itoa`-crate formatter and the
hand-written naive oracle disagree, so this property *is* the
equivalence claim between the two implementations.

The hypothesis `initial = «module».initialStore` pins the run to the
canonical instantiated store: the `itoa`-crate formatter reads its
decimal `DIGIT_TABLE` from the module's read-only data segment and
relies on the stack-pointer global, so the property is only meaningful
relative to a store in which the module's data and globals are
installed (it is *false* for an arbitrary store, where the table is
absent). This matches the equivalence-check corpus convention for
memory/global-touching specs (cf. `xor_sum`).

Unoptimized (`opt-level=0`) pipeline: the export `check_i64` is
`func31`, a shadow-stack wrapper that spills its arguments to a frame
in linear memory and forwards to `func28`, which in turn wraps the
actual harness `func21`. -/
@[spec_of "rust-exported" "itoa::check_i64"]
def CheckI64Spec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n : UInt64) (cap : UInt32),
    initial = «module».initialStore →
    TerminatesWith env «module» 31 initial [.i32 cap, .i64 n]
      (fun _ rs => rs = [])

/-- The exported `check_u64` terminates without trapping (and returns no
values) on every `(n, cap)` input.

Informal spec:
Same shape as [`CheckI64Spec`], but for the unsigned formatter export.
`n : UInt64` is the wasm value carrier (interpreted as `u64` by the
host) and `cap : UInt32` is the buffer capacity. As above, the
`TerminatesWith` arguments are written in operand-stack order.
Termination-without-trapping is equivalent to the `itoa`-crate and
naive formatters agreeing on every `(n, cap)` input. As with
`CheckI64Spec`, the hypothesis `initial = «module».initialStore` makes
the formatter's `DIGIT_TABLE` and stack-pointer global present.

Unoptimized (`opt-level=0`) pipeline: the export `check_u64` is
`func32`, a shadow-stack wrapper forwarding to `func29`, which wraps
the actual harness `func23`. -/
@[spec_of "rust-exported" "itoa::check_u64"]
def CheckU64Spec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n : UInt64) (cap : UInt32),
    initial = «module».initialStore →
    TerminatesWith env «module» 32 initial [.i32 cap, .i64 n]
      (fun _ rs => rs = [])

end Project.Itoa.Spec
