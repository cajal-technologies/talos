import Project.Itoa.Program

/-!
# Specifications for `itoa_i64`, `itoa_u64`, `itoa_i64_len`

The proofs are deferred; the function bodies live in `Program.lean`.
The `def`s below carry the spec statements and link to their Rust
exports via `@[spec_of …]`; once a discharging theorem lands, tag it
with `@[proves Project.Itoa.Spec.…]`.
-/

namespace Project.Itoa.Spec

open Wasm

/-- The exported `itoa_i64` writes the decimal representation of `n`
into the buffer at `ptr` and returns its length, or `-1` if `cap` is
too small to hold the representation.

Informal spec:
For any `n : Int64`, base pointer `ptr : UInt32`, and capacity
`cap : UInt32`, the wasm export `itoa_i64` returns the number of bytes
written if the decimal representation of `n` fits in `cap` bytes,
otherwise `-1`. On success the buffer `[ptr, ptr+returned)` holds the
ASCII-decimal bytes of `n`; on failure memory is unchanged. -/
@[spec_of "rust-exported" "itoa::itoa_i64"]
def ItoaI64Spec : Prop := True

/-- The exported `itoa_u64` is the unsigned-`u64` counterpart of
[`ItoaI64Spec`], same convention.

Informal spec:
Same as `ItoaI64Spec`, but `n : UInt64`. -/
@[spec_of "rust-exported" "itoa::itoa_u64"]
def ItoaU64Spec : Prop := True

/-- The exported `itoa_i64_len` returns the number of bytes the decimal
representation of `n` would occupy, without writing anything.

Informal spec:
For any `n : Int64`, `itoa_i64_len(n)` returns the length, in bytes, of
the ASCII-decimal representation of `n`. Memory is not touched. -/
@[spec_of "rust-exported" "itoa::itoa_i64_len"]
def ItoaI64LenSpec : Prop := True

end Project.Itoa.Spec
