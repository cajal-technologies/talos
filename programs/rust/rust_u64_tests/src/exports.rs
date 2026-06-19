//! Reuse tests for the `CodeLib/RustStd/U64` corpus.
//!
//! One crate accumulating *non-trivial* uses of the u64 std functions proven
//! in CodeLib, so each new CodeLib theorem gets exercised through the `call`
//! rule in a single emitted module (`Project.RustU64Tests.Spec`) instead of a
//! crate per function. Mirrors how `rust_u64` accumulates the corpus itself.
//!
//! Convention per std function:
//!   * if the std fn compiles to a real *called* function (e.g. `abs_diff`),
//!     call it directly — the `.call` reuses its CodeLib theorem;
//!   * if the std fn *inlines* at opt-0 (e.g. `+` → `i64.add`), expose a local
//!     `#[no_mangle] extern "C"` shim with the same body (so its emitted
//!     `Function` record equals the CodeLib `…Func`), then call the shim.

// ─── u64::div (inlines the guarded i64.div_u at opt-0) ─────────────────────
// Shim: identical source/codegen to `rust_u64::div`. Division-by-zero is always
// checked (even in release), so the opt-0 body is a `block` guarding the
// `i64.div_u`, followed by a crate-specific panic tail. The guard/divide prefix
// is identical to CodeLib `divFunc`; only the trailing panic `const`/`call`
// indices are resolved per crate (`div_wp` is reused tail-generically).
#[unsafe(no_mangle)]
pub extern "C" fn div(a: u64, b: u64) -> u64 {
    a / b
}

/// Test for `u64::div`: a non-trivial chain `(a / b) / c` (two `div` calls;
/// requires `b != 0` and `c != 0`).
#[unsafe(no_mangle)]
pub extern "C" fn div_chain(a: u64, b: u64, c: u64) -> u64 {
    div(div(a, b), c)
}
