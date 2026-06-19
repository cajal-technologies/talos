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

// ─── u64::add (inlines to a single i64.add) ────────────────────────────────
// Shim: identical source/codegen to `rust_u64::add`, so its opt-0 body is the
// frame-less `[localGet 0, localGet 1, addI64, ret]` == CodeLib `addFunc`.
#[unsafe(no_mangle)]
pub extern "C" fn add(a: u64, b: u64) -> u64 {
    a + b
}

/// Test for `u64::add`: a non-trivial chain `(a + b) + c` (two `add` calls).
#[unsafe(no_mangle)]
pub extern "C" fn add_sum3(a: u64, b: u64, c: u64) -> u64 {
    add(add(a, b), c)
}

// ─── u64::sub (inlines to a single i64.sub) ────────────────────────────────
// Shim: identical source/codegen to `rust_u64::sub`, so its opt-0 body is the
// frame-less `[localGet 0, localGet 1, subI64, ret]` == CodeLib `subFunc`.
#[unsafe(no_mangle)]
pub extern "C" fn sub(a: u64, b: u64) -> u64 {
    a - b
}

/// Test for `u64::sub`: a non-trivial chain `(a - b) - c` (two `sub` calls).
#[unsafe(no_mangle)]
pub extern "C" fn sub_chain3(a: u64, b: u64, c: u64) -> u64 {
    sub(sub(a, b), c)
}

// ─── u64::mul (inlines to a single i64.mul) ────────────────────────────────
// Shim: identical source/codegen to `rust_u64::mul`, so its opt-0 body is the
// frame-less `[localGet 0, localGet 1, mulI64, ret]` == CodeLib `mulFunc`.
#[unsafe(no_mangle)]
pub extern "C" fn mul(a: u64, b: u64) -> u64 {
    a * b
}

/// Test for `u64::mul`: a non-trivial chain `(a * b) * c` (two `mul` calls).
#[unsafe(no_mangle)]
pub extern "C" fn mul_prod3(a: u64, b: u64, c: u64) -> u64 {
    mul(mul(a, b), c)
}
