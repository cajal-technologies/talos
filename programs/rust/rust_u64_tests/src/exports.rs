//! Reuse tests for the `CodeLib/RustStd/U64` corpus.
//!
//! Each operator gets TWO structurally-distinct functions that use it INLINE
//! the way real client code emits it (no `#[no_mangle]` shim manufacturing a
//! call, no calling the op as a function). Their proofs in `Spec.lean`
//! discharge the inlined instruction chunks by reusing the CodeLib chunk
//! theorems — exactly what `opt-0`'s "same inlined sequence everywhere"
//! guarantees.

// ── add ─────────────────────────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn add_chain(a: u64, b: u64, c: u64) -> u64 { a + b + c }
#[unsafe(no_mangle)] pub extern "C" fn add_then_mul(a: u64, b: u64, c: u64) -> u64 { (a + b) * c }

// ── sub ─────────────────────────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn sub_chain(a: u64, b: u64, c: u64) -> u64 { a - b - c }
#[unsafe(no_mangle)] pub extern "C" fn sub_then_add(a: u64, b: u64, c: u64) -> u64 { (a - b) + c }

// ── mul ─────────────────────────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn mul_chain(a: u64, b: u64, c: u64) -> u64 { a * b * c }
#[unsafe(no_mangle)] pub extern "C" fn mul_then_add(a: u64, b: u64, c: u64) -> u64 { a * b + c }

// ── bitand ──────────────────────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn and_chain(a: u64, b: u64, c: u64) -> u64 { a & b & c }
#[unsafe(no_mangle)] pub extern "C" fn and_then_or(a: u64, b: u64, c: u64) -> u64 { (a & b) | c }

// ── bitor ───────────────────────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn or_chain(a: u64, b: u64, c: u64) -> u64 { a | b | c }
#[unsafe(no_mangle)] pub extern "C" fn or_then_xor(a: u64, b: u64, c: u64) -> u64 { (a | b) ^ c }

// ── bitxor ──────────────────────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn xor_chain(a: u64, b: u64, c: u64) -> u64 { a ^ b ^ c }
#[unsafe(no_mangle)] pub extern "C" fn xor_then_and(a: u64, b: u64, c: u64) -> u64 { (a ^ b) & c }

// ── not ─────────────────────────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn not_twice(a: u64) -> u64 { !!a }
#[unsafe(no_mangle)] pub extern "C" fn not_then_xor(a: u64, b: u64) -> u64 { (!a) ^ b }

// ── shl ─────────────────────────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn shl_then_add(a: u64, n: u32, b: u64) -> u64 { (a << n) + b }
#[unsafe(no_mangle)] pub extern "C" fn shl_twice(a: u64, n: u32, m: u32) -> u64 { (a << n) << m }

// ── shr ─────────────────────────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn shr_then_sub(a: u64, n: u32, b: u64) -> u64 { (a >> n) - b }
#[unsafe(no_mangle)] pub extern "C" fn shr_twice(a: u64, n: u32, m: u32) -> u64 { (a >> n) >> m }

// ── div (divisors nonzero) ──────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn div_then_add(a: u64, b: u64, c: u64) -> u64 { a / b + c }
#[unsafe(no_mangle)] pub extern "C" fn div_then_mul(a: u64, b: u64, c: u64) -> u64 { (a / b) * c }

// ── rem (divisors nonzero) ──────────────────────────────────────────────────
#[unsafe(no_mangle)] pub extern "C" fn rem_then_add(a: u64, b: u64, c: u64) -> u64 { a % b + c }
#[unsafe(no_mangle)] pub extern "C" fn rem_then_mul(a: u64, b: u64, c: u64) -> u64 { (a % b) * c }
