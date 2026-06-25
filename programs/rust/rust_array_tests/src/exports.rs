//! Reuse tests for the `CodeLib/RustStd/Array` corpus.
//!
//! Each primitive gets two structurally-distinct users. At opt-0 `len` inlines to
//! a length read while `is_empty` lowers to a `call`, so the two shapes the chunk
//! corpus targets are both exercised: the Lean proofs reuse the CodeLib chunk
//! theorems either way — `len_seq` against the inlined read, `isEmptyBodyWp`
//! through the call. The source helpers are generic over `T`; these wrappers only
//! choose a concrete monomorphization so Rust emits wasm.

#[unsafe(no_mangle)]
pub extern "C" fn len_plus_one(xs: &[u8]) -> usize {
    crate::len_plus_one(xs)
}

#[unsafe(no_mangle)]
pub extern "C" fn len_plus_arg(xs: &[u8], n: usize) -> usize {
    crate::len_plus_arg(xs, n)
}

#[unsafe(no_mangle)]
pub extern "C" fn empty_plus_three(xs: &[u8]) -> u32 {
    crate::empty_plus_three(xs)
}

#[unsafe(no_mangle)]
pub extern "C" fn empty_xor_flag(xs: &[u8], flag: u32) -> u32 {
    crate::empty_xor_flag(xs, flag)
}
