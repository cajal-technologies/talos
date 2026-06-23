//! Reuse tests for the `CodeLib/RustStd/Array` corpus.
//!
//! Each primitive gets two structurally-distinct inline users. These exports do
//! not call the primitive crate wrappers; their Lean proofs should reuse the
//! CodeLib chunk theorems against the emitted inline instruction sequences.
//! The source helpers are generic over `T`; these wrappers only choose a
//! concrete monomorphization so Rust emits wasm.

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
