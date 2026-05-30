/// Wasm-exported XOR-fold over a contiguous run of `u32` values in
/// linear memory. The host writes `len` little-endian `u32` words
/// starting at `ptr`, then calls `xor_sum(ptr, len)`. Returns `0` when
/// `len == 0`.
///
/// Thin `extern "C"` wrapper around [`crate::xor_sum`].
///
/// # Safety
///
/// `ptr` must be valid for reads of `len` `u32` words and properly
/// aligned.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xor_sum(ptr: *const u32, len: usize) -> u32 {
    let xs = unsafe { core::slice::from_raw_parts(ptr, len) };
    crate::xor_sum(xs)
}
