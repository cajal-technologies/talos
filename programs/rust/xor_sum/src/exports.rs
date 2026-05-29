/// Wasm-exported XOR-fold over a contiguous run of `u32` values in
/// linear memory. The host writes `len` little-endian `u32` words
/// starting at `ptr`, then calls `xor_sum(ptr, len)`. Returns `0` when
/// `len == 0`.
///
/// Thin `extern "C"` wrapper around [`crate::xor_sum`].
#[unsafe(no_mangle)]
pub extern "C" fn xor_sum(ptr: *const u32, len: usize) -> u32 {
    unsafe { crate::xor_sum(ptr, len) }
}
