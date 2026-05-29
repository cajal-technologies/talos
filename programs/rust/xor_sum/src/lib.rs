mod exports;

/// XOR-fold a slice of `u32`s laid out contiguously in linear memory.
///
/// Reads `len` little-endian `u32` words starting at `ptr`. Returns `0`
/// when `len == 0`.
///
/// # Safety
///
/// `ptr` must be valid for reads of `len` `u32` words and properly
/// aligned.
pub unsafe fn xor_sum(ptr: *const u32, len: usize) -> u32 {
    let mut acc: u32 = 0;
    let mut i: usize = 0;
    while i < len {
        acc ^= unsafe { *ptr.add(i) };
        i += 1;
    }
    acc
}
