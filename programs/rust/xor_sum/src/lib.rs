/// XOR-fold a slice of `u32`s laid out contiguously in linear memory.
///
/// The host writes `len` little-endian `u32` words starting at `ptr`,
/// then calls `xor_sum(ptr, len)`. Returns 0 when `len == 0`.
#[unsafe(no_mangle)]
pub extern "C" fn xor_sum(ptr: *const u32, len: usize) -> u32 {
    let mut acc: u32 = 0;
    let mut i: usize = 0;
    while i < len {
        acc ^= unsafe { *ptr.add(i) };
        i += 1;
    }
    acc
}
