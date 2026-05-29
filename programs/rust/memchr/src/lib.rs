mod exports;

/// Find the index of the first byte equal to `needle` in the buffer
/// `[ptr, ptr + len)`.
///
/// Returns the (0-based) index of the first match, or `len` if no byte
/// in the buffer equals `needle`. Using `len` as the "not found" sentinel
/// keeps the return type a plain `usize` (no `Option` / tagged union).
///
/// # Safety
///
/// `ptr` must be valid for reads of `len` bytes.
pub unsafe fn memchr(ptr: *const u8, len: usize, needle: u8) -> usize {
    let mut i: usize = 0;
    while i < len {
        if unsafe { *ptr.add(i) } == needle {
            return i;
        }
        i += 1;
    }
    len
}
