//! Wasm ABI for `encode_decode`: a length-prefixed frame codec over raw
//! `(pointer, length)` regions of linear memory. A *frame* is a 4-byte
//! little-endian `u32` length followed by that many payload bytes. Every access
//! is a `store32`/`load32` (the length) or a `memory.copy` (the payload), so the
//! emitted module is allocation-free and directly liftable. On wasm32 pointers
//! and `usize` are 32-bit.

/// `encode(src_ptr, src_len, dst_ptr) -> bytes_written`. Writes the frame
/// `[len_le32][payload]` at `dst_ptr` and returns `4 + src_len`.
///
/// The caller guarantees `[src_ptr, src_ptr + src_len)` is readable,
/// `[dst_ptr, dst_ptr + 4 + src_len)` is writable and disjoint from the source,
/// and `src_len ≤ u32::MAX`.
#[unsafe(no_mangle)]
pub extern "C" fn encode(src_ptr: *const u8, src_len: usize, dst_ptr: *mut u8) -> usize {
    unsafe {
        core::ptr::write_unaligned(dst_ptr as *mut u32, src_len as u32);
        core::ptr::copy_nonoverlapping(src_ptr, dst_ptr.add(4), src_len);
    }
    4 + src_len
}

/// `decode(src_ptr, src_len, dst_ptr, dst_cap) -> payload_len | negative status`.
/// Reads the length prefix and copies that many payload bytes into `dst`.
/// Returns the payload length, or `-1` (no room for the prefix), `-2` (payload
/// truncated), `-3` (`dst` too small).
#[unsafe(no_mangle)]
pub extern "C" fn decode(
    src_ptr: *const u8,
    src_len: usize,
    dst_ptr: *mut u8,
    dst_cap: usize,
) -> i64 {
    if src_len < 4 {
        return -1;
    }
    let n = unsafe { core::ptr::read_unaligned(src_ptr as *const u32) } as usize;
    if n > src_len - 4 {
        return -2;
    }
    if n > dst_cap {
        return -3;
    }
    unsafe { core::ptr::copy_nonoverlapping(src_ptr.add(4), dst_ptr, n) };
    n as i64
}
