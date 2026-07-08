//! Wasm ABI surface for `encode_decode`: raw `(pointer, length)` regions of
//! linear memory and scalar returns — never a Rust `Vec`/`String`/`Result`, so
//! the emitted module stays allocation-free and liftable. Thin wrappers over
//! the pure [`crate::encode`] / [`crate::decode`]. On wasm32 pointers and
//! `usize` are 32-bit.

/// `(src_ptr, src_len, dst_ptr) -> bytes_written`. Writes a length-prefixed
/// frame; the caller guarantees `[src_ptr, src_ptr + src_len)` is readable and
/// `[dst_ptr, dst_ptr + 4 + src_len)` is writable.
#[unsafe(no_mangle)]
pub extern "C" fn encode(src_ptr: *const u8, src_len: usize, dst_ptr: *mut u8) -> usize {
    let src = unsafe { core::slice::from_raw_parts(src_ptr, src_len) };
    let dst = unsafe { core::slice::from_raw_parts_mut(dst_ptr, crate::LEN_PREFIX + src_len) };
    crate::encode(src, dst)
}

/// `(src_ptr, src_len, dst_ptr, dst_cap) -> payload_len | negative status`.
/// Reads one frame and copies its payload into `[dst_ptr, dst_ptr + dst_cap)`.
#[unsafe(no_mangle)]
pub extern "C" fn decode(
    src_ptr: *const u8,
    src_len: usize,
    dst_ptr: *mut u8,
    dst_cap: usize,
) -> i64 {
    let src = unsafe { core::slice::from_raw_parts(src_ptr, src_len) };
    let dst = unsafe { core::slice::from_raw_parts_mut(dst_ptr, dst_cap) };
    crate::decode(src, dst)
}
