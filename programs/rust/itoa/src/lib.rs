use core::slice;
use itoa_crate as itoa;

mod exports;

/// Write the decimal representation of `n` into the caller-provided buffer
/// at `ptr`. The buffer must be at least `cap` bytes long. Returns the
/// number of bytes written, or `-1` if the buffer is too small.
///
/// `i64::MIN` needs at most 20 bytes; `u64::MAX` needs at most 20 bytes.
///
/// # Safety
///
/// `ptr` must be valid for writes of `cap` bytes.
pub unsafe fn itoa_i64(n: i64, ptr: *mut u8, cap: i32) -> i32 {
    let mut buf = itoa::Buffer::new();
    let s = buf.format(n).as_bytes();
    if (s.len() as i32) > cap {
        return -1;
    }
    unsafe {
        slice::from_raw_parts_mut(ptr, s.len()).copy_from_slice(s);
    }
    s.len() as i32
}

/// Unsigned 64-bit variant of [`itoa_i64`]. Same convention.
///
/// # Safety
///
/// `ptr` must be valid for writes of `cap` bytes.
pub unsafe fn itoa_u64(n: u64, ptr: *mut u8, cap: i32) -> i32 {
    let mut buf = itoa::Buffer::new();
    let s = buf.format(n).as_bytes();
    if (s.len() as i32) > cap {
        return -1;
    }
    unsafe {
        slice::from_raw_parts_mut(ptr, s.len()).copy_from_slice(s);
    }
    s.len() as i32
}

/// Length, in bytes, of the decimal representation of `n`. Writes
/// nothing; useful for sizing a buffer before calling [`itoa_i64`].
pub fn itoa_i64_len(n: i64) -> i32 {
    let mut buf = itoa::Buffer::new();
    buf.format(n).len() as i32
}
