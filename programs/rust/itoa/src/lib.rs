mod exports;

/// Write the decimal ASCII representation of `n` into `buf`, most-significant
/// digit first, and return the number of bytes written.
///
/// `0` is written as a single `b'0'`. A `u64` is at most 20 decimal digits, so
/// a 20-byte buffer always suffices. No allocation and no temporary buffer: the
/// digit count is computed first, then the digits are filled in from the least
/// significant end.
///
/// # Safety
/// `buf` must be valid for writes of `itoa(n, _)` (≤ 20) bytes.
pub unsafe fn itoa(n: u64, buf: *mut u8) -> usize {
    // Number of decimal digits of `n` (at least 1, for `n == 0`).
    let mut len: usize = 1;
    let mut m = n;
    while m >= 10 {
        m /= 10;
        len += 1;
    }
    // Fill digits from the least-significant (end) to most-significant (start).
    let mut m = n;
    let mut i = len;
    while i > 0 {
        i -= 1;
        unsafe {
            *buf.add(i) = b'0' + (m % 10) as u8;
        }
        m /= 10;
    }
    len
}
