use itoa_crate as itoa;

mod exports;

/// Maximum buffer size used by [`check`].
///
/// `i64::MIN` prints as `"-9223372036854775808"` (20 bytes); `u64::MAX`
/// prints as `"18446744073709551615"` (20 bytes). 32 leaves comfortable
/// slack and bounds the on-stack buffers below.
const BUF_CAP: i32 = 32;

/// Integers we know how to format two different ways. The `fast` side
/// is provided generically via [`itoa::Integer`]; this trait adds the
/// hand-written naive oracle the fast side is checked against.
pub trait Itoa: Copy + itoa::Integer {
    fn naive(self, out: &mut [u8], cap: i32) -> i32;
}

/// Write the decimal representation of `n` into `out` using the `itoa`
/// crate. Returns the number of bytes written, or `-1` if `cap` bytes
/// are not enough.
fn itoa_fast<T: itoa::Integer>(n: T, out: &mut [u8], cap: i32) -> i32 {
    let mut buf = itoa::Buffer::new();
    let s = buf.format(n).as_bytes();
    if (s.len() as i32) > cap {
        return -1;
    }
    out[..s.len()].copy_from_slice(s);
    s.len() as i32
}

/// Obviously-correct unsigned formatter: count digits, then write them
/// right-to-left by repeated `% 10` / `/ 10`. Used as the reference
/// oracle that the `itoa` crate is checked against.
#[inline(never)]
fn itoa_u64_naive(n: u64, out: &mut [u8], cap: i32) -> i32 {
    let mut len: i32 = 1;
    let mut m = n / 10;
    while m > 0 {
        len += 1;
        m /= 10;
    }
    if len > cap {
        return -1;
    }
    let mut m = n;
    let mut i = len as usize;
    while i > 0 {
        i -= 1;
        out[i] = b'0' + (m % 10) as u8;
        m /= 10;
    }
    len
}

/// Obviously-correct signed formatter: emit `'-'` for negatives, then
/// reuse [`itoa_u64_naive`] on the magnitude.
///
/// The magnitude is `(n as u64).wrapping_neg()` so `i64::MIN` is handled
/// without overflow — its magnitude is exactly `2^63`, which fits in
/// `u64`.
#[inline(never)]
fn itoa_i64_naive(n: i64, out: &mut [u8], cap: i32) -> i32 {
    if n >= 0 {
        return itoa_u64_naive(n as u64, out, cap);
    }
    let abs = (n as u64).wrapping_neg();
    let mut len: i32 = 1;
    let mut m = abs / 10;
    while m > 0 {
        len += 1;
        m /= 10;
    }
    let total = len + 1;
    if total > cap {
        return -1;
    }
    out[0] = b'-';
    let mut m = abs;
    let mut i = total as usize;
    while i > 1 {
        i -= 1;
        out[i] = b'0' + (m % 10) as u8;
        m /= 10;
    }
    total
}

impl Itoa for u64 {
    fn naive(self, out: &mut [u8], cap: i32) -> i32 {
        itoa_u64_naive(self, out, cap)
    }
}

impl Itoa for i64 {
    fn naive(self, out: &mut [u8], cap: i32) -> i32 {
        itoa_i64_naive(self, out, cap)
    }
}

fn trap() -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    unreachable!();
}

/// Run both formatters on `(n, cap)` and trap if they disagree.
///
/// `cap` is clamped to `[0, BUF_CAP]` so the on-stack scratch buffers
/// cannot overflow; within that range every `(n, cap)` is exercised,
/// including the "buffer too small" branch (`cap` below the required
/// length) and the success branch.
///
/// The wasm export traps iff the `itoa` crate and the naive oracle
/// disagree on either the returned length or the written bytes.
pub fn check<T: Itoa>(n: T, cap: i32) {
    let cap = cap.clamp(0, BUF_CAP);
    let mut buf_fast = [0u8; BUF_CAP as usize];
    let mut buf_naive = [0u8; BUF_CAP as usize];
    let r = itoa_fast(n, &mut buf_fast, cap);
    let s = n.naive(&mut buf_naive, cap);
    if r != s {
        trap();
    }
    if r > 0 {
        let mut i: usize = 0;
        while i < r as usize {
            if buf_fast[i] != buf_naive[i] {
                trap();
            }
            i += 1;
        }
    }
}

pub fn check_i64(n: i64, cap: i32) {
    check::<i64>(n, cap)
}

pub fn check_u64(n: u64, cap: i32) {
    check::<u64>(n, cap)
}
