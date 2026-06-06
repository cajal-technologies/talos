mod exports;

/// Maximum length the equivalence check exercises. Bounds the on-stack
/// scratch buffers.
const BUF_CAP: u32 = 32;

/// Reverse, in place, the `u32` slice via the swap-from-both-ends
/// pattern. This is the implementation under test.
#[inline(never)]
fn reverse_fast(xs: &mut [u32]) {
    let n = xs.len();
    if n == 0 {
        return;
    }
    let mut lo: usize = 0;
    let mut hi: usize = n - 1;
    while lo < hi {
        let a = xs[lo];
        let b = xs[hi];
        xs[lo] = b;
        xs[hi] = a;
        lo += 1;
        hi -= 1;
    }
}

/// Obviously-correct reversal: copy the slice reversed into a scratch
/// buffer, then copy back. Used as the reference oracle that
/// [`reverse_fast`] is checked against.
#[inline(never)]
fn reverse_naive(xs: &mut [u32]) {
    let n = xs.len();
    let mut tmp = [0u32; BUF_CAP as usize];
    let mut i: usize = 0;
    while i < n {
        tmp[i] = xs[n - 1 - i];
        i += 1;
    }
    let mut i: usize = 0;
    while i < n {
        xs[i] = tmp[i];
        i += 1;
    }
}

fn trap() -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    unreachable!();
}

/// Seed two identical length-`len` buffers from `seed`, reverse one
/// via [`reverse_fast`] and the other via [`reverse_naive`], and trap
/// if they disagree on any element.
///
/// `len` is clamped to `[0, BUF_CAP]` so the on-stack scratch buffers
/// cannot overflow.
pub fn check(seed: u32, len: u32) {
    let len = if len > BUF_CAP { BUF_CAP } else { len } as usize;
    let mut a = [0u32; BUF_CAP as usize];
    let mut b = [0u32; BUF_CAP as usize];
    let mut i: usize = 0;
    while i < len {
        let v = seed
            .wrapping_mul((i as u32).wrapping_add(1))
            .wrapping_add(i as u32);
        a[i] = v;
        b[i] = v;
        i += 1;
    }
    reverse_fast(&mut a[..len]);
    reverse_naive(&mut b[..len]);
    let mut i: usize = 0;
    while i < len {
        if a[i] != b[i] {
            trap();
        }
        i += 1;
    }
}
