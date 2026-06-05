mod exports;

/// Naive primality test: trial-divide by every `d` in `[2, n)`.
///
/// Returns `false` for `n < 2`. Used as the reference oracle that the
/// faster variant is checked against.
#[inline(never)]
pub fn is_prime_naive(n: u32) -> bool {
    if n < 2 {
        return false;
    }
    let mut d: u32 = 2;
    while d < n {
        if n % d == 0 {
            return false;
        }
        d += 1;
    }
    true
}

/// Faster primality test: trial-divide only by `d` in `[2, n / 2]`.
///
/// Skips the upper half of candidates relative to [`is_prime_naive`] —
/// no `d > n / 2` (with `d < n`) can divide `n`, because the cofactor
/// `n / d` would be `< 2`. This is a 2× speedup over the naive loop
/// with a much shorter correctness proof than the classic √n bound.
#[inline(never)]
pub fn is_prime_fast(n: u32) -> bool {
    if n < 2 {
        return false;
    }
    let mut d: u32 = 2;
    while d <= n / 2 {
        if n % d == 0 {
            return false;
        }
        d += 1;
    }
    true
}

/// Run both implementations on `n` and trap if they disagree.
///
/// The wasm export traps (via `unreachable`) iff
/// `is_prime_naive(n) != is_prime_fast(n)`. Proving the wasm export
/// "terminates without trapping for every input" is therefore the same
/// as proving the two algorithms agree on every `u32`.
pub fn check(n: u32) {
    if is_prime_naive(n) != is_prime_fast(n) {
        #[cfg(target_arch = "wasm32")]
        core::arch::wasm32::unreachable();
        #[cfg(not(target_arch = "wasm32"))]
        unreachable!();
    }
}
