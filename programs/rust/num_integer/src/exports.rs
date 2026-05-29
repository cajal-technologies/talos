/// Wasm-exported greatest common divisor of two `u64` values, delegating
/// to the binary-GCD (Stein's algorithm) implementation in the
/// `num-integer` crate. By the `num-integer` convention `gcd(0, 0) = 0`.
///
/// Thin `extern "C"` wrapper around [`crate::gcd_u64`].
#[unsafe(no_mangle)]
pub extern "C" fn gcd_u64(a: u64, b: u64) -> u64 {
    crate::gcd_u64(a, b)
}
