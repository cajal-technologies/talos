use num_integer_dep::Integer;

/// Greatest common divisor of two unsigned 64-bit integers, as implemented
/// by `num-integer`'s `Integer::gcd`. By convention `gcd(0, 0) = 0`.
#[unsafe(no_mangle)]
pub extern "C" fn gcd_u64(a: u64, b: u64) -> u64 {
    Integer::gcd(&a, &b)
}
