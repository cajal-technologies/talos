mod exports;

use num_integer_dep::Integer;
use talos_stdio::{read, write};

/// Keep the arithmetic kernel separate from the stream driver so its Wasm
/// contract can be reused independently of allocation and host I/O.
#[inline(never)]
fn gcd_u64(a: u64, b: u64) -> u64 {
    Integer::gcd(&a, &b)
}

/// Read two little-endian `u64` values and write their greatest common divisor
/// as one little-endian `u64`. Incomplete input produces no output.
pub fn gcd() {
    let mut input = Box::new([0_u8; 16]);
    if read(input.as_mut_slice()) != input.len() {
        return;
    }

    let a = u64::from_le_bytes(input[..8].try_into().unwrap());
    let b = u64::from_le_bytes(input[8..].try_into().unwrap());
    write(&gcd_u64(a, b).to_le_bytes());
}

#[cfg(test)]
mod tests {
    #[test]
    fn num_integer_gcd_matches_expected_values() {
        assert_eq!(super::gcd_u64(54, 24), 6);
        assert_eq!(super::gcd_u64(0, 0), 0);
        assert_eq!(super::gcd_u64(u64::MAX, 0), u64::MAX);
    }
}
