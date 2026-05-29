mod exports;

/// Pure parity check. `true` iff `n` is divisible by 2.
pub fn is_even(n: i32) -> bool {
    n % 2 == 0
}
