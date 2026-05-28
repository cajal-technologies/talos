mod exports;

pub fn is_odd(n: i32) -> bool {
    !is_even::is_even(n)
}
