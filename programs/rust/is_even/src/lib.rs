#[unsafe(no_mangle)]
pub extern "C" fn is_even(n: i32) -> bool {
    n % 2 == 0
}
