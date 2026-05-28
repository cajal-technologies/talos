#[unsafe(no_mangle)]
pub extern "C" fn is_even(n: i32) -> bool {
    crate::is_even(n)
}
