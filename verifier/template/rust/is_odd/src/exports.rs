#[unsafe(no_mangle)]
pub extern "C" fn is_odd(n: i32) -> bool {
    crate::is_odd(n)
}
