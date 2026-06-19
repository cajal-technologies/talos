#[unsafe(no_mangle)]
pub extern "C" fn abs_diff(a: u64, b: u64) -> u64 {
    a.abs_diff(b)
}


#[unsafe(no_mangle)]
pub extern "C" fn entrypoint(a: u64, b: u64) {
    let _ = abs_diff(a, b);
}
