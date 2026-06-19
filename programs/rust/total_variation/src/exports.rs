#[unsafe(no_mangle)]
pub extern "C" fn total_variation(a: u64, b: u64, c: u64) -> u64 {
    a.abs_diff(b).wrapping_add(b.abs_diff(c))
}
