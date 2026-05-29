mod exports;

/// XOR-fold a slice of `u32`s.
///
/// Returns `0` when `xs` is empty.
pub fn xor_sum(xs: &[u32]) -> u32 {
    let mut acc: u32 = 0;
    let mut i: usize = 0;
    while i < xs.len() {
        acc ^= xs[i];
        i += 1;
    }
    acc
}
