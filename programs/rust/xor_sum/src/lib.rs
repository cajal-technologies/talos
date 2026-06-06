mod exports;

/// Maximum length the equivalence check exercises. Bounds the on-stack
/// scratch buffer.
const BUF_CAP: u32 = 32;

/// Forward XOR-fold: accumulate left-to-right. This is the
/// implementation under test.
#[inline(never)]
fn xor_fast(xs: &[u32]) -> u32 {
    let mut acc: u32 = 0;
    let mut i: usize = 0;
    while i < xs.len() {
        acc ^= xs[i];
        i += 1;
    }
    acc
}

/// Obviously-correct XOR-fold: accumulate right-to-left. Since XOR is
/// associative and commutative, the result must agree with the forward
/// fold for every input. Used as the reference oracle that
/// [`xor_fast`] is checked against.
#[inline(never)]
fn xor_naive(xs: &[u32]) -> u32 {
    let mut acc: u32 = 0;
    let mut i: usize = xs.len();
    while i > 0 {
        i -= 1;
        acc ^= xs[i];
    }
    acc
}

fn trap() -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    unreachable!();
}

/// Seed a length-`len` buffer from `seed`, fold it both ways, and trap
/// if the results disagree.
///
/// `len` is clamped to `[0, BUF_CAP]` so the on-stack scratch buffer
/// cannot overflow.
pub fn check(seed: u32, len: u32) {
    let len = if len > BUF_CAP { BUF_CAP } else { len } as usize;
    let mut xs = [0u32; BUF_CAP as usize];
    let mut i: usize = 0;
    while i < len {
        xs[i] = seed
            .wrapping_mul((i as u32).wrapping_add(1))
            .wrapping_add(i as u32);
        i += 1;
    }
    if xor_fast(&xs[..len]) != xor_naive(&xs[..len]) {
        trap();
    }
}
