mod exports;

/// Reverse, in place, the `len` `u32` words starting at `ptr`.
///
/// Exercises both loads and stores to linear memory: the i-th and
/// (len-1-i)-th words are swapped for `i < len / 2`.
///
/// # Safety
///
/// `ptr` must be valid for reads and writes of `len` `u32` words and
/// properly aligned.
pub unsafe fn reverse_inplace(ptr: *mut u32, len: usize) {
    if len == 0 {
        return;
    }
    let mut lo: usize = 0;
    let mut hi: usize = len - 1;
    while lo < hi {
        unsafe {
            let a = *ptr.add(lo);
            let b = *ptr.add(hi);
            *ptr.add(lo) = b;
            *ptr.add(hi) = a;
        }
        lo += 1;
        hi -= 1;
    }
}
