mod exports;

/// Sort `data[0..len]` (unsigned 64-bit, ascending) in place, using
/// `scratch[0..len]` as auxiliary space. Bottom-up (iterative) merge sort:
/// stable, `O(n log n)`, no recursion and no allocation.
///
/// `scratch` must point at a distinct region of at least `len` `u64` slots; its
/// initial contents are irrelevant (they are overwritten). On return `data` is
/// sorted and `scratch` holds scratch data.
///
/// # Safety
/// `data` and `scratch` must each be valid for `len` `u64` reads and writes and
/// must not overlap each other.
pub unsafe fn mergesort(data: *mut u64, len: usize, scratch: *mut u64) {
    let mut width: usize = 1;
    while width < len {
        let mut lo: usize = 0;
        while lo < len {
            let mid = if lo + width < len { lo + width } else { len };
            let hi = if lo + 2 * width < len {
                lo + 2 * width
            } else {
                len
            };
            // Merge the two sorted runs data[lo..mid] and data[mid..hi] into
            // scratch[lo..hi].
            let mut i = lo;
            let mut j = mid;
            let mut k = lo;
            while i < mid && j < hi {
                let a = unsafe { *data.add(i) };
                let b = unsafe { *data.add(j) };
                if a <= b {
                    unsafe { *scratch.add(k) = a };
                    i += 1;
                } else {
                    unsafe { *scratch.add(k) = b };
                    j += 1;
                }
                k += 1;
            }
            while i < mid {
                unsafe { *scratch.add(k) = *data.add(i) };
                i += 1;
                k += 1;
            }
            while j < hi {
                unsafe { *scratch.add(k) = *data.add(j) };
                j += 1;
                k += 1;
            }
            lo += 2 * width;
        }
        // Copy the merged runs back into `data` for the next pass.
        let mut t: usize = 0;
        while t < len {
            unsafe { *data.add(t) = *scratch.add(t) };
            t += 1;
        }
        width *= 2;
    }
}
