pub mod exports;

/// Sort `data[0..len]` in ascending order using `scratch[0..len]` as
/// temporary storage.
///
/// The implementation is deliberately allocation-free. Recursive calls split
/// both buffers in half, so the termination argument follows the source-level
/// length recursion and each merge uses only the corresponding scratch range.
///
/// # Safety
///
/// `data` and `scratch` must point to disjoint, readable and writable arrays
/// of at least `len` `u64` elements.
pub unsafe fn mergesort_raw(data: *mut u64, len: usize, scratch: *mut u64) {
    if len <= 1 {
        return;
    }

    let mid = len / 2;
    unsafe {
        mergesort_raw(data, mid, scratch);
        mergesort_raw(data.add(mid), len - mid, scratch.add(mid));
        merge_raw(data, len, mid, scratch);
    }
}

/// Merge the two adjacent sorted ranges `[..mid]` and `[mid..len]`.
///
/// # Safety
///
/// `data` and `scratch` satisfy the same disjoint `len`-element layout as
/// [`mergesort_raw`], and `mid <= len`.
#[inline(never)]
unsafe fn merge_raw(data: *mut u64, len: usize, mid: usize, scratch: *mut u64) {
    unsafe { merge_into(data, len, mid, scratch, 0, mid, 0) };
    unsafe { copy_back(data, scratch, len, 0) };
}

#[inline(never)]
unsafe fn merge_into(
    data: *mut u64,
    len: usize,
    mid: usize,
    scratch: *mut u64,
    i: usize,
    j: usize,
    k: usize,
) {
    if i < mid && j < len {
        let left = unsafe { *data.add(i) };
        let right = unsafe { *data.add(j) };
        if left <= right {
            unsafe { *scratch.add(k) = left };
            unsafe { merge_into(data, len, mid, scratch, i + 1, j, k + 1) };
        } else {
            unsafe { *scratch.add(k) = right };
            unsafe { merge_into(data, len, mid, scratch, i, j + 1, k + 1) };
        }
    } else if i < mid {
        unsafe { *scratch.add(k) = *data.add(i) };
        unsafe { merge_into(data, len, mid, scratch, i + 1, j, k + 1) };
    } else if j < len {
        unsafe { *scratch.add(k) = *data.add(j) };
        unsafe { merge_into(data, len, mid, scratch, i, j + 1, k + 1) };
    }
}

#[inline(never)]
unsafe fn copy_back(data: *mut u64, scratch: *const u64, len: usize, index: usize) {
    if index < len {
        unsafe { *data.add(index) = *scratch.add(index) };
        unsafe { copy_back(data, scratch, len, index + 1) };
    }
}

/// Safe slice wrapper used by native callers and tests.
pub fn mergesort(data: &mut [u64], scratch: &mut [u64]) {
    assert_eq!(data.len(), scratch.len());
    // SAFETY: the two independent mutable slices are disjoint and equally long.
    unsafe { mergesort_raw(data.as_mut_ptr(), data.len(), scratch.as_mut_ptr()) }
}

#[cfg(test)]
mod tests {
    use super::mergesort;

    fn check(mut values: Vec<u64>) {
        let mut expected = values.clone();
        expected.sort();
        let mut scratch = vec![0; values.len()];
        mergesort(&mut values, &mut scratch);
        assert_eq!(values, expected);
    }

    #[test]
    fn sorts_representative_inputs() {
        check(vec![]);
        check(vec![7]);
        check(vec![5, 1, 4, 2, 3]);
        check(vec![4, 1, 4, 2, 1, 0]);
        check(vec![u64::MAX, 0, 1, u64::MAX - 1]);
    }
}
