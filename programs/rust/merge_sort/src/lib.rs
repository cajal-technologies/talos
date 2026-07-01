mod exports;

/// Sort `data` ascending and return it, using an internally allocated
/// scratch buffer of the same length as working space.
///
/// This is the ergonomic, owned-`Vec` entry point. The actual sorting is
/// done by [`merge_sort_into`], which is the routine the wasm export
/// targets — it takes the data and scratch buffers from the caller so that
/// no allocation happens across the wasm ABI.
pub fn merge_sort(mut data: Vec<u32>) -> Vec<u32> {
    sort_slice(&mut data);
    data
}

/// Sort `data` ascending **in place**, allocating the scratch buffer
/// internally.
///
/// This is the routine the wasm export now targets: the caller hands over
/// only the data slice, and the equal-sized scratch space is allocated here
/// (via `Vec`) rather than supplied across the ABI. The allocation is the
/// reason the export's verification must now also reason about the Rust
/// allocator (and, transitively, `memory.grow`).
pub(crate) fn sort_slice(data: &mut [u32]) {
    let mut scratch = vec![0u32; data.len()];
    merge_sort_into(data, &mut scratch);
}

/// Top-down (recursive) merge sort.
///
/// On entry `data` holds the values to sort and `scratch` is working space
/// of the **same length**. On return `data` is sorted ascending and is a
/// permutation of its original contents; `scratch`'s final contents are
/// unspecified.
///
/// The data and scratch buffers are split in lock-step so that every
/// recursive call again sees two equal-length slices: the left/right halves
/// of `data` are sorted recursively (each using the matching half of
/// `scratch` as its own working space), then merged into `scratch` and copied
/// back into `data`.
pub(crate) fn merge_sort_into(data: &mut [u32], scratch: &mut [u32]) {
    let n = data.len();
    if n <= 1 {
        return;
    }
    let mid = n / 2;
    let (data_left, data_right) = data.split_at_mut(mid);
    let (scratch_left, scratch_right) = scratch.split_at_mut(mid);
    merge_sort_into(data_left, scratch_left);
    merge_sort_into(data_right, scratch_right);
    // Both halves of `data` are now sorted; merge them into `scratch` and
    // copy the merged run back so the caller again finds the result in `data`.
    merge(data_left, data_right, scratch);
    data.copy_from_slice(scratch);
}

/// Merge two already-sorted slices `left` and `right` into `out`, preserving
/// ascending order. `out.len()` must equal `left.len() + right.len()`. Ties
/// favour `left`, making the overall sort stable.
fn merge(left: &[u32], right: &[u32], out: &mut [u32]) {
    let (mut i, mut j, mut k) = (0, 0, 0);
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            out[k] = left[i];
            i += 1;
        } else {
            out[k] = right[j];
            j += 1;
        }
        k += 1;
    }
    while i < left.len() {
        out[k] = left[i];
        i += 1;
        k += 1;
    }
    while j < right.len() {
        out[k] = right[j];
        j += 1;
        k += 1;
    }
}
