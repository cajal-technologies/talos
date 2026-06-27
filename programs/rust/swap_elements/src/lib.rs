mod exports;

/// Swap the elements at indices `i` and `j` of a mutable slice.
///
/// Pure logic kept here; the wasm ABI surface (raw pointer + length) lives in
/// `exports.rs`. Both `i` and `j` are assumed to be in bounds (`< arr.len()`),
/// matching the contract documented on the export.
pub fn swap_elements(arr: &mut [u64], i: usize, j: usize) {
    arr.swap(i, j);
}
