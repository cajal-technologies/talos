/// Wasm-exported entry point for `swap_elements`.
///
/// Thin `extern "C"` wrapper around the pure [`crate::swap_elements`]. The
/// project convention reserves this file for the wasm ABI surface, so the
/// export table matches exactly what the verifier reasons about.
///
/// Receives the array as a `(pointer, length)` pair plus the two indices to
/// swap. On wasm32 both `usize` and the pointer are 32-bit. The caller must
/// guarantee `i < data_length` and `j < data_length` and that
/// `[array_ptr, array_ptr + data_length)` is a valid, aligned `u64` region.
#[unsafe(no_mangle)]
pub extern "C" fn swap_elements(array_ptr: *mut u64, data_length: usize, i: usize, j: usize) {
    let arr = unsafe { core::slice::from_raw_parts_mut(array_ptr, data_length) };
    crate::swap_elements(arr, i, j);
}
