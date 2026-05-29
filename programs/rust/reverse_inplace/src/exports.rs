/// Wasm-exported in-place reverse of a `len`-element `u32` slice
/// starting at `ptr` in linear memory.
///
/// Thin `extern "C"` wrapper around [`crate::reverse_inplace`].
#[unsafe(no_mangle)]
pub extern "C" fn reverse_inplace(ptr: *mut u32, len: usize) {
    unsafe { crate::reverse_inplace(ptr, len) }
}
