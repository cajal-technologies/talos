/// Wasm-exported `mergesort`: sorts `data[0..len]` (`u64`, ascending) in place
/// using `scratch[0..len]` as auxiliary space.
///
/// Thin `extern "C"` wrapper around the pure [`crate::mergesort`].
#[unsafe(no_mangle)]
pub extern "C" fn mergesort(data: *mut u64, len: usize, scratch: *mut u64) {
    unsafe { crate::mergesort(data, len, scratch) }
}
