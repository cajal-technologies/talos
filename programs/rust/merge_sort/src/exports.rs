//! Wasm ABI surface for `merge_sort`. By project convention this file is the
//! *only* place `unsafe` appears: it reconstructs the data slice from the raw
//! (pointer, length) pair the wasm caller passes, then hands it to the safe,
//! slice-based [`crate::sort_slice`], which allocates its own scratch space.

/// Sort `len` consecutive `u32`s stored at `data_ptr` into ascending order,
/// in place. Scratch space is allocated internally, so the caller supplies
/// only the data buffer.
///
/// On return the `data` region holds the sorted permutation of its original
/// contents.
///
/// # ABI / safety contract
///
/// The caller must guarantee that `data_ptr` is aligned for `u32` and points
/// to `len` initialised, in-bounds `u32`s for the duration of the call.
///
/// `len` is a wasm `usize` (32-bit). All bounds reasoning lives in the safe
/// core; this wrapper only materialises the slice.
#[unsafe(no_mangle)]
pub extern "C" fn merge_sort(data_ptr: *mut u32, len: usize) {
    // SAFETY: upheld by the caller per the contract documented above —
    // `data_ptr` is a valid, initialised, `len`-element `u32` range that
    // lives for the whole call.
    let data = unsafe { core::slice::from_raw_parts_mut(data_ptr, len) };
    crate::sort_slice(data);
}
