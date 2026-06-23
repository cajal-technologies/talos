//! Slice primitive corpus. The primitive helpers are generic over `T`; these
//! wrappers pick one concrete monomorphization so the verifier has wasm to lift.
//! The emitted `len`/`is_empty` bodies only inspect the slice length, so the
//! codelib theorems are about the `&[T]` fat-pointer shape, not this element type.

#[unsafe(no_mangle)]
pub extern "C" fn len(xs: &[u8]) -> usize {
    crate::len(xs)
}

#[unsafe(no_mangle)]
pub extern "C" fn is_empty(xs: &[u8]) -> bool {
    crate::is_empty(xs)
}

#[unsafe(no_mangle)]
pub extern "C" fn entrypoint(xs: &[u8]) {
    let _ = len(xs);
    let _ = is_empty(xs);
}
