/// Wasm-exported dispatcher. Returns `OPS[sel % 2].apply(x)`.
///
/// Thin `extern "C"` wrapper around [`crate::dispatch`]; the indirect
/// vtable call lives inside `dispatch`.
#[unsafe(no_mangle)]
pub extern "C" fn dispatch(sel: i32, x: i32) -> i32 {
    crate::dispatch(sel, x)
}
