/// Wasm-exported equivalence check between the vtable-based dispatcher
/// and the direct-match reference. Traps via `unreachable` iff the two
/// disagree on `(sel, x)`.
///
/// Thin `extern "C"` wrapper around [`crate::check`]. The project
/// convention reserves this file for the wasm ABI surface.
#[unsafe(no_mangle)]
pub extern "C" fn check(sel: i32, x: i32) {
    crate::check(sel, x)
}
