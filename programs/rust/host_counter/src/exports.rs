/// Wasm-exported guarded counter step. Thin `extern "C"` wrapper
/// around [`crate::step`]. The project convention reserves this file
/// for the wasm ABI surface.
#[unsafe(no_mangle)]
pub extern "C" fn step() {
    crate::step()
}
