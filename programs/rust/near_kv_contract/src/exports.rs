/// Wasm-exported NEAR storage setter.
#[unsafe(no_mangle)]
pub extern "C" fn set_from_input() {
    crate::set_from_input()
}
