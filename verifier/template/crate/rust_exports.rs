/// Wasm-exported entry point for `CRATE_NAME`.
#[unsafe(no_mangle)]
pub extern "C" fn CRATE_NAME(n: i32) -> bool {
    crate::CRATE_NAME(n)
}
