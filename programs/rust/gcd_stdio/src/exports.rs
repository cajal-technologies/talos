/// Byte-stream entry point for the `num-integer` GCD example.
#[unsafe(no_mangle)]
pub extern "C" fn gcd() {
    crate::gcd();
}
