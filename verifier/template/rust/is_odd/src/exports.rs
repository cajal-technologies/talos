/// Wasm-exported parity check. Returns `true` iff `n` is odd.
///
/// Defined as the negation of the `is_even` crate's export — see
/// [`is_even::is_even`]. Lives here, in `exports.rs`, because the
/// project convention reserves this file for the wasm ABI surface.
#[unsafe(no_mangle)]
pub extern "C" fn is_odd(n: i32) -> bool {
    crate::is_odd(n)
}
