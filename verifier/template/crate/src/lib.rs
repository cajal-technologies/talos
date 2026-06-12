mod exports;

/// Starting-point implementation for `CRATE_NAME`. Replace the body with the
/// real logic you want to verify; keep the pure function here and expose it
/// across the wasm ABI in `exports.rs`.
pub fn CRATE_NAME(n: i32) -> bool {
    n % 2 == 0
}
