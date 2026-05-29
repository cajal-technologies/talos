//! Wasm ABI surface for the `rust_option` crate. Each export is a thin
//! `extern "C"` wrapper around a pure Rust function in [`crate`]. The
//! wire-format encoding (sentinel `i64::MIN` for `None`) lives in
//! [`crate::SENTINEL`].

/// `Option::unwrap_or` on a statically-known `Some(v)`. The compiler
/// collapses this to the identity; kept as a witness that the toolchain
/// does fold the trivial case away.
#[unsafe(no_mangle)]
pub extern "C" fn wrap(v: i64) -> i64 {
    crate::wrap(v)
}

/// `Option::is_some`. Returns `1` for `Some`, `0` for `None`.
#[unsafe(no_mangle)]
pub extern "C" fn is_some(opt: i64) -> i32 {
    crate::is_some(opt)
}

/// `Option::unwrap_or` — returns the contained value or `default`.
#[unsafe(no_mangle)]
pub extern "C" fn unwrap_or(opt: i64, default: i64) -> i64 {
    crate::unwrap_or(opt, default)
}

/// `Option::unwrap_or_default` — returns the contained value or `0`
/// (the `Default::default()` value for `i64`).
#[unsafe(no_mangle)]
pub extern "C" fn unwrap_or_default(opt: i64) -> i64 {
    crate::unwrap_or_default(opt)
}

/// `Option::map` over wrapping addition by `k`.
#[unsafe(no_mangle)]
pub extern "C" fn map_add(opt: i64, k: i64) -> i64 {
    crate::map_add(opt, k)
}

/// `Option::or` — returns `a` if it is `Some`, otherwise `b`.
#[unsafe(no_mangle)]
pub extern "C" fn or(a: i64, b: i64) -> i64 {
    crate::or(a, b)
}

/// `Option::filter` with the predicate `x > 0`.
#[unsafe(no_mangle)]
pub extern "C" fn filter_positive(opt: i64) -> i64 {
    crate::filter_positive(opt)
}
