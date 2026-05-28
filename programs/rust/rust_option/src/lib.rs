//! Small showcase of the `Option<T>` API, exposed through a wasm-friendly
//! C ABI. The wasm side encodes `None` as a sentinel `i64` value (`i64::MIN`)
//! and `Some(x)` as `x` itself; this keeps the surface monomorphic and easy
//! to reason about on the Lean side.

const SENTINEL: i64 = i64::MIN;

fn decode_in(v: i64) -> Option<i64> {
    if v == SENTINEL { None } else { Some(v) }
}

fn decode_out(v: Option<i64>) -> i64 {
    v.unwrap_or(SENTINEL)
}

/// `Option::unwrap_or` on a statically-known `Some(v)`. The compiler
/// collapses this to the identity; kept as a witness that the toolchain
/// does fold the trivial case away.
#[unsafe(no_mangle)]
pub extern "C" fn wrap(v: i64) -> i64 {
    decode_out(Some(v))
}

/// `Option::is_some`.
#[unsafe(no_mangle)]
pub extern "C" fn is_some(opt: i64) -> i32 {
    decode_in(opt).is_some() as i32
}

/// `Option::unwrap_or` — returns the contained value or `default`.
#[unsafe(no_mangle)]
pub extern "C" fn unwrap_or(opt: i64, default: i64) -> i64 {
    decode_in(opt).unwrap_or(default)
}

/// `Option::unwrap_or_default` — returns the contained value or `0`
/// (the `Default::default()` value for `i64`).
#[unsafe(no_mangle)]
pub extern "C" fn unwrap_or_default(opt: i64) -> i64 {
    decode_in(opt).unwrap_or_default()
}

/// `Option::map` over wrapping addition by `k`.
#[unsafe(no_mangle)]
pub extern "C" fn map_add(opt: i64, k: i64) -> i64 {
    decode_out(decode_in(opt).map(|x| x.wrapping_add(k)))
}

/// `Option::or` — returns `a` if it is `Some`, otherwise `b`.
#[unsafe(no_mangle)]
pub extern "C" fn or(a: i64, b: i64) -> i64 {
    decode_out(decode_in(a).or(decode_in(b)))
}

/// `Option::filter` with the predicate `x > 0`.
#[unsafe(no_mangle)]
pub extern "C" fn filter_positive(opt: i64) -> i64 {
    decode_out(decode_in(opt).filter(|x| *x > 0))
}
