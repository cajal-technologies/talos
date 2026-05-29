//! Small showcase of the `Option<T>` API, exposed through a wasm-friendly
//! C ABI. The wasm side encodes `None` as a sentinel `i64` value (`i64::MIN`)
//! and `Some(x)` as `x` itself; this keeps the surface monomorphic and easy
//! to reason about on the Lean side.

mod exports;

/// Encoded `None` value. Any `i64` other than this counts as `Some(x)`.
pub const SENTINEL: i64 = i64::MIN;

/// Decode a wire-format `i64` into a Rust `Option<i64>`.
pub fn decode_in(v: i64) -> Option<i64> {
    if v == SENTINEL { None } else { Some(v) }
}

/// Encode an `Option<i64>` back into the wire format.
pub fn decode_out(v: Option<i64>) -> i64 {
    v.unwrap_or(SENTINEL)
}

/// `Option::unwrap_or` on a statically-known `Some(v)` — the identity.
pub fn wrap(v: i64) -> i64 {
    decode_out(Some(v))
}

/// `Option::is_some`. Returns `1` for `Some`, `0` for `None`.
pub fn is_some(opt: i64) -> i32 {
    decode_in(opt).is_some() as i32
}

/// `Option::unwrap_or` — returns the contained value or `default`.
pub fn unwrap_or(opt: i64, default: i64) -> i64 {
    decode_in(opt).unwrap_or(default)
}

/// `Option::unwrap_or_default` — returns the contained value or `0`.
pub fn unwrap_or_default(opt: i64) -> i64 {
    decode_in(opt).unwrap_or_default()
}

/// `Option::map` over `i64::wrapping_add(k)`.
pub fn map_add(opt: i64, k: i64) -> i64 {
    decode_out(decode_in(opt).map(|x| x.wrapping_add(k)))
}

/// `Option::or` — returns `a` if it is `Some`, else `b`.
pub fn or(a: i64, b: i64) -> i64 {
    decode_out(decode_in(a).or(decode_in(b)))
}

/// `Option::filter` with the predicate `x > 0`.
pub fn filter_positive(opt: i64) -> i64 {
    decode_out(decode_in(opt).filter(|x| *x > 0))
}
