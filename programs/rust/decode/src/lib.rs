#![allow(improper_ctypes_definitions)]

mod exports;

/// Decode bytes back into the original string.
///
/// Inverse of `encode`: interprets the UTF-8 `bytes` as a string. Because a
/// `&str` is already stored as UTF-8, the round-trip `decode(encode(s)) == s`.
/// Pure logic kept here; the wasm ABI surface lives in `exports.rs`. This is
/// the function we reason about: bytes in, string out.
pub fn decode(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).unwrap()
}
