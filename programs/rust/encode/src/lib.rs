#![allow(improper_ctypes_definitions)]

mod exports;

/// Encode a string into its bytes.
///
/// A Rust `&str`/`String` is stored as UTF-8, so its bytes are exactly
/// `s.as_bytes()`. Pure logic kept here; the wasm ABI surface lives in
/// `exports.rs`. This is the function we reason about: string in, bytes out.
/// Inverse of `decode`.
pub fn encode(s: &str) -> Vec<u8> {
    s.as_bytes().to_vec()
}
