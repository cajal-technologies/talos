//! Wasm ABI for `encode_decode_tests` — client programs over the frame codec.
//!
//! `roundtrip` is the headline: it frames a payload with `encode` and reads it
//! straight back with `decode`. `encode_frame` / `decode_frame` exercise each
//! half on its own. Every function is a thin caller, so its Lean proof is just
//! the reused codec theorem crossed over the `call`.

use encode_decode::{decode, encode};

/// Frame the `len`-byte payload at `src` into `dst`; returns `4 + len`.
#[unsafe(no_mangle)]
pub extern "C" fn encode_frame(src: *const u8, len: usize, dst: *mut u8) -> usize {
    encode(src, len, dst)
}

/// Read the frame at `src` back into `dst` (capacity `cap`); returns the payload
/// length, or a negative status.
#[unsafe(no_mangle)]
pub extern "C" fn decode_frame(src: *const u8, len: usize, dst: *mut u8, cap: usize) -> i64 {
    decode(src, len, dst, cap)
}

/// Round-trip: `encode` the payload at `src` into the scratch buffer `mid`, then
/// `decode` that frame into `dst`. Returns `decode`'s result (the payload length
/// on success).
#[unsafe(no_mangle)]
pub extern "C" fn roundtrip(
    src: *const u8,
    len: usize,
    mid: *mut u8,
    dst: *mut u8,
    cap: usize,
) -> i64 {
    encode(src, len, mid);
    decode(mid as *const u8, 4 + len, dst, cap)
}
