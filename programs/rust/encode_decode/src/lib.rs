//! Length-prefixed frame codec. The whole surface is the raw wasm ABI in
//! `exports.rs` (this crate has no host-facing safe API to verify).
//!
//! `encode`/`decode` are re-exported at the crate root so downstream crates
//! (e.g. `encode_decode_tests`) can *call* them — the reuse story: their Lean
//! proofs discharge the client `call` with the codec's proven body theorems
//! rather than re-verifying the codec. The re-export is Rust-visibility only and
//! does not change the emitted wasm (the functions are already `no_mangle`).

mod exports;
pub use exports::{decode, encode};
