//! Reuse tests for the `encode_decode` frame codec.
//!
//! Each export here is *client code* that calls `encode_decode::encode` /
//! `decode`. At opt-0 those calls lower to wasm `call`s (no inlining), so the
//! codec bodies land in this module unchanged — and the Lean proofs discharge
//! each `call` with the codec's proven body theorems instead of re-verifying the
//! codec. That is the whole point: verifying a program that *uses* the codec
//! costs a couple of tactics, not a fresh memory proof.

mod exports;
