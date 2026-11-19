import Interpreter.Wasm

/-!
# `u64` shift-count normalization

When a Rust `u64` shift takes a `u32` count (as the `rust_u64` exports do),
rustc lowers the count to a mask to the low 6 bits followed by
`i64.extend_i32_u`. `shiftAmount_norm` proves that
prefix computes `b % 64`, so specs of `shl`/`shr` can rewrite with it.
-/

namespace Wasm.RustStd

open Wasm

namespace U64

/-- Wasm masks `u64` shift amounts to the low 6 bits. -/
abbrev shiftMask : UInt32 := 63

/-- The mask-and-extend prefix normalizes the shift count to `b % 64`.
It speaks of the shift *amount* only (not the shift direction), so the
kernel-checked mask identity is proved here once and reused by every shift
(`shl`, `shr`, and any future shift-like op). -/
theorem shiftAmount_norm (b : UInt32) :
    UInt64.ofNat (shiftMask &&& b).toNat % 64 = b.toUInt64 % 64 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_mod, UInt64.toNat_ofNat, UInt32.toNat_and, UInt32.toNat_toUInt64]
  change ((63 &&& b.toNat) % 2^64) % 64 = b.toNat % 64
  rw [Nat.and_comm, show (63 : Nat) = 2^6-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

end U64

end Wasm.RustStd
