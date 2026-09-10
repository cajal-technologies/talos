import CodeLib.RustStd.UInt

/-!
# `UInt64` as a wasm `i64`

The `UIntWasm UInt64` instance: a `u64` is carried as `Value.i64`. The trunk's
generic chunk/body helpers specialise to this instance; each operator's own
file (`U64/Add.lean`, …) supplies the concrete `i64.*` fragment. The `u32`
shift-count encoding (`toV_u32`) that `Shl`/`Shr` use comes from the trunk.
-/

namespace Wasm.RustStd

open Wasm

instance instUIntWasmUInt64 : UIntWasm UInt64 where
  toV a := .i64 a

/-- `toV` on `UInt64` is `Value.i64` — a `@[simp]` rewrite so chunk proofs reduce
the stack to concrete `i64` and the atomic `wp_*` lemmas fire. -/
@[simp] theorem toV_u64 (a : UInt64) : (UIntWasm.toV a : Value) = .i64 a := rfl

namespace U64

/-- Wasm masks `u64` shift amounts to the low 6 bits. -/
abbrev shiftMask : UInt32 := 63

/-- The emitted mask-and-extend prefix shared by `u64` shifts whose count starts
as a Rust `u32`. -/
abbrev shiftAmountFrag : Program := [.const shiftMask, .and, .extendUI32]

/-- The mask-and-extend prefix normalises the shift count to `b % 64`.
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
