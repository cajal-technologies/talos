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

/-- Close a `BinChunk` goal for a `u64` operation that the compiler inlines to a
single `i64` instruction, given the atomic lifting rule that justifies it:

    theorem add_chunk : BinChunk [.addI64] ((· + ·) : UInt64 → UInt64 → UInt64) := by
      bin_chunk_of Wasm.SmallStep.wp_addI64

Every such chunk is proved the same way — introduce the contextual telescope,
then reduce `toV` and the singleton-fragment append so the atomic rule's
conclusion is syntactically the goal. Only the rule differs, so only the rule is
written down.

Chunks with a precondition name it with `with`, and may then feed it to the
rule; the name is the caller's, so it is in scope in the rule term:

    theorem div_chunk : BinChunk [.divUI64] (· / ·) (fun _ b => b ≠ 0) := by
      bin_chunk_of Wasm.SmallStep.wp_divUI64 hne with hne

Operations that are *not* one instruction (`shl`, `shr`, `not`) have their own
proofs; this tactic is for the single-instruction family only. -/
syntax "bin_chunk_of " term (" with " ident)? : tactic

macro_rules
  | `(tactic| bin_chunk_of $rule:term) =>
      `(tactic| bin_chunk_of $rule with _hpre)
  | `(tactic| bin_chunk_of $rule:term with $hpre:ident) =>
      `(tactic|
        (intro α hlc inst s E Φ params localValues rest arity remainder
           controls calls a b vs $hpre
         simpa only [toV_u64, List.cons_append, List.nil_append] using $rule))

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
