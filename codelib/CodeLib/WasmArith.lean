import CodeLib.WasmArithAttr
import CodeLib.UInt32
import CodeLib.UInt64
import CodeLib.SepLogic.WasmHeap
import CodeLib.RustStd.Region
import CodeLib.RustStd.MemArray
import CodeLib.Examples.UInt32Array.Laws

/-!
# `wasm_arith` simp set and `wasm_side` closer

`wasm_arith` is a named simp set for UInt32/UInt64 address and word arithmetic
lemmas shared across Wasm proofs.  Tag new lemmas with `attribute [wasm_arith] …`
here; consume the set via the `wasm_side` tactic.

Mirrors the in-repo precedent `register_simp_attr wp_simp`
(`interpreter/Interpreter/Wasm/Wp/Defs.lean`).

**Excluded on purpose**
- `UInt32.add_comm`: causes `simp` loops.
- `Wasm.SepLogic.UInt32.addSteps4`, `addSteps8`: return conjunctions, not
  compatible as simp rewrite rules.
-/

-- no-wrap toNat of address + ofNat n (WasmHeap.lean)
attribute [wasm_arith] Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap
-- stride-4 slot address bridge (RustStd/MemArray.lean)
attribute [wasm_arith] Wasm.Mem.words32_slotAddr_toNat
-- stride-8 slot address bridge (RustStd/MemArray.lean)
attribute [wasm_arith] Wasm.Mem.words64_slotAddr_toNat
-- slot base toNat, stride 8 (RustStd/Region.lean)
attribute [wasm_arith] Wasm.MemRegion.slot64_base_toNat
-- slot base toNat, stride 4 (RustStd/Region.lean)
attribute [wasm_arith] Wasm.MemRegion.slot32_base_toNat
-- shift = multiply, stride 8 (RustStd/Region.lean)
attribute [wasm_arith] Wasm.MemRegion.shl3_eq_mul8
-- shift = multiply, stride 4 (RustStd/Region.lean)
attribute [wasm_arith] Wasm.MemRegion.shl2_eq_mul4
-- array address with index * 4 (Examples/UInt32Array/Laws.lean)
attribute [wasm_arith] Wasm.Examples.UInt32Array.arrayAddress_toNat
-- ofNat successor (UInt32.lean)
attribute [wasm_arith] UInt32.ofNat_succ
-- general stride-4 address step (UInt32.lean)
attribute [wasm_arith] Wasm.UInt32.add_stride4_ofNat
-- concrete stride-4 steps (+4 / +8 / +12) for rw-friendly simp matching
attribute [wasm_arith] Wasm.UInt32.add_stride4_add1
attribute [wasm_arith] Wasm.UInt32.add_stride4_add2
attribute [wasm_arith] Wasm.UInt32.add_stride4_add3
-- parity bridge via toNat (UInt32.lean)
attribute [wasm_arith] Wasm.UInt32.and_one_eq_zero_iff_toNat_mod_two
-- comparison inversion, UInt32 (UInt32.lean)
attribute [wasm_arith] Wasm.UInt32.le_of_not_lt
-- comparison inversion, UInt32 (UInt32.lean)
attribute [wasm_arith] Wasm.UInt32.le_of_not_le
-- comparison inversion, UInt64 (UInt64.lean)
attribute [wasm_arith] Wasm.UInt64.le_of_not_lt

/-- Close Wasm arithmetic side goals left by `wasm_twp_pures` / `iapply twp_*`.
Tries `omega` (linear arithmetic over `Nat`/`Int`) first, then `decide`
(concrete closed propositions), then `simp only [wasm_arith]` followed by
`omega`.

`bv_decide` and `native_decide` are intentionally excluded: both introduce
`Lean.ofReduceBool`, which propagates into shared memory-ownership facts and
lifting rules. -/
macro "wasm_side" : tactic =>
  `(tactic| first | omega | decide | (simp only [wasm_arith]; omega))
