import Interpreter.Wasm.Decoder.Wat

/-! Exact rounding and malformed-input regressions for WAT float literals.
Every result is checked by reduction in Lean's kernel. -/
namespace Wasm.Decoder.Wat

set_option maxRecDepth 10000

theorem float_literals_basic :
    parseF32Lit "1.5" = .ok 0x3fc00000 ∧
    parseF64Lit "-0x1.ep+2" = .ok 0xc01e000000000000 ∧
    parseF32Lit "-0" = .ok 0x80000000 ∧
    parseF64Lit "nan:0x123" = .ok 0x7ff0000000000123 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Round directly to binary32: an intermediate binary64 round would lose
this literal's tiny excess over the binary32 midpoint. -/
theorem float_literal_single_rounding :
    parseF32Lit "0x1.00000100000001p0" = .ok 0x3f800001 := rfl

theorem float_literals_extreme_exponents :
    parseF32Lit "1e1000000000" = .ok 0x7f800000 ∧
    parseF32Lit "-1e-1000000000" = .ok 0x80000000 ∧
    parseF64Lit "0x1p-1000000000" = .ok 0 ∧
    parseF64Lit "-0e1000000000" = .ok 0x8000000000000000 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem float_literals_reject_malformed :
    (parseF32Lit "1e").toOption = none ∧
    (parseF32Lit "1.2.3").toOption = none ∧
    (parseF64Lit "0x1p2p9").toOption = none ∧
    (parseF64Lit "nan:0x").toOption = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Wasm.Decoder.Wat
