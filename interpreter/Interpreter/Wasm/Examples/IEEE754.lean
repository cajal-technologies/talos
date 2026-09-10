import Interpreter.Wasm.IEEE754

/-! Kernel checks for rounding and exceptional-value boundaries of the pure model. -/
namespace Wasm.IEEE754

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem binary32_rounding_boundaries :
    add binary32 0x3f800000 0x33800000 = 0x3f800000 ∧
    add binary32 0x3f800001 0x33800000 = 0x3f800002 ∧
    add binary32 0x007fffff 1 = 0x00800000 ∧
    div binary32 1 0x40000000 = 0 ∧
    div binary32 0x00800000 0x40000000 = 0x00400000 ∧
    mul binary32 0x7f7fffff 0x40000000 = 0x7f800000 ∧
    div binary32 0x3f800000 0x40400000 = 0x3eaaaaab := by decide +kernel

theorem binary64_rounding_boundaries :
    add binary64 0x3ff0000000000000 0x3ca0000000000000 = 0x3ff0000000000000 ∧
    add binary64 0x3ff0000000000001 0x3ca0000000000000 = 0x3ff0000000000002 ∧
    add binary64 0x000fffffffffffff 1 = 0x0010000000000000 ∧
    div binary64 1 0x4000000000000000 = 0 ∧
    div binary64 0x0010000000000000 0x4000000000000000 = 0x0008000000000000 ∧
    mul binary64 0x7fefffffffffffff 0x4000000000000000 = 0x7ff0000000000000 ∧
    div binary64 0x3ff0000000000000 0x4008000000000000 = 0x3fd5555555555555 := by decide +kernel

theorem square_root_boundaries :
    sqrt binary32 0x40000000 = 0x3fb504f3 ∧
    sqrt binary64 0x4000000000000000 = 0x3ff6a09e667f3bcd ∧
    sqrt binary32 0x80000000 = 0x80000000 ∧
    sqrt binary64 0xbff0000000000000 = 0x7ff8000000000000 := by decide +kernel

theorem exceptional_values :
    add binary32 0x7f800000 0xff800000 = 0x7fc00000 ∧
    mul binary32 0 0x7f800000 = 0x7fc00000 ∧
    div binary64 0 0 = 0x7ff8000000000000 ∧
    minimum binary32 0 0x80000000 = 0x80000000 ∧
    maximum binary32 0 0x80000000 = 0 ∧
    roundIntegral binary32 .nearestEven 0xbf000000 = 0x80000000 ∧
    eq binary32 0 0x80000000 = true ∧
    lt binary64 0x7ff8000000000000 0 = false := by decide +kernel

theorem conversion_boundaries :
    ofInt binary64 18446744073709551615 = 0x43f0000000000000 ∧
    ofInt binary32 16777217 = 0x4b800000 ∧
    saturate binary32 0x4f000000 (-2147483648) 2147483647 = 2147483647 ∧
    saturate binary32 0xcf000000 (-2147483648) 2147483647 = -2147483648 ∧
    truncBounded binary32 0x4f000000 (-2147483648) 2147483647 = none ∧
    truncBounded binary32 0xcf000000 (-2147483648) 2147483647 = some (-2147483648) := by decide +kernel

end Wasm.IEEE754
