import Interpreter.Wasm.Semantics

/-!
# `UInt32` counter-stepping lemmas for the examples

Shared by the loop / recursion examples (`SimpleLoop`, `Factorial`,
`EvenOddRec`): their measures step a `UInt32` counter down by one, and both the
decreasing-measure obligation and the invariant re-establishment need
`(x - 1).toNat` in `Nat` terms. `x ≠ 0` rules out the `0 - 1` wraparound
(`0 - 1 = 0xFFFFFFFF` on `UInt32`, but `0 - 1 = 0` on `Nat`). Previously this
proof block was pasted in each of the three files.
-/

/-- On `UInt32`, when `x ≠ 0` the wrapping predecessor agrees with `Nat`
subtraction: `(x - 1).toNat = x.toNat - 1`. -/
theorem UInt32.toNat_sub_one_eq {x : UInt32} (hx : x.toNat ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  rw [UInt32.toNat_sub]
  simp only [show (1 : UInt32).toNat = 1 from rfl]
  have := x.toNat_lt
  omega

/-- On `UInt32`, when `x ≠ 0` the wrapping predecessor strictly decreases the
`Nat` value — the standard loop / recursion variant step. -/
theorem UInt32.toNat_sub_one_lt {x : UInt32} (hx : x.toNat ≠ 0) :
    (x - 1).toNat < x.toNat := by
  rw [UInt32.toNat_sub]
  simp only [show (1 : UInt32).toNat = 1 from rfl]
  have := x.toNat_lt
  omega
