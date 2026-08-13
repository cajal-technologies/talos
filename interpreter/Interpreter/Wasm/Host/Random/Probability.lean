import Interpreter.Wasm.Host.Random
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

/-!
# Finite probability models for the entropy oracle

A probabilistic theorem chooses a finite oracle prefix uniformly and evaluates
the otherwise deterministic Wasm machine with that prefix.  A program proof
must also establish that execution consumes no more than the sampled prefix;
`Oracle.ofPrefix` deliberately uses zero beyond it so accidental overuse is
visible in the functional proof rather than receiving unstated randomness.

This finite model supports exact probabilities for bounded executions.  An
IID product measure on infinite oracles can be added later without changing
the executable host or its pathwise contract.
-/

namespace Wasm.Random

open MeasureTheory
open scoped ENNReal

/-- A finite prefix containing exactly `count` oracle bytes. -/
abbrev Prefix (count : Nat) := Fin count → Byte

/-- Complete a finite prefix to an executable oracle with an explicit zero
fallback.  Probability claims using this completion must prove that the
program's final cursor is at most `count`. -/
def Oracle.ofPrefix {count : Nat} (bytes : Prefix count) : Oracle :=
  fun index => if h : index < count then bytes ⟨index, h⟩ else 0

@[simp]
theorem Oracle.ofPrefix_apply {count index : Nat} (bytes : Prefix count)
    (hindex : index < count) :
    Oracle.ofPrefix bytes index = bytes ⟨index, hindex⟩ := by
  simp [Oracle.ofPrefix, hindex]

/-- The uniform distribution over all byte strings of length `count`. -/
noncomputable def uniformPrefix (count : Nat) : PMF (Prefix count) :=
  PMF.uniformOfFintype (Prefix count)

/-- Lift any deterministic oracle-parametric evaluator—such as a projection
of the fuel-bounded Wasm runner—to a discrete distribution of results. -/
noncomputable def evalWithUniformPrefix (count : Nat)
    (eval : Oracle → β) : PMF β :=
  (uniformPrefix count).map fun bytes => eval (Oracle.ofPrefix bytes)

/-- Probability of an event under a discrete distribution. -/
noncomputable def probability (distribution : PMF α) (event : Set α) :
    ℝ≥0∞ :=
  distribution.toOuterMeasure event

/-- Uniform-prefix events reduce to finite counting.  This is the main bridge
for exact probability theorems about bounded randomized programs. -/
theorem uniformPrefix_probability (count : Nat)
    (event : Set (Prefix count)) [Fintype event] :
    probability (uniformPrefix count) event =
      Fintype.card event / Fintype.card (Prefix count) := by
  exact PMF.toOuterMeasure_uniformOfFintype_apply event

/-- A uniformly sampled oracle byte. -/
noncomputable def uniformByte : PMF Byte := PMF.uniformOfFintype Byte

/-- Bytes below 128 are canonically the elements of `Fin 128`. -/
def lowHalfEquiv : { byte : Byte // byte.val < 128 } ≃ Fin 128 where
  toFun byte := ⟨byte.val, byte.property⟩
  invFun byte := ⟨⟨byte.val, by omega⟩, byte.isLt⟩
  left_inv byte := by rfl
  right_inv byte := by rfl

/-- Exactly half of all bytes have a numeric value below 128. -/
theorem lowHalf_card :
    Fintype.card { byte : Byte // byte.val < 128 } = 128 := by
  rw [Fintype.card_congr lowHalfEquiv]
  simp

/-- A one-byte threshold test is a fair coin. -/
theorem uniformByte_lowHalf_probability :
    probability uniformByte { byte | byte.val < 128 } =
      (1 / 2 : ℝ≥0∞) := by
  rw [probability]
  change (PMF.uniformOfFintype Byte).toOuterMeasure
      { byte | byte.val < 128 } = 1 / 2
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  change (Fintype.card { byte : Byte // byte.val < 128 } : ℝ≥0∞) /
      (Fintype.card Byte : ℝ≥0∞) = 1 / 2
  rw [lowHalf_card]
  have half : (128 : ℝ≥0∞) / 256 = 1 / 2 := by
    apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2
    norm_num
  rw [Fintype.card_fin]
  exact half

end Wasm.Random
