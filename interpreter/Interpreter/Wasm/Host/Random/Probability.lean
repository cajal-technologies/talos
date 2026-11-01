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
    Oracle.ofPrefix bytes index = bytes ⟨index, hindex⟩ := by simp [Oracle.ofPrefix, hindex]

/-- Probability of an event under a distribution. Mathlib (≥ 2026-10) represents
finite uniform distributions as measures (`Measure.uniformOfFinset`). -/
noncomputable def probability [MeasurableSpace α] (distribution : Measure α) (event : Set α) :
    ℝ≥0∞ :=
  distribution event

/-- A uniformly sampled oracle byte. -/
noncomputable def uniformByte : Measure Byte := Measure.uniformOfFinset Finset.univ

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
  rw [probability, uniformByte, Measure.uniformOfFinset_apply]
  have hcard : (Finset.univ.filter (fun byte : Byte => byte.val < 128)).card = 128 := by
    have h := lowHalf_card
    rwa [Fintype.card_subtype] at h
  simp only [Set.mem_ofPred_eq, hcard, Finset.card_univ, Fintype.card_fin]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  norm_num

end Wasm.Random
