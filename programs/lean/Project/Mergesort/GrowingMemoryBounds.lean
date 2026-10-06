import Project.Mergesort.ExactWorkAllocators

/-!
# Closed numerical memory-bound checks

These checks expose the input-length formula and its strict arithmetic
acceptance boundary. They concern physical Wasm memory pages, not execution
work or elapsed time. A conservative bound above seventeen pages does not
claim that the corresponding execution attains that bound.
-/

namespace Project.Mergesort.GrowingMemoryBounds

open Project.Mergesort.Representations Project.Mergesort.MemoryBounds
open Project.Mergesort.ExactWorkAllocators

/-- The retained-input and two-work-array frontier for a nonempty word list. -/
theorem workArraysFrontierBound_nonempty (input : List UInt32)
    (hpositive : 0 < input.length) :
    workArraysFrontierBound (serialize input).length = 1049542 + 24 * input.length := by
  simp only [serialize_length]
  unfold workArraysFrontierBound inputFrontierBound heapBase
  change 1049536 + 2 * max (2 * (4 * input.length)) 8 +
    2 * (4 * input.length) + 6 = _
  omega

/-- The public page formula is valid for every input, including the empty case. -/
theorem programPageBound_public_formula (input : List UInt32) :
    programPageBound input =
      max 17 ((1049542 + 24 * input.length + 65535) / 65536) := by
  by_cases hzero : input.length = 0
  · unfold programPageBound workArraysFrontierBound inputFrontierBound heapBase
    simp only [serialize_length, hzero]
    decide
  · have hpositive : 0 < input.length := by omega
    unfold programPageBound
    rw [workArraysFrontierBound_nonempty input hpositive]

/-- The empty invocation's conservative upper bound remains seventeen pages. -/
theorem programPageBound_empty : programPageBound [] = 17 := by
  rw [programPageBound_public_formula]
  decide

/-- The existing arithmetic fit predicate has an exact closed word-count range.
This identifies the range of this conservative predicate, not the largest input
for which the program could execute successfully. -/
theorem workArraysFit_iff_word_count (input : List UInt32) :
    WorkArraysFit (serialize input).length ↔ input.length ≤ 89434754 := by
  unfold WorkArraysFit
  by_cases hzero : input.length = 0
  · unfold workArraysFrontierBound inputFrontierBound heapBase
    simp only [serialize_length, hzero]
    decide
  · rw [workArraysFrontierBound_nonempty input (by omega)]
    omega

/-- A closed input predicate supplies the work-array fit premise. -/
theorem workArraysFit_of_word_count (input : List UInt32)
    (hbound : input.length ≤ 89434754) :
    WorkArraysFit (serialize input).length :=
  (workArraysFit_iff_word_count input).2 hbound

/-- The last accepted word count is admitted by the strict signed-end budget. -/
theorem workArraysFit_last_accepted (input : List UInt32)
    (hlength : input.length = 89434754) :
    WorkArraysFit (serialize input).length := by
  apply workArraysFit_of_word_count
  omega

/-- The next word count violates this conservative arithmetic budget. -/
theorem workArraysFit_first_rejected (input : List UInt32)
    (hlength : input.length = 89434755) :
    ¬ WorkArraysFit (serialize input).length := by
  rw [workArraysFit_iff_word_count, hlength]
  decide

/-- The established no-growth range has conservative upper bound seventeen. -/
theorem programPageBound_at_2690 (input : List UInt32)
    (hlength : input.length = 2690) : programPageBound input = 17 := by
  rw [programPageBound_public_formula, hlength]
  decide

/-- The next word increases the conservative upper bound to eighteen. -/
theorem programPageBound_at_2691 (input : List UInt32)
    (hlength : input.length = 2691) : programPageBound input = 18 := by
  rw [programPageBound_public_formula, hlength]
  decide

/-- An 8192-word input has a twenty-page conservative upper bound. -/
theorem programPageBound_at_8192 (input : List UInt32)
    (hlength : input.length = 8192) : programPageBound input = 20 := by
  rw [programPageBound_public_formula, hlength]
  decide

/-- The last admitted word count still fits the unchanged 65536-page cap. -/
theorem programPageBound_last_accepted (input : List UInt32)
    (hlength : input.length = 89434754) : programPageBound input = 32768 := by
  rw [programPageBound_public_formula, hlength]
  decide

end Project.Mergesort.GrowingMemoryBounds
