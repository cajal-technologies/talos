import Project.Mergesort.SortCostRecurrence

/-!
# Numerical budget for the generated balanced sort

This module defines and bounds a terminating arithmetic budget. The separate
`SortExecutionCost.sort_call_cost` theorem connects it to the generated
recursive call through actual child calls, merge dispatchers, and copy-back.
-/

namespace Project.Mergesort.SortWorkBudget

/-- A conservative budget for the balanced recursion with ten-unit base calls
and local work `54 * n + 127`. -/
def budget (n : Nat) : Nat :=
  if h : n < 2 then 10
  else budget (n / 2) + budget (n - n / 2) + 54 * n + 127
termination_by n
decreasing_by all_goals omega

@[simp] theorem budget_zero : budget 0 = 10 := by
  rw [budget]
  decide

@[simp] theorem budget_one : budget 1 = 10 := by
  rw [budget]
  decide

theorem budget_base {n : Nat} (h : n < 2) : budget n = 10 := by
  rw [budget, dif_pos h]

theorem budget_step {n : Nat} (h : 2 ≤ n) :
    budget n = budget (n / 2) + budget (n - n / 2) + 54 * n + 127 := by
  rw [budget, dif_neg (by omega)]

theorem budget_ge_ten (n : Nat) : 10 ≤ budget n := by
  by_cases h : n < 2
  · rw [budget_base h]
  · rw [budget_step (by omega)]
    omega

theorem budget_monotone : Monotone budget := by
  intro m n hmn
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases hm : m < 2
    · rw [budget_base hm]
      exact budget_ge_ten n
    · have hn : 2 ≤ n := by omega
      rw [budget_step (by omega : 2 ≤ m), budget_step hn]
      have hl : budget (m / 2) ≤ budget (n / 2) :=
        ih (n / 2) (by omega) (by omega)
      have hr : budget (m - m / 2) ≤ budget (n - n / 2) :=
        ih (n - n / 2) (by omega) (by omega)
      omega

/-- The explicit logarithmic upper bound is an arithmetic consequence of the
defined recurrence. It makes no assumption about or claim of execution. -/
theorem budget_log_bound (n : Nat) :
    budget n ≤ 54 * n * Nat.clog 2 (n + 1) + 137 * n + 10 := by
  apply SortCostRecurrence.sort_recurrence_bound budget 54 127
  · intro k hk
    exact (budget_base hk).le
  · intro k hk
    exact (budget_step hk).le

/-- Any numerical cost function obeying these local inequalities is bounded
by the defined budget. The recurrence premise is explicit so this theorem
does not supply an operational composition argument by itself. -/
theorem dominates (cost : Nat → Nat)
    (hbase : ∀ n, n < 2 → cost n ≤ 10)
    (hstep : ∀ n, 2 ≤ n →
      cost n ≤ cost (n / 2) + cost (n - n / 2) + 54 * n + 127)
    (n : Nat) : cost n ≤ budget n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · rw [budget_base hn]
      exact hbase n hn
    · rw [budget_step (by omega)]
      have hl := ih (n / 2) (by omega)
      have hr := ih (n - n / 2) (by omega)
      have hs := hstep n (by omega)
      omega

end Project.Mergesort.SortWorkBudget
