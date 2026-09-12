import Project.Mergesort.SortProof
import CodeLib.SepLogic.CostedLoop
import Mathlib.Data.Nat.Log

/-!
# Arithmetic for the generated balanced recursion

`SortProof.twp_sort` splits the input into lengths `n / 2` and `n - n / 2`.
This module solves the associated numerical work recurrence under explicit
local-cost hypotheses. `SortExecutionCost.sort_call_log_cost` supplies the
operational recursive-call bound, and `ExportWorkProof.named_export_work`
composes it into the complete export budget. Total WP alone supplies neither.
-/

namespace Project.Mergesort.SortCostRecurrence

open Wasm Wasm.SmallStep
open Project.Mergesort.SortProof

private def baseTrace : List StepKind :=
  [.instruction (.call 5), .instruction (.block 0 0 sortBlock1),
    .instruction (.block 0 0 sortBlock2), .instruction (.block 0 0 sortBlock3),
    .instruction (.block 0 0 sortBlock4), .instruction (.localGet 1),
    .instruction (.const 2), .instruction .ltU, .instruction (.br_if 0),
    .administrative .returnFromCall]

/-- The actual generated call 5 costs exactly ten transitions for zero or one
word and preserves the complete store and caller context. It touches no memory;
the numerical base coefficient is measured by these actual semantic steps. -/
theorem sort_base_call_cost {α : Type} (store : MachineStore α)
    (source scratch length scratchLength : UInt32)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hbase : length < 2)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length = 10 ∧
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨{ callerLocals with values := (.i32 scratchLength :: .i32 scratch ::
            .i32 length :: .i32 source :: stack) },
          .call 5 :: code, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩, store⟩ 10 := by
  have execution : Steps
      ⟨.running ⟨{ callerLocals with values := (.i32 scratchLength :: .i32 scratch ::
          .i32 length :: .i32 source :: stack) },
        .call 5 :: code, arity, remainder, controls, calls⟩, store⟩ baseTrace
      ⟨.running ⟨{ callerLocals with values := stack },
        code, arity, remainder, controls, calls⟩, store⟩ := by
    unfold baseTrace
    apply Steps.cons (Step.call (fn := func2Def)
      (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
    simp only [func2Def, func2, Function.toLocals, Function.numParams]
    apply Steps.cons Step.block
    apply Steps.cons Step.block
    apply Steps.cons Step.block
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet (by rfl))
    apply Steps.cons Step.const
    apply Steps.cons (Step.ltU (result := 1) (by simp [hbase]))
    apply Steps.cons (Step.brIf (by decide) (by rfl))
    exact Steps.single (Step.returnFromCallExplicit rfl)
  refine ⟨baseTrace, rfl, execution.with_unit_cost ?_⟩
  intro before kind after member
  simp only [baseTrace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A balanced recursion with linear local work has at most `depth` charged
levels above its leaves. The extra `node` on the left accounts for the fact
that a full binary recursion on `n` nonempty leaves has `n - 1` internal nodes.
No monotonicity assumption on `cost` is needed. -/
theorem balanced_bound_of_capacity (cost : Nat → Nat) (word node leaf : Nat)
    (hleaf : cost 1 ≤ leaf)
    (hstep : ∀ n, 2 ≤ n →
      cost n ≤ cost (n / 2) + cost (n - n / 2) + word * n + node)
    (depth n : Nat) (hpositive : 0 < n) (hcapacity : n ≤ 2 ^ depth) :
    cost n + node ≤ word * n * depth + (node + leaf) * n := by
  induction depth generalizing n with
  | zero =>
    simp only [Nat.pow_zero] at hcapacity
    have hn : n = 1 := by omega
    subst n
    simp only [Nat.mul_one, Nat.mul_zero, Nat.zero_add]
    omega
  | succ depth ih =>
    by_cases hone : n = 1
    · subst n
      simp only [Nat.mul_one]
      omega
    have htwo : 2 ≤ n := by omega
    have hleft : 0 < n / 2 := by omega
    have hright : 0 < n - n / 2 := by omega
    have hsplit : n / 2 + (n - n / 2) = n := by omega
    rw [Nat.pow_succ] at hcapacity
    have hlcap : n / 2 ≤ 2 ^ depth := by omega
    have hrcap : n - n / 2 ≤ 2 ^ depth := by omega
    have hl := ih (n / 2) hleft hlcap
    have hr := ih (n - n / 2) hright hrcap
    have hlocal := hstep n htwo
    calc
      cost n + node ≤ (cost (n / 2) + node) +
          (cost (n - n / 2) + node) + word * n := by omega
      _ ≤ (word * (n / 2) * depth + (node + leaf) * (n / 2)) +
          (word * (n - n / 2) * depth + (node + leaf) * (n - n / 2)) +
          word * n := Nat.add_le_add_right (Nat.add_le_add hl hr) _
      _ = word * n * (depth + 1) + (node + leaf) * n := by
        calc
          _ = word * (n / 2 + (n - n / 2)) * depth +
              (node + leaf) * (n / 2 + (n - n / 2)) + word * n := by ring
          _ = _ := by rw [hsplit]; ring

/-- Explicit logarithmic polynomial from local recurrence coefficients.
`Nat.clog 2 (n + 1)` is the natural-number ceiling of `log₂(n + 1)`.
The zero-input cost is separate because it has no positive leaf.

The recurrence hypotheses describe numerical costs. The compiled-sort
connection is proved by `SortExecutionCost.sort_call_log_cost`, using actual
costed call segments alongside the functional resources from `SortProof.twp_sort`. -/
theorem balanced_recurrence_bound (cost : Nat → Nat)
    (word node leaf empty : Nat)
    (hempty : cost 0 ≤ empty) (hleaf : cost 1 ≤ leaf)
    (hstep : ∀ n, 2 ≤ n →
      cost n ≤ cost (n / 2) + cost (n - n / 2) + word * n + node)
    (n : Nat) :
    cost n ≤ word * n * Nat.clog 2 (n + 1) + (node + leaf) * n + empty := by
  by_cases zero : n = 0
  · subst n
    simpa using hempty
  have bound := balanced_bound_of_capacity cost word node leaf hleaf hstep
    (Nat.clog 2 (n + 1)) n (by omega)
    ((Nat.le_succ n).trans (Nat.le_pow_clog (by decide) (n + 1)))
  omega

/-- Specialization to the ten-unit base segments certified by
`sort_base_call_cost`. The caller supplies the connection to those segments and
the recursive local-work bound. The coefficients `word` and `node` are generic;
`SortExecutionCost.sort_call_log_cost` provides a concrete compiled-sort bound. -/
theorem sort_recurrence_bound (cost : Nat → Nat) (word node : Nat)
    (hbase : ∀ n, n < 2 → cost n ≤ 10)
    (hstep : ∀ n, 2 ≤ n →
      cost n ≤ cost (n / 2) + cost (n - n / 2) + word * n + node)
    (n : Nat) :
    cost n ≤ word * n * Nat.clog 2 (n + 1) + (node + 10) * n + 10 :=
  balanced_recurrence_bound cost word node 10 10
    (hbase 0 (by decide)) (hbase 1 (by decide)) hstep n

end Project.Mergesort.SortCostRecurrence
