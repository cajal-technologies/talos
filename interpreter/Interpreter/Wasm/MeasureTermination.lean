import Interpreter.Wasm.SmallStep

/-!
# Well-founded termination for the small-step semantics

`SmallStep.TerminatesWith.of_termination_and_partial` splits total correctness
into an Iris partial-correctness proof and a separate termination argument.
This file supplies the termination half in the general, symbolic form: a
measure that strictly decreases along `Step` forces a finite trace to a
configuration with no successor.

The corpus already uses that split: the two consumers of
`of_termination_and_partial` supply their termination halves separately,
`Project.SwapElementsOpt3.opt3_func0_terminates` by unrolling a straight-line
program step by step and
`Project.NumIntegerOpt3.mod3_gcd_smallStep_termination` by a hand-written
strong induction on a decreasing measure. The induction is the part that
recurs: the four loop and recursion examples cited on
`terminatesWith_of_iteration` below each write it out again. This file states
it once.

The development is deliberately split:

* `reachesNormal_of_measure` is pure well-founded reasoning and says only that
  a normal form is reached;
* classifying that normal form as `.done` (rather than `.trapped` or stuck) is
  a separate, semantic obligation, discharged by the caller's invariant.

Keeping them apart matters because `Config.Safe` gives error-freedom, not
progress: a `.running` configuration is not known to step in general, so
"reaches a normal form" and "terminates normally" are genuinely different
statements.
-/

namespace Wasm.SmallStep

variable {α : Type}

/-- A configuration with no successor. `.done` and `.trapped` are normal, and
a `.running` configuration is normal exactly when it is stuck. -/
def Config.Normal (config : Config α) : Prop :=
  ∀ kind next, ¬ Step config kind next

theorem done_normal {values : List Value} {store : MachineStore α} :
    Config.Normal ⟨.done values, store⟩ :=
  fun _ _ => done_terminal

theorem trapped_normal {reason : TrapReason} {store : MachineStore α} :
    Config.Normal ⟨.trapped reason, store⟩ :=
  fun _ _ => trapped_terminal

/-- Determinism lifts to normal forms: a configuration reaches at most one.
`Step` is deterministic (`step_deterministic`), so the trace out of a
configuration is unique up to its length. -/
theorem normal_unique {config final₁ final₂ : Config α} {trace₁ trace₂}
    (h₁ : Steps config trace₁ final₁) (hn₁ : Config.Normal final₁)
    (h₂ : Steps config trace₂ final₂) (hn₂ : Config.Normal final₂) :
    final₁ = final₂ := by
  induction h₁ generalizing trace₂ final₂ with
  | refl config =>
    cases h₂ with
    | refl => rfl
    | cons head _ => exact absurd head (hn₁ _ _)
  | cons head _ ih =>
    cases h₂ with
    | refl => exact absurd head (hn₂ _ _)
    | cons head' tail' =>
      obtain ⟨_, rfl⟩ := step_deterministic head head'
      exact ih hn₁ tail' hn₂

/-- **The termination principle.** A measure into a well-founded order that
strictly decreases along every step forces a finite trace to a normal form.
The invariant `I` is carried along the trace so the caller can use it to
classify the normal form. -/
theorem reachesNormal_of_wf {β : Sort _} {lt : β → β → Prop}
    (hwf : WellFounded lt) (μ : Config α → β) (I : Config α → Prop)
    (hdec : ∀ {config kind next}, I config → Step config kind next →
      lt (μ next) (μ config))
    (hpres : ∀ {config kind next}, I config → Step config kind next → I next)
    (config : Config α) (hI : I config) :
    ∃ trace final, Steps config trace final ∧ Config.Normal final ∧ I final := by
  revert hI
  induction config using (InvImage.wf μ hwf).induction with
  | _ config ih =>
    intro hI
    by_cases hstep : ∃ kind next, Step config kind next
    · obtain ⟨kind, next, hnext⟩ := hstep
      obtain ⟨trace, final, htrace, hnormal, hIfinal⟩ :=
        ih next (hdec hI hnext) (hpres hI hnext)
      exact ⟨kind :: trace, final, .cons hnext htrace, hnormal, hIfinal⟩
    · refine ⟨[], config, .refl config, ?_, hI⟩
      intro kind next hnext
      exact hstep ⟨kind, next, hnext⟩

/-- The `Nat` specialization: loop variants and recursion measures are almost
always natural numbers. -/
theorem reachesNormal_of_measure (μ : Config α → Nat) (I : Config α → Prop)
    (hdec : ∀ {config kind next}, I config → Step config kind next →
      μ next < μ config)
    (hpres : ∀ {config kind next}, I config → Step config kind next → I next)
    (config : Config α) (hI : I config) :
    ∃ trace final, Steps config trace final ∧ Config.Normal final ∧ I final :=
  reachesNormal_of_wf Nat.lt_wfRel.wf μ I hdec hpres config hI

/-- **Total correctness from a variant plus an invariant.** This is the shape a
loop proof has: `I` holds initially and is preserved, `μ` strictly decreases,
and `I` pins the result down once execution comes to rest.

The final hypothesis is where the semantic work lives. It must rule out both
traps and stuck `.running` configurations, which is exactly the obligation
`Config.Safe` does not discharge on its own. -/
theorem terminatesWith_of_measure (μ : Config α → Nat) (I : Config α → Prop)
    {post : List Value → MachineStore α → Prop}
    (hdec : ∀ {config kind next}, I config → Step config kind next →
      μ next < μ config)
    (hpres : ∀ {config kind next}, I config → Step config kind next → I next)
    (hrest : ∀ final : Config α, I final → Config.Normal final →
      ∃ values store, final = ⟨.done values, store⟩ ∧ post values store)
    (config : Config α) (hI : I config) :
    TerminatesWith config post := by
  obtain ⟨trace, final, htrace, hnormal, hIfinal⟩ :=
    reachesNormal_of_measure μ I hdec hpres config hI
  obtain ⟨values, store, rfl, hpost⟩ := hrest final hIfinal hnormal
  exact ⟨trace, values, store, htrace, hpost⟩

/-- Bare termination: the measure alone, with the classification obligation
reduced to "no reachable normal form is running or trapped". Feeds
`TerminatesWith.of_termination_and_partial` directly, leaving the
postcondition entirely to the Iris side. -/
theorem terminates_of_measure (μ : Config α → Nat) (I : Config α → Prop)
    (hdec : ∀ {config kind next}, I config → Step config kind next →
      μ next < μ config)
    (hpres : ∀ {config kind next}, I config → Step config kind next → I next)
    (hrest : ∀ final : Config α, I final → Config.Normal final →
      ∃ values store, final = ⟨.done values, store⟩)
    (config : Config α) (hI : I config) :
    TerminatesWith config (fun _ _ => True) :=
  terminatesWith_of_measure μ I hdec hpres
    (fun final hI hn => by
      obtain ⟨values, store, hEq⟩ := hrest final hI hn
      exact ⟨values, store, hEq, trivial⟩)
    config hI

/-- **Iteration-level termination**, the form loop and recursion proofs
actually take.

`terminatesWith_of_measure` above asks the measure to decrease on *every*
`Step`, which no Wasm loop satisfies: the instructions inside one iteration do
not decrease a trip count, only the back edge does. What a loop proof has
instead is a family of configurations indexed by the loop state, where each
index either finishes or reaches a smaller index after a finite trace.

That is exactly the skeleton currently written out by hand, once per example,
in `Examples/SimpleLoop.lean`, `Examples/Gcd.lean`, `Examples/Factorial.lean`,
and `Examples/EvenOddRec.lean` (each does its own
`Nat.strong_induction_on` and re-derives the same composition). This lemma
factors it.

The postcondition is indexed too, and the recursive case may weaken it, which
is what lets an accumulator be rewritten on the way out (`SimpleLoop` needs
`(x - 1) + (1 + y) = x + y`). -/
theorem terminatesWith_of_iteration {ι : Type _}
    (configs : ι → Config α) (μ : ι → Nat)
    (post : ι → List Value → MachineStore α → Prop)
    (hiterate : ∀ index,
      TerminatesWith (configs index) (post index) ∨
        ∃ next trace, μ next < μ index ∧
          Steps (configs index) trace (configs next) ∧
          ∀ values store, post next values store → post index values store)
    (index : ι) :
    TerminatesWith (configs index) (post index) := by
  suffices key : ∀ bound index, μ index ≤ bound →
      TerminatesWith (configs index) (post index) from
    key (μ index) index (Nat.le_refl _)
  intro bound
  induction bound with
  | zero =>
    intro index _
    rcases hiterate index with hdone | ⟨_, _, hlt, _, _⟩
    · exact hdone
    · omega
  | succ bound ih =>
    intro index hle
    rcases hiterate index with hdone | ⟨next, trace, hlt, htrace, hweaken⟩
    · exact hdone
    · exact TerminatesWith.prependSteps htrace
        ((ih next (by omega)).mono hweaken)

/-- The `while`-shaped specialization: a guard that exits when the variant hits
zero, and an iteration that decreases it. This is literally the case split the
existing examples make (`SimpleLoop` splits on `x = 0`, `Gcd` on the remainder
reaching zero), so porting one of them is a matter of supplying the two
branches and deleting its `Nat.strong_induction_on` block. -/
theorem terminatesWith_of_loop {ι : Type _}
    (configs : ι → Config α) (μ : ι → Nat)
    (post : ι → List Value → MachineStore α → Prop)
    (hexit : ∀ index, μ index = 0 → TerminatesWith (configs index) (post index))
    (hiterate : ∀ index, μ index ≠ 0 →
      ∃ next trace, μ next < μ index ∧
        Steps (configs index) trace (configs next) ∧
        ∀ values store, post next values store → post index values store)
    (index : ι) :
    TerminatesWith (configs index) (post index) :=
  terminatesWith_of_iteration configs μ post
    (fun index =>
      if h : μ index = 0 then Or.inl (hexit index h) else Or.inr (hiterate index h))
    index

/-- The intended composition: a measure carries termination, Iris carries the
postcondition, and `of_termination_and_partial` combines them. -/
theorem totalCorrectness_of_measure_of_partial
    (μ : Config α → Nat) (I : Config α → Prop)
    {post : List Value → MachineStore α → Prop}
    (hdec : ∀ {config kind next}, I config → Step config kind next →
      μ next < μ config)
    (hpres : ∀ {config kind next}, I config → Step config kind next → I next)
    (hrest : ∀ final : Config α, I final → Config.Normal final →
      ∃ values store, final = ⟨.done values, store⟩)
    (config : Config α) (hI : I config)
    (partial_correctness : PartiallyMeets config post) :
    TerminatesWith config post :=
  TerminatesWith.of_termination_and_partial
    (terminates_of_measure μ I hdec hpres hrest config hI)
    partial_correctness

end Wasm.SmallStep
