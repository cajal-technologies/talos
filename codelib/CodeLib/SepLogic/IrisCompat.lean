import Iris.ProgramLogic.TotalLifting

/-!
# iris-lean compatibility shims

iris-lean#554 moved `StronglyNormalizing` upstream to
`Relation.StronglyNormalizing` (an abbrev for `Acc (flip step)`) but dropped
its helpers, the no-fork single-expression normalization bridge, and the
no-fork total lifting rule when it merged. CodeLib's adequacy and total
lifting layers still need them, so they are ported here verbatim, in the
upstream namespaces they used to live in.

Everything this file declares lives in `Relation.StronglyNormalizing` or
`Iris.ProgramLogic`, i.e. in namespaces CodeLib does not own; keeping them in
one place makes a clash on the next iris-lean bump easy to spot. They are
candidates to upstream, after which this file should shrink to nothing.

* `Relation.StronglyNormalizing.intro` / `.map`
* `Iris.ProgramLogic.ExprErasedStep`, `LanguageNoFork`,
  `stronglyNormalizing_expr_of_threadPool`
* `Iris.ProgramLogic.twp_lift_step_no_fork`
-/

namespace Relation.StronglyNormalizing

theorem intro {α : Type _} {step : α → α → Prop} {x : α}
    (H : ∀ y, step x y → Relation.StronglyNormalizing step y) :
    Relation.StronglyNormalizing step x :=
  Acc.intro x H

theorem map {α β : Type _} {stepα : α → α → Prop}
    {stepβ : β → β → Prop} (f : β → α)
    (Hlift : ∀ x y, stepβ x y → stepα (f x) (f y))
    {x : β} (H : Relation.StronglyNormalizing stepα (f x)) :
    Relation.StronglyNormalizing stepβ x := by
  unfold Relation.StronglyNormalizing at H ⊢
  generalize hx : f x = z at H
  induction H generalizing x with
  | intro z Hz IH =>
      subst z
      apply Acc.intro
      intro y Hy
      exact IH (f y) (Hlift x y Hy) rfl

end Relation.StronglyNormalizing

namespace Iris.ProgramLogic

export Relation (StronglyNormalizing)

section
open Iris Language Language.Notation

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]

/-- Erased single-expression reduction. -/
def ExprErasedStep : Expr × State → Expr × State → Prop
  | (e₁, σ₁), (e₂, σ₂) =>
      ∃ (κ : List Obs) (efs : List Expr), (e₁, σ₁) -<κ>-> (e₂, σ₂, efs)

/-- A language whose primitive steps do not fork. -/
class LanguageNoFork (Expr State Obs Val : Type _)
    [Language Expr State Obs Val] : Prop where
  no_fork {e₁ e₂ : Expr} {σ₁ σ₂ : State} {κ : List Obs} {efs : List Expr} :
    (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → efs = []

/-- Derive single-expression normalization from thread-pool normalization. -/
theorem stronglyNormalizing_expr_of_threadPool
    [LanguageNoFork Expr State Obs Val] {e : Expr} {σ : State}
    (H : StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([e], σ)) :
    StronglyNormalizing
      (ExprErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      (e, σ) := by
  apply Relation.StronglyNormalizing.map (fun ρ : Expr × State => ([ρ.1], ρ.2)) ?_ H
  rintro ⟨e₁, σ₁⟩ ⟨e₂, σ₂⟩ ⟨κ, efs, Hstep⟩
  have hefs : efs = [] := LanguageNoFork.no_fork Hstep
  subst efs
  exact ⟨κ, .atomic Hstep [] []⟩

end

end Iris.ProgramLogic

namespace Iris.ProgramLogic

open Iris Language Language.Notation BI
open Lean.Parser.Tactic

section
variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors}
variable [ι : @IrisGS_gen hlc Expr Val State Obs Λ GF]
variable {s : Stuckness} {E : CoPset}
variable {e₁ : Expr} {Φ : Val → IProp GF}
/-- Total lifting for steps that fork no threads. Lived in iris-lean's
`TotalLifting` until iris-lean#554 was merged without it; ported verbatim
(modulo the upstream rename `twp_lift_step` → `twp.lift_step`). -/
theorem twp_lift_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗ ⌜eₜ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs nt ∗
        WP e₂ @ s; E [{ Φ }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply twp.lift_step h
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  imod H $$ %κ %e₂ %σ₂ %eₜ %Hstep with ⟨%hκ, %heₜ, Hσ, Hwp⟩
  subst heₜ
  imodintro
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  iframe %hκ Hσ Hwp

end

end Iris.ProgramLogic
