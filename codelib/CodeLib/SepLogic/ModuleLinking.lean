import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmWP

namespace Wasm.SepLogic.ModuleLinking
open Iris

variable [inst : WasmHeapGS]

/-! # iProp module linking (Iris-Wasm §2.2)

`FuncSpec.pre` and `FuncSpec.post` are `IProp WasmHeapGF` ownership predicates,
NOT Prop assertions about store values. There is **no** explicit `frame` field.

The frame rule is automatic: `funcSatisfies` universally quantifies over any
additional caller resource `R : IProp WasmHeapGF`. The implementation only needs
to reason about `pre` and `post`; `R` carries through automatically via
`BI.sep_assoc`.

Note on `∗` syntax: in iris-lean, the separating conjunction `∗` is defined via
`iprop(...)` macro expansion (see Iris.BI.BIBase). It is NOT a standalone infix
operator — it only elaborates inside `iprop(P ∗ Q)`, `iprop%(P ∗ Q)`, or the
`P ⊢ Q` / `P ⊣⊢ Q` macros (which wrap operands in `iprop`). -/

/-- iProp function specification. `pre st` and `post st' vs` are ownership
    assertions in the Iris ghost heap — e.g. `pointsTo_u64 ptr v`.
    No `frame` field is needed: the separation conjunction `∗` provides it. -/
structure FuncSpec where
  pre  : Store Unit → IProp WasmHeapGF
  post : Store Unit → List Value → IProp WasmHeapGF

/-- `funcSatisfies m idx S`: function `idx` of module `m` satisfies spec `S`.

    For any caller frame `R` and heap state `σ` where `S.pre st ∗ R` holds,
    calling `idx` terminates and the resulting heap satisfies `S.post st' vs ∗ R`.

    The universal quantification over `R` is the separation-logic frame rule
    baked into the spec: the function guarantees its postcondition AND preserves
    all additional resources the caller already owns. -/
def funcSatisfies (m : Module) (idx : Nat) (S : FuncSpec) : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (args : List Value)
    (R : IProp WasmHeapGF) (σ : WasmHeapMap (Option UInt8)),
    (genHeapInterp σ ⊢ S.pre st ∗ R) →
    TerminatesWith env m idx st args
      (fun st' vs => ∃ σ' : WasmHeapMap (Option UInt8),
        genHeapInterp σ' ⊢ S.post st' vs ∗ R)

-- Helper: frame-wrapped spec. Must use `iprop%` since `∗` is only available
-- inside the `iprop(...)` macro expansion (not as a standalone term operator).
-- @[reducible] ensures the projection `(framedSpec S R).pre st` is unfolded
-- to `BIBase.sep (S.pre st) R` during type-checking in `frame_rule`.
@[reducible] private def framedSpec (S : FuncSpec) (R : IProp WasmHeapGF) : FuncSpec where
  pre  st     := iprop% S.pre st ∗ R
  post st' vs := iprop% S.post st' vs ∗ R

/-- Frame rule: if `S` is satisfied, then `{S.pre ∗ R}` / `{S.post ∗ R}` is also
    satisfied for any additional frame `R`.

    Proof: reassociate `(pre ∗ R) ∗ R' ↔ pre ∗ (R ∗ R')` using `BI.sep_assoc`,
    apply `funcSatisfies` with compound frame `R ∗ R'`, then reassociate back. -/
theorem frame_rule
    {m : Module} {idx : Nat} {S : FuncSpec} (R : IProp WasmHeapGF)
    (h : funcSatisfies m idx S) :
    funcSatisfies m idx (framedSpec S R) := by
  intro env st args R' σ hpre
  -- hpre : genHeapInterp σ ⊢ (S.pre st ∗ R) ∗ R'
  -- Apply h with compound frame (R ∗ R') using BI.sep_assoc.mp.
  -- Note: `∗` in term position requires `iprop%` wrapper (Iris elaboration rule).
  have h1 : genHeapInterp σ ⊢ S.pre st ∗ (iprop%(R ∗ R')) := hpre.trans BI.sep_assoc.mp
  obtain ⟨N, hN⟩ := h env st args (iprop%(R ∗ R')) σ h1
  refine ⟨N, fun fuel hle => ?_⟩
  obtain ⟨vs, st', hrun, σ', hpost⟩ := hN fuel hle
  -- hpost : genHeapInterp σ' ⊢ S.post st' vs ∗ (R ∗ R')
  exact ⟨vs, st', hrun, σ', hpost.trans BI.sep_assoc.symm.mp⟩

/-- Module linking (Iris-Wasm §3.1 with iProp specs).

    If `m` exports `idx` satisfying `S`, and `P_correct` holds for any module
    satisfying `S`, then `P_correct m` holds — the client never sees the body. -/
theorem link_modules
    {m : Module} {idx : Nat} {S : FuncSpec}
    {P_correct : FuncSpec → Prop}
    (h_export : funcSatisfies m idx S)
    (h_import : ∀ S', funcSatisfies m idx S' → P_correct S') :
    P_correct S :=
  h_import S h_export

end Wasm.SepLogic.ModuleLinking
