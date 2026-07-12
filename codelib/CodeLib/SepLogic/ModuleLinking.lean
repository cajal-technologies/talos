import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmWP

namespace Wasm.SepLogic.ModuleLinking
open Iris

variable [inst : WasmHeapGS]

/-! # iProp module linking (standard Iris-Wasm §2.2 pattern)

`pre` and `post` are `IProp WasmHeapGF` ownership predicates, NOT Prop
assertions about store values.

Standard form: `funcSatisfies` has **no** baked-in frame `R`. The frame rule
(`frame_rule`) is a separate theorem that lifts a frame-free spec to the framed
spec `{pre ∗ R}` / `{post ∗ R}` for any additional caller resource `R`, using
the BI wand-star adjunction plus WP monotonicity.

Note on `∗`/`-∗` syntax: these elaborate inside `⊢`/`⊣⊢` macros or
`iprop%(...)`. -/

/-- `funcSatisfies m idx pre post`: function at local index `idx` of `m`
    satisfies the Hoare-style spec `{pre} / {post}` at the iProp level.

    There exists a function body `f` at `m.funcs[idx]` such that for any heap
    where `pre st` holds, the WP for `f`'s body yields `post`. -/
def funcSatisfies
    (m : Module) (idx : Nat)
    (pre  : Store Unit → IProp WasmHeapGF)
    (post : Store Unit → List Value → IProp WasmHeapGF) : Prop :=
  ∃ (f : Wasm.Function),
    m.funcs[idx]? = some f ∧
    ∀ (env : HostEnv Unit) (st : Store Unit) (args : List Value),
      ⊢ pre st -∗
          wp_wasm_iProp m st (f.toLocals args) f.body env
            (fun st' vs => post st' vs)

/-- Frame rule: lift a frame-free spec `{pre} / {post}` to the framed spec
    `{pre ∗ R} / {post ∗ R}` for any additional caller resource `R`.

    Proof sketch: from `⊢ pre -∗ wp Φ`, the BI law
    `(P -∗ Q) ⊢ (P ∗ R -∗ Q ∗ R)` gives `⊢ (pre ∗ R) -∗ (wp Φ ∗ R)`.
    WP monotonicity then lifts `wp Φ ∗ R ⊢ wp (Φ ∗ R)`.
    Full proof deferred: requires WP-level frame theorem. -/
theorem frame_rule
    {m : Module} {idx : Nat}
    {pre  : Store Unit → IProp WasmHeapGF}
    {post : Store Unit → List Value → IProp WasmHeapGF}
    (R : IProp WasmHeapGF)
    (h : funcSatisfies m idx pre post) :
    funcSatisfies m idx
      (fun st     => iprop% pre st ∗ R)
      (fun st' vs => iprop% post st' vs ∗ R) := by
  obtain ⟨f, hf, hspec⟩ := h
  refine ⟨f, hf, fun env st args => ?_⟩
  -- hspec env st args : ⊢ pre st -∗ wp_wasm_iProp ... (fun st' vs => post st' vs)
  -- Goal: ⊢ (pre st ∗ R) -∗ wp_wasm_iProp ... (fun st' vs => post st' vs ∗ R)
  -- BI chain: sep_mono_left (wand_entails hspec) : pre st ∗ R ⊢ wp ... post ∗ R
  --           wp_wasm_iProp_frame_right             : wp ... post ∗ R ⊢ wp ... (post ∗ R)
  exact BI.entails_wand
    ((BI.sep_mono_left (BI.wand_entails (hspec env st args))).trans
      wp_wasm_iProp_frame_right)

end Wasm.SepLogic.ModuleLinking
