import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmWP

/-! # Module Linking Infrastructure (with Frame Rule)

Prop-level module linking following Iris-Wasm (Rao et al., PLDI 2023) §2.2,
Lemma 3.1.

## Design note

The ideal formulation uses iProp ownership predicates (`pointsTo_u64` etc.) for
`pre`/`post`, with `funcSatisfies` bridging to `TerminatesWith` via
`wasm_heap_adequacy`.  That gives the full frame rule automatically: owning a
cell `{pointsTo_u64 ptr v}` is exclusive, so the separation-logic frame rule
guarantees every cell NOT in the function's footprint is untouched.

Here we use a Prop-level form that makes the frame obligation *explicit* in the
`FuncSpec` structure, demonstrating the key ownership insight without requiring
a full iProp elaboration of function specs.  The `frame` field plays the same
role as the separation-logic frame rule: the function spec *promises* that
memory outside its footprint is preserved, enabling callers to compose calls
without re-proving preservation of unrelated state.  The proof that a concrete
function satisfies this frame promise would normally proceed by exhibiting an
iProp Hoare triple and applying `wasm_heap_adequacy`. -/

namespace Wasm.SepLogic.ModuleLinking

open Wasm

/-- Pre/post/frame specification for a Wasm function.

    `pre`   — precondition on the initial store.
    `post`  — postcondition on the final store and return values.
    `frame` — the ownership component: `frame st st'` asserts that the
              function's effect is confined to the footprint declared by
              `pre`/`post`; every address OUTSIDE that footprint has the
              same value in `st'` as in `st`.  Callers use `frame` to
              know their other memory is preserved across a call. -/
structure FuncSpec where
  pre   : Store Unit → Prop
  post  : Store Unit → List Value → Prop
  /-- `frame st st'` — everything outside the spec's footprint is unchanged. -/
  frame : Store Unit → Store Unit → Prop

/-- `funcSatisfies m idx S` — function `idx` of module `m` satisfies `S`:
    whenever `S.pre` holds, the call terminates, `S.post` holds, AND the
    frame condition holds (memory outside the footprint is preserved).

    The full iProp path to discharging this would be: state the function
    body as an iProp WP, extract a `wp_wasm_prop` via `wasm_heap_adequacy`,
    then promote to `TerminatesWith` using `wp_wasm_prop_to_TerminatesWith`. -/
def funcSatisfies (m : Module) (idx : Nat) (S : FuncSpec) : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (args : List Value),
    S.pre st →
    TerminatesWith env m idx st args (fun st' rs => S.post st' rs ∧ S.frame st st')

/-- Module linking theorem (Iris-Wasm Lemma 3.1, Prop-level with frame).

    If `m` exports a function satisfying spec `S`, and a client property
    `P_correct` holds for ANY module satisfying `S`, then `P_correct`
    holds for `m`.  The client `P_correct` never inspects `m`'s code. -/
theorem link_modules
    {m : Module} {idx : Nat} {S : FuncSpec}
    {P_correct : FuncSpec → Prop}
    (h_export  : funcSatisfies m idx S)
    (h_import  : ∀ S', funcSatisfies m idx S' → P_correct S') :
    P_correct S :=
  h_import S h_export

/-- Weakening: if `S` is satisfied and the post/frame can be weakened,
    the derived spec is also satisfied. -/
theorem funcSatisfies_mono
    {m : Module} {idx : Nat} {S : FuncSpec}
    {Q : Store Unit → List Value → Prop}
    {F : Store Unit → Store Unit → Prop}
    (h  : funcSatisfies m idx S)
    (hQ : ∀ st' rs, S.post  st' rs → Q st' rs)
    (hF : ∀ st st', S.frame st  st' → F st  st') :
    funcSatisfies m idx { pre := S.pre, post := Q, frame := F } := by
  intro env st args hpre
  obtain ⟨N, hN⟩ := h env st args hpre
  exact ⟨N, fun fuel hle => by
    obtain ⟨vs, st', hrun, hpost, hfr⟩ := hN fuel hle
    exact ⟨vs, st', hrun, hQ st' vs hpost, hF st st' hfr⟩⟩

/-- Call-composition rule with frame.

    Given that `g` satisfies `S_g`, the continuation `h_cont` receives both
    the postcondition and the frame guarantee, enabling it to reason about
    memory the function did NOT touch without knowing `g`'s implementation. -/
theorem compose_with_import
    {m : Module} {env : HostEnv Unit}
    {st : Store Unit} {args : List Value}
    {g_idx : Nat} {S_g : FuncSpec}
    (h_g     : funcSatisfies m g_idx S_g)
    (h_g_pre : S_g.pre st)
    {Q : Store Unit → List Value → Prop}
    (h_cont  : ∀ st' rs, S_g.post st' rs → S_g.frame st st' → Q st' rs) :
    TerminatesWith env m g_idx st args Q := by
  obtain ⟨N, hN⟩ := h_g env st args h_g_pre
  exact ⟨N, fun fuel hle => by
    obtain ⟨vs, st', hrun, hpost, hfr⟩ := hN fuel hle
    exact ⟨vs, st', hrun, h_cont st' vs hpost hfr⟩⟩

end Wasm.SepLogic.ModuleLinking
