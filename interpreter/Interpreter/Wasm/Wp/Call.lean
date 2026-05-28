import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Semantics.Lemmas

/-! ### Function specifications and `call`.

    `FuncSpec m id Pre Post` says: given args satisfying `Pre`, calling
    function `id` of module `m` terminates with a success result whose values
    satisfy `Post`. Mutually-recursive specs share a single measure encoded
    inside `Pre` (e.g., `Pre args ↔ args = [n] ∧ n < bound`). -/

namespace Wasm

def FuncSpec (m : Module) (id : Nat)
    (Pre : List Value → Prop) (Post : Store → List Value → Prop) : Prop :=
  ∀ args, Pre args → ∀ initial : Store,
    ∃ N, ∀ fuel ≥ N, ∃ vs st, run fuel m id initial args = .Success vs st ∧ Post st vs

theorem wp_call_cons {id : Nat} {Pre : List Value → Prop} {Post : Store → List Value → Prop}
    (spec : FuncSpec m id Pre Post)
    (hPre : Pre s.values)
    (hPost : ∀ st' vs, Post st' vs → wp m rest Q st' { s with values := vs }) :
    wp m (.call id :: rest) Q st s := by
  unfold wp
  unfold FuncSpec at spec
  obtain ⟨Ns, hNs⟩ := spec s.values hPre st
  obtain ⟨vs, st', hRun, hPost_vs⟩ := hNs Ns le_rfl
  have hRun_ne : run Ns m id st s.values ≠ .OutOfFuel := by rw [hRun]; intro h; cases h
  have hwp_rest := hPost st' vs hPost_vs
  unfold wp at hwp_rest
  obtain ⟨Nr, hNr⟩ := hwp_rest
  refine ⟨max (Ns + 1) (Nr + 1), fun fuel hfuel => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hRun_f : run f m id st s.values = .Success vs st' := by
    rw [run_fuel_mono (by omega : f ≥ Ns) hRun_ne]; exact hRun
  rw [exec_call_cons, hRun_f]
  exact hNr (f + 1) (by omega)

/-- Bridge from `wp` of a function body to `FuncSpec`. The body sees locals
    built from `args.take f.numParams` reversed (so local 0 is the first
    argument), and the `Post` is checked on its `Fallthrough`/`Return`
    outcomes after taking the top `f.results.length` values and appending the
    caller-remainder — matching `run`'s standard Wasm calling convention. -/
theorem FuncSpec.of_wp_body
    {m : Module} {id : Nat} {f : Function} {Pre : List Value → Prop} {Post : Store → List Value → Prop}
    (hf : m.funcs[id]? = some f)
    (h : ∀ args, Pre args → ∀ initial : Store,
      wp m f.body
        (fun c => match c with
          | .Fallthrough st' s' =>
              Post st' (s'.values.take f.results.length ++ args.drop f.numParams)
          | .Return st' vs      =>
              Post st' (vs.take f.results.length ++ args.drop f.numParams)
          | _                   => False)
        initial (f.toLocals (args.take f.numParams).reverse)) :
    FuncSpec m id Pre Post := by
  intro args hPre initial
  have hwp := h args hPre initial
  unfold wp at hwp
  obtain ⟨N, hN⟩ := hwp
  refine ⟨N, fun fuel hfuel => ?_⟩
  have hQ := hN fuel hfuel
  rw [run_eq]
  simp only [hf]
  cases hexec : exec fuel m initial (f.toLocals (args.take f.numParams).reverse) f.body with
  | Fallthrough st' s' =>
    rw [hexec] at hQ
    exact ⟨s'.values.take f.results.length ++ args.drop f.numParams, st', rfl, hQ⟩
  | Return st' vs =>
    rw [hexec] at hQ
    exact ⟨vs.take f.results.length ++ args.drop f.numParams, st', rfl, hQ⟩
  | Break n st' s' => rw [hexec] at hQ; exact hQ.elim
  | Trap msg => rw [hexec] at hQ; exact hQ.elim
  | Invalid msg => rw [hexec] at hQ; exact hQ.elim
  | OutOfFuel => rw [hexec] at hQ; exact hQ.elim

end Wasm
