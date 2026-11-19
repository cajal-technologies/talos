import Interpreter.Wasm

/-!
# Entry bridges: fuel-free `TerminatesWith` spec ⇒ `wp` goal on the body

Single-step bridges from a fuel-free `TerminatesWith` spec down to a `wp`
goal on the function body. They fuse `FuncSpec.to_TerminatesWith` and
`FuncSpec.of_wp_body` and specialize to a fixed argument list, so corpus
proofs don't have to name `Pre`/`Post` or run the `FuncSpec` plumbing by
hand.

* `of_wp_entry` — store-parametric (body proof holds for every initial store).
* `of_wp_entry_for` — store-specific (body proof depends on the concrete store,
  e.g. memory bounds).
-/

namespace Wasm

/-- Discharge `TerminatesWith m id initial args P` by proving the `wp` of
the function body (parametric in the initial store). Locals are built from
`args.take f.numParams` reversed (Wasm calling convention), and the
post-condition is checked on `Fallthrough`/`Return` after taking the top
`f.results.length` values and appending the caller-remainder. -/
theorem TerminatesWith.of_wp_entry {env : HostEnv α}
    {m : Module} {id : Nat} {f : Function}
    {initial : Store α} {args : List Value} {P : Store α → List Value → Prop}
    (hf : m.funcs[id - m.imports.length]? = some f)
    (h : ∀ initial : Store α,
      wp m f.body
        (fun c => match c with
          | .Fallthrough st' s' =>
              P st' (s'.values.take f.results.length ++ args.drop f.numParams)
          | .Return st' vs      =>
              P st' (vs.take f.results.length ++ args.drop f.numParams)
          | _                   => False)
        initial (f.toLocals (args.take f.numParams).reverse) env)
    (hImp : m.imports[id]? = none := by rfl) :
    TerminatesWith env m id initial args P := by
  refine FuncSpec.to_TerminatesWith (Pre := (· = args))
    (FuncSpec.of_wp_body hf ?_ hImp) rfl
  rintro _ rfl initial'; exact h initial'

/-- Variant of `of_wp_entry` for a specific store rather than all stores.
Use when the function body's correctness depends on properties of the
initial store (e.g., memory bounds). -/
theorem TerminatesWith.of_wp_entry_for {env : HostEnv α}
    {m : Module} {id : Nat} {f : Function}
    {initial : Store α} {args : List Value} {P : Store α → List Value → Prop}
    (hf : m.funcs[id - m.imports.length]? = some f)
    (h : wp m f.body
        (fun c => match c with
          | .Fallthrough st' s' =>
              P st' (s'.values.take f.results.length ++ args.drop f.numParams)
          | .Return st' vs      =>
              P st' (vs.take f.results.length ++ args.drop f.numParams)
          | _                   => False)
        initial (f.toLocals (args.take f.numParams).reverse) env)
    (hImp : m.imports[id]? = none := by rfl) :
    TerminatesWith env m id initial args P := by
  unfold TerminatesWith
  unfold wp at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hfuel => ?_⟩
  have hQ := hN fuel hfuel
  rw [run_eq hImp]; simp only [hf]
  cases hexec : exec fuel m initial (f.toLocals (args.take f.numParams).reverse) f.body env with
  | Fallthrough st' s' =>
    rw [hexec] at hQ
    exact ⟨s'.values.take f.results.length ++ args.drop f.numParams, st', rfl, hQ⟩
  | Return st' vs =>
    rw [hexec] at hQ; exact ⟨vs.take f.results.length ++ args.drop f.numParams, st', rfl, hQ⟩
  | Break n st' s' => rw [hexec] at hQ; exact hQ.elim
  | Trap msg => rw [hexec] at hQ; exact hQ.elim
  | Invalid msg => rw [hexec] at hQ; exact hQ.elim
  | OutOfFuel => rw [hexec] at hQ; exact hQ.elim
  | ReturnCall fid st' vs => rw [hexec] at hQ; exact hQ.elim
  | Throwing tag targs st' s' => rw [hexec] at hQ; exact hQ.elim

end Wasm
