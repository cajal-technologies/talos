import Interpreter.Wasm

/-!
# `TerminatesWith.of_wp_entry`

Single-step bridge from a fuel-free `TerminatesWith` spec down to a `wp`
goal on the function body. Fuses `FuncSpec.to_TerminatesWith` and
`FuncSpec.of_wp_body` and specializes to a fixed argument list, so corpus
proofs don't have to name `Pre`/`Post` or run the `FuncSpec` plumbing by
hand.
-/

namespace Wasm

/-- Discharge `TerminatesWith m id initial args P` by proving the `wp` of
the function body (parametric in the initial store). Locals are built from
`args.take f.numParams` reversed (Wasm calling convention), and the
post-condition is checked on `Fallthrough`/`Return` after taking the top
`f.results.length` values and appending the caller-remainder. -/
theorem TerminatesWith.of_wp_entry {m : Module} {id : Nat} {f : Function}
    {initial : Store} {args : List Value} {P : Store → List Value → Prop}
    (hf : m.funcs[id]? = some f)
    (h : ∀ initial : Store,
      wp m f.body
        (fun c => match c with
          | .Fallthrough st' s' =>
              P st' (s'.values.take f.results.length ++ args.drop f.numParams)
          | .Return st' vs      =>
              P st' (vs.take f.results.length ++ args.drop f.numParams)
          | _                   => False)
        initial (f.toLocals (args.take f.numParams).reverse)) :
    TerminatesWith m id initial args P := by
  refine FuncSpec.to_TerminatesWith (Pre := (· = args))
    (FuncSpec.of_wp_body hf ?_) rfl
  rintro _ rfl initial'; exact h initial'

/-- Variant of `of_wp_entry` for a specific store rather than all stores.
Use when the function body's correctness depends on properties of the
initial store (e.g., memory bounds). -/
theorem TerminatesWith.of_wp_entry_for {m : Module} {id : Nat} {f : Function}
    {initial : Store} {args : List Value} {P : Store → List Value → Prop}
    (hf : m.funcs[id]? = some f)
    (h : wp m f.body
        (fun c => match c with
          | .Fallthrough st' s' =>
              P st' (s'.values.take f.results.length ++ args.drop f.numParams)
          | .Return st' vs      =>
              P st' (vs.take f.results.length ++ args.drop f.numParams)
          | _                   => False)
        initial (f.toLocals (args.take f.numParams).reverse)) :
    TerminatesWith m id initial args P := by
  unfold TerminatesWith
  unfold wp at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hfuel => ?_⟩
  have hQ := hN fuel hfuel
  rw [run_eq]; simp only [hf]
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

/-- Weakening the post-condition of a `TerminatesWith`. Lets a corpus
proof state the natural raw-value spec, then relift it through an
abstraction (e.g. an `Option` decoder) without re-running `wp`. -/
theorem TerminatesWith.mono {m : Module} {id : Nat}
    {initial : Store} {args : List Value}
    {P Q : Store → List Value → Prop}
    (h : TerminatesWith m id initial args P) (hPQ : ∀ st vs, P st vs → Q st vs) :
    TerminatesWith m id initial args Q := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hf => ?_⟩
  obtain ⟨vs, st, hRun, hP⟩ := hN fuel hf
  exact ⟨vs, st, hRun, hPQ st vs hP⟩

end Wasm
