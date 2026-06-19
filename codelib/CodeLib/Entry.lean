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
    rw [hexec] at hQ
    exact ⟨vs.take f.results.length ++ args.drop f.numParams, st', rfl, hQ⟩
  | Break n st' s' => rw [hexec] at hQ; exact hQ.elim
  | Trap msg => rw [hexec] at hQ; exact hQ.elim
  | Invalid msg => rw [hexec] at hQ; exact hQ.elim
  | OutOfFuel => rw [hexec] at hQ; exact hQ.elim
  | ReturnCall fid st' vs => rw [hexec] at hQ; exact hQ.elim
  | Throwing tag targs st' s' => rw [hexec] at hQ; exact hQ.elim

/-- Weakening the post-condition of a `TerminatesWith`. Lets a corpus
proof state the natural raw-value spec, then relift it through an
abstraction (e.g. an `Option` decoder) without re-running `wp`. -/
theorem TerminatesWith.mono {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value}
    {P Q : Store α → List Value → Prop}
    (h : TerminatesWith env m id initial args P) (hPQ : ∀ st vs, P st vs → Q st vs) :
    TerminatesWith env m id initial args Q := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hf => ?_⟩
  obtain ⟨vs, st, hRun, hP⟩ := hN fuel hf
  exact ⟨vs, st, hRun, hPQ st vs hP⟩

/-- Start a store-parametric entry proof by inferring the generated
`Function` witness from the concrete module. Use for specs whose body proof
does not depend on facts about the caller's initial store. -/
macro "wasm_entry" : tactic => `(tactic|
  apply TerminatesWith.of_wp_entry (by rfl))

/-- Store-specific entry-proof variant. Use when the proof depends on
properties of the concrete initial store, such as memory bounds. -/
macro "wasm_entry_for" : tactic => `(tactic|
  apply TerminatesWith.of_wp_entry_for (by rfl))

/-- Start a `FuncSpec` proof by inferring the generated `Function` witness
from the concrete module. -/
macro "wasm_funcspec" : tactic => `(tactic|
  refine FuncSpec.of_wp_body (by rfl) ?_)

/-! ## wp-style function specs

Per-function CodeLib theorems are stated as weakest-precondition goals about
the function *body* (no module/host-function hypotheses, no `TerminatesWith`).
`Returns rs P` reads "the body returns `rs` on the stack in a store satisfying
`P`"; `of_returns_wp` bridges such a wp lemma to the `TerminatesWith` form the
call rules consume, so the per-function statements stay clean while still
composing under `call`. -/

/-- Postcondition reading: the program returns with stack `rs` in a store
satisfying `P`. -/
def Returns (rs : List Value) (P : Store α → Prop) : Assertion α :=
  fun c => ∃ st', c = .Return st' rs ∧ P st'

/-- Bridge a clean `wp`/`Returns` body lemma to `TerminatesWith`. The callee
runs on an empty value stack (`f.toLocals …`), so the caller's leftover
operands `args.drop f.numParams` are re-appended to the result here, not
inside the body lemma. -/
theorem TerminatesWith.of_returns_wp {α} {env : HostEnv α} {m : Module} {id : Nat}
    {f : Function} {st : Store α} {args rs : List Value} {P : Store α → Prop}
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hres : rs.length = f.results.length)
    (hwp : wp m f.body (Returns rs P) st
            (f.toLocals (args.take f.numParams).reverse) env)
    (hImp : m.imports[id]? = none := by rfl) :
    TerminatesWith env m id st args
      (fun st' vs => vs = rs ++ args.drop f.numParams ∧ P st') := by
  apply TerminatesWith.of_wp_entry_for hf _ hImp
  refine wp.conseq ?_ hwp
  rintro c ⟨st', rfl, hP⟩
  have htake : rs.take f.results.length = rs := by rw [← hres]; simp
  simp only [htake]
  exact ⟨trivial, hP⟩

end Wasm
