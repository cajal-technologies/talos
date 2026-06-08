import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Semantics.Lemmas
import Interpreter.Wasm.Spec.Defs

/-! ### Function specifications and `call`.

    `FuncSpec m id Pre Post` says: given args satisfying `Pre`, calling
    function `id` of module `m` terminates with a success result whose values
    satisfy `Post`. Mutually-recursive specs share a single measure encoded
    inside `Pre` (e.g., `Pre args ↔ args = [n] ∧ n < bound`). -/

namespace Wasm

def FuncSpec (env : HostEnv α) (m : Module) (id : Nat)
    (Pre : List Value → Prop) (Post : Store α → List Value → Prop) : Prop :=
  ∀ args, Pre args → ∀ initial : Store α,
    TerminatesWith env m id initial args Post

/-- Store-specific core of the direct-call WP rule. Like `wp_call_cons`
but consumes the callee's success behaviour *at the current store* `st`
and *current operands* `s.values` — exactly a `TerminatesWith`
(`Spec/Termination.lean`) unfolded. Use directly when the callee reads
linear memory and so only has a meaningful spec on a particular store
(e.g. the module's `initialStore`), where a store-polymorphic `FuncSpec`
is unavailable. -/
theorem wp_call_at {env : HostEnv α}
    {id : Nat} {Post : Store α → List Value → Prop}
    (hRun : ∃ N, ∀ fuel ≥ N, ∃ vs st',
              run fuel m id st s.values env = .Success vs st' ∧ Post st' vs)
    (hPost : ∀ st' vs, Post st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env := by
  unfold wp
  obtain ⟨Ns, hNs⟩ := hRun
  obtain ⟨vs, st', hRun, hPost_vs⟩ := hNs Ns le_rfl
  have hRun_ne : run Ns m id st s.values env ≠ .OutOfFuel := by rw [hRun]; intro h; cases h
  have hwp_rest := hPost st' vs hPost_vs
  unfold wp at hwp_rest
  obtain ⟨Nr, hNr⟩ := hwp_rest
  refine ⟨max (Ns + 1) (Nr + 1), fun fuel hfuel => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hRun_f : run f m id st s.values env = .Success vs st' := by
    rw [run_fuel_mono (by omega : f ≥ Ns) hRun_ne]; exact hRun
  rw [exec_call_cons, hRun_f]
  exact hNr (f + 1) (by omega)

theorem wp_call_cons {env : HostEnv α}
    {id : Nat} {Pre : List Value → Prop} {Post : Store α → List Value → Prop}
    (spec : FuncSpec env m id Pre Post)
    (hPre : Pre s.values)
    (hPost : ∀ st' vs, Post st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env :=
  wp_call_at (spec s.values hPre st) hPost

/-- Direct-call WP rule consuming the public fuel-free total-correctness
predicate directly. Prefer this wrapper when the callee spec is already a
`TerminatesWith` theorem specialized to the current store and operands. -/
theorem wp_call_tw {env : HostEnv α}
    {id : Nat} {Post : Store α → List Value → Prop}
    (hRun : TerminatesWith env m id st s.values Post)
    (hPost : ∀ st' vs, Post st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env :=
  wp_call_at hRun hPost

/-- Backwards-compatible descriptive alias for `wp_call_tw`. -/
theorem wp_call_of_terminates {env : HostEnv α}
    {id : Nat} {Post : Store α → List Value → Prop}
    (hRun : TerminatesWith env m id st s.values Post)
    (hPost : ∀ st' vs, Post st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env :=
  wp_call_tw hRun hPost

/-- Store-specific core of the indirect-call WP rule. Instead of a
store-polymorphic `FuncSpec`, it consumes the resolved callee's success
behaviour *at the current store* `st` — exactly a `TerminatesWith`
(`Spec/Termination.lean`) unfolded to its existential. Use this directly
when the callee reads linear memory and so only has a meaningful spec on
a particular store (e.g. the module's `initialStore`), where a
store-polymorphic `FuncSpec` is unavailable. The hypotheses otherwise
match `wp_callIndirect_cons`: locate the selector (`hStack`), look it up
through the chosen table and slot (`hTbl`, `hSlot`), and confirm the
resolved function index has the declared signature (`hFn`, `hTy`,
`hSig`). -/
theorem wp_callIndirect_at {α : Type} {env : HostEnv α}
    {m : Module} {st : Store α} {s : Locals} {Q : Assertion α}
    {rest : Program} {ti tj : Nat}
    {Post : Store α → List Value → Prop}
    {i : UInt32} {vs0 : List Value} {tbl : TableInst} {fid : Nat}
    {fn : Function} {ty : FuncType}
    (hStack : s.values = .i32 i :: vs0)
    (hTbl  : st.tables[tj]? = some tbl)
    (hSlot : tbl[i.toNat]? = some (some fid))
    (hFn   : m.funcs[fid]? = some fn)
    (hTy   : m.types[ti]? = some ty)
    (hSig  : fn.params = ty.params ∧ fn.results = ty.results)
    (hRun  : ∃ N, ∀ fuel ≥ N, ∃ vs st',
              run fuel m fid st vs0 env = .Success vs st' ∧ Post st' vs)
    (hPost : ∀ st' vs, Post st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.callIndirect ti tj :: rest) Q st s env := by
  unfold wp
  obtain ⟨Ns, hNs⟩ := hRun
  obtain ⟨vs, st', hRun, hPost_vs⟩ := hNs Ns le_rfl
  have hRun_ne : run Ns m fid st vs0 env ≠ .OutOfFuel := by
    rw [hRun]; intro h; cases h
  have hwp_rest := hPost st' vs hPost_vs
  unfold wp at hwp_rest
  obtain ⟨Nr, hNr⟩ := hwp_rest
  refine ⟨max (Ns + 1) (Nr + 1), fun fuel hfuel => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hRun_f : run f m fid st vs0 env = .Success vs st' := by
    rw [run_fuel_mono (by omega : f ≥ Ns) hRun_ne]; exact hRun
  rw [exec_callIndirect_cons hStack hTbl hSlot hFn hTy hSig, hRun_f]
  exact hNr (f + 1) (by omega)

/-- Indirect-call analogue of `wp_call_cons`. The hypotheses split the
work of dispatching an indirect call into four steps: locate the
selector on the stack (`hStack`), look it up through the chosen table
and slot (`hTbl`, `hSlot`), confirm the resolved function index has the
expected signature against the declared `(type N)` (`hFn`, `hTy`,
`hSig`), and supply a `FuncSpec` for the target. A thin wrapper over
`wp_callIndirect_at` that instantiates the `FuncSpec` at `vs0` and the
current store. -/
theorem wp_callIndirect_cons {α : Type} {env : HostEnv α}
    {m : Module} {st : Store α} {s : Locals} {Q : Assertion α}
    {rest : Program} {ti tj : Nat}
    {Pre : List Value → Prop} {Post : Store α → List Value → Prop}
    {i : UInt32} {vs0 : List Value} {tbl : TableInst} {fid : Nat}
    {fn : Function} {ty : FuncType}
    (hStack : s.values = .i32 i :: vs0)
    (hTbl  : st.tables[tj]? = some tbl)
    (hSlot : tbl[i.toNat]? = some (some fid))
    (hFn   : m.funcs[fid]? = some fn)
    (hTy   : m.types[ti]? = some ty)
    (hSig  : fn.params = ty.params ∧ fn.results = ty.results)
    (spec  : FuncSpec env m fid Pre Post)
    (hPre  : Pre vs0)
    (hPost : ∀ st' vs, Post st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.callIndirect ti tj :: rest) Q st s env :=
  wp_callIndirect_at hStack hTbl hSlot hFn hTy hSig (spec vs0 hPre st) hPost

/-- Indirect-call WP rule consuming the resolved target's public
`TerminatesWith` theorem directly. -/
theorem wp_callIndirect_tw {α : Type} {env : HostEnv α}
    {m : Module} {st : Store α} {s : Locals} {Q : Assertion α}
    {rest : Program} {ti tj : Nat}
    {Post : Store α → List Value → Prop}
    {i : UInt32} {vs0 : List Value} {tbl : TableInst} {fid : Nat}
    {fn : Function} {ty : FuncType}
    (hStack : s.values = .i32 i :: vs0)
    (hTbl  : st.tables[tj]? = some tbl)
    (hSlot : tbl[i.toNat]? = some (some fid))
    (hFn   : m.funcs[fid]? = some fn)
    (hTy   : m.types[ti]? = some ty)
    (hSig  : fn.params = ty.params ∧ fn.results = ty.results)
    (hRun  : TerminatesWith env m fid st vs0 Post)
    (hPost : ∀ st' vs, Post st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.callIndirect ti tj :: rest) Q st s env :=
  wp_callIndirect_at hStack hTbl hSlot hFn hTy hSig hRun hPost

/-- Bridge from `wp` of a function body to `FuncSpec`. The body sees locals
    built from `args.take f.numParams` reversed (so local 0 is the first
    argument), and the `Post` is checked on its `Fallthrough`/`Return`
    outcomes after taking the top `f.results.length` values and appending the
    caller-remainder — matching `run`'s standard Wasm calling convention.

    `hf` indexes `m.funcs` *after* shifting by `m.imports.length` (so a
    module with one import maps unified index `1` to `funcs[0]`); for the
    common case `m.imports = []` the shift is zero and existing `rfl`
    proofs still discharge it. `hImp` confirms the called index isn't a
    host import; it defaults to `rfl`, which discharges for any module
    whose `imports` literal is `[]`. -/
theorem FuncSpec.of_wp_body
    {env : HostEnv α} {m : Module} {id : Nat} {f : Function}
    {Pre : List Value → Prop} {Post : Store α → List Value → Prop}
    (hf : m.funcs[id - m.imports.length]? = some f)
    (h : ∀ args, Pre args → ∀ initial : Store α,
      wp m f.body
        (fun c => match c with
          | .Fallthrough st' s' =>
              Post st' (s'.values.take f.results.length ++ args.drop f.numParams)
          | .Return st' vs      =>
              Post st' (vs.take f.results.length ++ args.drop f.numParams)
          | _                   => False)
        initial (f.toLocals (args.take f.numParams).reverse) env)
    (hImp : m.imports[id]? = none := by rfl) :
    FuncSpec env m id Pre Post := by
  intro args hPre initial
  have hwp := h args hPre initial
  unfold wp at hwp
  obtain ⟨N, hN⟩ := hwp
  refine ⟨N, fun fuel hfuel => ?_⟩
  have hQ := hN fuel hfuel
  rw [run_eq hImp]
  simp only [hf]
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

/-! ### Host calls.

    `wp_call_host_cons` is the WP rule for a `.call id` that resolves to
    a host import: it lets the user discharge the host invocation by
    reasoning about the concrete `HostFn.invoke` result, branching on
    `Return` vs `Trap` exactly as the host can. Compared with
    `wp_call_cons`, there is no `FuncSpec` indirection: the invoke
    function is fully concrete, and the user proves the post-condition
    by case analysis on it. The abstraction layer (per-import contract
    that hides `invoke` behind a relation) lands in M4. -/

theorem wp_call_host_cons {m : Module} {env : HostEnv α}
    {id : Nat} {imp : ImportDecl} {hf : HostFn α}
    {rest : Program} {Q : Assertion α} {st : Store α} {s : Locals}
    (hImp : m.imports[id]? = some imp)
    (hEnv : env.funcs[id]? = some hf)
    (hReturn : ∀ vs st',
      hf.invoke st (s.values.take imp.params.length).reverse = .Return vs st' →
      wp m rest Q st'
        { s with values := vs.take imp.results.length
                       ++ s.values.drop imp.params.length } env)
    (hTrap : ∀ st' msg,
      hf.invoke st (s.values.take imp.params.length).reverse = .Trap st' msg →
      Q (.Trap st' msg)) :
    wp m (.call id :: rest) Q st s env := by
  unfold wp
  cases hInv : hf.invoke st (s.values.take imp.params.length).reverse with
  | Return vs st' =>
    have hwp := hReturn vs st' hInv
    unfold wp at hwp
    obtain ⟨N, hN⟩ := hwp
    refine ⟨N + 1, fun fuel hfuel => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_call_host_cons hImp hEnv, hInv]
    exact hN (f + 1) (by omega)
  | Trap st' msg =>
    refine ⟨1, fun fuel hfuel => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [exec_call_host_cons hImp hEnv, hInv]
    exact hTrap st' msg hInv

/-- Host-call WP rule through an abstract contract in a satisfying
`HostEnv`. The concrete resolver stays existential; proof branches receive
only the contract fact for the actual host outcome. -/
theorem wp_call_host_contract {m : Module} {env : HostEnv α}
    {spec : HostSpec α} {id : Nat} {imp : ImportDecl} {c : HostContract α}
    {rest : Program} {Q : Assertion α} {st : Store α} {s : Locals}
    (hImp : m.imports[id]? = some imp)
    (hSat : env.Satisfies m spec)
    (hi : id < m.imports.length)
    (hC : spec.contracts[id]? = some c)
    (hReturn : ∀ vs st',
      c st (s.values.take imp.params.length).reverse (.Return vs st') →
      wp m rest Q st'
        { s with values := vs.take imp.results.length
                       ++ s.values.drop imp.params.length } env)
    (hTrap : ∀ st' msg,
      c st (s.values.take imp.params.length).reverse (.Trap st' msg) →
      Q (.Trap st' msg)) :
    wp m (.call id :: rest) Q st s env := by
  obtain ⟨hf, hEnv, hContract⟩ := hSat.lookup_contract hi hC
  refine wp_call_host_cons hImp hEnv ?_ ?_
  · intro vs st' hInv
    have hRel := hContract st (s.values.take imp.params.length).reverse
    rw [hInv] at hRel
    exact hReturn vs st' hRel
  · intro st' msg hInv
    have hRel := hContract st (s.values.take imp.params.length).reverse
    rw [hInv] at hRel
    exact hTrap st' msg hRel

end Wasm
