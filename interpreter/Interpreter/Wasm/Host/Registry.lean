import Interpreter.Wasm.Host

/-!
# Name-keyed host registries

`HostEnv.funcs` is *positional*: `funcs[i]` must be the resolver for
`m.imports[i]`, because that is how `call i` finds it. A fixed `HostEnv` value
therefore serves exactly one import list, which is why each host today proves
`env_satisfies` under the hypothesis `m.imports = imports` — the module has to
declare precisely that host's imports, in precisely that order.

A *registry* removes the hypothesis. It is keyed by `ImportDecl` rather than by
position, and builds the positional list on demand, per module, walking that
module's own imports in its own order. Resolution is total: an import no
registered entry claims resolves to a stub that traps, so `envFor` never fails
and a module may declare imports from several hosts at once, in any order.

The payoff is `HostRegistry.envFor_satisfies`: a registry environment satisfies
its own spec for *every* module, with no hypothesis at all. `envFor` and
`specFor` are the same walk over `m.imports`, so they agree by construction.

This generalises `Near.resolveEnv?`, and supplies the "subset/order variant"
that `Near/Proof.lean` notes is missing there.

`Store.mapHost` and `HostFn.lift` let one host's functions run inside a larger
host state — the mechanism behind `Interpreter.Wasm.Host.Universal`.
-/

namespace Wasm

/-! ## Component lenses

`Store` has one host-dependent field, `host`; the Wasm core never inspects it.
Relabelling it preserves every Wasm-visible resource, which is what lets one
host's functions run inside a composite host state. -/

/-- Replace a store's host state, changing its type. -/
@[inline] def Store.mapHost (f : α → β) (st : Store α) : Store β :=
  { st with host := f st.host }

/-- A view of one component `α` inside a composite host state `β`. The two laws
hold by `rfl` for a record field, which is the only way this is ever built. -/
structure HostLens (β α : Type) where
  get : β → α
  set : β → α → β
  get_set : ∀ whole part, get (set whole part) = part := by intro _ _; rfl
  set_get : ∀ whole, set whole (get whole) = whole := by intro _; rfl

/-- The `α`-view of a composite store. -/
@[inline] def Store.focus (l : HostLens β α) (st : Store β) : Store α :=
  st.mapHost l.get

/-- Paste a component's result store back into the composite one. Wasm-core
fields come from `inner` — a host function may legitimately have written
memory — while the host slot widens `inner`'s component against `outer`. -/
@[inline] def Store.unfocus (l : HostLens β α) (outer : β) (inner : Store α) :
    Store β :=
  inner.mapHost (l.set outer)

/-! ## Lifting a host function into a larger host state -/

/-- Run `f`'s component view of the store, then widen whatever it returns. -/
def HostFn.lift (l : HostLens β α) (f : HostFn α) : HostFn β where
  params := f.params
  results := f.results
  invoke := fun st args =>
    match f.invoke (st.focus l) args with
    | .Return values inner => .Return values (Store.unfocus l st.host inner)
    | .Trap inner message => .Trap (Store.unfocus l st.host inner) message
    | .Throw inner tag values => .Throw (Store.unfocus l st.host inner) tag values

/-! A lifted call is the component's call, with the composite host state carried
around it. These three turn a fact about the component into a fact about the
lifted function, which is what a proof under a composite host state needs — and
they let `HostFn.lift` stay out of the `simp` set, where unfolding it would
expand a whole `Store` update at every host call. -/

theorem HostFn.lift_invoke_return (l : HostLens β α) (f : HostFn α)
    (st : Store β) (args : List Value) {values : List Value} {inner : Store α}
    (h : f.invoke (st.focus l) args = .Return values inner) :
    (f.lift l).invoke st args =
      .Return values (Store.unfocus l st.host inner) := by
  simp [HostFn.lift, h]

theorem HostFn.lift_invoke_trap (l : HostLens β α) (f : HostFn α)
    (st : Store β) (args : List Value) {inner : Store α} {message : String}
    (h : f.invoke (st.focus l) args = .Trap inner message) :
    (f.lift l).invoke st args =
      .Trap (Store.unfocus l st.host inner) message := by
  simp [HostFn.lift, h]

theorem HostFn.lift_invoke_throw (l : HostLens β α) (f : HostFn α)
    (st : Store β) (args : List Value) {inner : Store α} {tag : Nat}
    {values : List Value}
    (h : f.invoke (st.focus l) args = .Throw inner tag values) :
    (f.lift l).invoke st args =
      .Throw (Store.unfocus l st.host inner) tag values := by
  simp [HostFn.lift, h]

/-! ## Registries -/

/-- Import declarations name the same function when module, name and signature
all agree. -/
def ImportDecl.matches (a b : ImportDecl) : Bool :=
  a.«module» == b.«module» && a.name == b.name &&
    a.params == b.params && a.results == b.results

/-- One registered host import: the declaration a module writes to reach it,
the function behind it, the contract a proof sees, and the fact they agree.

`contract` and `sound` default to the exact contract — "the result is what the
function computes" — which is what every host in the repo uses today, and which
`sound` discharges by `rfl`. A host wanting an implementation-hiding contract
overrides both fields. -/
structure HostEntry (α : Type) where
  decl : ImportDecl
  fn : HostFn α
  contract : HostContract α := fun st args result => result = fn.invoke st args
  sound : ∀ st args, contract st args (fn.invoke st args) := by intro _ _; rfl

/-- Everything a host offers, keyed by declaration rather than by position. -/
abbrev HostRegistry (α : Type) := List (HostEntry α)

/-- Pair a host's existing positional import list with its aligned resolvers.

A host already maintains those two lists — `imports` and `env.funcs` — and the
interpreter already relies on them lining up, since that alignment is what makes
`call i` find the right function. `ofImports` reuses exactly that invariant
rather than restating every declaration a second time, so a host's registry is
one line and cannot drift from its imports. -/
def HostRegistry.ofImports (imports : List ImportDecl) (funcs : List (HostFn α)) :
    HostRegistry α :=
  (imports.zip funcs).map fun p => { decl := p.fst, fn := p.snd }

/-- Run a registered entry inside a larger host state. The lifted entry takes
the exact contract of the lifted function; a component's own abstract contract
is recovered through its own lemmas, not carried through the lift. -/
def HostEntry.lift (l : HostLens β α) (entry : HostEntry α) : HostEntry β where
  decl := entry.decl
  fn := entry.fn.lift l

/-- Lift a whole registry into a larger host state. -/
def HostRegistry.lift (l : HostLens β α) (reg : HostRegistry α) :
    HostRegistry β :=
  reg.map (HostEntry.lift l)

/-- Register an existing host as a component of a composite host state: the
host's own `imports` and `env.funcs`, plus the field of the composite state it
occupies, named by that field's getter and setter.

This is the *entire* cost of adding a host to a composite one, and it asks the
host for nothing it does not already have — a host is written exactly as
`Host/StdIO.lean` and `Host/Random.lean` are written, and never mentions
registries, composition, or any other host.

The two lens laws are auto-params: for a record field they close by `rfl`, so a
call site writes only the projection and the update, and no `HostLens` is ever
named. -/
def HostRegistry.component (imports : List ImportDecl) (funcs : List (HostFn α))
    (get : β → α) (set : β → α → β)
    (get_set : ∀ whole part, get (set whole part) = part := by intro _ _; rfl)
    (set_get : ∀ whole, set whole (get whole) = whole := by intro _; rfl) :
    HostRegistry β :=
  (HostRegistry.ofImports imports funcs).lift { get, set, get_set, set_get }

/-- What an import resolves to when no entry claims it: a function of the
declared shape that traps, naming the import it could not find. -/
def HostFn.unresolved (decl : ImportDecl) : HostFn α where
  params := decl.params
  results := decl.results
  invoke := fun st _ =>
    .Trap st s!"no host function registered for {decl.«module»}.{decl.name}"

/-- The entry a declared import resolves to, first match wins. -/
def HostRegistry.entryFor (reg : HostRegistry α) (decl : ImportDecl) :
    HostEntry α :=
  match reg.find? (fun entry => ImportDecl.matches entry.decl decl) with
  | some entry => entry
  | none => { decl, fn := HostFn.unresolved decl }

/-- Whether every import `m` declares is claimed by some entry. A module that
does not pass this check still runs — its unclaimed imports trap — so specs
carry it as an explicit smoke test rather than relying on it silently. -/
def HostRegistry.covers (reg : HostRegistry α) (m : Module) : Bool :=
  m.imports.all fun decl =>
    (reg.find? (fun entry => ImportDecl.matches entry.decl decl)).isSome

/-- The positional environment `m` sees under this registry. -/
def HostRegistry.envFor (reg : HostRegistry α) (m : Module) : HostEnv α :=
  { funcs := m.imports.map fun decl => (reg.entryFor decl).fn }

/-- The positional spec matching `envFor`, entry by entry. -/
def HostRegistry.specFor (reg : HostRegistry α) (m : Module) : HostSpec α :=
  { contracts := m.imports.map fun decl => (reg.entryFor decl).contract }

@[simp] theorem HostRegistry.envFor_nil (reg : HostRegistry α)
    (m : Module) (h : m.imports = []) : reg.envFor m = HostEnv.empty := by
  simp [HostRegistry.envFor, HostEnv.empty, h]

theorem HostRegistry.envFor_getElem? (reg : HostRegistry α) (m : Module)
    {i : Nat} (hi : i < m.imports.length) :
    (reg.envFor m).funcs[i]? = some (reg.entryFor m.imports[i]).fn := by
  simp [HostRegistry.envFor, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem HostRegistry.specFor_getElem? (reg : HostRegistry α) (m : Module)
    {i : Nat} (hi : i < m.imports.length) :
    (reg.specFor m).contracts[i]? = some (reg.entryFor m.imports[i]).contract := by
  simp [HostRegistry.specFor, List.getElem?_map, List.getElem?_eq_getElem hi]

/-- A registry environment satisfies its own spec for **every** module, with no
hypothesis on the module's imports.

This is what lets a proof stop choosing a host. The per-host `env_satisfies`
theorems each require `m.imports = thatHost.imports`; here the environment and
the spec are the same walk over `m.imports`, so they line up by construction
whatever the module declares — a subset, a different order, or a mixture of
several hosts. -/
theorem HostRegistry.envFor_satisfies (reg : HostRegistry α) (m : Module) :
    (reg.envFor m).Satisfies m (reg.specFor m) := by
  intro i hi
  exact ⟨(reg.entryFor m.imports[i]).fn, (reg.entryFor m.imports[i]).contract,
    reg.envFor_getElem? m hi, reg.specFor_getElem? m hi,
    (reg.entryFor m.imports[i]).sound⟩

end Wasm
