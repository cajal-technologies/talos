import CodeLib.SepLogic.MemoryTrace
import Interpreter.Wasm.Host.Universal

/-!
# Physical memory along traces with concrete host calls

A host label alone gives no memory guarantee. These lemmas require a proof
about every resolver in the actual host environment, including its trapping
and throwing outcomes. The Universal host satisfies this property: its byte
transfers can change contents but do not resize primary memory.

The trace rules retain the instruction restriction of `MemoryTrace`; in
particular they do not cover indexed memory or cross-instance transitions.
-/

namespace Wasm

def HostResult.primaryPages : HostResult α → Nat
  | .Return _ store | .Trap store _ | .Throw store _ _ => store.mem.pages

def HostFn.PreservesPrimaryPages (host : HostFn α) : Prop :=
  ∀ store args, (host.invoke store args).primaryPages = store.mem.pages

theorem HostFn.PreservesPrimaryPages.return_pages
    {host : HostFn α} (preserves : host.PreservesPrimaryPages)
    {store next : Store α} {args values : List Value}
    (result : host.invoke store args = .Return values next) :
    next.mem.pages = store.mem.pages := by
  simpa only [result, HostResult.primaryPages] using preserves store args

theorem HostFn.PreservesPrimaryPages.trap_pages
    {host : HostFn α} (preserves : host.PreservesPrimaryPages)
    {store next : Store α} {args : List Value} {message : String}
    (result : host.invoke store args = .Trap next message) :
    next.mem.pages = store.mem.pages := by
  simpa only [result, HostResult.primaryPages] using preserves store args

theorem HostFn.PreservesPrimaryPages.throw_pages
    {host : HostFn α} (preserves : host.PreservesPrimaryPages)
    {store next : Store α} {args values : List Value} {tag : Nat}
    (result : host.invoke store args = .Throw next tag values) :
    next.mem.pages = store.mem.pages := by
  simpa only [result, HostResult.primaryPages] using preserves store args

theorem HostFn.PreservesPrimaryPages.lift
    {host : HostFn α} (preserves : host.PreservesPrimaryPages)
    (lens : HostLens β α) : (host.lift lens).PreservesPrimaryPages := by
  intro store args
  have original := preserves (store.focus lens) args
  dsimp only [HostFn.lift]
  cases result : host.invoke (store.focus lens) args <;>
    simp only [result, HostResult.primaryPages] at original ⊢ <;>
    simpa only [Store.unfocus, Store.focus, Store.mapHost] using original

theorem StdIO.readHost_preservesPrimaryPages :
    StdIO.readHost.PreservesPrimaryPages := by
  intro store args
  change (StdIO.readResult store args).primaryPages = store.mem.pages
  unfold StdIO.readResult
  split
  · dsimp only
    split <;> rfl
  · rfl

theorem StdIO.writeHost_preservesPrimaryPages :
    StdIO.writeHost.PreservesPrimaryPages := by
  intro store args
  change (StdIO.writeResult store args).primaryPages = store.mem.pages
  unfold StdIO.writeResult
  split
  · split <;> rfl
  · rfl

theorem Random.getHost_preservesPrimaryPages :
    Random.getHost.PreservesPrimaryPages := by
  intro store args
  change (Random.getResult store args).primaryPages = store.mem.pages
  unfold Random.getResult
  split
  · split <;> rfl
  · rfl

theorem OOM.oomHost_preservesPrimaryPages :
    OOM.oomHost.PreservesPrimaryPages := by
  intro store args
  change (OOM.oomResult store args).primaryPages = store.mem.pages
  unfold OOM.oomResult
  split <;> rfl

theorem HostFn.unresolved_preservesPrimaryPages (decl : ImportDecl) :
    (HostFn.unresolved (α := α) decl).PreservesPrimaryPages := by
  intro store args
  rfl

def HostEnv.PreservesPrimaryPages (env : HostEnv α) : Prop :=
  (∀ (index : Nat) (host : HostFn α),
    env.funcs[index]? = some host → host.PreservesPrimaryPages) ∧
  (∀ (index : Nat) (host : HostFn α),
    env.foreignFuncs[index]? = some host → host.PreservesPrimaryPages)

theorem HostRegistry.entryFor_preservesPrimaryPages (registry : HostRegistry α)
    (preserves : ∀ entry ∈ registry, entry.fn.PreservesPrimaryPages)
    (decl : ImportDecl) : (registry.entryFor decl).fn.PreservesPrimaryPages := by
  unfold HostRegistry.entryFor
  split
  · rename_i entry found
    exact preserves entry (List.mem_of_find?_eq_some found)
  · exact HostFn.unresolved_preservesPrimaryPages decl

theorem HostRegistry.envFor_preservesPrimaryPages (registry : HostRegistry α)
    (preserves : ∀ entry ∈ registry, entry.fn.PreservesPrimaryPages)
    (m : Module) : (registry.envFor m).PreservesPrimaryPages := by
  constructor
  · intro index host lookup
    have member : host ∈ (registry.envFor m).funcs := List.mem_of_getElem? lookup
    simp only [HostRegistry.envFor, List.mem_map] at member
    obtain ⟨decl, _, rfl⟩ := member
    exact registry.entryFor_preservesPrimaryPages preserves decl
  · intro index host lookup
    simp only [HostRegistry.envFor, List.getElem?_nil] at lookup
    contradiction

theorem Universal.envFor_preservesPrimaryPages (m : Module) :
    (Universal.envFor m).PreservesPrimaryPages := by
  apply HostRegistry.envFor_preservesPrimaryPages
  intro entry member
  simp only [Universal.registry, HostRegistry.component, HostRegistry.lift,
    HostRegistry.ofImports, StdIO.imports, StdIO.env, Random.imports, Random.env,
    OOM.imports, OOM.env, List.zip_cons_cons, List.zip_nil_left, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact StdIO.readHost_preservesPrimaryPages.lift _
  · exact StdIO.writeHost_preservesPrimaryPages.lift _
  · exact Random.getHost_preservesPrimaryPages.lift _
  · exact OOM.oomHost_preservesPrimaryPages.lift _

/-- Regression: a resolver may resize memory even when it returns normally.
Such a resolver cannot satisfy the premise used by the host-aware trace rules. -/
theorem HostFn.resizing_not_preserving :
    ¬ (HostFn.PreservesPrimaryPages (α := Unit)
      { invoke := fun store _ => .Return []
          { store with mem := { store.mem with pages := store.mem.pages + 1 } } }) := by
  intro preserves
  let store : Store Unit := { mem := Mem.empty 1, globals := ⟨[]⟩, host := () }
  have impossible := preserves store []
  change 2 = 1 at impossible
  omega

namespace SmallStep

def HostPrimaryMemoryKind : StepKind → Prop
  | .host _ => True
  | kind => PrimaryMemoryKind kind

theorem Step.host_primary_pages_eq {before after : Config α} {index : Nat}
    (execution : Step before (.host index) after)
    (hosts : before.store.runtime.currentHost.PreservesPrimaryPages) :
    after.store.wasm.mem.pages = before.store.wasm.mem.pages := by
  cases execution
  all_goals first
    | exact (hosts.1 _ _ (by assumption)).return_pages (by assumption)
    | exact (hosts.1 _ _ (by assumption)).trap_pages (by assumption)
    | exact (hosts.1 _ _ (by assumption)).throw_pages (by assumption)
    | exact (hosts.2 _ _ (by assumption)).return_pages (by assumption)
    | exact (hosts.2 _ _ (by assumption)).trap_pages (by assumption)
    | exact (hosts.2 _ _ (by assumption)).throw_pages (by assumption)

theorem Step.primary_pages_mono_with_hosts
    {before after : Config α} {kind : StepKind}
    (execution : Step before kind after)
    (hosts : before.store.runtime.currentHost.PreservesPrimaryPages)
    (allowed : HostPrimaryMemoryKind kind) :
    before.store.wasm.mem.pages ≤ after.store.wasm.mem.pages := by
  cases kind with
  | host index => exact Nat.le_of_eq (execution.host_primary_pages_eq hosts).symm
  | instruction instruction => exact execution.primary_pages_mono allowed
  | administrative action => exact execution.primary_pages_mono allowed

theorem Step.hostPrimaryMemory_runtime
    {before after : Config α} {kind : StepKind}
    (execution : Step before kind after) (allowed : HostPrimaryMemoryKind kind) :
    after.store.runtime = before.store.runtime := by
  apply runtime_preserved execution
  · intro equality
    simp only [equality, HostPrimaryMemoryKind, PrimaryMemoryKind] at allowed
  · intro equality
    simp only [equality, HostPrimaryMemoryKind, PrimaryMemoryKind] at allowed

theorem Steps.primary_pages_mono_with_hosts
    {initial final : Config α} {trace : List StepKind}
    (execution : Steps initial trace final)
    (hosts : initial.store.runtime.currentHost.PreservesPrimaryPages)
    (allowed : ∀ kind ∈ trace, HostPrimaryMemoryKind kind) :
    initial.store.wasm.mem.pages ≤ final.store.wasm.mem.pages := by
  induction execution with
  | refl => exact Nat.le_refl _
  | cons head tail ih =>
      have headAllowed := allowed _ (List.mem_cons_self ..)
      have nextHosts := hosts
      rw [← head.hostPrimaryMemory_runtime headAllowed] at nextHosts
      exact Nat.le_trans (head.primary_pages_mono_with_hosts hosts headAllowed)
        (ih nextHosts (fun kind member => allowed kind (by simp [member])))

theorem Steps.hostPrimaryMemory_runtime
    {initial final : Config α} {trace : List StepKind}
    (execution : Steps initial trace final)
    (allowed : ∀ kind ∈ trace, HostPrimaryMemoryKind kind) :
    final.store.runtime = initial.store.runtime := by
  induction execution with
  | refl => rfl
  | cons head tail ih =>
      exact (ih (fun kind member => allowed kind (by simp [member]))).trans
        (head.hostPrimaryMemory_runtime (allowed _ (by simp)))

/-- Every prefix of this same actual trace lies between its endpoint page
counts. Host preservation is checked against the initial concrete environment;
the admissible transitions retain that runtime throughout the segment. -/
theorem Steps.primary_pages_at_prefix_with_hosts
    {initial middle final : Config α} {fullTrace beforeTrace : List StepKind}
    (full : Steps initial fullTrace final) (first : Steps initial beforeTrace middle)
    (lengthBound : beforeTrace.length ≤ fullTrace.length)
    (hosts : initial.store.runtime.currentHost.PreservesPrimaryPages)
    (allowed : ∀ kind ∈ fullTrace, HostPrimaryMemoryKind kind) :
    initial.store.wasm.mem.pages ≤ middle.store.wasm.mem.pages ∧
      middle.store.wasm.mem.pages ≤ final.store.wasm.mem.pages := by
  obtain ⟨afterTrace, rfl, remaining⟩ := full.suffix_of_length_le first lengthBound
  have firstAllowed : ∀ kind ∈ beforeTrace, HostPrimaryMemoryKind kind :=
    fun kind member => allowed kind (by simp [member])
  have middleHosts := hosts
  rw [← first.hostPrimaryMemory_runtime firstAllowed] at middleHosts
  exact ⟨first.primary_pages_mono_with_hosts hosts firstAllowed,
    remaining.primary_pages_mono_with_hosts middleHosts
      (fun kind member => allowed kind (by simp [member]))⟩

/-- A normal-return trace bounds physical pages at every reachable state from
the same initial configuration, with no prefix-length assumption. -/
theorem Steps.primary_pages_at_every_prefix_of_normal_return
    {initial reached : Config α} {fullTrace trace : List StepKind}
    {values : List Value} {store : MachineStore α}
    (full : Steps initial fullTrace ⟨.done values, store⟩)
    (hosts : initial.store.runtime.currentHost.PreservesPrimaryPages)
    (allowed : ∀ kind ∈ fullTrace, HostPrimaryMemoryKind kind)
    (first : Steps initial trace reached) :
    initial.store.wasm.mem.pages ≤ reached.store.wasm.mem.pages ∧
      reached.store.wasm.mem.pages ≤ store.wasm.mem.pages := by
  obtain ⟨afterTrace, traceEq, _⟩ := full.suffix_of_normal_return first
  exact full.primary_pages_at_prefix_with_hosts first
    (by rw [traceEq, List.length_append]; omega) hosts allowed

end SmallStep
end Wasm
