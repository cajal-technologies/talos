import CodeLib.SepLogic.CostedSteps

/-!
# Physical page bounds along primary-memory traces

The trace filter covers ordinary control, integer, and primary-memory operations.
Host calls and indexed-memory operations are deliberately excluded: their labels
alone do not justify a claim about the primary physical memory. The results use
actual `Step` transitions and do not strengthen persistent Iris page snapshots.
-/

namespace Wasm.SmallStep

/-- A checked subset of labels whose transitions cannot shrink primary memory.
An ordinary Wasm call is included; host invocations have a separate label. -/
def PrimaryMemoryKind : StepKind → Prop
  | .administrative .finish | .administrative .exitControl
  | .administrative .returnFromFunction | .administrative .returnFromCall => True
  | .instruction (.block _ _ _) | .instruction (.loop _ _ _)
  | .instruction (.localGet _) | .instruction (.localSet _)
  | .instruction (.localTee _) | .instruction (.const _)
  | .instruction (.constI64 _) | .instruction (.globalGet _)
  | .instruction (.globalSet _) | .instruction .drop
  | .instruction (.load8U _) | .instruction (.load8S _)
  | .instruction (.load16U _) | .instruction (.load16S _)
  | .instruction (.load32 _) | .instruction (.load64 _)
  | .instruction (.store8 _) | .instruction (.store16 _)
  | .instruction (.store32 _) | .instruction (.store64 _)
  | .instruction (.br _) | .instruction (.br_if _) | .instruction (.call _)
  | .instruction (.brTable _ _)
  | .instruction .ret | .instruction .add | .instruction .sub
  | .instruction .mul | .instruction .divU
  | .instruction .and | .instruction .or | .instruction .xor
  | .instruction .select | .instruction .ltU | .instruction .ltS
  | .instruction .gtU | .instruction .gtS | .instruction .leU | .instruction .leS
  | .instruction .geU | .instruction .geS | .instruction .ne | .instruction .eq
  | .instruction .shrU | .instruction .shrS | .instruction .shl
  | .instruction .eqz | .instruction .clz | .instruction .extend8S
  | .instruction .wrapI64 | .instruction .extendUI32
  | .instruction .mulI64 | .instruction .neI64
  | .instruction .andI64 | .instruction .orI64
  | .instruction .shlI64 | .instruction .shrUI64
  | .instruction .memorySize | .instruction .memoryGrow
  | .instruction .memoryFill | .instruction .memoryCopy => True
  | _ => False

private theorem grow_pages_mono {memory grown : Mem} {delta : UInt32} {cap old : Nat}
    (success : memory.grow delta cap = some (grown, old)) :
    memory.pages ≤ grown.pages := by
  unfold Mem.grow at success
  dsimp only at success
  split at success
  · have pages := congrArg (fun result : Mem × Nat => result.1.pages)
      (Option.some.inj success)
    dsimp only at pages
    omega
  · contradiction

theorem Step.primary_pages_mono {before after : Config α} {kind : StepKind}
    (execution : Step before kind after) (allowed : PrimaryMemoryKind kind) :
    before.store.wasm.mem.pages ≤ after.store.wasm.mem.pages := by
  cases execution <;> try exact Nat.le_refl _
  all_goals simp_all [PrimaryMemoryKind]
  all_goals exact grow_pages_mono (by assumption)

theorem Step.primary_pages_eq_of_not_grow {before after : Config α} {kind : StepKind}
    (execution : Step before kind after) (allowed : PrimaryMemoryKind kind)
    (notGrow : kind ≠ .instruction .memoryGrow) :
    after.store.wasm.mem.pages = before.store.wasm.mem.pages := by
  cases execution <;> try rfl
  all_goals simp_all [PrimaryMemoryKind]

/-- Labels for which growth is the only byte-weighted operation. -/
def GrowthCostKind : StepKind → Prop
  | .instruction .memoryFill | .instruction .memoryCopy => False
  | kind => PrimaryMemoryKind kind

theorem GrowthCostKind.primary {kind : StepKind} (allowed : GrowthCostKind kind) :
    PrimaryMemoryKind kind := by
  unfold GrowthCostKind at allowed
  split at allowed <;> first | assumption | contradiction

theorem Step.byteWork_eq_growth {before after : Config α} {kind : StepKind}
    (execution : Step before kind after) (allowed : GrowthCostKind kind)
    (hostBytes : Config α → Nat → Config α → Nat) :
    byteWork hostBytes before kind after =
      1 + 65536 * (after.store.wasm.mem.pages - before.store.wasm.mem.pages) := by
  by_cases grow : kind = .instruction .memoryGrow
  · subst kind; rfl
  · have pages := execution.primary_pages_eq_of_not_grow allowed.primary grow
    cases kind with
    | host index => simp [GrowthCostKind, PrimaryMemoryKind] at allowed
    | administrative action => simp [byteWork, pages]
    | instruction instruction =>
        cases instruction <;> simp_all [GrowthCostKind, PrimaryMemoryKind, byteWork]

theorem Steps.primary_pages_mono {initial final : Config α} {trace : List StepKind}
    (execution : Steps initial trace final)
    (allowed : ∀ kind ∈ trace, PrimaryMemoryKind kind) :
    initial.store.wasm.mem.pages ≤ final.store.wasm.mem.pages := by
  induction execution with
  | refl => exact Nat.le_refl _
  | cons head tail ih =>
      exact Nat.le_trans (head.primary_pages_mono (allowed _ (by simp)))
        (ih (fun kind member => allowed kind (by simp [member])))

/-- Growth charges telescope over an actual trace: count semantic transitions
and every added byte once. No host charge is suppressed; host steps are excluded
by the checked label premise. -/
theorem Steps.growth_byteWork {initial final : Config α} {trace : List StepKind}
    (execution : Steps initial trace final)
    (allowed : ∀ kind ∈ trace, GrowthCostKind kind)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes) initial trace final
      (trace.length + 65536 * (final.store.wasm.mem.pages - initial.store.wasm.mem.pages)) := by
  induction execution with
  | refl => simpa using CostedSteps.refl (charge := byteWork hostBytes) _
  | cons head tail ih =>
      rename_i start kind middle tailTrace endpoint
      have headAllowed : GrowthCostKind kind := allowed kind (by simp)
      have tailAllowed : ∀ kind ∈ tailTrace, GrowthCostKind kind :=
        fun kind member => allowed kind (by simp [member])
      have headPages := head.primary_pages_mono headAllowed.primary
      have tailPages := tail.primary_pages_mono (fun kind member =>
        (tailAllowed kind member).primary)
      have amountEq : (kind :: tailTrace).length +
          65536 * (endpoint.store.wasm.mem.pages - start.store.wasm.mem.pages) =
          byteWork hostBytes start kind middle +
          (tailTrace.length + 65536 *
            (endpoint.store.wasm.mem.pages - middle.store.wasm.mem.pages)) := by
        rw [head.byteWork_eq_growth headAllowed hostBytes]
        simp only [List.length_cons]
        omega
      rw [amountEq]
      exact CostedSteps.cons head (ih tailAllowed)

/-- Every state at a split of the same actual trace lies between its initial
and final page counts. In particular, the terminal count is a peak bound. -/
theorem Steps.primary_pages_at_split
    {initial middle final : Config α} {beforeTrace afterTrace : List StepKind}
    (first : Steps initial beforeTrace middle) (second : Steps middle afterTrace final)
    (allowed : ∀ kind ∈ beforeTrace ++ afterTrace, PrimaryMemoryKind kind) :
    initial.store.wasm.mem.pages ≤ middle.store.wasm.mem.pages ∧
      middle.store.wasm.mem.pages ≤ final.store.wasm.mem.pages := by
  exact ⟨first.primary_pages_mono (fun kind member => allowed kind (by simp [member])),
    second.primary_pages_mono (fun kind member => allowed kind (by simp [member]))⟩

/-- Determinism makes every shorter execution an actual prefix of a longer
execution from the same configuration, even if their labels were not supplied
as a syntactic prefix in advance. -/
theorem Steps.suffix_of_length_le
    {initial middle final : Config α} {fullTrace beforeTrace : List StepKind}
    (full : Steps initial fullTrace final) (first : Steps initial beforeTrace middle)
    (lengthBound : beforeTrace.length ≤ fullTrace.length) :
    ∃ afterTrace, fullTrace = beforeTrace ++ afterTrace ∧
      Steps middle afterTrace final := by
  induction first generalizing final fullTrace with
  | refl => exact ⟨fullTrace, rfl, full⟩
  | cons firstHead firstTail ih =>
      cases full with
      | refl => simp at lengthBound
      | cons fullHead fullTail =>
          obtain ⟨rfl, rfl⟩ := step_deterministic firstHead fullHead
          obtain ⟨afterTrace, rfl, remaining⟩ :=
            ih fullTail (by simp only [List.length_cons] at lengthBound; omega)
          exact ⟨afterTrace, rfl, remaining⟩

/-- A terminal execution contains every execution from its initial state as a
prefix. The absence of a next step replaces a supplied trace-length bound. -/
theorem Steps.suffix_of_terminal
    {initial middle final : Config α} {fullTrace beforeTrace : List StepKind}
    (full : Steps initial fullTrace final)
    (terminal : ∀ kind next, ¬ Step final kind next)
    (first : Steps initial beforeTrace middle) :
    ∃ afterTrace, fullTrace = beforeTrace ++ afterTrace ∧
      Steps middle afterTrace final := by
  induction first generalizing final fullTrace with
  | refl => exact ⟨fullTrace, rfl, full⟩
  | cons firstHead firstTail ih =>
      cases full with
      | refl => exact False.elim (terminal _ _ firstHead)
      | cons fullHead fullTail =>
          obtain ⟨rfl, rfl⟩ := step_deterministic firstHead fullHead
          obtain ⟨afterTrace, rfl, remaining⟩ := ih fullTail terminal
          exact ⟨afterTrace, rfl, remaining⟩

theorem Steps.suffix_of_normal_return
    {initial middle : Config α} {fullTrace beforeTrace : List StepKind}
    {values : List Value} {store : MachineStore α}
    (full : Steps initial fullTrace ⟨.done values, store⟩)
    (first : Steps initial beforeTrace middle) :
    ∃ afterTrace, fullTrace = beforeTrace ++ afterTrace ∧
      Steps middle afterTrace ⟨.done values, store⟩ :=
  full.suffix_of_terminal (by intro kind next step; cases step) first

/-- Bound all actual prefixes up to a certified segment's endpoint; this
does not make any claim about instructions in the caller after that endpoint. -/
theorem Steps.primary_pages_at_prefix
    {initial middle final : Config α} {fullTrace beforeTrace : List StepKind}
    (full : Steps initial fullTrace final) (first : Steps initial beforeTrace middle)
    (lengthBound : beforeTrace.length ≤ fullTrace.length)
    (allowed : ∀ kind ∈ fullTrace, PrimaryMemoryKind kind) :
    initial.store.wasm.mem.pages ≤ middle.store.wasm.mem.pages ∧
      middle.store.wasm.mem.pages ≤ final.store.wasm.mem.pages := by
  obtain ⟨afterTrace, rfl, remaining⟩ := full.suffix_of_length_le first lengthBound
  exact first.primary_pages_at_split remaining allowed

end Wasm.SmallStep
