import Project.Mergesort.DriverProof
import Project.Mergesort.OutputCost
import CodeLib.SepLogic.SequentialExecution

set_option maxRecDepth 1048576

namespace Project.Mergesort.OutputResources

open Wasm Wasm.SmallStep Wasm.SepLogic
open Iris Iris.ProgramLogic Language.Notation Std
open Project.Mergesort.Representations
open scoped Wasm.SmallStep.Outcome

/-- The existing array ownership determines the physical word view. -/
theorem arrayAt_readWords32 [WasmSmallStepGS hlc Universal.State]
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (ptr : UInt32) (values : List UInt32)
    (hbound : ptr.toNat + 4 * values.length < UInt32.size) :
    stateInterp (GF := WasmHeapGF Universal.State) store steps observations threads ∗
      arrayAt 0 ptr values ==∗
      ⌜store.wasm.mem.readWords32 ptr values.length = values⌝ := by
  induction values generalizing ptr with
  | nil => iintro ⟨_, _⟩; ipureintro; rfl
  | cons value rest ih =>
      iintro ⟨Hstate, Harray⟩
      isimp only [arrayAt] at Harray
      icases Harray with ⟨Hword, Hrest⟩
      obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 ptr (by
        change ptr.toNat + 4 ≤ UInt32.size
        simp only [List.length_cons] at hbound
        omega)
      ihave_pure hword :
          ⌜store.wasm.mem.read32 ptr = value ∧
            ptr.toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ using
        stateInterp_pointsTo_u32_facts store steps observations threads ptr value h1 h2 h3
        $$ [Hstate Hword]
      have nextAddress : (ptr + 4).toNat = ptr.toNat + 4 := by
        rw [UInt32.toNat_add]
        exact Nat.mod_eq_of_lt (by
          change ptr.toNat + 4 < UInt32.size
          simp only [List.length_cons] at hbound
          omega)
      ihave_pure hrest :
          ⌜store.wasm.mem.readWords32 (ptr + 4) rest.length = rest⌝ using
        ih (ptr + 4) (by rw [nextAddress]; simp only [List.length_cons] at hbound; omega)
        $$ [Hstate Hrest]
      ipureintro
      simp only [List.length_cons, Mem.readWords32, hword.1, hrest]

/-- Canonical word-slice resources fix the physical source array and its
complete readable range. The nonempty premise is the generated loop guard. -/
theorem WordSlice_physical [WasmSmallStepGS hlc Universal.State]
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (ptr : UInt32) (values : List UInt32) (hpositive : 0 < values.length) :
    stateInterp (GF := WasmHeapGF Universal.State) store steps observations threads ∗
      WordSlice ptr values ==∗
      ⌜store.wasm.mem.readWords32 ptr values.length = values ∧
        ptr.toNat + 4 * values.length ≤ store.wasm.mem.pages * 65536 ∧
        ptr.toNat + 4 * values.length < UInt32.size⌝ := by
  iintro ⟨Hstate, Hwords⟩
  isimp only [WordSlice, Representations.ByteSlice] at Hwords
  icases Hwords with ⟨%_align, %nowrap, Hbytes⟩
  have bound : ptr.toNat + 4 * values.length < UInt32.size := by
    simpa only [serialize_length] using nowrap
  ihave_pure byteFacts :
      ⌜∀ i b, (serialize values)[i]? = some b →
        store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
        (ptr + UInt32.ofNat i).toNat < store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsToBytes_agree store steps observations threads ptr (serialize values)
    $$ [Hstate Hbytes]
  ihave Harray := (arrayAt_eq_wordCells ptr values).mpr $$ Hbytes
  ihave_pure words : ⌜store.wasm.mem.readWords32 ptr values.length = values⌝ using
    arrayAt_readWords32 store steps observations threads ptr values bound $$ [Hstate Harray]
  ipureintro
  refine ⟨words, ?_, bound⟩
  have physical := pointsToBytes_facts_bound byteFacts
    (by rw [serialize_length]; omega) (by simpa only [UInt32.size] using nowrap)
  simpa only [serialize_length] using physical

/-- Distinct exclusive word cells cannot start at the same address. -/
theorem word_cells_ne [WasmHeapGS Universal.State]
    (left right x y : UInt32) :
    pointsTo_u32 0 left x ∗ pointsTo_u32 0 right y ⊢ ⌜left ≠ right⌝ := by
  iintro ⟨Hleft, Hright⟩
  isimp only [pointsTo_u32] at Hleft Hright
  icases Hleft with ⟨Hleft, _, _, _⟩
  icases Hright with ⟨Hright, _, _, _⟩
  ihave %different := pointsTo_ne $$ Hleft Hright
  ipureintro
  intro same
  exact different (by subst right; rfl)

/-- Separating the actual source word slice from the four-byte output slot
derives the interval disjointness required by the operational certificate. -/
theorem WordSlice_output_disjoint [WasmHeapGS Universal.State]
    (ptr : UInt32) (values : List UInt32) (outputBytes : List UInt8)
    (houtput : outputBytes.length = 4) :
    WordSlice ptr values ∗ ByteSlice 1048572 outputBytes ⊢
      ⌜1048576 ≤ ptr.toNat ∨ ptr.toNat + 4 * values.length ≤ 1048572⌝ := by
  iintro ⟨Hwords, Houtput⟩
  ihave ⟨Hwords, %facts⟩ := WordSlice_facts ptr values $$ Hwords
  by_cases disjoint : 1048576 ≤ ptr.toNat ∨ ptr.toNat + 4 * values.length ≤ 1048572
  · ipureexact disjoint
  have start : ptr.toNat ≤ 1048572 := by omega
  let k := (1048572 - ptr.toNat) / 4
  have offset : ptr.toNat + 4 * k = 1048572 := by
    dsimp [k]
    omega
  have index : k < values.length := by omega
  have address : ptr + 4 * UInt32.ofNat k = 1048572 := by
    apply UInt32.toNat.inj
    rw [wordOffset_toNat ptr k (by omega)]
    exact offset
  ihave ⟨Hword, _⟩ := WordSlice_get ptr values k index $$ Hwords
  ihave ⟨Hslot, _⟩ := ByteSlice_storeAnyWordFocus 1048572 outputBytes
    houtput (by decide) $$ Houtput
  ihave %different : ⌜ptr + 4 * UInt32.ofNat k ≠ 1048572⌝ $$ [Hword Hslot]
  · iapply word_cells_ne (ptr + 4 * UInt32.ofNat k) 1048572 values[k]
      (Spec.decodeWord outputBytes)
    iframe Hword Hslot
  ipureintro
  exact False.elim (different address)

/-- The concrete local slots at the existing driver's output-loop boundary. -/
def driverAux (valuesPtr : UInt32) (values : List UInt32)
    (aux1 aux4 aux5 aux7 aux8 aux10 : UInt32) : OutputCost.Aux :=
  ⟨.i32 aux1, .i32 valuesPtr, .i32 aux4, .i32 aux5, .i32 aux7, .i32 aux8,
    .i32 (UInt32.ofNat values.length), .i32 aux10⟩

/-- Exactly the existing driver's resources at a positive output-loop entry. -/
def EntryResources [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (valuesId : Nat) (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes outputBytes : List UInt8) (values : List UInt32) :
    IProp (WasmHeapGF Universal.State) := iprop%
  RuntimeContext ∗ ExportFrame heapId capacity inputPtr input chunkBytes outputBytes ∗
    LiveWordBlock heapId valuesId valuesPtr values ∗ Streams [] [] false

/-- A caller-framed quantitative execution with the mathematical source list,
including its canonical output bytes on the same trace. -/
def OutputCertificate (store : MachineStore Universal.State) (aux : OutputCost.Aux)
    (valuesPtr : UInt32) (values : List UInt32) (ctx : OutputCost.OutputContext) : Prop :=
  ∃ trace finalStore,
    CostedSteps CostedStdIO.work (OutputCost.loopEntry store aux valuesPtr values.length ctx)
      trace (OutputCost.loopResume finalStore aux
        (valuesPtr + UInt32.ofNat (4 * values.length)) ctx) (26 * values.length + 2) ∧
    trace.length = 22 * values.length + 2 ∧
    finalStore.wasm.host.stdio.output = serialize values ∧
    finalStore.wasm.mem.pages = store.wasm.mem.pages

/-- Physical facts extracted from the existing driver's ownership. -/
structure PhysicalOutputFacts (store : MachineStore Universal.State)
    (valuesPtr : UInt32) (values : List UInt32) : Prop where
  module_eq : store.runtime.currentModule = Project.Mergesort.module
  host_eq : store.runtime.currentHost = Universal.envFor Project.Mergesort.module
  source_eq : store.wasm.mem.readWords32 valuesPtr values.length = values
  readable : valuesPtr.toNat + 4 * values.length ≤ store.wasm.mem.pages * 65536
  nowrap : valuesPtr.toNat + 4 * values.length < UInt32.size
  frame_readable : 1048576 ≤ store.wasm.mem.pages * 65536
  disjoint : 1048576 ≤ valuesPtr.toNat ∨ valuesPtr.toNat + 4 * values.length ≤ 1048572
  output_empty : store.wasm.host.stdio.output = []

/-- Instantiate the quantitative output theorem from the actual separation
resources. Physical source identity, read bounds, scratch separation, module,
host environment and initial output are all derived from ownership. -/
theorem physical_output_facts [WasmSmallStepGS hlc Universal.State]
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (heapId : GName) (valuesId : Nat) (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes outputBytes : List UInt8) (values : List UInt32)
    (hpositive : 0 < values.length) :
    stateInterp (GF := WasmHeapGF Universal.State) store steps observations threads ∗
      EntryResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes outputBytes values
      ==∗ ⌜PhysicalOutputFacts store valuesPtr values⌝ := by
  iintro ⟨Hstate, Hresources⟩
  isimp only [EntryResources, RuntimeContext, LiveWordBlock, Streams] at Hresources
  icases Hresources with ⟨⟨Hmodule, Henv⟩, Hframe,
    ⟨Htoken, Hwords, %_nonnull⟩, ⟨%random, Hhost⟩⟩
  ihave_pure moduleAgrees : ⌜store.runtime.currentModule = Project.Mergesort.module⌝ using
    stateInterp_runtimeModule_agree store steps observations threads ⟨0⟩ Project.Mergesort.module
    $$ [Hstate Hmodule]
  isimp only [runtimeModuleOwn] at Hmodule
  icases Hmodule with ⟨Helem, Hinstance⟩
  ihave_pure hostAgrees :
      ⌜store.runtime.currentHost = Universal.envFor Project.Mergesort.module⌝ using
    stateInterp_hostEnv store steps observations threads 0 (Universal.envFor Project.Mergesort.module)
    $$ [Hstate Hinstance Henv]
  ihave %hostState : ⌜store.wasm.host =
      ({ stdio := { input := [], output := [] }, random, oom := { raised := false } } :
        Universal.State)⌝ $$ [Hstate Hhost]
  · iapply stateInterp_host_agree store steps observations threads
    iframe Hstate Hhost
  isimp only [ExportFrame] at Hframe
  icases Hframe with ⟨Hvec, Hchunk, Hslot, %lengths⟩
  isimp only [show driverBase + 268 = (1048572 : UInt32) by decide] at Hslot
  ihave %disjoint : ⌜1048576 ≤ valuesPtr.toNat ∨
      valuesPtr.toNat + 4 * values.length ≤ 1048572⌝ $$ [Hwords Hslot]
  · iapply WordSlice_output_disjoint valuesPtr values outputBytes lengths.2
    iframe Hwords Hslot
  ihave_pure sourceFacts :
      ⌜store.wasm.mem.readWords32 valuesPtr values.length = values ∧
        valuesPtr.toNat + 4 * values.length ≤ store.wasm.mem.pages * 65536 ∧
        valuesPtr.toNat + 4 * values.length < UInt32.size⌝ using
    WordSlice_physical store steps observations threads valuesPtr values hpositive
    $$ [Hstate Hwords]
  isimp only [Representations.ByteSlice] at Hslot
  icases Hslot with ⟨%slotNowrap, HslotBytes⟩
  ihave_pure slotFacts :
      ⌜∀ i b, outputBytes[i]? = some b →
        store.wasm.mem.read8 ((1048572 : UInt32) + UInt32.ofNat i) = b ∧
        ((1048572 : UInt32) + UInt32.ofNat i).toNat < store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsToBytes_agree store steps observations threads 1048572 outputBytes
    $$ [Hstate HslotBytes]
  ipureintro
  have frameBound : 1048576 ≤ store.wasm.mem.pages * 65536 := by
    have bound := pointsToBytes_facts_bound slotFacts (by omega)
      (by simpa only [UInt32.size] using slotNowrap)
    simpa [lengths.2] using bound
  exact ⟨moduleAgrees, hostAgrees, sourceFacts.1, sourceFacts.2.1,
    sourceFacts.2.2, frameBound, disjoint, by rw [hostState]⟩

/-- The existing ownership instantiates the operational serialization theorem. -/
theorem output_certificate_of_resources [WasmSmallStepGS hlc Universal.State]
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (heapId : GName) (valuesId : Nat) (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes outputBytes : List UInt8) (values : List UInt32)
    (aux : OutputCost.Aux) (ctx : OutputCost.OutputContext)
    (hpositive : 0 < values.length) :
    stateInterp (GF := WasmHeapGF Universal.State) store steps observations threads ∗
      EntryResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes outputBytes values
      ==∗ ⌜OutputCertificate store aux valuesPtr values ctx⌝ := by
  iintro ⟨Hstate, Hresources⟩
  ihave_pure facts : ⌜PhysicalOutputFacts store valuesPtr values⌝ using
    physical_output_facts store steps observations threads heapId valuesId capacity inputPtr
      valuesPtr input chunkBytes outputBytes values hpositive $$ [Hstate Hresources]
  ipureintro
  obtain ⟨trace, finalStore, execution, length, output, pages⟩ :=
    OutputCost.output_loop_segment_serializes values.length hpositive store aux valuesPtr ctx
      facts.module_eq facts.host_eq (by have := facts.nowrap; omega)
      (by have := facts.nowrap; omega) facts.readable facts.frame_readable facts.disjoint
  refine ⟨trace, finalStore, execution, length, ?_, pages⟩
  rw [facts.source_eq, facts.output_empty, List.nil_append] at output
  exact output

/-- Pure execution extraction retains the original resources and state
interpretation, so the existing resource-transforming TWP remains usable. -/
theorem output_certificate_frame [WasmSmallStepGS hlc Universal.State]
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (heapId : GName) (valuesId : Nat) (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes outputBytes : List UInt8) (values : List UInt32)
    (aux : OutputCost.Aux) (ctx : OutputCost.OutputContext)
    (hpositive : 0 < values.length) :
    stateInterp (GF := WasmHeapGF Universal.State) store steps observations threads ∗
      EntryResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes outputBytes values
      ==∗ stateInterp (GF := WasmHeapGF Universal.State) store steps observations threads ∗
        EntryResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes outputBytes values ∗
        ⌜OutputCertificate store aux valuesPtr values ctx⌝ := by
  iintro ⟨Hstate, Hresources⟩
  ihave_pure certificate : ⌜OutputCertificate store aux valuesPtr values ctx⌝ using
    output_certificate_of_resources store steps observations threads heapId valuesId
      capacity inputPtr valuesPtr input chunkBytes outputBytes values aux ctx hpositive
    $$ [Hstate Hresources]
  imodintro
  iframe_pureexact certificate

/-- The physical successor store is independent of the surrounding caller.
This composes the existing per-iteration instruction certificates. -/
private theorem loop_common_store
    (n : Nat) (hpositive : 0 < n)
    (store : MachineStore Universal.State) (aux : OutputCost.Aux) (cursor : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[1]? = some CostedStdIO.writeHost)
    (hcount : 4 * n < UInt32.size)
    (haddress : cursor.toNat + 4 * n ≤ UInt32.size)
    (hread : cursor.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages * 65536) :
    ∃ finalStore, ∀ ctx : OutputCost.OutputContext, ∃ trace,
      CostedSteps CostedStdIO.work
        (OutputCost.loopHead store aux cursor (UInt32.ofNat (4 * n)) ctx) trace
        (OutputCost.loopResume finalStore aux (cursor + UInt32.ofNat (4 * n)) ctx)
        (26 * n + 1) ∧ trace.length = 22 * n + 1 := by
  induction n generalizing store cursor with
  | zero => omega
  | succ n ih =>
      by_cases zero : n = 0
      · subst n
        refine ⟨OutputCost.nextStore store cursor, ?_⟩
        intro ctx
        obtain ⟨trace, length, execution⟩ := OutputCost.iteration_exit_segment store aux cursor
          hmodule hhost (by simpa using hread) hframe ctx
        exact ⟨trace, execution, length⟩
      · have positive : 0 < n := by omega
        have cursorStep : (cursor + 4).toNat = cursor.toNat + 4 := by
          rw [UInt32.toNat_add]
          exact Nat.mod_eq_of_lt (by change cursor.toNat + 4 < UInt32.size; omega)
        have pages : (OutputCost.nextStore store cursor).wasm.mem.pages = store.wasm.mem.pages := rfl
        obtain ⟨finalStore, tails⟩ := ih positive (OutputCost.nextStore store cursor) (cursor + 4)
          hmodule hhost (by omega) (by rw [cursorStep]; omega)
          (by rw [cursorStep, pages]; omega) (by simpa only [pages] using hframe)
        refine ⟨finalStore, ?_⟩
        intro ctx
        obtain ⟨trace, length, execution⟩ := OutputCost.iteration_continue_cost store aux cursor n
          positive (by omega) hmodule hhost (by omega) hframe ctx
        obtain ⟨tail, tailExecution, tailLength⟩ := tails ctx
        have advance : (cursor + 4) + UInt32.ofNat (4 * n) =
            cursor + UInt32.ofNat (4 * (n + 1)) := by
          rw [Nat.mul_add, Nat.mul_one, UInt32.ofNat_add]
          change (cursor + 4) + UInt32.ofNat (4 * n) =
            cursor + (UInt32.ofNat (4 * n) + 4)
          ac_rfl
        refine ⟨trace ++ tail, ?_, ?_⟩
        · have combined := execution.trans tailExecution
          rw [advance] at combined
          convert combined using 1
          omega
        · simp only [List.length_append, length, tailLength]
          omega

/-- Every caller context reaches the same physical store. The exact segment
cost excludes any synthetic finish used by a closed resource proof. -/
theorem output_common_store
    (store : MachineStore Universal.State) (aux : OutputCost.Aux)
    (valuesPtr : UInt32) (values : List UInt32)
    (hpositive : 0 < values.length) (facts : PhysicalOutputFacts store valuesPtr values) :
    ∃ finalStore, ∀ ctx : OutputCost.OutputContext, ∃ trace,
      CostedSteps CostedStdIO.work (OutputCost.loopEntry store aux valuesPtr values.length ctx)
        trace (OutputCost.loopResume finalStore aux
          (valuesPtr + UInt32.ofNat (4 * values.length)) ctx) (26 * values.length + 2) ∧
        trace.length = 22 * values.length + 2 := by
  have resolved : store.runtime.currentHost.funcs[1]? = some CostedStdIO.writeHost := by
    rw [facts.host_eq]
    exact CostedStdIO.writeHost_resolves Project.Mergesort.module 1 (by decide) rfl
  obtain ⟨finalStore, bodies⟩ := loop_common_store values.length hpositive store aux valuesPtr
    facts.module_eq resolved (by have := facts.nowrap; omega) (by have := facts.nowrap; omega)
    facts.readable facts.frame_readable
  refine ⟨finalStore, ?_⟩
  intro ctx
  obtain ⟨trace, body, length⟩ := bodies ctx
  have entry : CostedSteps CostedStdIO.work (OutputCost.loopEntry store aux valuesPtr values.length ctx)
      [.instruction (.loop 0 0 OutputCost.outputBody)]
      (OutputCost.loopHead store aux valuesPtr (UInt32.ofNat (4 * values.length)) ctx) 1 :=
    CostedSteps.single Step.loop
  refine ⟨.instruction (.loop 0 0 OutputCost.outputBody) :: trace, ?_, ?_⟩
  · have combined := entry.trans body
    rw [show 1 + (26 * values.length + 1) = 26 * values.length + 2 by omega] at combined
    exact combined
  · simp only [List.length_cons, length]

/-- Ownership returned by the existing output-loop correctness theorem. -/
def ExitResources [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (valuesId : Nat) (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes : List UInt8) (values : List UInt32) :
    IProp (WasmHeapGF Universal.State) := iprop%
  ∃ finalOutput : List UInt8,
    RuntimeContext ∗ ExportFrame heapId capacity inputPtr input chunkBytes finalOutput ∗
      LiveWordBlock heapId valuesId valuesPtr values ∗ Streams [] (serialize values) false

/-- Closed use of the existing total-WP loop rule. Its sole extra finish
exposes client resources; it is not included in the caller-framed segment. -/
theorem output_closed_twp [WasmSmallStepGS hlc Universal.State]
    (store : MachineStore Universal.State)
    (heapId : GName) (valuesId : Nat) (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes outputBytes : List UInt8) (values : List UInt32)
    (aux1 aux4 aux5 aux7 aux8 aux10 : UInt32)
    (hpositive : 0 < values.length) (hbyteBound : 4 * values.length < UInt32.size)
    {s : Stuckness} {E : CoPset} :
    EntryResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes outputBytes values ⊢
      WP (OutputCost.loopEntry store
          (driverAux valuesPtr values aux1 aux4 aux5 aux7 aux8 aux10)
          valuesPtr values.length {}).expr @ s; E
        [{ fun _ : ObservableOutcome =>
          ExitResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes values }] := by
  have initial : (OutputCost.loopEntry store
      (driverAux valuesPtr values aux1 aux4 aux5 aux7 aux8 aux10)
      valuesPtr values.length {}).expr =
      (.running ⟨{ locals := [.i32 driverBase, .i32 aux1, .i32 valuesPtr,
          .i32 (valuesPtr + 4 * UInt32.ofNat 0), .i32 aux4, .i32 aux5,
          .i32 (UInt32.ofNat (4 * (values.length - 0))), .i32 aux7, .i32 aux8,
          .i32 (UInt32.ofNat values.length), .i32 aux10], values := [] },
        [.loop 0 0 OutputCost.outputBody], 0, [], [], []⟩ : Expr Universal.State) := by
    simp [OutputCost.loopEntry, OutputCost.outputLocals, driverAux, driverBase, entryStackTop]
  rw [initial]
  iintro Hresources
  have rule := DriverProof.twp_func3_output_loop heapId valuesId capacity inputPtr valuesPtr
    input chunkBytes outputBytes values aux1 aux4 aux5 aux7 aux8 aux10 hpositive hbyteBound
    (afterLoop := []) (arity := 0) (remainder := []) (controls := []) (calls := [])
    (s := s) (E := E) (Φ := fun _ : ObservableOutcome =>
      ExitResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes values)
  change iprop(
    RuntimeContext ∗ ExportFrame heapId capacity inputPtr input chunkBytes outputBytes ∗
    LiveWordBlock heapId valuesId valuesPtr values ∗ Streams [] [] false ∗
    (∀ finalOutput : List UInt8, RuntimeContext -∗
      ExportFrame heapId capacity inputPtr input chunkBytes finalOutput -∗
      LiveWordBlock heapId valuesId valuesPtr values -∗ Streams [] (serialize values) false -∗
      WP (.running ⟨{ locals := [.i32 driverBase, .i32 aux1, .i32 valuesPtr,
          .i32 (valuesPtr + 4 * UInt32.ofNat values.length), .i32 aux4, .i32 aux5,
          .i32 (UInt32.ofNat (4 * (values.length - values.length))), .i32 aux7, .i32 aux8,
          .i32 (UInt32.ofNat values.length), .i32 aux10], values := [] },
        [], 0, [], [], []⟩ : Expr Universal.State) @ s; E
        [{ fun _ : ObservableOutcome =>
          ExitResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes values }])) ⊢
      WP (.running ⟨{ locals := [.i32 driverBase, .i32 aux1, .i32 valuesPtr,
          .i32 (valuesPtr + 4 * UInt32.ofNat 0), .i32 aux4, .i32 aux5,
          .i32 (UInt32.ofNat (4 * (values.length - 0))), .i32 aux7, .i32 aux8,
          .i32 (UInt32.ofNat values.length), .i32 aux10], values := [] },
        [.loop 0 0 OutputCost.outputBody], 0, [], [], []⟩ : Expr Universal.State) @ s; E
        [{ fun _ : ObservableOutcome =>
          ExitResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes values }] at rule
  iapply rule
  isimp only [EntryResources] at Hresources
  icases Hresources with ⟨Hruntime, Hframe, Hvalues, Hstreams⟩
  isplitl_exacts [Hruntime Hframe Hvalues Hstreams]
  iintro %finalOutput Hruntime Hframe Hvalues Hstreams
  iapply (twp_finish (locals := { locals :=
    [.i32 driverBase, .i32 aux1, .i32 valuesPtr,
      .i32 (valuesPtr + 4 * UInt32.ofNat values.length), .i32 aux4, .i32 aux5,
      .i32 (UInt32.ofNat (4 * (values.length - values.length))), .i32 aux7, .i32 aux8,
      .i32 (UInt32.ofNat values.length), .i32 aux10] })
    (values := []) (arity := 0) (remainder := []) (s := s) (E := E))
  iapply Wasm.SmallStep.twp_outcome_done
  iunfold ExitResources
  iexists finalOutput
  iframe

/-- A caller-framed output execution and ownership for exactly its final
physical store. The mathematical serialization, cost, and resources describe
one trace. -/
def OutputExecution [WasmSmallStepGS hlc Universal.State]
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (heapId : GName) (valuesId : Nat) (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes : List UInt8) (values : List UInt32)
    (aux : OutputCost.Aux) (ctx : OutputCost.OutputContext) :
    IProp (WasmHeapGF Universal.State) := iprop%
  ∃ (trace : List StepKind) (finalStore : MachineStore Universal.State),
    ⌜CostedSteps CostedStdIO.work
        (OutputCost.loopEntry store aux valuesPtr values.length ctx) trace
        (OutputCost.loopResume finalStore aux
          (valuesPtr + UInt32.ofNat (4 * values.length)) ctx) (26 * values.length + 2) ∧
      trace.length = 22 * values.length + 2 ∧
      finalStore.wasm.host.stdio.output = serialize values ∧
      finalStore.wasm.mem.pages = store.wasm.mem.pages⌝ ∗
    stateInterp (GF := WasmHeapGF Universal.State) finalStore
      (steps + trace.length) observations threads ∗
    ExitResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes values

/-- Reuse the existing total-WP output proof to transform the actual driver
resources along the measured caller-framed execution. An auxiliary empty
context followed by one real finish exposes the resource postcondition;
context independence identifies its complete physical store with that of the
measured segment. No running continuation is inverted and the auxiliary
finish is not included in the reported cost or trace length. -/
theorem output_resources [WasmSmallStepGS hlc Universal.State]
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (heapId : GName) (valuesId : Nat) (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes outputBytes : List UInt8) (values : List UInt32)
    (aux1 aux4 aux5 aux7 aux8 aux10 : UInt32)
    (ctx : OutputCost.OutputContext) (hpositive : 0 < values.length)
    (E : CoPset) :
    stateInterp (GF := WasmHeapGF Universal.State) store steps observations threads ∗
      EntryResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes outputBytes values
      ={E}=∗ OutputExecution store steps observations threads heapId valuesId capacity inputPtr
        valuesPtr input chunkBytes values
        (driverAux valuesPtr values aux1 aux4 aux5 aux7 aux8 aux10) ctx := by
  let aux := driverAux valuesPtr values aux1 aux4 aux5 aux7 aux8 aux10
  iintro ⟨Hstate, Hresources⟩
  ihave_pure facts : ⌜PhysicalOutputFacts store valuesPtr values⌝ using
    physical_output_facts store steps observations threads heapId valuesId capacity inputPtr
      valuesPtr input chunkBytes outputBytes values hpositive $$ [Hstate Hresources]
  have hcount : 4 * values.length < UInt32.size := by have := facts.nowrap; omega
  obtain ⟨finalStore, contexts⟩ := output_common_store store aux valuesPtr values hpositive facts
  obtain ⟨trace, execution, length⟩ := contexts ctx
  obtain ⟨closedTrace, closedExecution, closedLength⟩ := contexts {}
  obtain ⟨serialTrace, serialStore, serialExecution, serialLength, output, pages⟩ :=
    OutputCost.output_loop_segment_serializes values.length hpositive store aux valuesPtr ctx
      facts.module_eq facts.host_eq hcount (by have := facts.nowrap; omega)
      facts.readable facts.frame_readable facts.disjoint
  have same := Steps.final_eq_of_length_eq execution.erase serialExecution.erase
    (by omega)
  have stores : finalStore = serialStore := congrArg Config.store same
  rw [← stores, facts.source_eq, facts.output_empty, List.nil_append] at output
  rw [← stores] at pages
  have finish : Step (OutputCost.loopResume finalStore aux
      (valuesPtr + UInt32.ofNat (4 * values.length)) {}) (.administrative .finish)
      ⟨.done [], finalStore⟩ := Step.finish
  have closedRun := closedExecution.erase.trans (Steps.single finish)
  ihave Hwp := output_closed_twp store heapId valuesId capacity inputPtr valuesPtr input
    chunkBytes outputBytes values aux1 aux4 aux5 aux7 aux8 aux10 hpositive hcount
    (s := .NotStuck) (E := E) $$ Hresources
  imod twp_replay_value (s := .NotStuck) (E := E)
      (post := fun _ : ObservableOutcome =>
        ExitResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes values) closedRun (ObservableOutcome.done []) ⟨rfl⟩
      steps observations threads $$ [Hstate Hwp] with ⟨HfinalState, Hpost⟩
  · isimp only [OutputCost.loopEntry] at Hwp
    isimp only [OutputCost.loopEntry]
    iframe Hstate Hwp
  imodintro
  iunfold OutputExecution
  iexists trace, finalStore
  isplitr_pureexact ⟨execution, length, output, pages⟩
  isplitl [HfinalState]
  · -- The current Wasm state interpretation ignores its counter arguments.
    -- Thus the auxiliary finish changes neither this assertion nor the store;
    -- the actual caller-framed trace and its reported length remain unchanged.
    iexact HfinalState
  iexact Hpost

/-- Project the stronger costed result into the reusable sequential resource
interface. The original `OutputExecution` additionally retains exact work. -/
theorem OutputExecution.to_sequential [WasmSmallStepGS hlc Universal.State]
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (heapId : GName) (valuesId : Nat) (capacity inputPtr valuesPtr : UInt32)
    (input chunkBytes : List UInt8) (values : List UInt32)
    (aux : OutputCost.Aux) (ctx : OutputCost.OutputContext) :
    OutputExecution store steps observations threads heapId valuesId capacity inputPtr valuesPtr
      input chunkBytes values aux ctx ⊢
    SequentialExecution (OutputCost.loopEntry store aux valuesPtr values.length ctx)
      steps observations threads (22 * values.length + 2) (fun final => iprop(
        ⌜final.expr = (OutputCost.loopResume final.store aux
            (valuesPtr + UInt32.ofNat (4 * values.length)) ctx).expr ∧
          final.store.wasm.host.stdio.output = serialize values ∧
          final.store.wasm.mem.pages = store.wasm.mem.pages⌝ ∗
        ExitResources heapId valuesId capacity inputPtr valuesPtr input chunkBytes values)) := by
  iintro H
  iunfold OutputExecution at H
  icases H with ⟨%trace, %finalStore, %evidence, Hstate, Hpost⟩
  iunfold SequentialExecution
  iexists trace, (OutputCost.loopResume finalStore aux
    (valuesPtr + UInt32.ofNat (4 * values.length)) ctx)
  isplitr_pureexact ⟨evidence.1.erase, by omega⟩
  isplitl [Hstate]
  · isimp only [OutputCost.loopResume]
    iexact Hstate
  isplitr_pureexact ⟨rfl, evidence.2.2.1, evidence.2.2.2⟩
  iexact Hpost

end Project.Mergesort.OutputResources
