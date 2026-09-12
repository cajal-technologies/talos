import Project.Mergesort.InputLoopCost
import Project.Mergesort.DriverDispatchCost

/-! # Initial physical invariant after the actual first input read -/

namespace Project.Mergesort.InputInitializationCost

open Wasm Wasm.SmallStep Project.Mergesort.Representations
open Project.Mergesort.InputCost Project.Mergesort.InputLoopCost

def initialState (store : MachineStore Universal.State) : State :=
  ⟨0,1,0,readCount store 256,0,heapBase.toNat,AllocationHistory.empty⟩

/-- The first read constructs the complete physical input invariant. The
premises describe its initial store only, including the actual header/cursor. -/
theorem initial_invariant (store : MachineStore Universal.State)
    (hcapacity : store.wasm.mem.read32 driverBase=0)
    (hpointer : store.wasm.mem.read32 (driverBase+4)=1)
    (hlength : store.wasm.mem.read32 (driverBase+8)=0)
    (hcursor : store.wasm.mem.read32 allocatorCursor=0)
    (hmodule : store.runtime.currentModule=Project.Mergesort.module)
    (hhost : store.runtime.currentHost=Universal.envFor Project.Mergesort.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0=Module.memoryHardCap)
    (hglobal : globalAt? store 0=some (.i32 driverBase))
    (hpages : store.wasm.mem.pages=17) :
    Invariant store.wasm.host.stdio.input.length
      (readResult store 256 (driverBase+12)) (initialState store) := by
  have hcount := readCount_bound store
  have hcountLe : readCount store 256≤store.wasm.host.stdio.input.length := min_le_right _ _
  have partition : readCount store 256+(store.wasm.host.stdio.input.drop (readCount store 256)).length=
      store.wasm.host.stdio.input.length := by rw [List.length_drop]; omega
  have capRead := readResult_metadata store 256 (driverBase+12) driverBase
    (Or.inl (by decide))
  have ptrRead := readResult_metadata store 256 (driverBase+12) (driverBase+4)
    (Or.inl (by decide))
  have lenRead := readResult_metadata store 256 (driverBase+12) (driverBase+8)
    (Or.inl (by decide))
  have cursorRead := readResult_metadata store 256 (driverBase+12) allocatorCursor
    (Or.inr (by
      have : (driverBase+12).toNat+256≤allocatorCursor.toNat := by decide
      omega))
  constructor
  · change _=0+readCount store 256+_
    rw [readResult_input]
    simpa only [Nat.zero_add] using partition.symm
  · change readCount store 256=min 256 (readCount store 256+_)
    rw [readResult_input,partition]
    rfl
  · change BoundedGeometricVecFacts _ 0 (readCount store 256+_) 0 1 heapBase.toNat AllocationHistory.empty
    rw [readResult_input,partition]
    exact MemoryBounds.BoundedGeometricVecFacts.initial _
  · exact capRead.trans hcapacity
  · exact ptrRead.trans hpointer
  · exact lenRead.trans hlength
  · exact cursorRead.trans hcursor
  · rfl
  · exact hmodule
  · exact hhost
  · exact hcap
  · exact hglobal
  · change 17≤store.wasm.mem.pages
    omega
  · change store.wasm.mem.pages≤Module.memoryHardCap
    rw [hpages]; decide
  · exact Nat.zero_le _
  · change 1+0≤1049536
    decide
  · change heapBase.toNat≤store.wasm.mem.pages*65536
    rw [hpages]; decide
  · change 1049536<2147483648
    decide
  · intro hz
    exact False.elim (hz rfl)

def canonicalContext : InputControlCost.Context :=
  { afterLoop := DriverDispatchCost.completedCode,controls := DriverDispatchCost.completedControls }

abbrev canonicalReadStore (input : List UInt32) : MachineStore Universal.State :=
  readResult (DriverDispatchCost.canonicalInitializedStore input) 256 (driverBase+12)

abbrev canonicalState (input : List UInt32) : State :=
  initialState (DriverDispatchCost.canonicalInitializedStore input)

set_option maxRecDepth 65536 in
/-- The canonical named-export initializer, complete prologue, first host read
and loop entry establish the physical invariant without additional premises. -/
theorem export_to_head_cost (input : List UInt32) (hne : input≠[]) :
    ∃ trace, CostedSteps CostedStdIO.work (TotalProof.exportConfig input) trace
      (InputControlCost.head (canonicalReadStore input) (stateLocals (canonicalState input) {})
        canonicalContext) (299+(canonicalState input).current) ∧
      Invariant (4*input.length) (canonicalReadStore input) (canonicalState input) ∧
      (canonicalReadStore input).wasm.mem.pages=17 ∧ 0<(canonicalState input).current := by
  rcases DriverDispatchCost.canonical_initialized_metadata input with
    ⟨hp,hc,hptr,hlen,hcursor,hglobal,hmodule,hhost,hcap,hinput,_⟩
  have hn : (DriverDispatchCost.canonicalInitializedStore input).wasm.host.stdio.input≠[] := by
    rw [hinput]
    intro hz
    have hlength := congrArg List.length hz
    rw [serialize_length] at hlength
    have : 0 < input.length := List.length_pos_iff_ne_nil.mpr hne
    simp only [List.length_nil] at hlength
    omega
  have inv := initial_invariant (DriverDispatchCost.canonicalInitializedStore input)
    hc hptr hlen hcursor hmodule hhost hcap hglobal hp
  rw [hinput,serialize_length] at inv
  obtain ⟨entryTrace,entry⟩ := DriverDispatchCost.export_to_read_cost input
  obtain ⟨readTrace,_,read⟩ := InputControlCost.initial_nonempty_cost
    (DriverDispatchCost.canonicalInitializedStore input) canonicalContext hn hmodule hhost
    (by rw [hp];decide)
  have hpositive : 0<(canonicalState input).current := by
    have hcount := readCount_zero_iff (DriverDispatchCost.canonicalInitializedStore input)
    change 0<readCount (DriverDispatchCost.canonicalInitializedStore input) 256
    have hnot : readCount (DriverDispatchCost.canonicalInitializedStore input) 256≠0 := by
      intro hz;exact hn (hcount.mp hz)
    omega
  refine ⟨entryTrace++readTrace,?_,inv,hp,hpositive⟩
  convert entry.trans read using 1 <;> first | rfl |
    (dsimp only [canonicalState,initialState]; omega)

end Project.Mergesort.InputInitializationCost
