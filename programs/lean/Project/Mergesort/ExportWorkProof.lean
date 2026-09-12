import Project.Mergesort.InputInitializationCost
import Project.Mergesort.InputExecutionCost
import Project.Mergesort.DriverCompletionCost
import Project.Mergesort.GrowingTotalProof
import CodeLib.SepLogic.CostedTerminalBounds

/-! # Numerical work of the complete named mergesort export

The bound charges authoritative semantic transitions, bulk memory bytes,
transferred host bytes and newly added physical bytes. It is a bound on modeled
work, not elapsed time or interpreter implementation complexity.
-/

namespace Project.Mergesort.ExportWorkProof

open Wasm Wasm.SmallStep Project.Mergesort.Representations
open Project.Mergesort.DriverProof Project.Mergesort.TotalProof
open Project.Mergesort.InputInitializationCost Project.Mergesort.InputLoopCost

/-- Closed numerical bound for n input words under the canonical byte-work
model. The page term uses the existing all-prefix physical-memory bound. -/
def workBound (input : List UInt32) : Nat :=
  let n := input.length
  54*n*Nat.clog 2 (n+1)+200*n+259*((4*n+255)/256)+583+
    65536*(Spec.growingPageBound input-17)

set_option maxRecDepth 65536 in
/-- The actual named export returns normally within the numerical budget.
The only public precondition is the covered input-size range. -/
theorem export_cost (input : List UInt32) (hbound : input.length≤89434754) :
    ∃ trace store amount,
      CostedSteps CostedStdIO.work (exportConfig input) trace ⟨.done [],store⟩ amount ∧
      trace.length≤amount ∧ amount≤workBound input := by
  by_cases hz : input=[]
  · subst input
    obtain ⟨trace,body⟩ := DriverDispatchCost.empty_export_body_cost
    have finish : CostedSteps CostedStdIO.work
        ⟨.running ⟨DriverDispatchCost.emptyReadyLocals,[],0,[],[],[]⟩,
          DriverDispatchCost.restoredStore (DriverDispatchCost.canonicalInitializedStore [])⟩
        [.administrative .finish]
        ⟨.done [],DriverDispatchCost.restoredStore (DriverDispatchCost.canonicalInitializedStore [])⟩ 1 :=
      CostedSteps.single Step.finish
    have run := body.trans finish
    exact ⟨_,_,339,run,run.length_le (fun _ _ _ _ => byteWork_positive _ _ _ _),by decide⟩
  · have hp : 0 < input.length := List.length_pos_iff_ne_nil.mpr hz
    have fit := GrowingMemoryBounds.workArraysFit_of_word_count input hbound
    have fitWords : MemoryBounds.WorkArraysFit (4*input.length) := by
      simpa only [serialize_length] using fit
    obtain ⟨entryTrace,entryRun,initialInv,initialPages,positive⟩ := export_to_head_cost input hz
    obtain ⟨read⟩ := InputExecutionCost.loop_cost (4*input.length) (canonicalReadStore input)
      (canonicalState input) {} canonicalContext initialInv positive fitWords
    have hremaining : read.store.wasm.host.stdio.input.length=0 := by
      have hs := read.invariant.chunk_shape
      rw [read.exhausted] at hs
      omega
    have hlength : read.state.length=4*input.length := by
      have ht := read.invariant.total_eq
      rw [read.exhausted,hremaining] at ht
      omega
    have hsigned : 4*input.length<2147483648 := by
      unfold MemoryBounds.WorkArraysFit workArraysFrontierBound at fitWords
      omega
    have hfixed : driverBase.toNat+4+4≤read.store.wasm.mem.pages*65536 :=
      le_trans (by decide) (Nat.mul_le_mul_right 65536 read.invariant.pages_lower)
    obtain ⟨dispatchTrace,dispatch⟩ := DriverDispatchCost.completed_nonempty_cost read.store
      read.state.dataPtr input.length [] hp hsigned read.invariant.header_pointer hfixed
      CostedStdIO.hostBytes
    have readRun : CostedSteps CostedStdIO.work (exportConfig input) (entryTrace++read.trace)
        ⟨.running ⟨func3AppendLocals read.state.dataPtr 0 (UInt32.ofNat (4*input.length))
          4 0 0 0 0 0 0 [],DriverDispatchCost.completedCode,0,[],
          DriverDispatchCost.completedControls,[]⟩,read.store⟩
        (299+(canonicalState input).current+read.amount) := by
      have run := entryRun.trans read.run
      simpa only [InputExecutionCost.done,stateLocals,read.exhausted,hlength,
        func3AppendLocals,canonicalContext,show UInt32.ofNat 0=(0:UInt32) from rfl] using run
    have hgeo : BoundedGeometricVecFacts (4*input.length) (4*input.length) 0
        read.state.capacity read.state.dataPtr read.state.frontier read.state.history := by
      simpa only [read.exhausted,hlength,hremaining,Nat.zero_add] using read.invariant.lineage
    have hsourceEnd : read.state.dataPtr.toNat+4*input.length≤read.state.frontier := by
      have hc := read.invariant.length_capacity
      have hf := read.invariant.allocation_frontier
      omega
    have hsourceWrap : read.state.dataPtr.toNat+4*input.length<UInt32.size := by
      have hf := read.invariant.frontier_signed
      norm_num [UInt32.size]
      omega
    obtain ⟨tailTrace,finalStore,finalLocals,tailAmount,tailRun,grow,_,tailBound⟩ :=
      DriverCompletionCost.complete_cost read.store input.length read.state.dataPtr read.state.capacity
        read.state.storedCursor read.state.frontier read.state.history [] hp hgeo fitWords
        read.invariant.module read.invariant.host read.invariant.cap read.invariant.pages_upper
        hsourceWrap (hsourceEnd.trans read.invariant.frontier_physical) read.invariant.cursor
        read.invariant.effective (fixed_ranges read.invariant).2
        (le_trans (by decide) (Nat.mul_le_mul_right 65536 read.invariant.pages_lower))
        (by rw [read.invariant.global];rfl)
    have finish : CostedSteps CostedStdIO.work
        ⟨.running ⟨finalLocals,[],0,[],[],[]⟩,finalStore⟩ [.administrative .finish]
        ⟨.done [],finalStore⟩ 1 := CostedSteps.single Step.finish
    have run := ((readRun.trans dispatch).trans tailRun).trans finish
    have finalPageBound : finalStore.wasm.mem.pages≤Spec.growingPageBound input := by
      have pages := GrowingTotalProof.export_pages_bounded_at_every_prefix input fit run.erase
      simpa only [GrowingMemoryBounds.programPageBound_public_formula,Spec.growingPageBound] using pages
    refine ⟨_,finalStore,_,run,run.length_le (fun _ _ _ _ => byteWork_positive _ _ _ _),?_⟩
    have chunkPartition : (canonicalState input).current+
        (canonicalReadStore input).wasm.host.stdio.input.length=4*input.length := by
      have ht := initialInv.total_eq
      change 4*input.length=0+_+_ at ht
      omega
    have capBound := read.invariant.lineage.2
    have inputBound := read.charge
    change read.amount≤InputWorkBudget.budget (canonicalState input).current
      (canonicalReadStore input).wasm.host.stdio.input.length 0
      (canonicalReadStore input).wasm.mem.pages read.state.capacity.toNat read.store.wasm.mem.pages at inputBound
    unfold InputWorkBudget.budget at inputBound
    rw [chunkPartition,initialPages,Nat.sub_zero] at inputBound
    have sortBound := SortWorkBudget.budget_log_bound input.length
    have telescope : read.store.wasm.mem.pages-17+(finalStore.wasm.mem.pages-read.store.wasm.mem.pages)=
        finalStore.wasm.mem.pages-17 := by
      have hp := read.invariant.pages_lower
      omega
    have growthBound : 65536*(read.store.wasm.mem.pages-17)+
        65536*(finalStore.wasm.mem.pages-read.store.wasm.mem.pages)≤
        65536*(Spec.growingPageBound input-17) := by
      rw [← Nat.mul_add,telescope]
      omega
    dsimp only [workBound]
    unfold InputWorkBudget.chunks at inputBound
    omega

/-- Functional output and the numerical work certificate describe the very
same normal-return trace and terminal store. Every finite prefix obeys both
the work bound and the existing physical-page bound. -/
theorem named_export_work (input : List UInt32) (hbound : input.length≤89434754) :
    ∃ initial : Config Universal.State,
      startExportConfig? (Universal.envFor Project.Mergesort.module) Project.Mergesort.module
        "mergesort" (Spec.args input)=some initial ∧
      (∃ trace store amount output,
        CostedSteps CostedStdIO.work initial trace ⟨.done [],store⟩ amount ∧
        trace.length≤amount ∧ amount≤workBound input ∧
        store.wasm.host.stdio.output=Spec.encodeValues output ∧
        Spec.SortedPermutation input output) ∧
      (∀ trace reached amount,
        CostedSteps CostedStdIO.work initial trace reached amount →
        amount≤workBound input ∧ reached.store.wasm.mem.pages≤Spec.growingPageBound input) := by
  have fit := GrowingMemoryBounds.workArraysFit_of_word_count input hbound
  obtain ⟨trace,store,amount,run,lengthBound,bound⟩ := export_cost input hbound
  have post := GrowingTotalProof.terminal_execution_normal input fit
    (outcome := .done []) run.erase
  have sorted : Spec.Post input ⟨.done [],store.wasm.host⟩ := by
    rcases post.2.1.1 with hoom | hsuccess
    · cases hoom.1
    · exact hsuccess
  obtain ⟨output,returned,permutation⟩ := sorted
  refine ⟨exportConfig input,startExportConfig_eq input,
    ⟨trace,store,amount,output,run,lengthBound,bound,returned.2,permutation⟩,?_⟩
  intro prefixTrace reached prefixAmount prefixRun
  refine ⟨(run.amount_le_normal_return prefixRun).trans bound,?_⟩
  have pages := GrowingTotalProof.export_pages_bounded_at_every_prefix input fit prefixRun.erase
  simpa only [GrowingMemoryBounds.programPageBound_public_formula,Spec.growingPageBound] using pages

/-- The non-growing regime removes the physical growth charge from the closed
budget. This is an arithmetic specialization of the complete export theorem. -/
theorem workBound_no_growth (input : List UInt32) (hbound : input.length≤2690) :
    workBound input=54*input.length*Nat.clog 2 (input.length+1)+200*input.length+
      259*((4*input.length+255)/256)+583 := by
  have pages : Spec.growingPageBound input=17 := by
    unfold Spec.growingPageBound
    omega
  simp only [workBound,pages,Nat.sub_self,Nat.mul_zero,Nat.add_zero]

end Project.Mergesort.ExportWorkProof
