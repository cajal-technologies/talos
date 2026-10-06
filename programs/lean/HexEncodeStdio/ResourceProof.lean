import HexEncodeStdio.ReadToEndExecutionCost
import HexEncodeStdio.ExportResourceCost
import HexEncodeStdio.OutputAllocationResources
import HexEncodeStdio.EncoderCompletionResources
import HexEncodeStdio.ResourceBounds

/-! # Resources of the complete named hex encoder

The certificates follow the generated program from named-export initialization
through normal return. Work charges semantic transitions, bulk memory bytes,
actual host transfer bytes, and newly added physical memory bytes.
-/

namespace Project.HexEncodeStdio.ResourceProof

open Wasm Wasm.SmallStep Project.HexStdio
open ExportResourceCost
open ResourceBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The empty export executes its reader, sentinel iterator, empty writer,
cleanup and final return without allocating or increasing physical memory. -/
theorem empty_export_cost :
    ∃ trace store amount,
      CostedSteps CostedStdIO.work (encodeInitialConfig []) trace ⟨.done [], store⟩ amount ∧
      (∀ kind ∈ trace, HostPrimaryMemoryKind kind) ∧
      store.wasm.mem.pages = 17 ∧ amount ≤ 440 := by
  obtain ⟨readTrace, readAmount, readBound, readRun, readLabels⟩ :=
    ReadToEndResourceCost.empty_cost
  obtain ⟨hmodule, _, hpages, hcapacity, hpointer, hlength, hglobal, _⟩ :=
    ReadToEndResourceCost.empty_store_facts
  obtain ⟨tailTrace, tailRun, tailLabels⟩ := empty_after_read_cost
    ReadToEndResourceCost.emptyStore 1 hmodule hcapacity hpointer hlength hglobal (by omega)
  have run := ((export_to_read_cost []).trans readRun).trans tailRun
  refine ⟨_, _, _, run, ?_, ?_, by omega⟩
  · intro kind member
    simp only [List.mem_append] at member
    rcases member with (entry | read) | tail
    · exact entryTrace_primary kind entry
    · exact readLabels kind read
    · exact tailLabels kind tail
  · simpa only [restoredMainStore, WriteResourceCost.writeAllEmptyResultStore,
      WriteResourceCost.writeAllFrameStore, emptyEncodedStore, EncodeResourceCost.finishStore,
      EncodeResourceCost.iteratorResetStore, emptyEncoderStore, encodeAllocFrameStore,
      Mem.write32_pages, Mem.write64_pages] using hpages

/-- Construct the complete nonempty invocation. Both physical growth charges
telescope from the initial seventeen pages to the same final store. -/
theorem nonempty_export_cost (input : List UInt8) (hne : input ≠ [])
    (hfit : ReadToEndResourceCost.InputFits input.length) :
    ∃ trace store amount,
      CostedSteps CostedStdIO.work (encodeInitialConfig input) trace ⟨.done [], store⟩ amount ∧
      (∀ kind ∈ trace, HostPrimaryMemoryKind kind) ∧
      store.wasm.mem.pages ≤ pageBound input ∧ amount ≤ workBound input := by
  have hn : 0 < input.length := List.length_pos_iff_ne_nil.mpr hne
  obtain ⟨readFinal, readTrace, readAmount, reader, readLabels, readSuccess,
    frontier, readPages, readBound⟩ := ReadToEndResourceCost.nonempty_call_cost input hne hfit
  have readShape : readFinal = encodeAfterReadConfig readFinal.store := by
    rcases readSuccess with ⟨store, capacity, pointer, bump, hconfig, _⟩
    rw [hconfig]
    rfl
  have hread : ReadToEndSuccess input (encodeAfterReadConfig readFinal.store) := by
    rw [← readShape]
    exact readSuccess
  have readRuntime := reader.erase.hostPrimaryMemory_runtime readLabels
  have readModule : readFinal.store.runtime.currentModule = Project.HexStdio.module := by
    rw [readRuntime]
    rfl
  have readHost : readFinal.store.runtime.currentHost = Universal.envFor Project.HexStdio.module := by
    rw [readRuntime]
    rfl
  have readLower : 17 ≤ readFinal.store.wasm.mem.pages :=
    reader.erase.primary_pages_mono_with_hosts (Universal.envFor_preservesPrimaryPages _) readLabels
  obtain ⟨inputCapacity, pointer, bump, allocationTrace, hcapacity, hpointer, hbump,
    allocationLength, allocation, success, allocationLabels⟩ :=
    OutputAllocationCost.after_read_reserve_cost input readFinal.store hne hfit hread frontier
  have facts := OutputAllocationResources.reserved_facts input readFinal.store inputCapacity pointer bump
    hne hfit hcapacity hpointer hbump hread (by rwa [hbump] at frontier) success
  let reserved := OutputAllocationCost.reservedStore input readFinal.store bump
  have reservedModule : reserved.runtime.currentModule = Project.HexStdio.module := by
    rw [facts.runtime_eq]
    exact readModule
  have reservedHost : reserved.runtime.currentHost = Universal.envFor Project.HexStdio.module := by
    rw [facts.runtime_eq]
    exact readHost
  have capacityBound : 2 * input.length ≤ (OutputAllocationCost.outputCapacity input).toNat := by
    rw [facts.capacity_nat]
    omega
  obtain ⟨memory, encodeTrace, encoder, encodeLabels, fields, frame⟩ :=
    EncodeFunctionResourceCost.after_allocation_cost reserved pointer (UInt32.ofNat input.length)
      (OutputAllocationCost.outputCapacity input) (allocatorPtr bump 1) input.length
      reservedModule facts.global_eq facts.length_nat hn facts.capacity_eq facts.output_eq facts.zero_eq
      capacityBound facts.source_lower facts.source_physical facts.source_noWrap
      facts.output_lower facts.output_physical facts.output_noWrap facts.table_ascii
  obtain ⟨tailTrace, tail, tailLabels, _, finalPages, _⟩ :=
    EncoderCompletionResources.after_encoder_cost reserved memory pointer inputCapacity
      (allocatorPtr bump 1) (OutputAllocationCost.outputCapacity input)
      (pointer + UInt32.ofNat input.length) input.length reservedModule reservedHost facts.global_eq
      fields frame facts.input_capacity_eq facts.input_capacity_ne hn capacityBound
      facts.output_lower facts.output_physical facts.output_noWrap
  rw [readShape] at reader
  rw [OutputAllocationResources.reserved_config_eq input readFinal.store inputCapacity pointer bump facts]
    at allocation
  have run := ((((export_to_read_cost input).trans reader).trans allocation).trans encoder).trans tail
  have inputPages : readFinal.store.wasm.mem.pages ≤ pageBound input := by
    unfold pageBound ReadToEndResourceCost.completeFrontierBound AllocatorResourceCost.requiredPages at *
    omega
  have outputPages : reserved.wasm.mem.pages ≤ pageBound input := by
    have bound := facts.pages_bound
    change reserved.wasm.mem.pages ≤ max readFinal.store.wasm.mem.pages
      (AllocatorResourceCost.requiredPages (ReadToEndResourceCost.completeFrontierBound input.length)) at bound
    unfold pageBound at inputPages ⊢
    omega
  refine ⟨_, _, _, run, ?_, finalPages.trans_le outputPages, ?_⟩
  · intro kind member
    simp only [List.mem_append] at member
    rcases member with (((entry | read) | allocation) | encode) | tail
    · exact entryTrace_primary kind entry
    · exact readLabels kind read
    · exact allocationLabels kind allocation
    · exact encodeLabels kind encode
    · exact tailLabels kind tail
  · have base : allocatorBase bump = bump :=
      (AllocatorResourceCost.ptr_one bump).symm.trans facts.pointer_eq
    have pages := facts.pages_eq
    have growth :
        (readFinal.store.wasm.mem.pages - 17) +
          (AllocatorResourceCost.requiredPages
            ((allocatorBase bump).toNat + (OutputAllocationCost.outputCapacity input).toNat) -
            readFinal.store.wasm.mem.pages) = reserved.wasm.mem.pages - 17 := by
      rw [base]
      change reserved.wasm.mem.pages = _ at pages
      omega
    have growthBound :
        65536 * (readFinal.store.wasm.mem.pages - 17) +
          65536 * (AllocatorResourceCost.requiredPages
            ((allocatorBase bump).toNat + (OutputAllocationCost.outputCapacity input).toNat) -
            readFinal.store.wasm.mem.pages) ≤ 65536 * (pageBound input - 17) := by
      rw [← Nat.mul_add, growth]
      omega
    unfold workBound
    omega

/-- A complete normal-return certificate from the actual export body, under
only the explicit initial input-size bound. -/
theorem export_cost (input : List UInt8) (hbound : input.length ≤ 357738263) :
    ∃ trace store amount,
      CostedSteps CostedStdIO.work (encodeInitialConfig input) trace ⟨.done [], store⟩ amount ∧
      (∀ kind ∈ trace, HostPrimaryMemoryKind kind) ∧
      trace.length ≤ amount ∧ amount ≤ workBound input ∧ store.wasm.mem.pages ≤ pageBound input := by
  by_cases he : input = []
  · subst input
    obtain ⟨trace, store, amount, run, labels, pages, bound⟩ := empty_export_cost
    exact ⟨trace, store, amount, run, labels,
      run.length_le (fun _ _ _ _ => byteWork_positive _ _ _ _),
      by rw [empty_bounds.2]; omega, by rw [pages, empty_bounds.1]⟩
  · obtain ⟨trace, store, amount, run, labels, pages, bound⟩ := nonempty_export_cost input he
      ((inputFits_iff input.length).mpr hbound)
    exact ⟨trace, store, amount, run, labels,
      run.length_le (fun _ _ _ _ => byteWork_positive _ _ _ _), bound, pages⟩

/-- The named export returns the correct hex encoding within one numerical
budget. Every finite execution from its canonical initializer obeys the same
physical-page bound, and every costed prefix obeys the same work bound. -/
theorem named_export_resources (input : List UInt8) (hbound : input.length ≤ 357738263) :
    ∃ initial : Config Universal.State,
      startConfig? (Universal.envFor Project.HexStdio.module) Project.HexStdio.module "encode"
        (Universal.State.ofInput input) = some initial ∧
      (∃ trace store amount,
        CostedSteps CostedStdIO.work initial trace ⟨.done [], store⟩ amount ∧
        store.wasm.host.stdio.output = Spec.encode input ∧
        trace.length ≤ amount ∧ amount ≤ workBound input) ∧
      (∀ trace reached, Steps initial trace reached →
        17 ≤ reached.store.wasm.mem.pages ∧ reached.store.wasm.mem.pages ≤ pageBound input) ∧
      (∀ trace reached amount, CostedSteps CostedStdIO.work initial trace reached amount →
        trace.length ≤ amount ∧ amount ≤ workBound input) := by
  obtain ⟨trace, store, amount, run, labels, lengthBound, bound, pages⟩ := export_cost input hbound
  have output := (normal_return_correct input run.erase).2
  refine ⟨encodeInitialConfig input, encode_start_config input,
    ⟨trace, store, amount, run, output, lengthBound, bound⟩, ?_, ?_⟩
  · intro prefixTrace reached execution
    have prefixPages := run.erase.primary_pages_at_every_prefix_of_normal_return
      (Universal.envFor_preservesPrimaryPages _) labels execution
    exact ⟨prefixPages.1, prefixPages.2.trans pages⟩
  · intro prefixTrace reached prefixAmount execution
    exact ⟨execution.length_le (fun _ _ _ _ => byteWork_positive _ _ _ _),
      (run.amount_le_normal_return execution).trans bound⟩

end Project.HexEncodeStdio.ResourceProof
