import HexEncodeStdio.EncodeFunctionResourceCost
import HexEncodeStdio.ExportResourceCost

/-! Connect the encoder's actual completed memory to the complete main suffix. -/
namespace Project.HexEncodeStdio.EncoderCompletionResources

open Wasm Wasm.SmallStep Project.HexStdio
open EncodeResourceCost EncodeFunctionResourceCost

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Words wholly outside the encoder frame and before its output allocation
are unchanged by the complete operational encoder loop. -/
theorem framed_read32 {before after : Mem} {output : UInt32}
    (frame : Framed before after output) (address : UInt32)
    (outside : address.toNat+4≤1048516 ∨ 1048544≤address.toNat)
    (beforeOutput : address.toNat+4≤output.toNat) :
    after.read32 address=before.read32 address := by
  simp only [Wasm.Mem.read32]
  rw [frame.2 _ (by omega) (by omega),frame.2 _ (by omega) (by omega),
    frame.2 _ (by omega) (by omega),frame.2 _ (by omega) (by omega)]

/-- The epilogue's vector stores are disjoint from the caller's input header. -/
theorem completed_input_capacity (store : MachineStore Universal.State) (memory : Mem)
    (output inputCapacity : UInt32) (n : Nat)
    (frame : Framed store.wasm.mem memory output)
    (hinput : store.wasm.mem.read32 1048552=inputCapacity)
    (houtput : 1048592≤output.toNat) :
    (completedStore store memory n).wasm.mem.read32 1048552=inputCapacity := by
  simp only [completedStore,finishStore,EncodeLoopResourceCost.memoryStore]
  rw [Wasm.Mem.read32_write64_disjoint _ _ _ _ (by decide),
    Wasm.Mem.read32_write32_disjoint _ _ _ _ (by decide)]
  rw [framed_read32 frame 1048552 (by decide) (by change 1048552+4≤output.toNat;omega)]
  exact hinput

theorem completed_global (store : MachineStore Universal.State) (memory : Mem) (n : Nat)
    (hglobal : globalAt? store 0=some (.i32 1048512)) :
    globalAt? (completedStore store memory n) 0=some (.i32 1048544) := by
  have hzero := (getElem?_eq_some_iff.mp
    (show store.wasm.globals.globals[0]?=some (.i32 1048512) by
      simpa only [globalAt?,canonicalGlobalIndex_zero] using hglobal)).1
  simp [completedStore,finishStore,EncodeLoopResourceCost.memoryStore,
    globalAt?,canonicalGlobalIndex_zero,hzero]

def finalStore (store : MachineStore Universal.State) (memory : Mem) (output : UInt32) (n : Nat) :
    MachineStore Universal.State :=
  ExportResourceCost.restoredMainStore
    (ExportResourceCost.completedWriteStore (completedStore store memory n) output (UInt32.ofNat (2*n)))

/-- Exact final state: the actual output bytes are appended, input and OOM
state are retained, runtime is unchanged, and no pages are added by this suffix. -/
theorem final_store_resources (store : MachineStore Universal.State) (memory : Mem) (output : UInt32) (n : Nat)
    (hlen : (UInt32.ofNat (2*n)).toNat=2*n) :
    (finalStore store memory output n).runtime=store.runtime ∧
    (finalStore store memory output n).wasm.mem.pages=memory.pages ∧
    (finalStore store memory output n).wasm.host=
      TotalWrite.afterWrite store.wasm.host
        ((completedStore store memory n).wasm.mem.readBytes output.toNat (2*n)) := by
  refine ⟨rfl,rfl,?_⟩
  simp only [finalStore,ExportResourceCost.restoredMainStore,ExportResourceCost.completedWriteStore,
    WriteResourceCost.writeAllResultStore,WriteResourceCost.writeAdapterResultStore,
    WriteResourceCost.universalWriteStore,WriteResourceCost.writeAllFrameStore,completedStore,finishStore,
    EncodeLoopResourceCost.memoryStore,hlen]

/-- Discharge the generated nonempty main continuation using only the
encoder's retained current-memory facts and the original input header. This
constructs the actual writer/cleanup/finish execution for 99 + 2*n work. -/
theorem after_encoder_cost (store : MachineStore Universal.State) (memory : Mem)
    (inputPointer inputCapacity output capacity cursor : UInt32) (n : Nat)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hhost : store.runtime.currentHost=Universal.envFor Project.HexStdio.module)
    (hglobal : globalAt? store 0=some (.i32 1048512))
    (fields : Fields memory capacity output (UInt32.ofNat (2*n)) sentinel cursor cursor)
    (frame : Framed store.wasm.mem memory output)
    (hinputCapacity : store.wasm.mem.read32 1048552=inputCapacity)
    (hinputNonzero : inputCapacity≠0) (hn : 0<n)
    (hcapacity : 2*n≤capacity.toNat)
    (houtput : 1048592≤output.toNat)
    (hphysical : output.toNat+2*n≤store.wasm.mem.pages*65536)
    (hnowrap : output.toNat+2*n<UInt32.size) :
    ∃ trace, CostedSteps CostedStdIO.work
      (EncodeFunctionResourceCost.afterEncodeConfig (completedStore store memory n) inputPointer) trace
      ⟨.done [],finalStore store memory output n⟩ (99+2*n) ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) ∧
      (finalStore store memory output n).runtime=store.runtime ∧
      (finalStore store memory output n).wasm.mem.pages=store.wasm.mem.pages ∧
      (finalStore store memory output n).wasm.host=
        TotalWrite.afterWrite store.wasm.host
          ((completedStore store memory n).wasm.mem.readBytes output.toNat (2*n)) := by
  have hlen : (UInt32.ofNat (2*n)).toNat=2*n := UInt32.toNat_ofNat_of_lt' (by omega)
  have hlenNe : UInt32.ofNat (2*n)≠0 := by
    intro equality
    have e := congrArg UInt32.toNat equality
    rw [hlen] at e
    change 2*n=0 at e
    omega
  have hcapacityNe : capacity≠0 := by
    intro equality
    subst capacity
    change 2*n≤0 at hcapacity
    omega
  have hpages : 17≤memory.pages := by rw [frame.1];omega
  obtain ⟨hcapacityRead,hpointerRead,hlengthRead⟩ := completed_result_fields store memory capacity output cursor n fields
  have hinputRead := completed_input_capacity store memory output inputCapacity n frame hinputCapacity houtput
  have hglobalRead := completed_global store memory n hglobal
  obtain ⟨trace,run,labels⟩ := ExportResourceCost.nonempty_main_cost (completedStore store memory n)
    inputPointer output inputCapacity capacity (UInt32.ofNat (2*n)) hmodule hhost
    hcapacityRead hinputRead hpointerRead hlengthRead hcapacityNe hinputNonzero hlenNe hglobalRead
    (by change output.toNat+(UInt32.ofNat (2*n)).toNat≤memory.pages*65536;rw [hlen,frame.1];exact hphysical)
    hpages
  obtain ⟨runtime,pages,host⟩ := final_store_resources store memory output n hlen
  refine ⟨trace,?_,labels,runtime,pages.trans frame.1,host⟩
  simpa only [hlen,finalStore,ExportResourceCost.afterEncodeConfig,EncodeFunctionResourceCost.afterEncodeConfig] using run

end Project.HexEncodeStdio.EncoderCompletionResources
