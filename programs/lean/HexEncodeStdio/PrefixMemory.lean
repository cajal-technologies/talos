import HexEncodeStdio.FullMemory

namespace Submission.PrefixMemory

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std FromMathlib
open Wasm.SepLogic Wasm.SmallStep

variable {α : Type}

/-- A finite, non-wrapping prefix of the concrete Wasm memory.  This avoids
materializing the inaccessible final byte when a memory has the full 65536
pages. -/
def heap (store : MachineStore α) (n : Nat) : WasmHeapMap (Option UInt8) :=
  Submission.Grow.insertBytes ∅ 0
    (Submission.Grow.bytesAt store.wasm.mem 0 n)

theorem heap_agrees (store : MachineStore α) (n : Nat)
    (hn : n < UInt32.size) :
    heapAgreesWithMem (heap store n) (storeResolve store) := by
  unfold heap
  apply Submission.Grow.insertBytes_agrees
  · simp [storeResolve]
  · simpa using hn
  · exact heapAgreesWithMem_empty _

theorem heap_inBounds (store : MachineStore α) (n : Nat)
    (hn : n < UInt32.size)
    (hbound : n ≤ store.wasm.mem.pages * 65536) :
    heapAddressesInBounds (heap store n) (storeResolve store) := by
  unfold heap
  apply Submission.Grow.insertBytes_inBounds
  · simp [storeResolve]
  · simpa using hn
  · simpa using hbound
  · exact heapAddressesInBounds_empty _

theorem heap_pointsTo {hlc : HasLC} [WasmSmallStepGS hlc α]
    (store : MachineStore α) (n : Nat) (hn : n < UInt32.size) :
    ([∗map] address ↦ value ∈ heap store n,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsToBytes 0 0 (Submission.Grow.bytesAt store.wasm.mem 0 n) := by
  unfold heap
  iintro Hheap
  ihave Hsplit := Submission.FullMemory.insertBytes_pointsTo
    (α := α) ∅ 0 (Submission.Grow.bytesAt store.wasm.mem 0 n)
    (by simpa using hn)
    (by intro i hi; simp [get?_empty]) $$ Hheap
  icases Hsplit with ⟨Hbytes, _⟩
  iexact Hbytes

theorem bytesAt_split {hlc : HasLC} [WasmSmallStepGS hlc α]
    (mem : Mem) (addr : UInt32) (m n : Nat)
    (hnowrap : addr.toNat + m + n < UInt32.size) :
    pointsToBytes (α := α) 0 addr
        (Submission.Grow.bytesAt mem addr (m + n)) ⊣⊢
      (pointsToBytes 0 addr (Submission.Grow.bytesAt mem addr m) ∗
        pointsToBytes 0 (addr + UInt32.ofNat m)
          (Submission.Grow.bytesAt mem (addr + UInt32.ofNat m) n)) := by
  rw [Submission.FullMemory.bytesAt_append mem addr m n hnowrap]
  simpa using (pointsToBytes_append (α := α) 0 addr
    (Submission.Grow.bytesAt mem addr m)
    (Submission.Grow.bytesAt mem (addr + UInt32.ofNat m) n))

theorem bytesAt_drop {hlc : HasLC} [WasmSmallStepGS hlc α]
    (mem : Mem) (addr : UInt32) (m n : Nat)
    (hnowrap : addr.toNat + m + n < UInt32.size) :
    pointsToBytes (α := α) 0 addr
        (Submission.Grow.bytesAt mem addr (m + n)) ⊢
      pointsToBytes 0 (addr + UInt32.ofNat m)
        (Submission.Grow.bytesAt mem (addr + UInt32.ofNat m) n) := by
  iintro H
  ihave Hsplit := (bytesAt_split mem addr m n hnowrap).mp $$ H
  icases Hsplit with ⟨_Hprefix, Hsuffix⟩
  iexact Hsuffix

theorem bytesAt_word_split {hlc : HasLC} [WasmSmallStepGS hlc α]
    (mem : Mem) (addr : UInt32) (n : Nat)
    (hnowrap : addr.toNat + 4 + n < UInt32.size) :
    pointsToBytes (α := α) 0 addr
        (Submission.Grow.bytesAt mem addr (4 + n)) ⊢
      pointsTo_u32 0 addr (mem.read32 addr) ∗
        pointsToBytes 0 (addr + 4)
          (Submission.Grow.bytesAt mem (addr + 4) n) := by
  iintro H
  ihave Hsplit := (bytesAt_split mem addr 4 n hnowrap).mp $$ H
  icases Hsplit with ⟨Hword, Hrest⟩
  isplitl [Hword]
  · iapply (pointsTo_u32_as_bytes 0 addr (mem.read32 addr)).mpr
    rw [← Submission.FullMemory.bytesAt_four mem addr (by omega)]
    iexact Hword
  · iexact Hrest

def wordsAt (mem : Mem) (addr : UInt32) : Nat → List UInt32
  | 0 => []
  | n + 1 => mem.read32 addr :: wordsAt mem (addr + 4) n

theorem bytesAt_words {hlc : HasLC} [WasmSmallStepGS hlc α]
    (mem : Mem) (addr : UInt32) (n : Nat)
    (hnowrap : addr.toNat + 4 * n < UInt32.size) :
    pointsToBytes (α := α) 0 addr
        (Submission.Grow.bytesAt mem addr (4 * n)) ⊢
      arrayAt 0 addr (wordsAt mem addr n) := by
  induction n generalizing addr with
  | zero =>
      simp only [Nat.mul_zero, wordsAt, arrayAt]
      iintro _
      itrivial
  | succ n ih =>
      rw [show 4 * (n + 1) = 4 + 4 * n by omega]
      iintro H
      ihave Hsplit := bytesAt_word_split mem addr (4 * n) (by omega) $$ H
      icases Hsplit with ⟨Hword, Hrest⟩
      simp only [wordsAt, arrayAt]
      isplitl [Hword]
      · iexact Hword
      · iapply ih (addr + 4) (by
          have hadd : (addr + 4).toNat = addr.toNat + 4 := by
            simpa using UInt32.add_ofNat_toNat_noWrap addr 4 (by decide)
              (by norm_num [UInt32.size] at hnowrap ⊢; omega)
          rw [hadd]
          omega)
        iexact Hrest

theorem terminates
    [WasmSmallStepGpreS α]
    (config : Config α) (n : Nat)
    (globalσ : WasmGlobalMap Value)
    (post : List Value → MachineStore α → Prop)
    (hn : n < UInt32.size)
    (hbound : n ≤ config.store.wasm.mem.pages * 65536)
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      (pointsToBytes 0 0
          (Submission.Grow.bytesAt config.store.wasm.mem 0 n) ∗
        ([∗map] index ↦ value ∈ globalσ, globalPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule ∗
        hostEnvOwn config.store.runtime.entry.id
          config.store.runtime.currentHost ∗
        hostStateOwn config.store.wasm.host) ⊢
      WP config.expr @ Stuckness.NotStuck; ⊤
        [{ values,
          ∀ (store : MachineStore α) (_observations : List StepKind),
            stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
            ⌜post values store⌝ }]) :
    TerminatesWith config post := by
  apply Wasm.SmallStep.heap_globals_runtime_host_store_terminates
    config (heap config.store n) globalσ post
  · exact heap_agrees config.store n hn
  · exact heap_inBounds config.store n hn hbound
  · exact hglobals
  · exact hwf
  · intro hlc _
    iintro ⟨Hheap, Hglobals, Hruntime, Henv, Hhost⟩
    ihave Hbytes := heap_pointsTo config.store n hn $$ Hheap
    iapply htwp hlc
    iframe

end Submission.PrefixMemory
