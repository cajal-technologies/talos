import HexEncodeStdio.ReadToEndOperational

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-- Compose the `read_to_end` prologue with its first 32-byte `read_chunk`.
The constants are the stack addresses reached from the encode export. -/
theorem read_to_end_first_outcome
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hglobal : globalAt? store 0 = some (.i32 1048544))
    (hpages : store.wasm.mem.pages = 17)
    (hbump : store.wasm.mem.read32 1053960 = 0) :
    let bytes := store.wasm.host.stdio.input.take 32
    let framed := readToEndFrameStore store readToEndStack
    let after := readAdapterResultStore
      (readChunkFrameStore framed firstChunkFrame)
      firstChunkResult firstChunkBuffer bytes
    let count := UInt32.ofNat bytes.length
    ReachesOrOOM
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues, .i32 1048564 :: stack⟩,
            [.call 10] ++ code, arity, remainder, controls, calls⟩
         store := store } : Config Universal.State)
      (fun final =>
        if bytes = [] then
          final =
            { expr := .running
                ⟨⟨[.i32 1048564],
                    [.i32 readToEndStack, .i32 0, .i32 0, .i32 0, .i32 0,
                      .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                      .i32 0, .i32 0, .i64 0], []⟩,
                  readToEndAfterFirstRead, 0, [], [],
                  { locals := ⟨outerParams, outerLocalValues, stack⟩
                    continuation := code
                    resultArity := arity
                    callerRemainder := remainder
                    control := controls
                    returningInstance := store.runtime.entry } :: calls⟩
              store := readChunkFinishedStore after readToEndResult
                readToEndVector 0 0 readToEndStack }
        else
          ∃ allocStore,
            ByteGrowSuccess
                (reserveFrameStore after (firstChunkFrame - 16))
                0 1 (reserveNewCapacity 0 count 0) 0 allocStore ∧
            let reserved := reserveFinishStore
              (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
                (allocatorPtr 0 1) (reserveNewCapacity 0 count 0))
              readToEndVector (allocatorPtr 0 1)
                (reserveNewCapacity 0 count 0) firstChunkFrame
            final =
              { expr := .running
                  ⟨⟨[.i32 1048564],
                      [.i32 readToEndStack, .i32 0, .i32 0, .i32 0, .i32 0,
                        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                        .i32 0, .i32 0, .i64 0], []⟩,
                    readToEndAfterFirstRead, 0, [], [],
                    { locals := ⟨outerParams, outerLocalValues, stack⟩
                      continuation := code
                      resultArity := arity
                      callerRemainder := remainder
                      control := controls
                      returningInstance := store.runtime.entry } :: calls⟩
                store := readChunkFinishedStore
                  (readChunkCopiedStore reserved
                    (allocatorPtr 0 1) firstChunkBuffer count)
                  readToEndResult readToEndVector count 0 readToEndStack }) := by
  dsimp only
  let framed := readToEndFrameStore store readToEndStack
  let bytes := store.wasm.host.stdio.input.take 32
  have hprefix := read_to_end_to_first_chunk store outerParams outerLocalValues
    stack code arity remainder controls calls 1048564 1048544 hmod hglobal
    (by rw [hpages]; decide)
  apply ReachesOrOOM.prependReaches hprefix
  apply read_chunk_first_outcome framed
      [.i32 1048564]
      [.i32 readToEndStack, .i32 0, .i32 0, .i32 0, .i32 0,
        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
        .i32 0, .i32 0, .i64 0]
      [] readToEndAfterFirstRead 0 [] []
      ({ locals := ⟨outerParams, outerLocalValues, stack⟩
         continuation := code
         resultArity := arity
         callerRemainder := remainder
         control := controls
         returningInstance := store.runtime.entry } :: calls)
      bytes
  · simpa [framed] using hmod
  · simpa [framed] using henv
  · simp only [framed, readToEndFrameStore, globalAt?,
      canonicalGlobalIndex_zero] at hglobal ⊢
    have hzero : 0 < store.wasm.globals.globals.length :=
      (getElem?_eq_some_iff.mp hglobal).1
    simpa using (List.getElem?_set_eq_of_lt (.i32 readToEndStack) hzero)
  · rfl
  · simpa [framed] using hpages
  · simp [framed, readToEndFrameStore, Mem.read32, Mem.write64,
      Mem.write32, Mem.write8] <;> decide
  · simp [framed, readToEndFrameStore, Mem.read32, Mem.write64,
      Mem.write32, Mem.write8] <;> decide
  · rw [show readToEndVector + 8 = readToEndStack + 12 by decide]
    simp [framed, readToEndFrameStore, Mem.read32, Mem.write64,
      Mem.write32, Mem.write8] <;> decide
  · simp only [framed, readToEndFrameStore]
    rw [Mem.read32_write64_disjoint, Mem.read32_write32_disjoint]
    · exact hbump
    · right; decide
    · right; decide

end Project.HexEncodeStdio
