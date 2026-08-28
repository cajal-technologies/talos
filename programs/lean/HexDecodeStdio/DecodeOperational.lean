import HexDecodeStdio.ReadToEndStoreFacts

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

@[simp] abbrev decodeStack : UInt32 := 1048528
@[simp] abbrev decodeInputVector : UInt32 := 1048564

@[simp] abbrev decodeStatusVector : UInt32 := decodeStack + 12

def decodeConfig (input : List UInt8) : SmallStep.Config Universal.State :=
  { expr := .running
      { locals := func9Def.toLocals []
        code := func9
        resultArity := 0
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances := #[{ module := «module», host := Universal.envFor «module» }]
            entry := ⟨0⟩ }
        wasm := { («module».initialStore : Store Universal.State) with
          host := Universal.State.ofInput input } } }

def decodeFrameStore (store : MachineStore Universal.State) :
    MachineStore Universal.State :=
  let memLen := store.wasm.mem.write32 (decodeStack + 20) 0
  let memVec := memLen.write64 (decodeStack + 12) 4294967296
  { store with wasm := { store.wasm with
      globals := { globals :=
        store.wasm.globals.globals.set 0 (.i32 decodeStack) }
      mem := memVec } }

def decodeAfterRead : Program := func9.drop 15

theorem func9_read_to_end_split :
    func9 =
      [.globalGet 0, .const 48, .sub, .localTee 0, .globalSet 0,
        .localGet 0, .const 0, .store32 20,
        .localGet 0, .constI64 4294967296, .store64 12,
        .localGet 0, .const 36, .add, .call 10] ++ decodeAfterRead := by
  rfl

def decodeAfterReadConfig (store : MachineStore Universal.State) :
    Config Universal.State :=
  { expr := .running
      { locals := ⟨[], [.i32 decodeStack, .i32 0, .i32 0, .i32 0,
            .i32 0, .i32 0], []⟩
        code := decodeAfterRead
        resultArity := 0
        callerRemainder := [] }
    store := store }

set_option maxRecDepth 1048576 in
theorem initial_allocator_bump :
    («module».initialStore : Store Universal.State).mem.read32 1053960 = 0 := by
  decide

theorem decode_to_read_to_end_store
    (store : MachineStore Universal.State)
    (hglobal : globalAt? store 0 = some (.i32 1048576))
    (hpages : store.wasm.mem.pages = 17) :
    Reaches
      ({ expr := .running
          { locals := func9Def.toLocals []
            code := func9
            resultArity := 0
            callerRemainder := [] }
         store := store } : Config Universal.State)
      ({ expr := .running
          ⟨⟨[], [.i32 decodeStack, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 decodeInputVector]⟩,
            [.call 10] ++ decodeAfterRead, 0, [], [], []⟩
         store := decodeFrameStore store } :
        Config Universal.State) := by
  have hbound20 : ((1048576 : UInt32) - 48).toNat + 20 + 4 ≤
      store.wasm.mem.pages * 65536 := by rw [hpages]; decide
  have hbound12 : ((1048576 : UInt32) - 48).toNat +
      (12 : UInt32).toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by rw [hpages]; decide
  apply Reaches.prepend (Step.globalGet hglobal)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.globalSet (by simp [hglobal]))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 hbound20)
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.constI64
  apply Reaches.prepend (Step.store64 rfl (by
    simpa only [Mem.write32_pages] using hbound12))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  simp [func9Def, Function.toLocals, Function.numParams, ValueType.zero,
    func9_read_to_end_split, decodeFrameStore, decodeInputVector]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 1048576 in
theorem decode_to_read_to_end (input : List UInt8) :
    Reaches (decodeConfig input)
      ({ expr := .running
          ⟨⟨[], [.i32 decodeStack, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 decodeInputVector]⟩,
            [.call 10] ++ decodeAfterRead, 0, [], [], []⟩
         store := decodeFrameStore (decodeConfig input).store } :
        Config Universal.State) := by
  apply decode_to_read_to_end_store
  · rfl
  · rfl

set_option maxRecDepth 1048576 in
theorem decode_to_first_chunk_outcome (input : List UInt8) :
    let entryStore := decodeFrameStore (decodeConfig input).store
    let framed := readToEndFrameStore entryStore readToEndStack
    let bytes := input.take 32
    let after := readAdapterResultStore
      (readChunkFrameStore framed firstChunkFrame)
      firstChunkResult firstChunkBuffer bytes
    let count := UInt32.ofNat bytes.length
    ReachesOrOOM
      ({ expr := .running
          ⟨⟨[], [.i32 decodeStack, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 decodeInputVector]⟩,
            [.call 10] ++ decodeAfterRead, 0, [], [], []⟩
         store := entryStore } : Config Universal.State)
      (fun final =>
        if bytes = [] then
          final =
            { expr := .running
                ⟨⟨[.i32 decodeInputVector],
                    [.i32 readToEndStack, .i32 0, .i32 0, .i32 0,
                      .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                      .i32 0, .i32 0, .i32 0, .i32 0, .i64 0], []⟩,
                  readToEndAfterFirstRead, 0, [], [],
                  [{ locals :=
                      ⟨[], [.i32 decodeStack, .i32 0, .i32 0, .i32 0,
                        .i32 0, .i32 0], []⟩
                     continuation := decodeAfterRead
                     resultArity := 0
                     callerRemainder := []
                     control := []
                     returningInstance := entryStore.runtime.entry }]⟩
              store := readChunkFinishedStore after readToEndResult
                readToEndVector 0 0 readToEndStack }
        else
          ∃ allocStore,
            ByteGrowSuccess
              (reserveFrameStore after (firstChunkFrame - 16))
              0 1 (reserveNewCapacity 0 count 0) 0 allocStore ∧
            final =
              { expr := .running
                  ⟨⟨[.i32 decodeInputVector],
                      [.i32 readToEndStack, .i32 0, .i32 0, .i32 0,
                        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                        .i32 0, .i32 0, .i32 0, .i32 0, .i64 0], []⟩,
                    readToEndAfterFirstRead, 0, [], [],
                    [{ locals :=
                        ⟨[], [.i32 decodeStack, .i32 0, .i32 0, .i32 0,
                          .i32 0, .i32 0], []⟩
                       continuation := decodeAfterRead
                       resultArity := 0
                       callerRemainder := []
                       control := []
                       returningInstance := entryStore.runtime.entry }]⟩
                store := readChunkFinishedStore
                  (readChunkCopiedStore
                    (reserveFinishStore
                      (growResultOkStore allocStore
                        ((firstChunkFrame - 16) + 4)
                        (allocatorPtr 0 1)
                        (reserveNewCapacity 0 count 0))
                      readToEndVector (allocatorPtr 0 1)
                      (reserveNewCapacity 0 count 0) firstChunkFrame)
                    (allocatorPtr 0 1) firstChunkBuffer count)
                  readToEndResult readToEndVector count 0 readToEndStack }) := by
  dsimp only
  let entryStore := decodeFrameStore (decodeConfig input).store
  let framed := readToEndFrameStore entryStore readToEndStack
  let bytes := input.take 32
  have hentryPages : entryStore.wasm.mem.pages = 17 := by rfl
  have hframedPages : framed.wasm.mem.pages = 17 := by
    simpa [framed] using hentryPages
  have hprefix := read_to_end_to_first_chunk entryStore
    [] [.i32 decodeStack, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
    [] decodeAfterRead 0 [] [] [] decodeInputVector decodeStack
    (by rfl) (by rfl) (by rw [hentryPages]; decide)
  have hchunk := read_chunk_first_outcome framed
    [.i32 decodeInputVector]
    [.i32 readToEndStack, .i32 0, .i32 0, .i32 0, .i32 0,
      .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
      .i32 0, .i32 0, .i64 0]
    [] readToEndAfterFirstRead 0 [] []
    [{ locals := ⟨[], [.i32 decodeStack, .i32 0, .i32 0, .i32 0,
        .i32 0, .i32 0], []⟩
       continuation := decodeAfterRead
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := entryStore.runtime.entry }]
    bytes (by rfl) (by rfl) (by
      simp [framed, entryStore, readToEndFrameStore, globalAt?,
        decodeFrameStore, decodeConfig]
      decide)
    (by rfl) hframedPages
    (by simp [framed, readToEndFrameStore, Mem.read32, Mem.write64,
      Mem.write32] <;> bv_decide)
    (by simp [framed, readToEndFrameStore, Mem.read32, Mem.write64,
      Mem.write32] <;> bv_decide)
    (by simp [framed, readToEndFrameStore, Mem.read32, Mem.write64,
      Mem.write32])
    (by
      simp only [framed, entryStore, readToEndFrameStore, decodeFrameStore,
        decodeConfig]
      rw [Mem.read32_write64_disjoint _ 1053960 (readToEndStack + 4) _
        (by decide)]
      rw [Mem.read32_write32_disjoint _ (readToEndStack + 12) 1053960 _
        (by decide)]
      rw [Mem.read32_write64_disjoint _ 1053960 (decodeStack + 12) _
        (by decide)]
      rw [Mem.read32_write32_disjoint _ (decodeStack + 20) 1053960 _
        (by decide)]
      exact initial_allocator_bump)
  exact ReachesOrOOM.prependReaches hprefix (by
    simpa [entryStore, framed, bytes] using hchunk)

end Project.HexDecodeStdio
