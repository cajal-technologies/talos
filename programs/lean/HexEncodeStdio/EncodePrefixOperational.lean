import HexEncodeStdio.ReadToEndFirst

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def encodeInitialStore (input : List UInt8) : MachineStore Universal.State :=
  { runtime :=
      { instances := #[
          { module := «module»
            host := Universal.envFor «module»
            resolvedImports := #[] }]
        entry := ⟨0⟩ }
    wasm := { («module».initialStore : Store Universal.State) with
      host := Universal.State.ofInput input } }

def encodeInitialConfig (input : List UInt8) : Config Universal.State :=
  ⟨.running
    ⟨⟨[], [.i32 0, .i32 0, .i32 0, .i32 0], []⟩,
      func10, 0, [], [], []⟩,
    encodeInitialStore input⟩

theorem encode_start_config (input : List UInt8) :
    startConfig? (Universal.envFor «module») «module» "encode"
      (Universal.State.ofInput input) = some (encodeInitialConfig input) := by
  rfl

def encodeFrameStore (input : List UInt8) : MachineStore Universal.State :=
  let store := encodeInitialStore input
  { store with wasm := { store.wasm with
      globals := { globals := store.wasm.globals.globals.set 0 (.i32 1048544) } } }

theorem encode_to_read_to_end (input : List UInt8) :
    Reaches (encodeInitialConfig input)
      ({ expr := .running
          ⟨⟨[], [.i32 1048544, .i32 0, .i32 0, .i32 0],
              [.i32 1048564]⟩,
            [.call 10] ++ func10.drop 9, 0, [], [], []⟩
         store := encodeFrameStore input } : Config Universal.State) := by
  simp only [encodeInitialConfig, func10, List.drop]
  apply Reaches.prepend (Step.globalGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.globalSet rfl)
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  simp [encodeFrameStore]
  exact ⟨[], .refl _⟩

end Submission.HexDecodeStdio
