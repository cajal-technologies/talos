import Project.Mergesort.FunctionSpecs
import Interpreter.Wasm.Host.StdIO

/-!
# Executable StdIO seam for generated merge sort

The generated driver is a straight-line composition of its generated
`read_raw` shim, `mergesort_raw`, and `write_raw` shim.  This file exposes that
composition as three explicit small-step phases.  Keeping the host-independent
sort phase separate is what lets its Iris proof use the ordinary Wasm heap
model while the two boundary phases retain the concrete `StdIO` host state.
-/

namespace Project.Mergesort.StdIO

open Wasm Wasm.SmallStep

/-- Beginning of the generated `WORK` allocation in linear memory. -/
def source : UInt32 := 1048576

/-- Maximum number of bytes accepted by the generated entry point. -/
def bufferBytes : Nat := 32768

/-- Initial module store with a fresh standard-input stream. -/
def initialStore (input : List UInt8) : Store Wasm.StdIO.State :=
  { («module».initialStore (α := Wasm.StdIO.State)) with
      host := Wasm.StdIO.State.ofInput input }

/-- The scratch array begins immediately after the words actually read. -/
def scratch (count : UInt32) : UInt32 := source + (count <<< 3)

/-- The emitted exported driver is exactly the read/sort/write composition
used by `RunsBytes`; the intervening instructions only retain the byte count
and calculate `count` and its adjacent scratch pointer. -/
theorem driver_shape : func4 =
    [ .const source, .const (UInt32.ofNat bufferBytes), .call 7, .localSet 0
    , .localGet 0, .const 3, .shrU, .localSet 1
    , .const source, .localGet 1, .const 3, .shl, .add, .localSet 2
    , .const source, .localGet 1, .localGet 2, .call 3
    , .const source, .localGet 0, .call 8, .ret ] := by
  rfl

theorem export_index : «module».findExport "mergesort" = some 6 := by
  rfl

/-- Change only the host-owned component of a Wasm store. -/
def replaceHost (store : Store α) (host : β) : Store β :=
  { store with host := host }

/-- Contextual call configuration for `mergesort_raw`.  Unlike `initConfig`,
this retains the `.call` instruction, exactly matching the public contextual
Iris contract proved for the generated recursive function. -/
def coreConfig (store : Store Wasm.StdIO.State) (count : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[], [], [.i32 (scratch count), .i32 count, .i32 source]⟩,
        [.call 3], 0, [], [], []⟩
    store :=
      { runtime := { module := «module», host := ({} : HostEnv Unit) }
        wasm := replaceHost store () } }

/-- Fuel-free relational execution of the exact three calls made by the
generated straight-line driver.  Each phase uses the authoritative small-step
relation; all traces and intermediate machine stores are existentially hidden. -/
def RunsBytes (input output : List UInt8) : Prop :=
  ∃ byteLength : UInt32,
    ∃ afterRead afterWrite : Store Wasm.StdIO.State,
    ∃ afterCore : Store Unit,
      TerminatesWith
        (FunctionSpecs.callConfig 7 (initialStore input)
          [.i32 source, .i32 (UInt32.ofNat bufferBytes)])
        (fun values final =>
          values = [.i32 byteLength] ∧ final.wasm = afterRead) ∧
      TerminatesWith (coreConfig afterRead (byteLength >>> 3))
        (fun values final => values = [] ∧ final.wasm = afterCore) ∧
      TerminatesWith
        (FunctionSpecs.callConfig 8
          (replaceHost afterCore afterRead.host)
          [.i32 source, .i32 byteLength])
        (fun values final => values = [] ∧ final.wasm = afterWrite) ∧
      afterWrite.host.output = output

end Project.Mergesort.StdIO
