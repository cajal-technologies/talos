import Mathlib
import CodeLib
import Project.HexStdio.Spec
import HexEncodeStdio.Hex
import HexEncodeStdio.Iterator
import HexEncodeStdio.Outcome
import HexEncodeStdio.Concrete
import HexEncodeStdio.TotalMain
import HexEncodeStdio.EndToEnd

/-!
# Proof blueprint

The generated function numbers below omit the three imports. Thus `func10` is
WAT function 13, the exported `encode` wrapper.

Informally, `func10` first calls `func7` to read the complete host input into a
Rust vector. Every vector allocation reaches `func12` (fresh allocation) or
`func15` (growth). At their `memory.grow`, success preserves the owned bytes and
continues; failure calls `func13`, which invokes the `talos.oom` host and proves
the exceptional branch of the target.

On the successful branch, `func6` allocates an output vector of twice the input
length and loops over its output positions. `func18` supplies alternating high
and low nibbles and indexes the static table `0123456789abcdef`. The loop
invariant says the initialized output prefix is exactly
`(input.take processedBytes).flatMap Spec.encodeByte`, with a possible first
digit of the next byte when the output index is odd. Hence the finished vector
is exactly `Spec.encode input`. Finally `func8` repeatedly invokes the write
host until the whole vector is consumed; its invariant is that the host output
is the corresponding prefix of `Spec.encode input`. Deallocation changes no
observable host state, and `func10` restores the stack pointer and returns no
values.

Lemma DAG (dependencies point upward):

* pure hexadecimal facts -> `func18_hex_digit`
* allocator grow-success / grow-failure legs -> `func12_alloc_outcome`,
  `func15_realloc_outcome`
* host read step + read loop legs + allocator outcomes -> `func7_read_all_outcome`
* `func18_hex_digit` + encode-loop init/step/exit + allocator outcomes ->
  `func6_encode_outcome`
* host write step + write-loop init/step/exit -> `func8_write_all`
* those three function specifications + cleanup -> `func10_export_outcome`
* entry adequacy and Universal host satisfaction -> `encode_export_outcome`
-/

namespace Project.HexEncodeStdio.Blueprint

open Wasm
open Project.HexStdio.Spec

/-- Nonempty input is handled by the read, encode, and write loop specs. -/
theorem func10_export_run_cons (byte : UInt8) (bytes : List UInt8) :
    ∃ config fuel,
      startConfig? (Universal.envFor Project.HexStdio.«module»)
          Project.HexStdio.«module» "encode"
          (Universal.State.ofInput (byte :: bytes)) = some config ∧
      Project.HexEncodeStdio.Outcome.EncodesOrOOM (byte :: bytes)
        (SmallStep.runSteps fuel config).result := by
  let input := byte :: bytes
  have hinput : input ≠ [] := by simp [input]
  have hread := Project.HexEncodeStdio.read_to_end_nonempty_outcome
    input hinput
  have houtcome : Project.HexEncodeStdio.ReachesOrOOM
      (Project.HexEncodeStdio.encodeInitialConfig input)
      (Project.HexEncodeStdio.EncodesConfig input) := by
    apply Project.HexEncodeStdio.ReachesOrOOM.bind hread
    intro readConfig hreadSuccess
    have hreserve := Project.HexEncodeStdio.encode_reserve_after_read
      input readConfig hinput hreadSuccess
    apply Project.HexEncodeStdio.ReachesOrOOM.bind hreserve
    intro final hfinal
    rcases hfinal with ⟨store, inputCapacity, inputPtr, inputBump, allocStore,
      hread', hcapacity, hptr, hbump, halloc, rfl⟩
    have hterm := Project.HexEncodeStdio.encode_after_alloc_terminates
      input store inputCapacity inputPtr inputBump allocStore hinput
      hcapacity hptr hbump hread' halloc
    rcases hterm with ⟨trace, values, finalStore, hsteps, hpost⟩
    left
    refine ⟨⟨.done values, finalStore⟩, ⟨trace, hsteps⟩, ?_⟩
    rcases hpost with ⟨rfl, hout⟩
    exact ⟨finalStore, rfl, hout⟩
  obtain ⟨fuel, hrun⟩ :=
    Project.HexEncodeStdio.reachesOrOOM_to_runner input
      (Project.HexEncodeStdio.encodeInitialConfig input) houtcome
  exact ⟨Project.HexEncodeStdio.encodeInitialConfig input, fuel,
    Project.HexEncodeStdio.encode_start_config input, hrun⟩

/-- Executable form of the whole function-level proof. All loop and callee
specifications below are assembled to establish this statement. -/
theorem func10_export_run (input : List UInt8) :
    ∃ config fuel,
      startConfig? (Universal.envFor Project.HexStdio.«module»)
          Project.HexStdio.«module» "encode" (Universal.State.ofInput input) =
        some config ∧
      Project.HexEncodeStdio.Outcome.EncodesOrOOM input
        (SmallStep.runSteps fuel config).result := by
  cases input with
  | nil => exact Project.HexEncodeStdio.Concrete.func10_export_run_nil
  | cons byte bytes => exact func10_export_run_cons byte bytes

/-- The top-level anchor implemented after the function-level specifications. -/
theorem encode_export_outcome (input : List UInt8) :
    RunsEncode input (encode input) ∨ RunsOutOfMemory input := by
  obtain ⟨config, fuel, hstart, hrun⟩ := func10_export_run input
  exact Project.HexEncodeStdio.Outcome.run_result_to_spec input config hstart fuel hrun

end Project.HexEncodeStdio.Blueprint
