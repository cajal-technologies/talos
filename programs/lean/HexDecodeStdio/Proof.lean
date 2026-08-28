import HexDecodeStdio.DecodeWrapperSuccess

/-!
# Proof blueprint for `hex_decode_stdio`

The generated `decode` export is Wasm function 12 (defined function 9 after
the three imports).  Its proof is decomposed along the source-level phases
that remain visible in the generated control flow:

1. `read_to_end` maintains that the initialized vector is exactly the prefix
   removed from the universal host's input.  Allocation has two terminal
   continuations: a successful `memory.grow`, or the `talos.oom` host trap.
2. The hex loop consumes two input bytes at a time.  Its successful-prefix
   invariant relates the bytes already stored in the output vector to
   `Spec.decode`; odd length is selected before looking at a digit, while the
   first invalid digit selects status byte `2`.
3. The output vector therefore contains exactly `Spec.decodeOutput input`.
4. `write_all` maintains that the host output is the already-written prefix
   and terminates after the remaining suffix is empty.
5. The export composes the normal phases into `Universal.RunsBytes`; every
   failed allocator growth instead composes with `OOM.oomContract` into
   `RunsOutOfMemory`.

The declarations below intentionally expose the top-down DAG.  During the
proof each placeholder is replaced by function- and loop-level Iris lemmas;
the target theorem itself stays a one-line application of the root lemma.
-/

namespace Submission.HexDecodeStdio

open Wasm
open Project.HexStdio
open Project.HexStdio.Spec

theorem startConfig_decode (input : List UInt8) :
    startConfig? (Universal.envFor «module») «module» "decode"
      (Universal.State.ofInput input) = some (decodeConfig input) := by
  rfl

/-- Pure nibble classification used by the generated decoder agrees with the
reference `hexValue`. -/
theorem classify_hex_byte_correct (c : UInt8) :
    hexValue c =
      if 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 then some (c.toNat - 0x30)
      else if 0x61 ≤ c.toNat ∧ c.toNat ≤ 0x66 then some (c.toNat - 0x61 + 10)
      else if 0x41 ≤ c.toNat ∧ c.toNat ≤ 0x46 then some (c.toNat - 0x41 + 10)
      else none := by
  rfl

/-- The mathematical invariant exposed by one successful pair iteration. -/
theorem decode_cons_eq (hi lo : UInt8) (rest bytes : List UInt8)
    (hiNibble loNibble : Nat)
    (hh : hexValue hi = some hiNibble)
    (hl : hexValue lo = some loNibble)
    (ht : decode rest = some bytes) :
    decode (hi :: lo :: rest) =
      some (UInt8.ofNat (16 * hiNibble + loNibble) :: bytes) := by
  simp [decode, hh, hl, ht]

/-- Reading, allocating, decoding, and writing the generated export has one
of the two observable terminal outcomes in the public specification. -/
theorem decode_config_outcome (input : List UInt8) :
    SmallStep.TerminatesWith (decodeConfig input)
        (fun values final =>
          values = [] ∧ final.wasm.host.stdio.output = decodeOutput input) ∨
      SmallStep.TrapsWith (decodeConfig input) (.host OOM.trapMessage)
        (fun final => final.wasm.host.oom.raised = true) := by
  rcases decode_core_outcome input with ⟨final, hreach, data, hresult⟩ | htrap
  · rcases hresult with
      ⟨store, capacity, ptr, outLen, bytes, rfl, hdecode, hcapacity,
        hpointer, hlengthField, hlength, hfits, hcapacitySigned,
        hsourceBound, hsourceRead, bump, hfacts, hplacement⟩ |
      ⟨store, bad, rfl, hdecode, htag, hbad, hkind, bump, hfacts⟩
    · rcases decode_success_wrapper_outcome input bytes store data capacity
        ptr outLen bump hdecode hcapacity hpointer hlengthField hlength hfits
        hcapacitySigned hsourceBound hsourceRead hfacts hplacement with
        hterm | hoom
      · left
        exact TerminatesWith.prependReaches hreach hterm
      · right
        exact TrapsWith.prependReaches hreach hoom
    · rcases decode_invalid_wrapper_outcome input store data bad bump htag
        hbad hkind hdecode hfacts with hterm | hoom
      · left
        exact TerminatesWith.prependReaches hreach hterm
      · right
        exact TrapsWith.prependReaches hreach hoom
  · exact Or.inr htrap

theorem decode_export_outcome (input : List UInt8) :
    RunsDecode input (decodeOutput input) ∨ RunsOutOfMemory input := by
  rcases decode_config_outcome input with hrun | hoom
  · left
    exact ⟨decodeConfig input, startConfig_decode input, hrun⟩
  · right
    exact ⟨decodeConfig input, startConfig_decode input, hoom⟩

end Submission.HexDecodeStdio
