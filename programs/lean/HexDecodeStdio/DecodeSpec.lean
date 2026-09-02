import Project.HexStdio.Program
import Interpreter.Wasm.Host.Universal

/-!
# Specification for `hex_stdio` (decode)

The Rust crate this module is about is a thin wrapper over the `hex` crate. It
exports `encode`, which writes the lowercase hex encoding of every byte it
reads from standard input, and `decode`, which writes a status byte — `0`
accepted, `1` odd length, `2` non-hex character — followed on acceptance by the
bytes its input spells out.

Reporting the outcome in-band keeps each specification a total function of the
input bytes while still distinguishing the two ways `hex::decode` fails, and
distinguishing both from an empty input.

The module is compiled with Talos's OOM-signalling allocator: on allocation
failure the private allocator calls the distinguished `talos.oom` host function
instead of trapping, giving an explicit terminal outcome. Each export therefore
has exactly two exhaustive terminal outcomes — it computes the reference Lean
function, or its allocator signals out-of-memory. Divergence and unrelated
traps satisfy neither branch.
-/

namespace Project.HexStdio.Spec

open Wasm

/-! ## The reference implementation -/

/-- The nibble an ASCII hex digit denotes; `none` for any other byte. Both
cases are accepted, matching `hex::decode`. -/
def hexValue (c : UInt8) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n ∧ n ≤ 0x39 then some (n - 0x30)
  else if 0x61 ≤ n ∧ n ≤ 0x66 then some (n - 0x61 + 10)
  else if 0x41 ≤ n ∧ n ≤ 0x46 then some (n - 0x41 + 10)
  else none

/-- Decode a hex byte string, `none` when some byte is not a hex digit. The
odd-length case is handled by `decodeOutput`, which tests the length first —
as `hex::decode` does, before it inspects any character. -/
def decode : List UInt8 → Option (List UInt8)
  | [] => some []
  | [_] => none
  | hi :: lo :: rest => do
      let h ← hexValue hi
      let l ← hexValue lo
      let tail ← decode rest
      pure (UInt8.ofNat (16 * h + l) :: tail)

/-- What the `decode` export writes: a status byte — `0` accepted, `1` odd
length, `2` non-hex character — followed on acceptance by the decoded bytes.
The length is tested first, so an odd length is reported even when the input
also contains a non-hex byte. -/
def decodeOutput (input : List UInt8) : List UInt8 :=
  if input.length % 2 = 1 then [1]
  else match decode input with
    | some bytes => 0 :: bytes
    | none => [2]

/-! Sanity checks on the reference implementation. They are evaluated at
elaboration time and are part of no proof obligation. -/

#guard decode "deadbeef".toUTF8.toList == some [0xde, 0xad, 0xbe, 0xef]
#guard decode "DEADBEEF".toUTF8.toList == some [0xde, 0xad, 0xbe, 0xef]
#guard decodeOutput [] == [0]
#guard decodeOutput "deadbeef".toUTF8.toList == 0 :: [0xde, 0xad, 0xbe, 0xef]
#guard decodeOutput "abc".toUTF8.toList == [1]
#guard decodeOutput "zzz".toUTF8.toList == [1]
#guard decodeOutput "zz".toUTF8.toList == [2]

/-! ## The Wasm side -/

/-- The generated module imports standard I/O plus the allocator-private,
terminal OOM notification. -/
theorem module_imports : «module».imports = StdIO.imports ++ OOM.imports := by
  native_decide

/-- Every import of the generated module is implemented by the universal host. -/
theorem universal_host_covers : Universal.covers «module» = true := by
  native_decide

/-- The name-keyed universal environment satisfies the matching relational
host contract regardless of generated import indices. -/
theorem universal_env_satisfies :
    (Universal.envFor «module»).Satisfies «module» (Universal.specFor «module») :=
  Universal.envFor_satisfies «module»

/-- Fuel-free successful execution over byte streams through the composite host,
at the exported `decode` entry point. -/
def RunsDecode (input output : List UInt8) : Prop :=
  Universal.RunsBytes «module» "decode" input output

/-- Fuel-free terminal resource exhaustion. The trap reason and the typed host
marker must both identify the allocator's `talos.oom` call, so an unrelated
host trap cannot satisfy this outcome. -/
def RunsOutOfMemory (input : List UInt8) : Prop :=
  TrapsWithHost (Universal.envFor «module») «module» "decode"
    (Universal.State.ofInput input) (.host OOM.trapMessage)
    (fun final => final.oom.raised = true)

/-- For every input, the exported `decode` has one of two finite terminal
outcomes: it writes exactly the Lean `decodeOutput` of the bytes it read, or its
private allocator calls the distinguished OOM host function. Divergence and
unrelated traps satisfy neither branch. -/
@[spec_of "rust-exported" "hex_stdio::decode"]
def DecodeSpec : Prop :=
  ∀ input,
    RunsDecode input (decodeOutput input) ∨
    RunsOutOfMemory input

end Project.HexStdio.Spec
