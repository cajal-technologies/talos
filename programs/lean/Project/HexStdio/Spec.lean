import Project.HexStdio.Program
import Interpreter.Wasm.Host.Universal

/-!
# Specification for `hex_stdio` (encode)

The Rust crate this module is about is a thin wrapper over the `hex` crate. It
exports `encode`, which writes the lowercase hex encoding of every byte it
reads from standard input, and `decode`, which writes a status byte — `0`
accepted, `1` odd length, `2` non-hex character — followed on acceptance by the
bytes its input spells out.

Both exports are specified against *reference implementations written here in
Lean*. The module is compiled with Talos's OOM-signalling allocator: on
allocation failure the private allocator calls the distinguished `talos.oom`
host function instead of trapping, giving an explicit terminal outcome. Each
export therefore has exactly two exhaustive terminal outcomes — it computes the
reference Lean function, or its allocator signals out-of-memory. Divergence and
unrelated traps satisfy neither branch.
-/

namespace Project.HexStdio.Spec

open Wasm

/-! ## The reference implementation -/

/-- The lowercase ASCII hex digit for a nibble (`n < 16`). -/
def hexDigit (n : Nat) : UInt8 :=
  if n < 10 then UInt8.ofNat (0x30 + n) else UInt8.ofNat (0x61 + (n - 10))

/-- The two hex digits of one byte, most significant nibble first. -/
def encodeByte (b : UInt8) : List UInt8 :=
  [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- The lowercase hex encoding of a byte string: two ASCII characters per
input byte, nothing else. -/
def encode (bytes : List UInt8) : List UInt8 :=
  bytes.flatMap encodeByte

/-! Sanity checks on the reference implementation. They are evaluated at
elaboration time and are part of no proof obligation. -/

#guard encode [] == []
#guard encode [0xde, 0xad, 0xbe, 0xef] == "deadbeef".toUTF8.toList
#guard encode [0x00, 0x0f, 0xf0] == "000ff0".toUTF8.toList

/-! ## The Wasm side -/

/-- The generated module imports standard I/O plus the allocator-private,
terminal OOM notification. -/
theorem module_imports : «module».imports = StdIO.imports ++ OOM.imports := by
  decide +kernel

/-- Every import of the generated module is implemented by the universal host. -/
theorem universal_host_covers : Universal.covers «module» = true := by
  decide +kernel

/-- The name-keyed universal environment satisfies the matching relational
host contract regardless of generated import indices. -/
theorem universal_env_satisfies :
    (Universal.envFor «module»).Satisfies «module» (Universal.specFor «module») :=
  Universal.envFor_satisfies «module»

/-- Fuel-free successful execution over byte streams through the composite host,
at the exported `encode` entry point. -/
def RunsEncode (input output : List UInt8) : Prop :=
  Universal.RunsBytes «module» "encode" input output

/-- Fuel-free terminal resource exhaustion. The trap reason and the typed host
marker must both identify the allocator's `talos.oom` call, so an unrelated
host trap cannot satisfy this outcome. -/
def RunsOutOfMemory (input : List UInt8) : Prop :=
  TrapsWithHost (Universal.envFor «module») «module» "encode"
    (Universal.State.ofInput input) (.host OOM.trapMessage)
    (fun final => final.oom.raised = true)

/-- For every input, the exported `encode` has one of two finite terminal
outcomes: it writes the lowercase hex encoding of the bytes it read, or its
private allocator calls the distinguished OOM host function. Divergence and
unrelated traps satisfy neither branch. -/
@[spec_of "rust-exported" "hex_stdio::encode"]
def EncodeSpec : Prop :=
  ∀ input,
    RunsEncode input (encode input) ∨
    RunsOutOfMemory input

end Project.HexStdio.Spec
