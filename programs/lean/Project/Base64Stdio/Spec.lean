import Project.Base64Stdio.Program
import Interpreter.Wasm.Host.Universal

/-!
# Specification for `base64_stdio` (encode)

The Rust crate this module is about is a thin wrapper over standard base64
(RFC 4648). It exports `encode`, which writes the standard base64 encoding of
every byte it reads from standard input.

The export is specified against a *reference implementation written here in
Lean*. The module is compiled with Talos's OOM-signalling allocator: on
allocation failure the private allocator calls the distinguished `talos.oom`
host function instead of trapping, giving an explicit terminal outcome. The
export therefore has exactly two exhaustive terminal outcomes — it computes the
reference Lean function, or its allocator signals out-of-memory. Divergence and
unrelated traps satisfy neither branch.
-/

namespace Project.Base64Stdio.Spec

open Wasm

/-! ## The reference implementation -/

/-- The standard base64 alphabet (RFC 4648 §4): index `n < 64` to its ASCII
byte. `A`–`Z` = 0–25, `a`–`z` = 26–51, `0`–`9` = 52–61, `+` = 62, `/` = 63.
Kept a standalone def so `decode` can define and relate its inverse. -/
def base64Char (n : Nat) : UInt8 :=
  if n < 26 then UInt8.ofNat (0x41 + n)
  else if n < 52 then UInt8.ofNat (0x61 + (n - 26))
  else if n < 62 then UInt8.ofNat (0x30 + (n - 52))
  else if n = 62 then (0x2b : UInt8)
  else (0x2f : UInt8)

/-- The padding byte `'='`. -/
def pad : UInt8 := 0x3d

/-- Encode a full 3-byte group into 4 base64 chars. -/
def encode3 (b0 b1 b2 : UInt8) : List UInt8 :=
  [ base64Char (b0.toNat >>> 2),
    base64Char (((b0.toNat % 4) <<< 4) ||| (b1.toNat >>> 4)),
    base64Char (((b1.toNat % 16) <<< 2) ||| (b2.toNat >>> 6)),
    base64Char (b2.toNat % 64) ]

/-- Final 1-byte group: 2 chars + `"=="`. -/
def encode1 (b0 : UInt8) : List UInt8 :=
  [ base64Char (b0.toNat >>> 2), base64Char ((b0.toNat % 4) <<< 4), pad, pad ]

/-- Final 2-byte group: 3 chars + `"="`. -/
def encode2 (b0 b1 : UInt8) : List UInt8 :=
  [ base64Char (b0.toNat >>> 2),
    base64Char (((b0.toNat % 4) <<< 4) ||| (b1.toNat >>> 4)),
    base64Char ((b1.toNat % 16) <<< 2), pad ]

/-- Standard base64 encoding of a byte string: 4 chars per 3 input bytes, with
`'='` padding on the final partial group. Structurally recursive on groups of 3,
mirroring `Project.HexStdio.Spec.encode`. -/
def encode : List UInt8 → List UInt8
  | [] => []
  | [b0] => encode1 b0
  | [b0, b1] => encode2 b0 b1
  | b0 :: b1 :: b2 :: rest => encode3 b0 b1 b2 ++ encode rest

/-! Sanity checks (RFC 4648 §10 test vectors). Evaluated at elaboration;
part of no proof obligation. -/
#guard encode [] == []
#guard encode "f".toUTF8.toList == "Zg==".toUTF8.toList
#guard encode "fo".toUTF8.toList == "Zm8=".toUTF8.toList
#guard encode "foo".toUTF8.toList == "Zm9v".toUTF8.toList
#guard encode "foob".toUTF8.toList == "Zm9vYg==".toUTF8.toList
#guard encode "fooba".toUTF8.toList == "Zm9vYmE=".toUTF8.toList
#guard encode "foobar".toUTF8.toList == "Zm9vYmFy".toUTF8.toList

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
outcomes: it writes the standard base64 encoding of the bytes it read, or its
private allocator calls the distinguished OOM host function. Divergence and
unrelated traps satisfy neither branch. -/
@[spec_of "rust-exported" "base64_stdio::encode"]
def EncodeSpec : Prop :=
  ∀ input,
    RunsEncode input (encode input) ∨
    RunsOutOfMemory input

end Project.Base64Stdio.Spec
