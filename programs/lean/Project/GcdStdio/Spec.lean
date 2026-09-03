import Project.GcdStdio.Program
import Project.NumIntegerOpt3.Spec
import Interpreter.Wasm.Host.Universal
import CodeLib.Examples.SelectionSort.StdIO

/-!
# Specification for the `num-integer` GCD stream

The exported `gcd` function consumes two packed little-endian `UInt64` words
and writes their greatest common divisor as one packed word. The implementation
uses a Talos stdio adapter with a fixed bump allocator specialized to its sole
`Box<[u8; 16]>` allocation.
-/

namespace Project.GcdStdio.Spec

open Wasm

/-- The canonical eight-byte little-endian codec already used by the StdIO
examples. -/
abbrev codec : WordCodec UInt64 :=
  Wasm.Examples.SelectionSort.StdIO.codec

/-- The mathematical input of `gcd`, independently of its byte layout. -/
structure Input where
  left : UInt64
  right : UInt64

/-- The mathematical output of `gcd`, independently of its byte layout. -/
abbrev Output := UInt64

/-! The proof below predates the semantic names. Keep these two internal
spellings while the machine proof is factored independently of the public
statement; client-facing specifications use only `Input`, `Output`, `args`,
and `result`. -/

def encodeInput (a b : UInt64) : List UInt8 :=
  codec.serialize [a, b]

def encodeOutput (value : UInt64) : List UInt8 :=
  codec.serialize [value]

/-- Package one semantic input as the initial host stream of the exported
zero-argument wrapper. -/
def args (input : Input) : ExportCall Universal.State :=
  ExportCall.ofHost «module»
    (Universal.State.ofInput (encodeInput input.left input.right))

/-- Recognize one semantic output in the wrapper's normal terminal state. -/
def result (output : Output) : ExportReturn Universal.State → Prop :=
  fun returned =>
    returned.values = [] ∧
      returned.final.host.stdio.output = encodeOutput output

@[simp] theorem encodeInput_length (a b : UInt64) :
    (encodeInput a b).length = 16 := by rfl

@[simp] theorem encodeOutput_length (value : UInt64) :
    (encodeOutput value).length = 8 := by rfl

@[simp] theorem decode_encodeInput (a b : UInt64) :
    codec.deserialize (encodeInput a b) = some [a, b] :=
  codec.deserialize_serialize [a, b]

@[simp] theorem decode_encodeOutput (value : UInt64) :
    codec.deserialize (encodeOutput value) = some [value] :=
  codec.deserialize_serialize [value]

/-- The generated module has exactly the two stream imports followed by the
allocator's terminal OOM notification. -/
theorem module_imports : «module».imports = StdIO.imports ++ OOM.imports := by
  native_decide

theorem universal_host_covers : Universal.covers «module» = true := by
  native_decide

/-- Isolated configuration for the compiled register-only arithmetic kernel.
Its store is deliberately irrelevant: `func1` has no memory, global, call, or
host instructions. -/
def kernelConfig (a b : UInt64) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a, .i64 b], [.i64 0], []⟩,
        func1, 1, [], [], []⟩
    store := (Project.NumIntegerOpt3.Spec.gcdConfig a b).store }

/-- The helper kept separate with `#[inline(never)]` compiles to exactly the
same Stein kernel as the independently verified optimized `num-integer`
example. -/
theorem kernel_body_eq :
    func1 = Project.NumIntegerOpt3.func0 := by
  rfl

/-- Functional contract for the arithmetic kernel linked into the stream
driver. -/
@[spec_of "rust-internal" "gcd_stdio::gcd_u64"]
def KernelSpecification : Prop :=
  ∀ a b : UInt64,
    SmallStep.TerminatesWith (kernelConfig a b)
      (fun values _store =>
        values = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])

/-- Fuel-free execution of a named export in this compiled module. -/
abbrev Runs := Universal.RunsExport «module»

theorem gcd_zeroArgument : ZeroArgumentExport «module» "gcd" := by
  native_decide

/-- For every semantic input there is an output produced by the compiled
`gcd` export, and that output is exactly Lean's reference greatest common
divisor on the two unsigned operands. -/
@[spec_of "rust-exported" "gcd_stdio::gcd"]
def PublicEntrySpecification : Prop :=
  ∀ input : Input,
    ∃ output : Output,
      Runs "gcd" (args input) (result output) ∧
      output.toNat = Nat.gcd input.left.toNat input.right.toNat

end Project.GcdStdio.Spec
