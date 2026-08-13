import Interpreter.Wasm.Host.Random.Probability

/-!
# A probabilistic Wasm coin

This example connects the two proof layers.  The pathwise theorem computes the
Wasm program for every fixed oracle.  The probability theorem then samples its
first oracle byte uniformly and proves that the program accepts with
probability exactly one half.
-/

namespace Wasm.Examples.Random

open Wasm.Random
open Wasm.SmallStep
open scoped ENNReal

/-- Read one random byte into address zero and return it as an `i32`. -/
def module : Module :=
  { imports := Wasm.Random.imports
    funcs := [{
      body := [
        .const 0, .const 1, .call 0,
        .const 0, .load8U 0]
      results := [.i32] }]
    memory := some { pagesMin := 1 } }

def initialStore (oracle : Oracle) : Store State :=
  { (module.initialStore (α := State)) with
    host := State.ofOracle oracle }

def config (oracle : Oracle) : Config State :=
  match initConfig { module, host := Wasm.Random.env }
      1 (initialStore oracle) [] with
  | .ok result => result
  | .error error =>
      { expr := .trapped (.host error.message)
        store :=
          { runtime := { module, host := Wasm.Random.env }
            wasm := initialStore oracle } }

/-- Functional, pathwise semantics: for any fixed oracle, the returned value
is exactly its first byte. -/
theorem returns_first_oracle_byte (oracle : Oracle) :
    (runSteps 6 (config oracle)).result.values? =
      some [.i32 (UInt8.ofFin (oracle 0)).toUInt32] := by
  rfl

def finalCursor? : RunnerResult State → Option Nat
  | .success _ store => some store.wasm.host.cursor
  | _ => none

/-- The pathwise run uses exactly the single byte supplied by the probability
model below, so its zero fallback is never observed. -/
theorem consumes_exactly_one_byte (oracle : Oracle) :
    finalCursor? (runSteps 6 (config oracle)).result = some 1 := by
  rfl

/-- The program's threshold branch, projected as an executable Boolean. -/
def accepts (oracle : Oracle) : Bool :=
  match (runSteps 6 (config oracle)).result.values? with
  | some [.i32 value] => decide (value.toNat < 128)
  | _ => false

theorem accepts_iff_first_byte_low (oracle : Oracle) :
    accepts oracle = decide ((oracle 0).val < 128) := by
  rw [accepts, returns_first_oracle_byte]
  simp

/-- Complete a single sampled byte to the oracle used by the executable
machine.  The program consumes exactly that one-byte prefix. -/
def oneByteOracle (byte : Byte) : Oracle :=
  Oracle.ofPrefix (count := 1) (fun _ => byte)

def acceptanceEvent : Set Byte :=
  { byte | accepts (oneByteOracle byte) = true }

theorem acceptanceEvent_eq :
    acceptanceEvent = { byte | byte.val < 128 } := by
  ext byte
  simp [acceptanceEvent, oneByteOracle, accepts_iff_first_byte_low]

/-- End-to-end probabilistic correctness of the Wasm program. -/
theorem accepts_with_probability_one_half :
    probability uniformByte acceptanceEvent = (1 / 2 : ℝ≥0∞) := by
  rw [acceptanceEvent_eq]
  exact uniformByte_lowHalf_probability

end Wasm.Examples.Random
