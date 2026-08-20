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

/-- Read one random byte into address zero and use Wasm's unsigned comparison
to return `1` when it is below 128 and `0` otherwise. -/
def module : Module :=
  { imports := Wasm.Random.imports
    funcs := [{
      body := [
        .const 0, .const 1, .call 0,
        .const 0, .load8U 0,
        .const 128, .ltU]
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
          { runtime := { instances := #[⟨module, Wasm.Random.env, #[]⟩], entry := ⟨0⟩ }
            wasm := initialStore oracle } }

/-- Functional, pathwise semantics: for any fixed oracle, the Wasm function
returns its threshold comparison on the first oracle byte. -/
theorem returns_threshold_result (oracle : Oracle) :
    (runSteps 8 (config oracle)).result.values? =
      some [.i32 (if (UInt8.ofFin (oracle 0)).toUInt32 < 128 then 1 else 0)] := by
  rfl

def finalCursor? : RunnerResult State → Option Nat
  | .success _ store => some store.wasm.host.cursor
  | _ => none

/-- The pathwise run uses exactly the single byte supplied by the probability
model below, so its zero fallback is never observed. -/
theorem consumes_exactly_one_byte (oracle : Oracle) :
    finalCursor? (runSteps 8 (config oracle)).result = some 1 := by
  rfl

/-- Observe whether the Wasm function returned its accepting value. -/
def accepts (oracle : Oracle) : Bool :=
  match (runSteps 8 (config oracle)).result.values? with
  | some [.i32 value] => value == 1
  | _ => false

theorem accepts_iff_first_byte_low (oracle : Oracle) :
    accepts oracle = decide ((oracle 0).val < 128) := by
  rw [accepts, returns_threshold_result]
  by_cases h : (oracle 0).val < 128
  · have h' : (UInt8.ofFin (oracle 0)).toUInt32 < 128 := by
      change (UInt8.ofFin (oracle 0)).toNat < 128
      simpa using h
    simp [h, h']
  · have h' : ¬(UInt8.ofFin (oracle 0)).toUInt32 < 128 := by
      change ¬(UInt8.ofFin (oracle 0)).toNat < 128
      simpa using h
    simp [h, h']

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
