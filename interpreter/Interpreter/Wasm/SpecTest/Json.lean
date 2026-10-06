import Lean.Data.Json
import Interpreter.Wasm.SpecTest.Verdict

/-!
# JSON rendering of observations and verdicts
-/

namespace Wasm.SpecTest

open Lean (Json toJson)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexOfBytes (bytes : List UInt8) : String :=
  String.ofList (bytes.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

def bytesOfHex? (s : String) : Option (List UInt8) :=
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: rest => do
      let hi ← hexValue? a
      let lo ← hexValue? b
      let tail ← go rest
      pure (UInt8.ofNat (hi * 16 + lo) :: tail)
    | [_] => none
  go s.toList

def terminationJson : Termination → Json
  | .done values => Json.mkObj [("kind", Json.str "done"),
      ("values", Json.arr (values.map (fun v => Json.str (toString (repr v)))).toArray)]
  | .trapped reason => Json.mkObj [("kind", Json.str "trapped"), ("reason", Json.str reason.message)]
  | .outOfFuel => Json.mkObj [("kind", Json.str "out_of_fuel")]
  | .internalError message => Json.mkObj [("kind", Json.str "internal_error"), ("message", Json.str message)]

def observationJson (obs : Observation) : Json :=
  Json.mkObj
    [ ("termination", terminationJson obs.termination)
    , ("output_hex", Json.str (hexOfBytes (obs.output.take 256)))
    , ("output_length", toJson obs.output.length)
    , ("oom_raised", toJson obs.oomRaised)
    , ("steps", toJson obs.steps) ]

def Verdict.name : Verdict → String
  | .pass => "pass"
  | .fail _ => "fail"
  | .vacuousOom => "vacuous-oom"
  | .vacuousDivergent => "vacuous-divergent"
  | .outOfFuelOriginal => "out-of-fuel"
  | .error _ => "error"

def Verdict.detail : Verdict → Option String
  | .fail clause => some clause
  | .error message => some message
  | _ => none

/-- Observable equality used by `--diff`: termination (returned values, trap
reason, fuel exhaustion), output bytes, and the OOM marker. -/
def Termination.sameAs : Termination → Termination → Bool
  | .done a, .done b => toString (repr a) == toString (repr b)
  | .trapped a, .trapped b => a == b
  | .outOfFuel, .outOfFuel => true
  | .internalError a, .internalError b => a == b
  | _, _ => false

def Observation.sameAs (a b : Observation) : Bool :=
  a.termination.sameAs b.termination && a.output == b.output && a.oomRaised == b.oomRaised

end Wasm.SpecTest
