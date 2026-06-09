import Project.NearKvContract.Program

/-!
# NEAR SDK contract fixture

`programs/rust/near_kv_contract` is a real `near-sdk-rs` crate. The verifier
pipeline emits the decoded Wasm module here; this spec checks that its host
imports are covered by the NEAR resolver.
-/

namespace Project.NearKvContract

open Wasm

def importsResolve : Bool :=
  match Wasm.Near.resolveEnv? «module», Wasm.Near.resolveSpec? «module» with
  | some _, some _ => true
  | _, _           => false

theorem imports_resolve : importsResolve = true := by native_decide

def resolvedNearEnv : HostEnv NearState :=
  (Wasm.Near.resolveEnv? «module»).getD {}

def runSetFromInput (ns : NearState) : Result NearState :=
  run 20000 «module» 5 { («module».initialStore : Store NearState) with host := ns } [] resolvedNearEnv

def storedAfterSetFromInput (input key : List UInt8) : Option (List UInt8) :=
  match runSetFromInput { context := { input } } with
  | .Success _ st => st.host.storage key
  | _             => none

/-- Concrete end-to-end storage property for the decoded `near-sdk-rs`
contract: input `[1, 7, 8]` stores value `[7, 8]` under key `[1]`. -/
theorem set_from_input_stores_tail :
    storedAfterSetFromInput [1, 7, 8] [1] = some [7, 8] := by native_decide

end Project.NearKvContract
