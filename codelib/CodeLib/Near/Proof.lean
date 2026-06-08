import CodeLib.Near.Env

/-!
# Proof-facing NEAR helpers

This module keeps relational proof APIs separate from the executable NEAR
host semantics in `Env.lean`. The contracts here are intentionally
definitionally tied to the reference `HostFn`s for now: they give Wasm proofs
a `HostSpec` surface and a satisfaction theorem, while finer relational
contracts can replace individual entries as proofs need more abstraction.
-/

namespace Wasm
namespace Near

/-! ## Host contracts -/

/-- Exact contract for a concrete host function. This is the conservative
starting point for proof-facing NEAR specs: it exposes a `HostSpec` interface
without weakening or rephrasing the executable semantics. -/
def exactHostContract (hf : HostFn NearState) : HostContract NearState :=
  fun st args res => res = hf.invoke st args

def inputContract : HostContract NearState := exactHostContract inputFn
def readRegisterContract : HostContract NearState := exactHostContract readRegisterFn
def registerLenContract : HostContract NearState := exactHostContract registerLenFn
def writeRegisterContract : HostContract NearState := exactHostContract writeRegisterFn
def valueReturnContract : HostContract NearState := exactHostContract valueReturnFn
def storageWriteContract : HostContract NearState := exactHostContract storageWriteFn
def storageReadContract : HostContract NearState := exactHostContract storageReadFn
def storageRemoveContract : HostContract NearState := exactHostContract storageRemoveFn
def storageHasKeyContract : HostContract NearState := exactHostContract storageHasKeyFn

/-- Canonical proof spec aligned with `nearImports`/`nearEnv`. -/
def nearSpec : HostSpec NearState :=
  { contracts := nearHostFns.map (fun p => exactHostContract p.snd) }

/-- Resolve one declared NEAR import to the proof contract for the concrete
reference host function selected by `resolveImport?`. -/
def resolveContract? (decl : ImportDecl) : Option (HostContract NearState) :=
  (resolveImport? decl).map exactHostContract

/-- Resolve a module's import subset/order into a proof spec aligned with the
positional host environment returned by `resolveImports?`. -/
def resolveContracts? : List ImportDecl → Option (HostSpec NearState)
  | [] => some { contracts := [] }
  | decl :: rest =>
    match resolveContract? decl, resolveContracts? rest with
    | some c, some spec => some { contracts := c :: spec.contracts }
    | _, _ => none

/-- Resolve a module's imports into a proof spec, returning `none` for unknown
NEAR names or signature mismatches. -/
def resolveSpec? (m : Module) : Option (HostSpec NearState) :=
  resolveContracts? m.imports

/-- The reference NEAR host environment satisfies the canonical proof spec for
any module whose imports are exactly `nearImports`. Hand-built examples can use
this directly; real compiled modules resolved through `resolveEnv?` will need a
subset/order variant. -/
theorem nearEnv_satisfies_canonical (m : Module) (himports : m.imports = nearImports) :
    nearEnv.Satisfies m nearSpec := by
  intro i hi
  have hiFns : i < nearHostFns.length := by
    rw [himports, nearImports] at hi
    simpa using hi
  let p := nearHostFns[i]
  refine ⟨p.snd, exactHostContract p.snd, ?_, ?_, ?_⟩
  · simp [nearEnv, p, hiFns]
  · simp [nearSpec, p, hiFns]
  · intro st args
    rfl

/-! ## Memory framing -/

@[simp] theorem readBytes_length (m : Mem) (off len : Nat) :
    (m.readBytes off len).length = len := by
  simp [Mem.readBytes]

@[simp] theorem writeBytes_pages (m : Mem) (off : Nat) (data : List UInt8) :
    (m.writeBytes off data).pages = m.pages := rfl

@[simp] theorem writeBytes_byte_in (m : Mem) (off i : Nat) (data : List UInt8)
    (h : i < data.length) :
    (m.writeBytes off data).bytes (off + i) = data[i] := by
  simp [Mem.writeBytes, h]

@[simp] theorem writeBytes_byte_before (m : Mem) (off i : Nat) (data : List UInt8)
    (h : i < off) :
    (m.writeBytes off data).bytes i = m.bytes i := by
  simp [Mem.writeBytes]
  omega

@[simp] theorem writeBytes_byte_after (m : Mem) (off i : Nat) (data : List UInt8)
    (h : off + data.length ≤ i) :
    (m.writeBytes off data).bytes i = m.bytes i := by
  simp [Mem.writeBytes]
  omega

@[simp] theorem read32_writeBytes_four (m : Mem) (a : UInt32) (b0 b1 b2 b3 : UInt8) :
    (m.writeBytes a.toNat [b0, b1, b2, b3]).read32 a =
      b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24) := by
  simp [Mem.read32, Mem.writeBytes]

end Near
end Wasm
