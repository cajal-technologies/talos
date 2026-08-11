import Interpreter.Wasm.SmallStep

/-!
# A byte-buffer standard-I/O host

`StdIO` is a deliberately small deterministic host environment.  Its mutable
state consists of an unread input buffer and an append-only output buffer.  It
provides two imports, both using `(length, pointer)` argument order:

* `read : (i32, i32) -> i32` copies up to `length` unread input bytes into
  linear memory at `pointer`, consumes exactly those bytes, and returns the
  number copied;
* `write : (i32, i32) -> ()` appends exactly `length` bytes from linear memory
  at `pointer` to the output buffer.

An out-of-bounds memory range or malformed argument list traps without making
any state change.  Zero-length accesses are valid even at the byte immediately
after the end of memory, matching the usual half-open-range convention.
-/

namespace Wasm.StdIO

/-- Mutable state owned by the `StdIO` host. -/
structure State where
  input : List UInt8
  output : List UInt8 := []
deriving Repr, Inhabited, DecidableEq

/-- Start a fresh host run with `input` available and an empty output. -/
def State.ofInput (input : List UInt8) : State := { input }

/-- The number of addressable bytes in the primary linear memory. -/
def byteCapacity (st : Store State) : Nat := st.mem.pages * 65536

/-- Whether the half-open range `[pointer, pointer + length)` is in memory. -/
def rangeInBounds (st : Store State) (pointer length : Nat) : Bool :=
  pointer + length ≤ byteCapacity st

private def readResult (st : Store State) (args : List Value) : HostResult State :=
  match args with
  | [.i32 length, .i32 pointer] =>
      let bytes := st.host.input.take length.toNat
      if rangeInBounds st pointer.toNat bytes.length then
        .Return [.i32 (UInt32.ofNat bytes.length)]
          { st with
            mem := st.mem.writeBytes pointer.toNat bytes
            host :=
              { input := st.host.input.drop bytes.length
                output := st.host.output } }
      else
        .Trap st "stdio.read: out of bounds memory access"
  | _ => .Trap st "stdio.read: expected (length, pointer)"

private def writeResult (st : Store State) (args : List Value) : HostResult State :=
  match args with
  | [.i32 length, .i32 pointer] =>
      if rangeInBounds st pointer.toNat length.toNat then
        let bytes := st.mem.readBytes pointer.toNat length.toNat
        .Return []
          { st with
            host :=
              { input := st.host.input
                output := st.host.output ++ bytes } }
      else
        .Trap st "stdio.write: out of bounds memory access"
  | _ => .Trap st "stdio.write: expected (length, pointer)"

/-- Concrete implementation of the `read(length, pointer) -> length` import. -/
def readHost : HostFn State :=
  { params := [.i32, .i32]
    results := [.i32]
    invoke := readResult }

/-- Concrete implementation of the `write(length, pointer)` import. -/
def writeHost : HostFn State :=
  { params := [.i32, .i32]
    results := []
    invoke := writeResult }

/-- The two imports expected by a module using `StdIO`. -/
def imports : List ImportDecl :=
  [ { «module» := "stdio", name := "read",
      params := [.i32, .i32], results := [.i32] }
  , { «module» := "stdio", name := "write",
      params := [.i32, .i32], results := [] } ]

/-- The executable `StdIO` host environment. -/
def env : HostEnv State := { funcs := [readHost, writeHost] }

/-- Exact relational contract for `read`.  Keeping the contract named lets
program proofs hide the concrete resolver behind `HostEnv.Satisfies`. -/
def readContract : HostContract State :=
  fun st args result => result = readResult st args

/-- Exact relational contract for `write`. -/
def writeContract : HostContract State :=
  fun st args result => result = writeResult st args

/-- Relational specification corresponding to `StdIO.imports`. -/
def spec : HostSpec State :=
  { contracts := [readContract, writeContract] }

/-- The concrete environment satisfies the `StdIO` specification for every
module whose import list is exactly `StdIO.imports`. -/
theorem env_satisfies (m : Module) (himports : m.imports = imports) :
    env.Satisfies m spec := by
  intro i hi
  rw [himports] at hi
  rcases i with _ | _ | i
  · refine ⟨readHost, readContract, rfl, rfl, ?_⟩
    intro st args
    rfl
  · refine ⟨writeHost, writeContract, rfl, rfl, ?_⟩
    intro st args
    rfl
  · simp [imports] at hi
    omega

end Wasm.StdIO
