import Interpreter.Wasm.SmallStep

/-!
# An explicit entropy-oracle host

`Random` exposes one import:

* `get : (i32, i32) -> ()` writes `length` bytes at `pointer`.

The host remains deterministic for a fixed `Oracle`.  Its state records an
infinite byte oracle and the index of the next unread byte.  Probability is
introduced separately, by placing a distribution on finite oracle prefixes;
it is not hidden inside the executable small-step semantics.

An out-of-bounds range or malformed argument list traps without changing the
store.  A zero-length request is valid at the byte immediately after memory.
-/

namespace Wasm.Random

/-- A byte in the mathematical entropy model.  `Fin 256` has the finite
structure needed by the probability library; it is converted to `UInt8` only
at the Wasm memory boundary. -/
abbrev Byte := Fin 256

/-- A deterministic realization of an infinite entropy source. -/
abbrev Oracle := Nat → Byte

/-- Mutable state owned by the random host. -/
structure State where
  oracle : Oracle
  cursor : Nat := 0

/-- Start reading an oracle at its first byte. -/
def State.ofOracle (oracle : Oracle) : State := { oracle }

/-- The all-zero oracle is useful as an inert default, not as a probabilistic
model. -/
def Oracle.zero : Oracle := fun _ => 0

instance : Inhabited State := ⟨State.ofOracle Oracle.zero⟩

/-- Avoid attempting to print the function-valued oracle. -/
instance : Repr State where
  reprPrec state _ := s!"Random.State(cursor={state.cursor})"

/-- The next `count` oracle bytes, converted to the representation stored in
linear memory. -/
def State.draw (state : State) (count : Nat) : List UInt8 :=
  List.ofFn fun index : Fin count =>
    UInt8.ofFin (state.oracle (state.cursor + index.val))

@[simp]
theorem State.draw_length (state : State) (count : Nat) :
    (state.draw count).length = count := by
  simp [State.draw]

/-- Advance past `count` bytes without changing the oracle realization. -/
def State.advance (state : State) (count : Nat) : State :=
  { state with cursor := state.cursor + count }

/-- The number of addressable bytes in the primary linear memory. -/
def byteCapacity (store : Store State) : Nat := store.mem.pages * 65536

/-- Whether the half-open range `[pointer, pointer + length)` is in memory. -/
def rangeInBounds (store : Store State) (pointer length : Nat) : Bool :=
  pointer + length ≤ byteCapacity store

/-- Pure implementation of `random.get(pointer, length)`. -/
def getResult (store : Store State) (args : List Value) : HostResult State :=
  match args with
  | [.i32 pointer, .i32 length] =>
      if rangeInBounds store pointer.toNat length.toNat then
        let bytes := store.host.draw length.toNat
        .Return []
          { store with
            mem := store.mem.writeBytes pointer.toNat bytes
            host := store.host.advance length.toNat }
      else
        .Trap store "random.get: out of bounds memory access"
  | _ => .Trap store "random.get: expected (pointer, length)"

/-- Concrete implementation of the `random.get(pointer, length)` import. -/
def getHost : HostFn State :=
  { params := [.i32, .i32]
    results := []
    invoke := getResult }

/-- The single import expected by a module using this random host. -/
def imports : List ImportDecl :=
  [{ «module» := "random", name := "get",
     params := [.i32, .i32], results := [] }]

/-- Executable environment for a fixed oracle stored in `Store.host`. -/
def env : HostEnv State := { funcs := [getHost] }

/-- Pathwise contract for `random.get`.  It fixes how the selected oracle
bytes affect memory while remaining parametric in the oracle itself. -/
def getContract : HostContract State :=
  fun store args result => result = getResult store args

/-- Relational specification corresponding to `Random.imports`. -/
def spec : HostSpec State := { contracts := [getContract] }

/-- The concrete environment satisfies the pathwise specification for every
module whose import list is exactly `Random.imports`. -/
theorem env_satisfies (module : Module) (himports : module.imports = imports) :
    env.Satisfies module spec := by
  intro index hindex
  rw [himports] at hindex
  have hzero : index = 0 := by
    simpa [imports] using hindex
  subst index
  refine ⟨getHost, getContract, rfl, rfl, ?_⟩
  intro store args
  rfl

end Wasm.Random
