import Interpreter.Wasm.SmallStep
import Interpreter.Wasm.Decoder.Wat

/-! ## Example: multi-value

    End-to-end coverage for Wasm's multi-value extension through the
    authoritative small-step semantics. Function completion, block exit, and
    call return all transport result lists with length greater than one.

    All three Wasm functions live in one shared `multiValueModule`, so
    `CallsSwap` exercises the concrete call-frame transition against the same
    `Swap` body specified below.

    The checks cover exact execution, fuel-free total and partial correctness,
    and decoding `(block (type $sig))` annotations.

    * `swap_runs` executes a two-result body.
    * `swapSpec` specifies arbitrary input values.
    * `pairBlockSpec` exercises `block 0 2` and administrative block exit.
    * `callsSwapSpec` exercises a call frame returning two values to a caller.
    * `multiValueBlockTypeDecodes`  — decodes a `(block (type $sig))`
                                       WAT snippet and asserts the parsed
                                       block has the correct arity. Locks
                                       in the decoder fix that resolves
                                       `(type N)` block annotations
                                       against the module's type table.

    Operand stacks remain head-first (top at the head), while parameter locals
    are stored in declaration order. -/

namespace Wasm
open SmallStep

/-! ### Function bodies -/

/-- `swap a b` pops two i32s and pushes them in the opposite order. With
    `local 0 = a` (first pushed, deepest) and `local 1 = b` (second pushed,
    top), the body leaves `[a, b]` on the stack (`a` on top), so the call
    flips the top two i32s. -/
def Swap : Program := [.localGet 1, .localGet 0]

/-- One i32 in, *two* i32s out via a `block` annotated `(result i32 i32)`.
    The block computes `[x - 1, 1 + x]` (top = `x - 1`) and the function
    returns those two values verbatim. The order in the spec — `1 + x`,
    not `x + 1` — matches what the relational `.add` transition produces:
    `i32.add` is defined as `top + second`, and the body pushes `x` then
    `1` before `.add`, so `top = 1`, `second = x`, result = `1 + x`. -/
def PairBlock : Program := [
  .block 0 2 [
    .localGet 0, .const 1, .add,
    .localGet 0, .const 1, .sub
  ]
]

/-- Pushes `3` then `5`, calls function 0 (= `Swap`), then `.add`s the two
    returned values. Concrete result: `[.i32 8]`. -/
def CallsSwap : Program := [
  .const 3,
  .const 5,
  .call 0,
  .add
]

/-! ### Shared module

    One module holds all three functions so that `callsSwap`'s `.call 0`
    dispatches to the same `Swap` whose behavior is exercised by the
    relational call trace in `callsSwapSpec`. -/

def multiValueModule : Module :=
  { funcs :=
      [ { params  := [.i32, .i32], body := Swap,      results := [.i32, .i32] },
        { params  := [.i32],       body := PairBlock, results := [.i32, .i32] },
        { params  := [],           body := CallsSwap, results := [.i32] } ] }

def multiValueStore : MachineStore Unit :=
  { runtime := { instances := #[{ module := multiValueModule, host := {} }], entry := ⟨0⟩ }
    wasm := multiValueModule.initialStore }

def swapConfig (a b : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 a, .i32 b] }
        code := Swap
        resultArity := 2
        callerRemainder := [] }
    store := multiValueStore }

def pairBlockConfig (x : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 x] }
        code := PairBlock
        resultArity := 2
        callerRemainder := [] }
    store := multiValueStore }

def callsSwapConfig : Config Unit :=
  { expr := .running
      { locals := {}
        code := CallsSwap
        resultArity := 1
        callerRemainder := [] }
    store := multiValueStore }

/-! ### Check 1 — concrete small-step execution -/

theorem swap_runs :
    (runSteps 3 (swapConfig 1 2)).result.values? =
      some [.i32 1, .i32 2] := by
  rfl

/-! ### Check 2 — total and partial contracts for `Swap` -/

/-- For *any* two i32 inputs, `swap` returns them in flipped order. The
    interesting bit is the `Post`'s value-list has length 2 — every earlier
    example's `Post` carried a length-≤ 1 list. -/
theorem swapSpec (a b : UInt32) :
    TerminatesWith (swapConfig a b)
      (fun values _ => values = [.i32 a, .i32 b]) := by
  apply runSteps_success_terminates (fuel := 3)
    (values := [.i32 a, .i32 b])
  · rfl
  · rfl

theorem swap_partial (a b : UInt32) :
    PartiallyMeets (swapConfig a b)
      (fun values _ => values = [.i32 a, .i32 b]) := by
  apply runSteps_success_partiallyMeets (fuel := 3)
    (values := [.i32 a, .i32 b])
  · rfl
  · rfl

/-! ### Check 3 — multi-value block -/

theorem pairBlockSpec (x : UInt32) :
    TerminatesWith (pairBlockConfig x)
      (fun values _ => values = [.i32 (x - 1), .i32 (1 + x)]) := by
  apply runSteps_success_terminates (fuel := 9)
    (values := [.i32 (x - 1), .i32 (1 + x)])
  · rfl
  · rfl

theorem pairBlock_partial (x : UInt32) :
    PartiallyMeets (pairBlockConfig x)
      (fun values _ => values = [.i32 (x - 1), .i32 (1 + x)]) := by
  apply runSteps_success_partiallyMeets (fuel := 9)
    (values := [.i32 (x - 1), .i32 (1 + x)])
  · rfl
  · rfl

/-! ### Check 4 — caller that consumes both results of a multi-value call -/

/-- `callsSwap` exercises relational call return with multiple values: in
    every earlier example the returned stack had length 1, so this checks
    composition when `f.results.length > 1`. -/
theorem callsSwapSpec :
    TerminatesWith callsSwapConfig
      (fun values _ => values = [.i32 8]) := by
  apply runSteps_success_terminates (fuel := 8)
    (values := [.i32 8])
  · rfl
  · rfl

theorem callsSwap_partial :
    PartiallyMeets callsSwapConfig
      (fun values _ => values = [.i32 8]) := by
  apply runSteps_success_partiallyMeets (fuel := 8)
    (values := [.i32 8])
  · rfl
  · rfl

/-! ### Check 5 — decoder: `block (type $sig)` resolves to the right arity

    `wasm-tools` commonly emits multi-value block-types via the type
    table (`block (type $sig)`) rather than inline `(result i32 i32)`.
    Before the decoder fix, the `(type N)` reference on a block was
    silently dropped and the block degenerated to `paramArity = 0,
    resultArity = 0`. The check below decodes a small module that uses
    the type-table form and asserts the parsed block has the correct
    `(0, 2)` arity. -/

/-- Tiny WAT module: declares a type `$pair = () → (i32, i32)`, then a
    function that returns two i32s by entering a `block (type $pair)`
    holding two `i32.const`s. -/
private def multiValueWat : String :=
  "(module
     (type $pair (func (result i32 i32)))
     (func (result i32 i32)
       (block (type $pair)
         (i32.const 1)
         (i32.const 2))))"

/-- Pull the `(paramArity, resultArity)` of the first instruction of the
    first function, if it's a `block`. -/
private def firstBlockArity (m : Wasm.Module) : Option (Nat × Nat) :=
  match m.funcs.head? with
  | some f =>
    match f.body.head? with
    | some (.block ps rs _ _ _) => some (ps, rs)
    | _ => none
  | none => none

/-- The decoded module has a block with `(paramArity = 0, resultArity = 2)`
    — i.e., the `(type $pair)` reference was honoured. Closed by
    `native_decide` on the literal decoder output. -/
theorem multiValueBlockTypeDecodes :
    (Wasm.Decoder.Wat.decode multiValueWat).toOption.bind firstBlockArity
      = some (0, 2) := by
  native_decide

end Wasm
