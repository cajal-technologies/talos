import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Call
import Interpreter.Wasm.Spec.Termination
import Interpreter.Wasm.Decoder.Wat

/-! ## Example: multi-value

    End-to-end coverage for Wasm's multi-value extension. The interpreter,
    decoder, and WP layer are already arity-generic
    (`Function.results : List ValueType`,
    `Instruction.block paramArity resultArity`, `wp_block_cons` over an
    arbitrary `rs : Nat`, `wp_call_cons` passing `vs : List Value` of any
    length, `FuncSpec.of_wp_body` taking `s'.values.take f.results.length`);
    this file is the first place those code paths are exercised with
    `results.length > 1` at the *spec* level.

    All three Wasm functions live in one shared `multiValueModule` so that
    `callsSwap`'s `call 0` resolves against the same module its caller's
    `FuncSpec` is stated on — `wp_call_cons` needs the callee's spec and the
    surrounding goal to mention the same module.

    Five progressively stronger checks:

    * `swap_runs`                   — concrete `run` of a 2-result function,
                                       compared against an expected `List
                                       Value` via `native_decide`. (We can't
                                       use `TerminatesWith` directly here
                                       because `Result` carries a `Store`
                                       and `Store` has no `DecidableEq`
                                       instance.)
    * `swapSpec`                    — abstract `FuncSpec` for the 2-result
                                       `swap`, via `FuncSpec.of_wp_body`.
                                       Exercises
                                       `Post (s'.values.take 2 ++ ...)`
                                       end-to-end.
    * `pairBlockSpec`               — `FuncSpec` whose body is a single
                                       `block 0 2 [...]`. Exercises
                                       `wp_block_cons` with
                                       `resultArity = 2`.
    * `callsSwapSpec`               — `FuncSpec` for a function that calls
                                       `swap` and reduces both returned
                                       values. Exercises `wp_call_cons`
                                       against a multi-value `vs`.
    * `multiValueBlockTypeDecodes`  — decodes a `(block (type $sig))`
                                       WAT snippet and asserts the parsed
                                       block has the correct arity. Locks
                                       in the decoder fix that resolves
                                       `(type N)` block annotations
                                       against the module's type table.

    Convention reminder: `FuncSpec`'s `args` parameter is the *caller's
    operand stack at the call site*, head = top. For a function with two
    `i32` parameters called as `(i32.const a) (i32.const b) (call $f)`,
    `args = [.i32 b, .i32 a]` (b on top); `run` then reverses the prefix to
    set `local 0 = a`, `local 1 = b`. -/

namespace Wasm

/-! ### Function bodies -/

/-- `swap a b` pops two i32s and pushes them in the opposite order. With
    `local 0 = a` (first pushed, deepest) and `local 1 = b` (second pushed,
    top), the body leaves `[a, b]` on the stack (`a` on top), so the call
    flips the top two i32s. -/
def Swap : Program := [.localGet 1, .localGet 0]

/-- One i32 in, *two* i32s out via a `block` annotated `(result i32 i32)`.
    The block computes `[x - 1, 1 + x]` (top = `x - 1`) and the function
    returns those two values verbatim. The order in the spec — `1 + x`,
    not `x + 1` — matches what `wp_add_cons` literally produces:
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
    dispatches to the same `Swap` that `swapSpec` was proved on — which is
    what lets `wp_call_cons (swapSpec 3 5)` compose inside `callsSwapSpec`. -/

def multiValueModule : Module :=
  { funcs :=
      [ { params  := [.i32, .i32], body := Swap,      results := [.i32, .i32] },
        { params  := [.i32],       body := PairBlock, results := [.i32, .i32] },
        { params  := [],           body := CallsSwap, results := [.i32] } ] }

/-! ### Check 1 — concrete `run` of a multi-value function -/

/-- Helper: extract just the values list from a `Result`. `List Value` has
    `DecidableEq` (so `native_decide` works on it), whereas `Result` carries
    a `Store` field and `Store` doesn't. Returns `[]` on any non-success
    outcome so the helper is total. Same idiom as `MemGrow.runValues`. -/
private def runValues (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store Unit) (args : List Value) : List Value :=
  match run fuel m idx st args with
  | .Success vs _ => vs
  | _ => []

/-- Pushing `1` then `2` (so `2` is on top) and calling `swap` leaves
    `[1, 2]` (now `1` on top). Closed by `native_decide`, which compiles
    `run` to native code and evaluates it. -/
theorem swap_runs :
    runValues 10 multiValueModule 0 multiValueModule.initialStore
      [.i32 2, .i32 1] = [.i32 1, .i32 2] := by
  native_decide

/-! ### Check 2 — abstract `FuncSpec` for `Swap` -/

/-- For *any* two i32 inputs, `swap` returns them in flipped order. The
    interesting bit is the `Post`'s value-list has length 2 — every earlier
    example's `Post` carried a length-≤ 1 list. -/
theorem swapSpec (a b : UInt32) :
    FuncSpec ({} : HostEnv Unit) multiValueModule 0 (· = [.i32 b, .i32 a])
      (fun _ vs => vs = [.i32 a, .i32 b]) := by
  apply FuncSpec.of_wp_body
    (f := { params := [.i32, .i32], body := Swap, results := [.i32, .i32] })
  · rfl
  · rintro args rfl initial
    simp [Function.toLocals, Function.numParams]
    unfold Swap
    wp_run
    simp

/-! ### Check 3 — `FuncSpec` whose body is a single multi-value block -/

theorem pairBlockSpec (x : UInt32) :
    FuncSpec ({} : HostEnv Unit) multiValueModule 1 (· = [.i32 x])
      (fun _ vs => vs = [.i32 (x - 1), .i32 (1 + x)]) := by
  apply FuncSpec.of_wp_body
    (f := { params := [.i32], body := PairBlock, results := [.i32, .i32] })
  · rfl
  · rintro args rfl initial
    simp [Function.toLocals, Function.numParams]
    unfold PairBlock
    apply wp_block_cons
    wp_run
    simp

/-! ### Check 4 — caller that consumes both results of a multi-value call -/

/-- `callsSwap` exercises `wp_call_cons` against a multi-value `vs`: in
    every earlier example `vs` had length 1, so this is the first test that
    the rule composes when `f.results.length > 1`. -/
theorem callsSwapSpec :
    FuncSpec ({} : HostEnv Unit) multiValueModule 2 (· = [])
      (fun _ vs => vs = [.i32 8]) := by
  apply FuncSpec.of_wp_body
    (f := { params := [], body := CallsSwap, results := [.i32] })
  · rfl
  · rintro args rfl initial
    simp [Function.toLocals, Function.numParams]
    unfold CallsSwap
    wp_run
    apply wp_call_cons
      (Pre  := (· = [.i32 5, .i32 3]))
      (Post := fun _ vs => vs = [.i32 3, .i32 5])
      (swapSpec 3 5)
    · rfl
    · rintro st' vs rfl
      wp_run
      decide

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
    | some (.block ps rs _) => some (ps, rs)
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
