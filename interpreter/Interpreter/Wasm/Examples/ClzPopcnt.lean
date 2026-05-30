import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-! ## Example: ClzPopcnt

    Unary i32 bit-counting ops (`clz`, `ctz`, `popcnt`) are implemented in
    `Semantics` via `clz32` / `ctz32` / `popcnt32` and have matching
    `wp_*_cons` rules in `Wp.Atomic`, but until this file no worked example
    or proof referred to them.

    One shared module exports three single-instruction bodies. Six checks:

    * `clz_zero_runs` / `ctz_eight_runs` / `popcnt_nibble_runs` — concrete
      `run` on representative inputs, closed by `native_decide`.
    * `clzSpec` / `ctzSpec` / `popcntSpec` — parametric `FuncSpec` for each
      body via `FuncSpec.of_wp_body` + `wp_run`.

    Wasm defines `clz`/`ctz` of zero as 32; `popcnt` counts set bits. -/

namespace Wasm

/-! ### Function bodies -/

/-- `clz x` — leading zero bits; 32 when `x = 0`. -/
def ClzBody : Program := [.localGet 0, .clz]

/-- `ctz x` — trailing zero bits; 32 when `x = 0`. -/
def CtzBody : Program := [.localGet 0, .ctz]

/-- `popcnt x` — number of one bits. -/
def PopcntBody : Program := [.localGet 0, .popcnt]

def clzPopcntModule : Module :=
  { funcs :=
      [ { params := [.i32], body := ClzBody,    results := [.i32] }
      , { params := [.i32], body := CtzBody,    results := [.i32] }
      , { params := [.i32], body := PopcntBody, results := [.i32] } ] }

/-! ### Helpers -/

private def runValues (fuel : Nat) (m : Module) (idx : Nat)
    (st : Store) (args : List Value) : List Value :=
  match run fuel m idx st args with
  | .Success vs _ => vs
  | _ => []

/-! ### Checks 1–3 — concrete `run` -/

theorem clz_zero_runs :
    runValues 10 clzPopcntModule 0 clzPopcntModule.initialStore [.i32 0]
      = [.i32 32] := by
  native_decide

theorem ctz_eight_runs :
    runValues 10 clzPopcntModule 1 clzPopcntModule.initialStore [.i32 8]
      = [.i32 3] := by
  native_decide

theorem popcnt_nibble_runs :
    runValues 10 clzPopcntModule 2 clzPopcntModule.initialStore [.i32 0xF]
      = [.i32 4] := by
  native_decide

/-! ### Checks 4–6 — `FuncSpec` via `wp` -/

theorem clzSpec (a : UInt32) :
    FuncSpec clzPopcntModule 0 (· = [.i32 a])
      (fun _ vs => vs = [.i32 (UInt32.ofNat (clz32 32 a))]) := by
  apply FuncSpec.of_wp_body
    (f := { params := [.i32], body := ClzBody, results := [.i32] })
  · rfl
  · rintro args rfl initial
    simp [Function.toLocals, Function.numParams]
    unfold ClzBody
    wp_run
    simp

theorem ctzSpec (a : UInt32) :
    FuncSpec clzPopcntModule 1 (· = [.i32 a])
      (fun _ vs => vs = [.i32 (UInt32.ofNat (ctz32 32 a))]) := by
  apply FuncSpec.of_wp_body
    (f := { params := [.i32], body := CtzBody, results := [.i32] })
  · rfl
  · rintro args rfl initial
    simp [Function.toLocals, Function.numParams]
    unfold CtzBody
    wp_run
    simp

theorem popcntSpec (a : UInt32) :
    FuncSpec clzPopcntModule 2 (· = [.i32 a])
      (fun _ vs => vs = [.i32 (UInt32.ofNat (popcnt32 32 a 0))]) := by
  apply FuncSpec.of_wp_body
    (f := { params := [.i32], body := PopcntBody, results := [.i32] })
  · rfl
  · rintro args rfl initial
    simp [Function.toLocals, Function.numParams]
    unfold PopcntBody
    wp_run
    simp

end Wasm
