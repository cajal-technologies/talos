import Interpreter.Wasm.SmallStep

/-! ## Example: ClzPopcnt

    Unary i32 bit-counting ops (`clz`, `ctz`, `popcnt`) are executed by the
    authoritative small-step machine.

    One shared module exports three single-instruction bodies. Six checks:

    * `clz_zero_runs` / `ctz_eight_runs` / `popcnt_nibble_runs` — concrete
      small-step traces on representative inputs.
    * `clzSpec` / `ctzSpec` / `popcntSpec` — parametric, fuel-free
      `TerminatesWith` contracts.
    * matching `*_partial` theorems preserve partial-correctness intent for
      Iris clients.

    Wasm defines `clz`/`ctz` of zero as 32; `popcnt` counts set bits. -/

namespace Wasm
open SmallStep

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

def bitCountConfig (body : Program) (a : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 a] }
        code := body
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := clzPopcntModule, host := {} }], entry := ⟨0⟩ }
        wasm := clzPopcntModule.initialStore } }

def clzConfig (a : UInt32) : Config Unit := bitCountConfig ClzBody a
def ctzConfig (a : UInt32) : Config Unit := bitCountConfig CtzBody a
def popcntConfig (a : UInt32) : Config Unit := bitCountConfig PopcntBody a

/-! ### Checks 1–3 — concrete small-step execution -/

theorem clz_zero_runs :
    (runSteps 3 (clzConfig 0)).result.values? = some [.i32 32] := by
  rfl

theorem ctz_eight_runs :
    (runSteps 3 (ctzConfig 8)).result.values? = some [.i32 3] := by
  rfl

theorem popcnt_nibble_runs :
    (runSteps 3 (popcntConfig 0xF)).result.values? = some [.i32 4] := by
  rfl

/-! ### Checks 4–6 — fuel-free small-step specifications -/

theorem clzSpec (a : UInt32) :
    TerminatesWith (clzConfig a)
      (fun values _ =>
        values = [.i32 (UInt32.ofNat (clz32 32 a))]) := by
  apply runSteps_success_terminates (fuel := 3)
    (values := [.i32 (UInt32.ofNat (clz32 32 a))])
  · rfl
  · rfl

theorem ctzSpec (a : UInt32) :
    TerminatesWith (ctzConfig a)
      (fun values _ =>
        values = [.i32 (UInt32.ofNat (ctz32 32 a))]) := by
  apply runSteps_success_terminates (fuel := 3)
    (values := [.i32 (UInt32.ofNat (ctz32 32 a))])
  · rfl
  · rfl

theorem popcntSpec (a : UInt32) :
    TerminatesWith (popcntConfig a)
      (fun values _ =>
        values = [.i32 (UInt32.ofNat (popcnt32 32 a 0))]) := by
  apply runSteps_success_terminates (fuel := 3)
    (values := [.i32 (UInt32.ofNat (popcnt32 32 a 0))])
  · rfl
  · rfl

theorem clz_partial (a : UInt32) :
    PartiallyMeets (clzConfig a)
      (fun values _ =>
        values = [.i32 (UInt32.ofNat (clz32 32 a))]) := by
  apply runSteps_success_partiallyMeets (fuel := 3)
    (values := [.i32 (UInt32.ofNat (clz32 32 a))])
  · rfl
  · rfl

theorem ctz_partial (a : UInt32) :
    PartiallyMeets (ctzConfig a)
      (fun values _ =>
        values = [.i32 (UInt32.ofNat (ctz32 32 a))]) := by
  apply runSteps_success_partiallyMeets (fuel := 3)
    (values := [.i32 (UInt32.ofNat (ctz32 32 a))])
  · rfl
  · rfl

theorem popcnt_partial (a : UInt32) :
    PartiallyMeets (popcntConfig a)
      (fun values _ =>
        values = [.i32 (UInt32.ofNat (popcnt32 32 a 0))]) := by
  apply runSteps_success_partiallyMeets (fuel := 3)
    (values := [.i32 (UInt32.ofNat (popcnt32 32 a 0))])
  · rfl
  · rfl

end Wasm
