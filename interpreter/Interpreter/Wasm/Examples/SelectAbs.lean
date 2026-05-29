import Interpreter.Wasm.Wp.Tactic

namespace Wasm

-- -----------------------------------------------------------------------
-- Example 1: Absolute value
-- -----------------------------------------------------------------------

/-! ### SelectAbs

We want: if n <ₛ 0 then −n else n.
- v1 = −n  (returned when c ≠ 0, i.e. n is negative)
- v2 = n   (returned when c = 0, i.e. n is non-negative)
- c  = (n <ₛ 0)

Push order: −n, n, (n <ₛ 0), select
-/

def SelectAbs : Program := [
  .const 0,                 -- push 0
  .localGet 0,              -- push n      stack: [n, 0]
  .sub,                     -- 0 − n = −n  stack: [−n]     ← v1
  .localGet 0,              -- push n      stack: [n, −n]  ← v2
  .localGet 0,              -- push n (for comparison)
  .const 0,                 -- push 0
  .ltS,                     -- n <ₛ 0 ?   stack: [c, n, −n]
  .select                   -- if c≠0: −n  else: n
]

#eval   -- expected: Fallthrough … values = [.i32 5]
  let m : Module :=
    { funcs := [{ params := [.i32], locals := [], body := SelectAbs }] }
  run 100 m 0 m.initialStore [.i32 5]

#eval   -- expected: Fallthrough … values = [.i32 3]  (input = −3)
  let m : Module :=
    { funcs := [{ params := [.i32], locals := [], body := SelectAbs }] }
  run 100 m 0 m.initialStore [.i32 (Int32.ofInt (-3)).toUInt32]

#eval   -- expected: Fallthrough … values = [.i32 0]
  let m : Module :=
    { funcs := [{ params := [.i32], locals := [], body := SelectAbs }] }
  run 100 m 0 m.initialStore [.i32 0]

theorem selectAbsSpec (m : Module) (st : Store) (n : UInt32) :
    wp m SelectAbs
      (fun c => ∃ st' s',
        c = .Fallthrough st' s' ∧
        s'.values = [.i32 (if n.toInt32 < 0 then (0 : UInt32) - n else n)])
      st { params := [.i32 n], locals := [], values := [] } := by
  unfold SelectAbs
  -- wp_run fires all @[simp] lemmas including wp_select_cons
  wp_run
  simp [Int32.lt_iff_toInt32_lt]
  split <;> rfl

-- -----------------------------------------------------------------------
-- Example 2: Unsigned minimum
-- -----------------------------------------------------------------------

/-! ### SelectMin

We want: if a <ᵤ b then a else b.
- v1 = a  (returned when c ≠ 0, i.e. a < b)
- v2 = b  (returned when c = 0, i.e. a ≥ b)
- c  = (a <ᵤ b)

Push order: a, b, (a <ᵤ b), select
-/

def SelectMin : Program := [
  .localGet 0,              -- push a               ← v1
  .localGet 1,              -- push b               ← v2
  .localGet 0,              -- push a (for cmp)
  .localGet 1,              -- push b (for cmp)
  .ltU,                     -- a <ᵤ b ?             ← c
  .select                   -- if a<b: a  else: b
]

#eval   -- expected: Fallthrough … values = [.i32 3]
  let m : Module :=
    { funcs := [{ params := [.i32, .i32], locals := [], body := SelectMin }] }
  run 100 m 0 m.initialStore [.i32 3, .i32 7]

#eval   -- expected: Fallthrough … values = [.i32 2]
  let m : Module :=
    { funcs := [{ params := [.i32, .i32], locals := [], body := SelectMin }] }
  run 100 m 0 m.initialStore [.i32 9, .i32 2]

theorem selectMinSpec (m : Module) (st : Store) (a b : UInt32) :
    wp m SelectMin
      (fun c => ∃ st' s',
        c = .Fallthrough st' s' ∧
        s'.values = [.i32 (min a b)])
      st { params := [.i32 a, .i32 b], locals := [], values := [] } := by
  unfold SelectMin
  wp_run
  simp [min_def]
  split <;> omega

end Wasm