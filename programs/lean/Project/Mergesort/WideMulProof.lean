import Project.Mergesort.FunctionSpecs

/-! Arithmetic facts for the generated `func254` wide multiply on the
decimal parser's `(acc, 10)` operands. -/

namespace Project.Mergesort.WideMulProof

def parserWideLow (x : UInt64) : UInt64 :=
  ((10 : UInt64) &&& (4294967295 : UInt64)) *
      (x &&& (4294967295 : UInt64)) +
    ((((10 : UInt64) >>> (32 % 64)) *
        (x &&& (4294967295 : UInt64)) +
      ((10 : UInt64) &&& (4294967295 : UInt64)) *
        (x >>> (32 % 64))) <<< (32 % 64))

def parserWideCross1 (x : UInt64) : UInt64 :=
  ((10 : UInt64) >>> (32 % 64)) *
    (x &&& (4294967295 : UInt64))

def parserWideCross (x : UInt64) : UInt64 :=
  parserWideCross1 x +
    ((10 : UInt64) &&& (4294967295 : UInt64)) *
      (x >>> (32 % 64))

def parserWideP0 (x : UInt64) : UInt64 :=
  ((10 : UInt64) &&& (4294967295 : UInt64)) *
    (x &&& (4294967295 : UInt64))

def parserWideHigh (x : UInt64) : UInt64 :=
  ((((10 : UInt64) >>> (32 % 64)) * (x >>> (32 % 64)) +
      ((UInt64.ofNat
          (if parserWideCross x < parserWideCross1 x then
            (1 : UInt32)
          else 0).toNat <<< (32 % 64)) |||
        (parserWideCross x >>> (32 % 64)))) +
    UInt64.ofNat
      (if parserWideLow x < parserWideP0 x then (1 : UInt32) else 0).toNat) +
    (0 * x + (10 : UInt64) * 0)

theorem parserWideLow_eq (x : UInt64) : parserWideLow x = x * 10 := by
  unfold parserWideLow
  bv_decide

theorem parserWideHigh_eq_zero (x : UInt64)
    (hbound : x ≤ 1844674407370955161) : parserWideHigh x = 0 := by
  unfold parserWideHigh parserWideLow parserWideP0 parserWideCross
    parserWideCross1
  split <;> split <;> simp_all <;> bv_decide

end Project.Mergesort.WideMulProof
