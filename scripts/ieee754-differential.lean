import Interpreter.Wasm.IEEE754

/-!
Runtime differential checks for the pure IEEE-754 implementation.
Run from `interpreter/` with:
  lake env lean --run ../scripts/ieee754-differential.lean

The native oracle below preserves the previous floating-point implementation.
It is used only for testing, never for constructing Lean proofs or executing
Wasm in the reference interpreter. A passing run is regression evidence,
not a theorem equating the pure model with opaque native externs.
-/

namespace Wasm.IEEE754Native

/-! ### Canonical NaN -/

/-- Canonical quiet `f32` NaN: sign 0, exponent all ones, top mantissa bit set. -/
def f32CanonicalNaN : UInt32 := 0x7FC00000
/-- Canonical quiet `f64` NaN. -/
def f64CanonicalNaN : UInt64 := 0x7FF8000000000000

/-- Normalise a numeric result: any NaN becomes the canonical NaN. -/
def f32Canon (b : UInt32) : UInt32 :=
  if (Float32.ofBits b).isNaN then f32CanonicalNaN else b
def f64Canon (b : UInt64) : UInt64 :=
  if (Float.ofBits b).isNaN then f64CanonicalNaN else b

/-! ### Sign-bit operations

Defined directly on the bits, matching the spec; NaN payloads survive. -/

def f32Abs (a : UInt32) : UInt32 := a &&& 0x7FFFFFFF
def f64Abs (a : UInt64) : UInt64 := a &&& 0x7FFFFFFFFFFFFFFF
def f32Neg (a : UInt32) : UInt32 := a ^^^ 0x80000000
def f64Neg (a : UInt64) : UInt64 := a ^^^ 0x8000000000000000
def f32Copysign (a b : UInt32) : UInt32 := (a &&& 0x7FFFFFFF) ||| (b &&& 0x80000000)
def f64Copysign (a b : UInt64) : UInt64 :=
  (a &&& 0x7FFFFFFFFFFFFFFF) ||| (b &&& 0x8000000000000000)

/-! ### Arithmetic -/

def f32Add (a b : UInt32) : UInt32 := f32Canon (Float32.ofBits a + Float32.ofBits b).toBits
def f32Sub (a b : UInt32) : UInt32 := f32Canon (Float32.ofBits a - Float32.ofBits b).toBits
def f32Mul (a b : UInt32) : UInt32 := f32Canon (Float32.ofBits a * Float32.ofBits b).toBits
def f32Div (a b : UInt32) : UInt32 := f32Canon (Float32.ofBits a / Float32.ofBits b).toBits
def f64Add (a b : UInt64) : UInt64 := f64Canon (Float.ofBits a + Float.ofBits b).toBits
def f64Sub (a b : UInt64) : UInt64 := f64Canon (Float.ofBits a - Float.ofBits b).toBits
def f64Mul (a b : UInt64) : UInt64 := f64Canon (Float.ofBits a * Float.ofBits b).toBits
def f64Div (a b : UInt64) : UInt64 := f64Canon (Float.ofBits a / Float.ofBits b).toBits

def f32Sqrt  (a : UInt32) : UInt32 := f32Canon (Float32.ofBits a).sqrt.toBits
def f64Sqrt  (a : UInt64) : UInt64 := f64Canon (Float.ofBits a).sqrt.toBits
def f32Ceil  (a : UInt32) : UInt32 := f32Canon (Float32.ofBits a).ceil.toBits
def f64Ceil  (a : UInt64) : UInt64 := f64Canon (Float.ofBits a).ceil.toBits
def f32Floor (a : UInt32) : UInt32 := f32Canon (Float32.ofBits a).floor.toBits
def f64Floor (a : UInt64) : UInt64 := f64Canon (Float.ofBits a).floor.toBits

/-- Round toward zero: ceiling for negatives, floor otherwise. -/
def f32Trunc (a : UInt32) : UInt32 :=
  let x := Float32.ofBits a
  f32Canon (if x.toFloat < 0.0 then x.ceil else x.floor).toBits
def f64Trunc (a : UInt64) : UInt64 :=
  let x := Float.ofBits a
  f64Canon (if x < 0.0 then x.ceil else x.floor).toBits

/-- Round to nearest integer, ties to even. -/
def f32Nearest (a : UInt32) : UInt32 :=
  let x := Float32.ofBits a
  let fl := x.floor
  let cl := x.ceil
  let dlo := x.toFloat - fl.toFloat
  let dhi := cl.toFloat - x.toFloat
  let r := if dlo < dhi then fl
           else if dhi < dlo then cl
           else if (fl.toFloat * 0.5).floor * 2.0 == fl.toFloat then fl else cl
  f32Canon r.toBits
def f64Nearest (a : UInt64) : UInt64 :=
  let x := Float.ofBits a
  let fl := x.floor
  let cl := x.ceil
  let dlo := x - fl
  let dhi := cl - x
  let r := if dlo < dhi then fl
           else if dhi < dlo then cl
           else if (fl * 0.5).floor * 2.0 == fl then fl else cl
  f64Canon r.toBits

/-! ### min / max

NaN in either operand yields the canonical NaN. When both operands are zero
the sign is resolved per spec: `min` keeps a negative zero, `max` a positive
zero (`|||` / `&&&` on the sign bits). -/

def f32Min (a b : UInt32) : UInt32 :=
  let x := Float32.ofBits a; let y := Float32.ofBits b
  if x.isNaN || y.isNaN then f32CanonicalNaN
  else if x.toFloat == 0.0 && y.toFloat == 0.0 then a ||| b
  else if x.toFloat < y.toFloat then a else b
def f32Max (a b : UInt32) : UInt32 :=
  let x := Float32.ofBits a; let y := Float32.ofBits b
  if x.isNaN || y.isNaN then f32CanonicalNaN
  else if x.toFloat == 0.0 && y.toFloat == 0.0 then a &&& b
  else if x.toFloat < y.toFloat then b else a
def f64Min (a b : UInt64) : UInt64 :=
  let x := Float.ofBits a; let y := Float.ofBits b
  if x.isNaN || y.isNaN then f64CanonicalNaN
  else if x == 0.0 && y == 0.0 then a ||| b
  else if x < y then a else b
def f64Max (a b : UInt64) : UInt64 :=
  let x := Float.ofBits a; let y := Float.ofBits b
  if x.isNaN || y.isNaN then f64CanonicalNaN
  else if x == 0.0 && y == 0.0 then a &&& b
  else if x < y then b else a

/-! ### Comparisons

IEEE-754 ordered comparisons (any comparison with NaN is `false`, except
`ne`; `+0` equals `-0`). The `f32` operands are promoted to `f64` first,
which is exact and preserves ordering, equality and NaN-ness. Each yields a
`Bool`; the interpreter lands it as an `i32` `0`/`1`. -/

def f32Eq (a b : UInt32) : Bool := (Float32.ofBits a).toFloat == (Float32.ofBits b).toFloat
def f32Ne (a b : UInt32) : Bool := !((Float32.ofBits a).toFloat == (Float32.ofBits b).toFloat)
def f32Lt (a b : UInt32) : Bool := decide ((Float32.ofBits a).toFloat < (Float32.ofBits b).toFloat)
def f32Gt (a b : UInt32) : Bool := decide ((Float32.ofBits b).toFloat < (Float32.ofBits a).toFloat)
def f32Le (a b : UInt32) : Bool := decide ((Float32.ofBits a).toFloat ≤ (Float32.ofBits b).toFloat)
def f32Ge (a b : UInt32) : Bool := decide ((Float32.ofBits b).toFloat ≤ (Float32.ofBits a).toFloat)
def f64Eq (a b : UInt64) : Bool := Float.ofBits a == Float.ofBits b
def f64Ne (a b : UInt64) : Bool := !(Float.ofBits a == Float.ofBits b)
def f64Lt (a b : UInt64) : Bool := decide (Float.ofBits a < Float.ofBits b)
def f64Gt (a b : UInt64) : Bool := decide (Float.ofBits b < Float.ofBits a)
def f64Le (a b : UInt64) : Bool := decide (Float.ofBits a ≤ Float.ofBits b)
def f64Ge (a b : UInt64) : Bool := decide (Float.ofBits b ≤ Float.ofBits a)

/-! ### Integer → float conversions

`_s` reads the operand as signed, `_u` as unsigned. These never produce a
NaN, but may round to the nearest representable value. -/

def f32ConvertI32S (a : UInt32) : UInt32 := (Float32.ofInt a.toInt32.toInt).toBits
def f32ConvertI32U (a : UInt32) : UInt32 := (Float32.ofNat a.toNat).toBits
def f32ConvertI64S (a : UInt64) : UInt32 := (Float32.ofInt a.toInt64.toInt).toBits
def f32ConvertI64U (a : UInt64) : UInt32 := (Float32.ofNat a.toNat).toBits
def f64ConvertI32S (a : UInt32) : UInt64 := (Float.ofInt a.toInt32.toInt).toBits
def f64ConvertI32U (a : UInt32) : UInt64 := (Float.ofNat a.toNat).toBits
def f64ConvertI64S (a : UInt64) : UInt64 := (Float.ofInt a.toInt64.toInt).toBits
def f64ConvertI64U (a : UInt64) : UInt64 := (Float.ofNat a.toNat).toBits

/-! ### float ↔ float -/

def f64PromoteF32 (a : UInt32) : UInt64 := f64Canon (Float32.ofBits a).toFloat.toBits
def f32DemoteF64  (a : UInt64) : UInt32 := f32Canon (Float.ofBits a).toFloat32.toBits

/-! ### float → integer (trapping)

`none` reports a wasm trap: NaN, infinity, or a value whose truncation falls
outside the target's range. `f32` operands are promoted to `f64` first —
exact, so the range checks against the integer bounds stay precise. The
unsigned-`i64` and signed-`i64` upper bounds (`2^64`, `2^63`) are exclusive
because the largest in-range integers are not themselves representable. -/

private def truncReal (x : Float) : Option Float :=
  if x.isNaN then none else some (if x < 0.0 then x.ceil else x.floor)

private def truncI32S (x : Float) : Option UInt32 :=
  match truncReal x with
  | none => none
  | some t => if (-2147483648.0 : Float) ≤ t ∧ t ≤ (2147483647.0 : Float)
              then some t.toInt64.toUInt64.toUInt32 else none
private def truncI32U (x : Float) : Option UInt32 :=
  match truncReal x with
  | none => none
  | some t => if (0.0 : Float) ≤ t ∧ t ≤ (4294967295.0 : Float)
              then some t.toUInt64.toUInt32 else none
private def truncI64S (x : Float) : Option UInt64 :=
  match truncReal x with
  | none => none
  | some t => if (-9223372036854775808.0 : Float) ≤ t ∧ t < (9223372036854775808.0 : Float)
              then some t.toInt64.toUInt64 else none
private def truncI64U (x : Float) : Option UInt64 :=
  match truncReal x with
  | none => none
  | some t => if (0.0 : Float) ≤ t ∧ t < (18446744073709551616.0 : Float)
              then some t.toUInt64 else none

def i32TruncF32S (a : UInt32) : Option UInt32 := truncI32S (Float32.ofBits a).toFloat
def i32TruncF32U (a : UInt32) : Option UInt32 := truncI32U (Float32.ofBits a).toFloat
def i32TruncF64S (a : UInt64) : Option UInt32 := truncI32S (Float.ofBits a)
def i32TruncF64U (a : UInt64) : Option UInt32 := truncI32U (Float.ofBits a)
def i64TruncF32S (a : UInt32) : Option UInt64 := truncI64S (Float32.ofBits a).toFloat
def i64TruncF32U (a : UInt32) : Option UInt64 := truncI64U (Float32.ofBits a).toFloat
def i64TruncF64S (a : UInt64) : Option UInt64 := truncI64S (Float.ofBits a)
def i64TruncF64U (a : UInt64) : Option UInt64 := truncI64U (Float.ofBits a)

/-! ### float → integer (saturating)

`trunc_sat` never traps: NaN maps to `0`, out-of-range values saturate to the
target's minimum or maximum. -/

private def satI32S (x : Float) : UInt32 :=
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
       if t ≤ (-2147483648.0 : Float) then 0x80000000
       else if t ≥ (2147483647.0 : Float) then 0x7FFFFFFF
       else t.toInt64.toUInt64.toUInt32
private def satI32U (x : Float) : UInt32 :=
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
       if t ≤ (0.0 : Float) then 0
       else if t ≥ (4294967295.0 : Float) then 0xFFFFFFFF
       else t.toUInt64.toUInt32
private def satI64S (x : Float) : UInt64 :=
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
       if t ≤ (-9223372036854775808.0 : Float) then 0x8000000000000000
       else if t ≥ (9223372036854775808.0 : Float) then 0x7FFFFFFFFFFFFFFF
       else t.toInt64.toUInt64
private def satI64U (x : Float) : UInt64 :=
  if x.isNaN then 0
  else let t := if x < 0.0 then x.ceil else x.floor
       if t ≤ (0.0 : Float) then 0
       else if t ≥ (18446744073709551616.0 : Float) then 0xFFFFFFFFFFFFFFFF
       else t.toUInt64

def i32TruncSatF32S (a : UInt32) : UInt32 := satI32S (Float32.ofBits a).toFloat
def i32TruncSatF32U (a : UInt32) : UInt32 := satI32U (Float32.ofBits a).toFloat
def i32TruncSatF64S (a : UInt64) : UInt32 := satI32S (Float.ofBits a)
def i32TruncSatF64U (a : UInt64) : UInt32 := satI32U (Float.ofBits a)
def i64TruncSatF32S (a : UInt32) : UInt64 := satI64S (Float32.ofBits a).toFloat
def i64TruncSatF32U (a : UInt32) : UInt64 := satI64U (Float32.ofBits a).toFloat
def i64TruncSatF64S (a : UInt64) : UInt64 := satI64S (Float.ofBits a)
def i64TruncSatF64U (a : UInt64) : UInt64 := satI64U (Float.ofBits a)

end Wasm.IEEE754Native


open Wasm Wasm.IEEE754Native

def binaryCases32 : List (String × (Nat → Nat → Nat) × (UInt32 → UInt32 → UInt32)) :=
  [("add32", IEEE754.add IEEE754.binary32, f32Add), ("sub32", IEEE754.sub IEEE754.binary32, f32Sub),
   ("mul32", IEEE754.mul IEEE754.binary32, f32Mul), ("div32", IEEE754.div IEEE754.binary32, f32Div),
   ("min32", IEEE754.minimum IEEE754.binary32, f32Min), ("max32", IEEE754.maximum IEEE754.binary32, f32Max)]
def binaryCases64 : List (String × (Nat → Nat → Nat) × (UInt64 → UInt64 → UInt64)) :=
  [("add64", IEEE754.add IEEE754.binary64, f64Add), ("sub64", IEEE754.sub IEEE754.binary64, f64Sub),
   ("mul64", IEEE754.mul IEEE754.binary64, f64Mul), ("div64", IEEE754.div IEEE754.binary64, f64Div),
   ("min64", IEEE754.minimum IEEE754.binary64, f64Min), ("max64", IEEE754.maximum IEEE754.binary64, f64Max)]
def unaryCases32 : List (String × (Nat → Nat) × (UInt32 → UInt32)) :=
  [("sqrt32", IEEE754.sqrt IEEE754.binary32, f32Sqrt),
   ("ceil32", IEEE754.roundIntegral IEEE754.binary32 .towardPositive, f32Ceil),
   ("floor32", IEEE754.roundIntegral IEEE754.binary32 .towardNegative, f32Floor),
   ("trunc32", IEEE754.roundIntegral IEEE754.binary32 .towardZero, f32Trunc),
   ("nearest32", IEEE754.roundIntegral IEEE754.binary32 .nearestEven, f32Nearest)]
def unaryCases64 : List (String × (Nat → Nat) × (UInt64 → UInt64)) :=
  [("sqrt64", IEEE754.sqrt IEEE754.binary64, f64Sqrt),
   ("ceil64", IEEE754.roundIntegral IEEE754.binary64 .towardPositive, f64Ceil),
   ("floor64", IEEE754.roundIntegral IEEE754.binary64 .towardNegative, f64Floor),
   ("trunc64", IEEE754.roundIntegral IEEE754.binary64 .towardZero, f64Trunc),
   ("nearest64", IEEE754.roundIntegral IEEE754.binary64 .nearestEven, f64Nearest)]
def edges32 : List Nat := [0,1,2,0x007fffff,0x00800000,0x00800001,
  0x3effffff,0x3f000000,0x3f000001,0x3f7fffff,0x3f800000,0x3f800001,
  0x40000000,0x4b000000,0x4effffff,0x4f000000,0x7f7fffff,0x7f800000,0x7fc00000,0x7f800001]
def edges64 : List Nat := [0,1,2,0x000fffffffffffff,0x0010000000000000,0x0010000000000001,
  0x3fdfffffffffffff,0x3fe0000000000000,0x3fe0000000000001,0x3fefffffffffffff,
  0x3ff0000000000000,0x3ff0000000000001,0x4000000000000000,0x4330000000000000,
  0x43dfffffffffffff,0x43e0000000000000,0x7fefffffffffffff,0x7ff0000000000000,0x7ff8000000000000,0x7ff0000000000001]

def check (name : String) (a b got want : Nat) : StateT (Nat × Nat) IO Unit := do
  let (count, failures) ← get
  set (count+1, failures + if got == want then 0 else 1)
  if got != want && failures < 12 then
    liftM (IO.println s!"{name}: a={a}, b={b}, got={got}, expected={want}")

def check32 (a b : Nat) : StateT (Nat × Nat) IO Unit := do
  for (name,pureOp,nativeOp) in binaryCases32 do
    check name a b (pureOp a b) (nativeOp a.toUInt32 b.toUInt32).toNat
  for (name,pureOp,nativeOp) in unaryCases32 do
    check name a 0 (pureOp a) (nativeOp a.toUInt32).toNat
  check "eq32" a b (if IEEE754.eq IEEE754.binary32 a b then 1 else 0) (if f32Eq a.toUInt32 b.toUInt32 then 1 else 0)
  check "lt32" a b (if IEEE754.lt IEEE754.binary32 a b then 1 else 0) (if f32Lt a.toUInt32 b.toUInt32 then 1 else 0)
  check "le32" a b (if IEEE754.le IEEE754.binary32 a b then 1 else 0) (if f32Le a.toUInt32 b.toUInt32 then 1 else 0)
  check "promote" a 0 (IEEE754.convert IEEE754.binary32 IEEE754.binary64 a) (f64PromoteF32 a.toUInt32).toNat
  check "ofUInt32_f32" a 0 (IEEE754.ofInt IEEE754.binary32 a) (f32ConvertI32U a.toUInt32).toNat
  check "ofInt32_f32" a 0 (IEEE754.ofInt IEEE754.binary32 a.toUInt32.toInt32.toInt) (f32ConvertI32S a.toUInt32).toNat
  check "satI32S_f32" a 0 (IEEE754.saturate IEEE754.binary32 a (-2147483648) 2147483647).toInt32.toUInt32.toNat (i32TruncSatF32S a.toUInt32).toNat
  check "truncI32S_f32" a 0 (if (IEEE754.truncBounded IEEE754.binary32 a (-2147483648) 2147483647).map (fun x => x.toInt32.toUInt32) == i32TruncF32S a.toUInt32 then 1 else 0) 1
  check "satI32S_f32" a 0 (IEEE754.saturate IEEE754.binary32 a (-2147483648) 2147483647).toInt32.toUInt32.toNat (i32TruncSatF32S a.toUInt32).toNat
  check "truncI32U_f32" a 0 (if (IEEE754.truncBounded IEEE754.binary32 a (0) 4294967295).map (fun x => x.toNat.toUInt32) == i32TruncF32U a.toUInt32 then 1 else 0) 1
  check "satI32U_f32" a 0 (IEEE754.saturate IEEE754.binary32 a (0) 4294967295).toNat.toUInt32.toNat (i32TruncSatF32U a.toUInt32).toNat
  check "truncI64S_f32" a 0 (if (IEEE754.truncBounded IEEE754.binary32 a (-9223372036854775808) 9223372036854775807).map (fun x => x.toInt64.toUInt64) == i64TruncF32S a.toUInt32 then 1 else 0) 1
  check "satI64S_f32" a 0 (IEEE754.saturate IEEE754.binary32 a (-9223372036854775808) 9223372036854775807).toInt64.toUInt64.toNat (i64TruncSatF32S a.toUInt32).toNat
  check "truncI64U_f32" a 0 (if (IEEE754.truncBounded IEEE754.binary32 a (0) 18446744073709551615).map (fun x => x.toNat.toUInt64) == i64TruncF32U a.toUInt32 then 1 else 0) 1
  check "satI64U_f32" a 0 (IEEE754.saturate IEEE754.binary32 a (0) 18446744073709551615).toNat.toUInt64.toNat (i64TruncSatF32U a.toUInt32).toNat
  check "ofI32S_f32" a 0 (IEEE754.ofInt IEEE754.binary32 a.toUInt32.toInt32.toInt) (f32ConvertI32S a.toUInt32).toNat
  check "ofI32U_f32" a 0 (IEEE754.ofInt IEEE754.binary32 a) (f32ConvertI32U a.toUInt32).toNat
  check "ofI32S_f64" a 0 (IEEE754.ofInt IEEE754.binary64 a.toUInt32.toInt32.toInt) (f64ConvertI32S a.toUInt32).toNat
  check "ofI32U_f64" a 0 (IEEE754.ofInt IEEE754.binary64 a) (f64ConvertI32U a.toUInt32).toNat

def check64 (a b : Nat) : StateT (Nat × Nat) IO Unit := do
  for (name,pureOp,nativeOp) in binaryCases64 do
    check name a b (pureOp a b) (nativeOp a.toUInt64 b.toUInt64).toNat
  for (name,pureOp,nativeOp) in unaryCases64 do
    check name a 0 (pureOp a) (nativeOp a.toUInt64).toNat
  check "eq64" a b (if IEEE754.eq IEEE754.binary64 a b then 1 else 0) (if f64Eq a.toUInt64 b.toUInt64 then 1 else 0)
  check "lt64" a b (if IEEE754.lt IEEE754.binary64 a b then 1 else 0) (if f64Lt a.toUInt64 b.toUInt64 then 1 else 0)
  check "le64" a b (if IEEE754.le IEEE754.binary64 a b then 1 else 0) (if f64Le a.toUInt64 b.toUInt64 then 1 else 0)
  check "demote" a 0 (IEEE754.convert IEEE754.binary64 IEEE754.binary32 a) (f32DemoteF64 a.toUInt64).toNat
  check "ofUInt64_f64" a 0 (IEEE754.ofInt IEEE754.binary64 a) (f64ConvertI64U a.toUInt64).toNat
  check "ofInt64_f64" a 0 (IEEE754.ofInt IEEE754.binary64 a.toUInt64.toInt64.toInt) (f64ConvertI64S a.toUInt64).toNat
  check "satI64S_f64" a 0 (IEEE754.saturate IEEE754.binary64 a (-9223372036854775808) 9223372036854775807).toInt64.toUInt64.toNat (i64TruncSatF64S a.toUInt64).toNat
  check "truncI32S_f64" a 0 (if (IEEE754.truncBounded IEEE754.binary64 a (-2147483648) 2147483647).map (fun x => x.toInt32.toUInt32) == i32TruncF64S a.toUInt64 then 1 else 0) 1
  check "satI32S_f64" a 0 (IEEE754.saturate IEEE754.binary64 a (-2147483648) 2147483647).toInt32.toUInt32.toNat (i32TruncSatF64S a.toUInt64).toNat
  check "truncI32U_f64" a 0 (if (IEEE754.truncBounded IEEE754.binary64 a (0) 4294967295).map (fun x => x.toNat.toUInt32) == i32TruncF64U a.toUInt64 then 1 else 0) 1
  check "satI32U_f64" a 0 (IEEE754.saturate IEEE754.binary64 a (0) 4294967295).toNat.toUInt32.toNat (i32TruncSatF64U a.toUInt64).toNat
  check "truncI64S_f64" a 0 (if (IEEE754.truncBounded IEEE754.binary64 a (-9223372036854775808) 9223372036854775807).map (fun x => x.toInt64.toUInt64) == i64TruncF64S a.toUInt64 then 1 else 0) 1
  check "satI64S_f64" a 0 (IEEE754.saturate IEEE754.binary64 a (-9223372036854775808) 9223372036854775807).toInt64.toUInt64.toNat (i64TruncSatF64S a.toUInt64).toNat
  check "truncI64U_f64" a 0 (if (IEEE754.truncBounded IEEE754.binary64 a (0) 18446744073709551615).map (fun x => x.toNat.toUInt64) == i64TruncF64U a.toUInt64 then 1 else 0) 1
  check "satI64U_f64" a 0 (IEEE754.saturate IEEE754.binary64 a (0) 18446744073709551615).toNat.toUInt64.toNat (i64TruncSatF64U a.toUInt64).toNat
  check "ofI64S_f32" a 0 (IEEE754.ofInt IEEE754.binary32 a.toUInt64.toInt64.toInt) (f32ConvertI64S a.toUInt64).toNat
  check "ofI64U_f32" a 0 (IEEE754.ofInt IEEE754.binary32 a) (f32ConvertI64U a.toUInt64).toNat
  check "ofI64S_f64" a 0 (IEEE754.ofInt IEEE754.binary64 a.toUInt64.toInt64.toInt) (f64ConvertI64S a.toUInt64).toNat
  check "ofI64U_f64" a 0 (IEEE754.ofInt IEEE754.binary64 a) (f64ConvertI64U a.toUInt64).toNat

def runChecks : StateT (Nat × Nat) IO Unit := do
  let all32 := edges32 ++ edges32.map (· + 0x80000000)
  let all64 := edges64 ++ edges64.map (· + 0x8000000000000000)
  for a in all32 do
    for b in all32 do check32 a b
  for a in all64 do
    for b in all64 do check64 a b
  let mut seed : UInt64 := 0x123456789abcdef0
  for _ in [:10000] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let a := seed
    seed := seed * 6364136223846793005 + 1442695040888963407
    let b := seed
    check32 a.toUInt32.toNat b.toUInt32.toNat
    check64 a.toNat b.toNat

def main : IO Unit := do
  let (_, (count, failures)) ← runChecks.run (0,0)
  IO.println s!"{count} comparisons, {failures} mismatches"
  if failures != 0 then throw (IO.userError "IEEE differential mismatch")
