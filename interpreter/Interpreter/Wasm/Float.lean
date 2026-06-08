/-! ## Floating-point values and operations

Wasm `f32`/`f64` values are modelled by their **IEEE-754 bit patterns**
(`UInt32` / `UInt64`), not by Lean's opaque `Float`. The bit pattern is the
faithful representation: it preserves NaN payloads and the sign of zero,
leaves `Value`'s derived `DecidableEq`/`BEq` intact, and matches the
bit-level style the integer instructions already use.

Numeric operations decode the bits to Lean's native `Float32` / `Float`
(so `f32` arithmetic rounds in single precision), compute, and re-encode.
Every numeric result funnels through one seam — `f32Canon` / `f64Canon` —
which maps a NaN result to the *canonical* quiet NaN. Producing the
canonical NaN is always a spec-conforming choice, and concentrating it in a
single function is where finer NaN-payload propagation would later attach.

`abs`, `neg` and `copysign` are bit operations exactly as the spec defines
them: they act on the sign bit alone and never canonicalize. -/

namespace Wasm

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

end Wasm
