import Init.Data.Nat.Sqrt
import Init.Data.Nat.Log2

/-!
Pure binary floating-point arithmetic for the reference Wasm interpreter.
Finite values are an integer significand times a power of two. Arithmetic
rounds exact integer ratios to the destination format, using nearest with
ties to even. No operation evaluates a native `Float` or `Float32`.
-/

namespace Wasm.IEEE754

structure Format where
  fractionBits : Nat
  exponentBits : Nat
  bias : Int
  deriving Repr

def binary32 : Format := ⟨23, 8, 127⟩
def binary64 : Format := ⟨52, 11, 1023⟩

def Format.signBit (f : Format) : Nat := 2 ^ (f.fractionBits + f.exponentBits)
def Format.hiddenBit (f : Format) : Nat := 2 ^ f.fractionBits
def Format.maxExponentField (f : Format) : Nat := 2 ^ f.exponentBits - 1
def Format.minExponent (f : Format) : Int := 1 - f.bias
def Format.maxExponent (f : Format) : Int := (f.maxExponentField - 1 : Nat) - f.bias

def pack (f : Format) (negative : Bool) (exponent fraction : Nat) : Nat :=
  (if negative then f.signBit else 0) + exponent * f.hiddenBit + fraction

def zero (f : Format) (negative : Bool) : Nat := pack f negative 0 0
def infinity (f : Format) (negative : Bool) : Nat := pack f negative f.maxExponentField 0
def canonicalNaN (f : Format) : Nat := pack f false f.maxExponentField (2 ^ (f.fractionBits - 1))

inductive Number where
  | nan
  | infinity (negative : Bool)
  | finite (negative : Bool) (significand : Nat) (exponent : Int)
  deriving Repr

def decode (f : Format) (bits : Nat) : Number :=
  let negative := bits / f.signBit % 2 == 1
  let exponent := bits / f.hiddenBit % (2 ^ f.exponentBits)
  let fraction := bits % f.hiddenBit
  if exponent == f.maxExponentField then
    if fraction == 0 then .infinity negative else .nan
  else if exponent == 0 then
    .finite negative fraction (f.minExponent - f.fractionBits)
  else .finite negative (f.hiddenBit + fraction) ((exponent : Int) - f.bias - f.fractionBits)

/-- Scale a ratio by an exact power of two. -/
def scaleRatio (numerator denominator : Nat) (exponent : Int) : Nat × Nat :=
  if exponent ≥ 0 then (numerator * 2 ^ exponent.toNat, denominator)
  else (numerator, denominator * 2 ^ (-exponent).toNat)

/-- Nearest integer, resolving an exact midpoint toward the even integer. -/
def roundRatio (numerator denominator : Nat) : Nat :=
  let whole := numerator / denominator
  let remainder := numerator % denominator
  if 2 * remainder > denominator ||
      (2 * remainder == denominator && whole % 2 == 1) then whole + 1 else whole

/-- Pack an already rounded significand expressed in units of `2^exponent`. -/
def packRounded (f : Format) (negative : Bool) (significand : Nat) (exponent : Int) : Nat :=
  if significand < f.hiddenBit then pack f negative 0 significand
  else
    let carry := significand ≥ 2 * f.hiddenBit
    let significand := if carry then significand / 2 else significand
    let leadingExponent := exponent + f.fractionBits + (if carry then 1 else 0)
    if leadingExponent > f.maxExponent then infinity f negative
    else pack f negative (leadingExponent + f.bias).toNat (significand - f.hiddenBit)

/-- Round the exact magnitude `numerator / denominator * 2^exponent`.
All callers supply a nonzero denominator. -/
def encodeRatio (f : Format) (negative : Bool)
    (numerator denominator : Nat) (exponent : Int) : Nat :=
  if numerator == 0 then zero f negative
  else
    let estimate := (numerator.log2 : Int) - denominator.log2 + exponent
    let (n, d) := scaleRatio numerator denominator (exponent - estimate)
    let leadingExponent := if n < d then estimate - 1 else estimate
    if leadingExponent > f.maxExponent then infinity f negative
    else
      let quantum := max (leadingExponent - f.fractionBits) (f.minExponent - f.fractionBits)
      let (n, d) := scaleRatio numerator denominator (exponent - quantum)
      packRounded f negative (roundRatio n d) quantum

def signed (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(magnitude : Int) else magnitude

def ofInt (f : Format) (value : Int) : Nat :=
  encodeRatio f (value < 0) value.natAbs 1 0

def add (f : Format) (a b : Nat) : Nat :=
  match decode f a, decode f b with
  | .nan, _ | _, .nan => canonicalNaN f
  | .infinity sa, .infinity sb => if sa == sb then infinity f sa else canonicalNaN f
  | .infinity s, _ | _, .infinity s => infinity f s
  | .finite sa ma ea, .finite sb mb eb =>
    let e := min ea eb
    let value := signed sa (ma * 2 ^ (ea - e).toNat) + signed sb (mb * 2 ^ (eb - e).toNat)
    encodeRatio f (if value == 0 then sa && sb else value < 0) value.natAbs 1 e

def negate (f : Format) (a : Nat) : Nat := a ^^^ f.signBit
def sub (f : Format) (a b : Nat) : Nat := add f a (negate f b)

def mul (f : Format) (a b : Nat) : Nat :=
  match decode f a, decode f b with
  | .nan, _ | _, .nan => canonicalNaN f
  | .infinity sa, .infinity sb => infinity f (sa != sb)
  | .infinity sa, .finite sb m _ | .finite sa m _, .infinity sb =>
    if m == 0 then canonicalNaN f else infinity f (sa != sb)
  | .finite sa ma ea, .finite sb mb eb =>
    encodeRatio f (sa != sb) (ma * mb) 1 (ea + eb)

def div (f : Format) (a b : Nat) : Nat :=
  match decode f a, decode f b with
  | .nan, _ | _, .nan | .infinity _, .infinity _ => canonicalNaN f
  | .infinity sa, .finite sb _ _ => infinity f (sa != sb)
  | .finite sa _ _, .infinity sb => zero f (sa != sb)
  | .finite sa ma ea, .finite sb mb eb =>
    if mb == 0 then
      if ma == 0 then canonicalNaN f else infinity f (sa != sb)
    else encodeRatio f (sa != sb) ma mb (ea - eb)

/-- Square root rounds by comparing the exact square of the midpoint. -/
def sqrt (f : Format) (a : Nat) : Nat :=
  match decode f a with
  | .nan | .infinity true => canonicalNaN f
  | .infinity false => infinity f false
  | .finite s m e =>
    if m == 0 then zero f s
    else if s then canonicalNaN f
    else
      let leadingExponent := ((m.log2 : Int) + e) / 2
      let quantum := max (leadingExponent - f.fractionBits) (f.minExponent - f.fractionBits)
      let (n, d) := scaleRatio m 1 (e - 2 * quantum)
      let lower := (n / d).sqrt
      let midpointSquare := d * (2 * lower + 1) ^ 2
      let rounded := if 4 * n > midpointSquare ||
          (4 * n == midpointSquare && lower % 2 == 1) then lower + 1 else lower
      packRounded f false rounded quantum

inductive IntegralRounding where
  | towardZero | towardPositive | towardNegative | nearestEven
  deriving Repr

def roundIntegral (f : Format) (mode : IntegralRounding) (a : Nat) : Nat :=
  match decode f a with
  | .nan => canonicalNaN f
  | .infinity s => infinity f s
  | .finite s m e =>
    if e ≥ 0 then a
    else
      let denominator := 2 ^ (-e).toNat
      let magnitude := match mode with
        | .towardZero => m / denominator
        | .towardPositive => if s then m / denominator else (m + denominator - 1) / denominator
        | .towardNegative => if s then (m + denominator - 1) / denominator else m / denominator
        | .nearestEven => roundRatio m denominator
      encodeRatio f s magnitude 1 0

def isNaN (f : Format) (a : Nat) : Bool :=
  match decode f a with | .nan => true | _ => false

def isZero (f : Format) (a : Nat) : Bool := a % f.signBit == 0

def eq (f : Format) (a b : Nat) : Bool :=
  !isNaN f a && !isNaN f b && (a == b || (isZero f a && isZero f b))

def lt (f : Format) (a b : Nat) : Bool :=
  if isNaN f a || isNaN f b || (isZero f a && isZero f b) then false
  else
    let sa := a ≥ f.signBit
    let sb := b ≥ f.signBit
    if sa != sb then sa else if sa then a > b else a < b

def le (f : Format) (a b : Nat) : Bool := lt f a b || eq f a b

def minimum (f : Format) (a b : Nat) : Nat :=
  if isNaN f a || isNaN f b then canonicalNaN f
  else if isZero f a && isZero f b then a ||| b
  else if lt f a b then a else b

def maximum (f : Format) (a b : Nat) : Nat :=
  if isNaN f a || isNaN f b then canonicalNaN f
  else if isZero f a && isZero f b then a &&& b
  else if lt f a b then b else a

def convert (source target : Format) (a : Nat) : Nat :=
  match decode source a with
  | .nan => canonicalNaN target
  | .infinity s => infinity target s
  | .finite s m e => encodeRatio target s m 1 e

/-- Truncate a finite value to a mathematical integer. -/
def truncInt (f : Format) (a : Nat) : Option Int :=
  match decode f a with
  | .nan | .infinity _ => none
  | .finite s m e =>
    let magnitude := if e ≥ 0 then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
    some (signed s magnitude)

def truncBounded (f : Format) (a : Nat) (lower upper : Int) : Option Int := do
  let value ← truncInt f a
  if lower ≤ value && value ≤ upper then some value else none

def saturate (f : Format) (a : Nat) (lower upper : Int) : Int :=
  match decode f a with
  | .nan => 0
  | .infinity s => if s then lower else upper
  | .finite _ _ _ => max lower (min upper ((truncInt f a).getD 0))

end Wasm.IEEE754
