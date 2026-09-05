import Interpreter.Wasm.IEEE754

/-!
Wasm floating-point values retain their exact IEEE-754 encodings. Numeric
operations use the pure integer-ratio model; sign operations preserve NaN
payloads, while numeric NaN results use the existing canonical-NaN policy.
-/
namespace Wasm

def f32CanonicalNaN : UInt32 := 0x7FC00000
def f64CanonicalNaN : UInt64 := 0x7FF8000000000000

def f32IsNaN (a : UInt32) : Bool := IEEE754.isNaN IEEE754.binary32 a.toNat
def f32Canon (a : UInt32) : UInt32 :=
  if f32IsNaN a then f32CanonicalNaN else a
def f32Abs (a : UInt32) : UInt32 := a &&& 0x7fffffff
def f32Neg (a : UInt32) : UInt32 := a ^^^ 0x80000000
def f32Copysign (a b : UInt32) : UInt32 := (a &&& 0x7fffffff) ||| (b &&& 0x80000000)
def f32Add (a b : UInt32) : UInt32 := (IEEE754.add IEEE754.binary32 a.toNat b.toNat).toUInt32
def f32Sub (a b : UInt32) : UInt32 := (IEEE754.sub IEEE754.binary32 a.toNat b.toNat).toUInt32
def f32Mul (a b : UInt32) : UInt32 := (IEEE754.mul IEEE754.binary32 a.toNat b.toNat).toUInt32
def f32Div (a b : UInt32) : UInt32 := (IEEE754.div IEEE754.binary32 a.toNat b.toNat).toUInt32
def f32Min (a b : UInt32) : UInt32 := (IEEE754.minimum IEEE754.binary32 a.toNat b.toNat).toUInt32
def f32Max (a b : UInt32) : UInt32 := (IEEE754.maximum IEEE754.binary32 a.toNat b.toNat).toUInt32
def f32Sqrt (a : UInt32) : UInt32 := (IEEE754.sqrt IEEE754.binary32 a.toNat).toUInt32
def f32Ceil (a : UInt32) : UInt32 :=
  (IEEE754.roundIntegral IEEE754.binary32 .towardPositive a.toNat).toUInt32
def f32Floor (a : UInt32) : UInt32 :=
  (IEEE754.roundIntegral IEEE754.binary32 .towardNegative a.toNat).toUInt32
def f32Trunc (a : UInt32) : UInt32 :=
  (IEEE754.roundIntegral IEEE754.binary32 .towardZero a.toNat).toUInt32
def f32Nearest (a : UInt32) : UInt32 :=
  (IEEE754.roundIntegral IEEE754.binary32 .nearestEven a.toNat).toUInt32
def f32Eq (a b : UInt32) : Bool := IEEE754.eq IEEE754.binary32 a.toNat b.toNat
def f32Lt (a b : UInt32) : Bool := IEEE754.lt IEEE754.binary32 a.toNat b.toNat
def f32Gt (a b : UInt32) : Bool := IEEE754.lt IEEE754.binary32 b.toNat a.toNat
def f32Le (a b : UInt32) : Bool := IEEE754.le IEEE754.binary32 a.toNat b.toNat
def f32Ge (a b : UInt32) : Bool := IEEE754.le IEEE754.binary32 b.toNat a.toNat
def f32Ne (a b : UInt32) : Bool := !(f32Eq a b)

def f32ConvertI32S (a : UInt32) : UInt32 :=
  (IEEE754.ofInt IEEE754.binary32 a.toInt32.toInt).toUInt32
def f32ConvertI32U (a : UInt32) : UInt32 :=
  (IEEE754.ofInt IEEE754.binary32 (a.toNat : Int)).toUInt32
def f32ConvertI64S (a : UInt64) : UInt32 :=
  (IEEE754.ofInt IEEE754.binary32 a.toInt64.toInt).toUInt32
def f32ConvertI64U (a : UInt64) : UInt32 :=
  (IEEE754.ofInt IEEE754.binary32 (a.toNat : Int)).toUInt32

def i32TruncF32S (a : UInt32) : Option UInt32 :=
  (IEEE754.truncBounded IEEE754.binary32 a.toNat (-2147483648) 2147483647).map
    (fun x => x.toInt32.toUInt32)
def i32TruncSatF32S (a : UInt32) : UInt32 :=
  let x := IEEE754.saturate IEEE754.binary32 a.toNat (-2147483648) 2147483647
  x.toInt32.toUInt32
def i32TruncF32U (a : UInt32) : Option UInt32 :=
  (IEEE754.truncBounded IEEE754.binary32 a.toNat (0) 4294967295).map
    (fun x => x.toNat.toUInt32)
def i32TruncSatF32U (a : UInt32) : UInt32 :=
  let x := IEEE754.saturate IEEE754.binary32 a.toNat (0) 4294967295
  x.toNat.toUInt32
def i64TruncF32S (a : UInt32) : Option UInt64 :=
  (IEEE754.truncBounded IEEE754.binary32 a.toNat (-9223372036854775808) 9223372036854775807).map
    (fun x => x.toInt64.toUInt64)
def i64TruncSatF32S (a : UInt32) : UInt64 :=
  let x := IEEE754.saturate IEEE754.binary32 a.toNat (-9223372036854775808) 9223372036854775807
  x.toInt64.toUInt64
def i64TruncF32U (a : UInt32) : Option UInt64 :=
  (IEEE754.truncBounded IEEE754.binary32 a.toNat (0) 18446744073709551615).map
    (fun x => x.toNat.toUInt64)
def i64TruncSatF32U (a : UInt32) : UInt64 :=
  let x := IEEE754.saturate IEEE754.binary32 a.toNat (0) 18446744073709551615
  x.toNat.toUInt64

def f64IsNaN (a : UInt64) : Bool := IEEE754.isNaN IEEE754.binary64 a.toNat
def f64Canon (a : UInt64) : UInt64 :=
  if f64IsNaN a then f64CanonicalNaN else a
def f64Abs (a : UInt64) : UInt64 := a &&& 0x7fffffffffffffff
def f64Neg (a : UInt64) : UInt64 := a ^^^ 0x8000000000000000
def f64Copysign (a b : UInt64) : UInt64 := (a &&& 0x7fffffffffffffff) ||| (b &&& 0x8000000000000000)
def f64Add (a b : UInt64) : UInt64 := (IEEE754.add IEEE754.binary64 a.toNat b.toNat).toUInt64
def f64Sub (a b : UInt64) : UInt64 := (IEEE754.sub IEEE754.binary64 a.toNat b.toNat).toUInt64
def f64Mul (a b : UInt64) : UInt64 := (IEEE754.mul IEEE754.binary64 a.toNat b.toNat).toUInt64
def f64Div (a b : UInt64) : UInt64 := (IEEE754.div IEEE754.binary64 a.toNat b.toNat).toUInt64
def f64Min (a b : UInt64) : UInt64 := (IEEE754.minimum IEEE754.binary64 a.toNat b.toNat).toUInt64
def f64Max (a b : UInt64) : UInt64 := (IEEE754.maximum IEEE754.binary64 a.toNat b.toNat).toUInt64
def f64Sqrt (a : UInt64) : UInt64 := (IEEE754.sqrt IEEE754.binary64 a.toNat).toUInt64
def f64Ceil (a : UInt64) : UInt64 :=
  (IEEE754.roundIntegral IEEE754.binary64 .towardPositive a.toNat).toUInt64
def f64Floor (a : UInt64) : UInt64 :=
  (IEEE754.roundIntegral IEEE754.binary64 .towardNegative a.toNat).toUInt64
def f64Trunc (a : UInt64) : UInt64 :=
  (IEEE754.roundIntegral IEEE754.binary64 .towardZero a.toNat).toUInt64
def f64Nearest (a : UInt64) : UInt64 :=
  (IEEE754.roundIntegral IEEE754.binary64 .nearestEven a.toNat).toUInt64
def f64Eq (a b : UInt64) : Bool := IEEE754.eq IEEE754.binary64 a.toNat b.toNat
def f64Lt (a b : UInt64) : Bool := IEEE754.lt IEEE754.binary64 a.toNat b.toNat
def f64Gt (a b : UInt64) : Bool := IEEE754.lt IEEE754.binary64 b.toNat a.toNat
def f64Le (a b : UInt64) : Bool := IEEE754.le IEEE754.binary64 a.toNat b.toNat
def f64Ge (a b : UInt64) : Bool := IEEE754.le IEEE754.binary64 b.toNat a.toNat
def f64Ne (a b : UInt64) : Bool := !(f64Eq a b)

def f64ConvertI32S (a : UInt32) : UInt64 :=
  (IEEE754.ofInt IEEE754.binary64 a.toInt32.toInt).toUInt64
def f64ConvertI32U (a : UInt32) : UInt64 :=
  (IEEE754.ofInt IEEE754.binary64 (a.toNat : Int)).toUInt64
def f64ConvertI64S (a : UInt64) : UInt64 :=
  (IEEE754.ofInt IEEE754.binary64 a.toInt64.toInt).toUInt64
def f64ConvertI64U (a : UInt64) : UInt64 :=
  (IEEE754.ofInt IEEE754.binary64 (a.toNat : Int)).toUInt64

def i32TruncF64S (a : UInt64) : Option UInt32 :=
  (IEEE754.truncBounded IEEE754.binary64 a.toNat (-2147483648) 2147483647).map
    (fun x => x.toInt32.toUInt32)
def i32TruncSatF64S (a : UInt64) : UInt32 :=
  let x := IEEE754.saturate IEEE754.binary64 a.toNat (-2147483648) 2147483647
  x.toInt32.toUInt32
def i32TruncF64U (a : UInt64) : Option UInt32 :=
  (IEEE754.truncBounded IEEE754.binary64 a.toNat (0) 4294967295).map
    (fun x => x.toNat.toUInt32)
def i32TruncSatF64U (a : UInt64) : UInt32 :=
  let x := IEEE754.saturate IEEE754.binary64 a.toNat (0) 4294967295
  x.toNat.toUInt32
def i64TruncF64S (a : UInt64) : Option UInt64 :=
  (IEEE754.truncBounded IEEE754.binary64 a.toNat (-9223372036854775808) 9223372036854775807).map
    (fun x => x.toInt64.toUInt64)
def i64TruncSatF64S (a : UInt64) : UInt64 :=
  let x := IEEE754.saturate IEEE754.binary64 a.toNat (-9223372036854775808) 9223372036854775807
  x.toInt64.toUInt64
def i64TruncF64U (a : UInt64) : Option UInt64 :=
  (IEEE754.truncBounded IEEE754.binary64 a.toNat (0) 18446744073709551615).map
    (fun x => x.toNat.toUInt64)
def i64TruncSatF64U (a : UInt64) : UInt64 :=
  let x := IEEE754.saturate IEEE754.binary64 a.toNat (0) 18446744073709551615
  x.toNat.toUInt64

def f64PromoteF32 (a : UInt32) : UInt64 :=
  (IEEE754.convert IEEE754.binary32 IEEE754.binary64 a.toNat).toUInt64
def f32DemoteF64 (a : UInt64) : UInt32 :=
  (IEEE754.convert IEEE754.binary64 IEEE754.binary32 a.toNat).toUInt32

end Wasm
