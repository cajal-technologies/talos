import Interpreter.Wasm.Float

/-!
# SIMD (v128) lane semantics

Pure lane-level semantics for the wasm `v128` proposal. A vector is a
`BitVec 128`; lanes are numbered from the least-significant end, matching
wasm's little-endian lane order (lane 0 occupies bits 0..laneBits-1).

The instruction surface is grouped by operand/result shape rather than
one constructor per mnemonic:

* `UnOp`    — `v128 → v128`
* `BinOp`   — `v128 → v128 → v128` (includes comparisons, which produce masks)
* `TestOp`  — `v128 → i32` (`any_true`, `all_true`, `bitmask`)
* `ShiftOp` — `v128 → i32 → v128`

plus splat/extract/replace/shuffle handled by the interpreter directly
with the lane helpers below. Float lanes reuse `Interpreter.Wasm.Float`,
so every NaN produced by a float lane operation is canonicalised exactly
as in the scalar semantics (`pmin`/`pmax` excepted: per spec they return
one operand unchanged).
-/

namespace Wasm.Simd

abbrev V128 := BitVec 128

/-- The six lane shapes of the SIMD proposal. -/
inductive Shape where
  | i8x16 | i16x8 | i32x4 | i64x2 | f32x4 | f64x2
deriving Repr, DecidableEq, Inhabited

def Shape.laneBits : Shape → Nat
  | .i8x16 => 8
  | .i16x8 => 16
  | .i32x4 => 32
  | .i64x2 => 64
  | .f32x4 => 32
  | .f64x2 => 64

def Shape.laneCount : Shape → Nat
  | .i8x16 => 16
  | .i16x8 => 8
  | .i32x4 => 4
  | .i64x2 => 2
  | .f32x4 => 4
  | .f64x2 => 2

/-! ## Lane access -/

/-- Extract lane `idx` of width `bits` as an unsigned `Nat`. -/
def getLane (bits idx : Nat) (v : V128) : Nat :=
  (v.toNat >>> (idx * bits)) % 2 ^ bits

/-- All `128 / bits` lanes, least-significant first. -/
def toLanes (bits : Nat) (v : V128) : List Nat :=
  (List.range (128 / bits)).map fun i => getLane bits i v

/-- Build a vector from unsigned lane values (least-significant first).
Each lane is reduced mod `2 ^ bits`. -/
def ofLanes (bits : Nat) (lanes : List Nat) : V128 :=
  BitVec.ofNat 128 <|
    (lanes.zipIdx.map fun (x, i) => (x % 2 ^ bits) <<< (i * bits)).foldl (· ||| ·) 0

/-- Replace lane `idx` of width `bits` with `x` (reduced mod `2 ^ bits`). -/
def setLane (bits idx : Nat) (v : V128) (x : Nat) : V128 :=
  ofLanes bits ((toLanes bits v).set idx x)

/-- Map an unsigned-lane function over every lane. -/
def mapLanes (bits : Nat) (f : Nat → Nat) (v : V128) : V128 :=
  ofLanes bits ((toLanes bits v).map f)

/-- Zip an unsigned-lane function over two vectors. -/
def zipLanes (bits : Nat) (f : Nat → Nat → Nat) (a b : V128) : V128 :=
  ofLanes bits (List.zipWith f (toLanes bits a) (toLanes bits b))

/-! ## Signedness and saturation helpers (lane values are unsigned `Nat`s) -/

/-- Signed reading of an unsigned `bits`-wide lane value. -/
def sx (bits n : Nat) : Int :=
  if n ≥ 2 ^ (bits - 1) then (n : Int) - (2 ^ bits : Nat) else (n : Int)

/-- Two's-complement encoding of `i` into `bits` bits. -/
def toU (bits : Nat) (i : Int) : Nat :=
  (i % (2 ^ bits : Nat)).toNat

/-- Clamp a signed value into the signed `bits`-bit range, then encode. -/
def satS (bits : Nat) (i : Int) : Nat :=
  let lo : Int := -(2 ^ (bits - 1) : Nat)
  let hi : Int := (2 ^ (bits - 1) : Nat) - 1
  toU bits (max lo (min hi i))

/-- Clamp a signed value into the unsigned `bits`-bit range. -/
def satU (bits : Nat) (i : Int) : Nat :=
  let hi : Int := (2 ^ bits : Nat) - 1
  (max 0 (min hi i)).toNat

/-- All-ones / all-zeros lane mask for comparison results. -/
def boolLane (bits : Nat) (b : Bool) : Nat :=
  if b then 2 ^ bits - 1 else 0

/-! ## Integer comparison kinds -/

inductive ICmp where
  | eq | ne | ltS | ltU | gtS | gtU | leS | leU | geS | geU
deriving Repr, DecidableEq, Inhabited

def ICmp.eval (bits : Nat) (op : ICmp) (a b : Nat) : Bool :=
  match op with
  | .eq  => a = b
  | .ne  => a ≠ b
  | .ltS => sx bits a < sx bits b
  | .ltU => a < b
  | .gtS => sx bits a > sx bits b
  | .gtU => a > b
  | .leS => sx bits a ≤ sx bits b
  | .leU => a ≤ b
  | .geS => sx bits a ≥ sx bits b
  | .geU => a ≥ b

inductive FCmp where
  | eq | ne | lt | gt | le | ge
deriving Repr, DecidableEq, Inhabited

def FCmp.eval32 (op : FCmp) (a b : UInt32) : Bool :=
  match op with
  | .eq => f32Eq a b | .ne => f32Ne a b
  | .lt => f32Lt a b | .gt => f32Gt a b
  | .le => f32Le a b | .ge => f32Ge a b

def FCmp.eval64 (op : FCmp) (a b : UInt64) : Bool :=
  match op with
  | .eq => f64Eq a b | .ne => f64Ne a b
  | .lt => f64Lt a b | .gt => f64Gt a b
  | .le => f64Le a b | .ge => f64Ge a b

/-! ## Float lane wrappers (bit-pattern in, bit-pattern out, as `Nat`) -/

private def f32LaneUn (f : UInt32 → UInt32) (n : Nat) : Nat :=
  (f (UInt32.ofNat n)).toNat
private def f64LaneUn (f : UInt64 → UInt64) (n : Nat) : Nat :=
  (f (UInt64.ofNat n)).toNat
private def f32LaneBin (f : UInt32 → UInt32 → UInt32) (a b : Nat) : Nat :=
  (f (UInt32.ofNat a) (UInt32.ofNat b)).toNat
private def f64LaneBin (f : UInt64 → UInt64 → UInt64) (a b : Nat) : Nat :=
  (f (UInt64.ofNat a) (UInt64.ofNat b)).toNat

/-- `pmin`: `b < a ? b : a`, NaN-insensitive, operand returned unchanged. -/
def f32Pmin (a b : UInt32) : UInt32 := if f32Lt b a then b else a
def f32Pmax (a b : UInt32) : UInt32 := if f32Lt a b then b else a
def f64Pmin (a b : UInt64) : UInt64 := if f64Lt b a then b else a
def f64Pmax (a b : UInt64) : UInt64 := if f64Lt a b then b else a

/-! ## Unary operations -/

inductive UnOp where
  | not
  | intAbs (sh : Shape) | intNeg (sh : Shape)
  | popcnt                                   -- i8x16 only
  | fAbs (sh : Shape) | fNeg (sh : Shape) | fSqrt (sh : Shape)
  | fCeil (sh : Shape) | fFloor (sh : Shape) | fTrunc (sh : Shape)
  | fNearest (sh : Shape)
  /-- `dst.extend_{low,high}_src_{s,u}`: `dst` is the destination shape
  (`i16x8`/`i32x4`/`i64x2`); source lanes are half the width. -/
  | extend (dst : Shape) (high : Bool) (signed : Bool)
  /-- `dst.extadd_pairwise_src_{s,u}` (`dst` ∈ {i16x8, i32x4}). -/
  | extaddPairwise (dst : Shape) (signed : Bool)
  | i32x4TruncSatF32x4 (signed : Bool)
  | i32x4TruncSatF64x2Zero (signed : Bool)
  | f32x4ConvertI32x4 (signed : Bool)
  | f64x2ConvertLowI32x4 (signed : Bool)
  | f32x4DemoteF64x2Zero
  | f64x2PromoteLowF32x4
deriving Repr, DecidableEq, Inhabited

private def popcntNat : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcntNat ((n + 1) / 2)

def UnOp.eval (op : UnOp) (v : V128) : V128 :=
  match op with
  | .not => ~~~v
  | .intAbs sh =>
    let b := sh.laneBits
    mapLanes b (fun n => toU b (sx b n).natAbs) v
  | .intNeg sh =>
    let b := sh.laneBits
    mapLanes b (fun n => toU b (-(sx b n))) v
  | .popcnt => mapLanes 8 popcntNat v
  | .fAbs sh => match sh with
    | .f64x2 => mapLanes 64 (f64LaneUn f64Abs) v
    | _      => mapLanes 32 (f32LaneUn f32Abs) v
  | .fNeg sh => match sh with
    | .f64x2 => mapLanes 64 (f64LaneUn f64Neg) v
    | _      => mapLanes 32 (f32LaneUn f32Neg) v
  | .fSqrt sh => match sh with
    | .f64x2 => mapLanes 64 (f64LaneUn f64Sqrt) v
    | _      => mapLanes 32 (f32LaneUn f32Sqrt) v
  | .fCeil sh => match sh with
    | .f64x2 => mapLanes 64 (f64LaneUn f64Ceil) v
    | _      => mapLanes 32 (f32LaneUn f32Ceil) v
  | .fFloor sh => match sh with
    | .f64x2 => mapLanes 64 (f64LaneUn f64Floor) v
    | _      => mapLanes 32 (f32LaneUn f32Floor) v
  | .fTrunc sh => match sh with
    | .f64x2 => mapLanes 64 (f64LaneUn f64Trunc) v
    | _      => mapLanes 32 (f32LaneUn f32Trunc) v
  | .fNearest sh => match sh with
    | .f64x2 => mapLanes 64 (f64LaneUn f64Nearest) v
    | _      => mapLanes 32 (f32LaneUn f32Nearest) v
  | .extend dst high signed =>
    let db := dst.laneBits
    let sb := db / 2
    let cnt := 128 / db
    let src := toLanes sb v
    let lanes := (List.range cnt).map fun i =>
      let n := src.getD (i + if high then cnt else 0) 0
      if signed then toU db (sx sb n) else n
    ofLanes db lanes
  | .extaddPairwise dst signed =>
    let db := dst.laneBits
    let sb := db / 2
    let rd : Nat → Int := fun n => if signed then sx sb n else (n : Int)
    let src := toLanes sb v
    let lanes := (List.range (128 / db)).map fun i =>
      toU db (rd (src.getD (2 * i) 0) + rd (src.getD (2 * i + 1) 0))
    ofLanes db lanes
  | .i32x4TruncSatF32x4 signed =>
    mapLanes 32 (fun n =>
      let b := UInt32.ofNat n
      (if signed then i32TruncSatF32S b else i32TruncSatF32U b).toNat) v
  | .i32x4TruncSatF64x2Zero signed =>
    let src := toLanes 64 v
    let conv : Nat → Nat := fun n =>
      let b := UInt64.ofNat n
      (if signed then i32TruncSatF64S b else i32TruncSatF64U b).toNat
    ofLanes 32 [conv (src.getD 0 0), conv (src.getD 1 0), 0, 0]
  | .f32x4ConvertI32x4 signed =>
    mapLanes 32 (fun n =>
      let b := UInt32.ofNat n
      (if signed then f32ConvertI32S b else f32ConvertI32U b).toNat) v
  | .f64x2ConvertLowI32x4 signed =>
    let src := toLanes 32 v
    let conv : Nat → Nat := fun n =>
      let b := UInt32.ofNat n
      (if signed then f64ConvertI32S b else f64ConvertI32U b).toNat
    ofLanes 64 [conv (src.getD 0 0), conv (src.getD 1 0)]
  | .f32x4DemoteF64x2Zero =>
    let src := toLanes 64 v
    let conv : Nat → Nat := fun n => (f32DemoteF64 (UInt64.ofNat n)).toNat
    ofLanes 32 [conv (src.getD 0 0), conv (src.getD 1 0), 0, 0]
  | .f64x2PromoteLowF32x4 =>
    let src := toLanes 32 v
    let conv : Nat → Nat := fun n => (f64PromoteF32 (UInt32.ofNat n)).toNat
    ofLanes 64 [conv (src.getD 0 0), conv (src.getD 1 0)]

/-! ## Binary operations -/

inductive BinOp where
  | and | andnot | or | xor
  | swizzle                                  -- i8x16
  | add (sh : Shape) | sub (sh : Shape) | mul (sh : Shape)
  | addSat (sh : Shape) (signed : Bool) | subSat (sh : Shape) (signed : Bool)
  | minI (sh : Shape) (signed : Bool) | maxI (sh : Shape) (signed : Bool)
  | avgrU (sh : Shape)
  | q15mulrSatS                              -- i16x8
  /-- `dst.extmul_{low,high}_src_{s,u}`. -/
  | extmul (dst : Shape) (high : Bool) (signed : Bool)
  | dot                                      -- i32x4.dot_i16x8_s
  | dotI8                                    -- i16x8.relaxed_dot_i8x16_i7x16_s
  /-- `dst.narrow_src_{s,u}`: `dst` ∈ {i8x16, i16x8}, source lanes are
  double width; result = saturated `a`-lanes then saturated `b`-lanes. -/
  | narrow (dst : Shape) (signed : Bool)
  | cmp (sh : Shape) (op : ICmp)
  | fcmp (sh : Shape) (op : FCmp)
  | fAdd (sh : Shape) | fSub (sh : Shape) | fMul (sh : Shape) | fDiv (sh : Shape)
  | fMin (sh : Shape) | fMax (sh : Shape) | fPmin (sh : Shape) | fPmax (sh : Shape)
deriving Repr, DecidableEq, Inhabited

def BinOp.eval (op : BinOp) (a b : V128) : V128 :=
  match op with
  | .and    => a &&& b
  | .andnot => a &&& ~~~b
  | .or     => a ||| b
  | .xor    => a ^^^ b
  | .swizzle =>
    let src := toLanes 8 a
    let idx := toLanes 8 b
    ofLanes 8 (idx.map fun i => if i < 16 then src.getD i 0 else 0)
  | .add sh => let n := sh.laneBits; zipLanes n (fun x y => (x + y) % 2 ^ n) a b
  | .sub sh => let n := sh.laneBits; zipLanes n (fun x y => (2 ^ n + x - y) % 2 ^ n) a b
  | .mul sh => let n := sh.laneBits; zipLanes n (fun x y => (x * y) % 2 ^ n) a b
  | .addSat sh signed =>
    let n := sh.laneBits
    if signed then zipLanes n (fun x y => satS n (sx n x + sx n y)) a b
    else zipLanes n (fun x y => satU n ((x : Int) + (y : Int))) a b
  | .subSat sh signed =>
    let n := sh.laneBits
    if signed then zipLanes n (fun x y => satS n (sx n x - sx n y)) a b
    else zipLanes n (fun x y => satU n ((x : Int) - (y : Int))) a b
  | .minI sh signed =>
    let n := sh.laneBits
    if signed then zipLanes n (fun x y => if sx n x ≤ sx n y then x else y) a b
    else zipLanes n (fun x y => min x y) a b
  | .maxI sh signed =>
    let n := sh.laneBits
    if signed then zipLanes n (fun x y => if sx n x ≥ sx n y then x else y) a b
    else zipLanes n (fun x y => max x y) a b
  | .avgrU sh =>
    let n := sh.laneBits
    zipLanes n (fun x y => (x + y + 1) / 2) a b
  | .q15mulrSatS =>
    zipLanes 16 (fun x y => satS 16 ((sx 16 x * sx 16 y + 2 ^ 14) >>> 15)) a b
  | .extmul dst high signed =>
    let db := dst.laneBits
    let sb := db / 2
    let cnt := 128 / db
    let off := if high then cnt else 0
    let rd : Nat → Int := fun n => if signed then sx sb n else (n : Int)
    let la := toLanes sb a
    let lb := toLanes sb b
    ofLanes db <| (List.range cnt).map fun i =>
      toU db (rd (la.getD (i + off) 0) * rd (lb.getD (i + off) 0))
  | .dot =>
    let la := toLanes 16 a
    let lb := toLanes 16 b
    ofLanes 32 <| (List.range 4).map fun i =>
      toU 32 (sx 16 (la.getD (2 * i) 0) * sx 16 (lb.getD (2 * i) 0)
            + sx 16 (la.getD (2 * i + 1) 0) * sx 16 (lb.getD (2 * i + 1) 0))
  | .dotI8 =>
    let la := toLanes 8 a
    let lb := toLanes 8 b
    ofLanes 16 <| (List.range 8).map fun i =>
      toU 16 (sx 8 (la.getD (2 * i) 0) * sx 8 (lb.getD (2 * i) 0)
            + sx 8 (la.getD (2 * i + 1) 0) * sx 8 (lb.getD (2 * i + 1) 0))
  | .narrow dst signed =>
    let db := dst.laneBits
    let sb := db * 2
    let conv : Nat → Nat := fun n =>
      if signed then satS db (sx sb n) else satU db (sx sb n)
    ofLanes db ((toLanes sb a).map conv ++ (toLanes sb b).map conv)
  | .cmp sh op =>
    let n := sh.laneBits
    zipLanes n (fun x y => boolLane n (op.eval n x y)) a b
  | .fcmp sh op => match sh with
    | .f64x2 => zipLanes 64 (fun x y =>
        boolLane 64 (op.eval64 (UInt64.ofNat x) (UInt64.ofNat y))) a b
    | _ => zipLanes 32 (fun x y =>
        boolLane 32 (op.eval32 (UInt32.ofNat x) (UInt32.ofNat y))) a b
  | .fAdd sh => match sh with
    | .f64x2 => zipLanes 64 (f64LaneBin f64Add) a b
    | _      => zipLanes 32 (f32LaneBin f32Add) a b
  | .fSub sh => match sh with
    | .f64x2 => zipLanes 64 (f64LaneBin f64Sub) a b
    | _      => zipLanes 32 (f32LaneBin f32Sub) a b
  | .fMul sh => match sh with
    | .f64x2 => zipLanes 64 (f64LaneBin f64Mul) a b
    | _      => zipLanes 32 (f32LaneBin f32Mul) a b
  | .fDiv sh => match sh with
    | .f64x2 => zipLanes 64 (f64LaneBin f64Div) a b
    | _      => zipLanes 32 (f32LaneBin f32Div) a b
  | .fMin sh => match sh with
    | .f64x2 => zipLanes 64 (f64LaneBin f64Min) a b
    | _      => zipLanes 32 (f32LaneBin f32Min) a b
  | .fMax sh => match sh with
    | .f64x2 => zipLanes 64 (f64LaneBin f64Max) a b
    | _      => zipLanes 32 (f32LaneBin f32Max) a b
  | .fPmin sh => match sh with
    | .f64x2 => zipLanes 64 (f64LaneBin f64Pmin) a b
    | _      => zipLanes 32 (f32LaneBin f32Pmin) a b
  | .fPmax sh => match sh with
    | .f64x2 => zipLanes 64 (f64LaneBin f64Pmax) a b
    | _      => zipLanes 32 (f32LaneBin f32Pmax) a b

/-! ## Test operations (`v128 → i32`) -/

inductive TestOp where
  | anyTrue
  | allTrue (sh : Shape)
  | bitmask (sh : Shape)
deriving Repr, DecidableEq, Inhabited

def TestOp.eval (op : TestOp) (v : V128) : UInt32 :=
  match op with
  | .anyTrue => if v.toNat ≠ 0 then 1 else 0
  | .allTrue sh =>
    if (toLanes sh.laneBits v).all (· ≠ 0) then 1 else 0
  | .bitmask sh =>
    let n := sh.laneBits
    UInt32.ofNat <|
      ((toLanes n v).zipIdx.map fun (x, i) =>
        (if x ≥ 2 ^ (n - 1) then 1 else 0) <<< i).foldl (· ||| ·) 0

/-! ## Shifts (`v128 → i32 → v128`; count taken mod lane width) -/

inductive ShiftOp where
  | shl (sh : Shape)
  | shrS (sh : Shape)
  | shrU (sh : Shape)
deriving Repr, DecidableEq, Inhabited

def ShiftOp.eval (op : ShiftOp) (v : V128) (count : UInt32) : V128 :=
  match op with
  | .shl sh =>
    let n := sh.laneBits
    let k := count.toNat % n
    mapLanes n (fun x => (x <<< k) % 2 ^ n) v
  | .shrU sh =>
    let n := sh.laneBits
    let k := count.toNat % n
    mapLanes n (fun x => x >>> k) v
  | .shrS sh =>
    let n := sh.laneBits
    let k := count.toNat % n
    mapLanes n (fun x => toU n (Int.shiftRight (sx n x) k)) v

/-! ## Relaxed SIMD (deterministic choices)

The relaxed-SIMD ops admit several implementation behaviours; the
testsuite accepts any of the listed alternatives. We always pick the
deterministic, unfused choice: `relaxed_madd` is multiply-then-add with
intermediate rounding, `laneselect` is bitwise `bitselect`, the relaxed
truncations/min/max coincide with the non-relaxed ops. -/

/-- `f32x4/f64x2.relaxed_madd` (`neg := false`) and `relaxed_nmadd`
(`neg := true`): per-lane `±(a*b) + c`, unfused. -/
def fma (sh : Shape) (neg : Bool) (a b c : V128) : V128 :=
  match sh with
  | .f64x2 =>
    ofLanes 64 <| List.zipWith (fun ab cc =>
        f64LaneBin f64Add (if neg then f64LaneUn f64Neg ab else ab) cc)
      (List.zipWith (f64LaneBin f64Mul) (toLanes 64 a) (toLanes 64 b))
      (toLanes 64 c)
  | _ =>
    ofLanes 32 <| List.zipWith (fun ab cc =>
        f32LaneBin f32Add (if neg then f32LaneUn f32Neg ab else ab) cc)
      (List.zipWith (f32LaneBin f32Mul) (toLanes 32 a) (toLanes 32 b))
      (toLanes 32 c)

/-- `i16x8.relaxed_dot_i8x16_i7x16_s`: per-16-bit-lane signed dot of the
two corresponding i8 pairs (both operands read signed — the
deterministic choice). -/
def dot8 (a b : V128) : V128 :=
  let la := toLanes 8 a
  let lb := toLanes 8 b
  ofLanes 16 <| (List.range 8).map fun i =>
    toU 16 (sx 8 (la.getD (2 * i) 0) * sx 8 (lb.getD (2 * i) 0)
          + sx 8 (la.getD (2 * i + 1) 0) * sx 8 (lb.getD (2 * i + 1) 0))

/-- `i32x4.relaxed_dot_i8x16_i7x16_add_s`: `dot8` pairs widened and
pairwise-summed into i32 lanes, plus the accumulator `c`. -/
def dotAdd (a b c : V128) : V128 :=
  let d := toLanes 16 (dot8 a b)
  let lc := toLanes 32 c
  ofLanes 32 <| (List.range 4).map fun i =>
    toU 32 (sx 16 (d.getD (2 * i) 0) + sx 16 (d.getD (2 * i + 1) 0)
          + sx 32 (lc.getD i 0))

/-! ## Splat / shuffle helpers -/

/-- Broadcast the low `sh.laneBits` bits of `x` to every lane. -/
def splat (sh : Shape) (x : Nat) : V128 :=
  ofLanes sh.laneBits (List.replicate sh.laneCount x)

/-- `i8x16.shuffle`: byte `i` of the result is `a ++ b` indexed by `idx[i]`. -/
def shuffle (idx : List Nat) (a b : V128) : V128 :=
  let lanes := toLanes 8 a ++ toLanes 8 b
  ofLanes 8 (idx.map fun i => lanes.getD i 0)

end Wasm.Simd
