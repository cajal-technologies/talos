import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Float
import Interpreter.Wasm.Locals
import Interpreter.Wasm.Continuation
import Interpreter.Wasm.Host

namespace Wasm

/-! ## Numeric helpers (carried over from `Interpreter.Core.Interp`). -/

/-- Number of leading zero bits in a 32-bit word; 32 if zero. -/
def clz32 : Nat → UInt32 → Nat
  | 0, _ => 32
  | k + 1, a => if a &&& 0x80000000 ≠ 0 then 32 - (k + 1) else clz32 k (a <<< 1)

/-- Number of trailing zero bits in a 32-bit word; 32 if zero. -/
def ctz32 : Nat → UInt32 → Nat
  | 0, _ => 32
  | k + 1, a => if a &&& 1 ≠ 0 then 32 - (k + 1) else ctz32 k (a >>> 1)

/-- Number of one bits in a 32-bit word. -/
def popcnt32 : Nat → UInt32 → Nat → Nat
  | 0, _, acc => acc
  | k + 1, a, acc => popcnt32 k (a >>> 1) (acc + (a &&& 1).toNat)

/-- Number of leading zero bits in a 64-bit word; 64 if zero. -/
def clz64 : Nat → UInt64 → Nat
  | 0, _ => 64
  | k + 1, a => if a &&& 0x8000000000000000 ≠ 0 then 64 - (k + 1) else clz64 k (a <<< 1)

/-- Number of trailing zero bits in a 64-bit word; 64 if zero. -/
def ctz64 : Nat → UInt64 → Nat
  | 0, _ => 64
  | k + 1, a => if a &&& 1 ≠ 0 then 64 - (k + 1) else ctz64 k (a >>> 1)

/-- Number of one bits in a 64-bit word. -/
def popcnt64 : Nat → UInt64 → Nat → Nat
  | 0, _, acc => acc
  | k + 1, a, acc => popcnt64 k (a >>> 1) (acc + (a &&& 1).toNat)

/-- Sign-extend the low `bits` bits of `n` to a signed `Int`. -/
def signExtend (n : Nat) (bits : Nat) : Int :=
  let half := 2 ^ (bits - 1)
  let bound := 2 ^ bits
  if n ≥ half then (n : Int) - (bound : Int) else (n : Int)

/-! ## Big-step fuel-bounded interpreter.

Mutual recursion across three entry points:

* `execOne` runs a single instruction.
* `exec`    runs a `Program` (list of instructions) sequentially.
* `run`     runs a function call from a `Module` by index.

Stack-shape mismatches yield `Continuation.Invalid` — those should be ruled
out by a future validator; until then the interpreter defends against them
at runtime. Real Wasm traps (division by zero, signed-divide overflow,
`unreachable`) yield `Continuation.Trap` with a descriptive string. -/

mutual

def execOne (fuel : Nat) (m : Module) (st : Store α) (s : Locals) (inst : Instruction)
    (env : HostEnv α := {}) : Continuation α :=
  match fuel, inst with
    | 0, _ => .OutOfFuel

    -- Locals
    | _, Instruction.localGet i => match s.get i with
      | some v => .Fallthrough st { s with values := v :: s.values }
      | none   => .Invalid "localGet index out of bounds"
    | _, Instruction.localSet i => match s.values with
      | v :: vs => match s.set? i v with
        | some s => .Fallthrough st { s with values := vs }
        | none   => .Invalid "localSet index out of bounds"
      | _ => .Invalid "localSet with empty stack"

    -- Globals
    | _, Instruction.globalGet i => match st.globals.globals[i]? with
      | some v => .Fallthrough st { s with values := v :: s.values }
      | none   => .Invalid "globalGet index out of bounds"
    | _, Instruction.globalSet i => match s.values with
      | v :: vs => match st.globals.globals[i]? with
        | some _ =>
          .Fallthrough { st with globals := { globals := st.globals.globals.set i v } }
                       { s with values := vs }
        | none => .Invalid "globalSet index out of bounds"
      | _ => .Invalid "globalSet with empty stack"

    -- Constants
    | _, Instruction.const v    => .Fallthrough st { s with values := .i32 v :: s.values }
    | _, Instruction.constI64 v => .Fallthrough st { s with values := .i64 v :: s.values }

    -- i32 arithmetic
    | _, Instruction.add => match s.values with
      | .i32 a :: .i32 b :: vs => .Fallthrough st { s with values := .i32 (a + b) :: vs }
      | _ => .Invalid "add: ill-shaped operand stack"
    | _, Instruction.sub => match s.values with
      | .i32 a :: .i32 b :: vs => .Fallthrough st { s with values := .i32 (b - a) :: vs }
      | _ => .Invalid "sub: ill-shaped operand stack"
    | _, Instruction.mul => match s.values with
      | .i32 a :: .i32 b :: vs => .Fallthrough st { s with values := .i32 (a * b) :: vs }
      | _ => .Invalid "mul: ill-shaped operand stack"
    | _, Instruction.divU => match s.values with
      | .i32 b :: .i32 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else .Fallthrough st { s with values := .i32 (a / b) :: vs }
      | _ => .Invalid "divU: ill-shaped operand stack"
    | _, Instruction.divS => match s.values with
      | .i32 b :: .i32 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else if a = 0x80000000 ∧ b = 0xFFFFFFFF then .Trap st "integer overflow"
        else
          let q : UInt32 := (Int32.ofInt (Int.tdiv a.toInt32.toInt b.toInt32.toInt)).toUInt32
          .Fallthrough st { s with values := .i32 q :: vs }
      | _ => .Invalid "divS: ill-shaped operand stack"
    | _, Instruction.remU => match s.values with
      | .i32 b :: .i32 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else .Fallthrough st { s with values := .i32 (a % b) :: vs }
      | _ => .Invalid "remU: ill-shaped operand stack"
    | _, Instruction.remS => match s.values with
      | .i32 b :: .i32 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else
          let r' : UInt32 := (Int32.ofInt (Int.tmod a.toInt32.toInt b.toInt32.toInt)).toUInt32
          .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "remS: ill-shaped operand stack"

    -- i32 comparison
    | _, Instruction.eqz => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a = 0 then 1 else 0) :: vs }
      | _ => .Invalid "eqz: ill-shaped operand stack"
    | _, Instruction.eq => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a = b then 1 else 0) :: vs }
      | _ => .Invalid "eq: ill-shaped operand stack"
    | _, Instruction.ne => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a ≠ b then 1 else 0) :: vs }
      | _ => .Invalid "ne: ill-shaped operand stack"
    | _, Instruction.ltU => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a < b then 1 else 0) :: vs }
      | _ => .Invalid "ltU: ill-shaped operand stack"
    | _, Instruction.ltS => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt32 < b.toInt32 then 1 else 0) :: vs }
      | _ => .Invalid "ltS: ill-shaped operand stack"
    | _, Instruction.gtU => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a > b then 1 else 0) :: vs }
      | _ => .Invalid "gtU: ill-shaped operand stack"
    | _, Instruction.gtS => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt32 > b.toInt32 then 1 else 0) :: vs }
      | _ => .Invalid "gtS: ill-shaped operand stack"
    | _, Instruction.leU => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a ≤ b then 1 else 0) :: vs }
      | _ => .Invalid "leU: ill-shaped operand stack"
    | _, Instruction.leS => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt32 ≤ b.toInt32 then 1 else 0) :: vs }
      | _ => .Invalid "leS: ill-shaped operand stack"
    | _, Instruction.geU => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a ≥ b then 1 else 0) :: vs }
      | _ => .Invalid "geU: ill-shaped operand stack"
    | _, Instruction.geS => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt32 ≥ b.toInt32 then 1 else 0) :: vs }
      | _ => .Invalid "geS: ill-shaped operand stack"

    -- i32 bitwise / shift / counting
    | _, Instruction.and => match s.values with
      | .i32 a :: .i32 b :: vs => .Fallthrough st { s with values := .i32 (a &&& b) :: vs }
      | _ => .Invalid "and: ill-shaped operand stack"
    | _, Instruction.or => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (a ||| b) :: vs }
      | _ => .Invalid "or: ill-shaped operand stack"
    | _, Instruction.xor => match s.values with
      | .i32 b :: .i32 a :: vs => .Fallthrough st { s with values := .i32 (a ^^^ b) :: vs }
      | _ => .Invalid "xor: ill-shaped operand stack"
    | _, Instruction.shl => match s.values with
      | .i32 b :: .i32 a :: vs =>
        let k := b % 32
        .Fallthrough st { s with values := .i32 (a <<< k) :: vs }
      | _ => .Invalid "shl: ill-shaped operand stack"
    | _, Instruction.shrU => match s.values with
      | .i32 b :: .i32 a :: vs =>
        let k := b % 32
        .Fallthrough st { s with values := .i32 (a >>> k) :: vs }
      | _ => .Invalid "shrU: ill-shaped operand stack"
    | _, Instruction.shrS => match s.values with
      | .i32 b :: .i32 a :: vs =>
        let k : Nat := (b % 32).toNat
        let r' : UInt32 := UInt32.ofNat (BitVec.sshiftRight a.toBitVec k).toNat
        .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "shrS: ill-shaped operand stack"
    | _, Instruction.rotl => match s.values with
      | .i32 b :: .i32 a :: vs =>
        let k := b % 32
        let r' : UInt32 := if k = 0 then a else (a <<< k) ||| (a >>> (32 - k))
        .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "rotl: ill-shaped operand stack"
    | _, Instruction.rotr => match s.values with
      | .i32 b :: .i32 a :: vs =>
        let k := b % 32
        let r' : UInt32 := if k = 0 then a else (a >>> k) ||| (a <<< (32 - k))
        .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "rotr: ill-shaped operand stack"
    | _, Instruction.clz => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i32 (UInt32.ofNat (clz32 32 a)) :: vs }
      | _ => .Invalid "clz: ill-shaped operand stack"
    | _, Instruction.ctz => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i32 (UInt32.ofNat (ctz32 32 a)) :: vs }
      | _ => .Invalid "ctz: ill-shaped operand stack"
    | _, Instruction.popcnt => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i32 (UInt32.ofNat (popcnt32 32 a 0)) :: vs }
      | _ => .Invalid "popcnt: ill-shaped operand stack"

    -- i64 arithmetic
    | _, Instruction.addI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a + b) :: vs }
      | _ => .Invalid "addI64: ill-shaped operand stack"
    | _, Instruction.subI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a - b) :: vs }
      | _ => .Invalid "subI64: ill-shaped operand stack"
    | _, Instruction.mulI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a * b) :: vs }
      | _ => .Invalid "mulI64: ill-shaped operand stack"
    | _, Instruction.divUI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else .Fallthrough st { s with values := .i64 (a / b) :: vs }
      | _ => .Invalid "divUI64: ill-shaped operand stack"
    | _, Instruction.divSI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else if a = 0x8000000000000000 ∧ b = 0xFFFFFFFFFFFFFFFF then .Trap st "integer overflow"
        else
          let q : UInt64 := (Int64.ofInt (Int.tdiv a.toInt64.toInt b.toInt64.toInt)).toUInt64
          .Fallthrough st { s with values := .i64 q :: vs }
      | _ => .Invalid "divSI64: ill-shaped operand stack"
    | _, Instruction.remUI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else .Fallthrough st { s with values := .i64 (a % b) :: vs }
      | _ => .Invalid "remUI64: ill-shaped operand stack"
    | _, Instruction.remSI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        if b = 0 then .Trap st "integer divide by zero"
        else
          let r' : UInt64 := (Int64.ofInt (Int.tmod a.toInt64.toInt b.toInt64.toInt)).toUInt64
          .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "remSI64: ill-shaped operand stack"

    -- i64 comparison (result is i32 0/1)
    | _, Instruction.eqzI64 => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a = 0 then 1 else 0) :: vs }
      | _ => .Invalid "eqzI64: ill-shaped operand stack"
    | _, Instruction.eqI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a = b then 1 else 0) :: vs }
      | _ => .Invalid "eqI64: ill-shaped operand stack"
    | _, Instruction.neI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a ≠ b then 1 else 0) :: vs }
      | _ => .Invalid "neI64: ill-shaped operand stack"
    | _, Instruction.ltUI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a < b then 1 else 0) :: vs }
      | _ => .Invalid "ltUI64: ill-shaped operand stack"
    | _, Instruction.ltSI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt64 < b.toInt64 then 1 else 0) :: vs }
      | _ => .Invalid "ltSI64: ill-shaped operand stack"
    | _, Instruction.gtUI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a > b then 1 else 0) :: vs }
      | _ => .Invalid "gtUI64: ill-shaped operand stack"
    | _, Instruction.gtSI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt64 > b.toInt64 then 1 else 0) :: vs }
      | _ => .Invalid "gtSI64: ill-shaped operand stack"
    | _, Instruction.leUI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a ≤ b then 1 else 0) :: vs }
      | _ => .Invalid "leUI64: ill-shaped operand stack"
    | _, Instruction.leSI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt64 ≤ b.toInt64 then 1 else 0) :: vs }
      | _ => .Invalid "leSI64: ill-shaped operand stack"
    | _, Instruction.geUI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a ≥ b then 1 else 0) :: vs }
      | _ => .Invalid "geUI64: ill-shaped operand stack"
    | _, Instruction.geSI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i32 (if a.toInt64 ≥ b.toInt64 then 1 else 0) :: vs }
      | _ => .Invalid "geSI64: ill-shaped operand stack"

    -- i64 bitwise / shift / counting
    | _, Instruction.andI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a &&& b) :: vs }
      | _ => .Invalid "andI64: ill-shaped operand stack"
    | _, Instruction.orI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a ||| b) :: vs }
      | _ => .Invalid "orI64: ill-shaped operand stack"
    | _, Instruction.xorI64 => match s.values with
      | .i64 b :: .i64 a :: vs => .Fallthrough st { s with values := .i64 (a ^^^ b) :: vs }
      | _ => .Invalid "xorI64: ill-shaped operand stack"
    | _, Instruction.shlI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k := b % 64
        .Fallthrough st { s with values := .i64 (a <<< k) :: vs }
      | _ => .Invalid "shlI64: ill-shaped operand stack"
    | _, Instruction.shrUI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k := b % 64
        .Fallthrough st { s with values := .i64 (a >>> k) :: vs }
      | _ => .Invalid "shrUI64: ill-shaped operand stack"
    | _, Instruction.shrSI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k : Nat := (b % 64).toNat
        let r' : UInt64 := UInt64.ofNat (BitVec.sshiftRight a.toBitVec k).toNat
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "shrSI64: ill-shaped operand stack"
    | _, Instruction.rotlI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k := b % 64
        let r' : UInt64 := if k = 0 then a else (a <<< k) ||| (a >>> (64 - k))
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "rotlI64: ill-shaped operand stack"
    | _, Instruction.rotrI64 => match s.values with
      | .i64 b :: .i64 a :: vs =>
        let k := b % 64
        let r' : UInt64 := if k = 0 then a else (a >>> k) ||| (a <<< (64 - k))
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "rotrI64: ill-shaped operand stack"
    | _, Instruction.clzI64 => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i64 (UInt64.ofNat (clz64 64 a)) :: vs }
      | _ => .Invalid "clzI64: ill-shaped operand stack"
    | _, Instruction.ctzI64 => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i64 (UInt64.ofNat (ctz64 64 a)) :: vs }
      | _ => .Invalid "ctzI64: ill-shaped operand stack"
    | _, Instruction.popcntI64 => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i64 (UInt64.ofNat (popcnt64 64 a 0)) :: vs }
      | _ => .Invalid "popcntI64: ill-shaped operand stack"

    -- Conversions / sign-extension
    | _, Instruction.wrapI64 => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .i32 (UInt32.ofNat (a.toNat % 2 ^ 32)) :: vs }
      | _ => .Invalid "wrapI64: ill-shaped operand stack"
    | _, Instruction.extendUI32 => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i64 (UInt64.ofNat a.toNat) :: vs }
      | _ => .Invalid "extendUI32: ill-shaped operand stack"
    | _, Instruction.extendSI32 => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .i64 ((Int64.ofInt a.toInt32.toInt).toUInt64) :: vs }
      | _ => .Invalid "extendSI32: ill-shaped operand stack"
    | _, Instruction.extend8S => match s.values with
      | .i32 a :: vs =>
        let r' : UInt32 := (Int32.ofInt (signExtend (a.toNat % 256) 8)).toUInt32
        .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "extend8S: ill-shaped operand stack"
    | _, Instruction.extend16S => match s.values with
      | .i32 a :: vs =>
        let r' : UInt32 := (Int32.ofInt (signExtend (a.toNat % 65536) 16)).toUInt32
        .Fallthrough st { s with values := .i32 r' :: vs }
      | _ => .Invalid "extend16S: ill-shaped operand stack"
    | _, Instruction.extend8SI64 => match s.values with
      | .i64 a :: vs =>
        let r' : UInt64 := (Int64.ofInt (signExtend (a.toNat % 256) 8)).toUInt64
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "extend8SI64: ill-shaped operand stack"
    | _, Instruction.extend16SI64 => match s.values with
      | .i64 a :: vs =>
        let r' : UInt64 := (Int64.ofInt (signExtend (a.toNat % 65536) 16)).toUInt64
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "extend16SI64: ill-shaped operand stack"
    | _, Instruction.extend32SI64 => match s.values with
      | .i64 a :: vs =>
        let r' : UInt64 := (Int64.ofInt (signExtend (a.toNat % 2 ^ 32) 32)).toUInt64
        .Fallthrough st { s with values := .i64 r' :: vs }
      | _ => .Invalid "extend32SI64: ill-shaped operand stack"

    -- Float constants
    | _, Instruction.f32Const v => .Fallthrough st { s with values := .f32 v :: s.values }
    | _, Instruction.f64Const v => .Fallthrough st { s with values := .f64 v :: s.values }

    -- f32 arithmetic. The top operand is `b`, the one below it `a`; results
    -- follow the wasm convention `a ⊘ b` (`sub` is `a - b`, `div` is `a / b`).
    | _, Instruction.f32Add => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Add a b) :: vs }
      | _ => .Invalid "f32Add: ill-shaped operand stack"
    | _, Instruction.f32Sub => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Sub a b) :: vs }
      | _ => .Invalid "f32Sub: ill-shaped operand stack"
    | _, Instruction.f32Mul => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Mul a b) :: vs }
      | _ => .Invalid "f32Mul: ill-shaped operand stack"
    | _, Instruction.f32Div => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Div a b) :: vs }
      | _ => .Invalid "f32Div: ill-shaped operand stack"
    | _, Instruction.f32Min => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Min a b) :: vs }
      | _ => .Invalid "f32Min: ill-shaped operand stack"
    | _, Instruction.f32Max => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Max a b) :: vs }
      | _ => .Invalid "f32Max: ill-shaped operand stack"
    | _, Instruction.f32Copysign => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Copysign a b) :: vs }
      | _ => .Invalid "f32Copysign: ill-shaped operand stack"

    -- f64 arithmetic
    | _, Instruction.f64Add => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Add a b) :: vs }
      | _ => .Invalid "f64Add: ill-shaped operand stack"
    | _, Instruction.f64Sub => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Sub a b) :: vs }
      | _ => .Invalid "f64Sub: ill-shaped operand stack"
    | _, Instruction.f64Mul => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Mul a b) :: vs }
      | _ => .Invalid "f64Mul: ill-shaped operand stack"
    | _, Instruction.f64Div => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Div a b) :: vs }
      | _ => .Invalid "f64Div: ill-shaped operand stack"
    | _, Instruction.f64Min => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Min a b) :: vs }
      | _ => .Invalid "f64Min: ill-shaped operand stack"
    | _, Instruction.f64Max => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Max a b) :: vs }
      | _ => .Invalid "f64Max: ill-shaped operand stack"
    | _, Instruction.f64Copysign => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Copysign a b) :: vs }
      | _ => .Invalid "f64Copysign: ill-shaped operand stack"

    -- f32 unary
    | _, Instruction.f32Abs => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Abs a) :: vs }
      | _ => .Invalid "f32Abs: ill-shaped operand stack"
    | _, Instruction.f32Neg => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Neg a) :: vs }
      | _ => .Invalid "f32Neg: ill-shaped operand stack"
    | _, Instruction.f32Sqrt => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Sqrt a) :: vs }
      | _ => .Invalid "f32Sqrt: ill-shaped operand stack"
    | _, Instruction.f32Ceil => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Ceil a) :: vs }
      | _ => .Invalid "f32Ceil: ill-shaped operand stack"
    | _, Instruction.f32Floor => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Floor a) :: vs }
      | _ => .Invalid "f32Floor: ill-shaped operand stack"
    | _, Instruction.f32Trunc => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Trunc a) :: vs }
      | _ => .Invalid "f32Trunc: ill-shaped operand stack"
    | _, Instruction.f32Nearest => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f32 (f32Nearest a) :: vs }
      | _ => .Invalid "f32Nearest: ill-shaped operand stack"

    -- f64 unary
    | _, Instruction.f64Abs => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Abs a) :: vs }
      | _ => .Invalid "f64Abs: ill-shaped operand stack"
    | _, Instruction.f64Neg => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Neg a) :: vs }
      | _ => .Invalid "f64Neg: ill-shaped operand stack"
    | _, Instruction.f64Sqrt => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Sqrt a) :: vs }
      | _ => .Invalid "f64Sqrt: ill-shaped operand stack"
    | _, Instruction.f64Ceil => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Ceil a) :: vs }
      | _ => .Invalid "f64Ceil: ill-shaped operand stack"
    | _, Instruction.f64Floor => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Floor a) :: vs }
      | _ => .Invalid "f64Floor: ill-shaped operand stack"
    | _, Instruction.f64Trunc => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Trunc a) :: vs }
      | _ => .Invalid "f64Trunc: ill-shaped operand stack"
    | _, Instruction.f64Nearest => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f64 (f64Nearest a) :: vs }
      | _ => .Invalid "f64Nearest: ill-shaped operand stack"

    -- f32 comparison (top = `b`, below = `a`; compares `a ⋈ b`)
    | _, Instruction.f32Eq => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Eq a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Eq: ill-shaped operand stack"
    | _, Instruction.f32Ne => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Ne a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Ne: ill-shaped operand stack"
    | _, Instruction.f32Lt => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Lt a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Lt: ill-shaped operand stack"
    | _, Instruction.f32Gt => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Gt a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Gt: ill-shaped operand stack"
    | _, Instruction.f32Le => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Le a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Le: ill-shaped operand stack"
    | _, Instruction.f32Ge => match s.values with
      | .f32 b :: .f32 a :: vs => .Fallthrough st { s with values := .i32 (if f32Ge a b then 1 else 0) :: vs }
      | _ => .Invalid "f32Ge: ill-shaped operand stack"

    -- f64 comparison
    | _, Instruction.f64Eq => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Eq a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Eq: ill-shaped operand stack"
    | _, Instruction.f64Ne => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Ne a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Ne: ill-shaped operand stack"
    | _, Instruction.f64Lt => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Lt a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Lt: ill-shaped operand stack"
    | _, Instruction.f64Gt => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Gt a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Gt: ill-shaped operand stack"
    | _, Instruction.f64Le => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Le a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Le: ill-shaped operand stack"
    | _, Instruction.f64Ge => match s.values with
      | .f64 b :: .f64 a :: vs => .Fallthrough st { s with values := .i32 (if f64Ge a b then 1 else 0) :: vs }
      | _ => .Invalid "f64Ge: ill-shaped operand stack"

    -- Float memory loads / stores. Bytes move unchanged through the same
    -- little-endian `Mem` words the i32/i64 accesses use.
    | _, .f32Load off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough st { s with values := .f32 (st.mem.read32 (a + off)) :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough st { s with values := .f32 (st.mem.read32 (a.toUInt32 + off)) :: vs }
      | _ => .Invalid "f32Load: ill-shaped operand stack"
    | _, .f64Load off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough st { s with values := .f64 (st.mem.read64 (a + off)) :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough st { s with values := .f64 (st.mem.read64 (a.toUInt32 + off)) :: vs }
      | _ => .Invalid "f64Load: ill-shaped operand stack"
    | _, .f32Store off => match s.values with
      | .f32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough { st with mem := st.mem.write32 (a + off) v } { s with values := vs }
      | .f32 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough { st with mem := st.mem.write32 (a.toUInt32 + off) v } { s with values := vs }
      | _ => .Invalid "f32Store: ill-shaped operand stack"
    | _, .f64Store off => match s.values with
      | .f64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough { st with mem := st.mem.write64 (a + off) v } { s with values := vs }
      | .f64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough { st with mem := st.mem.write64 (a.toUInt32 + off) v } { s with values := vs }
      | _ => .Invalid "f64Store: ill-shaped operand stack"

    -- Integer → float
    | _, Instruction.f32ConvertI32S => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .f32 (f32ConvertI32S a) :: vs }
      | _ => .Invalid "f32ConvertI32S: ill-shaped operand stack"
    | _, Instruction.f32ConvertI32U => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .f32 (f32ConvertI32U a) :: vs }
      | _ => .Invalid "f32ConvertI32U: ill-shaped operand stack"
    | _, Instruction.f32ConvertI64S => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .f32 (f32ConvertI64S a) :: vs }
      | _ => .Invalid "f32ConvertI64S: ill-shaped operand stack"
    | _, Instruction.f32ConvertI64U => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .f32 (f32ConvertI64U a) :: vs }
      | _ => .Invalid "f32ConvertI64U: ill-shaped operand stack"
    | _, Instruction.f64ConvertI32S => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .f64 (f64ConvertI32S a) :: vs }
      | _ => .Invalid "f64ConvertI32S: ill-shaped operand stack"
    | _, Instruction.f64ConvertI32U => match s.values with
      | .i32 a :: vs => .Fallthrough st { s with values := .f64 (f64ConvertI32U a) :: vs }
      | _ => .Invalid "f64ConvertI32U: ill-shaped operand stack"
    | _, Instruction.f64ConvertI64S => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .f64 (f64ConvertI64S a) :: vs }
      | _ => .Invalid "f64ConvertI64S: ill-shaped operand stack"
    | _, Instruction.f64ConvertI64U => match s.values with
      | .i64 a :: vs => .Fallthrough st { s with values := .f64 (f64ConvertI64U a) :: vs }
      | _ => .Invalid "f64ConvertI64U: ill-shaped operand stack"

    -- Float → integer (trapping). NaN traps "invalid conversion to
    -- integer"; an out-of-range magnitude traps "integer overflow".
    | _, Instruction.i32TruncF32S => match s.values with
      | .f32 a :: vs => match i32TruncF32S a with
        | some r => .Fallthrough st { s with values := .i32 r :: vs }
        | none => if (Float32.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i32TruncF32S: ill-shaped operand stack"
    | _, Instruction.i32TruncF32U => match s.values with
      | .f32 a :: vs => match i32TruncF32U a with
        | some r => .Fallthrough st { s with values := .i32 r :: vs }
        | none => if (Float32.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i32TruncF32U: ill-shaped operand stack"
    | _, Instruction.i32TruncF64S => match s.values with
      | .f64 a :: vs => match i32TruncF64S a with
        | some r => .Fallthrough st { s with values := .i32 r :: vs }
        | none => if (Float.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i32TruncF64S: ill-shaped operand stack"
    | _, Instruction.i32TruncF64U => match s.values with
      | .f64 a :: vs => match i32TruncF64U a with
        | some r => .Fallthrough st { s with values := .i32 r :: vs }
        | none => if (Float.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i32TruncF64U: ill-shaped operand stack"
    | _, Instruction.i64TruncF32S => match s.values with
      | .f32 a :: vs => match i64TruncF32S a with
        | some r => .Fallthrough st { s with values := .i64 r :: vs }
        | none => if (Float32.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i64TruncF32S: ill-shaped operand stack"
    | _, Instruction.i64TruncF32U => match s.values with
      | .f32 a :: vs => match i64TruncF32U a with
        | some r => .Fallthrough st { s with values := .i64 r :: vs }
        | none => if (Float32.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i64TruncF32U: ill-shaped operand stack"
    | _, Instruction.i64TruncF64S => match s.values with
      | .f64 a :: vs => match i64TruncF64S a with
        | some r => .Fallthrough st { s with values := .i64 r :: vs }
        | none => if (Float.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i64TruncF64S: ill-shaped operand stack"
    | _, Instruction.i64TruncF64U => match s.values with
      | .f64 a :: vs => match i64TruncF64U a with
        | some r => .Fallthrough st { s with values := .i64 r :: vs }
        | none => if (Float.ofBits a).isNaN then .Trap st "invalid conversion to integer"
                  else .Trap st "integer overflow"
      | _ => .Invalid "i64TruncF64U: ill-shaped operand stack"

    -- Float → integer (saturating; never traps)
    | _, Instruction.i32TruncSatF32S => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .i32 (i32TruncSatF32S a) :: vs }
      | _ => .Invalid "i32TruncSatF32S: ill-shaped operand stack"
    | _, Instruction.i32TruncSatF32U => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .i32 (i32TruncSatF32U a) :: vs }
      | _ => .Invalid "i32TruncSatF32U: ill-shaped operand stack"
    | _, Instruction.i32TruncSatF64S => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .i32 (i32TruncSatF64S a) :: vs }
      | _ => .Invalid "i32TruncSatF64S: ill-shaped operand stack"
    | _, Instruction.i32TruncSatF64U => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .i32 (i32TruncSatF64U a) :: vs }
      | _ => .Invalid "i32TruncSatF64U: ill-shaped operand stack"
    | _, Instruction.i64TruncSatF32S => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .i64 (i64TruncSatF32S a) :: vs }
      | _ => .Invalid "i64TruncSatF32S: ill-shaped operand stack"
    | _, Instruction.i64TruncSatF32U => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .i64 (i64TruncSatF32U a) :: vs }
      | _ => .Invalid "i64TruncSatF32U: ill-shaped operand stack"
    | _, Instruction.i64TruncSatF64S => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .i64 (i64TruncSatF64S a) :: vs }
      | _ => .Invalid "i64TruncSatF64S: ill-shaped operand stack"
    | _, Instruction.i64TruncSatF64U => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .i64 (i64TruncSatF64U a) :: vs }
      | _ => .Invalid "i64TruncSatF64U: ill-shaped operand stack"

    -- Float ↔ float, and bitwise reinterpret (a pure retag of the bits)
    | _, Instruction.f32DemoteF64 => match s.values with
      | .f64 a :: vs => .Fallthrough st { s with values := .f32 (f32DemoteF64 a) :: vs }
      | _ => .Invalid "f32DemoteF64: ill-shaped operand stack"
    | _, Instruction.f64PromoteF32 => match s.values with
      | .f32 a :: vs => .Fallthrough st { s with values := .f64 (f64PromoteF32 a) :: vs }
      | _ => .Invalid "f64PromoteF32: ill-shaped operand stack"
    | _, Instruction.i32ReinterpretF32 => match s.values with
      | .f32 b :: vs => .Fallthrough st { s with values := .i32 b :: vs }
      | _ => .Invalid "i32ReinterpretF32: ill-shaped operand stack"
    | _, Instruction.i64ReinterpretF64 => match s.values with
      | .f64 b :: vs => .Fallthrough st { s with values := .i64 b :: vs }
      | _ => .Invalid "i64ReinterpretF64: ill-shaped operand stack"
    | _, Instruction.f32ReinterpretI32 => match s.values with
      | .i32 b :: vs => .Fallthrough st { s with values := .f32 b :: vs }
      | _ => .Invalid "f32ReinterpretI32: ill-shaped operand stack"
    | _, Instruction.f64ReinterpretI64 => match s.values with
      | .i64 b :: vs => .Fallthrough st { s with values := .f64 b :: vs }
      | _ => .Invalid "f64ReinterpretI64: ill-shaped operand stack"

    -- Structured control. Stack discipline matches the wasm spec:
    -- on entry, the top `paramArity` values are the construct's inputs;
    -- on a `br` to a `block`/`if` we keep the top `resultArity` values
    -- (the block's output); on a `br` back to a `loop` we keep the top
    -- `paramArity` values (the loop's next-iteration inputs). Values
    -- pushed between the entry mark and the kept top are discarded —
    -- the validator guarantees there are exactly the right number of
    -- "kept" values on top at every branch and at fall-through.
    | f + 1, .block paramArity resultArity body =>
      let belowStack := s.values.drop paramArity
      match exec f m st s body env with
      | .Fallthrough r' s' =>
        .Fallthrough r' { s' with values := s'.values.take resultArity ++ belowStack }
      | .Break 0 r' s' =>
        -- `br 0` to a block exits with the block's result values. We
        -- preserve whatever the brancher left on top (validator says
        -- it's exactly `resultArity` values).
        .Fallthrough r' { s' with values := s'.values.take resultArity ++ belowStack }
      | .Break (k + 1) r' s' => .Break k r' s'
      | other => other
    | f + 1, .loop paramArity resultArity body =>
      let belowStack := s.values.drop paramArity
      match exec f m st s body env with
      | .Fallthrough r' s' =>
        .Fallthrough r' { s' with values := s'.values.take resultArity ++ belowStack }
      | .Break 0 r' s' =>
        -- `br 0` to a loop = restart from the top. Reset the stack to
        -- the kept top values (the loop's next-iteration params) atop
        -- the entry's below-stack, then re-execute the loop.
        execOne f m r' { s' with values := s'.values.take paramArity ++ belowStack } inst env
      | .Break (k + 1) r' s' => .Break k r' s'
      | other => other
    | f + 1, .iff paramArity resultArity thn els => match s.values with
      | .i32 c :: vs =>
        let belowStack := vs.drop paramArity
        let s' : Locals := { s with values := vs }
        let body := if c ≠ 0 then thn else els
        match exec f m st s' body env with
        | .Fallthrough r' s'' =>
          .Fallthrough r' { s'' with values := s''.values.take resultArity ++ belowStack }
        | .Break 0 r' s'' =>
          .Fallthrough r' { s'' with values := s''.values.take resultArity ++ belowStack }
        | .Break (k + 1) r' s'' => .Break k r' s''
        | other => other
      | _ => .Invalid "iff: ill-shaped operand stack"

    -- Branching
    | _, .br n => .Break n st s
    | _, .br_if n => match s.values with
      | .i32 0 :: vs => .Fallthrough st { s with values := vs }
      | .i32 _ :: vs => .Break n st { s with values := vs }
      | _ => .Invalid "br_if: ill-shaped operand stack"
    | _, .brTable targets dflt => match s.values with
      | .i32 i :: vs =>
        let n := i.toNat
        let lbl := if h : n < targets.length then targets[n] else dflt
        .Break lbl st { s with values := vs }
      | _ => .Invalid "brTable: ill-shaped operand stack"

    -- Calls
    | f + 1, .call id => match run f m id st s.values env with
      | .Success vs st' => .Fallthrough st' { s with values := vs }
      | .Trap st' msg   => .Trap st' msg
      | .Invalid msg    => .Invalid msg
      | .OutOfFuel      => .OutOfFuel

    -- Tail calls. Both build a `ReturnCall` continuation; `run` resolves
    -- the re-dispatch (consuming one unit of fuel per tail call), so a
    -- chain of N tail calls needs O(N) fuel but constant host stack.
    -- `return_call_indirect` performs the same table lookup, null check,
    -- and signature check as `call_indirect`, with the same trap wording.
    | _, .returnCall id => .ReturnCall id st s.values
    | _, .returnCallIndirect typeIdx tableIdx => match s.values with
      | .i32 i :: rest =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"returnCallIndirect: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none                       => .Trap st "undefined element"
          | some (.funcref none)       => .Trap st "uninitialized element"
          | some (.funcref (some fid)) =>
            match m.funcSig? fid with
            | none    => .Invalid s!"returnCallIndirect: function index {fid} out of range"
            | some fn =>
              match m.types[typeIdx]? with
              | none    => .Invalid s!"returnCallIndirect: type index {typeIdx} out of range"
              | some ty =>
                if fn.params = ty.params ∧ fn.results = ty.results then
                  .ReturnCall fid st rest
                else .Trap st "indirect call type mismatch"
          | some _ => .Invalid "returnCallIndirect: non-funcref table entry"
      | .i64 i :: rest =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"returnCallIndirect: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none                       => .Trap st "undefined element"
          | some (.funcref none)       => .Trap st "uninitialized element"
          | some (.funcref (some fid)) =>
            match m.funcSig? fid with
            | none    => .Invalid s!"returnCallIndirect: function index {fid} out of range"
            | some fn =>
              match m.types[typeIdx]? with
              | none    => .Invalid s!"returnCallIndirect: type index {typeIdx} out of range"
              | some ty =>
                if fn.params = ty.params ∧ fn.results = ty.results then
                  .ReturnCall fid st rest
                else .Trap st "indirect call type mismatch"
          | some _ => .Invalid "returnCallIndirect: non-funcref table entry"
      | _ => .Invalid "returnCallIndirect: ill-shaped operand stack"

    -- Typed function references. `call_ref` dispatches through a popped
    -- funcref (null traps with the spec's wording); validation makes a
    -- runtime signature check unnecessary. `return_call_ref` is the
    -- tail-call form, resolved by `run` like the other tail calls.
    | f + 1, .callRef _typeIdx => match s.values with
      | .funcref none :: _ => .Trap st "null function reference"
      | .funcref (some fid) :: rest =>
        (match run f m fid st rest env with
         | .Success vs st' => .Fallthrough st' { s with values := vs }
         | .Trap st' msg   => .Trap st' msg
         | .Invalid msg    => .Invalid msg
         | .OutOfFuel      => .OutOfFuel)
      | _ => .Invalid "callRef: ill-shaped operand stack"
    | _, .returnCallRef _typeIdx => match s.values with
      | .funcref none :: _ => .Trap st "null function reference"
      | .funcref (some fid) :: rest => .ReturnCall fid st rest
      | _ => .Invalid "returnCallRef: ill-shaped operand stack"
    | _, .refAsNonNull => match s.values with
      | v :: vs =>
        match v.isNullRef? with
        | some true  => .Trap st "null reference"
        | some false => .Fallthrough st { s with values := v :: vs }
        | none       => .Invalid "refAsNonNull: ill-shaped operand stack"
      | _ => .Invalid "refAsNonNull: ill-shaped operand stack"
    | _, .brOnNull n => match s.values with
      | v :: vs =>
        match v.isNullRef? with
        | some true  => .Break n st { s with values := vs }
        | some false => .Fallthrough st { s with values := v :: vs }
        | none       => .Invalid "brOnNull: ill-shaped operand stack"
      | _ => .Invalid "brOnNull: ill-shaped operand stack"
    | _, .brOnNonNull n => match s.values with
      | v :: vs =>
        match v.isNullRef? with
        | some true  => .Fallthrough st { s with values := vs }
        | some false => .Break n st { s with values := v :: vs }
        | none       => .Invalid "brOnNonNull: ill-shaped operand stack"
      | _ => .Invalid "brOnNonNull: ill-shaped operand stack"

    -- Indirect call. Pop an i32 index, look up the entry in the chosen
    -- table, then dispatch to the referenced function — trapping on
    -- out-of-bounds, null refs, or signature mismatches against the
    -- declared `(type N)`. Trap message strings match the wasm spec's
    -- canonical wording so the testsuite's `assert_trap` text matcher
    -- accepts them.
    | f + 1, .callIndirect typeIdx tableIdx => match s.values with
      | .i32 i :: rest =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"callIndirect: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none                       => .Trap st "undefined element"
          | some (.funcref none)       => .Trap st "uninitialized element"
          | some (.funcref (some fid)) =>
            -- Signature lookup is in the *unified* function index space
            -- (imports first), matching what the table entry refers to.
            match m.funcSig? fid with
            | none    => .Invalid s!"callIndirect: function index {fid} out of range"
            | some fn =>
              match m.types[typeIdx]? with
              | none    => .Invalid s!"callIndirect: type index {typeIdx} out of range"
              | some ty =>
                if fn.params = ty.params ∧ fn.results = ty.results then
                  match run f m fid st rest env with
                  | .Success vs st' => .Fallthrough st' { s with values := vs }
                  | .Trap st' msg   => .Trap st' msg
                  | .Invalid msg    => .Invalid msg
                  | .OutOfFuel      => .OutOfFuel
                else .Trap st "indirect call type mismatch"
          | some _ => .Invalid "callIndirect: non-funcref table entry"
      -- table64: the selector arrives as an i64. The flow is identical to
      -- the i32 arm above.
      | .i64 i :: rest =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"callIndirect: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none                       => .Trap st "undefined element"
          | some (.funcref none)       => .Trap st "uninitialized element"
          | some (.funcref (some fid)) =>
            match m.funcSig? fid with
            | none    => .Invalid s!"callIndirect: function index {fid} out of range"
            | some fn =>
              match m.types[typeIdx]? with
              | none    => .Invalid s!"callIndirect: type index {typeIdx} out of range"
              | some ty =>
                if fn.params = ty.params ∧ fn.results = ty.results then
                  match run f m fid st rest env with
                  | .Success vs st' => .Fallthrough st' { s with values := vs }
                  | .Trap st' msg   => .Trap st' msg
                  | .Invalid msg    => .Invalid msg
                  | .OutOfFuel      => .OutOfFuel
                else .Trap st "indirect call type mismatch"
          | some _ => .Invalid "callIndirect: non-funcref table entry"
      | _ => .Invalid "callIndirect: ill-shaped operand stack"

    -- Memory load / store. Every access traps when
    -- `addr.toNat + off.toNat + size > byteCap`; the check is done in
    -- `Nat` to avoid the i32 wraparound that would otherwise hide
    -- accesses with `addr = 0xFFFFFFFC` and `size = 4`, etc.
    | _, .load8U off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (st.mem.read8 (a + off)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (st.mem.read8 (a.toUInt32 + off)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load8U: ill-shaped operand stack"
    | _, .load8S off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (Int32.ofInt (signExtend (st.mem.read8 (a + off)).toNat 8)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (Int32.ofInt (signExtend (st.mem.read8 (a.toUInt32 + off)).toNat 8)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load8S: ill-shaped operand stack"
    | _, .load16U off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read16 (a + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read16 (a.toUInt32 + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load16U: ill-shaped operand stack"
    | _, .load16S off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (Int32.ofInt (signExtend (st.mem.read16 (a + off)).toNat 16)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (Int32.ofInt (signExtend (st.mem.read16 (a.toUInt32 + off)).toNat 16)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load16S: ill-shaped operand stack"
    | _, .load32 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read32 (a + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read32 (a.toUInt32 + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load32: ill-shaped operand stack"
    | _, .store8 off => match s.values with
      | .i32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write8 (a + off) v.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i32 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write8 (a.toUInt32 + off) v.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store8: ill-shaped operand stack"
    | _, .store16 off => match s.values with
      | .i32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write16 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i32 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write16 (a.toUInt32 + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store16: ill-shaped operand stack"
    | _, .store32 off => match s.values with
      | .i32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i32 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a.toUInt32 + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store32: ill-shaped operand stack"
    | _, .load64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read64 (a + off)
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read64 (a.toUInt32 + off)
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load64: ill-shaped operand stack"
    | _, .store64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write64 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write64 (a.toUInt32 + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store64: ill-shaped operand stack"

    | _, .load8UI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read8 (a + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read8 (a.toUInt32 + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load8UI64: ill-shaped operand stack"
    | _, .load8SI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read8 (a + off)).toNat 8)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read8 (a.toUInt32 + off)).toNat 8)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load8SI64: ill-shaped operand stack"
    | _, .load16UI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read16 (a + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read16 (a.toUInt32 + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load16UI64: ill-shaped operand stack"
    | _, .load16SI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read16 (a + off)).toNat 16)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read16 (a.toUInt32 + off)).toNat 16)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load16SI64: ill-shaped operand stack"
    | _, .load32UI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read32 (a + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read32 (a.toUInt32 + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load32UI64: ill-shaped operand stack"
    | _, .load32SI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read32 (a + off)).toNat 32)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read32 (a.toUInt32 + off)).toNat 32)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load32SI64: ill-shaped operand stack"
    | _, .store8I64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write8 (a + off) v.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write8 (a.toUInt32 + off) v.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store8I64: ill-shaped operand stack"
    | _, .store16I64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write16 (a + off) v.toUInt32
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write16 (a.toUInt32 + off) v.toUInt32
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store16I64: ill-shaped operand stack"
    | _, .store32I64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a + off) v.toUInt32
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .i64 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a.toUInt32 + off) v.toUInt32
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store32I64: ill-shaped operand stack"

    -- Memory size / grow. `memory.grow`'s cap is computed once via
    -- `Module.memoryCap` so the semantics and the corresponding wp
    -- lemma share a single matchable shape.
    | _, .memorySize =>
      -- The result type follows the declared memory's address type
      -- (memory64): i64 pages for a 64-bit memory, i32 otherwise.
      .Fallthrough st { s with values := sizeValue m.memIs64 st.mem.pages :: s.values }
    | _, .memoryGrow => match s.values with
      | .i32 delta :: vs =>
        match st.mem.grow delta m.memoryCap with
        | some (mem', cur) =>
          .Fallthrough { st with mem := mem' }
            { s with values := .i32 cur.toUInt32 :: vs }
        | none =>
          .Fallthrough st { s with values := .i32 (0xFFFFFFFF : UInt32) :: vs }
      -- memory64: delta and result are i64. A delta of 2^32 pages or more
      -- can never fit under the implementation cap, so it fails directly
      -- (the spec permits growth to fail); otherwise defer to `Mem.grow`
      -- with the (faithful) 32-bit truncation of the delta.
      | .i64 delta :: vs =>
        if delta.toNat ≥ 2 ^ 32 then
          .Fallthrough st { s with values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: vs }
        else
          match st.mem.grow delta.toUInt32 m.memoryCap with
          | some (mem', cur) =>
            .Fallthrough { st with mem := mem' }
              { s with values := .i64 cur.toUInt64 :: vs }
          | none =>
            .Fallthrough st { s with values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: vs }
      | _ => .Invalid "memoryGrow: ill-shaped operand stack"

    -- Memory fill. Wasm stack discipline: dst is pushed first, then val,
    -- then len, so the list (top = head) has len :: val :: dst :: …
    -- Trap if [dst, dst+len) escapes the legal byte range; the trap is
    -- observed *before* any write, matching the spec's atomicity.
    | _, .memoryFill => match s.values with
      | .i32 len :: .i32 val :: .i32 dst :: vs =>
        let byteCap : Nat := st.mem.pages * 65536
        if dst.toNat + len.toNat > byteCap then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.fill dst.toNat len.toNat val.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      -- memory64: dst and len are i64; the fill value stays i32 per spec.
      | .i64 len :: .i32 val :: .i64 dst :: vs =>
        let byteCap : Nat := st.mem.pages * 65536
        if dst.toNat + len.toNat > byteCap then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.fill dst.toNat len.toNat val.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "memoryFill: ill-shaped operand stack"

    -- memory.copy: pops len :: src :: dst (top = len). Trap is observed
    -- *before* any write, matching the spec's atomicity: if either the
    -- source or destination range escapes the legal byte span, the
    -- whole instruction traps with no partial effect.
    | _, .memoryCopy => match s.values with
      | .i32 len :: .i32 src :: .i32 dst :: vs =>
        let byteCap : Nat := st.mem.pages * 65536
        if dst.toNat + len.toNat > byteCap ∨ src.toNat + len.toNat > byteCap then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.copy dst.toNat src.toNat len.toNat
          .Fallthrough { st with mem := mem' } { s with values := vs }
      -- memory64: all three operands are i64.
      | .i64 len :: .i64 src :: .i64 dst :: vs =>
        let byteCap : Nat := st.mem.pages * 65536
        if dst.toNat + len.toNat > byteCap ∨ src.toNat + len.toNat > byteCap then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.copy dst.toNat src.toNat len.toNat
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "memoryCopy: ill-shaped operand stack"

    -- memory.init i: pops len :: src :: dst (top = len). Source bytes
    -- come from data segment `i`; a dropped segment is modelled as
    -- having length 0, so any nonzero-length init from it traps on
    -- the source-bounds check. Both bounds are checked atomically
    -- before any write.
    | _, .memoryInit i => match s.values with
      | .i32 len :: .i32 src :: .i32 dst :: vs =>
        match st.dataSegments[i]? with
        | none => .Invalid s!"memoryInit: segment index {i} out of range"
        | some none =>
          -- segment already dropped: equivalent to length-0 source
          if 0 < len.toNat ∨ dst.toNat + len.toNat > st.mem.pages * 65536 then
            .Trap st "out of bounds memory access"
          else
            .Fallthrough st { s with values := vs }
        | some (some segBytes) =>
          if src.toNat + len.toNat > segBytes.length
             ∨ dst.toNat + len.toNat > st.mem.pages * 65536 then
            .Trap st "out of bounds memory access"
          else
            let mem' := st.mem.writeBytesFrom dst.toNat segBytes src.toNat len.toNat
            .Fallthrough { st with mem := mem' } { s with values := vs }
      -- memory64: dst takes the memory's address type (i64); src and len
      -- index into the data segment and stay i32 per spec.
      | .i32 len :: .i32 src :: .i64 dst :: vs =>
        match st.dataSegments[i]? with
        | none => .Invalid s!"memoryInit: segment index {i} out of range"
        | some none =>
          if 0 < len.toNat ∨ dst.toNat + len.toNat > st.mem.pages * 65536 then
            .Trap st "out of bounds memory access"
          else
            .Fallthrough st { s with values := vs }
        | some (some segBytes) =>
          if src.toNat + len.toNat > segBytes.length
             ∨ dst.toNat + len.toNat > st.mem.pages * 65536 then
            .Trap st "out of bounds memory access"
          else
            let mem' := st.mem.writeBytesFrom dst.toNat segBytes src.toNat len.toNat
            .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "memoryInit: ill-shaped operand stack"

    -- data.drop i: mark segment `i` as no-longer-available. Idempotent
    -- (dropping an already-dropped segment is a no-op).
    | _, .dataDrop i =>
      match st.dataSegments[i]? with
      | none => .Invalid s!"dataDrop: segment index {i} out of range"
      | some _ =>
        let dataSegments' := st.dataSegments.set i none
        .Fallthrough { st with dataSegments := dataSegments' } s

    -- Multi-memory. Swap memory `k` (and its declaration) into the
    -- default slot, run the wrapped memory instruction, then swap the
    -- (possibly written) memory back into `extraMems`. The wrapped
    -- instruction never breaks/returns, so only `Fallthrough` and `Trap`
    -- carry a store to map back.
    | f + 1, .memOp k inner =>
      match st.extraMems[k - 1]?, m.extraMemories[k - 1]? with
      | some memK, some declK =>
        let stIn : Store α := { st with mem := memK }
        let mIn : Module := { m with memory := some declK }
        let restore (st' : Store α) : Store α :=
          { st' with mem := st.mem, extraMems := st.extraMems.set (k - 1) st'.mem }
        match execOne f mIn stIn s inner env with
        | .Fallthrough st' s' => .Fallthrough (restore st') s'
        | .Trap st' msg       => .Trap (restore st') msg
        | other               => other
      | _, _ => .Invalid s!"memOp: memory index {k} out of range"

    -- Cross-memory memory.copy (multi-memory). Each address operand is
    -- read by its runtime width (i32 or i64, per its memory's declared
    -- address type); bounds are checked in ℕ before any write.
    | _, .memoryCopyBetween dstMem srcMem => match s.values with
      | lenV :: srcV :: dstV :: vs =>
        match lenV.addrNat?, srcV.addrNat?, dstV.addrNat? with
        | some len, some src, some dst =>
          let memOf : Nat → Option Mem := fun k =>
            if k = 0 then some st.mem else st.extraMems[k - 1]?
          match memOf dstMem, memOf srcMem with
          | some dMem, some sMem =>
            if dst + len > dMem.pages * 65536 ∨ src + len > sMem.pages * 65536 then
              .Trap st "out of bounds memory access"
            else
              let dMem' := dMem.writeBytes dst (sMem.readBytes src len)
              let st' :=
                if dstMem = 0 then { st with mem := dMem' }
                else { st with extraMems := st.extraMems.set (dstMem - 1) dMem' }
              .Fallthrough st' { s with values := vs }
          | _, _ => .Invalid "memoryCopyBetween: memory index out of range"
        | _, _, _ => .Invalid "memoryCopyBetween: ill-shaped operand stack"
      | _ => .Invalid "memoryCopyBetween: ill-shaped operand stack"

    -- SIMD (v128). Lane semantics live in `Interpreter.Wasm.Simd`; the
    -- arms here only manage the operand stack and (for the memory
    -- variants) the usual Nat-domain bounds checks. A v128 occupies 16
    -- bytes in memory, lane 0 first (little-endian), so the two 64-bit
    -- halves are the low word at `a` and the high word at `a+8`.
    | _, .vConst bits => .Fallthrough st { s with values := .v128 bits :: s.values }
    | _, .vUnOp op => match s.values with
      | .v128 a :: vs => .Fallthrough st { s with values := .v128 (op.eval a) :: vs }
      | _ => .Invalid "vUnOp: ill-shaped operand stack"
    | _, .vBinOp op => match s.values with
      | .v128 b :: .v128 a :: vs =>
        .Fallthrough st { s with values := .v128 (op.eval a b) :: vs }
      | _ => .Invalid "vBinOp: ill-shaped operand stack"
    | _, .vBitselect => match s.values with
      | .v128 c :: .v128 b :: .v128 a :: vs =>
        .Fallthrough st { s with values := .v128 ((a &&& c) ||| (b &&& ~~~c)) :: vs }
      | _ => .Invalid "vBitselect: ill-shaped operand stack"
    | _, .vTestOp op => match s.values with
      | .v128 a :: vs => .Fallthrough st { s with values := .i32 (op.eval a) :: vs }
      | _ => .Invalid "vTestOp: ill-shaped operand stack"
    | _, .vShiftOp op => match s.values with
      | .i32 k :: .v128 a :: vs =>
        .Fallthrough st { s with values := .v128 (op.eval a k) :: vs }
      | _ => .Invalid "vShiftOp: ill-shaped operand stack"
    | _, .vSplat sh => match s.values with
      | v :: vs =>
        match v.scalarBitsFor? sh with
        | some x => .Fallthrough st { s with values := .v128 (Simd.splat sh x) :: vs }
        | none   => .Invalid "vSplat: ill-shaped operand stack"
      | _ => .Invalid "vSplat: ill-shaped operand stack"
    | _, .vExtractLane sh signed lane => match s.values with
      | .v128 a :: vs =>
        let n := Simd.getLane sh.laneBits lane a
        let v : Value := match sh with
          | .i8x16 => .i32 (if signed then UInt32.ofNat (Simd.toU 32 (Simd.sx 8 n))
                            else UInt32.ofNat n)
          | .i16x8 => .i32 (if signed then UInt32.ofNat (Simd.toU 32 (Simd.sx 16 n))
                            else UInt32.ofNat n)
          | .i32x4 => .i32 (UInt32.ofNat n)
          | .i64x2 => .i64 (UInt64.ofNat n)
          | .f32x4 => .f32 (UInt32.ofNat n)
          | .f64x2 => .f64 (UInt64.ofNat n)
        .Fallthrough st { s with values := v :: vs }
      | _ => .Invalid "vExtractLane: ill-shaped operand stack"
    | _, .vReplaceLane sh lane => match s.values with
      | v :: .v128 a :: vs =>
        match v.scalarBitsFor? sh with
        | some x =>
          .Fallthrough st
            { s with values := .v128 (Simd.setLane sh.laneBits lane a x) :: vs }
        | none => .Invalid "vReplaceLane: ill-shaped operand stack"
      | _ => .Invalid "vReplaceLane: ill-shaped operand stack"
    | _, .vShuffle idx => match s.values with
      | .v128 b :: .v128 a :: vs =>
        .Fallthrough st { s with values := .v128 (Simd.shuffle idx a b) :: vs }
      | _ => .Invalid "vShuffle: ill-shaped operand stack"
    | _, .v128Load off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 16 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let lo := st.mem.read64 (a + off)
          let hi := st.mem.read64 (a + off + 8)
          let bits := BitVec.ofNat 128 (lo.toNat + hi.toNat * 2 ^ 64)
          .Fallthrough st { s with values := .v128 bits :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 16 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let lo := st.mem.read64 (a.toUInt32 + off)
          let hi := st.mem.read64 (a.toUInt32 + off + 8)
          let bits := BitVec.ofNat 128 (lo.toNat + hi.toNat * 2 ^ 64)
          .Fallthrough st { s with values := .v128 bits :: vs }
      | _ => .Invalid "v128Load: ill-shaped operand stack"
    | _, .v128Store off => match s.values with
      | .v128 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 16 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let lo := UInt64.ofNat (v.toNat % 2 ^ 64)
          let hi := UInt64.ofNat (v.toNat / 2 ^ 64)
          let mem' := (st.mem.write64 (a + off) lo).write64 (a + off + 8) hi
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .v128 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + 16 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let lo := UInt64.ofNat (v.toNat % 2 ^ 64)
          let hi := UInt64.ofNat (v.toNat / 2 ^ 64)
          let mem' := (st.mem.write64 (a.toUInt32 + off) lo).write64 (a.toUInt32 + off + 8) hi
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "v128Store: ill-shaped operand stack"
    | _, .v128LoadExt srcBits signed off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let word := st.mem.read64 (a + off)
          let dstBits := srcBits * 2
          let cnt := 64 / srcBits
          let lanes := (List.range cnt).map fun i =>
            let n := (word.toNat >>> (i * srcBits)) % 2 ^ srcBits
            if signed then Simd.toU dstBits (Simd.sx srcBits n) else n
          .Fallthrough st { s with values := .v128 (Simd.ofLanes dstBits lanes) :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let word := st.mem.read64 (a.toUInt32 + off)
          let dstBits := srcBits * 2
          let cnt := 64 / srcBits
          let lanes := (List.range cnt).map fun i =>
            let n := (word.toNat >>> (i * srcBits)) % 2 ^ srcBits
            if signed then Simd.toU dstBits (Simd.sx srcBits n) else n
          .Fallthrough st { s with values := .v128 (Simd.ofLanes dstBits lanes) :: vs }
      | _ => .Invalid "v128LoadExt: ill-shaped operand stack"
    | _, .v128LoadSplat bits off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 8  => (st.mem.read8 (a + off)).toNat
            | 16 => (st.mem.read16 (a + off)).toNat
            | 32 => (st.mem.read32 (a + off)).toNat
            | _  => (st.mem.read64 (a + off)).toNat
          let lanes := List.replicate (128 / bits) n
          .Fallthrough st { s with values := .v128 (Simd.ofLanes bits lanes) :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 8  => (st.mem.read8 (a.toUInt32 + off)).toNat
            | 16 => (st.mem.read16 (a.toUInt32 + off)).toNat
            | 32 => (st.mem.read32 (a.toUInt32 + off)).toNat
            | _  => (st.mem.read64 (a.toUInt32 + off)).toNat
          let lanes := List.replicate (128 / bits) n
          .Fallthrough st { s with values := .v128 (Simd.ofLanes bits lanes) :: vs }
      | _ => .Invalid "v128LoadSplat: ill-shaped operand stack"
    | _, .v128LoadZero bits off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 32 => (st.mem.read32 (a + off)).toNat
            | _  => (st.mem.read64 (a + off)).toNat
          .Fallthrough st { s with values := .v128 (BitVec.ofNat 128 n) :: vs }
      | .i64 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 32 => (st.mem.read32 (a.toUInt32 + off)).toNat
            | _  => (st.mem.read64 (a.toUInt32 + off)).toNat
          .Fallthrough st { s with values := .v128 (BitVec.ofNat 128 n) :: vs }
      | _ => .Invalid "v128LoadZero: ill-shaped operand stack"
    | _, .v128LoadLane bits lane off => match s.values with
      | .v128 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 8  => (st.mem.read8 (a + off)).toNat
            | 16 => (st.mem.read16 (a + off)).toNat
            | 32 => (st.mem.read32 (a + off)).toNat
            | _  => (st.mem.read64 (a + off)).toNat
          .Fallthrough st { s with values := .v128 (Simd.setLane bits lane v n) :: vs }
      | .v128 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n : Nat := match bits with
            | 8  => (st.mem.read8 (a.toUInt32 + off)).toNat
            | 16 => (st.mem.read16 (a.toUInt32 + off)).toNat
            | 32 => (st.mem.read32 (a.toUInt32 + off)).toNat
            | _  => (st.mem.read64 (a.toUInt32 + off)).toNat
          .Fallthrough st { s with values := .v128 (Simd.setLane bits lane v n) :: vs }
      | _ => .Invalid "v128LoadLane: ill-shaped operand stack"
    | _, .v128StoreLane bits lane off => match s.values with
      | .v128 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n := Simd.getLane bits lane v
          let mem' := match bits with
            | 8  => st.mem.write8  (a + off) (UInt8.ofNat n)
            | 16 => st.mem.write16 (a + off) (UInt32.ofNat n)
            | 32 => st.mem.write32 (a + off) (UInt32.ofNat n)
            | _  => st.mem.write64 (a + off) (UInt64.ofNat n)
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | .v128 v :: .i64 a :: vs =>
        if a.toNat + off.toNat + bits / 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let n := Simd.getLane bits lane v
          let mem' := match bits with
            | 8  => st.mem.write8  (a.toUInt32 + off) (UInt8.ofNat n)
            | 16 => st.mem.write16 (a.toUInt32 + off) (UInt32.ofNat n)
            | 32 => st.mem.write32 (a.toUInt32 + off) (UInt32.ofNat n)
            | _  => st.mem.write64 (a.toUInt32 + off) (UInt64.ofNat n)
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "v128StoreLane: ill-shaped operand stack"

    -- Return / parametric / nullary
    | _, .ret  => .Return st s.values
    | _, .drop => match s.values with
      | _ :: vs => .Fallthrough st { s with values := vs }
      | _ => .Invalid "drop: empty operand stack"
    | _, .select => match s.values with
      | .i32 c :: v2 :: v1 :: vs =>
        let picked := if c ≠ 0 then v1 else v2
        .Fallthrough st { s with values := picked :: vs }
      | _ => .Invalid "select: ill-shaped operand stack"
    | _, .nop => .Fallthrough st s
    | _, .unreachable => .Trap st "unreachable"

    -- Reference instructions. Reference values are carried directly on
    -- the operand stack (`Value.funcref` / `Value.externref`), so these
    -- never touch the store: the null/func constructors just push a
    -- value, `refIsNull` inspects one.
    | _, .refNull       => .Fallthrough st { s with values := .funcref none :: s.values }
    | _, .refNullExtern => .Fallthrough st { s with values := .externref none :: s.values }
    | _, .refFunc fidx  => .Fallthrough st { s with values := .funcref (some fidx) :: s.values }
    | _, .refIsNull => match s.values with
      | .funcref r :: vs =>
        .Fallthrough st { s with values := .i32 (if r.isNone then 1 else 0) :: vs }
      | .externref r :: vs =>
        .Fallthrough st { s with values := .i32 (if r.isNone then 1 else 0) :: vs }
      | _ => .Invalid "refIsNull: ill-shaped operand stack"

    -- Table read instructions. Both look the runtime table up on the
    -- store; neither mutates it. An out-of-range *table* index is a
    -- validation error (`.Invalid`); an out-of-bounds *element* index is a
    -- genuine runtime trap, with the wasm spec's canonical wording so the
    -- testsuite's `assert_trap` text matcher accepts it.
    | _, .tableGet tableIdx => match s.values with
      | .i32 i :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableGet: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none   => .Trap st "out of bounds table access"
          | some r => .Fallthrough st { s with values := r :: vs }
      -- table64: the element index arrives as an i64.
      | .i64 i :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableGet: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none   => .Trap st "out of bounds table access"
          | some r => .Fallthrough st { s with values := r :: vs }
      | _ => .Invalid "tableGet: ill-shaped operand stack"
    | _, .tableSize tableIdx =>
      match st.tables[tableIdx]? with
      | none     => .Invalid s!"tableSize: table index {tableIdx} out of range"
      | some tbl =>
        -- The result type follows the declared table's address type
        -- (table64): i64 for a 64-bit table, i32 otherwise.
        .Fallthrough st
          { s with values := sizeValue (m.tableIs64 tableIdx) tbl.length :: s.values }

    -- table.set t: pops [val(ref), idx(i32)] (top = val).
    | _, .tableSet tableIdx => match s.values with
      | v :: .i32 i :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableSet: table index {tableIdx} out of range"
        | some tbl =>
          if i.toNat < tbl.length then
            let tables' := listSetAt st.tables tableIdx (listSetAt tbl i.toNat v)
            .Fallthrough { st with tables := tables' } { s with values := vs }
          else .Trap st "out of bounds table access"
      -- table64: the element index arrives as an i64.
      | v :: .i64 i :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableSet: table index {tableIdx} out of range"
        | some tbl =>
          if i.toNat < tbl.length then
            let tables' := listSetAt st.tables tableIdx (listSetAt tbl i.toNat v)
            .Fallthrough { st with tables := tables' } { s with values := vs }
          else .Trap st "out of bounds table access"
      | _ => .Invalid "tableSet: ill-shaped operand stack"

    -- table.grow t: pops [delta(i32), init(ref)] (top = delta). Pushes
    -- the old size on success, -1 on failure. Growth past the declared
    -- max (or the implementation ceiling, see `Module.tableCap`) fails.
    | _, .tableGrow tableIdx => match s.values with
      | .i32 delta :: init :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableGrow: table index {tableIdx} out of range"
        | some tbl =>
          let cur := tbl.length
          if cur + delta.toNat ≤ m.tableCap tableIdx then
            let tables' := listSetAt st.tables tableIdx
              (tbl ++ List.replicate delta.toNat init)
            .Fallthrough { st with tables := tables' }
              { s with values := .i32 (UInt32.ofNat cur) :: vs }
          else
            .Fallthrough st { s with values := .i32 (0xFFFFFFFF : UInt32) :: vs }
      -- table64: delta and result are i64.
      | .i64 delta :: init :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableGrow: table index {tableIdx} out of range"
        | some tbl =>
          let cur := tbl.length
          if cur + delta.toNat ≤ m.tableCap tableIdx then
            let tables' := listSetAt st.tables tableIdx
              (tbl ++ List.replicate delta.toNat init)
            .Fallthrough { st with tables := tables' }
              { s with values := .i64 (UInt64.ofNat cur) :: vs }
          else
            .Fallthrough st { s with values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: vs }
      | _ => .Invalid "tableGrow: ill-shaped operand stack"

    -- table.fill t: pops [len(i32), val(ref), dst(i32)] (top = len).
    -- Bounds are checked before any write, matching the spec's atomicity.
    | _, .tableFill tableIdx => match s.values with
      | .i32 len :: v :: .i32 dst :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableFill: table index {tableIdx} out of range"
        | some tbl =>
          if dst.toNat + len.toNat > tbl.length then
            .Trap st "out of bounds table access"
          else
            let tbl' := listWriteAt tbl dst.toNat (List.replicate len.toNat v)
            .Fallthrough { st with tables := listSetAt st.tables tableIdx tbl' }
              { s with values := vs }
      -- table64: dst and len are i64.
      | .i64 len :: v :: .i64 dst :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableFill: table index {tableIdx} out of range"
        | some tbl =>
          if dst.toNat + len.toNat > tbl.length then
            .Trap st "out of bounds table access"
          else
            let tbl' := listWriteAt tbl dst.toNat (List.replicate len.toNat v)
            .Fallthrough { st with tables := listSetAt st.tables tableIdx tbl' }
              { s with values := vs }
      | _ => .Invalid "tableFill: ill-shaped operand stack"

    -- table.copy d s: pops [len(i32), src(i32), dst(i32)] (top = len).
    -- The source slice is captured before the write, so overlapping
    -- ranges behave like memmove, as the spec requires.
    | _, .tableCopy dstIdx srcIdx => match s.values with
      | .i32 len :: .i32 src :: .i32 dst :: vs =>
        match st.tables[dstIdx]?, st.tables[srcIdx]? with
        | some dstTbl, some srcTbl =>
          if dst.toNat + len.toNat > dstTbl.length
             ∨ src.toNat + len.toNat > srcTbl.length then
            .Trap st "out of bounds table access"
          else
            let slice := (srcTbl.drop src.toNat).take len.toNat
            let dstTbl' := listWriteAt dstTbl dst.toNat slice
            .Fallthrough { st with tables := listSetAt st.tables dstIdx dstTbl' }
              { s with values := vs }
        | _, _ => .Invalid s!"tableCopy: table index out of range"
      -- table64: all three operands are i64.
      | .i64 len :: .i64 src :: .i64 dst :: vs =>
        match st.tables[dstIdx]?, st.tables[srcIdx]? with
        | some dstTbl, some srcTbl =>
          if dst.toNat + len.toNat > dstTbl.length
             ∨ src.toNat + len.toNat > srcTbl.length then
            .Trap st "out of bounds table access"
          else
            let slice := (srcTbl.drop src.toNat).take len.toNat
            let dstTbl' := listWriteAt dstTbl dst.toNat slice
            .Fallthrough { st with tables := listSetAt st.tables dstIdx dstTbl' }
              { s with values := vs }
        | _, _ => .Invalid s!"tableCopy: table index out of range"
      | _ => .Invalid "tableCopy: ill-shaped operand stack"

    -- table.init t e: pops [len(i32), src(i32), dst(i32)] (top = len).
    -- A dropped segment behaves as length 0; bounds are checked before
    -- any write.
    | _, .tableInit tableIdx elemIdx => match s.values with
      | .i32 len :: .i32 src :: .i32 dst :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableInit: table index {tableIdx} out of range"
        | some tbl =>
          match st.elementSegments[elemIdx]? with
          | none => .Invalid s!"tableInit: segment index {elemIdx} out of range"
          | some seg =>
            let segFuncs := seg.getD []
            if src.toNat + len.toNat > segFuncs.length
               ∨ dst.toNat + len.toNat > tbl.length then
              .Trap st "out of bounds table access"
            else
              let slice := ((segFuncs.drop src.toNat).take len.toNat).map Value.funcref
              let tbl' := listWriteAt tbl dst.toNat slice
              .Fallthrough { st with tables := listSetAt st.tables tableIdx tbl' }
                { s with values := vs }
      -- table64: dst takes the table's address type (i64); src and len
      -- index into the element segment and stay i32 per spec.
      | .i32 len :: .i32 src :: .i64 dst :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableInit: table index {tableIdx} out of range"
        | some tbl =>
          match st.elementSegments[elemIdx]? with
          | none => .Invalid s!"tableInit: segment index {elemIdx} out of range"
          | some seg =>
            let segFuncs := seg.getD []
            if src.toNat + len.toNat > segFuncs.length
               ∨ dst.toNat + len.toNat > tbl.length then
              .Trap st "out of bounds table access"
            else
              let slice := ((segFuncs.drop src.toNat).take len.toNat).map Value.funcref
              let tbl' := listWriteAt tbl dst.toNat slice
              .Fallthrough { st with tables := listSetAt st.tables tableIdx tbl' }
                { s with values := vs }
      | _ => .Invalid "tableInit: ill-shaped operand stack"

    -- elem.drop e: mark element segment `e` as dropped. Idempotent.
    | _, .elemDrop elemIdx =>
      match st.elementSegments[elemIdx]? with
      | none => .Invalid s!"elemDrop: segment index {elemIdx} out of range"
      | some _ =>
        .Fallthrough { st with elementSegments := st.elementSegments.set elemIdx none } s

def exec (fuel : Nat) (m : Module) (st : Store α) (s : Locals) (p : Program)
    (env : HostEnv α := {}) : Continuation α :=
  match p with
  | [] => .Fallthrough st s
  | inst :: rest => match execOne fuel m st s inst env with
    | Continuation.Fallthrough st s => exec fuel m st s rest env
    | other => other

def run (fuel : Nat) (m : Module) (id : Nat)
        (initial : Store α) (params : List Value) (env : HostEnv α := {}) : Result α :=
  -- Unified function index space: indices `< m.imports.length` resolve to
  -- host imports via `env.funcs`; the remainder map to `m.funcs` after
  -- shifting down by `m.imports.length`. Matching on `m.imports[id]?`
  -- (rather than computing the boolean) keeps the lemma surface clean:
  -- modules with `imports = []` reduce the host arm away by computation.
  match m.imports[id]? with
  | some imp =>
    match env.funcs[id]? with
    | none    => .Invalid s!"unresolved host function: index {id}"
    | some hf =>
      let callerRemainder := params.drop imp.params.length
      -- Same calling convention as the wasm path: params reversed so the
      -- host receives the first declared param first.
      let hostArgs := (params.take imp.params.length).reverse
      match hf.invoke initial hostArgs with
      | .Return vs st' =>
        .Success (vs.take imp.results.length ++ callerRemainder) st'
      | .Trap st' msg  => .Trap st' msg
  | none =>
    match m.funcs[id - m.imports.length]? with
    | some f =>
      -- Standard Wasm calling convention. Params are reversed so local 0
      -- is the first (deepest) argument; only the top `f.results.length`
      -- values are returned to the caller; remaining caller args pass
      -- through unchanged.
      let callerRemainder := params.drop f.numParams
      match exec fuel m initial (f.toLocals (params.take f.numParams).reverse) f.body env with
      | Continuation.Fallthrough st s => .Success (s.values.take f.results.length ++ callerRemainder) st
      | Continuation.Return st vs     => .Success (vs.take f.results.length ++ callerRemainder) st
      | Continuation.Break 0 st s     => .Success (s.values.take f.results.length ++ callerRemainder) st
      | Continuation.Break (_+1) _ _  => .Invalid "Unexpected break targeting scope out of function"
      | Continuation.Invalid msg      => .Invalid msg
      | Continuation.OutOfFuel        => .OutOfFuel
      | Continuation.Trap st msg      => .Trap st msg
      -- Tail call: the callee replaces this frame. Validation guarantees
      -- the callee's result types equal `f.results`, so truncating its
      -- results to `f.results.length` and restoring this frame's
      -- caller-remainder preserves the standard calling convention.
      | Continuation.ReturnCall id' st' vs =>
        match runTail fuel m id' st' vs env with
        | .Success vs2 st2 => .Success (vs2.take f.results.length ++ callerRemainder) st2
        | other => other
    | none => .Invalid "Function index out of bounds"

/-- Resolve a pending tail call: re-dispatch with one less fuel. Kept as
its own (mutual) definition so `run`'s equation lemma does not mention
`run` itself — `simp only [run]` unfolds one frame and stops at
`runTail`, exactly like the pre-tail-call unfolding discipline. -/
def runTail (fuel : Nat) (m : Module) (id : Nat)
    (st : Store α) (vs : List Value) (env : HostEnv α := {}) : Result α :=
  match fuel with
  | 0 => .OutOfFuel
  | f' + 1 => run f' m id st vs env

end

end Wasm
