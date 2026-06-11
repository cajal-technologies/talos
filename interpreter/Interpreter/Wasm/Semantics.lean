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
      | _ => .Invalid "f32Load: ill-shaped operand stack"
    | _, .f64Load off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough st { s with values := .f64 (st.mem.read64 (a + off)) :: vs }
      | _ => .Invalid "f64Load: ill-shaped operand stack"
    | _, .f32Store off => match s.values with
      | .f32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough { st with mem := st.mem.write32 (a + off) v } { s with values := vs }
      | _ => .Invalid "f32Store: ill-shaped operand stack"
    | _, .f64Store off => match s.values with
      | .f64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          .Fallthrough { st with mem := st.mem.write64 (a + off) v } { s with values := vs }
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
          | none           => .Trap st "undefined element"
          | some none      => .Trap st "uninitialized element"
          | some (some fid) =>
            match m.funcs[fid]? with
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
      | _ => .Invalid "load8U: ill-shaped operand stack"
    | _, .load8S off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (Int32.ofInt (signExtend (st.mem.read8 (a + off)).toNat 8)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load8S: ill-shaped operand stack"
    | _, .load16U off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read16 (a + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load16U: ill-shaped operand stack"
    | _, .load16S off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt32 := (Int32.ofInt (signExtend (st.mem.read16 (a + off)).toNat 16)).toUInt32
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load16S: ill-shaped operand stack"
    | _, .load32 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read32 (a + off)
          .Fallthrough st { s with values := .i32 v :: vs }
      | _ => .Invalid "load32: ill-shaped operand stack"
    | _, .store8 off => match s.values with
      | .i32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write8 (a + off) v.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store8: ill-shaped operand stack"
    | _, .store16 off => match s.values with
      | .i32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write16 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store16: ill-shaped operand stack"
    | _, .store32 off => match s.values with
      | .i32 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store32: ill-shaped operand stack"
    | _, .load64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v := st.mem.read64 (a + off)
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load64: ill-shaped operand stack"
    | _, .store64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write64 (a + off) v
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store64: ill-shaped operand stack"

    | _, .load8UI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read8 (a + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load8UI64: ill-shaped operand stack"
    | _, .load8SI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read8 (a + off)).toNat 8)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load8SI64: ill-shaped operand stack"
    | _, .load16UI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read16 (a + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load16UI64: ill-shaped operand stack"
    | _, .load16SI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read16 (a + off)).toNat 16)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load16SI64: ill-shaped operand stack"
    | _, .load32UI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (st.mem.read32 (a + off)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load32UI64: ill-shaped operand stack"
    | _, .load32SI64 off => match s.values with
      | .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let v : UInt64 := (Int64.ofInt (signExtend (st.mem.read32 (a + off)).toNat 32)).toUInt64
          .Fallthrough st { s with values := .i64 v :: vs }
      | _ => .Invalid "load32SI64: ill-shaped operand stack"
    | _, .store8I64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write8 (a + off) v.toUInt8
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store8I64: ill-shaped operand stack"
    | _, .store16I64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write16 (a + off) v.toUInt32
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store16I64: ill-shaped operand stack"
    | _, .store32I64 off => match s.values with
      | .i64 v :: .i32 a :: vs =>
        if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
          .Trap st "out of bounds memory access"
        else
          let mem' := st.mem.write32 (a + off) v.toUInt32
          .Fallthrough { st with mem := mem' } { s with values := vs }
      | _ => .Invalid "store32I64: ill-shaped operand stack"

    -- Memory size / grow. `memory.grow`'s cap is computed once via
    -- `Module.memoryCap` so the semantics and the corresponding wp
    -- lemma share a single matchable shape.
    | _, .memorySize =>
      let v : UInt32 := st.mem.pages.toUInt32
      .Fallthrough st { s with values := .i32 v :: s.values }
    | _, .memoryGrow => match s.values with
      | .i32 delta :: vs =>
        match st.mem.grow delta m.memoryCap with
        | some (mem', cur) =>
          .Fallthrough { st with mem := mem' }
            { s with values := .i32 cur.toUInt32 :: vs }
        | none =>
          .Fallthrough st { s with values := .i32 (0xFFFFFFFF : UInt32) :: vs }
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
      | _ => .Invalid "memoryInit: ill-shaped operand stack"

    -- data.drop i: mark segment `i` as no-longer-available. Idempotent
    -- (dropping an already-dropped segment is a no-op).
    | _, .dataDrop i =>
      match st.dataSegments[i]? with
      | none => .Invalid s!"dataDrop: segment index {i} out of range"
      | some _ =>
        let dataSegments' := st.dataSegments.set i none
        .Fallthrough { st with dataSegments := dataSegments' } s

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

    -- Reference instructions. `funcref` values reuse the existing
    -- `Value.funcref (Option Nat)` representation, so these never touch the
    -- store: `refNull`/`refFunc` just push a value, `refIsNull` inspects one.
    | _, .refNull      => .Fallthrough st { s with values := .funcref none :: s.values }
    | _, .refFunc fidx => .Fallthrough st { s with values := .funcref (some fidx) :: s.values }
    | _, .refIsNull => match s.values with
      | .funcref r :: vs =>
        .Fallthrough st { s with values := .i32 (if r.isNone then 1 else 0) :: vs }
      | _ => .Invalid "refIsNull: ill-shaped operand stack"

    -- Table instructions. An out-of-range *table* index is a validation
    -- error (`.Invalid`); an out-of-bounds *element* index is a genuine
    -- runtime trap, with the wasm spec's canonical wording so the
    -- testsuite's `assert_trap` text matcher accepts it.
    | _, .tableGet tableIdx => match s.values with
      | .i32 i :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableGet: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none   => .Trap st "out of bounds table access"
          | some r => .Fallthrough st { s with values := .funcref r :: vs }
      | _ => .Invalid "tableGet: ill-shaped operand stack"
    | _, .tableSize tableIdx =>
      match st.tables[tableIdx]? with
      | none     => .Invalid s!"tableSize: table index {tableIdx} out of range"
      | some tbl =>
        .Fallthrough st { s with values := .i32 (UInt32.ofNat tbl.length) :: s.values }
    | _, .tableSet tableIdx => match s.values with
      | .funcref r :: .i32 i :: vs =>
        match st.tables[tableIdx]? with
        | none     => .Invalid s!"tableSet: table index {tableIdx} out of range"
        | some tbl =>
          match tbl[i.toNat]? with
          | none   => .Trap st "out of bounds table access"
          | some _ =>
            let tbl' := tbl.set i.toNat r
            .Fallthrough { st with tables := st.tables.set tableIdx tbl' }
                         { s with values := vs }
      | _ => .Invalid "tableSet: ill-shaped operand stack"
    | _, .tableGrow tableIdx => match s.values with
      | .i32 delta :: .funcref r :: vs =>
        match st.tables[tableIdx]? with
        | none => .Invalid s!"tableGrow: table index {tableIdx} out of range"
        | some tbl =>
          match m.tables[tableIdx]? >>= (·.max) with
          | none =>
            .Fallthrough { st with tables := st.tables.set tableIdx (tbl ++ List.replicate delta.toNat r) }
                         { s with values := .i32 (UInt32.ofNat tbl.length) :: vs }
          | some n =>
            if tbl.length + delta.toNat ≤ n then
              .Fallthrough { st with tables := st.tables.set tableIdx (tbl ++ List.replicate delta.toNat r) }
                           { s with values := .i32 (UInt32.ofNat tbl.length) :: vs }
            else
              .Fallthrough st { s with values := .i32 (0xFFFFFFFF : UInt32) :: vs }
      | _ => .Invalid "tableGrow: ill-shaped operand stack"
    | _, .tableFill tableIdx => match s.values with
      | .i32 len :: .funcref val :: .i32 idx :: vs =>
        match st.tables[tableIdx]? with
        | none => .Invalid s!"tableFill: table index {tableIdx} out of range"
        | some tbl =>
          if idx.toNat + len.toNat > tbl.length then
            .Trap st "out of bounds table access"
          else
            let tbl' := tbl.take idx.toNat ++ List.replicate len.toNat val ++ tbl.drop (idx.toNat + len.toNat)
            .Fallthrough { st with tables := st.tables.set tableIdx tbl' }
                         { s with values := vs }
      | _ => .Invalid "tableFill: ill-shaped operand stack"
    -- table.copy dst src: pops i32 len (top), i32 src_offset, i32 dst_offset.
    -- Reads from srcTable[src..src+len) and writes to dstTable[dst..dst+len).
    -- Trap is checked atomically before any write.  Same-table overlap is
    -- handled correctly because srcSlice is extracted from the original table.
    | _, .tableCopy dstTableIdx srcTableIdx => match s.values with
      | .i32 len :: .i32 src :: .i32 dst :: vs =>
        match st.tables[dstTableIdx]? with
        | none => .Invalid s!"tableCopy: dst table index {dstTableIdx} out of range"
        | some dstTbl =>
          match st.tables[srcTableIdx]? with
          | none => .Invalid s!"tableCopy: src table index {srcTableIdx} out of range"
          | some srcTbl =>
            if dst.toNat + len.toNat > dstTbl.length ∨ src.toNat + len.toNat > srcTbl.length then
              .Trap st "out of bounds table access"
            else
              let srcSlice := (srcTbl.drop src.toNat).take len.toNat
              let dstTbl' := dstTbl.take dst.toNat ++ srcSlice ++ dstTbl.drop (dst.toNat + len.toNat)
              .Fallthrough { st with tables := st.tables.set dstTableIdx dstTbl' }
                           { s with values := vs }
      | _ => .Invalid "tableCopy: ill-shaped operand stack"

    | _, .tableInit tableIdx segIdx => match s.values with
      | .i32 len :: .i32 src :: .i32 dst :: vs =>
        match st.tables[tableIdx]? with
        | none => .Invalid s!"tableInit: table index {tableIdx} out of range"
        | some dstTbl =>
          match st.elementSegments[segIdx]? with
          | none => .Invalid s!"tableInit: segment index {segIdx} out of range"
          | some none =>
            if 0 < len.toNat ∨ dst.toNat + len.toNat > dstTbl.length then
              .Trap st "out of bounds table access"
            else
              .Fallthrough st { s with values := vs }
          | some (some funcs) =>
            if src.toNat + len.toNat > funcs.length
               ∨ dst.toNat + len.toNat > dstTbl.length then
              .Trap st "out of bounds table access"
            else
              let srcSlice := (funcs.drop src.toNat).take len.toNat
              let dstTbl' := dstTbl.take dst.toNat ++ srcSlice ++ dstTbl.drop (dst.toNat + len.toNat)
              .Fallthrough { st with tables := st.tables.set tableIdx dstTbl' }
                           { s with values := vs }
      | _ => .Invalid "tableInit: ill-shaped operand stack"
    | _, .elemDrop i =>
      match st.elementSegments[i]? with
      | none => .Invalid s!"elemDrop: segment index {i} out of range"
      | some _ =>
        let elementSegments' := st.elementSegments.set i none
        .Fallthrough { st with elementSegments := elementSegments' } s

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
    | none => .Invalid "Function index out of bounds"

end

end Wasm
