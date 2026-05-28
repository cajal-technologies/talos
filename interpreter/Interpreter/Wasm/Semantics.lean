import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Locals
import Interpreter.Wasm.Continuation

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

def execOne (fuel : Nat) (m : Module) (st : Store) (s : Locals) (inst : Instruction) : Continuation :=
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
      match exec f m st s body with
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
      match exec f m st s body with
      | .Fallthrough r' s' =>
        .Fallthrough r' { s' with values := s'.values.take resultArity ++ belowStack }
      | .Break 0 r' s' =>
        -- `br 0` to a loop = restart from the top. Reset the stack to
        -- the kept top values (the loop's next-iteration params) atop
        -- the entry's below-stack, then re-execute the loop.
        execOne f m r' { s' with values := s'.values.take paramArity ++ belowStack } inst
      | .Break (k + 1) r' s' => .Break k r' s'
      | other => other
    | f + 1, .iff paramArity resultArity thn els => match s.values with
      | .i32 c :: vs =>
        let belowStack := vs.drop paramArity
        let s' : Locals := { s with values := vs }
        let body := if c ≠ 0 then thn else els
        match exec f m st s' body with
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
    | f + 1, .call id => match run f m id st s.values with
      | .Success vs st' => .Fallthrough st' { s with values := vs }
      | .Trap st' msg   => .Trap st' msg
      | .Invalid msg    => .Invalid msg
      | .OutOfFuel      => .OutOfFuel

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

def exec (fuel : Nat) (m : Module) (st : Store) (s : Locals) (p : Program) : Continuation :=
  match p with
  | [] => .Fallthrough st s
  | inst :: rest => match execOne fuel m st s inst with
    | Continuation.Fallthrough st s => exec fuel m st s rest
    | other => other

def run (fuel : Nat) (m : Module) (id : Nat)
        (initial : Store) (params : List Value) : Result :=
  match m.funcs[id]? with
  | some f =>
    -- Standard Wasm calling convention. Params are reversed so local 0
    -- is the first (deepest) argument; only the top `f.results.length`
    -- values are returned to the caller; remaining caller args pass
    -- through unchanged.
    let callerRemainder := params.drop f.numParams
    match exec fuel m initial (f.toLocals (params.take f.numParams).reverse) f.body with
    | Continuation.Fallthrough st s => .Success (s.values.take f.results.length ++ callerRemainder) st
    | Continuation.Return st vs     => .Success (vs.take f.results.length ++ callerRemainder) st
    | Continuation.Break _ st _     => .Trap st "Unexpected break targeting function"
    | Continuation.Invalid msg      => .Invalid msg
    | Continuation.OutOfFuel        => .OutOfFuel
    | Continuation.Trap st msg      => .Trap st msg
  | none => .Invalid "Function index out of bounds"

end

end Wasm
