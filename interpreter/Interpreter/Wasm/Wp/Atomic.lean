import Interpreter.Wasm.Wp.Defs

/-! ### Atomic equations.

    `@[simp]` rewrite rules: when the head of the program matches a constructor,
    `wp` reduces structurally. Stack-consuming instructions reveal a
    `match s.values with ...` that `simp` reduces whenever the stack shape is
    concrete.

    Each lemma is discharged by the `wp_atomic` macro defined below, which
    unfolds `wp`, `exec`, and `execOne` and splits on the relevant `match`/`if`
    structure of the instruction. -/

namespace Wasm

/-- Solve a `wp` atomic-instruction goal whose RHS may contain `match`/`if`
    splits. Repeatedly opens splits and discharges the remaining leaves with
    the `exec`-unfolding helpers from `Defs.lean`. -/
macro "wp_atomic" : tactic => `(tactic|
  (repeat' (first
    | (apply wp_of_exec_eq_succ; intro fuel; simp_all [exec, execOne])
    | (apply wp_of_exec_const_succ; intro fuel; simp_all [exec, execOne])
    | split)
   all_goals try grind))

@[simp, wp_simp] theorem wp_nil : wp m [] Q st s env ↔ Q (.Fallthrough st s) := by
  wp_atomic

/-! ## Locals / constants -/

@[simp, wp_simp] theorem wp_localGet_cons :
    wp m (.localGet i :: rest) Q st s env ↔
    (match s.get i with
     | some v => wp m rest Q st { s with values := v :: s.values } env
     | none   => Q (.Invalid "localGet index out of bounds")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_localSet_cons :
    wp m (.localSet i :: rest) Q st s env ↔
    (match s.values with
     | v :: vs =>
        (match s.set? i v with
         | some s' => wp m rest Q st { s' with values := vs } env
         | none    => Q (.Invalid "localSet index out of bounds"))
     | _ => Q (.Invalid "localSet with empty stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_const_cons :
    wp m (.const v :: rest) Q st s env ↔
    wp m rest Q st { s with values := .i32 v :: s.values } env := by
  wp_atomic

@[simp, wp_simp] theorem wp_constI64_cons :
    wp m (.constI64 v :: rest) Q st s env ↔
    wp m rest Q st { s with values := .i64 v :: s.values } env := by
  wp_atomic

/-! ## i32 arithmetic -/

@[simp, wp_simp] theorem wp_add_cons :
    wp m (.add :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: .i32 b :: vs => wp m rest Q st { s with values := .i32 (a + b) :: vs } env
     | _ => Q (.Invalid "add: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_sub_cons :
    wp m (.sub :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: .i32 b :: vs => wp m rest Q st { s with values := .i32 (b - a) :: vs } env
     | _ => Q (.Invalid "sub: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_mul_cons :
    wp m (.mul :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: .i32 b :: vs => wp m rest Q st { s with values := .i32 (a * b) :: vs } env
     | _ => Q (.Invalid "mul: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_divU_cons :
    wp m (.divU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wp m rest Q st { s with values := .i32 (a / b) :: vs } env
     | _ => Q (.Invalid "divU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_divS_cons :
    wp m (.divS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else if a = 0x80000000 ∧ b = 0xFFFFFFFF then Q (.Trap st "integer overflow")
       else wp m rest Q st
         { s with values := .i32 ((Int32.ofInt (Int.tdiv a.toInt32.toInt b.toInt32.toInt)).toUInt32) :: vs } env
     | _ => Q (.Invalid "divS: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_remU_cons :
    wp m (.remU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wp m rest Q st { s with values := .i32 (a % b) :: vs } env
     | _ => Q (.Invalid "remU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_remS_cons :
    wp m (.remS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wp m rest Q st
         { s with values := .i32 ((Int32.ofInt (Int.tmod a.toInt32.toInt b.toInt32.toInt)).toUInt32) :: vs } env
     | _ => Q (.Invalid "remS: ill-shaped operand stack")) := by
  wp_atomic

/-! ## i32 comparison -/

@[simp, wp_simp] theorem wp_eqz_cons :
    wp m (.eqz :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a = 0 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "eqz: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_eq_cons :
    wp m (.eq :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a = b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "eq: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ne_cons :
    wp m (.ne :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a ≠ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "ne: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ltU_cons :
    wp m (.ltU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a < b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "ltU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ltS_cons :
    wp m (.ltS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt32 < b.toInt32 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "ltS: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_gtU_cons :
    wp m (.gtU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a > b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "gtU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_gtS_cons :
    wp m (.gtS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt32 > b.toInt32 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "gtS: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_leU_cons :
    wp m (.leU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a ≤ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "leU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_leS_cons :
    wp m (.leS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt32 ≤ b.toInt32 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "leS: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_geU_cons :
    wp m (.geU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (if a ≥ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "geU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_geS_cons :
    wp m (.geS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt32 ≥ b.toInt32 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "geS: ill-shaped operand stack")) := by
  wp_atomic

/-! ## i32 bitwise / shift / counting -/

@[simp, wp_simp] theorem wp_and_cons :
    wp m (.and :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: .i32 b :: vs => wp m rest Q st { s with values := .i32 (a &&& b) :: vs } env
     | _ => Q (.Invalid "and: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_or_cons :
    wp m (.or :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (a ||| b) :: vs } env
     | _ => Q (.Invalid "or: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_xor_cons :
    wp m (.xor :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (a ^^^ b) :: vs } env
     | _ => Q (.Invalid "xor: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_shl_cons :
    wp m (.shl :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (a <<< (b % 32)) :: vs } env
     | _ => Q (.Invalid "shl: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_shrU_cons :
    wp m (.shrU :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st { s with values := .i32 (a >>> (b % 32)) :: vs } env
     | _ => Q (.Invalid "shrU: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_shrS_cons :
    wp m (.shrS :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs => wp m rest Q st
         { s with values := .i32 (UInt32.ofNat (BitVec.sshiftRight a.toBitVec (b % 32).toNat).toNat) :: vs } env
     | _ => Q (.Invalid "shrS: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_rotl_cons :
    wp m (.rotl :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       let k := b % 32
       wp m rest Q st
         { s with values := .i32 (if k = 0 then a else (a <<< k) ||| (a >>> (32 - k))) :: vs } env
     | _ => Q (.Invalid "rotl: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_rotr_cons :
    wp m (.rotr :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: .i32 a :: vs =>
       let k := b % 32
       wp m rest Q st
         { s with values := .i32 (if k = 0 then a else (a >>> k) ||| (a <<< (32 - k))) :: vs } env
     | _ => Q (.Invalid "rotr: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_clz_cons :
    wp m (.clz :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st { s with values := .i32 (UInt32.ofNat (clz32 32 a)) :: vs } env
     | _ => Q (.Invalid "clz: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ctz_cons :
    wp m (.ctz :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st { s with values := .i32 (UInt32.ofNat (ctz32 32 a)) :: vs } env
     | _ => Q (.Invalid "ctz: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_popcnt_cons :
    wp m (.popcnt :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st { s with values := .i32 (UInt32.ofNat (popcnt32 32 a 0)) :: vs } env
     | _ => Q (.Invalid "popcnt: ill-shaped operand stack")) := by
  wp_atomic

/-! ## i64 arithmetic -/

@[simp, wp_simp] theorem wp_addI64_cons :
    wp m (.addI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i64 (a + b) :: vs } env
     | _ => Q (.Invalid "addI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_subI64_cons :
    wp m (.subI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i64 (a - b) :: vs } env
     | _ => Q (.Invalid "subI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_mulI64_cons :
    wp m (.mulI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i64 (a * b) :: vs } env
     | _ => Q (.Invalid "mulI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_divUI64_cons :
    wp m (.divUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wp m rest Q st { s with values := .i64 (a / b) :: vs } env
     | _ => Q (.Invalid "divUI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_divSI64_cons :
    wp m (.divSI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else if a = 0x8000000000000000 ∧ b = 0xFFFFFFFFFFFFFFFF then Q (.Trap st "integer overflow")
       else wp m rest Q st
         { s with values := .i64 ((Int64.ofInt (Int.tdiv a.toInt64.toInt b.toInt64.toInt)).toUInt64) :: vs } env
     | _ => Q (.Invalid "divSI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_remUI64_cons :
    wp m (.remUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wp m rest Q st { s with values := .i64 (a % b) :: vs } env
     | _ => Q (.Invalid "remUI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_remSI64_cons :
    wp m (.remSI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs =>
       if b = 0 then Q (.Trap st "integer divide by zero")
       else wp m rest Q st
         { s with values := .i64 ((Int64.ofInt (Int.tmod a.toInt64.toInt b.toInt64.toInt)).toUInt64) :: vs } env
     | _ => Q (.Invalid "remSI64: ill-shaped operand stack")) := by
  wp_atomic

/-! ## i64 comparison (results land as i32 0/1) -/

@[simp, wp_simp] theorem wp_eqzI64_cons :
    wp m (.eqzI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st { s with values := .i32 (if a = 0 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "eqzI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_eqI64_cons :
    wp m (.eqI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i32 (if a = b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "eqI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_neI64_cons :
    wp m (.neI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i32 (if a ≠ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "neI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ltUI64_cons :
    wp m (.ltUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i32 (if a < b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "ltUI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ltSI64_cons :
    wp m (.ltSI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt64 < b.toInt64 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "ltSI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_gtUI64_cons :
    wp m (.gtUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i32 (if a > b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "gtUI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_gtSI64_cons :
    wp m (.gtSI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt64 > b.toInt64 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "gtSI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_leUI64_cons :
    wp m (.leUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i32 (if a ≤ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "leUI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_leSI64_cons :
    wp m (.leSI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt64 ≤ b.toInt64 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "leSI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_geUI64_cons :
    wp m (.geUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i32 (if a ≥ b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "geUI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_geSI64_cons :
    wp m (.geSI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st
         { s with values := .i32 (if a.toInt64 ≥ b.toInt64 then 1 else 0) :: vs } env
     | _ => Q (.Invalid "geSI64: ill-shaped operand stack")) := by
  wp_atomic

/-! ## i64 bitwise / shift / counting -/

@[simp, wp_simp] theorem wp_andI64_cons :
    wp m (.andI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i64 (a &&& b) :: vs } env
     | _ => Q (.Invalid "andI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_orI64_cons :
    wp m (.orI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i64 (a ||| b) :: vs } env
     | _ => Q (.Invalid "orI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_xorI64_cons :
    wp m (.xorI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i64 (a ^^^ b) :: vs } env
     | _ => Q (.Invalid "xorI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_shlI64_cons :
    wp m (.shlI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i64 (a <<< (b % 64)) :: vs } env
     | _ => Q (.Invalid "shlI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_shrUI64_cons :
    wp m (.shrUI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st { s with values := .i64 (a >>> (b % 64)) :: vs } env
     | _ => Q (.Invalid "shrUI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_shrSI64_cons :
    wp m (.shrSI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs => wp m rest Q st
         { s with values := .i64 (UInt64.ofNat (BitVec.sshiftRight a.toBitVec (b % 64).toNat).toNat) :: vs } env
     | _ => Q (.Invalid "shrSI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_rotlI64_cons :
    wp m (.rotlI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs =>
       let k := b % 64
       wp m rest Q st
         { s with values := .i64 (if k = 0 then a else (a <<< k) ||| (a >>> (64 - k))) :: vs } env
     | _ => Q (.Invalid "rotlI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_rotrI64_cons :
    wp m (.rotrI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: .i64 a :: vs =>
       let k := b % 64
       wp m rest Q st
         { s with values := .i64 (if k = 0 then a else (a >>> k) ||| (a <<< (64 - k))) :: vs } env
     | _ => Q (.Invalid "rotrI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_clzI64_cons :
    wp m (.clzI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st { s with values := .i64 (UInt64.ofNat (clz64 64 a)) :: vs } env
     | _ => Q (.Invalid "clzI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ctzI64_cons :
    wp m (.ctzI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st { s with values := .i64 (UInt64.ofNat (ctz64 64 a)) :: vs } env
     | _ => Q (.Invalid "ctzI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_popcntI64_cons :
    wp m (.popcntI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st { s with values := .i64 (UInt64.ofNat (popcnt64 64 a 0)) :: vs } env
     | _ => Q (.Invalid "popcntI64: ill-shaped operand stack")) := by
  wp_atomic

/-! ## Conversions / sign-extension -/

@[simp, wp_simp] theorem wp_wrapI64_cons :
    wp m (.wrapI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st { s with values := .i32 (UInt32.ofNat (a.toNat % 2 ^ 32)) :: vs } env
     | _ => Q (.Invalid "wrapI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_extendUI32_cons :
    wp m (.extendUI32 :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st { s with values := .i64 (UInt64.ofNat a.toNat) :: vs } env
     | _ => Q (.Invalid "extendUI32: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_extendSI32_cons :
    wp m (.extendSI32 :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st
         { s with values := .i64 ((Int64.ofInt a.toInt32.toInt).toUInt64) :: vs } env
     | _ => Q (.Invalid "extendSI32: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_extend8S_cons :
    wp m (.extend8S :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st
         { s with values := .i32 ((Int32.ofInt (signExtend (a.toNat % 256) 8)).toUInt32) :: vs } env
     | _ => Q (.Invalid "extend8S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_extend16S_cons :
    wp m (.extend16S :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st
         { s with values := .i32 ((Int32.ofInt (signExtend (a.toNat % 65536) 16)).toUInt32) :: vs } env
     | _ => Q (.Invalid "extend16S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_extend8SI64_cons :
    wp m (.extend8SI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st
         { s with values := .i64 ((Int64.ofInt (signExtend (a.toNat % 256) 8)).toUInt64) :: vs } env
     | _ => Q (.Invalid "extend8SI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_extend16SI64_cons :
    wp m (.extend16SI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st
         { s with values := .i64 ((Int64.ofInt (signExtend (a.toNat % 65536) 16)).toUInt64) :: vs } env
     | _ => Q (.Invalid "extend16SI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_extend32SI64_cons :
    wp m (.extend32SI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st
         { s with values := .i64 ((Int64.ofInt (signExtend (a.toNat % 2 ^ 32) 32)).toUInt64) :: vs } env
     | _ => Q (.Invalid "extend32SI64: ill-shaped operand stack")) := by
  wp_atomic

/-! ## Branching / parametric / nullary -/

@[simp, wp_simp] theorem wp_br_cons : wp m (.br n :: rest) Q st s env ↔ Q (.Break n st s) := by
  wp_atomic

@[simp, wp_simp] theorem wp_br_if_cons :
    wp m (.br_if n :: rest) Q st s env ↔
    (match s.values with
     | .i32 0 :: vs => wp m rest Q st { s with values := vs } env
     | .i32 _ :: vs => Q (.Break n st { s with values := vs })
     | _ => Q (.Invalid "br_if: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_brTable_cons :
    wp m (.brTable targets dflt :: rest) Q st s env ↔
    (match s.values with
     | .i32 i :: vs =>
       let n := i.toNat
       let lbl := if h : n < targets.length then targets[n] else dflt
       Q (.Break lbl st { s with values := vs })
     | _ => Q (.Invalid "brTable: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_ret_cons : wp m (.ret :: rest) Q st s env ↔ Q (.Return st s.values) := by
  wp_atomic

@[simp, wp_simp] theorem wp_drop_cons :
    wp m (.drop :: rest) Q st s env ↔
    (match s.values with
     | _ :: vs => wp m rest Q st { s with values := vs } env
     | _ => Q (.Invalid "drop: empty operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_select_cons :
    wp m (.select :: rest) Q st s env ↔
    (match s.values with
     | .i32 c :: v2 :: v1 :: vs =>
       wp m rest Q st { s with values := (if c ≠ 0 then v1 else v2) :: vs } env
     | _ => Q (.Invalid "select: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_nop_cons : wp m (.nop :: rest) Q st s env ↔ wp m rest Q st s env := by
  wp_atomic

@[simp, wp_simp] theorem wp_unreachable_cons :
    wp m (.unreachable :: rest) Q st s env ↔ Q (.Trap st "unreachable") := by
  wp_atomic

/-! ## Reference instructions -/

@[simp, wp_simp] theorem wp_refNull_cons :
    wp m (.refNull :: rest) Q st s env ↔
    wp m rest Q st { s with values := .funcref none :: s.values } env := by
  wp_atomic

@[simp, wp_simp] theorem wp_refFunc_cons :
    wp m (.refFunc fidx :: rest) Q st s env ↔
    wp m rest Q st { s with values := .funcref (some fidx) :: s.values } env := by
  wp_atomic

@[simp, wp_simp] theorem wp_refIsNull_cons :
    wp m (.refIsNull :: rest) Q st s env ↔
    (match s.values with
     | .funcref r :: vs =>
       wp m rest Q st { s with values := .i32 (if r.isNone then 1 else 0) :: vs } env
     | _ => Q (.Invalid "refIsNull: ill-shaped operand stack")) := by
  wp_atomic

/-! ## Table instructions -/

@[simp, wp_simp] theorem wp_tableGet_cons :
    wp m (.tableGet tableIdx :: rest) Q st s env ↔
    (match s.values with
     | .i32 i :: vs =>
       (match st.tables[tableIdx]? with
        | none     => Q (.Invalid s!"tableGet: table index {tableIdx} out of range")
        | some tbl =>
          (match tbl[i.toNat]? with
           | none   => Q (.Trap st "out of bounds table access")
           | some r => wp m rest Q st { s with values := .funcref r :: vs } env))
     | _ => Q (.Invalid "tableGet: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_tableSize_cons :
    wp m (.tableSize tableIdx :: rest) Q st s env ↔
    (match st.tables[tableIdx]? with
     | none     => Q (.Invalid s!"tableSize: table index {tableIdx} out of range")
     | some tbl =>
       wp m rest Q st { s with values := .i32 (UInt32.ofNat tbl.length) :: s.values } env) := by
  wp_atomic

/-! ## Globals -/

@[simp, wp_simp] theorem wp_globalGet_cons :
    wp m (.globalGet i :: rest) Q st s env ↔
    (match st.globals.globals[i]? with
     | some v => wp m rest Q st { s with values := v :: s.values } env
     | none   => Q (.Invalid "globalGet index out of bounds")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_globalSet_cons :
    wp m (.globalSet i :: rest) Q st s env ↔
    (match s.values with
     | v :: vs =>
       (match st.globals.globals[i]? with
        | some _ =>
          wp m rest Q { st with globals := { globals := st.globals.globals.set i v } }
                      { s with values := vs } env
        | none => Q (.Invalid "globalSet index out of bounds"))
     | _ => Q (.Invalid "globalSet with empty stack")) := by
  wp_atomic

/-! ## Memory load / store -/

@[simp, wp_simp] theorem wp_load32_cons :
    wp m (.load32 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i32 (st.mem.read32 (a + off)) :: vs } env
     | _ => Q (.Invalid "load32: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_store32_cons :
    wp m (.store32 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q { st with mem := st.mem.write32 (a + off) v } { s with values := vs } env
     | _ => Q (.Invalid "store32: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load8U_cons :
    wp m (.load8U off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i32 (st.mem.read8 (a + off)).toUInt32 :: vs } env
     | _ => Q (.Invalid "load8U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load8S_cons :
    wp m (.load8S off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i32 (Int32.ofInt (signExtend (st.mem.read8 (a + off)).toNat 8)).toUInt32 :: vs } env
     | _ => Q (.Invalid "load8S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load16U_cons :
    wp m (.load16U off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i32 (st.mem.read16 (a + off)) :: vs } env
     | _ => Q (.Invalid "load16U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load16S_cons :
    wp m (.load16S off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i32 (Int32.ofInt (signExtend (st.mem.read16 (a + off)).toNat 16)).toUInt32 :: vs } env
     | _ => Q (.Invalid "load16S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_store8_cons :
    wp m (.store8 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q { st with mem := st.mem.write8 (a + off) v.toUInt8 } { s with values := vs } env
     | _ => Q (.Invalid "store8: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_store16_cons :
    wp m (.store16 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q { st with mem := st.mem.write16 (a + off) v } { s with values := vs } env
     | _ => Q (.Invalid "store16: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load64_cons :
    wp m (.load64 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i64 (st.mem.read64 (a + off)) :: vs } env
     | _ => Q (.Invalid "load64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_store64_cons :
    wp m (.store64 off :: rest) Q st s env ↔
    (match s.values with
     | .i64 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q { st with mem := st.mem.write64 (a + off) v } { s with values := vs } env
     | _ => Q (.Invalid "store64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load8UI64_cons :
    wp m (.load8UI64 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i64 (st.mem.read8 (a + off)).toUInt64 :: vs } env
     | _ => Q (.Invalid "load8UI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load8SI64_cons :
    wp m (.load8SI64 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i64 (Int64.ofInt (signExtend (st.mem.read8 (a + off)).toNat 8)).toUInt64 :: vs } env
     | _ => Q (.Invalid "load8SI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load16UI64_cons :
    wp m (.load16UI64 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i64 (st.mem.read16 (a + off)).toUInt64 :: vs } env
     | _ => Q (.Invalid "load16UI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load16SI64_cons :
    wp m (.load16SI64 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i64 (Int64.ofInt (signExtend (st.mem.read16 (a + off)).toNat 16)).toUInt64 :: vs } env
     | _ => Q (.Invalid "load16SI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load32UI64_cons :
    wp m (.load32UI64 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i64 (st.mem.read32 (a + off)).toUInt64 :: vs } env
     | _ => Q (.Invalid "load32UI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_load32SI64_cons :
    wp m (.load32SI64 off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .i64 (Int64.ofInt (signExtend (st.mem.read32 (a + off)).toNat 32)).toUInt64 :: vs } env
     | _ => Q (.Invalid "load32SI64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_store8I64_cons :
    wp m (.store8I64 off :: rest) Q st s env ↔
    (match s.values with
     | .i64 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 1 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q { st with mem := st.mem.write8 (a + off) v.toUInt8 } { s with values := vs } env
     | _ => Q (.Invalid "store8I64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_store16I64_cons :
    wp m (.store16I64 off :: rest) Q st s env ↔
    (match s.values with
     | .i64 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 2 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q { st with mem := st.mem.write16 (a + off) v.toUInt32 } { s with values := vs } env
     | _ => Q (.Invalid "store16I64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_store32I64_cons :
    wp m (.store32I64 off :: rest) Q st s env ↔
    (match s.values with
     | .i64 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q { st with mem := st.mem.write32 (a + off) v.toUInt32 } { s with values := vs } env
     | _ => Q (.Invalid "store32I64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_memorySize_cons :
    wp m (.memorySize :: rest) Q st s env ↔
    wp m rest Q st { s with values := .i32 st.mem.pages.toUInt32 :: s.values } env := by
  wp_atomic

@[simp, wp_simp] theorem wp_memoryGrow_cons :
    wp m (.memoryGrow :: rest) Q st s env ↔
    (match s.values with
     | .i32 delta :: vs =>
       match st.mem.grow delta m.memoryCap with
       | some (mem', cur) =>
         wp m rest Q { st with mem := mem' }
            { s with values := .i32 cur.toUInt32 :: vs } env
       | none =>
         wp m rest Q st { s with values := .i32 (0xFFFFFFFF : UInt32) :: vs } env
     | _ => Q (.Invalid "memoryGrow: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_memoryFill_cons :
    wp m (.memoryFill :: rest) Q st s env ↔
    (match s.values with
     | .i32 len :: .i32 val :: .i32 dst :: vs =>
       if dst.toNat + len.toNat > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else
         wp m rest Q { st with mem := st.mem.fill dst.toNat len.toNat val.toUInt8 }
            { s with values := vs } env
     | _ => Q (.Invalid "memoryFill: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_memoryCopy_cons :
    wp m (.memoryCopy :: rest) Q st s env ↔
    (match s.values with
     | .i32 len :: .i32 src :: .i32 dst :: vs =>
       if dst.toNat + len.toNat > st.mem.pages * 65536
          ∨ src.toNat + len.toNat > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else
         wp m rest Q { st with mem := st.mem.copy dst.toNat src.toNat len.toNat }
            { s with values := vs } env
     | _ => Q (.Invalid "memoryCopy: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_memoryInit_cons :
    wp m (.memoryInit i :: rest) Q st s env ↔
    (match s.values with
     | .i32 len :: .i32 src :: .i32 dst :: vs =>
       (match st.dataSegments[i]? with
        | none => Q (.Invalid s!"memoryInit: segment index {i} out of range")
        | some none =>
          if 0 < len.toNat ∨ dst.toNat + len.toNat > st.mem.pages * 65536 then
            Q (.Trap st "out of bounds memory access")
          else
            wp m rest Q st { s with values := vs } env
        | some (some segBytes) =>
          if src.toNat + len.toNat > segBytes.length
             ∨ dst.toNat + len.toNat > st.mem.pages * 65536 then
            Q (.Trap st "out of bounds memory access")
          else
            wp m rest Q
              { st with mem := st.mem.writeBytesFrom dst.toNat segBytes src.toNat len.toNat }
              { s with values := vs } env)
     | _ => Q (.Invalid "memoryInit: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_dataDrop_cons :
    wp m (.dataDrop i :: rest) Q st s env ↔
    (match st.dataSegments[i]? with
     | none => Q (.Invalid s!"dataDrop: segment index {i} out of range")
     | some _ =>
       wp m rest Q { st with dataSegments := st.dataSegments.set i none } s env) := by
  wp_atomic

/-! ## float constants -/

@[simp, wp_simp] theorem wp_f32Const_cons :
    wp m (.f32Const v :: rest) Q st s env ↔
    wp m rest Q st { s with values := .f32 v :: s.values } env := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Const_cons :
    wp m (.f64Const v :: rest) Q st s env ↔
    wp m rest Q st { s with values := .f64 v :: s.values } env := by
  wp_atomic

/-! ## f32 arithmetic -/

@[simp, wp_simp] theorem wp_f32Add_cons :
    wp m (.f32Add :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Add a b) :: vs } env
     | _ => Q (.Invalid "f32Add: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Sub_cons :
    wp m (.f32Sub :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Sub a b) :: vs } env
     | _ => Q (.Invalid "f32Sub: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Mul_cons :
    wp m (.f32Mul :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Mul a b) :: vs } env
     | _ => Q (.Invalid "f32Mul: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Div_cons :
    wp m (.f32Div :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Div a b) :: vs } env
     | _ => Q (.Invalid "f32Div: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Min_cons :
    wp m (.f32Min :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Min a b) :: vs } env
     | _ => Q (.Invalid "f32Min: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Max_cons :
    wp m (.f32Max :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Max a b) :: vs } env
     | _ => Q (.Invalid "f32Max: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Copysign_cons :
    wp m (.f32Copysign :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Copysign a b) :: vs } env
     | _ => Q (.Invalid "f32Copysign: ill-shaped operand stack")) := by
  wp_atomic

/-! ## f64 arithmetic -/

@[simp, wp_simp] theorem wp_f64Add_cons :
    wp m (.f64Add :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Add a b) :: vs } env
     | _ => Q (.Invalid "f64Add: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Sub_cons :
    wp m (.f64Sub :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Sub a b) :: vs } env
     | _ => Q (.Invalid "f64Sub: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Mul_cons :
    wp m (.f64Mul :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Mul a b) :: vs } env
     | _ => Q (.Invalid "f64Mul: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Div_cons :
    wp m (.f64Div :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Div a b) :: vs } env
     | _ => Q (.Invalid "f64Div: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Min_cons :
    wp m (.f64Min :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Min a b) :: vs } env
     | _ => Q (.Invalid "f64Min: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Max_cons :
    wp m (.f64Max :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Max a b) :: vs } env
     | _ => Q (.Invalid "f64Max: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Copysign_cons :
    wp m (.f64Copysign :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Copysign a b) :: vs } env
     | _ => Q (.Invalid "f64Copysign: ill-shaped operand stack")) := by
  wp_atomic

/-! ## f32 unary -/

@[simp, wp_simp] theorem wp_f32Abs_cons :
    wp m (.f32Abs :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Abs a) :: vs } env
     | _ => Q (.Invalid "f32Abs: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Neg_cons :
    wp m (.f32Neg :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Neg a) :: vs } env
     | _ => Q (.Invalid "f32Neg: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Sqrt_cons :
    wp m (.f32Sqrt :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Sqrt a) :: vs } env
     | _ => Q (.Invalid "f32Sqrt: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Ceil_cons :
    wp m (.f32Ceil :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Ceil a) :: vs } env
     | _ => Q (.Invalid "f32Ceil: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Floor_cons :
    wp m (.f32Floor :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Floor a) :: vs } env
     | _ => Q (.Invalid "f32Floor: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Trunc_cons :
    wp m (.f32Trunc :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Trunc a) :: vs } env
     | _ => Q (.Invalid "f32Trunc: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Nearest_cons :
    wp m (.f32Nearest :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .f32 (f32Nearest a) :: vs } env
     | _ => Q (.Invalid "f32Nearest: ill-shaped operand stack")) := by
  wp_atomic

/-! ## f64 unary -/

@[simp, wp_simp] theorem wp_f64Abs_cons :
    wp m (.f64Abs :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Abs a) :: vs } env
     | _ => Q (.Invalid "f64Abs: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Neg_cons :
    wp m (.f64Neg :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Neg a) :: vs } env
     | _ => Q (.Invalid "f64Neg: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Sqrt_cons :
    wp m (.f64Sqrt :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Sqrt a) :: vs } env
     | _ => Q (.Invalid "f64Sqrt: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Ceil_cons :
    wp m (.f64Ceil :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Ceil a) :: vs } env
     | _ => Q (.Invalid "f64Ceil: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Floor_cons :
    wp m (.f64Floor :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Floor a) :: vs } env
     | _ => Q (.Invalid "f64Floor: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Trunc_cons :
    wp m (.f64Trunc :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Trunc a) :: vs } env
     | _ => Q (.Invalid "f64Trunc: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Nearest_cons :
    wp m (.f64Nearest :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .f64 (f64Nearest a) :: vs } env
     | _ => Q (.Invalid "f64Nearest: ill-shaped operand stack")) := by
  wp_atomic

/-! ## f32 comparison -/

@[simp, wp_simp] theorem wp_f32Eq_cons :
    wp m (.f32Eq :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .i32 (if f32Eq a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f32Eq: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Ne_cons :
    wp m (.f32Ne :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .i32 (if f32Ne a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f32Ne: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Lt_cons :
    wp m (.f32Lt :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .i32 (if f32Lt a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f32Lt: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Gt_cons :
    wp m (.f32Gt :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .i32 (if f32Gt a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f32Gt: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Le_cons :
    wp m (.f32Le :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .i32 (if f32Le a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f32Le: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Ge_cons :
    wp m (.f32Ge :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: .f32 a :: vs => wp m rest Q st { s with values := .i32 (if f32Ge a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f32Ge: ill-shaped operand stack")) := by
  wp_atomic

/-! ## f64 comparison -/

@[simp, wp_simp] theorem wp_f64Eq_cons :
    wp m (.f64Eq :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .i32 (if f64Eq a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f64Eq: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Ne_cons :
    wp m (.f64Ne :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .i32 (if f64Ne a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f64Ne: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Lt_cons :
    wp m (.f64Lt :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .i32 (if f64Lt a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f64Lt: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Gt_cons :
    wp m (.f64Gt :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .i32 (if f64Gt a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f64Gt: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Le_cons :
    wp m (.f64Le :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .i32 (if f64Le a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f64Le: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Ge_cons :
    wp m (.f64Ge :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: .f64 a :: vs => wp m rest Q st { s with values := .i32 (if f64Ge a b then 1 else 0) :: vs } env
     | _ => Q (.Invalid "f64Ge: ill-shaped operand stack")) := by
  wp_atomic

/-! ## float memory -/

@[simp, wp_simp] theorem wp_f32Load_cons :
    wp m (.f32Load off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .f32 (st.mem.read32 (a + off)) :: vs } env
     | _ => Q (.Invalid "f32Load: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Load_cons :
    wp m (.f64Load off :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q st { s with values := .f64 (st.mem.read64 (a + off)) :: vs } env
     | _ => Q (.Invalid "f64Load: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32Store_cons :
    wp m (.f32Store off :: rest) Q st s env ↔
    (match s.values with
     | .f32 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 4 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q { st with mem := st.mem.write32 (a + off) v } { s with values := vs } env
     | _ => Q (.Invalid "f32Store: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64Store_cons :
    wp m (.f64Store off :: rest) Q st s env ↔
    (match s.values with
     | .f64 v :: .i32 a :: vs =>
       if a.toNat + off.toNat + 8 > st.mem.pages * 65536 then
         Q (.Trap st "out of bounds memory access")
       else wp m rest Q { st with mem := st.mem.write64 (a + off) v } { s with values := vs } env
     | _ => Q (.Invalid "f64Store: ill-shaped operand stack")) := by
  wp_atomic

/-! ## integer → float conversions -/

@[simp, wp_simp] theorem wp_f32ConvertI32S_cons :
    wp m (.f32ConvertI32S :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st { s with values := .f32 (f32ConvertI32S a) :: vs } env
     | _ => Q (.Invalid "f32ConvertI32S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32ConvertI32U_cons :
    wp m (.f32ConvertI32U :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st { s with values := .f32 (f32ConvertI32U a) :: vs } env
     | _ => Q (.Invalid "f32ConvertI32U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32ConvertI64S_cons :
    wp m (.f32ConvertI64S :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st { s with values := .f32 (f32ConvertI64S a) :: vs } env
     | _ => Q (.Invalid "f32ConvertI64S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32ConvertI64U_cons :
    wp m (.f32ConvertI64U :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st { s with values := .f32 (f32ConvertI64U a) :: vs } env
     | _ => Q (.Invalid "f32ConvertI64U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64ConvertI32S_cons :
    wp m (.f64ConvertI32S :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st { s with values := .f64 (f64ConvertI32S a) :: vs } env
     | _ => Q (.Invalid "f64ConvertI32S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64ConvertI32U_cons :
    wp m (.f64ConvertI32U :: rest) Q st s env ↔
    (match s.values with
     | .i32 a :: vs => wp m rest Q st { s with values := .f64 (f64ConvertI32U a) :: vs } env
     | _ => Q (.Invalid "f64ConvertI32U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64ConvertI64S_cons :
    wp m (.f64ConvertI64S :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st { s with values := .f64 (f64ConvertI64S a) :: vs } env
     | _ => Q (.Invalid "f64ConvertI64S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64ConvertI64U_cons :
    wp m (.f64ConvertI64U :: rest) Q st s env ↔
    (match s.values with
     | .i64 a :: vs => wp m rest Q st { s with values := .f64 (f64ConvertI64U a) :: vs } env
     | _ => Q (.Invalid "f64ConvertI64U: ill-shaped operand stack")) := by
  wp_atomic

/-! ## float → integer (trapping) -/

@[simp, wp_simp] theorem wp_i32TruncF32S_cons :
    wp m (.i32TruncF32S :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs =>
       match i32TruncF32S a with
       | some r => wp m rest Q st { s with values := .i32 r :: vs } env
       | none => if (Float32.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i32TruncF32S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncF32U_cons :
    wp m (.i32TruncF32U :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs =>
       match i32TruncF32U a with
       | some r => wp m rest Q st { s with values := .i32 r :: vs } env
       | none => if (Float32.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i32TruncF32U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncF64S_cons :
    wp m (.i32TruncF64S :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs =>
       match i32TruncF64S a with
       | some r => wp m rest Q st { s with values := .i32 r :: vs } env
       | none => if (Float.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i32TruncF64S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncF64U_cons :
    wp m (.i32TruncF64U :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs =>
       match i32TruncF64U a with
       | some r => wp m rest Q st { s with values := .i32 r :: vs } env
       | none => if (Float.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i32TruncF64U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncF32S_cons :
    wp m (.i64TruncF32S :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs =>
       match i64TruncF32S a with
       | some r => wp m rest Q st { s with values := .i64 r :: vs } env
       | none => if (Float32.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i64TruncF32S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncF32U_cons :
    wp m (.i64TruncF32U :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs =>
       match i64TruncF32U a with
       | some r => wp m rest Q st { s with values := .i64 r :: vs } env
       | none => if (Float32.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i64TruncF32U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncF64S_cons :
    wp m (.i64TruncF64S :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs =>
       match i64TruncF64S a with
       | some r => wp m rest Q st { s with values := .i64 r :: vs } env
       | none => if (Float.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i64TruncF64S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncF64U_cons :
    wp m (.i64TruncF64U :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs =>
       match i64TruncF64U a with
       | some r => wp m rest Q st { s with values := .i64 r :: vs } env
       | none => if (Float.ofBits a).isNaN then Q (.Trap st "invalid conversion to integer")
                 else Q (.Trap st "integer overflow")
     | _ => Q (.Invalid "i64TruncF64U: ill-shaped operand stack")) := by
  wp_atomic

/-! ## float → integer (saturating) -/

@[simp, wp_simp] theorem wp_i32TruncSatF32S_cons :
    wp m (.i32TruncSatF32S :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .i32 (i32TruncSatF32S a) :: vs } env
     | _ => Q (.Invalid "i32TruncSatF32S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncSatF32U_cons :
    wp m (.i32TruncSatF32U :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .i32 (i32TruncSatF32U a) :: vs } env
     | _ => Q (.Invalid "i32TruncSatF32U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncSatF64S_cons :
    wp m (.i32TruncSatF64S :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .i32 (i32TruncSatF64S a) :: vs } env
     | _ => Q (.Invalid "i32TruncSatF64S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32TruncSatF64U_cons :
    wp m (.i32TruncSatF64U :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .i32 (i32TruncSatF64U a) :: vs } env
     | _ => Q (.Invalid "i32TruncSatF64U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncSatF32S_cons :
    wp m (.i64TruncSatF32S :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .i64 (i64TruncSatF32S a) :: vs } env
     | _ => Q (.Invalid "i64TruncSatF32S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncSatF32U_cons :
    wp m (.i64TruncSatF32U :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .i64 (i64TruncSatF32U a) :: vs } env
     | _ => Q (.Invalid "i64TruncSatF32U: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncSatF64S_cons :
    wp m (.i64TruncSatF64S :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .i64 (i64TruncSatF64S a) :: vs } env
     | _ => Q (.Invalid "i64TruncSatF64S: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64TruncSatF64U_cons :
    wp m (.i64TruncSatF64U :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .i64 (i64TruncSatF64U a) :: vs } env
     | _ => Q (.Invalid "i64TruncSatF64U: ill-shaped operand stack")) := by
  wp_atomic

/-! ## float ↔ float / reinterpret -/

@[simp, wp_simp] theorem wp_f32DemoteF64_cons :
    wp m (.f32DemoteF64 :: rest) Q st s env ↔
    (match s.values with
     | .f64 a :: vs => wp m rest Q st { s with values := .f32 (f32DemoteF64 a) :: vs } env
     | _ => Q (.Invalid "f32DemoteF64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64PromoteF32_cons :
    wp m (.f64PromoteF32 :: rest) Q st s env ↔
    (match s.values with
     | .f32 a :: vs => wp m rest Q st { s with values := .f64 (f64PromoteF32 a) :: vs } env
     | _ => Q (.Invalid "f64PromoteF32: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i32ReinterpretF32_cons :
    wp m (.i32ReinterpretF32 :: rest) Q st s env ↔
    (match s.values with
     | .f32 b :: vs => wp m rest Q st { s with values := .i32 b :: vs } env
     | _ => Q (.Invalid "i32ReinterpretF32: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_i64ReinterpretF64_cons :
    wp m (.i64ReinterpretF64 :: rest) Q st s env ↔
    (match s.values with
     | .f64 b :: vs => wp m rest Q st { s with values := .i64 b :: vs } env
     | _ => Q (.Invalid "i64ReinterpretF64: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f32ReinterpretI32_cons :
    wp m (.f32ReinterpretI32 :: rest) Q st s env ↔
    (match s.values with
     | .i32 b :: vs => wp m rest Q st { s with values := .f32 b :: vs } env
     | _ => Q (.Invalid "f32ReinterpretI32: ill-shaped operand stack")) := by
  wp_atomic

@[simp, wp_simp] theorem wp_f64ReinterpretI64_cons :
    wp m (.f64ReinterpretI64 :: rest) Q st s env ↔
    (match s.values with
     | .i64 b :: vs => wp m rest Q st { s with values := .f64 b :: vs } env
     | _ => Q (.Invalid "f64ReinterpretI64: ill-shaped operand stack")) := by
  wp_atomic

end Wasm
