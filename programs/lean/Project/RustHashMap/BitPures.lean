import CodeLib.SepLogic.SmallStepTotalLiftingBits
import CodeLib.RustStd.HashMap.SipHash

/-!
# Pure-step cases and rotate bridges for the inlined SipHash

`CodeLib.SepLogic.SmallStepTotalLiftingBits` adds the total-WP rules that the
two hash map bodies need, but the `wasm_twp_pures` macro at
`CodeLib/SepLogic/SmallStepTotalLifting.lean:1662` predates them, so it has no
case for any of them.  A run of `i64.xor`, `i64.add` and `i64.rotl` then costs
one `iapply` per instruction.  Absolute `func 18` holds 161 such instructions
in one straight line, so this file adds the missing cases.

A `macro_rules` block extends the syntax of the upstream package, so these
cases cost no rebuild of `codelib`.  Move them next to the rules themselves
when `codelib` is edited for another reason.

## Why the rotate needs a bridge

`rotateLeft64` at `Interpreter/Wasm/SmallStep.lean:459` is private, so
`twp_rotlI64` states its result in the unfolded form

```
let count := rhs % 64
if count = 0 then lhs else (lhs <<< count) ||| (lhs >>> (64 - count))
```

while the model writes `Wasm.RustStd.HashMap.SipHash.rotl lhs rhs`.  The two
agree at every rotate amount that the compiled body uses, and the body uses
five: 13, 16, 17, 21 and 32.  One bridge per amount turns the unfolded form
into the model one.
-/

namespace Wasm.SmallStep

/-! ## The missing `wasm_twp_pures` cases -/

macro_rules
  | `(tactic| wasm_twp_pures [twp_addI64 $rest:ident*]) =>
      `(tactic| iapply twp_addI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_andI64 $rest:ident*]) =>
      `(tactic| iapply twp_andI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_xorI64 $rest:ident*]) =>
      `(tactic| iapply twp_xorI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_rotlI64 $rest:ident*]) =>
      `(tactic| iapply twp_rotlI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_xor $rest:ident*]) =>
      `(tactic| iapply twp_xor; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_clz $rest:ident*]) =>
      `(tactic| iapply twp_clz; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_eqzI64 $rest:ident*]) =>
      `(tactic| iapply twp_eqzI64 rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_neI64 $rest:ident*]) =>
      `(tactic| iapply twp_neI64 rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_eqI64 $rest:ident*]) =>
      `(tactic| iapply twp_eqI64 rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_ltS $rest:ident*]) =>
      `(tactic| iapply twp_ltS rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_ne $rest:ident*]) =>
      `(tactic| iapply twp_ne rfl; wasm_twp_pures [$rest:ident*])

end Wasm.SmallStep

namespace Project.RustHashMap.BitPures

open Wasm.RustStd.HashMap

/-! ## The five rotate bridges -/

/-- The rotate that `twp_rotlI64` gives, at amount 13. -/
theorem rotlWasm13 (x : UInt64) :
    (let count := (13 : UInt64) % 64
     if count = 0 then x else (x <<< count) ||| (x >>> (64 - count)))
      = SipHash.rotl x 13 := rfl

/-- The rotate that `twp_rotlI64` gives, at amount 16. -/
theorem rotlWasm16 (x : UInt64) :
    (let count := (16 : UInt64) % 64
     if count = 0 then x else (x <<< count) ||| (x >>> (64 - count)))
      = SipHash.rotl x 16 := rfl

/-- The rotate that `twp_rotlI64` gives, at amount 17. -/
theorem rotlWasm17 (x : UInt64) :
    (let count := (17 : UInt64) % 64
     if count = 0 then x else (x <<< count) ||| (x >>> (64 - count)))
      = SipHash.rotl x 17 := rfl

/-- The rotate that `twp_rotlI64` gives, at amount 21. -/
theorem rotlWasm21 (x : UInt64) :
    (let count := (21 : UInt64) % 64
     if count = 0 then x else (x <<< count) ||| (x >>> (64 - count)))
      = SipHash.rotl x 21 := rfl

/-- The rotate that `twp_rotlI64` gives, at amount 32. -/
theorem rotlWasm32 (x : UInt64) :
    (let count := (32 : UInt64) % 64
     if count = 0 then x else (x <<< count) ||| (x >>> (64 - count)))
      = SipHash.rotl x 32 := rfl

/-! ## The shift-amount bridges

`twp_shlI64`, `twp_shrUI64`, `twp_shl` and `twp_shrU` state the Wasm rule
that the shift amount is taken modulo the width.  The compiled body uses
five literal amounts, and at a literal the modulo is definitional.  These
bridges remove it, so a later rewrite sees the plain amount. -/

/-- `i64.shr_u` at 1. -/
theorem shrU64Wasm1 (x : UInt64) : x >>> ((1 : UInt64) % 64) = x >>> 1 := rfl

/-- `i64.shr_u` at 25. -/
theorem shrU64Wasm25 (x : UInt64) : x >>> ((25 : UInt64) % 64) = x >>> 25 := rfl

/-- `i64.shr_u` at 32. -/
theorem shrU64Wasm32 (x : UInt64) : x >>> ((32 : UInt64) % 64) = x >>> 32 := rfl

/-- `i64.shl` at 1. -/
theorem shl64Wasm1 (x : UInt64) : x <<< ((1 : UInt64) % 64) = x <<< 1 := rfl

/-- `i32.shr_u` at 3. -/
theorem shrU32Wasm3 (x : UInt32) : x >>> ((3 : UInt32) % 32) = x >>> 3 := rfl

/-- `i32.shl` at 3. -/
theorem shl32Wasm3 (x : UInt32) : x <<< ((3 : UInt32) % 32) = x <<< 3 := rfl

end Project.RustHashMap.BitPures
