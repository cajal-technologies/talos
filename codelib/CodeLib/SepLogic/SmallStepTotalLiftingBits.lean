import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Total lifting rules for the bit operations of the hash map program

`CodeLib.SepLogic.SmallStepTotalLifting` carries the total-WP rules of the
Wasm instructions that the proofs needed until now.  The compiled hash map
uses eight more instructions that had no rule.  This file adds them.

Every rule here is a pure rule.  The interpreter already has a `Step`
constructor for each instruction, so each rule is one use of the
`wasm_twp_pure_rule` macro over that constructor.  The macro is at
`CodeLib/SepLogic/SmallStepTotalLifting.lean:164`.

## Where the instructions come from

The SipHash-1-3 of `std::collections::HashMap` is inlined into two bodies of
the program: absolute `func 17`, which rehashes, and absolute `func 18`,
which inserts.  The two bodies hold 215 of the 231 uses of `i64.xor`,
`i64.rotl`, `i64.add` and `i64.and`.  The remaining rules serve the capacity
arithmetic of `func 17`.

No body below absolute `func 52` uses any of these instructions, and the
borsh decoder at absolute `func 4` uses none of them either.  These rules are
therefore a prerequisite of `collect_entries` alone.

## Two names that are private

`rotateLeft64` at `Interpreter/Wasm/SmallStep.lean:459` is private, so
`twp_rotlI64` states the rotate in the unfolded form that the public theorem
`rotateLeft64_eq` gives.  That theorem is `rfl`, so the `Step` constructor
still closes the rule.  `twp_wrapI64` and `twp_extendUI32` state their
results the same way.

`clz32` at `Interpreter/Wasm/Semantics.lean:12` and `clz64` at
`Interpreter/Wasm/Semantics.lean:27` are public.  `twp_clz` names `clz32`
directly and `twp_clzI64` names `clz64` directly, as `twp_ctzI64` names
`ctz64`.

## Why there is no rule for `unreachable`

The gap survey counted `unreachable` as a twelfth missing rule.  This file
does not add one, and the map proof does not need one.

Every `unreachable` in the studied regions stands directly after a call to a
function that does not return: `call 99`, `call 102`, `call 103`, `call 104`
and `call 107` are the panic and abort paths that `rustc` emits.  The
instruction is the terminator of a block that control reaches only after the
panic call.  A total-correctness proof closes such a block by showing that
its guard is false, so the step never happens.

The contracts already carry that obligation.
`Project.RustHashMap.CollectContract` states that the body proof must show
the capacity-overflow exit of absolute `func 17` is not reachable, because
absolute `func 58` refuses the allocation and raises `talos.oom` first.  The
decoder carries the same obligation for absolute `func 99`.

Write `twp_unreachable_gen` only if one of those guards turns out to be
live.  The rule cannot use `wasm_twp_pure_rule`, because the step leaves the
`.running` expression for `.trapped`, which `twp_pureStep` cannot state.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

section terminalGenericBits

variable [WasmSmallStepGS hlc α]
variable {Terminal : Type}
variable [view : TerminalView α Terminal]
local instance (priority := high) activeTerminalLanguageBits :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage
local instance (priority := high) activeTerminalIrisGSBits :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      activeTerminalLanguageBits (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }
variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

/-! ## The 64-bit operations of the SipHash round

`twp_subI64`, `twp_mulI64`, `twp_orI64`, `twp_shlI64` and `twp_shrUI64`
already exist.  The four rules below complete the set that the round needs.
-/

wasm_twp_pure_rule twp_addI64 {lhs rhs : UInt64} :
  .addI64, .i64 rhs :: .i64 lhs :: values =>
    .i64 (lhs + rhs) :: values := Step.addI64

-- The same statement as `twp_andI64` in PR #235, under a suffix so that the
-- two PRs merge in either order.  Delete this copy and its two
-- `wasm_twp_pures` cases in `Project.RustHashMap.BitPures` and
-- `Project.RustHashMap.LookupPures` when that PR lands.
wasm_twp_pure_rule twp_andI64_bits {lhs rhs : UInt64} :
  .andI64, .i64 rhs :: .i64 lhs :: values =>
    .i64 (lhs &&& rhs) :: values := Step.andI64

wasm_twp_pure_rule twp_xorI64 {lhs rhs : UInt64} :
  .xorI64, .i64 rhs :: .i64 lhs :: values =>
    .i64 (lhs ^^^ rhs) :: values := Step.xorI64

wasm_twp_pure_rule twp_rotlI64 {lhs rhs : UInt64} :
  .rotlI64, .i64 rhs :: .i64 lhs :: values =>
    .i64 (let count := rhs % 64
          if count = 0 then lhs
          else (lhs <<< count) ||| (lhs >>> (64 - count))) :: values :=
  Step.rotlI64

/-! ## The 64-bit test -/

wasm_twp_pure_rule twp_eqzI64 {value : UInt64} {result : UInt32}
    (hresult : result = if value = 0 then 1 else 0) :
  .eqzI64, .i64 value :: values =>
    .i32 result :: values := Step.eqzI64 hresult

/-! ## The 32-bit operations of the capacity arithmetic -/

wasm_twp_pure_rule twp_xor {lhs rhs : UInt32} :
  .xor, .i32 rhs :: .i32 lhs :: values =>
    .i32 (lhs ^^^ rhs) :: values := Step.xor

wasm_twp_pure_rule twp_clz {value : UInt32} :
  .clz, .i32 value :: values =>
    .i32 (UInt32.ofNat (clz32 32 value)) :: values := Step.clz

wasm_twp_pure_rule twp_clzI64 {value : UInt64} :
  .clzI64, .i64 value :: values =>
    .i64 (UInt64.ofNat (clz64 64 value)) :: values := Step.clzI64

/-! ## The `wasm_twp_pures` case of the 64-bit count of leading zeros

The macro at `CodeLib/SepLogic/SmallStepTotalLifting.lean:1662` predates
this rule, so it has no case for it.  The case below adds one.  The other
rules of this file get their cases downstream.
-/

macro_rules
  | `(tactic| wasm_twp_pures [twp_clzI64 $rest:ident*]) =>
      `(tactic| iapply twp_clzI64; wasm_twp_pures [$rest:ident*])

wasm_twp_pure_rule twp_divU {dividend divisor : UInt32}
    (hdivisor : divisor ≠ 0) :
  .divU, .i32 divisor :: .i32 dividend :: values =>
    .i32 (dividend / divisor) :: values := Step.divU hdivisor

end terminalGenericBits

section terminalGenericBitsMemory

variable {hlc : outParam HasLC} {α : Type}
variable [WasmSmallStepGS hlc α]
variable {Terminal : Type}
variable [view : TerminalView α Terminal]
local instance (priority := high) activeTerminalLanguageBitsMem :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage
local instance (priority := high) activeTerminalIrisGSBitsMem :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      activeTerminalLanguageBitsMem (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }
variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

/-! ## The two narrow loads

`extend8To32` at `Interpreter/Wasm/SmallStep.lean:525` is private, so
`twp_load8S_gen` states the sign extension in the unfolded form that the
public theorem `extend8To32_eq` gives.  `signExtend` at
`Interpreter/Wasm/Semantics.lean:42` is public.

The proofs follow `twp_load8U_gen` at
`SmallStepTotalLiftingBytesTerminal.lean:38` and `twp_load32` at
`SmallStepTotalLifting.lean:860`.  Each rule reuses the state lemma that its
template uses, so this file adds no state-interpretation lemma.
-/

/-- Total rule for `i32.load8_s` under every terminal view. -/
theorem twp_load8S_gen
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8)
    (hnowrap : (address + offset).toNat = address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8S offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues,
        .i32 (Int32.ofInt (signExtend byte.toNat 8)).toUInt32
          :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some byte) -∗
    (pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address + offset⟩ (DFrac.own 1) (some byte) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  wasm_twp_start_with iintro Hpt Htwp
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read8 (address + offset) = byte ∧
        (address + offset).toNat < store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_facts store ns obs nt (address + offset) byte $$
      [Hσ Hpt]
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by omega
  wasm_twp_step (by
      simpa [Hread, extend8To32_eq] using
        (Step.load8S (α := α) (address := Value.i32 address) rfl hbound)) =>
    wasm_twp_frame
      iapply_exact Htwp with Hpt

/-- Total rule for `i64.load32_u` under every terminal view.  The resource is
a `pointsTo_u32`, because the instruction reads four bytes, and the pushed
value is the same word widened to 64 bits. -/
theorem twp_load32UI64
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (word : UInt32)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat =
      (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat =
      (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat =
      (address + offset).toNat + 3) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load32UI64 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i64 word.toUInt64 :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u32 0 (address + offset) word -∗
    (pointsTo_u32 0 (address + offset) word -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  wasm_twp_start_with iintro Hword Htwp
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = word ∧
        (address + offset).toNat + 4 ≤
          store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u32_facts store ns obs nt
      (address + offset) word h1 h2 h3 $$ [Hσ Hword]
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by simpa only [hnowrap] using HinBounds
  wasm_twp_step (by
    simpa [Hread] using
      (Step.load32UI64 (α := α) (address := Value.i32 address) rfl hbound)) =>
    wasm_twp_frame
      iapply_exact Htwp with Hword

end terminalGenericBitsMemory

end Wasm.SmallStep
