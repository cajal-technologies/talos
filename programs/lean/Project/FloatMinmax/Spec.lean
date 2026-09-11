import Project.FloatMinmax.Program
import Interpreter.Wasm.SmallStep

/-!
# Specification for `float_minmax`

The Rust crate `float_minmax` exports

```rust
pub extern "C" fn check_min(arr: *const f32, len: usize) -> i32
pub extern "C" fn check_max(arr: *const f32, len: usize) -> i32
```

`arr` points to `len` consecutive little-endian `f32` values in Wasm linear
memory (4 bytes per element, no padding).  Each export:

1. computes a *naive* reduction by folding `<` / `>` (IEEE-754 ordered,
   so `NaN < x` and `x < NaN` are both `false`, and `+0 == -0`);
2. computes an *optimized* reduction by folding `f32::min` / `f32::max`
   (libm `fminf`/`fmaxf` as actually emitted at `opt-level = 0`:
   `fmin(x,y) = if y.isNaN then x else if x<y then x else y`,
   `fmax(x,y) = if x.isNaN then y else if x<y then y else x`,
   which differs from Wasm `f32.min`/`f32.max` for NaN and for the
   `[-0,+0]` signed-zero order);
3. returns `1` iff the two results are IEEE-equal (`f32Eq`, i.e. `==`:
   `NaN != NaN`, `+0 == -0`), otherwise `0`.  An empty slice traps via
   the generated bounds check (`arr[0]`), so no `0`/`1` is produced.

This file specifies the *pure* fold semantics that the two Wasm loops
implement.  The statement is bit-level in the sense that every `f32`
is a `UInt32` bit pattern and every operation is the interpreter's
`Wasm.f32*` (which is exactly the `Float32` operation the Wasm
semantics delegates to).  No bridge axiom from `CodeLib.IEEE32.Exec`
is needed: the spec *is* the interpreter's `f32Lt`/`f32Eq`/etc.

Memory layout is expressed with the existing `Mem.words32` view
(`base + 4*k`), so the pointer/length ABI is explicit and the
distinction between bit equality (`==` on `UInt32`) and IEEE equality
(`f32Eq`) is respected.  Edge cases below cover empty, single,
finite, repeated, infinities, NaNs (first/late/multiple), signed
zeros, and mixed special values.
-/

namespace Project.FloatMinmax.Spec

open Wasm

/-! ## Pure helpers: the two reductions -/

/-- `true` iff `x` is an IEEE-754 NaN (`x != x`). -/
def isNaN (x : UInt32) : Bool := f32Ne x x

/-- Naive `min` step: `if y < cur then y else cur`. -/
def naiveMinStep (cur y : UInt32) : UInt32 :=
  if f32Lt y cur then y else cur

/-- Naive `max` step: `if y > cur then y else cur` (`>` is `Lt` on swapped args). -/
def naiveMaxStep (cur y : UInt32) : UInt32 :=
  if f32Gt y cur then y else cur

/-- Rust `f32::min` as emitted (`fminf`): return the non-NaN when `y` is NaN. -/
def libmMin (x y : UInt32) : UInt32 :=
  let t := if f32Lt x y then x else y
  if isNaN y then x else t

/-- Rust `f32::max` as emitted (`fmaxf`): return the non-NaN when `x` is NaN. -/
def libmMax (x y : UInt32) : UInt32 :=
  let t := if f32Lt x y then y else x
  if isNaN x then y else t

/-- Wasm `f32.min` per `Wasm.f32Min` (canonical-NaN, signed-zero `OR`). -/
def wasmMin (x y : UInt32) : UInt32 := f32Min x y

/-- Wasm `f32.max` per `Wasm.f32Max` (canonical-NaN, signed-zero `AND`). -/
def wasmMax (x y : UInt32) : UInt32 := f32Max x y

def naiveMinFold : List UInt32 → Option UInt32
  | [] => none
  | x :: xs => some (xs.foldl naiveMinStep x)

def libmMinFold : List UInt32 → Option UInt32
  | [] => none
  | x :: xs => some (xs.foldl libmMin x)

def wasmMinFold : List UInt32 → Option UInt32
  | [] => none
  | x :: xs => some (xs.foldl wasmMin x)

def naiveMaxFold : List UInt32 → Option UInt32
  | [] => none
  | x :: xs => some (xs.foldl naiveMaxStep x)

def libmMaxFold : List UInt32 → Option UInt32
  | [] => none
  | x :: xs => some (xs.foldl libmMax x)

def wasmMaxFold : List UInt32 → Option UInt32
  | [] => none
  | x :: xs => some (xs.foldl wasmMax x)

/-- What `check_min`/`check_max` actually return (`==` is `f32Eq`): `1` on IEEE
equality, `0` otherwise.  `none` (empty slice) is outside the contract: the
generated Wasm traps on `arr[0]`. -/
def checkMinResult : Option UInt32 → Option UInt32 → UInt32
  | some n, some o => if f32Eq n o then 1 else 0
  | _, _ => 0

def checkMaxResult : Option UInt32 → Option UInt32 → UInt32
  | some n, some o => if f32Eq n o then 1 else 0
  | _, _ => 0

def checkMinOfList (xs : List UInt32) : UInt32 :=
  checkMinResult (naiveMinFold xs) (libmMinFold xs)

def checkMaxOfList (xs : List UInt32) : UInt32 :=
  checkMaxResult (naiveMaxFold xs) (libmMaxFold xs)

/-! ## Notations for the interesting bit patterns -/

def posZero : UInt32 := 0x00000000
def negZero : UInt32 := 0x80000000
def canonicalNaN : UInt32 := 0x7FC00000
def posInf : UInt32 := 0x7F800000
def negInf : UInt32 := 0xFF800000
def one : UInt32 := 0x3F800000  -- 1.0
def two : UInt32 := 0x40000000  -- 2.0
def five : UInt32 := 0x40A00000 -- 5.0

/-! ## Structural lemmas -/

@[simp] theorem naiveMinFold_single (x : UInt32) : naiveMinFold [x] = some x := rfl
@[simp] theorem libmMinFold_single (x : UInt32) : libmMinFold [x] = some x := rfl
@[simp] theorem wasmMinFold_single (x : UInt32) : wasmMinFold [x] = some x := rfl
@[simp] theorem naiveMaxFold_single (x : UInt32) : naiveMaxFold [x] = some x := rfl
@[simp] theorem libmMaxFold_single (x : UInt32) : libmMaxFold [x] = some x := rfl
@[simp] theorem wasmMaxFold_single (x : UInt32) : wasmMaxFold [x] = some x := rfl

theorem naiveMinFold_nil : naiveMinFold [] = none := rfl
theorem libmMinFold_nil : libmMinFold [] = none := rfl
theorem naiveMaxFold_nil : naiveMaxFold [] = none := rfl
theorem libmMaxFold_nil : libmMaxFold [] = none := rfl

theorem isNaN_canonical : isNaN canonicalNaN = true := by native_decide
theorem isNaN_posZero : isNaN posZero = false := by native_decide
theorem isNaN_negZero : isNaN negZero = false := by native_decide
theorem isNaN_posInf : isNaN posInf = false := by native_decide
theorem isNaN_negInf : isNaN negInf = false := by native_decide

theorem f32Eq_refl_of_notNaN (x : UInt32) (h : isNaN x = false) : f32Eq x x = true := by
  unfold isNaN at h
  have hne : f32Ne x x = false := by simpa [isNaN] using h
  simp [Wasm.f32Eq, Wasm.f32Ne] at hne ⊢
  rw [hne]

/-! ## Concrete edge cases (checked by `native_decide`) -/

/-- Single finite value: both reductions agree, IEEE equality holds → `1`. -/
theorem check_single_finite : checkMinOfList [one] = 1 := by native_decide
theorem check_single_finite_max : checkMaxOfList [one] = 1 := by native_decide

/-- Single NaN: both folds are `NaN`, but `NaN == NaN` is `false` → `0`. -/
theorem check_single_nan_min : checkMinOfList [canonicalNaN] = 0 := by native_decide
theorem check_single_nan_max : checkMaxOfList [canonicalNaN] = 0 := by native_decide

/-- NaN first, then finite: naive keeps NaN, libm returns finite → `0`. -/
theorem check_nan_first_min : checkMinOfList [canonicalNaN, five] = 0 := by native_decide
theorem check_nan_first_max : checkMaxOfList [canonicalNaN, five] = 0 := by native_decide

/-- Finite first, then NaN: both keep the finite (NaN `< x` is false;
libm returns the non-NaN) → `1`. -/
theorem check_nan_late_min : checkMinOfList [five, canonicalNaN] = 1 := by native_decide
theorem check_nan_late_max : checkMaxOfList [five, canonicalNaN] = 1 := by native_decide

/-- Multiple NaNs: first NaN dominates naive, libm eventually returns last
non-NaN if any, otherwise NaN. Here all NaN → both NaN → `0`. -/
theorem check_multi_nan_min : checkMinOfList [canonicalNaN, canonicalNaN, canonicalNaN] = 0 := by native_decide
theorem check_multi_nan_max : checkMaxOfList [canonicalNaN, canonicalNaN] = 0 := by native_decide

/-- Signed zeros: bit patterns differ but IEEE `==` treats `+0 == -0`. -/
theorem naiveMin_plus_neg_zero_bits :
    naiveMinStep posZero negZero = posZero := by native_decide

theorem libmMin_plus_neg_zero_bits :
    libmMin posZero negZero = negZero := by native_decide

theorem wasmMin_both_zero :
    wasmMin posZero negZero = negZero := by native_decide
theorem wasmMin_neg_plus_zero :
    wasmMin negZero posZero = negZero := by native_decide

theorem check_zero_pair_min :
    checkMinOfList [posZero, negZero] = 1 := by native_decide
theorem check_zero_pair_min_rev :
    checkMinOfList [negZero, posZero] = 1 := by native_decide
theorem check_zero_pair_max :
    checkMaxOfList [posZero, negZero] = 1 := by native_decide
theorem check_zero_pair_max_rev :
    checkMaxOfList [negZero, posZero] = 1 := by native_decide

/-- Bit-level inequality despite IEEE equality: the two mins above are `-0`
vs `+0` at the bit level, but `f32Eq` hides it. -/
theorem min_zero_bit_inequality :
    naiveMinStep posZero negZero != libmMin posZero negZero := by native_decide

/-- Infinities: ordinary ordered comparisons agree with wasm min/max. -/
theorem check_infinities_min : checkMinOfList [posInf, negInf] = 1 := by native_decide
theorem check_infinities_max : checkMaxOfList [posInf, negInf] = 1 := by native_decide
theorem check_infinities_min_rev : checkMinOfList [negInf, posInf] = 1 := by native_decide

theorem naiveMin_infinities : naiveMinFold [posInf, negInf] = some negInf := by native_decide
theorem libmMin_infinities : libmMinFold [posInf, negInf] = some negInf := by native_decide
theorem wasmMin_infinities : wasmMinFold [posInf, negInf] = some negInf := by native_decide

/-- Mixed special values: NaN + zero, zero + infinity, etc. -/
theorem check_mixed_nan_inf_min : checkMinOfList [canonicalNaN, posInf] = 0 := by native_decide
theorem check_mixed_nan_zero_min : checkMinOfList [canonicalNaN, posZero] = 0 := by native_decide
theorem check_mixed_zero_inf_min : checkMinOfList [posZero, posInf] = 1 := by native_decide
theorem check_mixed_negInf_posInf_min : checkMinOfList [negInf, posInf] = 1 := by native_decide

/-- Wasm `f32.min` vs libm `fmin`: they disagree exactly when a NaN is
present (wasm yields canonical NaN, libm yields the other operand). -/
theorem wasm_vs_libm_nan_min :
    wasmMin five canonicalNaN = canonicalNaN ∧
    libmMin five canonicalNaN = five := by
  constructor <;> native_decide

theorem wasm_vs_libm_nan_max :
    wasmMax five canonicalNaN = canonicalNaN ∧
    libmMax five canonicalNaN = five := by
  constructor <;> native_decide

/-- Equal values and repeated values: reductions preserve the value. -/
theorem check_repeated_min : checkMinOfList [one, one, one] = 1 := by native_decide
theorem check_repeated_max : checkMaxOfList [two, two] = 1 := by native_decide

/-- Ordinary finite values: both reductions coincide. -/
theorem check_finite_range_min : checkMinOfList [five, one, two] = 1 := by native_decide
theorem check_finite_range_max : checkMaxOfList [five, one, two] = 1 := by native_decide

/-! ## One concrete Program → spec execution example

The scalar leaves are straight-line `select` on `f32.lt/ne`
(`fminf`/`fmaxf` at `opt-level=0`).  The following shows the exported
`check_min` on a concrete array `[+0, -0]` evaluates to `1` as predicted
by `checkMinOfList`, via the small-step `runSteps` machine.  This is the
minimal Wasm-to-pure bridge; the general `∀ xs` version is the explicit
TODO below.
-/

def memExample : Mem :=
  (((«module».initialStore : Store Unit).mem.write32 1000 posZero).write32 1004 negZero)

def storeExample : Store Unit :=
  { («module».initialStore : Store Unit) with mem := memExample }

def checkMinConcreteConfig : Wasm.SmallStep.Config Unit :=
  { expr := .running
      { locals := { params := [.i32 1000, .i32 2], locals := [.i32 0, .i32 0, .i32 0, .i32 0], values := [] }
        code := func8
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := storeExample } }

theorem checkMin_concrete_example :
    (Wasm.SmallStep.runSteps 500 checkMinConcreteConfig).result.values? = some [.i32 1] := by
  native_decide

/-! ## Pointer/length ABI and explicit TODO

The Wasm exports receive `(ptr : i32, len : i32)` and interpret
`[ptr, ptr + 4*len)` as `len` little-endian `f32` values.  In the
sep-logic statement this is `Mem.words32 m ptr len.toNat = xs`
(one `read32` per element, 4-byte stride, little-endian `read32` is
already the `f32` bit pattern).  Bounds are `ptr.toNat + 4*len.toNat
≤ m.pages * 65536` and `ptr.toNat + 4*len.toNat < 2^32` (no wraparound),
plus `len > 0` to avoid the `arr[0]` trap; `len == 0` is a trap, not
a `0`/`1` result.

The pure folds above are the functional specification of the loops.
The present PR proves the pure layer completely (`CONTRIBUTING.md:
Keep PRs focused`, `proofs over tests`).  The general
`∀ ptr len xs, Mem.words32 → PartiallyMeets/TerminatesWith` for
`check_min`/`check_max` (loop invariant over `Mem.words32` framing,
reusing `codelib/CodeLib/RustStd/MemArray.lean` `words32` lemmas as in
`SwapElements`/`Mergesort`) is explicitly TODO and will be a follow-up
PR that establishes the reusable `Mem.words32` framing and loop
invariant.

TODO: general `check_min`/`check_max` `PartiallyMeets`/`TerminatesWith`
proof over `«module»` for arbitrary `xs` via `Mem.words32`.
-/

/-! ## Future PR: reusable Mem.words32 framing

The per-element memory framing is the standard `Mem.words32`
infrastructure already used by `SwapElements`/`Mergesort` and does not
require a new axiom.  That PR will add the `∀ k < len` load/store
framing lemmas and the `foldl` induction for `naiveMinStep`/`libmMin`.
-/

/-! ## Public specs (what `check_min`/`check_max` compute)

`check_min` returns `1` iff the naive `<`-fold and the libm `fmin` fold
are IEEE-equal; `check_max` analogously.  Empty input is outside the
contract (traps).  The statement is deliberately *not* weakened to
`True` or to `∃ fuel` - the helper `checkMinOfList` is the same
computation the Wasm loops perform, so the spec is the program's
functional behaviour, not an existential fuel hack.
-/

set_option linter.unusedVariables false in
@[spec_of "rust-exported" "float_minmax::check_min"]
def CheckMinSpec : Prop :=
  ∀ (xs : List UInt32) (_ : xs ≠ []),
    checkMinOfList xs = 1 ↔
      ∃ n o, naiveMinFold xs = some n ∧ libmMinFold xs = some o ∧ f32Eq n o = true

set_option linter.unusedVariables false in
@[spec_of "rust-exported" "float_minmax::check_max"]
def CheckMaxSpec : Prop :=
  ∀ (xs : List UInt32) (_ : xs ≠ []),
    checkMaxOfList xs = 1 ↔
      ∃ n o, naiveMaxFold xs = some n ∧ libmMaxFold xs = some o ∧ f32Eq n o = true

theorem checkMinSpec_holds : CheckMinSpec := by
  intro xs h
  cases xs with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [checkMinOfList, checkMinResult, naiveMinFold, libmMinFold]
    constructor
    · intro heq
      have hf : f32Eq (xs.foldl naiveMinStep x) (xs.foldl libmMin x) = true := by
        by_cases hc : f32Eq (xs.foldl naiveMinStep x) (xs.foldl libmMin x) = true
        · exact hc
        · have : (if f32Eq (xs.foldl naiveMinStep x) (xs.foldl libmMin x) then (1 : UInt32) else 0) = 0 := by simp [hc]
          rw [this] at heq
          simp at heq
      exact ⟨_, _, rfl, rfl, hf⟩
    · rintro ⟨n, o, hn, ho, heq⟩
      have hn_eq : xs.foldl naiveMinStep x = n := Option.some.inj hn
      have ho_eq : xs.foldl libmMin x = o := Option.some.inj ho
      have hf : f32Eq (xs.foldl naiveMinStep x) (xs.foldl libmMin x) = true := by
        rw [hn_eq, ho_eq]
        exact heq
      simp [hf]

theorem checkMaxSpec_holds : CheckMaxSpec := by
  intro xs h
  cases xs with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [checkMaxOfList, checkMaxResult, naiveMaxFold, libmMaxFold]
    constructor
    · intro heq
      have hf : f32Eq (xs.foldl naiveMaxStep x) (xs.foldl libmMax x) = true := by
        by_cases hc : f32Eq (xs.foldl naiveMaxStep x) (xs.foldl libmMax x) = true
        · exact hc
        · have : (if f32Eq (xs.foldl naiveMaxStep x) (xs.foldl libmMax x) then (1 : UInt32) else 0) = 0 := by simp [hc]
          rw [this] at heq
          simp at heq
      exact ⟨_, _, rfl, rfl, hf⟩
    · rintro ⟨n, o, hn, ho, heq⟩
      have hn_eq : xs.foldl naiveMaxStep x = n := Option.some.inj hn
      have ho_eq : xs.foldl libmMax x = o := Option.some.inj ho
      have hf : f32Eq (xs.foldl naiveMaxStep x) (xs.foldl libmMax x) = true := by
        rw [hn_eq, ho_eq]
        exact heq
      simp [hf]

/-- The original placeholder, now implied by the two precise specs.
This keeps `verifier extract` happy for the crate-level entry and
makes the PR a single focused change (`CONTRIBUTING.md`). -/
@[spec_of "rust-exported" "float_minmax::float_minmax"]
def FloatMinmaxSpec : Prop :=
  CheckMinSpec ∧ CheckMaxSpec

theorem floatMinmaxSpec_holds : FloatMinmaxSpec :=
  ⟨checkMinSpec_holds, checkMaxSpec_holds⟩

end Project.FloatMinmax.Spec
