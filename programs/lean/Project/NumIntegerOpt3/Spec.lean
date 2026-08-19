import Project.NumIntegerOpt3.Program

namespace Project.NumIntegerOpt3.Spec

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SmallStep
open Wasm.SepLogic

set_option maxRecDepth 1048576

/-- Small-step entry configuration for the generated `gcd_u64` body.  The
legacy theorem below starts through the old entry runner; migration proofs use
this configuration directly so their semantics is solely `SmallStep.Step`. -/
def gcdConfig (a b : UInt64) : Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a, .i64 b], [.i64 0], []⟩,
        func0, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

/-- Control frame installed by the outer generated block.  Naming it keeps
the later Stein-loop proof readable while preserving the exact administrative
state used by `SmallStep.Step`. -/
def gcdOuterFrame (body : Program) : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body
    continuation := [.localGet 2]
    belowStack := [] }

local instance instGcdIrisGS [WasmSmallStepGS hlc Unit] :
    IrisGS_gen hlc (Expr Unit) (WasmHeapGF Unit) :=
  Wasm.SmallStep.instIrisGS (α := Unit)

/-- Execute the common recombination tail after the odd-part loop has selected
its surviving value. -/
theorem finishGcd_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (outerBody : Program) (g gy shared expected : UInt64)
    (hrecombine : g <<< (shared % 64) = expected) :
    (iprop(True) : IProp (WasmHeapGF Unit)) ⊢ WP (.running
      ⟨⟨[.i64 g, .i64 gy], [.i64 shared], []⟩,
        [.localGet 0, .localGet 2, .shlI64, .localSet 2],
        1, [], [gcdOuterFrame outerBody], []⟩ : Expr Unit) @ s; E
      {{ rs, ⌜rs = [Value.i64 expected]⌝ }} := by
  iintro Htrue
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_shlI64
  inext
  iapply wp_localSet rfl
  inext
  iapply wp_exitControl rfl
  inext
  simp only [gcdOuterFrame, List.take_nil, List.nil_append]
  iapply wp_localGet rfl
  inext
  rw [hrecombine]
  iapply wp_finish
  inext
  iapply wp_value'
  ipureintro
  rfl

/-- The two early exits of generated `gcd_u64`, proved through iris-lean's WP
over the authoritative small-step relation.  This is deliberately a complete
vertical slice: both zero cases include block entry/branch administration,
function completion, and operational adequacy. -/
theorem mod3_gcd_zero_smallStep (a b : UInt64) (hz : a = 0 ∨ b = 0) :
    PartiallyMeets (gcdConfig a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  apply wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [gcdConfig, func0]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_orI64
  inext
  iapply wp_localSet rfl
  inext
  iapply wp_block
  inext
  by_cases ha : a = 0
  · subst a
    iapply wp_localGet rfl
    inext
    iapply wp_eqzI64 (result := 1) (by decide)
    inext
    iapply wp_brIf (by decide) rfl
    inext
    simp only [List.take_nil, List.nil_append]
    iapply wp_localGet rfl
    inext
    iapply wp_finish
    inext
    iapply wp_value'
    ipureintro
    simp
  · have hb : b = 0 := hz.resolve_left ha
    subst b
    iapply wp_localGet rfl
    inext
    iapply wp_eqzI64 (result := 0) (by rw [if_neg ha])
    inext
    iapply wp_brIfZero
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_eqzI64 (result := 1) (by decide)
    inext
    iapply wp_brIf (by decide) rfl
    inext
    simp only [List.take_nil, List.drop_nil, List.nil_append]
    iapply wp_localGet rfl
    inext
    iapply wp_finish
    inext
    iapply wp_value'
    ipureintro
    simp

/-- Straight-line driver for the register-only `func0`: the atomic `wp`
lemmas plus list/`Nat` reductions (no memory lemmas — this build never
touches linear memory). -/
local macro "drive" : tactic => `(tactic|
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append,
    List.take, List.drop, List.replicate, List.map, ValueType.zero, List.headD,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, reduceIte, Nat.reduceLeDiff,
    UInt32.reduceAdd, UInt32.reduceToNat, gt_iff_lt])

/-- Reduce a `br_if` `match` once its `i32` condition is a literal (`0` or a
nonzero constant). Plain `simp` reduces the `.i32 0` (fall-through) arm but not
the nonzero (break) arm; `decide` closes that gap. -/
local macro "pick" : tactic => `(tactic| simp (config := { decide := true }) only [])

/-- The `UInt64` odd part written as a `Nat` shift (the form the `CodeLib`
Stein lemmas produce). -/
theorem oddPart_toNat (v : UInt64) :
    (v >>> (UInt64.ofNat (ctz64 64 v) % 64)).toNat = v.toNat >>> (ctz64 64 v % 64) := by
  rw [UInt64.toNat_shiftRight, UInt64.toNat_mod]
  congr 1
  rw [UInt64.toNat_ofNat', show UInt64.toNat 64 = 64 from rfl,
      Nat.mod_mod_of_dvd _ (by norm_num : (64 : Nat) ∣ 2 ^ 64), Nat.mod_mod]

/-- The loop body of Stein's subtract-and-halve, kept as a definition so it
stays opaque while the surrounding structure is driven. -/
def loopBody : Program :=
  [ .block 0 0
      [ .localGet 0, .localGet 1, .gtUI64, .br_if 0,
        .localGet 0, .localGet 1, .localGet 0, .subI64, .localSet 1,
        .localGet 1, .localGet 1, .ctzI64, .shrUI64, .localSet 1,
        .localGet 1, .eqI64, .br_if 2, .br 1 ],
    .localGet 0, .localGet 1, .subI64, .localSet 0,
    .localGet 0, .localGet 0, .ctzI64, .shrUI64, .localSet 0,
    .localGet 0, .localGet 1, .neI64, .br_if 0 ]

/-- The body of the inner block: reduce both operands to their odd parts,
short-circuit when they are already equal, then run the loop, then copy the
surviving odd value into local 0. -/
def innerBody : Program :=
  [ .localGet 0, .localGet 0, .ctzI64, .shrUI64, .localSet 0,
    .localGet 0, .localGet 1, .localGet 1, .ctzI64, .shrUI64, .localSet 1,
    .localGet 1, .eqI64, .br_if 0,
    .loop 0 0 loopBody,
    .localGet 1, .localSet 0 ]

/-- Body of the generated outer early-exit block, factored without changing
the generated instruction sequence. -/
def gcdOuterBody : Program :=
  [ .localGet 0, .eqzI64, .br_if 0,
    .localGet 1, .eqzI64, .br_if 0,
    .localGet 2, .ctzI64, .localSet 2,
    .block 0 0 innerBody,
    .localGet 0, .localGet 2, .shlI64, .localSet 2 ]

/-- Control frame for the odd-part block nested inside the generated outer
block. -/
def gcdInnerFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := innerBody
    continuation := [.localGet 0, .localGet 2, .shlI64, .localSet 2]
    belowStack := [] }

/-- Control frame installed by Stein's generated loop. -/
def gcdLoopFrame : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := loopBody
    continuation := [.localGet 1, .localSet 0]
    belowStack := [] }

/-- Partial-correctness loop invariant for the generated subtract-and-halve
kernel.  Löb induction is sufficient: unlike the legacy total-correctness
proof, Iris does not need the decreasing `x+y` variant. -/
theorem gcdLoopBody_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (outerBody : Program) (ao bo x y shared expected : UInt64)
    (hxne : x ≠ 0) (hyne : y ≠ 0)
    (hxodd : x.toNat % 2 = 1) (hyodd : y.toNat % 2 = 1)
    (hxyne : x ≠ y)
    (hgcd : Nat.gcd x.toNat y.toNat = Nat.gcd ao.toNat bo.toNat)
    (hrecombine : ∀ g : UInt64,
      g.toNat = Nat.gcd ao.toNat bo.toNat →
      g <<< (shared % 64) = expected) :
    (iprop(True) : IProp (WasmHeapGF Unit)) ⊢
      WP (.running
        ⟨⟨[.i64 x, .i64 y], [.i64 shared], []⟩,
          loopBody, 1, [],
          [gcdLoopFrame, gcdInnerFrame, gcdOuterFrame outerBody], []⟩ :
          Expr Unit) @ s; E
        {{ rs, ⌜rs = [.i64 expected]⌝ }} := by
  iintro _
  iloeb as IH generalizing %x %y %hxne %hyne %hxodd %hyodd %hxyne %hgcd
  simp only [loopBody]
  iapply wp_block
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  by_cases hgt : y < x
  · iapply wp_gtUI64 (result := 1) (by simp [hgt])
    inext
    iapply wp_brIf (by decide) rfl
    inext
    simp only [List.take_nil, List.drop_nil, List.nil_append]
    iapply wp_localGet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_subI64
    inext
    iapply wp_localSet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_ctzI64
    inext
    iapply wp_shrUI64
    inext
    iapply wp_localSet rfl
    inext
    simp only [List.set]
    let x' := (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64)
    obtain ⟨hx'ne, hx'odd, hgcd', _hdec⟩ :=
      UInt64.stein_step_x x y hxne hyne hxodd hyodd hgt
    by_cases hx'y : x' = y
    · change (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64) = y at hx'y
      iapply wp_localGet rfl
      inext
      iapply wp_localGet rfl
      inext
      iapply wp_neI64 (result := 0) (by simp [hx'y])
      inext
      iapply wp_brIfZero
      inext
      iapply wp_exitControl rfl
      inext
      simp only [gcdLoopFrame, List.take_nil, List.nil_append]
      iapply wp_localGet rfl
      inext
      iapply wp_localSet rfl
      inext
      simp only [List.set]
      iapply wp_exitControl rfl
      inext
      simp only [gcdInnerFrame, List.take_nil, List.nil_append]
      have hh : (x - y).toNat >>> (ctz64 64 (x - y) % 64) = y.toNat := by
        rw [← oddPart_toNat, hx'y]
      have hyGcd : y.toNat = Nat.gcd ao.toNat bo.toNat := by
        rw [← hgcd, ← hgcd', hh, Nat.gcd_self]
      iapply finishGcd_smallStep_wp outerBody y y shared expected
        (hrecombine y hyGcd)
      itrivial
    · change (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64) ≠ y at hx'y
      iapply wp_localGet rfl
      inext
      iapply wp_localGet rfl
      inext
      iapply wp_neI64 (result := 1) (by simp [hx'y])
      inext
      iapply wp_brIf (by decide) rfl
      inext
      simp only [gcdLoopFrame, List.take_nil, List.nil_append]
      simp only [loopBody]
      ispecialize IH $$ %
        ((x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64)) %y
      iapply IH
      ipureintro
      exact hx'ne
      ipureintro
      exact hyne
      ipureintro
      simpa [x', oddPart_toNat] using hx'odd
      ipureintro
      exact hyodd
      ipureintro
      exact hx'y
      ipureintro
      simpa [x', oddPart_toNat] using hgcd'.trans hgcd
      itrivial
  · iapply wp_gtUI64 (result := 0) (by simp [hgt])
    inext
    iapply wp_brIfZero
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_subI64
    inext
    iapply wp_localSet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_ctzI64
    inext
    iapply wp_shrUI64
    inext
    iapply wp_localSet rfl
    inext
    simp only [List.set]
    let y' := (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64)
    obtain ⟨hy'ne, hy'odd, hgcd', _hdec⟩ :=
      UInt64.stein_step_y x y hxne hyne hxodd hyodd hgt hxyne
    by_cases hxy' : x = y'
    · change x = (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64) at hxy'
      iapply wp_localGet rfl
      inext
      iapply wp_eqI64 (result := 1) (by rw [if_pos hxy'])
      inext
      iapply wp_brIf (by decide) rfl
      inext
      simp only [gcdInnerFrame, List.take_nil, List.nil_append]
      rw [← hxy']
      have hh : (y - x).toNat >>> (ctz64 64 (y - x) % 64) = x.toNat := by
        rw [← oddPart_toNat, ← hxy']
      have hxGcd : x.toNat = Nat.gcd ao.toNat bo.toNat := by
        rw [← hgcd, ← hgcd', hh, Nat.gcd_self]
      iapply finishGcd_smallStep_wp outerBody x x shared expected
        (hrecombine x hxGcd)
      itrivial
    · change x ≠ (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64) at hxy'
      iapply wp_localGet rfl
      inext
      iapply wp_eqI64 (result := 0) (by rw [if_neg hxy'])
      inext
      iapply wp_brIfZero
      inext
      iapply wp_br rfl
      inext
      simp only [gcdLoopFrame, List.take_nil, List.nil_append]
      simp only [loopBody]
      ispecialize IH $$ %x %
        ((y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64))
      iapply IH
      ipureintro
      exact hxne
      ipureintro
      exact hy'ne
      ipureintro
      exact hxodd
      ipureintro
      simpa [y', oddPart_toNat] using hy'odd
      ipureintro
      exact hxy'
      ipureintro
      simpa [y', oddPart_toNat] using hgcd'.trans hgcd
      itrivial

/-- The generated odd-part setup and equality fast path, followed by the
Löb-inductive Stein loop when the odd parts differ. -/
theorem gcdInner_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (outerBody : Program) (p0 p1 shared expected : UInt64)
    (hp0 : p0 ≠ 0) (hp1 : p1 ≠ 0)
    (hrecombine : ∀ g : UInt64,
      g.toNat =
        Nat.gcd
          (p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64)).toNat
          (p1 >>> (UInt64.ofNat (ctz64 64 p1) % 64)).toNat →
      g <<< (shared % 64) = expected) :
    (iprop(True) : IProp (WasmHeapGF Unit)) ⊢
      WP (.running
        ⟨⟨[.i64 p0, .i64 p1], [.i64 shared], []⟩,
          innerBody, 1, [],
          [gcdInnerFrame, gcdOuterFrame outerBody], []⟩ :
          Expr Unit) @ s; E
        {{ rs, ⌜rs = [.i64 expected]⌝ }} := by
  iintro Htrue
  simp only [innerBody]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_ctzI64
  inext
  iapply wp_shrUI64
  inext
  iapply wp_localSet rfl
  inext
  simp only [List.set]
  let ao := p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64)
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_ctzI64
  inext
  iapply wp_shrUI64
  inext
  iapply wp_localSet rfl
  inext
  simp only [List.set]
  let bo := p1 >>> (UInt64.ofNat (ctz64 64 p1) % 64)
  have haone : ao ≠ 0 := UInt64.shr_ctz_ne_zero p0 hp0
  have hbone : bo ≠ 0 := UInt64.shr_ctz_ne_zero p1 hp1
  have haodd : ao.toNat % 2 = 1 := by
    simpa [ao, oddPart_toNat] using UInt64.shr_ctz_toNat_odd p0 hp0
  have hbodd : bo.toNat % 2 = 1 := by
    simpa [bo, oddPart_toNat] using UInt64.shr_ctz_toNat_odd p1 hp1
  iapply wp_localGet rfl
  inext
  by_cases hab : ao = bo
  · iapply wp_eqI64 (result := 1) (by rw [if_pos hab])
    inext
    iapply wp_brIf (by decide) rfl
    inext
    simp only [gcdInnerFrame, List.take_nil, List.nil_append]
    have haoGcd : ao.toNat = Nat.gcd ao.toNat bo.toNat := by
      rw [← hab, Nat.gcd_self]
    iapply finishGcd_smallStep_wp outerBody ao bo shared expected
      (hrecombine ao haoGcd)
    itrivial
  · iapply wp_eqI64 (result := 0) (by rw [if_neg hab])
    inext
    iapply wp_brIfZero
    inext
    iapply wp_loop
    inext
    simp only [List.drop_nil]
    rw [show
      ({ kind := .loop
         paramArity := 0
         resultArity := 0
         body := loopBody
         continuation := [.localGet 1, .localSet 0]
         belowStack := [] } : ControlFrame) = gcdLoopFrame from rfl]
    iapply gcdLoopBody_smallStep_wp outerBody
      (p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64))
      (p1 >>> (UInt64.ofNat (ctz64 64 p1) % 64))
      (p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64))
      (p1 >>> (UInt64.ofNat (ctz64 64 p1) % 64))
      shared expected
      haone hbone haodd hbodd hab rfl hrecombine
    iexact Htrue

/-- Complete small-step/Iris specification of the optimized exported
`gcd_u64`.  The theorem is partial correctness, matching iris-lean's current
adequacy boundary; the legacy total theorem below remains only until the
termination ledger is cut over. -/
theorem mod3_gcd_smallStep (a b : UInt64) :
    PartiallyMeets (gcdConfig a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  apply wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [gcdConfig]
  rw [show func0 =
    [.localGet 1, .localGet 0, .orI64, .localSet 2,
      .block 0 0 gcdOuterBody, .localGet 2] from rfl]
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_orI64
  inext
  iapply wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply wp_block
  inext
  simp only [gcdOuterBody, List.drop_nil]
  iapply wp_localGet rfl
  inext
  by_cases ha : a = 0
  · subst a
    iapply wp_eqzI64 (result := 1) (by decide)
    inext
    iapply wp_brIf (by decide) rfl
    inext
    simp only [List.take_nil, List.nil_append]
    iapply wp_localGet rfl
    inext
    iapply wp_finish
    inext
    iapply wp_value'
    ipureintro
    simp
  · iapply wp_eqzI64 (result := 0) (by rw [if_neg ha])
    inext
    iapply wp_brIfZero
    inext
    iapply wp_localGet rfl
    inext
    by_cases hb : b = 0
    · subst b
      iapply wp_eqzI64 (result := 1) (by decide)
      inext
      iapply wp_brIf (by decide) rfl
      inext
      simp only [List.take_nil, List.nil_append]
      iapply wp_localGet rfl
      inext
      iapply wp_finish
      inext
      iapply wp_value'
      ipureintro
      simp
    · iapply wp_eqzI64 (result := 0) (by rw [if_neg hb])
      inext
      iapply wp_brIfZero
      inext
      iapply wp_localGet rfl
      inext
      iapply wp_ctzI64
      inext
      iapply wp_localSet rfl
      inext
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
        List.set]
      iapply wp_block
      inext
      simp only [List.drop_nil]
      rw [show
        ({ kind := .block
           paramArity := 0
           resultArity := 0
           body := innerBody
           continuation := [.localGet 0, .localGet 2, .shlI64, .localSet 2]
           belowStack := [] } : ControlFrame) =
          gcdInnerFrame from rfl]
      rw [show
        ({ kind := .block
           paramArity := 0
           resultArity := 0
           body :=
             [ .localGet 0, .eqzI64, .br_if 0,
               .localGet 1, .eqzI64, .br_if 0,
               .localGet 2, .ctzI64, .localSet 2,
               .block 0 0 innerBody,
               .localGet 0, .localGet 2, .shlI64, .localSet 2 ]
           continuation := [.localGet 2]
           belowStack := [] } : ControlFrame) =
          gcdOuterFrame gcdOuterBody from rfl]
      iapply gcdInner_smallStep_wp gcdOuterBody a b
        (UInt64.ofNat (ctz64 64 (b ||| a)))
        (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ha hb
      · intro g hg
        apply UInt64.recombine_loop a b g ha hb
        rw [Nat.gcd_self, hg]
        rw [oddPart_toNat, oddPart_toNat]
      · itrivial

/-- The first early-zero path has a uniform finite small-step trace.  This is
the first total-correctness bridge used by the termination ledger: it refers
only to the executable small-step iterator and its proved relational
adequacy. -/
theorem mod3_gcd_left_zero_smallStep_terminates (b : UInt64) :
    SmallStep.TerminatesWith (gcdConfig 0 b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd 0 b.toNat))]) := by
  refine ⟨[.instruction (.localGet 1), .instruction (.localGet 0),
      .instruction .orI64, .instruction (.localSet 2),
      .instruction (.block 0 0 gcdOuterBody),
      .instruction (.localGet 0), .instruction .eqzI64,
      .instruction (.br_if 0), .instruction (.localGet 2),
      .administrative .finish],
    [.i64 b], (gcdConfig 0 b).store, ?_, by simp⟩
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .orI64
  apply Steps.cons (.localSet rfl)
  simp only [UInt64.or_zero]
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqzI64 (result := 1) (value := 0) rfl)
  apply Steps.cons (.brIf (condition := 1)
    (targetCode := [.localGet 2]) (targetControl := [])
    (targetValues := []) (by decide) rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .finish
  exact .refl _

/-- Symmetric early-zero finite trace. -/
theorem mod3_gcd_right_zero_smallStep_terminates (a : UInt64) :
    SmallStep.TerminatesWith (gcdConfig a 0)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat 0))]) := by
  by_cases ha : a = 0
  · subst a
    simpa using mod3_gcd_left_zero_smallStep_terminates 0
  · refine ⟨[.instruction (.localGet 1), .instruction (.localGet 0),
        .instruction .orI64, .instruction (.localSet 2),
        .instruction (.block 0 0 gcdOuterBody),
        .instruction (.localGet 0), .instruction .eqzI64,
        .instruction (.br_if 0), .instruction (.localGet 1),
        .instruction .eqzI64, .instruction (.br_if 0),
        .instruction (.localGet 2), .administrative .finish],
      [.i64 a], (gcdConfig a 0).store, ?_, by simp⟩
    apply Steps.cons (.localGet rfl)
    apply Steps.cons (.localGet rfl)
    apply Steps.cons .orI64
    apply Steps.cons (.localSet rfl)
    simp only [UInt64.zero_or]
    apply Steps.cons .block
    apply Steps.cons (.localGet rfl)
    apply Steps.cons (.eqzI64 (result := 0) (value := a) (by simp [ha]))
    apply Steps.cons .brIfZero
    apply Steps.cons (.localGet rfl)
    apply Steps.cons (.eqzI64 (result := 1) (value := 0) rfl)
    apply Steps.cons (.brIf (condition := 1)
      (targetCode := [.localGet 2]) (targetControl := [])
      (targetValues := []) (by decide) rfl)
    apply Steps.cons (.localGet rfl)
    apply Steps.cons .finish
    exact .refl _

/-- Both generated early exits are total in the relational small-step
semantics, with no appeal to the retained big-step interpreter. -/
theorem mod3_gcd_zero_smallStep_terminates
    (a b : UInt64) (hz : a = 0 ∨ b = 0) :
    SmallStep.TerminatesWith (gcdConfig a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  rcases hz with rfl | rfl
  · exact mod3_gcd_left_zero_smallStep_terminates b
  · exact mod3_gcd_right_zero_smallStep_terminates a

/-- Machine state at the head of the generated subtract-and-halve loop. -/
def gcdLoopConfig (x y shared : UInt64) : Config Unit :=
  { expr := .running
      ⟨⟨[.i64 x, .i64 y], [.i64 shared], []⟩,
        loopBody, 1, [],
        [gcdLoopFrame, gcdInnerFrame, gcdOuterFrame gcdOuterBody], []⟩
    store := (gcdConfig x y).store }

/-- State at entry to the odd-part normalization block. -/
def gcdInnerConfig (p0 p1 shared : UInt64) : Config Unit :=
  { expr := .running
      ⟨⟨[.i64 p0, .i64 p1], [.i64 shared], []⟩,
        innerBody, 1, [],
        [gcdInnerFrame, gcdOuterFrame gcdOuterBody], []⟩
    store := (gcdConfig p0 p1).store }

/-- Nonzero operands pass the two generated early checks and enter the
odd-part normalization block. -/
theorem gcd_nonzero_setup_steps
    (a b : UInt64) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ trace, Steps (gcdConfig a b) trace
      (gcdInnerConfig a b (UInt64.ofNat (ctz64 64 (b ||| a)))) := by
  refine ⟨[
    .instruction (.localGet 1), .instruction (.localGet 0),
    .instruction .orI64, .instruction (.localSet 2),
    .instruction (.block 0 0 gcdOuterBody),
    .instruction (.localGet 0), .instruction .eqzI64,
    .instruction (.br_if 0), .instruction (.localGet 1),
    .instruction .eqzI64, .instruction (.br_if 0),
    .instruction (.localGet 2), .instruction .ctzI64,
    .instruction (.localSet 2),
    .instruction (.block 0 0 innerBody)], ?_⟩
  simp only [gcdConfig, gcdInnerConfig, func0]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .orI64
  apply Steps.cons (.localSet rfl)
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqzI64 (result := 0) (by simp [ha]))
  apply Steps.cons .brIfZero
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqzI64 (result := 0) (by simp [hb]))
  apply Steps.cons .brIfZero
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .ctzI64
  apply Steps.cons (.localSet rfl)
  exact Steps.single .block

/-- Odd-part normalization followed by the unequal fast-path enters the loop
head used by `gcdLoop_terminates`. -/
theorem gcdInner_to_loop_steps
    (p0 p1 shared : UInt64)
    (hne :
      p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64) ≠
      p1 >>> (UInt64.ofNat (ctz64 64 p1) % 64)) :
    ∃ trace, Steps (gcdInnerConfig p0 p1 shared) trace
      (gcdLoopConfig
        (p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64))
        (p1 >>> (UInt64.ofNat (ctz64 64 p1) % 64))
        shared) := by
  refine ⟨[
    .instruction (.localGet 0), .instruction (.localGet 0),
    .instruction .ctzI64, .instruction .shrUI64,
    .instruction (.localSet 0), .instruction (.localGet 0),
    .instruction (.localGet 1), .instruction (.localGet 1),
    .instruction .ctzI64, .instruction .shrUI64,
    .instruction (.localSet 1), .instruction (.localGet 1),
    .instruction .eqI64, .instruction (.br_if 0),
    .instruction (.loop 0 0 loopBody)], ?_⟩
  simp only [gcdInnerConfig, gcdLoopConfig, innerBody]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .ctzI64
  apply Steps.cons .shrUI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .ctzI64
  apply Steps.cons .shrUI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqI64 (result := 0) (by simp [hne]))
  apply Steps.cons .brIfZero
  exact Steps.single .loop

/-- Equal odd parts bypass the loop and complete the recombination tail. -/
theorem gcdInner_equal_steps
    (p0 p1 shared : UInt64)
    (heq :
      p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64) =
      p1 >>> (UInt64.ofNat (ctz64 64 p1) % 64)) :
    ∃ trace, Steps (gcdInnerConfig p0 p1 shared) trace
      ⟨.done
        [.i64 ((p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64)) <<<
          (shared % 64))],
        (gcdInnerConfig p0 p1 shared).store⟩ := by
  refine ⟨[
    .instruction (.localGet 0), .instruction (.localGet 0),
    .instruction .ctzI64, .instruction .shrUI64,
    .instruction (.localSet 0), .instruction (.localGet 0),
    .instruction (.localGet 1), .instruction (.localGet 1),
    .instruction .ctzI64, .instruction .shrUI64,
    .instruction (.localSet 1), .instruction (.localGet 1),
    .instruction .eqI64, .instruction (.br_if 0),
    .instruction (.localGet 0), .instruction (.localGet 2),
    .instruction .shlI64, .instruction (.localSet 2),
    .administrative .exitControl, .instruction (.localGet 2),
    .administrative .finish], ?_⟩
  simp only [gcdInnerConfig, innerBody]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .ctzI64
  apply Steps.cons .shrUI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .ctzI64
  apply Steps.cons .shrUI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqI64 (result := 1) (by rw [if_pos heq]))
  apply Steps.cons (.brIf (by decide) rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .shlI64
  apply Steps.cons (.localSet rfl)
  apply Steps.cons (.exitControl rfl)
  apply Steps.cons (.localGet rfl)
  exact Steps.single .finish

/-- One decreasing loop iteration for the `x > y` arm, stopping exactly at
the next loop head. -/
theorem gcdLoop_step_x
    (x y shared : UInt64) (hgt : y < x)
    (hnext : (x - y) >>>
      (UInt64.ofNat (ctz64 64 (x - y)) % 64) ≠ y) :
    ∃ trace, Steps (gcdLoopConfig x y shared) trace
      (gcdLoopConfig
        ((x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64))
        y shared) := by
  refine ⟨[
    .instruction (.block 0 0
      [ .localGet 0, .localGet 1, .gtUI64, .br_if 0,
        .localGet 0, .localGet 1, .localGet 0, .subI64, .localSet 1,
        .localGet 1, .localGet 1, .ctzI64, .shrUI64, .localSet 1,
        .localGet 1, .eqI64, .br_if 2, .br 1 ]),
    .instruction (.localGet 0), .instruction (.localGet 1),
    .instruction .gtUI64, .instruction (.br_if 0),
    .instruction (.localGet 0), .instruction (.localGet 1),
    .instruction .subI64, .instruction (.localSet 0),
    .instruction (.localGet 0), .instruction (.localGet 0),
    .instruction .ctzI64, .instruction .shrUI64,
    .instruction (.localSet 0), .instruction (.localGet 0),
    .instruction (.localGet 1), .instruction .neI64,
    .instruction (.br_if 0)], ?_⟩
  simp only [gcdLoopConfig, loopBody]
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.gtUI64 (result := 1) (by simp [hgt]))
  apply Steps.cons (.brIf (by decide) rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .subI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .ctzI64
  apply Steps.cons .shrUI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.neI64 (result := 1) (by simp [hnext]))
  exact Steps.single (.brIf (by decide) rfl)

/-- Symmetric decreasing iteration for the `x < y` arm. -/
theorem gcdLoop_step_y
    (x y shared : UInt64) (hgt : ¬y < x)
    (hnext : x ≠ (y - x) >>>
      (UInt64.ofNat (ctz64 64 (y - x)) % 64)) :
    ∃ trace, Steps (gcdLoopConfig x y shared) trace
      (gcdLoopConfig x
        ((y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64))
        shared) := by
  refine ⟨[
    .instruction (.block 0 0
      [ .localGet 0, .localGet 1, .gtUI64, .br_if 0,
        .localGet 0, .localGet 1, .localGet 0, .subI64, .localSet 1,
        .localGet 1, .localGet 1, .ctzI64, .shrUI64, .localSet 1,
        .localGet 1, .eqI64, .br_if 2, .br 1 ]),
    .instruction (.localGet 0), .instruction (.localGet 1),
    .instruction .gtUI64, .instruction (.br_if 0),
    .instruction (.localGet 0), .instruction (.localGet 1),
    .instruction (.localGet 0), .instruction .subI64,
    .instruction (.localSet 1), .instruction (.localGet 1),
    .instruction (.localGet 1), .instruction .ctzI64,
    .instruction .shrUI64, .instruction (.localSet 1),
    .instruction (.localGet 1), .instruction .eqI64,
    .instruction (.br_if 2), .instruction (.br 1)], ?_⟩
  simp only [gcdLoopConfig, loopBody]
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.gtUI64 (result := 0) (by simp [hgt]))
  apply Steps.cons .brIfZero
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .subI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .ctzI64
  apply Steps.cons .shrUI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqI64 (result := 0) (by simp [hnext]))
  apply Steps.cons .brIfZero
  exact Steps.single (.br rfl)

/-- The equality exit reached by the `x > y` arm completes the enclosing
loop, inner block, and outer recombination frame. -/
theorem gcdLoop_exit_x
    (x y shared : UInt64) (hgt : y < x)
    (hnext : (x - y) >>>
      (UInt64.ofNat (ctz64 64 (x - y)) % 64) = y) :
    ∃ trace, Steps (gcdLoopConfig x y shared) trace
      ⟨.done [.i64 (y <<< (shared % 64))],
        (gcdLoopConfig x y shared).store⟩ := by
  refine ⟨[
    .instruction (.block 0 0
      [ .localGet 0, .localGet 1, .gtUI64, .br_if 0,
        .localGet 0, .localGet 1, .localGet 0, .subI64, .localSet 1,
        .localGet 1, .localGet 1, .ctzI64, .shrUI64, .localSet 1,
        .localGet 1, .eqI64, .br_if 2, .br 1 ]),
    .instruction (.localGet 0), .instruction (.localGet 1),
    .instruction .gtUI64, .instruction (.br_if 0),
    .instruction (.localGet 0), .instruction (.localGet 1),
    .instruction .subI64, .instruction (.localSet 0),
    .instruction (.localGet 0), .instruction (.localGet 0),
    .instruction .ctzI64, .instruction .shrUI64,
    .instruction (.localSet 0), .instruction (.localGet 0),
    .instruction (.localGet 1), .instruction .neI64,
    .instruction (.br_if 0), .administrative .exitControl,
    .instruction (.localGet 1), .instruction (.localSet 0),
    .administrative .exitControl, .instruction (.localGet 0),
    .instruction (.localGet 2), .instruction .shlI64,
    .instruction (.localSet 2), .administrative .exitControl,
    .instruction (.localGet 2), .administrative .finish], ?_⟩
  simp only [gcdLoopConfig, loopBody]
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.gtUI64 (result := 1) (by simp [hgt]))
  apply Steps.cons (.brIf (by decide) rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .subI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .ctzI64
  apply Steps.cons .shrUI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.neI64 (result := 0) (by simp [hnext]))
  apply Steps.cons .brIfZero
  apply Steps.cons (.exitControl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.exitControl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .shlI64
  apply Steps.cons (.localSet rfl)
  apply Steps.cons (.exitControl rfl)
  apply Steps.cons (.localGet rfl)
  exact Steps.single .finish

/-- Symmetric equality exit reached by the `x < y` arm. -/
theorem gcdLoop_exit_y
    (x y shared : UInt64) (hgt : ¬y < x)
    (hnext : x = (y - x) >>>
      (UInt64.ofNat (ctz64 64 (y - x)) % 64)) :
    ∃ trace, Steps (gcdLoopConfig x y shared) trace
      ⟨.done [.i64 (x <<< (shared % 64))],
        (gcdLoopConfig x y shared).store⟩ := by
  refine ⟨[
    .instruction (.block 0 0
      [ .localGet 0, .localGet 1, .gtUI64, .br_if 0,
        .localGet 0, .localGet 1, .localGet 0, .subI64, .localSet 1,
        .localGet 1, .localGet 1, .ctzI64, .shrUI64, .localSet 1,
        .localGet 1, .eqI64, .br_if 2, .br 1 ]),
    .instruction (.localGet 0), .instruction (.localGet 1),
    .instruction .gtUI64, .instruction (.br_if 0),
    .instruction (.localGet 0), .instruction (.localGet 1),
    .instruction (.localGet 0), .instruction .subI64,
    .instruction (.localSet 1), .instruction (.localGet 1),
    .instruction (.localGet 1), .instruction .ctzI64,
    .instruction .shrUI64, .instruction (.localSet 1),
    .instruction (.localGet 1), .instruction .eqI64,
    .instruction (.br_if 2), .instruction (.localGet 0),
    .instruction (.localGet 2), .instruction .shlI64,
    .instruction (.localSet 2), .administrative .exitControl,
    .instruction (.localGet 2), .administrative .finish], ?_⟩
  simp only [gcdLoopConfig, loopBody]
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.gtUI64 (result := 0) (by simp [hgt]))
  apply Steps.cons .brIfZero
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .subI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .ctzI64
  apply Steps.cons .shrUI64
  apply Steps.cons (.localSet rfl)
  simp only [List.set]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqI64 (result := 1) (by rw [if_pos hnext]))
  apply Steps.cons (.brIf (by decide) rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .shlI64
  apply Steps.cons (.localSet rfl)
  apply Steps.cons (.exitControl rfl)
  apply Steps.cons (.localGet rfl)
  exact Steps.single .finish

/-- Well-founded termination of the generated subtract-and-halve loop.  The
measure is the sum of the two positive odd operands; semantic correctness is
kept out of this theorem and supplied independently by Iris. -/
theorem gcdLoop_terminates
    (x y shared : UInt64)
    (hxne : x ≠ 0) (hyne : y ≠ 0)
    (hxodd : x.toNat % 2 = 1) (hyodd : y.toNat % 2 = 1)
    (hxyne : x ≠ y) :
    SmallStep.TerminatesWith (gcdLoopConfig x y shared)
      (fun _ _ => True) := by
  induction hmeasure : x.toNat + y.toNat using Nat.strong_induction_on
      generalizing x y with
  | h n ih =>
    subst n
    by_cases hgt : y < x
    · let x' :=
        (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64)
      obtain ⟨hx'ne, hx'odd, _hgcd, hdec⟩ :=
        UInt64.stein_step_x x y hxne hyne hxodd hyodd hgt
      by_cases hx'y : x' = y
      · obtain ⟨trace, execution⟩ :=
          gcdLoop_exit_x x y shared hgt (by simpa [x'] using hx'y)
        exact TerminatesWith.of_steps execution trivial
      · obtain ⟨initialTrace, initial⟩ :=
          gcdLoop_step_x x y shared hgt (by simpa [x'] using hx'y)
        have hdecrease : x'.toNat + y.toNat < x.toNat + y.toNat := by
          simpa [x', oddPart_toNat] using hdec
        have hx'odd' : x'.toNat % 2 = 1 := by
          simpa [x', oddPart_toNat] using hx'odd
        have suffix := ih (x'.toNat + y.toNat) hdecrease
          x' y hx'ne hyne hx'odd' hyodd hx'y rfl
        exact TerminatesWith.prependSteps initial suffix
    · let y' :=
        (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64)
      obtain ⟨hy'ne, hy'odd, _hgcd, hdec⟩ :=
        UInt64.stein_step_y x y hxne hyne hxodd hyodd hgt hxyne
      by_cases hxy' : x = y'
      · obtain ⟨trace, execution⟩ :=
          gcdLoop_exit_y x y shared hgt (by simpa [y'] using hxy')
        exact TerminatesWith.of_steps execution trivial
      · obtain ⟨initialTrace, initial⟩ :=
          gcdLoop_step_y x y shared hgt (by simpa [y'] using hxy')
        have hdecrease : x.toNat + y'.toNat < x.toNat + y.toNat := by
          simpa [y', oddPart_toNat] using hdec
        have hy'odd' : y'.toNat % 2 = 1 := by
          simpa [y', oddPart_toNat] using hy'odd
        have suffix := ih (x.toNat + y'.toNat) hdecrease
          x y' hxne hy'ne hxodd hy'odd' hxy' rfl
        exact TerminatesWith.prependSteps initial suffix

/-- Finite termination of the complete optimized body. -/
theorem mod3_gcd_smallStep_termination (a b : UInt64) :
    SmallStep.TerminatesWith (gcdConfig a b) (fun _ _ => True) := by
  by_cases ha : a = 0
  · subst a
    exact (mod3_gcd_left_zero_smallStep_terminates b).mono
      (fun _ _ _ => trivial)
  · by_cases hb : b = 0
    · subst b
      exact (mod3_gcd_right_zero_smallStep_terminates a).mono
        (fun _ _ _ => trivial)
    · let shared := UInt64.ofNat (ctz64 64 (b ||| a))
      let ao := a >>> (UInt64.ofNat (ctz64 64 a) % 64)
      let bo := b >>> (UInt64.ofNat (ctz64 64 b) % 64)
      obtain ⟨setupTrace, setup⟩ :=
        gcd_nonzero_setup_steps a b ha hb
      change Steps (gcdConfig a b) setupTrace
        (gcdInnerConfig a b shared) at setup
      by_cases hab : ao = bo
      · obtain ⟨finishTrace, finish⟩ :=
          gcdInner_equal_steps a b shared (by simpa [ao, bo] using hab)
        exact TerminatesWith.prependSteps setup
          (TerminatesWith.of_steps finish trivial)
      · obtain ⟨innerTrace, inner⟩ :=
          gcdInner_to_loop_steps a b shared
            (by simpa [ao, bo] using hab)
        change Steps (gcdInnerConfig a b shared) innerTrace
          (gcdLoopConfig ao bo shared) at inner
        have haone : ao ≠ 0 := by
          exact UInt64.shr_ctz_ne_zero a ha
        have hbone : bo ≠ 0 := by
          exact UInt64.shr_ctz_ne_zero b hb
        have haodd : ao.toNat % 2 = 1 := by
          simpa [ao, oddPart_toNat] using
            UInt64.shr_ctz_toNat_odd a ha
        have hbodd : bo.toNat % 2 = 1 := by
          simpa [bo, oddPart_toNat] using
            UInt64.shr_ctz_toNat_odd b hb
        have loopTermination :=
          gcdLoop_terminates ao bo shared
            haone hbone haodd hbodd hab
        exact TerminatesWith.prependSteps setup
          (TerminatesWith.prependSteps inner loopTermination)

/-- Total correctness recovered by combining the finite-trace termination
argument with the Iris partial-correctness theorem. -/
theorem mod3_gcd_smallStep_total (a b : UInt64) :
    SmallStep.TerminatesWith (gcdConfig a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) :=
  TerminatesWith.of_termination_and_partial
    (mod3_gcd_smallStep_termination a b)
    (mod3_gcd_smallStep a b)

/-- Running the inner block from two nonzero operands leaves local 0 holding
the gcd of their odd parts, local 2 untouched, and the store unchanged, at
either a fall-through or a `Break 0`. -/
theorem inner_wp (env : HostEnv Unit) (st0 : Store Unit) (shared p0 p1 : UInt64)
    (vs0 : List Value) (Q : Continuation Unit → Prop)
    (hp0 : p0 ≠ 0) (hp1 : p1 ≠ 0)
    (hQ : ∀ (g gy : UInt64),
        g.toNat = Nat.gcd (p0.toNat >>> (ctz64 64 p0 % 64)) (p1.toNat >>> (ctz64 64 p1 % 64)) →
        Q (.Fallthrough st0 { params := [.i64 g, .i64 gy], locals := [.i64 shared], values := vs0 }) ∧
        Q (.Break 0 st0 { params := [.i64 g, .i64 gy], locals := [.i64 shared], values := vs0 })) :
    wp «module» innerBody Q st0
      { params := [.i64 p0, .i64 p1], locals := [.i64 shared], values := vs0 } env := by
  unfold innerBody
  drive
  set ao : UInt64 := p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64) with hao_def
  set bo : UInt64 := p1 >>> (UInt64.ofNat (ctz64 64 p1) % 64) with hbo_def
  have haone : ao ≠ 0 := UInt64.shr_ctz_ne_zero p0 hp0
  have hbone : bo ≠ 0 := UInt64.shr_ctz_ne_zero p1 hp1
  have haodd : ao.toNat % 2 = 1 := UInt64.shr_ctz_toNat_odd p0 hp0
  have hbodd : bo.toNat % 2 = 1 := UInt64.shr_ctz_toNat_odd p1 hp1
  have haN : ao.toNat = p0.toNat >>> (ctz64 64 p0 % 64) := oddPart_toNat p0
  have hbN : bo.toNat = p1.toNat >>> (ctz64 64 p1 % 64) := oddPart_toNat p1
  by_cases hab : ao = bo
  · -- Odd parts already equal: break out with local 0 = ao.
    rw [if_pos hab]
    exact (hQ ao bo (by rw [← haN, ← hbN, ← hab, Nat.gcd_self])).2
  · -- Odd parts differ: run the subtract-and-halve loop.
    rw [if_neg hab]
    pick
    apply wp_loop_cons
      (Inv := fun st s =>
        st = st0 ∧ ∃ x y : UInt64,
          s = { params := [.i64 x, .i64 y], locals := [.i64 shared], values := vs0 } ∧
          x ≠ 0 ∧ y ≠ 0 ∧ x.toNat % 2 = 1 ∧ y.toNat % 2 = 1 ∧ x ≠ y ∧
          Nat.gcd x.toNat y.toNat = Nat.gcd ao.toNat bo.toNat)
      (μ := fun _ s => match s.params with | [.i64 x, .i64 y] => x.toNat + y.toNat | _ => 0)
    · exact ⟨rfl, ao, bo, rfl, haone, hbone, haodd, hbodd, hab, rfl⟩
    · rintro st s ⟨rfl, x, y, rfl, hxne, hyne, hxodd, hyodd, hxyne, hgcd⟩
      unfold loopBody
      apply wp_block_cons
      drive
      by_cases hgt : y < x
      · -- x > y: fall through the inner block to the x-branch (x := oddPart (x - y)).
        rw [if_pos hgt]
        pick
        obtain ⟨hne', hodd', hgcd', hdec⟩ := UInt64.stein_step_x x y hxne hyne hxodd hyodd hgt
        by_cases hxy2 : (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64) = y
        · -- x' = y: the loop falls through; copy y into local 0 and finish.
          rw [if_neg (not_not_intro hxy2)]
          pick
          refine (hQ y y ?_).1
          have hh : (x - y).toNat >>> (ctz64 64 (x - y) % 64) = y.toNat := by
            rw [← oddPart_toNat, hxy2]
          rw [← haN, ← hbN, ← hgcd, ← hgcd', hh, Nat.gcd_self]
        · -- x' ≠ y: continue the loop with (x', y).
          rw [if_pos hxy2]
          pick
          refine ⟨⟨trivial, _, y, rfl, hne', hyne, ?_, hyodd, hxy2, ?_⟩, ?_⟩
          · rw [oddPart_toNat]; exact hodd'
          · rw [oddPart_toNat]; exact hgcd'.trans hgcd
          · rw [oddPart_toNat]; omega
      · -- x < y: stay in the inner block, y-branch (y := oddPart (y - x)).
        rw [if_neg hgt]
        pick
        obtain ⟨hne', hodd', hgcd', hdec⟩ := UInt64.stein_step_y x y hxne hyne hxodd hyodd hgt hxyne
        by_cases hxy2 : x = (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64)
        · -- x = y': break out of the loop with local 0 = x.
          rw [if_pos hxy2]
          pick
          refine (hQ x ((y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64)) ?_).2
          have hh : (y - x).toNat >>> (ctz64 64 (y - x) % 64) = x.toNat := by
            rw [← oddPart_toNat, ← hxy2]
          rw [← haN, ← hbN, ← hgcd, ← hgcd', hh, Nat.gcd_self]
        · -- x ≠ y': continue the loop with (x, y').
          rw [if_neg hxy2]
          pick
          refine ⟨⟨trivial, x, _, rfl, hxne, hne', hxodd, ?_, hxy2, ?_⟩, ?_⟩
          · rw [oddPart_toNat]; exact hodd'
          · rw [oddPart_toNat]; exact hgcd'.trans hgcd
          · rw [oddPart_toNat]; omega

/-- Public fuel-free specification of the optimized exported `gcd_u64`.
Unlike the retained compatibility theorem below, this contract is stated
entirely over the authoritative small-step machine. -/
@[spec_of "rust-exported" "num_integer_opt3::gcd_u64"]
def GcdU64Spec : Prop :=
  ∀ (a b : UInt64),
    SmallStep.TerminatesWith (gcdConfig a b)
      (fun rs _store =>
        rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])

@[proves Project.NumIntegerOpt3.Spec.GcdU64Spec]
theorem gcd_u64_correct : GcdU64Spec :=
  mod3_gcd_smallStep_total

/-- The exported `gcd_u64` (func 0) computes the gcd of its two operands and
leaves the store untouched. This legacy theorem is retained only as a
termination-ledger compatibility artifact; public spec discovery uses
`GcdU64Spec`. -/
theorem mod3_gcd (env : HostEnv Unit) (st0 : Store Unit) (a b : UInt64) :
    TerminatesWith env «module» 0 st0 [.i64 a, .i64 b]
      (fun st vs => vs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))] ∧ st = st0) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  unfold func0Def func0
  drive
  apply wp_block_cons
  drive
  by_cases hb : b = 0
  · -- b = 0: exit early, the result `a ||| b = a ||| 0 = a = gcd a 0`.
    rw [if_pos hb]
    pick
    subst hb
    refine ⟨?_, trivial⟩
    rw [show UInt64.toNat 0 = 0 from rfl, Nat.gcd_zero_right, UInt64.ofNat_toNat,
        show a ||| (0 : UInt64) = a from by apply UInt64.toNat.inj; rw [UInt64.toNat_or]; simp]
  · rw [if_neg hb]
    pick
    by_cases ha : a = 0
    · -- a = 0: exit early, the result `a ||| b = 0 ||| b = b = gcd 0 b`.
      rw [if_pos ha]
      pick
      subst ha
      refine ⟨?_, trivial⟩
      rw [show UInt64.toNat 0 = 0 from rfl, Nat.gcd_zero_left, UInt64.ofNat_toNat,
          show (0 : UInt64) ||| b = b from by apply UInt64.toNat.inj; rw [UInt64.toNat_or]; simp]
    · -- both nonzero: compute the shared power of two, run the inner block, recombine.
      rw [if_neg ha]
      pick
      apply wp_block_cons
      refine inner_wp env st0 _ b a [] _ hb ha ?_
      intro g gy hg
      have hrec : g <<< (UInt64.ofNat (ctz64 64 (a ||| b)) % 64)
          = UInt64.ofNat (Nat.gcd a.toNat b.toNat) := by
        rw [UInt64.recombine_loop b a g hb ha (by rw [Nat.gcd_self]; exact hg), Nat.gcd_comm]
      constructor <;> (drive; exact ⟨by rw [hrec], trivial⟩)

end Project.NumIntegerOpt3.Spec
