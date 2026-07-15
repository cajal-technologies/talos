import Project.NumIntegerOpt3.Program

namespace Project.NumIntegerOpt3.Spec

open Wasm

set_option maxRecDepth 1048576

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

/-- The exported `gcd_u64` (func 0) computes the gcd of its two operands and
leaves the store untouched — it is pure register code. -/
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
