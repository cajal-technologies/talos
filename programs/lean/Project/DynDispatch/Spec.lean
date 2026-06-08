import Project.DynDispatch.Program

set_option maxRecDepth 1048576

/-! # Specification for the `dyn_dispatch` crate

The exported `check(sel, x)` runs two implementations of the same
dispatcher and traps via `unreachable` iff they disagree:

* `dispatch_dyn` (`func0`): looks up `OPS[sel % 2]` (a static array of
  `&dyn Op`) and calls `.apply(x)` through the vtable. Compiles to
  `call_indirect (type N)` — exactly the wasm instruction this crate
  exists to exercise.
* `dispatch_naive` (`func1`): an inline `match`/`select` that names the
  concrete `Add(1)` / `Mul(2)` impls directly.

`func2` calls both, compares the results with `i32.ne`, and `br_if`s to
an `unreachable` when they differ; `func5` is the exported `check`
wrapper. Proving `check` terminates without trapping for every
`(sel, x)` is therefore exactly the claim that the indirect dispatch
agrees with the direct one — a property of `call_indirect`-through-a-vtable.

The spec is pinned to the module's `initialStore`: `dispatch_dyn` reads
the `OPS`/vtable pointers out of *static* linear memory and resolves the
call through the preinitialised function table, so the equivalence is
meaningless (indeed false) over an arbitrary store. The end-to-end chain
— memory-backed vtable read + table lookup + chained call — is discharged
with `wp_callIndirect_tw` / `wp_call_tw`, the store-specific call WP rules. -/

namespace Project.DynDispatch.Spec

open Wasm

/-- The module's canonical initial store: linear memory holds the folded
`OPS`/vtable data segment and `table[0]` is filled by the element segment
(`[none, some 3, some 4]`). -/
private abbrev S : Store Unit := «module».initialStore

/-- The value both dispatchers compute: `x + 1` for even `sel` (the
`Add(1)` op) and `x * 2` for odd `sel` (the `Mul(2)` op). -/
private def dispatchResult (sel x : UInt32) : UInt32 :=
  if sel &&& 1 = 0 then x + 1 else x * 2

/-! ## Callees: the two `Op::apply` implementations -/

/-- `func3` is `<Add as Op>::apply`: loads the boxed inner value at
`*self` and adds the i32 argument. Holds over any store large enough to
contain the 4-byte load. -/
private theorem add_apply (initial : Store Unit) (p x : UInt32)
    (hMem : p.toNat + 4 ≤ initial.mem.pages * 65536) :
    TerminatesWith ({} : HostEnv Unit) «module» 3 initial [.i32 x, .i32 p]
      (fun st rs => rs = [.i32 (initial.mem.read32 p + x)] ∧ st = initial) := by
  apply TerminatesWith.of_wp_entry_for
    (f := { params := [.i32, .i32], locals := [], body := func3, results := [.i32] }) rfl
  unfold func3
  wp_run
  simp [UInt32.add_comm]
  exact hMem

/-- `func4` is `<Mul as Op>::apply`: loads the boxed inner value at
`*self` and multiplies the i32 argument by it. -/
private theorem mul_apply (initial : Store Unit) (p x : UInt32)
    (hMem : p.toNat + 4 ≤ initial.mem.pages * 65536) :
    TerminatesWith ({} : HostEnv Unit) «module» 4 initial [.i32 x, .i32 p]
      (fun st rs => rs = [.i32 (initial.mem.read32 p * x)] ∧ st = initial) := by
  apply TerminatesWith.of_wp_entry_for
    (f := { params := [.i32, .i32], locals := [], body := func4, results := [.i32] }) rfl
  unfold func4
  wp_run
  simp [UInt32.mul_comm]
  exact hMem

/-! ## `dispatch_dyn` (`func0`): indirect dispatch through the vtable -/

/-- The indirect dispatcher resolves `apply` through the in-memory vtable
and returns `dispatchResult sel x`. Even `sel` reads `self = 1048576`
(boxed value `1`) and resolves through `table[1] → func3`; odd `sel`
reads `self = 1048596` (boxed value `2`) and resolves through
`table[2] → func4`. -/
private theorem dispatch_dyn (sel x : UInt32) :
    TerminatesWith ({} : HostEnv Unit) «module» 0 S [.i32 x, .i32 sel]
      (fun st rs => rs = [.i32 (dispatchResult sel x)] ∧ st = S) := by
  apply TerminatesWith.of_wp_entry_for
    (f := { params := [.i32, .i32], locals := [], body := func0, results := [.i32] }) rfl
  unfold func0
  wp_run
  simp [dispatchResult]
  -- After symbolic execution: three load-bounds checks and a `wp` on the
  -- trailing `call_indirect`. The selector's low bit picks the `Op`.
  have hsa : (1 &&& sel).toNat = sel.toNat % 2 := by simp [UInt32.toNat_and]
  rw [UInt32.and_comm sel 1]
  rcases Nat.mod_two_eq_zero_or_one sel.toNat with hpar | hpar
  · -- Even `sel`: vtable slot 1 → `func3` (`Add(1).apply`), `self = 1048576`.
    have hv : 1 &&& sel = 0 := UInt32.toNat.inj (by simp [hsa, hpar])
    rw [hpar, hv]
    refine ⟨by native_decide, by native_decide, by native_decide, ?_⟩
    rw [show S.mem.read32 ((0 : UInt32) <<< 3 + 1048616) = 1048576 from by native_decide,
        show S.mem.read32 ((0 : UInt32) <<< 3 + 1048620) = 1048580 from by native_decide,
        show S.mem.read32 ((1048580 : UInt32) + 12) = 1 from by native_decide]
    apply wp_callIndirect_tw
      (i := 1) (vs0 := [.i32 x, .i32 1048576])
      (tbl := [none, some 3, some 4]) (fid := 3)
      (fn := { params := [.i32, .i32], locals := [], body := func3, results := [.i32] })
      (ty := { params := [.i32, .i32], results := [.i32] })
      (Post := fun st rs => rs = [.i32 (S.mem.read32 1048576 + x)] ∧ st = S)
    · rfl
    · native_decide
    · decide
    · rfl
    · rfl
    · exact ⟨rfl, rfl⟩
    · exact add_apply S 1048576 x (by native_decide)
    · rintro st' vs ⟨rfl, rfl⟩
      wp_run
      rw [show S.mem.read32 1048576 = 1 from by native_decide]
      simp [UInt32.add_comm]
  · -- Odd `sel`: vtable slot 2 → `func4` (`Mul(2).apply`), `self = 1048596`.
    have hv : 1 &&& sel = 1 := UInt32.toNat.inj (by simp [hsa, hpar])
    rw [hpar, hv]
    refine ⟨by native_decide, by native_decide, by native_decide, ?_⟩
    rw [show S.mem.read32 ((1 : UInt32) <<< 3 + 1048616) = 1048596 from by native_decide,
        show S.mem.read32 ((1 : UInt32) <<< 3 + 1048620) = 1048600 from by native_decide,
        show S.mem.read32 ((1048600 : UInt32) + 12) = 2 from by native_decide]
    apply wp_callIndirect_tw
      (i := 2) (vs0 := [.i32 x, .i32 1048596])
      (tbl := [none, some 3, some 4]) (fid := 4)
      (fn := { params := [.i32, .i32], locals := [], body := func4, results := [.i32] })
      (ty := { params := [.i32, .i32], results := [.i32] })
      (Post := fun st rs => rs = [.i32 (S.mem.read32 1048596 * x)] ∧ st = S)
    · rfl
    · native_decide
    · decide
    · rfl
    · rfl
    · exact ⟨rfl, rfl⟩
    · exact mul_apply S 1048596 x (by native_decide)
    · rintro st' vs ⟨rfl, rfl⟩
      wp_run
      rw [show S.mem.read32 1048596 = 2 from by native_decide]
      simp [UInt32.mul_comm]

/-! ## `dispatch_naive` (`func1`): direct dispatch via `select` -/

/-- The naive dispatcher is pure (it reads no memory), so it has a fully
store-polymorphic spec; the `tail` parameter threads the caller's stack
frame through the call. It also returns `dispatchResult sel x`. -/
private theorem dispatch_naive (sel x : UInt32) (tail : List Value) :
    FuncSpec ({} : HostEnv Unit) «module» 1 (· = [.i32 x, .i32 sel] ++ tail)
      (fun _ rs => rs = .i32 (dispatchResult sel x) :: tail) := by
  apply FuncSpec.of_wp_body
    (f := { params := [.i32, .i32], locals := [], body := func1, results := [.i32] }) rfl
  rintro args rfl initial
  unfold func1
  wp_run
  simp [dispatchResult]
  -- `select` chooses `x <<< 1` (= `x * 2`) when `sel &&& 1 ≠ 0`, else
  -- `x + 1`; reconcile with `dispatchResult`'s `= 0` phrasing.
  have hshl : x <<< 1 = x * 2 := by bv_decide
  rw [UInt32.and_comm 1 sel]
  by_cases h : sel &&& 1 = 0 <;> simp [h, UInt32.add_comm, hshl]

/-! ## `func2`: the equivalence check, and the exported `check` -/

/-- `func2` runs both dispatchers, and because they agree it never trips
the `br_if`/`unreachable`; it returns with an empty value stack. -/
private theorem check_block (sel x : UInt32) :
    TerminatesWith ({} : HostEnv Unit) «module» 2 S [.i32 x, .i32 sel]
      (fun _ rs => rs = []) := by
  apply TerminatesWith.of_wp_entry_for
    (f := { params := [.i32, .i32], locals := [], body := func2, results := [] }) rfl
  unfold func2
  apply wp_block_cons
  wp_run
  -- stack `[.i32 x, .i32 sel]`; call `func0` (dyn) via the store-specific rule
  apply wp_call_tw
  · exact dispatch_dyn sel x
  · rintro st' vs ⟨rfl, rfl⟩
    wp_run
    -- stack `[.i32 x, .i32 sel, .i32 (dispatchResult sel x)]`; call `func1` (naive)
    apply wp_call_cons (dispatch_naive sel x [.i32 (dispatchResult sel x)])
    · rfl
    · rintro st1 vs1 rfl
      -- stack `[.i32 R, .i32 R]`; `ne` yields 0, `br_if` not taken, `ret`
      wp_run
      simp

/-- The exported `check` terminates without trapping (returning no
values) on every `(sel, x)` input — equivalently, the indirect dispatch
agrees with the direct dispatch.

Stated on `initialStore` (see the module docstring): the dynamic
dispatcher reads the static vtable out of linear memory, so the
equivalence is only meaningful there. -/
@[spec_of "rust-exported" "dyn_dispatch::check"]
def CheckSpec : Prop :=
  ∀ (sel x : UInt32),
    TerminatesWith ({} : HostEnv Unit) «module» 5 S [.i32 x, .i32 sel]
      (fun _ rs => rs = [])

@[proves Project.DynDispatch.Spec.CheckSpec]
theorem check_correct : CheckSpec := by
  intro sel x
  apply TerminatesWith.of_wp_entry_for
    (f := { params := [.i32, .i32], locals := [], body := func5, results := [] }) rfl
  unfold func5
  wp_run
  -- `check` just forwards `(sel, x)` to `func2`
  apply wp_call_tw
  · exact check_block sel x
  · rintro st' vs rfl
    wp_run
    simp

end Project.DynDispatch.Spec
