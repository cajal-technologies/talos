import Programs.RustStd.Option.Program

/-!
# Specifications for `corpus/rust/rust_std/option`

Each exported function is given a `TerminatesWith` spec at the raw
`UInt64` level (i.e. in terms of the C-ABI sentinel encoding). The shared
helpers — most importantly `sentinel` and the `encode` lifting — live in
`CodeLib.RustStd.Option` so downstream corpora using the same convention
can reuse them.
-/

namespace Programs.RustStd.Option.Spec

open Wasm
open Wasm.RustStd.Option (sentinel encode)

/-! ## Wasm-level specs (raw `UInt64` view) -/

/-- `filter_positive(opt)`: returns `opt` when it is a strictly-positive
`Some` (signed), and the sentinel `None` otherwise. Note that this
folds the "filtered out" and "already None" cases together — the
sentinel `i64::MIN < 0` is never `> 0`, so they share the same answer. -/
theorem filter_positive_correct (initial : Store) (opt : UInt64) :
    TerminatesWith «module» 0 initial [.i64 opt]
      (fun _ rs => rs = [.i64 (if opt.toInt64 > 0 then opt else sentinel)]) := by
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64], [], func0, [.i64]⟩) rfl
  intro initial'
  unfold func0
  wp_run
  simp [sentinel]
  split <;> simp_all

/-- `is_some(opt)`: returns `1 : i32` when `opt ≠ sentinel`, else `0`. -/
theorem is_some_correct (initial : Store) (opt : UInt64) :
    TerminatesWith «module» 1 initial [.i64 opt]
      (fun _ rs => rs = [.i32 (if opt = sentinel then 0 else 1)]) := by
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64], [], func1, [.i32]⟩) rfl
  intro initial'
  unfold func1
  wp_run
  simp [sentinel]

/-- `map_add(opt, k)`: wrapping `Some(x) ↦ Some(x + k)`; `None ↦ None`.
On the wasm side this is the propagated sentinel + a `UInt64` addition
(which models `i64::wrapping_add` exactly). -/
theorem map_add_correct (initial : Store) (opt k : UInt64) :
    TerminatesWith «module» 2 initial [.i64 k, .i64 opt]
      (fun _ rs => rs = [.i64 (if opt = sentinel then sentinel else opt + k)]) := by
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64, .i64], [], func2, [.i64]⟩) rfl
  intro initial'
  unfold func2
  wp_run
  simp [sentinel]
  split <;> simp [UInt64.add_comm]

/-- `or(a, b) = unwrap_or(a, b)`: returns `a` when it is `Some`, else `b`. -/
theorem or_correct (initial : Store) (a b : UInt64) :
    TerminatesWith «module» 3 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (if a = sentinel then b else a)]) := by
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64, .i64], [], func3, [.i64]⟩) rfl
  intro initial'
  unfold func3
  wp_run
  simp [sentinel]
  split <;> simp_all

/-- `unwrap_or` and `or` share `func3` — same proof, different alias. -/
theorem unwrap_or_correct (initial : Store) (a b : UInt64) :
    TerminatesWith «module» 3 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (if a = sentinel then b else a)]) :=
  or_correct initial a b

/-- `unwrap_or_default(opt)`: `Default::default() = 0` for `i64`. -/
theorem unwrap_or_default_correct (initial : Store) (opt : UInt64) :
    TerminatesWith «module» 4 initial [.i64 opt]
      (fun _ rs => rs = [.i64 (if opt = sentinel then 0 else opt)]) := by
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64], [], func4, [.i64]⟩) rfl
  intro initial'
  unfold func4
  wp_run
  simp [sentinel]
  split <;> simp_all

/-- `wrap(v)`: lifts an unwrapped `i64` into the `Some` encoding — which
is the identity, since `Some(v)` is encoded as `v` itself. -/
theorem wrap_correct (initial : Store) (v : UInt64) :
    TerminatesWith «module» 5 initial [.i64 v]
      (fun _ rs => rs = [.i64 v]) := by
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64], [], func5, [.i64]⟩) rfl
  intro initial'
  unfold func5
  wp_run
  simp

/-! ## `Option`-level lifts

These restate the wasm specs in terms of `Option Int64`, under the side
condition that no input is `some Int64.minValue` (which would collide
with the sentinel encoding). -/

open Wasm.RustStd.Option

theorem is_some_lifted (initial : Store) (o : Option Int64) (h : o ≠ some Int64.minValue) :
    TerminatesWith «module» 1 initial [.i64 (encode o)]
      (fun _ rs => rs = [.i32 (if o.isSome then 1 else 0)]) := by
  refine (is_some_correct initial (encode o)).mono ?_
  intro _ rs hrs; rw [hrs]; congr 1
  cases o with
  | none => simp
  | some x =>
    have hne : encode (some x) ≠ sentinel :=
      encode_ne_sentinel_of_some (by simpa using h)
    rw [if_neg hne]; simp

theorem unwrap_or_lifted (initial : Store) (o : Option Int64) (d : UInt64)
    (h : o ≠ some Int64.minValue) :
    TerminatesWith «module» 3 initial [.i64 d, .i64 (encode o)]
      (fun _ rs => rs = [.i64 (match o with | some x => x.toUInt64 | none => d)]) := by
  refine (or_correct initial (encode o) d).mono ?_
  intro _ rs hrs; rw [hrs]; congr 1
  cases o with
  | none => simp
  | some x =>
    have hne : encode (some x) ≠ sentinel :=
      encode_ne_sentinel_of_some (by simpa using h)
    rw [if_neg hne]; simp

end Programs.RustStd.Option.Spec
