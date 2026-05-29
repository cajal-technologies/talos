import Project.RustOption.Program

/-!
# Specifications for the `rust_option` crate

Each exported function is given a `TerminatesWith` spec at the raw
`UInt64` level (i.e. in terms of the C-ABI sentinel encoding). The
shared helpers — most importantly `sentinel` and the `encode` lifting —
live in `CodeLib.RustStd.Option` so downstream corpora using the same
convention can reuse them.
-/

namespace Project.RustOption.Spec

open Wasm
open Wasm.RustStd.Option (sentinel encode)

/-! ## Wasm-level specs (raw `UInt64` view) -/

/-- The exported `filter_positive` returns `opt` when its `i64` argument
encodes a strictly-positive `Some`, and the sentinel `None` otherwise.

Informal spec:
For any `opt : UInt64`, the wasm export `filter_positive` terminates
and leaves a single i64 on the value stack equal to `opt` if
`opt.toInt64 > 0` and to the `None`-sentinel (`i64::MIN`) otherwise.
The "filtered out" and "already None" cases share the same answer —
the sentinel `i64::MIN < 0` is never `> 0`. -/
@[spec_of "rust-exported" "rust_option::filter_positive"]
def FilterPositiveSpec : Prop :=
  ∀ (initial : Store) (opt : UInt64),
    TerminatesWith «module» 0 initial [.i64 opt]
      (fun _ rs => rs = [.i64 (if opt.toInt64 > 0 then opt else sentinel)])

@[proves Project.RustOption.Spec.FilterPositiveSpec]
theorem filter_positive_correct : FilterPositiveSpec := by
  intro initial opt
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64], [], func0, [.i64]⟩) rfl
  intro initial'
  unfold func0
  wp_run
  simp [sentinel]
  split <;> simp_all

/-- The exported `unwrap_or_default` returns `opt` when it is `Some`,
and `0` (the `Default::default()` value for `i64`) when it is `None`.

Informal spec:
For any `opt : UInt64`, the wasm export `unwrap_or_default` terminates
and leaves a single i64 on the value stack equal to `0` if
`opt = sentinel` (i.e. encodes `None`) and to `opt` otherwise. -/
@[spec_of "rust-exported" "rust_option::unwrap_or_default"]
def UnwrapOrDefaultSpec : Prop :=
  ∀ (initial : Store) (opt : UInt64),
    TerminatesWith «module» 1 initial [.i64 opt]
      (fun _ rs => rs = [.i64 (if opt = sentinel then 0 else opt)])

@[proves Project.RustOption.Spec.UnwrapOrDefaultSpec]
theorem unwrap_or_default_correct : UnwrapOrDefaultSpec := by
  intro initial opt
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64], [], func1, [.i64]⟩) rfl
  intro initial'
  unfold func1
  wp_run
  simp [sentinel]
  split <;> simp_all

/-- The exported `or` returns `a` when it is `Some`, otherwise `b`.

Informal spec:
For any `a b : UInt64`, the wasm export `or` (and its alias
`unwrap_or`) terminates and leaves a single i64 on the value stack
equal to `b` if `a = sentinel` (i.e. `a` encodes `None`) and to `a`
otherwise. -/
@[spec_of "rust-exported" "rust_option::or"]
def OrSpec : Prop :=
  ∀ (initial : Store) (a b : UInt64),
    TerminatesWith «module» 2 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (if a = sentinel then b else a)])

@[proves Project.RustOption.Spec.OrSpec]
theorem or_correct : OrSpec := by
  intro initial a b
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64, .i64], [], func2, [.i64]⟩) rfl
  intro initial'
  unfold func2
  wp_run
  simp [sentinel]
  split <;> simp_all

/-- The exported `unwrap_or` shares the wasm body of `or`; same spec.

Informal spec:
For any `a b : UInt64`, the wasm export `unwrap_or` terminates and
leaves a single i64 on the value stack equal to `b` if `a = sentinel`
and to `a` otherwise. The behaviour is bit-for-bit identical to
[`OrSpec`] because the two exports share the same wasm function. -/
@[spec_of "rust-exported" "rust_option::unwrap_or"]
def UnwrapOrSpec : Prop :=
  ∀ (initial : Store) (a b : UInt64),
    TerminatesWith «module» 2 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (if a = sentinel then b else a)])

@[proves Project.RustOption.Spec.UnwrapOrSpec]
theorem unwrap_or_correct : UnwrapOrSpec :=
  or_correct

/-- The exported `wrap` lifts an unwrapped `i64` into the `Some`
encoding — the identity, since `Some(v)` is encoded as `v` itself.

Informal spec:
For any `v : UInt64`, the wasm export `wrap` terminates and leaves the
input value on the value stack unchanged. -/
@[spec_of "rust-exported" "rust_option::wrap"]
def WrapSpec : Prop :=
  ∀ (initial : Store) (v : UInt64),
    TerminatesWith «module» 3 initial [.i64 v]
      (fun _ rs => rs = [.i64 v])

@[proves Project.RustOption.Spec.WrapSpec]
theorem wrap_correct : WrapSpec := by
  intro initial v
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64], [], func3, [.i64]⟩) rfl
  intro initial'
  unfold func3
  wp_run
  simp

/-- The exported `is_some` returns `1 : i32` when `opt ≠ sentinel`,
else `0`.

Informal spec:
For any `opt : UInt64`, the wasm export `is_some` terminates and
leaves a single i32 on the value stack equal to `0` if `opt = sentinel`
and to `1` otherwise. -/
@[spec_of "rust-exported" "rust_option::is_some"]
def IsSomeSpec : Prop :=
  ∀ (initial : Store) (opt : UInt64),
    TerminatesWith «module» 4 initial [.i64 opt]
      (fun _ rs => rs = [.i32 (if opt = sentinel then 0 else 1)])

@[proves Project.RustOption.Spec.IsSomeSpec]
theorem is_some_correct : IsSomeSpec := by
  intro initial opt
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64], [], func4, [.i32]⟩) rfl
  intro initial'
  unfold func4
  wp_run
  simp [sentinel]

/-- The exported `map_add` propagates the sentinel and otherwise adds
`k` (wrapping) to the contained value.

Informal spec:
For any `opt k : UInt64`, the wasm export `map_add` terminates and
leaves a single i64 on the value stack equal to the sentinel if
`opt = sentinel`, else to `opt + k` (UInt64 wrapping addition, which
models `i64::wrapping_add`). -/
@[spec_of "rust-exported" "rust_option::map_add"]
def MapAddSpec : Prop :=
  ∀ (initial : Store) (opt k : UInt64),
    TerminatesWith «module» 5 initial [.i64 k, .i64 opt]
      (fun _ rs => rs = [.i64 (if opt = sentinel then sentinel else opt + k)])

@[proves Project.RustOption.Spec.MapAddSpec]
theorem map_add_correct : MapAddSpec := by
  intro initial opt k
  apply TerminatesWith.of_wp_entry (f := ⟨[.i64, .i64], [], func5, [.i64]⟩) rfl
  intro initial'
  unfold func5
  wp_run
  simp [sentinel]
  split <;> simp [UInt64.add_comm]

/-! ## `Option`-level lifts

These restate the wasm specs in terms of `Option Int64`, under the side
condition that no input is `some Int64.minValue` (which would collide
with the sentinel encoding). -/

open Wasm.RustStd.Option

theorem is_some_lifted (initial : Store) (o : Option Int64) (h : o ≠ some Int64.minValue) :
    TerminatesWith «module» 4 initial [.i64 (encode o)]
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
    TerminatesWith «module» 2 initial [.i64 d, .i64 (encode o)]
      (fun _ rs => rs = [.i64 (match o with | some x => x.toUInt64 | none => d)]) := by
  refine (or_correct initial (encode o) d).mono ?_
  intro _ rs hrs; rw [hrs]; congr 1
  cases o with
  | none => simp
  | some x =>
    have hne : encode (some x) ≠ sentinel :=
      encode_ne_sentinel_of_some (by simpa using h)
    rw [if_neg hne]; simp

end Project.RustOption.Spec
