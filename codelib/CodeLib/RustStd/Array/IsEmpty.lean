import CodeLib.RustStd.Array.Basic

/-! `&[T]::is_empty` — a zero-length test masked to a Rust bool, computed from the
slice length component. The reusable unit is the unary chunk (a `UnChunk` over
`UInt32`) for the fragment `[.const 0, .eq, .const 1, .and]`; the called body
(`isEmptyBodyTerminates`) derives from it through the trunk's
`unSliceBodyTerminates`, and an inlined occurrence reuses the chunk directly. -/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd

/-- The `i32` result encoding emitted for `xs.is_empty()`: `1` when empty, else
`0`. -/
abbrev isEmptyValue (len : UInt32) : UInt32 :=
  if len = 0 then 1 else 0

/-- The extra `& 1` a caller emits after a bool-returning `is_empty` call is a
no-op on the canonical result (it is already `0`/`1`). The caller's fragment is
`… ; .const 1 ; .and` (i.e. `result &&& 1`); stated here as `1 &&& …` since `&&&`
commutes and `wp_and_cons` normalises the operand order. Reused at call sites
where Rust re-masks the returned bool. -/
theorem isEmptyValue_and_one (len : UInt32) :
    1 &&& isEmptyValue len = isEmptyValue len := by
  unfold isEmptyValue
  by_cases h : len = 0 <;> simp [h]

/-- The reusable chunk: with the slice length on the stack, the fragment
`[.const 0, .eq, .const 1, .and]` computes `isEmptyValue len`. The single
stack-form unit for `is_empty` (a `UnChunk` over `UInt32`): it feeds the called
body via the trunk's `unSliceBodyTerminates`, and is `rw`-able directly at an
inlined `is_empty` once the length is on the stack. -/
theorem isEmpty_chunk : UnChunk (T := UInt32) [.const 0, .eq, .const 1, .and] isEmptyValue := by
  intro α m env Q st P L rest len vs
  simp only [toV_u32, List.cons_append, List.nil_append, wp_const_cons, wp_eq_cons, wp_and_cons]
  unfold isEmptyValue
  by_cases h : len = 0 <;> simp [h]

/-- Reusable *callee* fact for a generated leaf `is_empty` body. Any module
function `id` whose body is the canonical `[localGet 1, const 0, eq, const 1, and,
ret]` (the slice length sits in param local `1`, the second fat-pointer field)
terminates, when called with stack `(len, dataPtr, …rest)`, returning
`isEmptyValue len` on top of `rest`. This is the trunk's `unSliceBodyTerminates`
at `isEmpty_chunk`; each corpus' leaf `is_empty` call bridge is this lemma at its
concrete `func…Def`. -/
theorem isEmptyBodyTerminates {α} {env : HostEnv α} {m : Module} {id : Nat}
    {f : Function} (st : Store α) (dataPtr len : UInt32) (rest : List Value)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hbody : f.body = [.localGet 1, .const 0, .eq, .const 1, .and, .ret])
    (hnp : f.numParams = 2)
    (hres : f.results.length = 1)
    (hImp : m.imports[id]? = none := by rfl) :
    TerminatesWith env m id st (.i32 len :: .i32 dataPtr :: rest)
      (fun st' vs => vs = .i32 (isEmptyValue len) :: rest ∧ framePost st st') :=
  unSliceBodyTerminates isEmpty_chunk st dataPtr len rest hf hbody hnp hres hImp

end Wasm.RustStd.Array
