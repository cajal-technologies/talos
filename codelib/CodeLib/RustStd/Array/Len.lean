import CodeLib.RustStd.Array.Basic

/-! `&[T]::len` — the slice length is the `i32` length component of the fat
pointer; the monomorphized primitive body just returns it. The reusable unit is
the degenerate unary chunk (`frag = []`, `op = id`) over the length, which feeds
the called body through the trunk's `unSliceBodyTerminates`. The *inlined* read
is just `wp_localGet_cons`, so it needs no slice-specific lemma. -/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd

/-- The reusable chunk: with the length on the stack, the empty fragment leaves
it unchanged — `len` is the identity length-only op. The `frag = []`, `op = id`
case of the trunk's `UnChunk` (at `UInt32`, whose `toV` is `.i32`); feeds
`lenBodyTerminates` via `unSliceBodyTerminates`. -/
theorem len_chunk : UnChunk (T := UInt32) [] (id : UInt32 → UInt32) := by
  intro α m env Q st P L rest len vs
  simp

/-- Reusable *callee* fact for a generated leaf `len` body. Any module function
`id` whose body is the canonical `[localGet 1, ret]` (the slice length sits in
param local `1`, the second fat-pointer field) terminates, when called with stack
`(len, dataPtr, …rest)`, returning `len` on top of `rest`. This is the trunk's
`unSliceBodyTerminates` at `len_chunk` (`op = id`); each corpus' leaf `len` call
bridge is this lemma at its concrete `func…Def`. -/
theorem lenBodyTerminates {α} {env : HostEnv α} {m : Module} {id : Nat}
    {f : Function} (st : Store α) (dataPtr len : UInt32) (rest : List Value)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hbody : f.body = [.localGet 1, .ret])
    (hnp : f.numParams = 2)
    (hres : f.results.length = 1)
    (hImp : m.imports[id]? = none := by rfl) :
    TerminatesWith env m id st (.i32 len :: .i32 dataPtr :: rest)
      (fun st' vs => vs = .i32 len :: rest ∧ framePost st st') :=
  unSliceBodyTerminates len_chunk st dataPtr len rest hf hbody hnp hres hImp

end Wasm.RustStd.Array
