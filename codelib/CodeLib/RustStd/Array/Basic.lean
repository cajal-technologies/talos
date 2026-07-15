import CodeLib.RustStd.UInt

/-!
# `CodeLib.RustStd.Array` — the `&[T]` slice trunk

A Rust slice `&[T]` is compiled to a **fat pointer**: a data pointer and an
element count, both carried as `i32` (a `usize` on `wasm32`). Every reasoning
fact about a slice operation is a fact about these two `i32` components — the
element type `T` never appears, which is exactly why one proof serves `&[u8]`,
`&[u64]`, `&[Foo]`, … alike.

The operations in this corpus (`len`, `is_empty`) inspect only the **length**
component, so on the value stack each is a **unary transform of one `i32`** — the
exact shape the integer trunk `CodeLib/RustStd/UInt.lean` already abstracts as
`UnChunk` (over any `UIntWasm` type; here `UInt32`, whose `toV` is `.i32`).
So a length-only op needs *no new chunk shape*: its chunk is a `UnChunk` instance
(`Len.len_chunk`, `IsEmpty.isEmpty_chunk`) and its called monomorphized body is
discharged by the shared `unSliceBodyTerminates` below (instantiated per op as
`Len.lenBodyTerminates`, `IsEmpty.isEmptyBodyTerminates`), which feeds the chunk
through the integer trunk's `unBodyReturnsWp`. That reads the length from the
slice's second fat-pointer field (param local `1`), so nothing beyond the chunk
is needed per op.

The one genuinely new unit here is `fatPtrLoadWp`: unlike a scalar, a slice
crosses the C ABI **spilled to linear memory**, so the export wrapper must read
the `(dataPtr, len)` fields back before it can feed a `UnChunk`/called body. That
memory marshalling has no integer-trunk analogue, so it lives here.

Scope: a length-only op's length reaches the stack either from a **local** (the
inlined read and the called monomorphized body, via the trunk's
`wp_localGet_cons`/`unBodyReturnsWp`) or from **linear memory** (`fatPtrLoadWp`
below, used by the export wrappers in `RustArray/Spec.lean`). Because `UnChunk`
is stated in stack form, both sources feed the *same* `isEmpty_chunk`/`len_chunk`
— a new length source only needs its own loader, never a reformulation. Still
genuinely out of scope (a different chunk shape, not a `UnChunk` instance): a
*binary* slice fact such as an `idx < len` bounds check for `get`/indexing,
which relates two `i32`s rather than transforming one (that is the trunk's
`BinChunk`).
-/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd

/-! ## Memory-resident slices

A slice handed across the C ABI is spilled to linear memory: the caller passes a
single `i32` pointer `p` to a `(dataPtr, len)` fat pointer laid out as two
adjacent `i32`s (`dataPtr` at `p+0`, `len` at `p+4`). An export wrapper reads the
fat pointer back with `localGet p; load32 0; localGet p; load32 4` before calling
the monomorphized body. `fatPtrLoadWp` is that read as a reusable chunk: it puts
`len` (and the data pointer below it) on the stack, which a `UnChunk`/called
body then consumes. It needs the fat pointer to be in bounds and the two memory
words to hold the fat-pointer fields — both facts the caller supplies, bundled as
`FatPtrAt`. -/

/-- The fat-pointer ABI contract at memory address `p`: the caller has spilled a
`(dataPtr, len)` fat pointer to linear memory (`dataPtr` at `p+0`, `len` at
`p+4`), with the whole 8-byte pointer in bounds. This is the single shared
precondition every memory-resident slice export carries; `fatPtrLoadWp` consumes
exactly these three facts. Factoring it here keeps the export specs from
restating the layout, and means a future layout change (offsets, alignment, a
third field) is edited in one place. -/
structure FatPtrAt {α : Type} (st : Store α) (p dataPtr len : UInt32) : Prop where
  /-- The data pointer lives in the first word, at `p+0`. -/
  data : st.mem.read32 (p + 0) = dataPtr
  /-- The element count lives in the second word, at `p+4`. -/
  count : st.mem.read32 (p + 4) = len
  /-- The whole 8-byte fat pointer is in bounds. -/
  bound : p.toNat + 8 ≤ st.mem.pages * 65536

/-- Reusable fat-pointer-from-memory reader: given local `i` holds the fat-pointer
address `p` and the `FatPtrAt` ABI contract holds, the loader fragment pushes
`len` on top of `dataPtr` (the call-argument order the monomorphized
`len`/`is_empty` body expects). The trailing `rest` and the existing stack `vs`
stay free, so this composes wherever a memory-resident slice's length is needed. -/
theorem fatPtrLoadWp {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program}
    (i : Nat) (p dataPtr len : UInt32) (vs : List Value)
    (hp : (⟨P, L, vs⟩ : Locals).get i = some (.i32 p))
    (h : FatPtrAt st p dataPtr len) :
    wp m (.localGet i :: .load32 0 :: .localGet i :: .load32 4 :: rest) Q st ⟨P, L, vs⟩ env ↔
    wp m rest Q st ⟨P, L, .i32 len :: .i32 dataPtr :: vs⟩ env := by
  obtain ⟨hdata, hlen, hbound⟩ := h
  have hb0 : ¬ (p.toNat + (0 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    simp only [UInt32.toNat_ofNat]; omega
  have hb4 : ¬ (p.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    simp only [UInt32.toNat_ofNat]; omega
  -- `Locals.get` ignores the value stack, so the one `hp` fact resolves both
  -- `localGet i`s (the second runs after the first load has pushed a value).
  simp only [Locals.get] at hp
  simp only [wp_localGet_cons, Locals.get, hp, wp_load32_cons, hb0, hb4, ↓reduceIte, hdata, hlen]

/-- Open a memory-resident slice export: peel the entry frame down to the
`localGet 0; load32 0; localGet 0; load32 4` prefix (the slice pointer is the
first param, local `0`) and rewrite that prefix with `fatPtrLoadWp`, leaving the
called body with `len` on top of `dataPtr`. Every export wrapper in the slice
corpora opens the same way; this is that opener as one tactic so the peel set and
the `fatPtrLoadWp` invocation live in a single place. Use as
`load_fat_ptr p, dataPtr, len using hfat`. -/
syntax "load_fat_ptr " term ", " term ", " term " using " term : tactic

macro_rules
  | `(tactic| load_fat_ptr $p, $dataPtr, $len using $hfat) =>
    `(tactic|
      (simp only [Function.toLocals, Function.numParams, List.take, List.reverse,
          List.reverseAux, List.map, List.length_cons, List.length_nil]
       rw [fatPtrLoadWp 0 $p $dataPtr $len [] (by simp) $hfat]))

/-- Open a memory-resident slice *export* proof: apply the entry lemma, unfold the
wrapper `def`s, and marshal the fat pointer back from memory with `load_fat_ptr` —
the uniform three-line head every slice export shares before it `call`s its body.
`fdef`/`fbody` are the wrapper's `Function`/`Program` defs; the remaining operands
match `load_fat_ptr`. Leaves the goal just past the fat-pointer read, with the
per-export tail (`wp_call_tw`, result rewriting) still explicit since it varies. -/
syntax "open_slice_export " ident ", " ident " at "
  term ", " term ", " term " using " term : tactic

macro_rules
  | `(tactic| open_slice_export $fdef, $fbody at $p, $dataPtr, $len using $hfat) =>
    `(tactic|
      (apply TerminatesWith.of_wp_entry_for (f := $fdef) rfl
       unfold $fdef $fbody
       load_fat_ptr $p, $dataPtr, $len using $hfat))

/-! ## Generic length-only slice callee

A length-only slice primitive compiles at opt-0 to a two-param leaf body
`[.localGet 1] ++ frag ++ [.ret]`: the fat pointer is passed as `(dataPtr, len)`
(local `0`, local `1`), the body reads the length from local `1`, and `frag` is a
`UnChunk` transforming it. `len` (`frag = []`, `op = id`) and `is_empty`
(`frag = [.const 0, .eq, .const 1, .and]`, `op = isEmptyValue`) are both this
shape, so one chunk-generic `TerminatesWith` bridge serves them — and any future
unary slice primitive — instead of a per-op copy of the `of_returns_wp` glue. -/

/-- Callee bridge for a length-only slice body: any module function `id` whose
body is `[.localGet 1] ++ frag ++ [.ret]` for a `UnChunk frag op` terminates,
when called with stack `(len, dataPtr, …rest)`, returning `op len` on top of
`rest`. Instantiate at a concrete chunk (`len_chunk`, `isEmpty_chunk`) to obtain
that primitive's leaf-call fact; the `of_returns_wp`/`unBodyReturnsWp` glue lives
here once. -/
theorem unSliceBodyTerminates {α} {env : HostEnv α} {m : Module} {id : Nat}
    {f : Function} {frag : Program} {op : UInt32 → UInt32} (chunk : UnChunk frag op)
    (st : Store α) (dataPtr len : UInt32) (rest : List Value)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hbody : f.body = [.localGet 1] ++ frag ++ [.ret])
    (hnp : f.numParams = 2)
    (hres : f.results.length = 1)
    (hImp : m.imports[id]? = none := by rfl) :
    TerminatesWith env m id st (.i32 len :: .i32 dataPtr :: rest)
      (fun st' vs => vs = .i32 (op len) :: rest ∧ framePost st st') := by
  refine (TerminatesWith.of_returns_wp (f := f) (rs := [.i32 (op len)])
      (P := framePost st) hf hres.symm ?_ hImp).mono ?_
  · rw [hbody]
    simp only [Function.toLocals, hnp]
    exact unBodyReturnsWp chunk st 1 len [] rfl
  · intro st' vs h
    refine ⟨?_, h.2⟩
    rw [h.1, hnp]
    simp

end Wasm.RustStd.Array
