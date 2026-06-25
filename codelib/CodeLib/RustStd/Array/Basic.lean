import CodeLib.RustStd.UInt

/-!
# `CodeLib.RustStd.Array` — the `&[T]` slice trunk

A Rust slice `&[T]` is compiled to a **fat pointer**: a data pointer and an
element count, both carried as `i32` (a `usize` on `wasm32`). Every reasoning
fact about a slice operation is a fact about these two `i32` components — the
element type `T` never appears, which is exactly why one proof serves `&[u8]`,
`&[u64]`, `&[Foo]`, … alike.

The operations in this corpus (`len`, `is_empty`) inspect only the **length**
component, so on the value stack each is a unary transform of the length `i32`.
This file is the slice analogue of the integer trunk `CodeLib/RustStd/UInt.lean`:
it fixes the one reusable unit — a **stack-form chunk** over the length — and the
one template that turns such a chunk into a function-body theorem.

As in the integer corpus, *one chunk per op* serves both shapes the opt-0
compiler may pick — an *inlined* length read + fragment, or a *called*
monomorphized body — so a proof never needs to know which the compiler chose.
The body template `lenOpBodyWp` reads the length from an **arbitrary** local `i`
(slices carry the length in the second fat-pointer field, e.g. param local `1`),
via a `Locals.get` hypothesis.

Scope: a length-only op's length reaches the stack either from a **local** (the
inlined read and the called monomorphized body, `lenOpBodyWp`) or from **linear
memory** when the slice crosses the ABI as a fat pointer (`fatPtrLoadWp` below,
used by the export wrappers in `RustArray/Spec.lean`). Because `LenChunk` is
stated in stack form, both sources feed the *same* `is_empty_chunk`/`len_chunk`
— a new length source only needs its own loader, never a reformulation. Still
genuinely out of scope (a different chunk shape, not a `LenChunk` instance): a
*binary* slice fact such as an `idx < len` bounds check for `get`/indexing,
which relates two `i32`s rather than transforming one.
-/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd

/-- A **length-only slice operation** as a stack-form chunk: with the slice
length `.i32 len` on the value stack, running `frag` then `rest` equals running
`rest` with `.i32 (op len)` on the stack. `op : UInt32 → UInt32` is the result
encoding (`isEmptyValue` for `is_empty`, `id` for `len`). Stated in stack form so
it `rw`s directly onto an inlined occurrence regardless of how the length got
there (`localGet`, a memory load, a call result, …). -/
abbrev LenChunk (frag : Program) (op : UInt32 → UInt32) : Prop :=
  ∀ {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α} {st : Store α}
    {P L : List Value} {rest : Program} (len : UInt32) (vs : List Value),
    wp m (frag ++ rest) Q st ⟨P, L, .i32 len :: vs⟩ env ↔
    wp m rest Q st ⟨P, L, .i32 (op len) :: vs⟩ env

/-- Discharge the body of a length-only slice primitive
`[localGet i] ++ frag ++ [.ret]` that reads the slice length from local `i`, by
reusing the op's `LenChunk`. The opaque `frag` is what keeps `wp_run` from
bypassing the chunk, so the chunk is the only way through — the same chunk a
called body and an inlined site both consume. One template for every length-only
op. -/
theorem lenOpBodyWp {frag : Program} {op : UInt32 → UInt32} (chunk : LenChunk frag op)
    {α : Type} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i : Nat) (len : UInt32) (vs : List Value)
    (hlen : (⟨P, L, vs⟩ : Locals).get i = some (.i32 len)) :
    wp m ([.localGet i] ++ frag ++ [.ret])
      (Returns (.i32 (op len) :: vs) (framePost st)) st ⟨P, L, vs⟩ env := by
  rw [show [.localGet i] ++ frag ++ [.ret] = .localGet i :: (frag ++ [.ret]) from by simp]
  simp only [wp_localGet_cons, hlen]
  rw [chunk len vs]
  unfold Returns framePost
  simp

/-! ## Memory-resident slices

A slice handed across the C ABI is spilled to linear memory: the caller passes a
single `i32` pointer `p` to a `(dataPtr, len)` fat pointer laid out as two
adjacent `i32`s (`dataPtr` at `p+0`, `len` at `p+4`). An export wrapper reads the
fat pointer back with `localGet p; load32 0; localGet p; load32 4` before calling
the monomorphized body. `fatPtrLoadWp` is that read as a reusable chunk: it puts
`len` (and the data pointer below it) on the stack, which a `LenChunk`/called
body then consumes. It needs the fat pointer to be in bounds and the two memory
words to hold the fat-pointer fields — both facts the caller supplies. -/

/-- Reusable fat-pointer-from-memory reader: given local `i` holds the fat-pointer
address `p`, the 8-byte fat pointer is in bounds, and memory holds `dataPtr` at
`p+0` and `len` at `p+4`, the loader fragment pushes `len` on top of `dataPtr`
(the call-argument order the monomorphized `len`/`is_empty` body expects). The
trailing `rest` and the existing stack `vs` stay free, so this composes wherever
a memory-resident slice's length is needed. -/
theorem fatPtrLoadWp {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program}
    (i : Nat) (p dataPtr len : UInt32) (vs : List Value)
    (hp : (⟨P, L, vs⟩ : Locals).get i = some (.i32 p))
    (hbound : p.toNat + 8 ≤ st.mem.pages * 65536)
    (hdata : st.mem.read32 (p + 0) = dataPtr)
    (hlen : st.mem.read32 (p + 4) = len) :
    wp m (.localGet i :: .load32 0 :: .localGet i :: .load32 4 :: rest) Q st ⟨P, L, vs⟩ env ↔
    wp m rest Q st ⟨P, L, .i32 len :: .i32 dataPtr :: vs⟩ env := by
  have hb0 : ¬ (p.toNat + (0 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    simp only [UInt32.toNat_ofNat]; omega
  have hb4 : ¬ (p.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    simp only [UInt32.toNat_ofNat]; omega
  -- `Locals.get` ignores the value stack, so the one `hp` fact resolves both
  -- `localGet i`s (the second runs after the first load has pushed a value).
  simp only [Locals.get] at hp
  simp only [wp_localGet_cons, Locals.get, hp, wp_load32_cons, hb0, hb4, ↓reduceIte, hdata, hlen]

end Wasm.RustStd.Array
