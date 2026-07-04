/-! ## Linear memory model

A `Mem` is a function from byte addresses to `UInt8`, together with a
page count (1 page = 64 KiB). The function is total: reads outside the
"legal" range `[0, pages * 65536)` return whatever `bytes` returns there
(typically zero, since `Mem.empty` initialises with `fun _ => 0`), but
well-formed programs never read those addresses.

This is the live memory model backing every memory instruction:
loads/stores, `memory.size`/`grow`/`fill`/`copy`/`init`, and the
multi-memory and data-segment machinery all read and write a `Mem`.

The simplicity-of-reasoning convention applies: writes update the
underlying `bytes` function pointwise via `fun i => if i ∈ range then …
else m.bytes i`, which is trivially easy to `simp` through. -/

namespace Wasm

/-- A function-model linear memory. `pages` counts 64 KiB pages; `bytes`
maps every byte address to its current value. -/
structure Mem where
  pages : Nat
  bytes : Nat → UInt8
deriving Inhabited

/-- Custom `Repr` instance: prints only `pages`. The byte function is
elided because functions don't have a sensible textual representation
and `#eval` results in examples don't need byte-level dumps. -/
instance : Repr Mem where
  reprPrec m _ := s!"Mem(pages={m.pages})"

/-- An empty memory with `pages` pages, all bytes zeroed. -/
def Mem.empty (pages : Nat) : Mem :=
  { pages, bytes := fun _ => 0 }

/-- Read a single byte. -/
def Mem.read8 (m : Mem) (a : UInt32) : UInt8 :=
  m.bytes a.toNat

/-- Read a little-endian 32-bit word starting at `a`. -/
def Mem.read32 (m : Mem) (a : UInt32) : UInt32 :=
  let b0 : UInt32 := (m.bytes a.toNat).toUInt32
  let b1 : UInt32 := (m.bytes (a.toNat + 1)).toUInt32
  let b2 : UInt32 := (m.bytes (a.toNat + 2)).toUInt32
  let b3 : UInt32 := (m.bytes (a.toNat + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Write a single byte. -/
def Mem.write8 (m : Mem) (a : UInt32) (v : UInt8) : Mem :=
  { m with bytes := fun i => if i = a.toNat then v else m.bytes i }

/-- Write a little-endian 32-bit word starting at `a`. -/
def Mem.write32 (m : Mem) (a : UInt32) (v : UInt32) : Mem :=
  let n := a.toNat
  let b0 : UInt8 := (v &&& 0xFF).toUInt8
  let b1 : UInt8 := ((v >>> 8) &&& 0xFF).toUInt8
  let b2 : UInt8 := ((v >>> 16) &&& 0xFF).toUInt8
  let b3 : UInt8 := ((v >>> 24) &&& 0xFF).toUInt8
  { m with bytes := fun i =>
      if i = n then b0
      else if i = n + 1 then b1
      else if i = n + 2 then b2
      else if i = n + 3 then b3
      else m.bytes i }

/-- Read a little-endian 16-bit value starting at `a`; zero-extended to UInt32. -/
def Mem.read16 (m : Mem) (a : UInt32) : UInt32 :=
  let b0 : UInt32 := (m.bytes a.toNat).toUInt32
  let b1 : UInt32 := (m.bytes (a.toNat + 1)).toUInt32
  b0 ||| (b1 <<< 8)

/-- Read a little-endian 64-bit word starting at `a`. -/
def Mem.read64 (m : Mem) (a : UInt32) : UInt64 :=
  let b0 : UInt64 := (m.bytes a.toNat).toUInt64
  let b1 : UInt64 := (m.bytes (a.toNat + 1)).toUInt64
  let b2 : UInt64 := (m.bytes (a.toNat + 2)).toUInt64
  let b3 : UInt64 := (m.bytes (a.toNat + 3)).toUInt64
  let b4 : UInt64 := (m.bytes (a.toNat + 4)).toUInt64
  let b5 : UInt64 := (m.bytes (a.toNat + 5)).toUInt64
  let b6 : UInt64 := (m.bytes (a.toNat + 6)).toUInt64
  let b7 : UInt64 := (m.bytes (a.toNat + 7)).toUInt64
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

/-- Write the low 2 bytes of `v` in little-endian order starting at `a`. -/
def Mem.write16 (m : Mem) (a : UInt32) (v : UInt32) : Mem :=
  let n := a.toNat
  let b0 : UInt8 := (v &&& 0xFF).toUInt8
  let b1 : UInt8 := ((v >>> 8) &&& 0xFF).toUInt8
  { m with bytes := fun i =>
      if i = n then b0
      else if i = n + 1 then b1
      else m.bytes i }

/-- Write a little-endian 64-bit word starting at `a`. -/
def Mem.write64 (m : Mem) (a : UInt32) (v : UInt64) : Mem :=
  let n := a.toNat
  let b0 : UInt8 := (v &&& 0xFF).toUInt8
  let b1 : UInt8 := ((v >>> 8) &&& 0xFF).toUInt8
  let b2 : UInt8 := ((v >>> 16) &&& 0xFF).toUInt8
  let b3 : UInt8 := ((v >>> 24) &&& 0xFF).toUInt8
  let b4 : UInt8 := ((v >>> 32) &&& 0xFF).toUInt8
  let b5 : UInt8 := ((v >>> 40) &&& 0xFF).toUInt8
  let b6 : UInt8 := ((v >>> 48) &&& 0xFF).toUInt8
  let b7 : UInt8 := ((v >>> 56) &&& 0xFF).toUInt8
  { m with bytes := fun i =>
      if i = n then b0
      else if i = n + 1 then b1
      else if i = n + 2 then b2
      else if i = n + 3 then b3
      else if i = n + 4 then b4
      else if i = n + 5 then b5
      else if i = n + 6 then b6
      else if i = n + 7 then b7
      else m.bytes i }

/-- Fill `len` consecutive bytes starting at `offset` with `val`. The
pointwise `if i ∈ [offset, offset+len) then val else m.bytes i` form is
the canonical "easy to `simp` through" shape — no list allocation, no
recursion. The caller is responsible for the bounds check (the spec
requires a trap when `offset + len` exceeds the memory's byte size). -/
def Mem.fill (m : Mem) (offset len : Nat) (val : UInt8) : Mem :=
  { m with bytes := fun i =>
      if offset ≤ i ∧ i < offset + len then val
      else m.bytes i }

/-- Copy `len` bytes from `[src, src+len)` to `[dst, dst+len)`. The
result is defined pointwise — for an address `i` in the destination
range, the new byte is the *original* `m.bytes (src + (i - dst))`.
Reading from the pre-copy bytes function gives `memmove` semantics for
free even when the source and destination ranges overlap, while staying
in the canonical "easy to `simp` through" shape. The caller checks
bounds; the spec requires a trap when `dst + len` or `src + len`
exceeds the memory's byte size. -/
def Mem.copy (m : Mem) (dst src len : Nat) : Mem :=
  { m with bytes := fun i =>
      if dst ≤ i ∧ i < dst + len then m.bytes (src + (i - dst))
      else m.bytes i }

/-- Attempt to grow `m` by `delta` pages, accepting only if the resulting
page count stays within `cap`. On success returns the new memory paired
with the *previous* page count (what `memory.grow` pushes); on failure
returns `none`. -/
def Mem.grow (m : Mem) (delta : UInt32) (cap : Nat) : Option (Mem × Nat) :=
  let cur := m.pages
  let newPages := cur + delta.toNat
  if newPages ≤ cap then some ({ m with pages := newPages }, cur)
  else none

/-- Write a list of bytes starting at byte offset `offset`. The list's
i-th element lands at address `offset + i`. -/
def Mem.writeBytes (m : Mem) (offset : Nat) (data : List UInt8) : Mem :=
  let len := data.length
  { m with bytes := fun i =>
      if h : offset ≤ i ∧ i < offset + len then
        data[i - offset]'(by
          have : i - offset < len := by
            have := h.2; omega
          exact this)
      else m.bytes i }

/-- Read `len` bytes starting at byte offset `offset`. Used by the
cross-memory `memory.copy`; the caller checks bounds. -/
def Mem.readBytes (m : Mem) (offset len : Nat) : List UInt8 :=
  (List.range len).map fun i => m.bytes (offset + i)

/-- Write a slice of `src` into memory at `dst`. The byte at address
`dst + k` (for `0 ≤ k < len`) is `src[srcOff + k]`. The caller is
responsible for bounds — both `dst + len ≤ pages * 65536` and
`srcOff + len ≤ src.length`. Out-of-range source reads fall back to
the existing byte (defensive default, never observed in spec-conforming
runs). -/
def Mem.writeBytesFrom (m : Mem) (dst : Nat) (src : List UInt8)
    (srcOff len : Nat) : Mem :=
  { m with bytes := fun i =>
      if dst ≤ i ∧ i < dst + len then
        (src[srcOff + (i - dst)]?).getD (m.bytes i)
      else m.bytes i }

end Wasm
