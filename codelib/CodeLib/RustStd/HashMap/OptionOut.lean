import CodeLib.RustStd.HashMap.TableMem

/-!
# The `Option<u32>` return of the compiled insert

`Table.insert` returns `Option V × Table K V`.  On wasm32 the compiled
insert, func 18, takes the `Option<u32>` half as an eight-byte
out-parameter in its first argument.  Func 18 writes it at WAT lines 4520
to 4525 of `programs/rust/build/rust_hash_map/program.wat`:

```
local.get 0   ;; the out-parameter
local.get 1   ;; the payload
i32.store offset=4
local.get 0
local.get 12  ;; the discriminant
i32.store
```

The discriminant is local 12.  Func 18 sets it to `0` at WAT line 4432 on
the arm that inserts a new key, and to `1` at WAT line 4517 on the arm
that replaces the value of a key that is already there.  So `0` is `none`
and `1` is `some`.  On the `none` arm local 1 holds a leftover address, so
the payload word has no meaning there.

`optionU32At` is that layout.  `optionU32At_of_words` is the one lemma a
body proof needs after the two stores, and `optionU32At_forget` gives the
eight bytes back to a caller that drops the result, which is what func 5
does.
-/

namespace Wasm.RustStd.HashMap.Table

open Wasm.SepLogic Iris Std

section Memory

variable {α : Type} [WasmHeapGS α]

/-- `Option<u32>` in an eight-byte out-parameter: the discriminant word at
`addr`, then the payload word.  The payload of `none` is any word. -/
def optionU32At (memId : Nat) (addr : UInt32) :
    Option UInt32 → IProp (WasmHeapGF α)
  | none =>
      iprop(∃ pad : UInt32,
        pointsTo_u32 memId addr 0 ∗ pointsTo_u32 memId (addr + 4) pad)
  | some v =>
      iprop(pointsTo_u32 memId addr 1 ∗ pointsTo_u32 memId (addr + 4) v)

/-- `none` is discriminant `0` and any payload. -/
theorem optionU32At_none (memId : Nat) (addr : UInt32) :
    optionU32At (α := α) memId addr none ⊣⊢
      iprop(∃ pad : UInt32,
        pointsTo_u32 memId addr 0 ∗ pointsTo_u32 memId (addr + 4) pad) := .rfl

/-- `some v` is discriminant `1` and payload `v`. -/
theorem optionU32At_some (memId : Nat) (addr : UInt32) (v : UInt32) :
    optionU32At (α := α) memId addr (some v) ⊣⊢
      iprop(pointsTo_u32 memId addr 1 ∗ pointsTo_u32 memId (addr + 4) v) := .rfl

/-- The two stores of func 18 build the layout.  The discriminant is `1`
on the arm that found the key and `0` on the arm that inserted it, and the
payload matters only on the first arm. -/
theorem optionU32At_of_words (memId : Nat) (addr : UInt32)
    (o : Option UInt32) (payload : UInt32)
    (hpayload : ∀ v : UInt32, o = some v → payload = v) :
    iprop(pointsTo_u32 (α := α) memId addr (if o.isSome then 1 else 0) ∗
      pointsTo_u32 memId (addr + 4) payload) ⊢ optionU32At memId addr o := by
  cases o with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, optionU32At]
    iintro ⟨Htag, Hpad⟩
    iexists payload
    isplitl [Htag]
    · iexact Htag
    · iexact Hpad
  | some v =>
    have hv : payload = v := hpayload v rfl
    subst hv
    simp only [Option.isSome_some, if_true, optionU32At]
    iintro ⟨Htag, Hpayload⟩
    isplitl [Htag]
    · iexact Htag
    · iexact Hpayload

/-- A caller that drops the result gets two anonymous words back, so the
out-parameter returns to the frame it came from.  Func 5 takes this
direction. -/
theorem optionU32At_forget (memId : Nat) (addr : UInt32) (o : Option UInt32) :
    optionU32At (α := α) memId addr o ⊢
      iprop(∃ tag : UInt32, ∃ payload : UInt32,
        pointsTo_u32 memId addr tag ∗ pointsTo_u32 memId (addr + 4) payload) := by
  cases o with
  | none =>
    simp only [optionU32At]
    iintro ⟨%pad, Htag, Hpad⟩
    iexists (0 : UInt32)
    iexists pad
    isplitl [Htag]
    · iexact Htag
    · iexact Hpad
  | some v =>
    simp only [optionU32At]
    iintro ⟨Htag, Hpayload⟩
    iexists (1 : UInt32)
    iexists v
    isplitl [Htag]
    · iexact Htag
    · iexact Hpayload

end Memory

end Wasm.RustStd.HashMap.Table
