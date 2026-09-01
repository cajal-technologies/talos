import Interpreter.Wasm

/-!
# `CodeLib.RustStd.Vec`

A pure model of the safe `Vec<T>` surface, as a plain `List W`.

The model carries no capacity field.  Capacity is not observable through the
safe API: no safe method reads it back, and two vectors that differ only in
capacity answer every safe query identically.  The heap-level three-word
layout, where capacity is a real word, is a separate concern and already has
a model of its own in the merge-sort formalization; this file is the
spec-level counterpart and deliberately does not overlap with it.

Panic indexing (`v[i]`) is not modeled.  A panic compiles to a wasm trap, so
it is an outcome of the run rather than an operation of the data structure.
`get` is the total `Option`-returning form, matching `Vec::get`.

Iteration is the underlying `List`, so specs over folds and maps are stated
directly in `List.foldl` and `List.map` terms rather than through a wrapper.
-/

namespace Wasm.RustStd.Vec

open Wasm

variable {W : Type}

/-- `Vec::push`: append one element at the back. -/
def push (values : List W) (x : W) : List W := values ++ [x]

/-- `Vec::pop`: remove the last element and return it, `none` when empty.
The second component is the vector that remains. -/
def pop (values : List W) : Option W × List W :=
  (values.getLast?, values.dropLast)

/-- `Vec::get`: bounds-checked read, `none` when out of range. -/
def get (values : List W) (i : Nat) : Option W := values[i]?

/-- `Vec::len`. -/
def len (values : List W) : Nat := values.length

/-- `Vec::is_empty`. -/
def isEmpty (values : List W) : Bool := values.isEmpty

/-- `<[T]>::contains`, reached through `Vec`'s slice deref. -/
def contains [BEq W] (values : List W) (x : W) : Bool := values.contains x

/-! ## Access-pattern lemmas -/

@[simp] theorem len_nil : len ([] : List W) = 0 := rfl

@[simp] theorem len_push (values : List W) (x : W) :
    len (push values x) = len values + 1 := by
  simp [len, push]

@[simp] theorem pop_push (values : List W) (x : W) :
    pop (push values x) = (some x, values) := by
  simp [pop, push]

@[simp] theorem pop_nil : pop ([] : List W) = (none, []) := rfl

/-- Popping shortens by one, and by nothing at all when empty. -/
theorem len_pop (values : List W) : len (pop values).2 = len values - 1 := by
  simp [len, pop]

@[simp] theorem get_push_len (values : List W) (x : W) :
    get (push values x) (len values) = some x := by
  simp [get, push, len]

theorem get_push_lt {values : List W} {i : Nat} (h : i < len values) (x : W) :
    get (push values x) i = get values i := by
  simp [get, push, List.getElem?_append_left h]

theorem get_eq_none_iff (values : List W) (i : Nat) :
    get values i = none ↔ len values ≤ i := by
  simp [get, len]

theorem isEmpty_iff_len_eq_zero (values : List W) :
    isEmpty values = true ↔ len values = 0 := by
  simp [isEmpty, len]

theorem contains_push [BEq W] [LawfulBEq W] (values : List W) (x y : W) :
    contains (push values x) y = (contains values y || y == x) := by
  simp only [contains, push]
  by_cases h : y = x <;> simp [h]

end Wasm.RustStd.Vec
