/-!
# `CodeLib.RustStd.Vec.Basic`

A pure model of the safe `Vec<T>` surface, as a plain `List W`.

Like `CodeLib.RustStd.Option`, this is a spec-level model rather than a
wasm-level `_wp` lemma file.  Its consumer is `Project.RustVec.Spec`, which
states the contract of each `rust_vec` export in these terms.  Lemmas about
the model arrive with the first proof that needs them.

The model carries no capacity field.  Capacity is not observable through the
safe API: no safe method reads it back, and two vectors that differ only in
capacity answer every safe query identically.  The heap-level header, where
capacity is a real word, has its own model (`VecU8` in the merge-sort
formalization); this file is the spec-level counterpart and does not overlap
with it.

Panic indexing (`v[i]`) is not modeled.  A panic compiles to a wasm trap, so
it is an outcome of the run rather than an operation of the data structure.
`get` is the total `Option`-returning form, matching `Vec::get`.
-/

namespace Wasm.RustStd.Vec

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

/-- `<[T]>::contains`, reached through `Vec`'s slice deref. -/
def contains [BEq W] (values : List W) (x : W) : Bool := values.contains x

end Wasm.RustStd.Vec
