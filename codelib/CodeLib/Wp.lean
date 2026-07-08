import CodeLib.WpAttr

/-!
# `wp_entry` — reusable straight-line-reduction simp set

`of_returns_wp` starts a function body on the locals `(args.take n).reverse` with
an empty value stack. Reducing such a body needs, on top of `wp_simp`, the
list/locals lemmas that compute `reverse`, `set`, `getElem?`, `toLocals`, etc.
Every memory-program proof was repeating that ~16-lemma list inline; this bundles
it once. Use as `simp only [wp_simp, wp_entry, <facts>]` (numeric `if`s and
`Nat`/`UInt` literal arithmetic are handled by the default simprocs).
-/

open Wasm

attribute [wp_entry]
  Locals.get Locals.set? Function.toLocals Function.numParams
  List.take List.length List.map ValueType.zero List.drop_nil
  List.reverse_cons List.reverse_nil List.nil_append List.cons_append
  List.set_cons_zero List.set_cons_succ List.getElem?_cons_zero List.getElem?_cons_succ
  Nat.add_zero

/-! ## `wp_reduce` — the numeric/`ite` simprocs the wp proofs need

Bundles every reduction simproc a straight-line wp proof needs on the concrete
values it produces: `UInt32` literal `.toNat` and scratch-address arithmetic
(`(1048576 - 16 + 12).toNat`, which `reduceToNat` alone cannot fold — the
subtraction/addition simprocs are required), the `Nat` index arithmetic in
`Locals.get`/list lengths, and `if` elimination. Lets proofs write
`simp only [wp_simp, wp_entry, wp_reduce, <facts>]` and delete the ~19
per-file `have h : (K : UInt32).toNat = K := rfl`/`by decide` literal `have`s.
These are all core Lean simprocs — a reader can still expand the set; it hides
nothing and adds no bespoke tactic. -/
attribute [wp_reduce]
  UInt32.reduceToNat UInt32.reduceSub UInt32.reduceAdd UInt32.reduceMul
  Nat.reducePow Nat.reduceAdd Nat.reduceSub Nat.reduceLT Nat.reduceMod reduceIte
