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
  List.take List.length List.map ValueType.zero
  List.reverse_cons List.reverse_nil List.nil_append List.cons_append
  List.set_cons_zero List.set_cons_succ List.getElem?_cons_zero List.getElem?_cons_succ
  Nat.add_zero
