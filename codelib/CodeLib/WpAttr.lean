import Interpreter.Wasm.Wp.Tactic

/-! Registration of the `wp_entry` and `wp_reduce` simp sets (see
`CodeLib/Wp.lean` for the members). Split out because `register_simp_attr` only
takes effect in importing modules. -/

register_simp_attr wp_entry
register_simp_attr wp_reduce
