import Interpreter.Wasm.Wp.Tactic

/-! Registration of the `wp_entry` simp set (see `CodeLib/Wp.lean` for the
lemmas). Split out because `register_simp_attr` only takes effect in importing
modules. -/

register_simp_attr wp_entry
