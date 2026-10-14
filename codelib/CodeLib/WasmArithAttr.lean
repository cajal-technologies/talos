import Interpreter.Wasm

/-! Declares the `wasm_arith` simp attribute. Kept separate from
`WasmArith.lean` so that `attribute [wasm_arith]` commands in that file see
the attribute after import (Lean's `initialize`-based registration is only
visible to *importing* modules, not to the registering file itself — the same
reason `register_simp_attr wp_simp` lives in `Wp/Defs.lean` and its users are
in `Wp/Atomic.lean`). -/
register_simp_attr wasm_arith
