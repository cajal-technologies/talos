import CodeLib.Attrs

/-!
# Application sites for `@[rust_ref]` and `@[equiv_of]`

Registering an attribute and accepting the form its documentation shows are
two different things, and only an application site can fail — the
registration in `CodeLib/Attrs.lean` compiles whatever grammar it declares.
These two declarations are that site: the build stops here if `@[rust_ref]`
stops taking a quoted `crate::fn` target, or `@[equiv_of]` stops taking a
bare identifier.

`@[spec_of]` and `@[proves]` need no counterpart: the crates under
`programs/` apply them on every build.

Nothing below is claimed about wasm. `identity` names no Rust function and
`identityModel` models nothing — these declarations exist to be tagged.
-/

namespace CodeLib.Attrs.Check

/-- Stands in for a hand-written Lean model of a Rust function. -/
@[rust_ref "codelib_attrs_check::identity"]
def identityModel (n : Nat) : Nat := n

/-- Stands in for the equivalence `identityModel` owes to the compiled
function it models. -/
@[equiv_of identityModel]
theorem identityModel_eq (n : Nat) : identityModel n = n := rfl

end CodeLib.Attrs.Check
