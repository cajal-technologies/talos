import Lean

/-!
# The load-bearing project attributes

These four attributes are the link between Lean specifications and the code
they describe, between proofs and the specifications they discharge, and
between a hand-written Lean model and the compiled function it stands in
for. They carry the metadata that `verifier extract` reads off the source.
The runtime behavior here is intentionally minimal — the attribute
machinery only needs to *exist* so the source typechecks; semantics live in
the extractor.

## `@[spec_of <kind> "qualified::name"]`

Marks a `def Name : Prop := …` as a formal spec linked to a code symbol.
`<kind>` is one of:

* `rust-exported` — `target` is `crate::fn_name`, naming a wasm-exported
  Rust function (`#[unsafe(no_mangle)] pub extern "C" fn`).
* `rust-internal` — any other Rust path (`crate::module::fn`). Opaque to
  the extractor.
* `lean` — any Lean symbol. Opaque to the extractor.

A def may carry several `@[spec_of …]` attributes if it specifies more
than one symbol; each becomes a `Reference` in the extracted artifact.

## `@[proves SpecName]`

Marks a `theorem` as a verification of the named formal spec. `SpecName`
is the fully qualified name of a `@[spec_of …] def`. The theorem's stated
type is not required to be syntactically `SpecName` (a reformulation is
fine); the attribute is the source of truth for the link.

## `@[rust_ref "qualified::name"]`

Marks a `def` as a hand-written Lean model of a Rust function — the
readable transliteration a proof reasons about when the compiled wasm is
too raw to state anything against. The argument is the `crate::fn_name`
join key `@[spec_of "rust-exported" …]` already uses, quoted for the same
reason: a Rust path is not a Lean identifier.

A model tagged this way *owes* an equivalence. Without a theorem tying it
to the compiled function, everything proved about the model says nothing
about the code that runs; `@[equiv_of]` is how that debt is discharged.
Neither attribute enforces the obligation — together they make owed and
discharged both visible, to a reader and to tooling.

## `@[equiv_of modelName]`

Marks a `theorem` as the equivalence a `@[rust_ref]` model owes: the
compiled function computes what the model says. `modelName` names a Lean
declaration, so it is written **bare** and registers the way `@[proves]`
does, not the way `@[spec_of]` and `@[rust_ref]` do. As with `@[proves]`,
the theorem's stated type is not constrained to any particular shape; the
attribute is the link.

`CodeLib/Attrs/Check.lean` applies both model attributes, so a build fails
if either registration here stops accepting the form documented above.

See `verifier/EXTRACT.md` (§P4, §P5, §P7) for the full discovery
contract. `extract` reads `@[spec_of]` and `@[proves]` today; `@[rust_ref]`
and `@[equiv_of]` are not part of the artifact yet.
-/

open Lean

namespace CodeLib

/-- `@[spec_of "<kind>" "qualified::name"]` — tag a `def : Prop` as a
formal spec linked to a code symbol. `<kind>` is one of
`"rust-exported"`, `"rust-internal"`, `"lean"`. The kind is passed as a
quoted string so that the hyphenated names don't trip up the Lean
tokenizer; the extractor sees identical text either way. See module
docstring. -/
syntax (name := spec_of) "spec_of" str str : attr

/-- `@[proves SpecName]` — tag a theorem as a verification of the named
formal spec. See module docstring. -/
syntax (name := proves) "proves" ident : attr

/-- `@[rust_ref "<crate>::<fn>"]` — tag a `def` as a hand-written Lean
model of the named Rust function. The target is quoted for the same reason
`spec_of`'s is: a Rust path is not a Lean identifier. A model tagged this
way owes an `@[equiv_of]`. See module docstring. -/
syntax (name := rust_ref) "rust_ref" str : attr

/-- `@[equiv_of modelName]` — tag a theorem as the equivalence a
`@[rust_ref]` model owes to the compiled function. The model is named
bare, as an identifier, not as a string. See module docstring. -/
syntax (name := equiv_of) "equiv_of" ident : attr

initialize
  Lean.registerBuiltinAttribute {
    name            := `spec_of
    descr           := "Mark a `def : Prop` as a formal spec linked to a code symbol."
    applicationTime := .afterCompilation
    add             := fun _ _ _ => pure ()
    erase           := fun _ => pure ()
  }

initialize
  Lean.registerBuiltinAttribute {
    name            := `proves
    descr           := "Mark a theorem as a verification of a named formal spec."
    applicationTime := .afterCompilation
    add             := fun _ _ _ => pure ()
    erase           := fun _ => pure ()
  }

initialize
  Lean.registerBuiltinAttribute {
    name            := `rust_ref
    descr           := "Mark a `def` as a hand-written Lean model of a Rust function."
    applicationTime := .afterCompilation
    add             := fun _ _ _ => pure ()
    erase           := fun _ => pure ()
  }

initialize
  Lean.registerBuiltinAttribute {
    name            := `equiv_of
    descr           := "Mark a theorem as the equivalence a hand-written Lean model owes."
    applicationTime := .afterCompilation
    add             := fun _ _ _ => pure ()
    erase           := fun _ => pure ()
  }

end CodeLib
