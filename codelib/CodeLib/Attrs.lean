import Lean

/-!
# `@[spec_of]` and `@[proves]` — load-bearing project attributes

These two attributes are the link between Lean specifications and the code
they describe, and between proofs and the specifications they discharge.
They carry the metadata that `verifier extract` reads off the source. The
runtime behavior here is intentionally minimal — the attribute machinery
only needs to *exist* so the source typechecks; semantics live in the
extractor.

## `@[spec_of <kind> "qualified::name"]`

Marks a `def Name : Prop := …` as a formal spec linked to code or to a
crate-level property.
`<kind>` is one of:

* `rust-exported` — `target` is `crate::fn_name`, naming a wasm-exported
  Rust function (`#[unsafe(no_mangle)] pub extern "C" fn`).
* `rust-exported-partial` — the same target provenance, when the public
  proposition constrains every finite return but does not prove termination.
* `rust-internal` — any other Rust path (`crate::module::fn`). Opaque to
  the extractor.
* `rust-internal-partial` — the same internal target provenance for a
  partial-correctness proposition.
* `crate-property` — `target` is `crate::property_name`, naming a property of
  the crate rather than pretending that a composing function exists. Such a
  property may carry additional `rust-exported` references for the operations
  whose executions occur in its statement.
* `lean` — any Lean symbol. Opaque to the extractor.

A def may carry several `@[spec_of …]` attributes if it specifies more
than one symbol; each becomes a `Reference` in the extracted artifact.

## `@[proves SpecName]`

Marks a `theorem` as a verification of the named formal spec. `SpecName`
is the fully qualified name of a `@[spec_of …] def`. The theorem's stated
type is not required to be syntactically `SpecName` (a reformulation is
fine); the attribute is the source of truth for the link.

See `verifier/EXTRACT.md` (§P4, §P5, §P7) for the full discovery
contract.
-/

open Lean

namespace CodeLib

/-- `@[spec_of "<kind>" "qualified::name"]` — tag a `def : Prop` as a
formal spec linked to code or to a crate-level property. `<kind>` is one of
`"rust-exported"`, `"rust-exported-partial"`, `"rust-internal"`,
`"rust-internal-partial"`, `"crate-property"`, `"lean"`. The kind is passed
as a quoted string so that the hyphenated names don't trip up the Lean
tokenizer; the extractor sees identical text either way. See module docstring. -/
syntax (name := spec_of) "spec_of" str str : attr

/-- `@[proves SpecName]` — tag a theorem as a verification of the named
formal spec. See module docstring. -/
syntax (name := proves) "proves" ident : attr

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

end CodeLib
