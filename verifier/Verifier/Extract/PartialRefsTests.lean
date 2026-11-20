import Verifier.Extract.Lean

/-! Partial contracts retain their kind and resolve exports exactly like total
contracts; missing and cross-crate targets must still produce diagnostics. -/

namespace Verifier.Extract.PartialRefsTests

private def source := "@[spec_of \"rust-exported-partial\" \"rust_vec::vec_pop\",
  spec_of \"rust-internal-partial\" \"rust_vec::pop\"]
def PopSpec : Prop := True
"

private def scanned := LeanScan.scanFile "Spec.lean" source "rust_vec" ["vec_pop"]

-- The scanner uses partial functions; test its executable results without
-- introducing native-evaluation axioms into the environment.
#eval show IO Unit from do
  let refs := (scanned.specs.toList.flatMap (·.refs)).map
    (fun r => (r.kind.toString, r.target, r.resolved))
  unless refs == [("rust-exported-partial", "rust_vec::vec_pop", true),
      ("rust-internal-partial", "rust_vec::pop", false)] do
    throw <| IO.userError "partial contract references were not preserved"
  if scanned.diagnostics.any (·.kind == "malformed_spec_of_attribute") then
    throw <| IO.userError "partial contract kinds were rejected"
  unless (LeanScan.scanFile "Spec.lean" source "rust_vec" []).diagnostics.any
      (·.kind == "unresolved_spec_of_target") do
    throw <| IO.userError "missing export did not produce a diagnostic"
  unless (LeanScan.scanFile "Spec.lean" source "other_crate" []).diagnostics.any
      (·.kind == "cross_crate_reference") do
    throw <| IO.userError "cross-crate reference did not produce a diagnostic"

end Verifier.Extract.PartialRefsTests
