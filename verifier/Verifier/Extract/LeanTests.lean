import Verifier.Extract.Lean

/-! Regression checks for specification source ranges, run by `lake build`. -/

namespace Verifier.Extract.LeanScan.Tests

private def findings (indent : String) : FileFindings :=
  let body := String.intercalate "\n" <|
    ["namespace Demo"] ++
    (["@[spec_of \"rust-exported\" \"demo::run\"]",
      "def RunSpec : Prop :=",
      "  True",
      "",
      "@[proves Demo.RunSpec]",
      "theorem run_correct : RunSpec := by",
      "  trivial",
      "",
      "@[spec_of \"rust-exported\" \"demo::other\"]",
      "def OtherSpec : Prop :=",
      "  open Classical in",
      "  True",
      "private def helper : Nat := 0",
      "",
      "@[spec_of \"rust-exported\" \"demo::last\"]",
      "def LastSpec : Prop :=",
      "  True",
      "end Demo"].map (indent ++ ·))
  scanFile "Spec.lean" body "demo" ["run", "other", "last"]

-- The first statement ends before the proof attribute, the second before a
-- private sibling declaration, and the last before the namespace end. The
-- deeper `open ... in` term remains part of the second statement.
private def expectedStatements (indent : String) : Array String :=
  #[s!"RunSpec : Prop :=\n{indent}  True",
    s!"OtherSpec : Prop :=\n{indent}  open Classical in\n{indent}  True",
    s!"LastSpec : Prop :=\n{indent}  True"]

example : (findings "").specs.map (·.statement) = expectedStatements "" := by
  native_decide

example : (findings "  ").specs.map (·.statement) = expectedStatements "  " := by
  native_decide

example : (findings "  ").specs.map (·.location.span.«end».line) =
    #[4, 13, 18] := by native_decide

example : (findings "  ").verifications.map (·.name) =
    #["Demo.run_correct"] := by native_decide

end Verifier.Extract.LeanScan.Tests
