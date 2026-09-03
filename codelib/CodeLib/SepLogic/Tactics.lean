import Iris.ProofMode

/-! Small proof-mode patterns shared by CodeLib clients. -/

/-- Split a separating conjunction, dedicate one spatial hypothesis to the
left side, and discharge that side with the same hypothesis. -/
macro "isplitl_exact " hypothesis:ident : tactic =>
  `(tactic|
    (isplitl [$hypothesis]
     · iexact $hypothesis))

/-- Introduce a pure Iris obligation and discharge it with a Lean proof. -/
macro "ipureexact " proof:term : tactic =>
  `(tactic|
    (ipureintro
     exact $proof))

/-- Apply an Iris entailment and frame its next spatial obligation. -/
macro "iapply_frame " rule:pmTerm : tactic =>
  `(tactic|
    (iapply $rule
     iframe))
