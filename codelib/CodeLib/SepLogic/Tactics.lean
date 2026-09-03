import Iris.ProofMode

open Lean.Parser.Tactic

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

/-- Split a separating conjunction and discharge its pure left side with a
Lean proof. -/
macro "isplitl_pureexact " proof:term : tactic =>
  `(tactic|
    (isplitl []
     · ipureexact $proof))

/-- Split a separating conjunction and discharge its pure right side with a
Lean proof. -/
macro "isplitr_pureexact " proof:term : tactic =>
  `(tactic|
    (isplitr
     · ipureexact $proof))

/-- Apply an Iris entailment and frame its next spatial obligation. -/
macro "iapply_frame " rule:pmTerm : tactic =>
  `(tactic|
    (iapply $rule
     iframe))

/-- Introduce one later and discharge it with an existing spatial fact. -/
macro "ilater_exact " hypothesis:ident : tactic =>
  `(tactic|
    (inext
     iexact $hypothesis))

/-- Introduce one later, rewrite its goal, and discharge it with an existing
spatial fact. -/
macro "ilater_rw_exact " rules:rwRuleSeq " with " hypothesis:ident : tactic =>
  `(tactic|
    (inext
     rw $rules:rwRuleSeq
     iexact $hypothesis))
