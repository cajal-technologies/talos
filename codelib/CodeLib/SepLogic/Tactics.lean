import Iris.ProofMode

/-! Small proof-mode patterns shared by CodeLib clients. -/

/-- Split a separating conjunction, dedicate one spatial hypothesis to the
left side, and discharge that side with the same hypothesis. -/
macro "isplitl_exact " hypothesis:ident : tactic =>
  `(tactic|
    (isplitl [$hypothesis]
     · iexact $hypothesis))
