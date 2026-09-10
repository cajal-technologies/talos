import Iris.ProofMode

open Lean.Parser.Tactic

/-! Small proof-mode patterns shared by CodeLib clients. -/

/-- Split a separating conjunction, dedicate one spatial hypothesis to the
left side, and discharge that side with the same hypothesis. -/
macro "isplitl_exact " hypothesis:ident : tactic =>
  `(tactic|
    (isplitl [$hypothesis]
     · iexact $hypothesis))

/-- Split off and discharge several spatial hypotheses in order. -/
syntax "isplitl_exacts" "[" ident* "]" : tactic

macro_rules
  | `(tactic| isplitl_exacts []) => `(tactic| skip)
  | `(tactic| isplitl_exacts [$hypothesis:ident $rest:ident*]) =>
      `(tactic|
        (isplitl_exact $hypothesis
         isplitl_exacts [$rest:ident*]))

/-- Rewrite an Iris goal and discharge it with an existing spatial fact. -/
macro "irw_exact " rules:rwRuleSeq " with " hypothesis:ident : tactic =>
  `(tactic|
    (rw $rules:rwRuleSeq
     iexact $hypothesis))

/-- Split off one spatial fact, rewrite that branch, and discharge it with the
same fact. -/
macro "isplitl_rw_exact " rules:rwRuleSeq " with " hypothesis:ident : tactic =>
  `(tactic|
    (isplitl [$hypothesis]
     · irw_exact $rules:rwRuleSeq with $hypothesis))

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

/-- Split off and discharge several pure right conjuncts in order. -/
syntax "isplitr_pureexacts" "[" term,* "]" : tactic

macro_rules
  | `(tactic| isplitr_pureexacts []) => `(tactic| skip)
  | `(tactic| isplitr_pureexacts [$proof:term]) =>
      `(tactic| isplitr_pureexact $proof)
  | `(tactic| isplitr_pureexacts [$proof:term, $proofs:term,*]) =>
      `(tactic|
        (isplitr_pureexact $proof
         isplitr_pureexacts [$proofs,*]))

/-- Apply an Iris entailment and frame its next spatial obligation. -/
macro "iapply_frame " rule:pmTerm : tactic =>
  `(tactic|
    (iapply $rule
     iframe))

/-- Apply an Iris entailment, frame its premise, and introduce the continuation. -/
macro "iapply_frame_intro " rule:pmTerm " as " hypothesis:introPat : tactic =>
  `(tactic|
    (iapply_frame $rule
     iintro $hypothesis))

/-- Apply an Iris entailment and frame its next obligation explicitly. -/
syntax "iapply_frame " pmTerm " using " "[" selPat* "]" : tactic

macro_rules
  | `(tactic| iapply_frame $rule:pmTerm using [$hypotheses:selPat*]) =>
      `(tactic| (iapply $rule; iframe $hypotheses*))

/-- Apply an Iris entailment, prove its first obligation, then frame the next. -/
syntax "iapply_then_frame " pmTerm " =>" ppLine colGt tacticSeq : tactic

macro_rules
  | `(tactic| iapply_then_frame $rule:pmTerm => $proof:tacticSeq) =>
      `(tactic|
        (iapply $rule
         next => $proof
         next => iframe))

/-- Apply an Iris entailment and prove its first pure premise. -/
syntax "iapply_pure " pmTerm " =>" ppLine colGt tacticSeq : tactic

macro_rules
  | `(tactic| iapply_pure $rule:pmTerm => $proof:tacticSeq) =>
      `(tactic|
        (iapply $rule
         next =>
           ipureintro
           next => $proof))

/-- Frame spatial goals, then discharge the remaining pure goal. -/
macro "iframe_pureexact " proof:term : tactic =>
  `(tactic|
    (iframe
     ipureexact $proof))

/-- Frame selected spatial hypotheses, then discharge the remaining pure goal. -/
syntax "iframe_pureexact " "using " "[" selPat* "]" " => " term : tactic

macro_rules
  | `(tactic| iframe_pureexact using [$hypotheses:selPat*] => $proof:term) =>
      `(tactic|
        (iframe $hypotheses*
         ipureexact $proof))

/-- Apply an Iris entailment and discharge its next goal with one hypothesis. -/
macro "iapply_exact " rule:pmTerm " with " hypothesis:ident : tactic =>
  `(tactic|
    (iapply $rule
     iexact $hypothesis))

/-- Apply an Iris entailment and dedicate one hypothesis to its first split. -/
macro "iapply_splitl_exact " rule:pmTerm " with " hypothesis:ident : tactic =>
  `(tactic|
    (iapply $rule
     isplitl_exact $hypothesis))

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
     irw_exact $rules:rwRuleSeq with $hypothesis))
