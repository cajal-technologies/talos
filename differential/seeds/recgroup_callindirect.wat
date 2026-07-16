;; Rec-group canonicalization soundness probe (the #108 class).
;;
;; $A1 and $A2 are function types in *different* rec groups. Because each rec group
;; also contains a struct that back-references the func type, the two groups are not
;; structurally equal, so $A1 and $A2 are DISTINCT types. A `call_indirect (type $A2)`
;; against a table slot holding a `$A1` function must therefore fail the type check
;; and trap.
;;
;; V8 (and the spec) trap here. A runner that canonicalizes the two rec groups to the
;; same type would accept the call and return 40 instead -- a value where the oracle
;; traps, i.e. a SOUNDNESS divergence. That was #108.
;;
;; The runner traps correctly today (`trap: indirect call type mismatch`), so this is
;; kept as a regression guard: it must keep trapping. `recgroup` mode generates many
;; more of the same class on the fly.
;;
;; The entry point is exported as "f": miscast's seed-corpus loader drives a bare
;; `.wat` through the export named `f` (its upstream seeds all follow this), so any
;; other name would make the seed-driven modes silently skip the module.
(module
  (rec (type $A1 (func (param (ref null $B1)) (result i32))) (type $B1 (struct (field (ref null $A1)))))
  (rec (type $B2 (struct (field (ref null $A2)))) (type $A2 (func (param (ref null $B2)) (result i32))))
  (func $callee (type $A1) i32.const 40)
  (table 1 funcref) (elem (i32.const 0) $callee)
  (func (export "f") (result i32) (call_indirect (type $A2) (ref.null $B2) (i32.const 0))))
