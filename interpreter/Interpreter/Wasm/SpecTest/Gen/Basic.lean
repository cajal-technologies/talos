import Lean.Data.Json
import Std.Data.HashSet
import Interpreter.Wasm.SpecTest.Rng

/-!
# Input families

Every problem draws inputs from the same four families, implemented once per
input type (`Gen.Word`): edge values, exhaustive small domains, candidates
derived from the module's own constants, and seeded random inputs. Inputs are
always values of the specification's input type, so an input the specification
does not quantify over can never be generated.
-/

namespace Wasm.SpecTest

inductive Family where
  | edge
  | exhaustive
  | moduleDerived
  | random
deriving BEq, Inhabited

def Family.name : Family → String
  | .edge => "edge"
  | .exhaustive => "exhaustive"
  | .moduleDerived => "module"
  | .random => "random"

def Family.ofString? : String → Option Family
  | "edge" => some .edge
  | "exhaustive" => some .exhaustive
  | "module" => some .moduleDerived
  | "random" => some .random
  | _ => none

def Family.index : Family → Nat
  | .edge => 0
  | .exhaustive => 1
  | .moduleDerived => 2
  | .random => 3

def Family.all : List Family := [.edge, .exhaustive, .moduleDerived, .random]

/-- Parameters shared by every input type. -/
structure GenConfig where
  /-- Override for the exhaustive family's domain bound (scalar range or list length). -/
  exhaustiveTo : Option Nat := none
  /-- Longest list the random family draws. -/
  maxLen : Nat := 32
  /-- Draw random lists of exactly this length (e.g. for timing at a fixed size). -/
  fixedLen : Option Nat := none
  /-- Longest list the module-derived family builds from a constant used as a size. -/
  maxDerivedLen : Nat := 256
  /-- At most this many module-derived candidates. -/
  moduleCap : Nat := 300

/-- One input type's generators. -/
class Domain (ι : Type) where
  edges : List ι
  exhaustive : GenConfig → List ι
  /-- Candidates built from the module's constants (as values and as sizes). -/
  fromConstants : GenConfig → List Nat → List ι
  random : GenConfig → Rng → ι × Rng
  /-- Strictly simpler inputs to try when this one fails. -/
  shrink : ι → List ι
  toJson : ι → Lean.Json

/-- Keep the first occurrence of each element. -/
def dedup [BEq α] [Hashable α] (xs : List α) : List α :=
  (xs.foldl (fun (acc : Array α × Std.HashSet α) x =>
    if acc.2.contains x then acc else (acc.1.push x, acc.2.insert x)) (#[], {})).1.toList

end Wasm.SpecTest
