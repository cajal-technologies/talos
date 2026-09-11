/-!
# Deterministic pseudo-random numbers

SplitMix64: a 64-bit state advanced by a Weyl increment and mixed by two
multiply-xorshift rounds. A seed fixes the whole input sequence, so a
counterexample is reproducible on any machine.
-/

namespace Wasm.SpecTest

structure Rng where
  state : UInt64
deriving Repr, Inhabited

def Rng.ofSeed (seed : UInt64) : Rng := ⟨seed⟩

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- A natural number below `bound` (`0` when `bound = 0`). -/
def Rng.below (g : Rng) (bound : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (if bound = 0 then 0 else x.toNat % bound, g)

/-- A `bits`-wide word with magnitude bias: the width `w` is uniform in
`0 ..= bits`, then the value is uniform below `2 ^ w`. Small, boundary-sized
and huge values are all common. -/
def Rng.biased (g : Rng) (bits : Nat) : Nat × Rng :=
  let (w, g) := g.below (bits + 1)
  let (x, g) := g.next
  (x.toNat % (2 ^ w), g)

end Wasm.SpecTest
