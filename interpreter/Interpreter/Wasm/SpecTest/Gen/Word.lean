import Interpreter.Wasm.SpecTest.Gen.Basic

/-!
# Generators for machine words, pairs of words, and lists of words

`Word` abstracts the fixed-width unsigned types a specification quantifies over.
`Domain` instances for a word, a pair of words and a list of words implement the
four families once; problems reuse them through their input type.
-/

namespace Wasm.SpecTest

class Word (α : Type) where
  bits : Nat
  toNat : α → Nat
  /-- Reduce modulo `2 ^ bits`. -/
  ofNat : Nat → α

instance : Word UInt32 := ⟨32, UInt32.toNat, UInt32.ofNat⟩
instance : Word UInt64 := ⟨64, UInt64.toNat, UInt64.ofNat⟩

namespace Word

def maxNat (α : Type) [Word α] : Nat := 2 ^ Word.bits α - 1

/-- Edge values: 0, 1, 2, 3, around the sign bit, around the lower half word,
all-ones, and every power of two. -/
def edgeNats (α : Type) [Word α] : List Nat :=
  let b := Word.bits α
  let half := b / 2
  dedup ([0, 1, 2, 3, 2 ^ (b - 1) - 1, 2 ^ (b - 1), 2 ^ half - 1, 2 ^ half, 2 ^ b - 1]
    ++ (List.range b).map (2 ^ ·))

/-- Values around a constant: `c - 1`, `c`, `c + 1`, within the word's range. -/
def around (α : Type) [Word α] (c : Nat) : List Nat :=
  [c - 1, c, c + 1].filter fun v => decide (v ≤ maxNat α)

def shrinkNat (v : Nat) : List Nat :=
  dedup ([0, 1, v / 2, v - 1].filter fun w => decide (w < v))

def pairEdgeNats (α : Type) [Word α] : List (Nat × Nat) :=
  let b := Word.bits α
  let top := maxNat α
  let core := [0, 1, 2, 2 ^ (b - 1), top]
  let product := core.flatMap fun x => core.map fun y => (x, y)
  let equal := (edgeNats α).map fun x => (x, x)
  let divides := [3, 7, 12, 2 ^ (b / 2) + 1].flatMap fun d =>
    [2, 3, 5, 2 ^ (b / 2 - 1)].filterMap fun k =>
      if d * k ≤ top then some (d, d * k) else none
  let sharedTwo := (List.range (b - 3)).flatMap fun i =>
    [(3 * 2 ^ i, 5 * 2 ^ i), (2 ^ i, 2 ^ (i + 2))].filter fun p =>
      decide (p.1 ≤ top ∧ p.2 ≤ top)
  dedup (product ++ equal ++ divides ++ divides.map Prod.swap ++ sharedTwo)

/-- Every list of length at most `n` over `alphabet`. -/
def allLists (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
    let shorter := allLists alphabet n
    dedup (shorter ++ (shorter.filter fun l => l.length == n).flatMap fun l =>
      alphabet.map (· :: l))

/-- `len` values, each small (below 8) when `small`, else magnitude-biased. -/
def randomValues (bits : Nat) (small : Bool) : Nat → Rng → List Nat → List Nat × Rng
  | 0, g, acc => (acc, g)
  | n + 1, g, acc =>
    let (v, g) := if small then g.below 8 else g.biased bits
    randomValues bits small n g (v :: acc)

end Word

open Word

instance wordDomain {α : Type} [Word α] : Domain α where
  edges := (edgeNats α).map Word.ofNat
  exhaustive cfg := (List.range (cfg.exhaustiveTo.getD 64)).map Word.ofNat
  fromConstants cfg cs := ((dedup (cs.flatMap (around α))).map Word.ofNat).take cfg.moduleCap
  random _ g := let (v, g) := g.biased (Word.bits α); (Word.ofNat v, g)
  shrink v := (shrinkNat (Word.toNat v)).map Word.ofNat
  toJson v := Lean.toJson (Word.toNat v)

/-- Pairs: combinations of core edges, equal pairs, one dividing the other, and
pairs sharing a power of two. -/
instance pairDomain {α : Type} [Word α] : Domain (α × α) where
  edges := (pairEdgeNats α).map fun p => (Word.ofNat p.1, Word.ofNat p.2)
  exhaustive cfg :=
    let k := cfg.exhaustiveTo.getD 64
    (List.range k).flatMap fun x => (List.range k).map fun y => (Word.ofNat x, Word.ofNat y)
  fromConstants cfg cs :=
    let top := maxNat α
    let vs := dedup (cs.flatMap (around α))
    let pairs := vs.flatMap fun v => [(v, v), (v, 0), (0, v), (v, 1), (v, top)]
    ((dedup pairs).map fun p => (Word.ofNat p.1, Word.ofNat p.2)).take cfg.moduleCap
  random _ g :=
    let (x, g) := g.biased (Word.bits α)
    let (mode, g) := g.below 8
    let (y, g) := g.biased (Word.bits α)
    let (k, g) := g.below 16
    let y := if mode = 0 then x
      else if mode = 1 ∧ x * (k + 2) ≤ maxNat α then x * (k + 2)
      else y
    ((Word.ofNat x, Word.ofNat y), g)
  shrink p :=
    (shrinkNat (Word.toNat p.1)).map (fun x => (Word.ofNat x, p.2))
      ++ (shrinkNat (Word.toNat p.2)).map (fun y => (p.1, Word.ofNat y))
  toJson p := Lean.Json.arr #[Lean.toJson (Word.toNat p.1), Lean.toJson (Word.toNat p.2)]

/-- Lists: shape edges (empty, singleton, all-equal, sorted, reverse-sorted,
duplicates, extremes present), every list up to length six over `{0, 1, max}`,
module constants as element values and as lengths (in bytes and in words), and
size-biased random lists. -/
instance listDomain {α : Type} [Word α] : Domain (List α) where
  edges :=
    let top := maxNat α
    let sign := 2 ^ (Word.bits α - 1)
    let nats : List (List Nat) :=
      [[], [0], [1], [top], [5, 5, 5, 5], [0, 1, 2, 3, 4, 5], [5, 4, 3, 2, 1, 0],
       [3, 1, 3, 1, 2, 2, 3], [top, 0, 1, top - 1, 0, top], [sign, sign - 1, sign + 1],
       edgeNats α, (edgeNats α).reverse]
    nats.map (·.map Word.ofNat)
  exhaustive cfg := (allLists [0, 1, maxNat α] (cfg.exhaustiveTo.getD 6)).map (·.map Word.ofNat)
  fromConstants cfg cs :=
    let width := Word.bits α / 8
    let asValues := (dedup (cs.flatMap (around α))).flatMap fun v => [[v], [v, 0], [0, v]]
    let lengths := dedup (cs.flatMap fun c =>
      [c - 1, c, c + 1] ++ [(c - 1) / width, c / width, (c + 1) / width])
    let asSizes := (lengths.filter fun n => decide (0 < n ∧ n ≤ cfg.maxDerivedLen)).map fun n =>
      (List.range n).reverse
    ((dedup (asValues ++ asSizes)).map (·.map Word.ofNat)).take cfg.moduleCap
  random cfg g :=
    let (len, g) := match cfg.fixedLen with
      | some n => (n, g)
      | none =>
        -- size class `w` uniform, then a length in `[2 ^ (w - 1), 2 ^ w)`: short and long lists are
        -- equally common, and no draw is spent on the empty list (edge and exhaustive cover it)
        let (w, g) := g.below (Nat.log2 (max cfg.maxLen 1) + 1)
        let (n, g) := g.below (2 ^ w)
        (min (2 ^ w + n) (max cfg.maxLen 1), g)
    let (small, g) := g.below 4
    let (vs, g) := randomValues (Word.bits α) (small == 0) len g []
    (vs.map Word.ofNat, g)
  shrink l :=
    let n := l.length
    let halves := if n ≥ 2 then [l.take (n / 2), l.drop (n / 2)] else []
    let removals := (List.range (min n 32)).map fun i => l.eraseIdx i
    let values := (List.range (min n 16)).flatMap fun i =>
      match l[i]? with
      | some v => (shrinkNat (Word.toNat v)).map fun w => l.set i (Word.ofNat w)
      | none => []
    halves ++ removals ++ values
  toJson l := Lean.Json.arr (l.map fun v => Lean.toJson (Word.toNat v)).toArray

end Wasm.SpecTest
