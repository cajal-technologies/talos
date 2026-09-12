import Project.Mergesort.SortWorkBudget

/-! # Arithmetic for the actual fixed-size input transfers

These lemmas discharge arithmetic joins in `InputExecutionCost.loop_cost`.
They bound the sum of scalar, copying and growth charges; that operational
theorem supplies the actual execution segments.
-/

namespace Project.Mergesort.InputWorkBudget

/-- Number of nonempty transfers at the generated 256-byte request size. -/
def chunks (bytes : Nat) : Nat := (bytes+255)/256

theorem chunks_step (current remaining : Nat) (hpositive : 0<current)
    (hshape : current=min 256 (current+remaining)) :
    chunks (current+remaining)=1+chunks remaining := by
  unfold chunks
  omega

/-- Remaining copying and growth are charged by monotonically increasing
capacity/page potentials. Bytes still in the host input will be read and copied. -/
def budget (current remaining capacity pages finalCapacity finalPages : Nat) : Nat :=
  259*chunks (current+remaining)+current+2*remaining+(finalCapacity-capacity)+
    65536*(finalPages-pages)

theorem step (current remaining capacity pages nextCapacity nextPages finalCapacity finalPages : Nat)
    (hpositive : 0<current) (hshape : current=min 256 (current+remaining))
    (hcapacity : capacity≤nextCapacity) (hfinalCapacity : nextCapacity≤finalCapacity)
    (hpages : pages≤nextPages) (hfinalPages : nextPages≤finalPages) :
    259+current+min 256 remaining+(nextCapacity-capacity)+65536*(nextPages-pages)+
      budget (min 256 remaining) (remaining-min 256 remaining)
        nextCapacity nextPages finalCapacity finalPages ≤
      budget current remaining capacity pages finalCapacity finalPages := by
  have hnext : min 256 remaining≤remaining := min_le_right _ _
  have hc := chunks_step current remaining hpositive hshape
  unfold budget
  rw [Nat.add_sub_of_le hnext]
  omega

theorem finish (current capacity pages finalCapacity finalPages : Nat)
    (hpositive : 0<current) (hsmall : current≤256) :
    259+current+(finalCapacity-capacity)+65536*(finalPages-pages)=
      budget current 0 capacity pages finalCapacity finalPages := by
  unfold budget chunks
  omega

theorem reallocation_copy (oldCapacity newCapacity : Nat)
    (hdoubled : 2*oldCapacity≤newCapacity) :
    oldCapacity≤newCapacity-oldCapacity := by omega

/-- Closed input-size bound after the 19-transition first-read setup; the
physical page increase is kept separate to telescope with later allocations. -/
def canonical (bytes : Nat) : Nat :=
  19+259*chunks bytes+2*bytes+max (2*bytes) 8

theorem initial (current remaining pages finalCapacity finalPages : Nat)
    (hcapacity : finalCapacity≤max (2*(current+remaining)) 8) :
    19+current+budget current remaining 0 pages finalCapacity finalPages≤
      canonical (current+remaining)+65536*(finalPages-pages) := by
  unfold budget canonical
  omega

end Project.Mergesort.InputWorkBudget
