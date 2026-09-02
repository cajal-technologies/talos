import HexEncodeStdio.AllocatorOperational

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-- A finite execution either reaches a state satisfying `post`, or ends in
the one allocator failure admitted by the public specification. -/
def ReachesOrOOM (initial : Config Universal.State)
    (post : Config Universal.State → Prop) : Prop :=
  (∃ final, Reaches initial final ∧ post final) ∨
    TrapsWith initial (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true)

theorem ReachesOrOOM.refl
    (config : Config Universal.State) (post : Config Universal.State → Prop)
    (hpost : post config) : ReachesOrOOM config post := by
  left
  exact ⟨config, ⟨[], .refl _⟩, hpost⟩

theorem ReachesOrOOM.prepend
    {initial next : Config Universal.State} {post : Config Universal.State → Prop}
    {kind : StepKind} (head : Step initial kind next)
    (tail : ReachesOrOOM next post) : ReachesOrOOM initial post := by
  rcases tail with ⟨final, hreach, hpost⟩ | htrap
  · left
    exact ⟨final, Reaches.prepend head hreach, hpost⟩
  · right
    exact TrapsWith.prepend head htrap

theorem ReachesOrOOM.prependReaches
    {initial middle : Config Universal.State}
    {post : Config Universal.State → Prop}
    (pre : Reaches initial middle) (tail : ReachesOrOOM middle post) :
    ReachesOrOOM initial post := by
  rcases tail with ⟨final, hreach, hpost⟩ | htrap
  · left
    exact ⟨final, pre.trans hreach, hpost⟩
  · right
    exact TrapsWith.prependReaches pre htrap

theorem ReachesOrOOM.bind
    {initial : Config Universal.State} {middlePost finalPost :
      Config Universal.State → Prop}
    (first : ReachesOrOOM initial middlePost)
    (next : ∀ middle, middlePost middle →
      ReachesOrOOM middle finalPost) :
    ReachesOrOOM initial finalPost := by
  rcases first with ⟨middle, hreach, hmiddle⟩ | htrap
  · exact ReachesOrOOM.prependReaches hreach (next middle hmiddle)
  · exact Or.inr htrap

theorem ReachesOrOOM.of_reaches
    {initial final : Config Universal.State}
    {post : Config Universal.State → Prop}
    (hreach : Reaches initial final) (hpost : post final) :
    ReachesOrOOM initial post := by
  exact Or.inl ⟨final, hreach, hpost⟩

end Project.HexEncodeStdio
