import HexEncodeStdio.ReadChunkCost
import HexEncodeStdio.ReserveResourceCost
import HexEncodeStdio.ReadChunkFull

/-! Actual first-chunk scalar and bulk-copy costs. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace Project.HexEncodeStdio.ReadChunkResourceCost
open Wasm Wasm.SmallStep Project.HexStdio ReadChunkCost

theorem read_chunk_after_read_fits_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored vector frame capacity data length count : UInt32)
    (htag : store.wasm.mem.read8 (frame + 40) = 4)
    (hcount : store.wasm.mem.read32 (frame + 44) = count)
    (hcountLt : count < 33)
    (hcountNe : count ≠ 0)
    (hcapacity : store.wasm.mem.read32 vector = capacity)
    (hdata : store.wasm.mem.read32 (vector + 4) = data)
    (hlength : store.wasm.mem.read32 (vector + 8) = length)
    (hfits : count ≤ capacity - length)
    (htagBound : frame.toNat + 40 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 44 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hcapacityBound : vector.toNat + 4 ≤
      store.wasm.mem.pages * 65536)
    (hdataBound : vector.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hlengthBound : vector.toNat + 8 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hsourceBound : (frame + 8).toNat + count.toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestinationBound : (data + length).toNat + count.toNat ≤
      store.wasm.mem.pages * 65536)
    (houtBound : out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hglobal : (globalAt? store 0).isSome = true) :
    ReadCostRun
      ({ expr := .running
          ⟨⟨[.i32 out, .i32 ignored, .i32 vector],
              [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
            readChunkAfterRead, 0, [], [],
            { locals := ⟨outerParams, outerLocalValues, stack⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩
         store := store } : Config Universal.State)
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues, stack⟩,
            code, arity, remainder, controls, calls⟩
         store := readChunkFinishedStore
           (readChunkCopiedStore store (data + length) (frame + 8) count)
           out vector count length (frame + 48) } :
        Config Universal.State) 61 count.toNat := by
  simp only [readChunkAfterRead, func1, List.drop]
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.load8U rfl (by simpa using htagBound)) rfl (by trivial)
  simp only [htag]
  apply ReadCostRun.prepend (Step.localTee rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.const rfl (by trivial)
  apply ReadCostRun.prepend (Step.eq (result := 1) (by simp)) rfl (by trivial)
  apply ReadCostRun.prepend (Step.brIf (condition := 1) (by decide) rfl) rfl (by trivial)
  simp
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.load32 rfl (by simpa using hcountBound)) rfl (by trivial)
  simp only [hcount]
  apply ReadCostRun.prepend (Step.localTee rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.const rfl (by trivial)
  apply ReadCostRun.prepend (Step.geU (result := 0) (by
    simp only [if_neg (UInt32.not_le.mpr hcountLt)])) rfl (by trivial)
  apply ReadCostRun.prepend Step.brIfZero rfl (by trivial)
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.load32 rfl (by simpa using hcapacityBound)) rfl (by trivial)
  simp only [UInt32.add_zero, hcapacity]
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.load32 rfl (by simpa using hlengthBound)) rfl (by trivial)
  simp only [hlength]
  apply ReadCostRun.prepend (Step.localTee rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.sub rfl (by trivial)
  apply ReadCostRun.prepend (Step.leU (result := 1) (by simp [hfits])) rfl (by trivial)
  apply ReadCostRun.prepend (Step.brIf (condition := 1) (by decide) rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.eqz (result := 0) (by simp [hcountNe])) rfl (by trivial)
  apply ReadCostRun.prepend Step.brIfZero rfl (by trivial)
  apply ReadCostRun.prepend (Step.exitControl rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.eqz (result := 0) (by simp [hcountNe])) rfl (by trivial)
  apply ReadCostRun.prepend Step.brIfZero rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.load32 rfl (by simpa using hdataBound)) rfl (by trivial)
  simp only [hdata]
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.add rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.const rfl (by trivial)
  apply ReadCostRun.prepend Step.add rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  rw [show 8 + frame = frame + 8 by bv_normalize (config := { enums := false }),
    show length + data = data + length by bv_normalize (config := { enums := false })]
  apply ReadCostRun.prepend_bulk (bulk := count.toNat) (bytes := 0) (by
    simpa only [setMemory_eq] using
      (Step.memoryCopy32 hdestinationBound hsourceBound)) rfl (by trivial)
  apply ReadCostRun.prepend (Step.exitControl rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.store32 rfl (by
    simpa [Mem.copy_pages] using houtBound)) rfl (by trivial)
  rw [setMemory_eq]
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.const rfl (by trivial)
  apply ReadCostRun.prepend (Step.store8 rfl (by
    simpa [Mem.copy_pages] using (show out.toNat + 1 ≤
      store.wasm.mem.pages * 65536 by omega))) rfl (by trivial)
  rw [setMemory_eq]
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.add rfl (by trivial)
  apply ReadCostRun.prepend (Step.store32 rfl (by
    change vector.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536
    exact hlengthBound)) rfl (by trivial)
  rw [setMemory_eq]
  apply ReadCostRun.prepend (Step.exitControl rfl) rfl (by trivial)
  simp
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.const rfl (by trivial)
  apply ReadCostRun.prepend Step.add rfl (by trivial)
  rw [show 48 + frame = frame + 48 by bv_normalize (config := { enums := false })]
  apply ReadCostRun.prepend (Step.globalSet (by
    simpa [readChunkCopiedStore, globalAt?] using hglobal)) rfl (by trivial)
  rw [setGlobal_zero_eq]
  apply ReadCostRun.prepend (Step.returnFromCallExplicit rfl) rfl (by trivial)
  simp [readChunkCopiedStore, readChunkFinishedStore,
    resumeCaller]
  exact ⟨[], CostedSteps.refl _, rfl, by simp⟩

theorem read_chunk_after_read_eof_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored vector frame capacity length : UInt32)
    (htag : store.wasm.mem.read8 (frame + 40) = 4)
    (hcount : store.wasm.mem.read32 (frame + 44) = 0)
    (hcapacity : store.wasm.mem.read32 vector = capacity)
    (hlength : store.wasm.mem.read32 (vector + 8) = length)
    (htagBound : frame.toNat + 40 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 44 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hcapacityBound : vector.toNat + 4 ≤
      store.wasm.mem.pages * 65536)
    (hlengthBound : vector.toNat + 8 + 4 ≤
      store.wasm.mem.pages * 65536)
    (houtBound : out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hglobal : (globalAt? store 0).isSome = true) :
    ReadCostRun
      ({ expr := .running
          ⟨⟨[.i32 out, .i32 ignored, .i32 vector],
              [.i32 frame, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
            readChunkAfterRead, 0, [], [],
            { locals := ⟨outerParams, outerLocalValues, stack⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩
         store := store } : Config Universal.State)
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues, stack⟩,
            code, arity, remainder, controls, calls⟩
         store := readChunkFinishedStore store out vector 0 length
           (frame + 48) } : Config Universal.State) 47 0 := by
  simp only [readChunkAfterRead, func1, List.drop]
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.load8U rfl (by simpa using htagBound)) rfl (by trivial)
  simp only [htag]
  apply ReadCostRun.prepend (Step.localTee rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.const rfl (by trivial)
  apply ReadCostRun.prepend (Step.eq (result := 1) (by simp)) rfl (by trivial)
  apply ReadCostRun.prepend (Step.brIf (condition := 1) (by decide) rfl) rfl (by trivial)
  simp
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.load32 rfl (by simpa using hcountBound)) rfl (by trivial)
  simp only [hcount]
  apply ReadCostRun.prepend (Step.localTee rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.const rfl (by trivial)
  apply ReadCostRun.prepend (Step.geU (result := 0) (by decide)) rfl (by trivial)
  apply ReadCostRun.prepend Step.brIfZero rfl (by trivial)
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend Step.block rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.load32 rfl (by simpa using hcapacityBound)) rfl (by trivial)
  simp only [UInt32.add_zero, hcapacity]
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.load32 rfl (by simpa using hlengthBound)) rfl (by trivial)
  simp only [hlength]
  apply ReadCostRun.prepend (Step.localTee rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.sub rfl (by trivial)
  apply ReadCostRun.prepend (Step.leU (result := 1) (by simp)) rfl (by trivial)
  apply ReadCostRun.prepend (Step.brIf (condition := 1) (by decide) rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.eqz (result := 1) (by simp)) rfl (by trivial)
  apply ReadCostRun.prepend (Step.brIf (condition := 1) (by decide) rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.store32 rfl (by simpa using houtBound)) rfl (by trivial)
  rw [setMemory_eq]
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.const rfl (by trivial)
  apply ReadCostRun.prepend (Step.store8 rfl (by
    change out.toNat + 1 ≤ store.wasm.mem.pages * 65536
    omega)) rfl (by trivial)
  rw [setMemory_eq]
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.add rfl (by trivial)
  apply ReadCostRun.prepend (Step.store32 rfl (by
    change vector.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536
    exact hlengthBound)) rfl (by trivial)
  rw [setMemory_eq]
  apply ReadCostRun.prepend (Step.exitControl rfl) rfl (by trivial)
  simp
  apply ReadCostRun.prepend (Step.localGet rfl) rfl (by trivial)
  apply ReadCostRun.prepend Step.const rfl (by trivial)
  apply ReadCostRun.prepend Step.add rfl (by trivial)
  rw [show 48 + frame = frame + 48 by bv_normalize (config := { enums := false })]
  apply ReadCostRun.prepend (Step.globalSet (by
    simpa [globalAt?] using hglobal)) rfl (by trivial)
  rw [setGlobal_zero_eq]
  apply ReadCostRun.prepend (Step.returnFromCallExplicit rfl) rfl (by trivial)
  simp [readChunkFinishedStore, resumeCaller]
  exact ⟨[], CostedSteps.refl _, rfl, by simp⟩

/-- A bounded scalar segment whose byte charge is exact. -/
def ChunkCostOutcome (initial : Config Universal.State) (post : Config Universal.State→Prop)
    (bound bytes : Nat) : Prop :=
  ∃ final scalar, scalar≤bound ∧ ReadCostRun initial final scalar bytes ∧ post final

private theorem ChunkCostOutcome.prepend {initial middle : Config Universal.State}
    {post : Config Universal.State→Prop} {kind : StepKind} {bound bytes : Nat}
    (head : Step initial kind middle) (unit : CostedStdIO.work initial kind middle=1)
    (allowed : HostPrimaryMemoryKind kind) (tail : ChunkCostOutcome middle post bound bytes) :
    ChunkCostOutcome initial post (bound+1) bytes := by
  obtain ⟨final,scalar,hscalar,run,result⟩ := tail
  exact ⟨final,scalar+1,Nat.add_le_add_right hscalar 1,run.prepend head unit allowed,result⟩

private theorem ChunkCostOutcome.prepend_bulk {initial middle : Config Universal.State}
    {post : Config Universal.State→Prop} {kind : StepKind} {bound bytes bulk : Nat}
    (head : Step initial kind middle) (charge : CostedStdIO.work initial kind middle=1+bulk)
    (allowed : HostPrimaryMemoryKind kind) (tail : ChunkCostOutcome middle post bound bytes) :
    ChunkCostOutcome initial post (bound+1) (bulk+bytes) := by
  obtain ⟨final,scalar,hscalar,run,result⟩ := tail
  exact ⟨final,scalar+1,Nat.add_le_add_right hscalar 1,run.prepend_bulk head charge allowed,result⟩

private theorem ChunkCostOutcome.bind {initial : Config Universal.State}
    {middlePost post : Config Universal.State→Prop} {b₁ b₂ bytes₁ bytes₂ : Nat}
    (first : ChunkCostOutcome initial middlePost b₁ bytes₁)
    (second : ∀middle,middlePost middle→ChunkCostOutcome middle post b₂ bytes₂) :
    ChunkCostOutcome initial post (b₁+b₂) (bytes₁+bytes₂) := by
  obtain ⟨middle,s₁,hs₁,⟨front,firstRun,firstLength,firstLabels⟩,hmiddle⟩ := first
  obtain ⟨final,s₂,hs₂,⟨tail,secondRun,secondLength,secondLabels⟩,hfinal⟩ := second middle hmiddle
  refine ⟨final,s₁+s₂,Nat.add_le_add hs₁ hs₂,⟨front++tail,?_,by simp [firstLength,secondLength],?_⟩,hfinal⟩
  · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using firstRun.trans secondRun
  · intro kind member
    rcases List.mem_append.mp member with hm|hm
    · exact firstLabels kind hm
    · exact secondLabels kind hm

private theorem ChunkCostOutcome.refl {config : Config Universal.State}
    {post : Config Universal.State→Prop} (hpost : post config) :
    ChunkCostOutcome config post 0 0 :=
  ⟨config,0,le_refl _,⟨[],CostedSteps.refl _,rfl,by simp⟩,hpost⟩

private theorem reserve_outcome
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (vector length additional capacity data sp bump : UInt32)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0=Module.memoryHardCap)
    (hpages : store.wasm.mem.pages≤Module.memoryHardCap)
    (hglobal : globalAt? store 0=some (.i32 sp))
    (hsum : reserveRequired length additional≥additional)
    (hcapacity : store.wasm.mem.read32 vector=capacity)
    (hdata : store.wasm.mem.read32 (vector+4)=data)
    (hread : store.wasm.mem.read32 1053960=bump)
    (hcursor : 1053960+4≤store.wasm.mem.pages*65536)
    (hfit : (allocatorBase bump).toNat+(reserveNewCapacity length additional capacity).toNat<2147483648)
    (hold : capacity.toNat<(reserveNewCapacity length additional capacity).toNat)
    (hsource : data.toNat+capacity.toNat≤store.wasm.mem.pages*65536)
    (hframe : (sp-16).toNat+16≤store.wasm.mem.pages*65536)
    (houtNoWrap : ((sp-16)+4).toNat=(sp-16).toNat+4)
    (houtNext : (((sp-16)+4)+4).toNat=((sp-16)+4).toNat+4)
    (hvector : vector.toNat+8≤store.wasm.mem.pages*65536) :
    ChunkCostOutcome
      ⟨.running ⟨⟨params,localValues,[.i32 additional,.i32 length,.i32 vector]++stack⟩,
          .call 5::code,arity,remainder,controls,calls⟩,store⟩
      (fun final => ∃ allocated,
        ByteGrowSuccess (reserveFrameStore store (sp-16)) capacity data
          (reserveNewCapacity length additional capacity) bump allocated ∧
        final=growResultFinal
          (reserveFinishStore (growResultOkStore allocated ((sp-16)+4)
            (allocatorPtr bump 1) (reserveNewCapacity length additional capacity))
            vector (allocatorPtr bump 1) (reserveNewCapacity length additional capacity) sp)
          params localValues stack code arity remainder controls calls)
      163 (capacity.toNat+65536*(AllocatorResourceCost.requiredPages
        ((allocatorBase bump).toNat+(reserveNewCapacity length additional capacity).toNat)-store.wasm.mem.pages)) := by
  obtain ⟨trace,length,run,success,labels⟩ := ReserveResourceCost.reserve_cost store params localValues stack code arity
    remainder controls calls vector length additional capacity data sp bump hmodule hcap hpages hglobal hsum hcapacity
    hdata hread hcursor hfit hold hsource hframe houtNoWrap houtNext hvector
  refine ⟨_,trace.length,?_,⟨trace,?_,rfl,?_⟩,_,success,rfl⟩
  · split_ifs at length <;> omega
  · simpa only [Nat.add_assoc,ReserveResourceCost.finalStore] using run
  · intro kind member
    cases kind with
    | host => trivial
    | instruction instruction => exact labels _ member
    | administrative admin => exact labels _ member

theorem read_chunk_after_read_reserve_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored vector frame capacity data length count oldBump : UInt32)
    (htag : store.wasm.mem.read8 (frame + 40) = 4)
    (hcount : store.wasm.mem.read32 (frame + 44) = count)
    (hcountLt : count < 33) (hcountNe : count ≠ 0)
    (hnotFits : ¬ count ≤ capacity - length)
    (hcapacity : store.wasm.mem.read32 vector = capacity)
    (hdata : store.wasm.mem.read32 (vector + 4) = data)
    (hlength : store.wasm.mem.read32 (vector + 8) = length)
    (hbump : store.wasm.mem.read32 1053960 = oldBump)
    (hmod : store.runtime.currentModule = «module»)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0=Module.memoryHardCap)
    (hglobal : globalAt? store 0 = some (.i32 frame))
    (htagBound : frame.toNat + 40 + 1 ≤ store.wasm.mem.pages * 65536)
    (hcountBound : frame.toNat + 44 + 4 ≤ store.wasm.mem.pages * 65536)
    (hcapacityBound : vector.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdataBound : vector.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hlengthBound : vector.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (hbumpBound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 65536)
    (hsum : reserveRequired length count ≥ count)
    (hfit : (allocatorBase oldBump).toNat+(reserveNewCapacity length count capacity).toNat<2147483648)
    (hold : capacity.toNat<(reserveNewCapacity length count capacity).toNat)
    (hreserveFrame : (frame - 16).toNat + 16 ≤
      store.wasm.mem.pages * 65536)
    (hreserveOutNo : ((frame - 16) + 4).toNat =
      (frame - 16).toNat + 4)
    (hreserveOutNext : (((frame - 16) + 4) + 4).toNat =
      ((frame - 16) + 4).toNat + 4)
    (hsource : data.toNat+capacity.toNat≤store.wasm.mem.pages*65536)
    (hsuccessFacts : ∀ allocStore,
      ByteGrowSuccess (reserveFrameStore store (frame - 16)) capacity data
          (reserveNewCapacity length count capacity) oldBump allocStore →
      let reserved := reserveFinishStore
        (growResultOkStore allocStore ((frame - 16) + 4)
          (allocatorPtr oldBump 1)
          (reserveNewCapacity length count capacity))
        vector (allocatorPtr oldBump 1)
          (reserveNewCapacity length count capacity) frame
      reserved.wasm.mem.read32 (vector + 4) = allocatorPtr oldBump 1 ∧
      reserved.wasm.mem.read32 (vector + 8) = length ∧
      (frame + 8).toNat + count.toNat ≤
        reserved.wasm.mem.pages * 65536 ∧
      (allocatorPtr oldBump 1 + length).toNat + count.toNat ≤
        reserved.wasm.mem.pages * 65536 ∧
      out.toNat + 4 + 4 ≤ reserved.wasm.mem.pages * 65536 ∧
      vector.toNat + 4 + 4 ≤ reserved.wasm.mem.pages * 65536 ∧
      vector.toNat + 8 + 4 ≤ reserved.wasm.mem.pages * 65536 ∧
      (globalAt? reserved 0).isSome = true) :
    ChunkCostOutcome
      (readChunkAfterReadConfig store outerParams outerLocalValues stack code
        arity remainder controls calls out ignored vector frame)
      (fun final => ∃ allocStore,
        ByteGrowSuccess (reserveFrameStore store (frame - 16)) capacity data
          (reserveNewCapacity length count capacity) oldBump allocStore ∧
        let reserved := reserveFinishStore
          (growResultOkStore allocStore ((frame - 16) + 4)
            (allocatorPtr oldBump 1)
            (reserveNewCapacity length count capacity))
          vector (allocatorPtr oldBump 1)
            (reserveNewCapacity length count capacity) frame
        final =
          { expr := .running
              ⟨⟨outerParams, outerLocalValues, stack⟩,
                code, arity, remainder, controls, calls⟩
            store := readChunkFinishedStore
              (readChunkCopiedStore reserved
                (allocatorPtr oldBump 1 + length) (frame + 8) count)
              out vector count length (frame + 48) }) 227 (capacity.toNat+65536*(AllocatorResourceCost.requiredPages
      ((allocatorBase oldBump).toNat+(reserveNewCapacity length count capacity).toNat)-store.wasm.mem.pages)+count.toNat) := by
  simp only [readChunkAfterReadConfig, readChunkCalls, readChunkCallerFrame,
    readChunkAfterRead, func1, List.drop]
  apply ChunkCostOutcome.prepend Step.block rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.block rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.block rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.load8U rfl (by simpa using htagBound)) rfl (by trivial)
  simp only [htag]
  apply ChunkCostOutcome.prepend (Step.localTee rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.const rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.eq (result := 1) (by simp)) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.brIf (condition := 1) (by decide) rfl) rfl (by trivial)
  simp
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.load32 rfl (by simpa using hcountBound)) rfl (by trivial)
  simp only [hcount]
  apply ChunkCostOutcome.prepend (Step.localTee rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.const rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.geU (result := 0) (by
    simp only [if_neg (UInt32.not_le.mpr hcountLt)])) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.brIfZero rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.block rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.block rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.block rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.load32 rfl (by simpa using hcapacityBound)) rfl (by trivial)
  simp only [UInt32.add_zero, hcapacity]
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.load32 rfl (by simpa using hlengthBound)) rfl (by trivial)
  simp only [hlength]
  apply ChunkCostOutcome.prepend (Step.localTee rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.sub rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.leU (result := 0) (by simp [hnotFits])) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.brIfZero rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.bind (b₂ := 34) (bytes₂ := count.toNat)
    (reserve_outcome store _ _ [] _ _ _ _ _ vector length count capacity data frame oldBump
      hmod hcap (Nat.le_of_lt hpages) hglobal hsum hcapacity hdata hbump hbumpBound hfit hold hsource
      hreserveFrame hreserveOutNo hreserveOutNext (by omega))
  intro middle hmiddle
  rcases hmiddle with ⟨allocStore, hsuccess, rfl⟩
  dsimp only [growResultFinal]
  obtain ⟨hreservedData, hreservedLength, hsourceBound, hdestBound,
    houtBound, hreservedDataBound, hlengthBound, hreservedGlobal⟩ :=
      hsuccessFacts allocStore hsuccess
  let reserved := reserveFinishStore
    (growResultOkStore allocStore ((frame - 16) + 4)
      (allocatorPtr oldBump 1)
      (reserveNewCapacity length count capacity))
    vector (allocatorPtr oldBump 1)
      (reserveNewCapacity length count capacity) frame
  change ChunkCostOutcome
    { expr := .running _
      store := reserved } _ 34 count.toNat
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.load32 rfl (by
    change vector.toNat + 8 + 4 ≤ reserved.wasm.mem.pages * 65536
    exact hlengthBound)) rfl (by trivial)
  rw [hreservedLength]
  apply ChunkCostOutcome.prepend (Step.localSet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.br rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.eqz (result := 0) (by simp [hcountNe])) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.brIfZero rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.load32 rfl (by
    change vector.toNat + 4 + 4 ≤ reserved.wasm.mem.pages * 65536
    exact hreservedDataBound)) rfl (by trivial)
  rw [hreservedData]
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.add rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.const rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.add rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  rw [show 8 + frame = frame + 8 by bv_normalize (config := { enums := false }),
    show length + allocatorPtr oldBump 1 =
      allocatorPtr oldBump 1 + length by bv_normalize (config := { enums := false })]
  apply ChunkCostOutcome.prepend_bulk (bulk := count.toNat) (bytes := 0) (by
    simpa only [setMemory_eq] using
      (Step.memoryCopy32 hdestBound hsourceBound)) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.exitControl rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.store32 rfl (by
    simpa [Mem.copy_pages] using houtBound)) rfl (by trivial)
  rw [setMemory_eq]
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.const rfl (by trivial)
  have houtOne : out.toNat + 1 ≤ reserved.wasm.mem.pages * 65536 := by
    exact (Nat.le_trans
      (by omega : out.toNat + 1 ≤ out.toNat + 4 + 4) houtBound)
  apply ChunkCostOutcome.prepend (Step.store8 rfl (by
    change out.toNat + 1 ≤ reserved.wasm.mem.pages * 65536
    exact houtOne)) rfl (by trivial)
  rw [setMemory_eq]
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.add rfl (by trivial)
  apply ChunkCostOutcome.prepend (Step.store32 rfl (by
    change vector.toNat + 8 + 4 ≤ reserved.wasm.mem.pages * 65536
    exact hlengthBound)) rfl (by trivial)
  rw [setMemory_eq]
  apply ChunkCostOutcome.prepend (Step.exitControl rfl) rfl (by trivial)
  simp
  apply ChunkCostOutcome.prepend (Step.localGet rfl) rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.const rfl (by trivial)
  apply ChunkCostOutcome.prepend Step.add rfl (by trivial)
  rw [show 48 + frame = frame + 48 by bv_normalize (config := { enums := false })]
  apply ChunkCostOutcome.prepend (Step.globalSet (by
    simpa [reserved, globalAt?] using hreservedGlobal)) rfl (by trivial)
  rw [setGlobal_zero_eq]
  apply ChunkCostOutcome.prepend (Step.returnFromCallExplicit (by
    have hruntime := hsuccess.runtime_eq
    exact (congrArg (fun runtime => runtime.entry) hruntime).symm)) rfl (by trivial)
  apply ChunkCostOutcome.refl
  refine ⟨allocStore, hsuccess, ?_⟩
  simp [readChunkCopiedStore, readChunkFinishedStore,
    resumeCaller]

private theorem ChunkCostOutcome.of_read {initial final : Config Universal.State}
    {post : Config Universal.State→Prop} {scalar bound bytes : Nat}
    (run : ReadCostRun initial final scalar bytes) (hbound : scalar≤bound) (result : post final) :
    ChunkCostOutcome initial post bound bytes := ⟨final,scalar,hbound,run,result⟩

private theorem ChunkCostOutcome.prepend_read {initial middle : Config Universal.State}
    {post : Config Universal.State→Prop} {scalar bound firstBytes lastBytes : Nat}
    (first : ReadCostRun initial middle scalar firstBytes)
    (tail : ChunkCostOutcome middle post bound lastBytes) :
    ChunkCostOutcome initial post (scalar+bound) (firstBytes+lastBytes) := by
  apply ChunkCostOutcome.bind (ChunkCostOutcome.of_read first (le_refl _) rfl)
  intro config equality
  subst config
  exact tail

theorem first_chunk_after_read_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (bytes : List UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0=Module.memoryHardCap)
    (hglobal : globalAt? store 0 = some (.i32 readToEndStack))
    (hbytes : bytes = store.wasm.host.stdio.input.take 32)
    (hpages : store.wasm.mem.pages = 17)
    (hcapacity : store.wasm.mem.read32 readToEndVector = 0)
    (hdata : store.wasm.mem.read32 (readToEndVector + 4) = 1)
    (hlength : store.wasm.mem.read32 (readToEndVector + 8) = 0)
    (hbump : store.wasm.mem.read32 1053960 = 0) :
    let after := readAdapterResultStore
      (readChunkFrameStore store firstChunkFrame)
      firstChunkResult firstChunkBuffer bytes
    let count := UInt32.ofNat bytes.length
    ChunkCostOutcome
      (readChunkAfterReadConfig after outerParams outerLocalValues stack code arity remainder controls calls
        readToEndResult readToEndIgnored readToEndVector firstChunkFrame)
      (fun final =>
        if bytes = [] then
          final =
            { expr := .running
                ⟨⟨outerParams, outerLocalValues, stack⟩,
                  code, arity, remainder, controls, calls⟩
              store := readChunkFinishedStore after readToEndResult
                readToEndVector 0 0 readToEndStack }
        else
          ∃ allocStore,
            ByteGrowSuccess
                (reserveFrameStore after (firstChunkFrame - 16))
                0 1 (reserveNewCapacity 0 count 0) 0 allocStore ∧
            let reserved := reserveFinishStore
              (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
                (allocatorPtr 0 1) (reserveNewCapacity 0 count 0))
              readToEndVector (allocatorPtr 0 1)
                (reserveNewCapacity 0 count 0) firstChunkFrame
            final =
              { expr := .running
                  ⟨⟨outerParams, outerLocalValues, stack⟩,
                    code, arity, remainder, controls, calls⟩
                store := readChunkFinishedStore
                  (readChunkCopiedStore reserved
                    (allocatorPtr 0 1) firstChunkBuffer count)
                  readToEndResult readToEndVector count 0 readToEndStack }) 227 bytes.length := by
  dsimp only
  simp only [readToEndStack, readToEndVector, readToEndResult,
    readToEndIgnored, firstChunkFrame, firstChunkBuffer,
    firstChunkResult] at *
  let after := readAdapterResultStore
    (readChunkFrameStore store firstChunkFrame)
    firstChunkResult firstChunkBuffer bytes
  let count := UInt32.ofNat bytes.length
  have hlen : bytes.length ≤ 32 := by
    rw [hbytes, List.length_take]
    omega
  have hcountNat : count.toNat = bytes.length := by
    have hsmall : bytes.length < UInt32.size := by
      change bytes.length < 4294967296
      omega
    simp [count, Nat.mod_eq_of_lt hsmall]
  have hcountLt : count < 33 := by
    rw [UInt32.lt_iff_toNat_lt, hcountNat]
    have h33 : (33 : UInt32).toNat = 33 := by decide
    rw [h33]
    omega
  have htag : after.wasm.mem.read8 (firstChunkFrame + 40) = 4 := by
    apply readAdapterResultStore_read_tag
    decide
  have hcount : after.wasm.mem.read32 (firstChunkFrame + 44) = count := by
    simpa [after, count] using
      readAdapterResultStore_read_count
        (readChunkFrameStore store firstChunkFrame)
        firstChunkResult firstChunkBuffer bytes
  have hafterCapacity : after.wasm.mem.read32 readToEndVector = 0 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame store firstChunkFrame
        readToEndVector (by decide) (by decide) (by decide) (by decide)).trans
        hcapacity
    all_goals (simp_all <;> omega)
  have hafterData : after.wasm.mem.read32 (readToEndVector + 4) = 1 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame store firstChunkFrame
        (readToEndVector + 4) (by decide) (by decide) (by decide)
        (by decide)).trans hdata
    all_goals (simp_all <;> omega)
  have hafterLength : after.wasm.mem.read32 (readToEndVector + 8) = 0 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame store firstChunkFrame
        (readToEndVector + 8) (by decide) (by decide) (by decide)
        (by decide)).trans hlength
    all_goals (simp_all <;> omega)
  have hafterBump : after.wasm.mem.read32 1053960 = 0 := by
    rw [readAdapterResultStore_read32_disjoint]
    · exact (readChunkFrameStore_read32_after_frame store firstChunkFrame
        1053960 (by decide) (by decide) (by decide) (by decide)).trans hbump
    all_goals (simp_all <;> omega)
  have hafterGlobal : globalAt? after 0 = some (.i32 firstChunkFrame) := by
    rw [readAdapterResultStore_globalAt]
    exact readChunkFrameStore_global_zero store firstChunkFrame readToEndStack
      hglobal
  have hafterPages : after.wasm.mem.pages = 17 := by
    simpa [after] using hpages
  have hafterMod : after.runtime.currentModule = «module» := by
    simpa [after] using hmod
  have hafterCap : after.wasm.memoryCap after.runtime.currentModule 0=Module.memoryHardCap := hcap
  have hframe48 : (1048464:UInt32)+48=1048512 := by decide
  have hframe8 : (1048464:UInt32)+8=1048472 := by decide
  by_cases hempty : bytes = []
  · simp only [if_pos hempty]
    have hcountZero : count = 0 := by simp [count, hempty]
    have hsuffix := read_chunk_after_read_eof_cost after outerParams
      outerLocalValues stack code arity remainder controls calls
      readToEndResult readToEndIgnored readToEndVector firstChunkFrame
      0 0 htag (by simpa [hcountZero] using hcount) hafterCapacity
      hafterLength (by rw [hafterPages]; decide)
      (by rw [hafterPages]; decide) (by rw [hafterPages]; decide)
      (by rw [hafterPages]; decide) (by rw [hafterPages]; decide)
      (by simp [hafterGlobal])
    refine ⟨_,47,by decide,?_,rfl⟩
    simpa only [after,readChunkAfterReadConfig,readChunkCalls,readChunkCallerFrame,
      firstChunkFrame,firstChunkResult,firstChunkBuffer,readToEndResult,readToEndVector,readToEndIgnored,
      hempty,List.length_nil,hframe48] using hsuffix
  · simp only [if_neg hempty]
    have hcountNe : count ≠ 0 := by
      intro hz
      have : count.toNat = 0 := congrArg UInt32.toNat hz
      rw [hcountNat] at this
      have hpos : 0 < bytes.length := List.length_pos_iff.mpr hempty
      omega
    have hnotFits : ¬ count ≤ (0 : UInt32) - 0 := by
      simp [hcountNe]
    have hcountPos : 0 < count := UInt32.pos_iff_ne_zero.mpr hcountNe
    have hnewLe : (reserveNewCapacity 0 count 0).toNat ≤ 32 := by
      by_cases hc : count > 8
      · simp [reserveNewCapacity, reserveCandidate, reserveRequired,
          reserveDoubled, hc, hcountPos, hcountNat]
        exact hlen
      · simp [reserveNewCapacity, reserveCandidate, reserveRequired,
          reserveDoubled, hc, hcountPos]
    have hsuccessFacts : ∀ allocStore,
        ByteGrowSuccess
            (reserveFrameStore after (firstChunkFrame - 16)) 0 1
            (reserveNewCapacity 0 count 0) 0 allocStore →
        let reserved := reserveFinishStore
          (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
            (allocatorPtr 0 1) (reserveNewCapacity 0 count 0))
          readToEndVector (allocatorPtr 0 1)
            (reserveNewCapacity 0 count 0) firstChunkFrame
        reserved.wasm.mem.read32 (readToEndVector + 4) = allocatorPtr 0 1 ∧
        reserved.wasm.mem.read32 (readToEndVector + 8) = 0 ∧
        (firstChunkFrame + 8).toNat + count.toNat ≤
          reserved.wasm.mem.pages * 65536 ∧
        (allocatorPtr 0 1 + 0).toNat + count.toNat ≤
          reserved.wasm.mem.pages * 65536 ∧
        readToEndResult.toNat + 4 + 4 ≤
          reserved.wasm.mem.pages * 65536 ∧
        readToEndVector.toNat + 4 + 4 ≤
          reserved.wasm.mem.pages * 65536 ∧
        readToEndVector.toNat + 8 + 4 ≤
          reserved.wasm.mem.pages * 65536 ∧
        (globalAt? reserved 0).isSome = true := by
      intro allocStore hsuccess
      let postGrow := growResultOkStore allocStore
        ((firstChunkFrame - 16) + 4) (allocatorPtr 0 1)
        (reserveNewCapacity 0 count 0)
      let reserved := reserveFinishStore postGrow readToEndVector
        (allocatorPtr 0 1) (reserveNewCapacity 0 count 0) firstChunkFrame
      have hmono := hsuccess.pages_mono
      have hbasePages :
          (reserveFrameStore after (firstChunkFrame - 16)).wasm.mem.pages =
            17 := by simpa using hafterPages
      have hpages17 : 17 ≤ allocStore.wasm.mem.pages := by
        rw [← hbasePages]
        exact hmono
      have hreservedPages : reserved.wasm.mem.pages = allocStore.wasm.mem.pages := by
        simp [reserved, postGrow]
      have hglobalBase : globalAt?
          (reserveFrameStore after (firstChunkFrame - 16)) 0 =
          some (.i32 (firstChunkFrame - 16)) :=
        reserveFrameStore_global_zero after _ firstChunkFrame hafterGlobal
      have hglobalAlloc : (globalAt? allocStore 0).isSome = true := by
        have heq : globalAt? allocStore 0 =
            some (.i32 (firstChunkFrame - 16)) :=
          (hsuccess.globalAt_eq 0).trans hglobalBase
        simp [heq]
      have hglobalPost : globalAt? postGrow 0 = globalAt? allocStore 0 := by
        simp [postGrow]
      refine ⟨reserveFinishStore_read_data postGrow readToEndVector
          (allocatorPtr 0 1) (reserveNewCapacity 0 count 0) firstChunkFrame,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply reserveFinishStore_read_length_of_fresh
          (store := reserveFrameStore after (firstChunkFrame - 16))
          (allocStore := allocStore) (frame := firstChunkFrame - 16)
          (vector := readToEndVector) (oldPtr := 1)
          (newCapacity := reserveNewCapacity 0 count 0)
          (oldBump := 0) (length := 0) hsuccess
        · simpa [reserveFrameStore] using hafterLength
        all_goals decide
      · rw [hreservedPages]
        have hc : count.toNat ≤ 32 := hcountNat ▸ hlen
        change 1048472 + count.toNat ≤ allocStore.wasm.mem.pages * 65536
        omega
      · rw [hreservedPages]
        have hc : count.toNat ≤ 32 := hcountNat ▸ hlen
        change 1054000 + count.toNat ≤ allocStore.wasm.mem.pages * 65536
        omega
      · rw [hreservedPages]
        change 1048536 ≤ allocStore.wasm.mem.pages * 65536
        omega
      · rw [hreservedPages]
        change 1048524 ≤ allocStore.wasm.mem.pages * 65536
        omega
      · rw [hreservedPages]
        change 1048528 ≤ allocStore.wasm.mem.pages * 65536
        omega
      · apply Option.isSome_iff_exists.mpr
        exact ⟨.i32 firstChunkFrame,
          reserveFinishStore_global_zero postGrow readToEndVector
            (allocatorPtr 0 1) (reserveNewCapacity 0 count 0)
            firstChunkFrame (firstChunkFrame - 16)
            (by simpa [postGrow, hglobalPost] using
              (show globalAt? allocStore 0 =
                  some (.i32 (firstChunkFrame - 16)) from
                (hsuccess.globalAt_eq 0).trans hglobalBase))⟩
    have hnewPos : 0 < (reserveNewCapacity 0 count 0).toNat := by
      by_cases hc : count > 8
      · simpa [reserveNewCapacity,reserveCandidate,reserveRequired,reserveDoubled,hc,hcountPos]
          using (UInt32.lt_iff_toNat_lt.mp hcountPos)
      · simp [reserveNewCapacity,reserveCandidate,reserveRequired,reserveDoubled,hc,hcountPos]
    have hrequired : AllocatorResourceCost.requiredPages
        ((allocatorBase 0).toNat+(reserveNewCapacity 0 count 0).toNat)≤17 := by
      change (65535+(1054000+(reserveNewCapacity 0 count 0).toNat))/65536≤17
      omega
    have result := read_chunk_after_read_reserve_cost after outerParams outerLocalValues
      stack code arity remainder controls calls readToEndResult
      readToEndIgnored readToEndVector firstChunkFrame 0 1 0 count 0
      htag hcount hcountLt hcountNe hnotFits hafterCapacity hafterData
      hafterLength hafterBump hafterMod hafterCap hafterGlobal
      (by rw [hafterPages]; decide) (by rw [hafterPages]; decide)
      (by rw [hafterPages]; decide) (by rw [hafterPages]; decide)
      (by rw [hafterPages]; decide) (by rw [hafterPages]; decide)
      (by rw [hafterPages]; decide) (by simp [reserveRequired])
      (by change 1054000+(reserveNewCapacity 0 count 0).toNat<2147483648;omega)
      hnewPos (by rw [hafterPages]; decide) (by decide) (by decide)
      (by rw [hafterPages]; decide) hsuccessFacts
    simpa only [hafterPages,Nat.sub_eq_zero_of_le hrequired,Nat.mul_zero,
      UInt32.toNat_zero,Nat.zero_add,hcountNat,UInt32.add_zero,after,count,
      firstChunkFrame,firstChunkResult,firstChunkBuffer,readToEndResult,readToEndVector,readToEndIgnored,
      hframe48,hframe8]
      using result

theorem first_chunk_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (bytes : List UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost=Universal.envFor «module»)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0=Module.memoryHardCap)
    (hglobal : globalAt? store 0 = some (.i32 readToEndStack))
    (hbytes : bytes = store.wasm.host.stdio.input.take 32)
    (hpages : store.wasm.mem.pages = 17)
    (hcapacity : store.wasm.mem.read32 readToEndVector = 0)
    (hdata : store.wasm.mem.read32 (readToEndVector + 4) = 1)
    (hlength : store.wasm.mem.read32 (readToEndVector + 8) = 0)
    (hbump : store.wasm.mem.read32 1053960 = 0) :
    let after := readAdapterResultStore
      (readChunkFrameStore store firstChunkFrame)
      firstChunkResult firstChunkBuffer bytes
    let count := UInt32.ofNat bytes.length
    ChunkCostOutcome
      ⟨.running ⟨⟨outerParams,outerLocalValues,
          [.i32 readToEndVector,.i32 readToEndIgnored,.i32 readToEndResult]++stack⟩,
        .call 4::code,arity,remainder,controls,calls⟩,store⟩
      (fun final =>
        if bytes = [] then
          final =
            { expr := .running
                ⟨⟨outerParams, outerLocalValues, stack⟩,
                  code, arity, remainder, controls, calls⟩
              store := readChunkFinishedStore after readToEndResult
                readToEndVector 0 0 readToEndStack }
        else
          ∃ allocStore,
            ByteGrowSuccess
                (reserveFrameStore after (firstChunkFrame - 16))
                0 1 (reserveNewCapacity 0 count 0) 0 allocStore ∧
            let reserved := reserveFinishStore
              (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
                (allocatorPtr 0 1) (reserveNewCapacity 0 count 0))
              readToEndVector (allocatorPtr 0 1)
                (reserveNewCapacity 0 count 0) firstChunkFrame
            final =
              { expr := .running
                  ⟨⟨outerParams, outerLocalValues, stack⟩,
                    code, arity, remainder, controls, calls⟩
                store := readChunkFinishedStore
                  (readChunkCopiedStore reserved
                    (allocatorPtr 0 1) firstChunkBuffer count)
                  readToEndResult readToEndVector count 0 readToEndStack }) 265 (2*bytes.length) := by
  have firstRun := first_chunk_read_run store outerParams outerLocalValues stack code arity remainder controls calls
    readToEndResult readToEndIgnored readToEndVector readToEndStack hmod henv hglobal
    (by decide) (by decide) (by rw [hpages]; decide)
  have suffix := first_chunk_after_read_cost store outerParams outerLocalValues stack code arity remainder controls calls
    bytes hmod hcap hglobal hbytes hpages hcapacity hdata hlength hbump
  have adapted : ReadCostRun
      ⟨.running ⟨⟨outerParams,outerLocalValues,
          [.i32 readToEndVector,.i32 readToEndIgnored,.i32 readToEndResult]++stack⟩,
        .call 4::code,arity,remainder,controls,calls⟩,store⟩
      (readChunkAfterReadConfig
        (readAdapterResultStore (readChunkFrameStore store firstChunkFrame) firstChunkResult firstChunkBuffer bytes)
        outerParams outerLocalValues stack code arity remainder controls calls
        readToEndResult readToEndIgnored readToEndVector firstChunkFrame) 38 bytes.length := by
    have hframe : readToEndStack-48=firstChunkFrame := by decide
    have hout : firstChunkFrame+40=firstChunkResult := by decide
    have hbuffer : firstChunkFrame+8=firstChunkBuffer := by decide
    simpa only [hbytes,List.length_take,hframe,hout,hbuffer] using firstRun
  simpa only [two_mul] using suffix.prepend_read adapted

end Project.HexEncodeStdio.ReadChunkResourceCost
