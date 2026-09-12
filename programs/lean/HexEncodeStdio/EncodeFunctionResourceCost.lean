import HexEncodeStdio.EncodeLoopResourceCost
import HexEncodeStdio.EncodeAllocOperational
import HexEncodeStdio.ReadToEndTransition

/-! Physical post-allocation execution of the complete generated encoder. -/
namespace Project.HexEncodeStdio.EncodeFunctionResourceCost

open Wasm Wasm.SmallStep Project.HexStdio
open EncodeResourceCost EncodeLoopResourceCost

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def initializedStore (store : MachineStore Universal.State) (source length : UInt32) :
    MachineStore Universal.State :=
  {store with wasm := {store.wasm with mem :=
    (((store.wasm.mem.write32 1048540 1048576).write32 1048536 (source+length)).write32 1048532 source).write32 1048528 sentinel}}

def outerControl : ControlFrame :=
  {kind := .block,paramArity := 0,resultArity := 0,body := TotalEncodeLoop.encodeOuterBody,
    continuation := TotalEncodeFunction.func6FinishCode,belowStack := []}

def afterAllocationConfig (store : MachineStore Universal.State) (source length : UInt32) : Config Universal.State :=
  ⟨.running ⟨EncodeResourceCost.encodeLocals 1048564 source length 1048512 (source+length) 0 0 0 0,
    [],0,[],encodeReserveControls,encodeMainCalls store source⟩,store⟩

def firstIteratorConfig (store : MachineStore Universal.State) (source length : UInt32) : Config Universal.State :=
  ⟨.running ⟨EncodeResourceCost.encodeLocals 1048564 source length 1048512 (source+length) 0 0 0 0 [.i32 1048528],
    TotalEncodeLoop.encodeOuterBody.drop 3,0,[],[outerControl],encodeMainCalls store source⟩,
    initializedStore store source length⟩

/-- Exit the reserve block and initialize all four concrete iterator words. -/
theorem initialize_cost (store : MachineStore Universal.State) (source length : UInt32)
    (hpages : 1048544≤store.wasm.mem.pages*65536) :
    ∃ trace, CostedSteps CostedStdIO.work (afterAllocationConfig store source length) trace
      (firstIteratorConfig store source length) 17 ∧ (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  let trace : List StepKind :=
    [.administrative .exitControl,.instruction (.localGet 3),.instruction (.const 1048576),
      .instruction (.store32 28),.instruction (.localGet 3),.instruction (.localGet 4),
      .instruction (.store32 24),.instruction (.localGet 3),.instruction (.localGet 1),
      .instruction (.store32 20),.instruction (.localGet 3),.instruction (.const sentinel),
      .instruction (.store32 16),.instruction (.block 0 0 TotalEncodeLoop.encodeOuterBody),
      .instruction (.localGet 3),.instruction (.const 16),.instruction .add]
  refine ⟨trace,?_,?_⟩
  · apply Steps.with_unit_cost
    · unfold trace
      wasm_steps [(.exitControl rfl),(.localGet rfl),.const,
        (.store32 rfl (by change 1048512+28+4≤_;omega)),(.localGet rfl),(.localGet rfl),
        (.store32 rfl (by change 1048512+24+4≤store.wasm.mem.pages*65536;omega)),
        (.localGet rfl),(.localGet rfl),
        (.store32 rfl (by change 1048512+20+4≤store.wasm.mem.pages*65536;omega)),
        (.localGet rfl),.const,
        (.store32 rfl (by change 1048512+16+4≤store.wasm.mem.pages*65536;omega)),
        .block,(.localGet rfl),.const]
      exact Steps.single Step.add
    · intro before kind after member
      simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro kind member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [HostPrimaryMemoryKind,PrimaryMemoryKind]

theorem initialized_fields (store : MachineStore Universal.State) (source length capacity output : UInt32)
    (hc : store.wasm.mem.read32 1048516=capacity)
    (ho : store.wasm.mem.read32 1048520=output)
    (hp : store.wasm.mem.read32 1048524=0) :
    Fields (initializedStore store source length).wasm.mem capacity output 0 sentinel source (source+length) := by
  constructor
  all_goals simp only [initializedStore]
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact hc
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact ho
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact hp
  · exact Mem.read32_write32_same _ _ _
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact Mem.read32_write32_same _ _ _
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide)]
    exact Mem.read32_write32_same _ _ _
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact Mem.read32_write32_same _ _ _

theorem initialized_framed (store : MachineStore Universal.State) (source length output : UInt32) :
    Framed store.wasm.mem (initializedStore store source length).wasm.mem output := by
  refine ⟨rfl,?_⟩
  intro address outside beforeOutput
  simp only [initializedStore]
  rw [Mem.write32_bytes_of_disjoint _ _ _ _ (by change address<1048528 ∨ 1048528+4≤address;omega),
    Mem.write32_bytes_of_disjoint _ _ _ _ (by change address<1048532 ∨ 1048532+4≤address;omega),
    Mem.write32_bytes_of_disjoint _ _ _ _ (by change address<1048536 ∨ 1048536+4≤address;omega),
    Mem.write32_bytes_of_disjoint _ _ _ _ (by change address<1048540 ∨ 1048540+4≤address;omega)]

def loopContext (store : MachineStore Universal.State) (source : UInt32) : Context :=
  {controls := [outerControl],calls := encodeMainCalls store source}

/-- The first returned high digit takes the nonempty outer guard and enters
exactly the generated loop, loading its initial zero output length. -/
theorem first_head_cost (store : MachineStore Universal.State) (source length high : UInt32)
    (hhigh : high<128) (hposition : store.wasm.mem.read32 1048524=0)
    (hpages : 1048528≤store.wasm.mem.pages*65536) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨EncodeResourceCost.encodeLocals 1048564 source length 1048512 (source+length) 0 0 0 0 [.i32 high],
        TotalEncodeLoop.encodeOuterBody.drop 4,0,[],[outerControl],encodeMainCalls store source⟩,store⟩ trace
      (headConfig (loopContext store source) store 0 high (source+length) 0 0) 8 ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  let trace : List StepKind := [.instruction (.localTee 2),.instruction (.const sentinel),
    .instruction .eq,.instruction (.br_if 0),.instruction (.localGet 3),
    .instruction (.load32 12),.instruction (.localSet 1),.instruction (.loop 0 0 loopBody)]
  refine ⟨trace,?_,?_⟩
  · apply Steps.with_unit_cost
    · unfold trace
      wasm_steps [(.localTee rfl),.const,(.eq (result := 0) (by simp [ascii_ne_sentinel hhigh])),
        .brIfZero,(.localGet rfl),(.load32 rfl (by change 1048512+12+4≤_;omega))]
      rw [show (1048512:UInt32)+12=1048524 from rfl,hposition]
      wasm_steps [(.localSet rfl)]
      exact Steps.single Step.loop
    · intro before kind after member
      simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro kind member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [HostPrimaryMemoryKind,PrimaryMemoryKind]

def completedStore (store : MachineStore Universal.State) (memory : Mem) (n : Nat) :
    MachineStore Universal.State :=
  finishStore (memoryStore store memory) 1048564 1048512 (UInt32.ofNat (2*n)) (memory.read64 1048516)

def afterEncodeConfig (store : MachineStore Universal.State) (source : UInt32) : Config Universal.State :=
  ⟨.running ⟨⟨[],[.i32 1048544,.i32 source,.i32 0,.i32 0],[]⟩,
    func10.drop 18,0,[],[],[]⟩,store⟩

/-- Exit the completed loop's outer block, publish the vector, and execute the
actual return to the original main frame. -/
theorem publish_return_cost (store : MachineStore Universal.State) (source destination : UInt32) (n : Nat)
    (hglobal : globalAt? store 0=some (.i32 1048512))
    (hposition : store.wasm.mem.read32 1048524=UInt32.ofNat (2*n))
    (hpages : 1048576≤store.wasm.mem.pages*65536) :
    ∃ trace, CostedSteps CostedStdIO.work
      (doneConfig (loopContext store source) store (UInt32.ofNat (2*n)) destination) trace
      (afterEncodeConfig (completedStore store store.wasm.mem n) source) 14 ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  let locals := EncodeResourceCost.encodeLocals 1048564 (UInt32.ofNat (2*n)) sentinel 1048512 1 1 destination 0 0
  have exitStep : CostedSteps CostedStdIO.work
      (doneConfig (loopContext store source) store (UInt32.ofNat (2*n)) destination)
      [.administrative .exitControl]
      ⟨.running ⟨locals,TotalEncodeFunction.func6FinishCode,0,[],[],encodeMainCalls store source⟩,store⟩ 1 := by
    exact CostedSteps.single (.exitControl rfl)
  obtain ⟨a,asteps,aprimary⟩ := finish_body_cost store 1048564 (UInt32.ofNat (2*n)) sentinel 1048512
    1 1 destination 0 0 (UInt32.ofNat (2*n)) (store.wasm.mem.read64 1048516) 0 [] [] (encodeMainCalls store source)
    (by rw [hglobal];rfl) hposition rfl (by change 1048512+16≤_;omega)
    (by change 1048564+12≤_;omega) (by decide)
  have returnStep : CostedSteps CostedStdIO.work
      ⟨.running ⟨locals,[],0,[],[],encodeMainCalls store source⟩,completedStore store store.wasm.mem n⟩
      [.administrative .returnFromCall]
      (afterEncodeConfig (completedStore store store.wasm.mem n) source) 1 := by
    exact CostedSteps.single (.returnFromCallFallthrough rfl)
  have full := (exitStep.trans asteps).trans returnStep
  refine ⟨([.administrative .exitControl]++a)++[.administrative .returnFromCall],?_,?_⟩
  · exact full
  · intro kind member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with (rfl|member)|rfl
    · trivial
    · exact aprimary kind member
    · trivial

/-- Complete nonempty encoder after its successful reserve call. Every premise
is a current physical store fact or a finite numerical range; the proof builds
the actual execution through initialization, all loop iterations, and return. -/
theorem after_allocation_cost (store : MachineStore Universal.State)
    (source length capacity output : UInt32) (n : Nat)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hglobal : globalAt? store 0=some (.i32 1048512))
    (hlen : length.toNat=n) (hn : 0<n)
    (hc : store.wasm.mem.read32 1048516=capacity)
    (ho : store.wasm.mem.read32 1048520=output)
    (hp : store.wasm.mem.read32 1048524=0)
    (hcapacity : 2*n≤capacity.toNat)
    (hsourceLower : 1048592 ≤ source.toNat)
    (hsourcePhysical : source.toNat+n≤store.wasm.mem.pages*65536)
    (hsourceWrap : source.toNat+n<UInt32.size)
    (houtputLower : 1048592 ≤ output.toNat)
    (houtputPhysical : output.toNat+2*n≤store.wasm.mem.pages*65536)
    (houtputWrap : output.toNat+2*n<UInt32.size)
    (table : AsciiTable store.wasm.mem) :
    ∃ memory trace,
      CostedSteps CostedStdIO.work (afterAllocationConfig store source length) trace
        (afterEncodeConfig (completedStore store memory n) source) (156*n+63) ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) ∧
      Fields memory capacity output (UInt32.ofNat (2*n)) sentinel (source+length) (source+length) ∧
      Framed store.wasm.mem memory output := by
  have hfinish : (source+length).toNat=source.toNat+n := by
    rw [UInt32.toNat_add,hlen];exact Nat.mod_eq_of_lt hsourceWrap
  have hnext : (source+1).toNat=source.toNat+1 := by
    simpa only [show (UInt32.ofNat 1:UInt32)=1 from rfl] using offset_toNat source 1 (by omega)
  have hsourceNe : source≠source+length := by
    intro equality
    have e := congrArg UInt32.toNat equality
    rw [hfinish] at e
    omega
  let initialized := initializedStore store source length
  let byte := initialized.wasm.mem.read8 source
  let low := initialized.wasm.mem.read8 (1048576+UInt32.ofNat (byte.toNat%16))
  let high := initialized.wasm.mem.read8 (1048576+UInt32.ofNat (byte.toNat/16))
  let first := iteratorHighStore initialized 1048528 source low
  have initialFields := initialized_fields store source length capacity output hc ho hp
  have initFrame := initialized_framed store source length output
  have initTable := initFrame.ascii table houtputLower
  have lowAscii : low.toUInt32<128 := initTable _ (Nat.mod_lt _ (by decide))
  have highAscii : high.toUInt32<128 := initTable _ (by have := byte.toNat_lt;omega)
  obtain ⟨a,asteps,aprimary⟩ := initialize_cost store source length (by omega)
  obtain ⟨b,bsteps,bprimary⟩ := iterator_high_cost initialized
    (EncodeResourceCost.encodeLocals 1048564 source length 1048512 (source+length) 0 0 0 0)
    [] (TotalEncodeLoop.encodeOuterBody.drop 4) 0 [] [outerControl] (encodeMainCalls store source)
    1048528 source (source+length) byte low high hmodule initialFields.saved initialFields.cursor
    initialFields.finish initialFields.table rfl rfl rfl hsourceNe (by decide) hsourceLower
    (by change source.toNat+1≤store.wasm.mem.pages*65536;omega)
  have firstFields := high_fields initialized capacity output 0 sentinel source (source+length) low initialFields
  have firstFrame := high_framed initialized output source low
  obtain ⟨c,csteps,cprimary⟩ := first_head_cost first source length high.toUInt32 highAscii firstFields.position
    (by change 1048528≤store.wasm.mem.pages*65536;omega)
  obtain ⟨memory,destination,d,dsteps,dprimary,finalFields,finalFrame⟩ :=
    pair_loop_cost (loopContext store source) first 0 (n-1) capacity output (source+1) (source+length)
      high.toUInt32 low.toUInt32 (source+length) 0 0 hmodule firstFields
      (firstFrame.ascii initTable houtputLower) highAscii lowAscii
      (by rw [hnext,hfinish];omega) (by rw [hnext];omega)
      (by change (source+length).toNat≤store.wasm.mem.pages*65536;rw [hfinish];exact hsourcePhysical)
      (by omega) houtputLower
      (by change output.toNat+(0+2*(n-1+1))≤store.wasm.mem.pages*65536;omega) (by omega)
  have count : 0+2*(n-1+1)=2*n := by omega
  rw [count] at dsteps finalFields
  obtain ⟨e,esteps,eprimary⟩ := publish_return_cost (memoryStore store memory) source destination n
    hglobal finalFields.position (by change 1048576≤memory.pages*65536;rw [finalFrame.1];change 1048576≤store.wasm.mem.pages*65536;omega)
  have full := (((asteps.trans bsteps).trans csteps).trans dsteps).trans esteps
  refine ⟨memory,(((a++b)++c)++d)++e,?_,?_,finalFields,?_⟩
  · have hcost : 17+48+8+(156*(n-1)+132)+14=156*n+63 := by omega
    simpa only [completedStore,memoryStore,first,initialized,iteratorHighStore,initializedStore,hcost] using full
  · intro kind member
    simp only [List.mem_append] at member
    rcases member with (((member|member)|member)|member)|member
    · exact aprimary kind member
    · exact bprimary kind member
    · exact cprimary kind member
    · exact dprimary kind member
    · exact eprimary kind member
  · exact (initFrame.trans firstFrame).trans finalFrame

/-- The published vector header contains the same proved capacity, pointer,
and final length used by the operational loop. -/
theorem completed_result_fields (store : MachineStore Universal.State) (memory : Mem)
    (capacity output cursor : UInt32) (n : Nat)
    (fields : Fields memory capacity output (UInt32.ofNat (2*n)) sentinel cursor cursor) :
    (completedStore store memory n).wasm.mem.read32 1048564=capacity ∧
    (completedStore store memory n).wasm.mem.read32 1048568=output ∧
    (completedStore store memory n).wasm.mem.read32 1048572=UInt32.ofNat (2*n) := by
  constructor
  · simp only [completedStore,finishStore,memoryStore]
    rw [Mem.read32_write64_low,Mem.read64_low]
    exact fields.capacity
  constructor
  · simp only [completedStore,finishStore,memoryStore]
    rw [show (1048568:UInt32)=1048564+4 from rfl,Mem.read32_write64_high _ _ _ (by decide),
      Mem.read64_high _ _ (by decide)]
    exact fields.output
  · simp only [completedStore,finishStore,memoryStore]
    rw [Wasm.Mem.read32_write64_disjoint _ _ _ _ (by decide)]
    exact Wasm.Mem.read32_write32_same _ _ _

end Project.HexEncodeStdio.EncodeFunctionResourceCost
