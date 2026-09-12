import Project.Mergesort.ExactReserve
import Project.Mergesort.DriverProof

/-!
# Exact growth at the generated driver's reserve call site

ReadFacts supplies the actual serialized-input partition and retained-buffer
lineage. A closed WorkArraysFit bound derives arithmetic acceptance; the
canonical physical cap then implies growth success. The continuation receives
the updated linear token, reconstructed frame, and retained-input page bound.
-/

namespace Project.Mergesort.ExactDriver

open Wasm Wasm.SmallStep Wasm.SepLogic
open Iris Iris.ProgramLogic Language.Notation Std
open Project.Mergesort.Contracts Project.Mergesort.Representations
open Project.Mergesort.DriverProof Project.Mergesort.MemoryBounds
open scoped Wasm.SmallStep.Outcome

/-- A reserve reached from the actual read-loop bookkeeping returns normally,
including when it grows physical memory. No accepted classification or grow
outcome is assumed by the caller. -/
theorem twp_func3_reserve_exact
    [WasmSmallStepGS hlc Universal.State]
    (original : List UInt32) (current remaining : List UInt8)
    (capacity dataPtr : UInt32)
    (initialized chunkBytes outputBytes shadow : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (output : List UInt8) (raised : Bool)
    (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (h : BoundedDriverFacts.ReadFacts original initialized current remaining
      capacity dataPtr frontier history)
    (pages : Nat)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hpages : pages ≤ Module.memoryHardCap)
    (hfit : MemoryBounds.WorkArraysFit (serialize original).length)
    (hreserve : capacity.toNat - initialized.length < current.length)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    let callerLocals := func3AppendLocals dataPtr
      (UInt32.ofNat current.length) (UInt32.ofNat initialized.length)
      aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack
    let newCapacityNat :=
      selectedCapacity initialized.length current.length capacity.toNat
    let newCapacity := UInt32.ofNat newCapacityNat
    let newLayout : AllocLayout := { size := newCapacityNat, alignment := 1 }
    iprop(
      RuntimeContext ∗ memoryCapOwn 0 Module.memoryHardCap ∗ memoryPagesHalf pages ∗
      StackPointer driverBase ∗
      StackReserve reserveBase shadow ∗
      ExportFrame heapId capacity dataPtr initialized chunkBytes outputBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams remaining output raised ∗
      (∀ newPtr : UInt32, ∀ finish : UInt32, ∀ finalHistory : AllocationHistory,
        RuntimeContext -∗ memoryCapOwn 0 Module.memoryHardCap -∗
        memoryPagesHalf (max pages (allocatorRequiredPages finish).toNat) -∗
        StackPointer driverBase -∗
        StackReserve reserveBase
          (reserveSuccessShadow shadow newPtr newCapacity) -∗
        ExportFrame heapId newCapacity newPtr initialized chunkBytes outputBytes -∗
        BumpHeap heapId finish finish.toNat finalHistory -∗
        ⌜classifyBump frontier newLayout = .success newPtr finish ∧
          VecReserveHistory history finalHistory capacity dataPtr newPtr newLayout ∧
          BoundedGeometricVecFacts (serialize original).length
            (initialized.length + current.length) remaining.length
            newCapacity newPtr finish.toNat finalHistory ∧
          max pages (allocatorRequiredPages finish).toNat ≤
            max pages ((inputFrontierBound (serialize original).length + 65535) / 65536)⌝ -∗
        Streams remaining output raised -∗
        ResumeWP [] callerLocals stack code arity remainder controls calls s E Φ)) ⊢
      WP (.running
        ⟨callerLocals,
          [.localGet 0, .localGet 6, .localGet 3,
            .const 1, .const 1, .call 4] ++ code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  dsimp only
  let total := (serialize original).length
  let callerLocals := func3AppendLocals dataPtr
    (UInt32.ofNat current.length) (UInt32.ofNat initialized.length)
    aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack
  let newCapacityNat := selectedCapacity initialized.length current.length capacity.toNat
  let newCapacity := UInt32.ofNat newCapacityNat
  let newLayout : AllocLayout := { size := newCapacityNat, alignment := 1 }
  let newPtr := UInt32.ofNat frontier
  let finish := UInt32.ofNat (frontier + newCapacityNat)
  have htotal : total = initialized.length + current.length + remaining.length := by
    dsimp only [total]
    rw [h.partition]
    simp only [List.length_append]
  have hlayout := GeometricVecFacts.reserveLayout total
    initialized.length (current.length + remaining.length) current.length
    capacity dataPtr frontier history h.bounded.1 h.chunk_shape h.chunk_positive
  dsimp only at hlayout
  have hclassify : classifyBump frontier newLayout = .success newPtr finish :=
    BoundedGeometricVecFacts.reserve_classify_success total initialized.length
      current.length remaining.length capacity dataPtr frontier history
      h.bounded h.chunk_positive (by omega) hfit
  have hfinishSigned : finish.toNat < 2147483648 := by
    have hf := classifyBump_success_facts frontier newLayout newPtr finish hclassify
    dsimp only at hf
    omega
  have hcapfit : (allocatorRequiredPages finish).toNat ≤ Module.memoryHardCap :=
    (allocatorRequiredPages_le_signedLimit finish hfinishSigned).trans (by decide)
  have hinitializedWord : (UInt32.ofNat initialized.length).toNat = initialized.length :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have hcurrentWord : (UInt32.ofNat current.length).toNat = current.length :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  iintro ⟨Hruntime, Hcap, Hexact, Hsp, Hreserve, Hframe, Hbump, Hstreams, Hnormal⟩
  isimp only [ExportFrame] at Hframe
  icases Hframe with ⟨Hvec, Hchunk, Houtput, %hframeLengths⟩
  simp only [List.cons_append, List.nil_append, func3AppendLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const twp_const]
  have HreserveCall := ExactReserve.twp_func1_call_exact
    driverBase (UInt32.ofNat initialized.length) (UInt32.ofNat current.length) 1 1
    total current remaining capacity dataPtr initialized shadow heapId storedCursor
    frontier history output raised newPtr finish pages Module.memoryHardCap
    ⟨rfl, rfl, rfl, hinitializedWord, hcurrentWord,
      h.chunk_shape, h.chunk_positive, h.chunk_mod, hreserve, htotal,
      h.bounded.1, hlayout.1, hlayout.2.1, hlayout.2.2⟩
    hclassify hmode hpages (Nat.le_refl _) hcapfit
    (callerLocals := callerLocals) (stack := stack) (code := code) (arity := arity)
    (remainder := remainder) (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  dsimp only at HreserveCall
  unfold CallContract callExpr at HreserveCall
  simp only [List.cons_append, List.nil_append, callerLocals, func3AppendLocals] at HreserveCall
  iapply HreserveCall
  iframe Hruntime Hcap Hexact Hsp Hreserve Hvec Hbump Hstreams
  iintro %finalHistory Hruntime Hcap Hexact Hsp Hreserve Hvec Hbump %hpure Hstreams
  ihave Hframe : ExportFrame heapId newCapacity newPtr initialized
      chunkBytes outputBytes $$ [Hvec Hchunk Houtput]
  · unfold ExportFrame
    iframe_pureexact hframeLengths
  have hbounded := BoundedGeometricVecFacts.reserveSuccess total
    initialized.length current.length remaining.length capacity dataPtr
    newPtr finish frontier history finalHistory h.bounded h.chunk_shape h.chunk_positive
    (by omega) hclassify hpure.1
  have hfrontier := BoundedGeometricVecFacts.frontier_le total
    (initialized.length + current.length) remaining.length newCapacity newPtr
    finish.toNat finalHistory hbounded
  have htarget : (allocatorRequiredPages finish).toNat ≤
      (inputFrontierBound total + 65535) / 65536 := by
    rw [allocatorRequiredPages_toNat finish hfinishSigned]
    exact Nat.div_le_div_right (Nat.add_le_add_right hfrontier 65535)
  iapply Hnormal $$ %newPtr %finish %finalHistory Hruntime Hcap Hexact Hsp Hreserve
    Hframe Hbump %⟨hclassify, hpure.1, hbounded, max_le_max_left pages htarget⟩ Hstreams

end Project.Mergesort.ExactDriver
