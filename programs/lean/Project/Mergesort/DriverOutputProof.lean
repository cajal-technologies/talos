import Project.Mergesort.DriverSortProof
import Project.Mergesort.OutputIteratorProof

/-!
# Generated driver output-iterator setup

This file isolates the straight-line portion of unchanged generated `func127`
after the verified sort.  It copies the input vector descriptor, calls
`Vec<u64>::into_iter` at absolute index 125, copies the returned iterator into
the output-loop slot, and stops at the exact generated loop instruction.

The preceding one-byte first-element flag initialization is intentionally a
separate boundary: this contract starts at `func127.drop 141`, immediately
after that store, and preserves ownership of the initialized byte.
-/

namespace Project.Mergesort.DriverOutputProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.DriverProof
open Project.Mergesort.DriverSortProof
open Project.Mergesort.VectorProof
open Project.Mergesort.SortFunctionProof
open Project.Mergesort.OutputIteratorProof
open Project.Mergesort.SplitAtProof
open Project.Mergesort.FormatProof

def driverAfterFirstFlag : Program := func127.drop 141
def driverAtIntoIter : Program := func127.drop 155
def driverAfterIntoIter : Program := func127.drop 156
def driverAtOutputLoop : Program := func127.drop 164

theorem driverAfterFirstFlag_eq :
    driverAfterFirstFlag =
      [.localGet 0, .localGet 0, .load32 156, .store32 280,
       .localGet 0, .localGet 0, .load64 148, .store64 272,
       .localGet 0, .const 256, .add,
       .localGet 0, .const 272, .add] ++ driverAtIntoIter := by
  rfl

theorem driverAtIntoIter_eq :
    driverAtIntoIter = .call 125 :: driverAfterIntoIter := by
  rfl

theorem driverAfterIntoIter_eq :
    driverAfterIntoIter =
      [.localGet 0, .localGet 0, .load64 264, .store64 296,
       .localGet 0, .localGet 0, .load64 256, .store64 288] ++
        driverAtOutputLoop := by
  rfl

/-! Exact generated descriptor-copy and iterator-construction segment. -/
set_option maxHeartbeats 6000000 in
theorem driver_into_iter_setup_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame capacity data length : UInt32)
    (oldVecCapacity oldVecData oldVecLength : UInt32)
    (oldResult0 oldResult4 oldResult8 oldResult12 : UInt32)
    (oldIter0 oldIter4 oldIter8 oldIter12 : UInt32)
    (flag : UInt8)
    (depth : Nat)
    (hframeRoom : frame.toNat + 304 ≤ UInt32.size)
    (hcalleeRoom : (frame - 48).toNat + 48 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      vecDescriptorAt (148 + frame) capacity data length ∗
      vecDescriptorAt (272 + frame) oldVecCapacity oldVecData oldVecLength ∗
      intoIterDescriptorAt (256 + frame) oldResult0 oldResult4
        oldResult8 oldResult12 ∗
      intoIterDescriptorAt (288 + frame) oldIter0 oldIter4
        oldIter8 oldIter12 ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (255 + frame) (DFrac.own 1) (some flag) ∗
      SortWorkspace frame (depth + 1) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 frame) -∗
        vecDescriptorAt (148 + frame) capacity data length -∗
        vecDescriptorAt (272 + frame) capacity data length -∗
        intoIterDescriptorAt (256 + frame) data data capacity
          (data + (length <<< 3)) -∗
        intoIterDescriptorAt (288 + frame) data data capacity
          (data + (length <<< 3)) -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (255 + frame) (DFrac.own 1) (some flag) -∗
        SortWorkspace frame (depth + 1) -∗
        WP (.running
          ⟨⟨[], driverSortCallLocals frame length length data length, []⟩,
            driverAtOutputLoop, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], driverSortCallLocals frame length length data length, []⟩,
        driverAfterFirstFlag, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h1480, h1481, h1482, h1483, h1484, h1485, h1486, h1487⟩ :=
    descriptorSlot64Facts frame 148 304 hframeRoom (by decide)
  obtain ⟨h1560, h1561, h1562, h1563⟩ :=
    descriptorSlot32Facts frame 156 304 hframeRoom (by decide)
  obtain ⟨h2560, h2561, h2562, h2563, h2564, h2565, h2566, h2567⟩ :=
    descriptorSlot64Facts frame 256 304 hframeRoom (by decide)
  obtain ⟨h2640, h2641, h2642, h2643, h2644, h2645, h2646, h2647⟩ :=
    descriptorSlot64Facts frame 264 304 hframeRoom (by decide)
  obtain ⟨h2720, h2721, h2722, h2723, h2724, h2725, h2726, h2727⟩ :=
    descriptorSlot64Facts frame 272 304 hframeRoom (by decide)
  obtain ⟨h2800, h2801, h2802, h2803⟩ :=
    descriptorSlot32Facts frame 280 304 hframeRoom (by decide)
  obtain ⟨h2880, h2881, h2882, h2883, h2884, h2885, h2886, h2887⟩ :=
    descriptorSlot64Facts frame 288 304 hframeRoom (by decide)
  obtain ⟨h2960, h2961, h2962, h2963, h2964, h2965, h2966, h2967⟩ :=
    descriptorSlot64Facts frame 296 304 hframeRoom (by decide)
  have hvecRoom : (272 + frame).toNat + 12 ≤ UInt32.size := by
    calc
      (272 + frame).toNat + 12 =
          (frame + UInt32.ofNat 272).toNat + 12 := by
        congr 1
        exact congrArg UInt32.toNat (UInt32.add_comm 272 frame)
      _ = frame.toNat + 272 + 12 := congrArg (fun n => n + 12) h2720
      _ ≤ UInt32.size := by omega
  have hresultRoom : (256 + frame).toNat + 16 ≤ UInt32.size := by
    calc
      (256 + frame).toNat + 16 =
          (frame + UInt32.ofNat 256).toNat + 16 := by
        congr 1
        exact congrArg UInt32.toNat (UInt32.add_comm 256 frame)
      _ = frame.toNat + 256 + 16 := congrArg (fun n => n + 16) h2560
      _ ≤ UInt32.size := by omega
  have h148 : frame + 148 = 148 + frame := UInt32.add_comm frame 148
  have h156 : frame + 156 = (148 + frame) + 8 := by bv_decide
  have h256 : frame + 256 = 256 + frame := UInt32.add_comm frame 256
  have h264 : frame + 264 = (256 + frame) + 8 := by bv_decide
  have h272 : frame + 272 = 272 + frame := UInt32.add_comm frame 272
  have h280 : frame + 280 = (272 + frame) + 8 := by bv_decide
  have h288 : frame + 288 = 288 + frame := UInt32.add_comm frame 288
  have h296 : frame + 296 = (288 + frame) + 8 := by bv_decide
  iintro ⟨Hruntime, Hglobal, HsourceVec, HcopiedVec, Hresult, Hiter,
    Hflag, Hworkspace, Hdone⟩
  isimp only [vecDescriptorAt] at HsourceVec HcopiedVec
  icases HsourceVec with ⟨HsourceCapacity, HsourceData, HsourceLength⟩
  icases HcopiedVec with ⟨HcopiedCapacity, HcopiedData, HcopiedLength⟩
  ihave HsourceWord : pointsTo_u64 (148 + frame)
      (packU32 capacity data) $$ [HsourceCapacity HsourceData]
  · iapply (sliceDescriptorAt_eq_u64 (148 + frame) capacity data).mp
    isimp only [sliceDescriptorAt]
    iframe
  ihave HcopiedWord : pointsTo_u64 (272 + frame)
      (packU32 oldVecCapacity oldVecData) $$ [HcopiedCapacity HcopiedData]
  · iapply (sliceDescriptorAt_eq_u64 (272 + frame)
      oldVecCapacity oldVecData).mp
    isimp only [sliceDescriptorAt]
    iframe
  isimp only [SortWorkspace] at Hworkspace
  icases Hworkspace with ⟨HcalleeFrame, Hworkspace⟩
  isimp only [SortFrameOwn] at HcalleeFrame
  icases HcalleeFrame with
    ⟨%v0, %v1, %v2, %v3, %v4, %v5, %v6, %v7, %v8, %v9, %v10, %v11,
      Hv0, Hv1, Hv2, Hv3, Hv4, Hv5, Hv6, Hv7, Hv8, Hv9, Hv10, Hv11⟩
  isimp only [intoIterDescriptorAt] at Hresult Hiter
  icases Hresult with ⟨Hresult0, Hresult4, Hresult8, Hresult12⟩
  icases Hiter with ⟨Hiter0, Hiter4, Hiter8, Hiter12⟩
  rw [driverAfterFirstFlag_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HsourceLengthAt : pointsTo_u32 (frame + 156) length $$ [HsourceLength]
  · rw [h156]
    iexact HsourceLength
  iapply twp_load32 length h1560 h1561 h1562 h1563 $$ HsourceLengthAt
  iintro HsourceLengthAt
  ihave HcopiedLengthAt : pointsTo_u32 (frame + 280) oldVecLength $$
      [HcopiedLength]
  · rw [h280]
    iexact HcopiedLength
  iapply twp_store32 oldVecLength h2800 h2801 h2802 h2803 $$ HcopiedLengthAt
  iintro HcopiedLengthAt
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HsourceWordAt : pointsTo_u64 (frame + 148)
      (packU32 capacity data) $$ [HsourceWord]
  · rw [h148]
    iexact HsourceWord
  iapply twp_load64 (packU32 capacity data)
    h1480 h1481 h1482 h1483 h1484 h1485 h1486 h1487 $$ HsourceWordAt
  iintro HsourceWordAt
  ihave HcopiedWordAt : pointsTo_u64 (frame + 272)
      (packU32 oldVecCapacity oldVecData) $$ [HcopiedWord]
  · rw [h272]
    iexact HcopiedWord
  iapply twp_store64 (packU32 oldVecCapacity oldVecData)
    h2720 h2721 h2722 h2723 h2724 h2725 h2726 h2727 $$ HcopiedWordAt
  iintro HcopiedWordAt
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [driverAtIntoIter_eq]
  ihave HcopiedDesc : vecDescriptorAt (272 + frame) capacity data length $$
      [HcopiedWordAt HcopiedLengthAt]
  · ihave Hhead : sliceDescriptorAt (272 + frame) capacity data $$
        [HcopiedWordAt]
    · iapply (sliceDescriptorAt_eq_u64 (272 + frame) capacity data).mpr
      rw [← h272]
      iexact HcopiedWordAt
    isimp only [sliceDescriptorAt] at Hhead
    icases Hhead with ⟨Hcapacity, Hdata⟩
    isimp only [vecDescriptorAt]
    isplitl [Hcapacity]
    · iexact Hcapacity
    isplitl [Hdata]
    · iexact Hdata
    rw [← h280]
    iexact HcopiedLengthAt
  ihave HresultDesc : intoIterDescriptorAt (256 + frame)
      oldResult0 oldResult4 oldResult8 oldResult12 $$
      [Hresult0 Hresult4 Hresult8 Hresult12]
  · isimp only [intoIterDescriptorAt]
    iframe
  ihave Hf8 : sliceDescriptorAt ((frame - 48) + 8) v2 v3 $$ [Hv2 Hv3]
  · isimp only [sliceDescriptorAt]
    isplitl [Hv2]
    · iexact Hv2
    rw [show (frame - 48) + 8 + 4 = (frame - 48) + 12 by bv_decide]
    iexact Hv3
  ihave Hf32 : sliceDescriptorAt ((frame - 48) + 32) v8 v9 $$ [Hv8 Hv9]
  · isimp only [sliceDescriptorAt]
    isplitl [Hv8]
    · iexact Hv8
    rw [show (frame - 48) + 32 + 4 = (frame - 48) + 36 by bv_decide]
    iexact Hv9
  have Hcall := vecIntoIter_call_twp (α := α)
    (256 + frame) (272 + frame) capacity data length frame
    v2 v3 v4 v6 v7 v8 v9 v10
    oldResult0 oldResult4 oldResult8 oldResult12
    hcalleeRoom hvecRoom hresultRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[], driverSortCallLocals frame length length data length, []⟩)
    (stack := []) (code := driverAfterIntoIter) (arity := 0)
    (remainder := []) (controls := []) (calls := calls)
  simp only [List.append_nil] at Hcall
  iapply Hcall
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [HcopiedDesc]
  · iexact HcopiedDesc
  isplitl [Hf8]
  · iexact Hf8
  isplitl [Hv4]
  · iexact Hv4
  isplitl [Hv6]
  · iexact Hv6
  isplitl [Hv7]
  · iexact Hv7
  isplitl [Hf32]
  · iexact Hf32
  isplitl [Hv10]
  · iexact Hv10
  isplitl [HresultDesc]
  · iexact HresultDesc
  iintro Hruntime Hglobal HcopiedDesc Hf8 Hv4 Hv6 Hv7 Hf32 Hv10 Hresult
  isimp only [intoIterDescriptorAt] at Hresult
  icases Hresult with ⟨Hresult0, Hresult4, Hresult8, Hresult12⟩
  rw [driverAfterIntoIter_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HresultTail : pointsTo_u64 (frame + 264)
      (packU32 capacity (data + (length <<< 3))) $$
      [Hresult8 Hresult12]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 264) capacity
      (data + (length <<< 3))).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hresult8]
    · rw [h264]
      iexact Hresult8
    rw [show frame + 264 + 4 = (256 + frame) + 12 by bv_decide]
    iexact Hresult12
  iapply twp_load64 (packU32 capacity (data + (length <<< 3)))
    h2640 h2641 h2642 h2643 h2644 h2645 h2646 h2647 $$ HresultTail
  iintro HresultTail
  ihave HiterTail : pointsTo_u64 (frame + 296)
      (packU32 oldIter8 oldIter12) $$ [Hiter8 Hiter12]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 296)
      oldIter8 oldIter12).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hiter8]
    · rw [h296]
      iexact Hiter8
    rw [show frame + 296 + 4 = (288 + frame) + 12 by bv_decide]
    iexact Hiter12
  iapply twp_store64 (packU32 oldIter8 oldIter12)
    h2960 h2961 h2962 h2963 h2964 h2965 h2966 h2967 $$ HiterTail
  iintro HiterTail
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HresultHead : pointsTo_u64 (frame + 256) (packU32 data data) $$
      [Hresult0 Hresult4]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 256) data data).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hresult0]
    · rw [h256]
      iexact Hresult0
    rw [show frame + 256 + 4 = (256 + frame) + 4 by bv_decide]
    iexact Hresult4
  iapply twp_load64 (packU32 data data)
    h2560 h2561 h2562 h2563 h2564 h2565 h2566 h2567 $$ HresultHead
  iintro HresultHead
  ihave HiterHead : pointsTo_u64 (frame + 288)
      (packU32 oldIter0 oldIter4) $$ [Hiter0 Hiter4]
  · iapply (sliceDescriptorAt_eq_u64 (frame + 288)
      oldIter0 oldIter4).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hiter0]
    · rw [h288]
      iexact Hiter0
    rw [show frame + 288 + 4 = (288 + frame) + 4 by bv_decide]
    iexact Hiter4
  iapply twp_store64 (packU32 oldIter0 oldIter4)
    h2880 h2881 h2882 h2883 h2884 h2885 h2886 h2887 $$ HiterHead
  iintro HiterHead
  ihave HsourceDesc : vecDescriptorAt (148 + frame) capacity data length $$
      [HsourceWordAt HsourceLengthAt]
  · ihave Hhead : sliceDescriptorAt (148 + frame) capacity data $$
        [HsourceWordAt]
    · iapply (sliceDescriptorAt_eq_u64 (148 + frame) capacity data).mpr
      rw [← h148]
      iexact HsourceWordAt
    isimp only [sliceDescriptorAt] at Hhead
    icases Hhead with ⟨Hcapacity, Hdata⟩
    isimp only [vecDescriptorAt]
    isplitl [Hcapacity]
    · iexact Hcapacity
    isplitl [Hdata]
    · iexact Hdata
    rw [← h156]
    iexact HsourceLengthAt
  ihave HresultDesc : intoIterDescriptorAt (256 + frame) data data capacity
      (data + (length <<< 3)) $$
      [HresultHead HresultTail]
  · ihave Hhead : sliceDescriptorAt (256 + frame) data data $$ [HresultHead]
    · iapply (sliceDescriptorAt_eq_u64 (256 + frame) data data).mpr
      rw [← h256]
      iexact HresultHead
    ihave Htail : sliceDescriptorAt ((256 + frame) + 8) capacity
        (data + (length <<< 3)) $$ [HresultTail]
    · iapply (sliceDescriptorAt_eq_u64 ((256 + frame) + 8) capacity
        (data + (length <<< 3))).mpr
      rw [← h264]
      iexact HresultTail
    isimp only [sliceDescriptorAt] at Hhead Htail
    icases Hhead with ⟨Hresult0, Hresult4⟩
    icases Htail with ⟨Hresult8, Hresult12⟩
    ihave Hresult12At : pointsTo_u32 ((256 + frame) + 12)
        (data + (length <<< 3)) $$ [Hresult12]
    · rw [show (256 + frame) + 8 + 4 = (256 + frame) + 12 by bv_decide]
      iexact Hresult12
    isimp only [intoIterDescriptorAt]
    iframe
  ihave HiterDesc : intoIterDescriptorAt (288 + frame) data data capacity
      (data + (length <<< 3)) $$ [HiterHead HiterTail]
  · ihave Hhead : sliceDescriptorAt (288 + frame) data data $$ [HiterHead]
    · iapply (sliceDescriptorAt_eq_u64 (288 + frame) data data).mpr
      rw [← h288]
      iexact HiterHead
    ihave Htail : sliceDescriptorAt ((288 + frame) + 8) capacity
        (data + (length <<< 3)) $$ [HiterTail]
    · iapply (sliceDescriptorAt_eq_u64 ((288 + frame) + 8) capacity
        (data + (length <<< 3))).mpr
      rw [← h296]
      iexact HiterTail
    isimp only [sliceDescriptorAt] at Hhead Htail
    icases Hhead with ⟨Hiter0, Hiter4⟩
    icases Htail with ⟨Hiter8, Hiter12⟩
    ihave Hiter12At : pointsTo_u32 ((288 + frame) + 12)
        (data + (length <<< 3)) $$ [Hiter12]
    · rw [show (288 + frame) + 8 + 4 = (288 + frame) + 12 by bv_decide]
      iexact Hiter12
    isimp only [intoIterDescriptorAt]
    iframe
  isimp only [sliceDescriptorAt] at Hf8 Hf32
  icases Hf8 with ⟨Hv2, Hv3⟩
  icases Hf32 with ⟨Hv8, Hv9⟩
  ihave Hv3At : pointsTo_u32 ((frame - 48) + 12) data $$ [Hv3]
  · rw [show (frame - 48) + 8 + 4 = (frame - 48) + 12 by bv_decide]
    iexact Hv3
  ihave Hv9At : pointsTo_u32 ((frame - 48) + 36) data $$ [Hv9]
  · rw [show (frame - 48) + 32 + 4 = (frame - 48) + 36 by bv_decide]
    iexact Hv9
  ihave HcalleeFrame : SortFrameOwn (frame - 48) $$
      [Hv0 Hv1 Hv2 Hv3At Hv4 Hv5 Hv6 Hv7 Hv8 Hv9At Hv10 Hv11]
  · isimp only [SortFrameOwn]
    iexists v0, v1, capacity, data, length, v5,
      data + (length <<< 3), capacity, capacity, data, length, v11
    iframe
  ihave HworkspaceOut : SortWorkspace frame (depth + 1) $$
      [HcalleeFrame Hworkspace]
  · isimp only [SortWorkspace]
    iframe
  iapply Hdone $$ Hruntime Hglobal HsourceDesc HcopiedDesc HresultDesc
    HiterDesc Hflag HworkspaceOut

end Project.Mergesort.DriverOutputProof
