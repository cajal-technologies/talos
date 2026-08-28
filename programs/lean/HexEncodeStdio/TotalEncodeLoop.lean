import CodeLib
import Project.HexStdio.Program
import HexEncodeStdio.Helpers
import HexEncodeStdio.TotalHelpers
import HexEncodeStdio.Hex
import HexEncodeStdio.TotalIterator

namespace Project.HexEncodeStdio.TotalEncodeLoop

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

private theorem hdtwp_leU {hlc : HasLC} {α : Type} [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≤ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .leU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.leU hresult)

/-- The outer block of generated `func6` (WAT function 9). -/
def encodeOuterBody : Program :=
  match Project.HexStdio.func6[28]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

/-- The body of the output loop nested in `encodeOuterBody`. -/
abbrev encodeLoopBody : Program :=
  match encodeOuterBody[11]? with
  | some (Instruction.loop _ _ body _ _) => body
  | _ => []

theorem encodeOuterBody_eq : encodeOuterBody =
    [.localGet 3, .const 16, .add, .call 21, .localTee 2,
      .const 1114112, .eq, .br_if 0, .localGet 3, .load32 12,
      .localSet 1, .loop 0 0 encodeLoopBody [] []] := by
  rfl

/-- Instructions after the character-width classification block. -/
def encodeLoopAfterClassify : Program := encodeLoopBody.drop 1

/-- The suffix beginning at the iterator call at the end of one iteration. -/
def encodeLoopCallTail : Program := encodeLoopBody.drop 19

abbrev encodeLoopFrame (continuation : Program := []) : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := encodeLoopBody, continuation, belowStack := [] }

private abbrev encodeLocals (result outLen char stackPtr charLen ascii dest
    tmp1 tmp2 : UInt32) (values : List Value := []) : Locals :=
  ⟨[.i32 result, .i32 outLen, .i32 char],
    [.i32 stackPtr, .i32 charLen, .i32 ascii, .i32 dest,
      .i32 tmp1, .i32 tmp2], values⟩

/-- A semantic index for the alternating high/low digit loop. -/
structure EncodeLoopState (input : List UInt8) where
  byteIndex : Nat
  byteIndex_lt : byteIndex < input.length
  lowPhase : Bool
  dest : UInt32
  oldLen : UInt32
  oldAscii : UInt32

abbrev loopPosition {input : List UInt8} (state : EncodeLoopState input) : Nat :=
  match state.lowPhase with
  | false => 2 * state.byteIndex
  | true => 2 * state.byteIndex + 1

abbrev loopDigit {input : List UInt8} (state : EncodeLoopState input) : UInt8 :=
  match state.lowPhase with
  | false => Project.HexStdio.Spec.hexDigit
      ((input[state.byteIndex]'state.byteIndex_lt).toNat / 16)
  | true => Project.HexStdio.Spec.hexDigit
      ((input[state.byteIndex]'state.byteIndex_lt).toNat % 16)

abbrev loopSaved {input : List UInt8} (state : EncodeLoopState input) : UInt32 :=
  match state.lowPhase with
  | false => (Project.HexStdio.Spec.hexDigit
      ((input[state.byteIndex]'state.byteIndex_lt).toNat % 16)).toUInt32
  | true => Project.HexEncodeStdio.TotalIterator.sentinel

abbrev loopLocals (result stackPtr output : UInt32)
    {input : List UInt8} (state : EncodeLoopState input) : Locals :=
  encodeLocals result (UInt32.ofNat (loopPosition state))
    (loopDigit state).toUInt32 stackPtr state.oldLen state.oldAscii state.dest 0 0

/-- Capacity selected by `RawVec::grow_amortized` for an initially empty byte
vector.  Rust enforces a minimum non-zero allocation of eight bytes. -/
abbrev encodeCapacityNat (input : List UInt8) : Nat :=
  max 8 (2 * input.length)

/-- Owned state at the top of one encode-loop iteration.  Only the initialized
prefix is constrained; the unused allocation tail is deliberately framed. -/
abbrev encodeLoopInvariant {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (result stackPtr output source : UInt32) (input : List UInt8)
    (Finish : IProp (WasmHeapGF α)) (state : EncodeLoopState input) :
    IProp (WasmHeapGF α) := iprop%
  runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
  pointsTo_u32 0 (stackPtr + 4) (UInt32.ofNat (encodeCapacityNat input)) ∗
  pointsTo_u32 0 (stackPtr + 8) output ∗
  pointsTo_u32 0 (stackPtr + 12) (UInt32.ofNat (loopPosition state)) ∗
  pointsTo_u32 0 (stackPtr + 16) (loopSaved state) ∗
  pointsTo_u32 0 (stackPtr + 20)
    (source + UInt32.ofNat (state.byteIndex + 1)) ∗
  pointsTo_u32 0 (stackPtr + 24)
    (source + UInt32.ofNat input.length) ∗
  pointsTo_u32 0 (stackPtr + 28) 1048576 ∗
  pointsToBytes 0 source input ∗
  pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable ∗
  ∃ out : List UInt8,
    pointsToBytes 0 output out ∗
    ⌜out.length = 2 * input.length⌝ ∗
    ⌜out.take (loopPosition state) =
      (Project.HexStdio.Spec.encode input).take (loopPosition state)⌝ ∗
    Finish

theorem u32_ofNat_succ {n : Nat} (h : n + 1 < UInt32.size) :
    UInt32.ofNat n + 1 = UInt32.ofNat (n + 1) := by
  have _ := h
  simpa using (UInt32.ofNat_add n 1).symm

theorem u32_room {i capacity : Nat} (hi : i < capacity)
    (hcapacity : capacity < UInt32.size) :
    (1 : UInt32) ≤ UInt32.ofNat capacity - UInt32.ofNat i := by
  rw [← UInt32.ofNat_sub (Nat.le_of_lt hi), UInt32.le_iff_toNat_le,
    UInt32.toNat_ofNat_of_lt' (by omega)]
  simp
  omega

theorem update_prefix_high (input out : List UInt8) (i : Nat)
    (hi : i < input.length) (hlen : out.length = 2 * input.length)
    (hprefix : out.take (2 * i) =
      (Project.HexStdio.Spec.encode input).take (2 * i)) :
    (out.set (2 * i)
        (Project.HexStdio.Spec.hexDigit (input[i].toNat / 16))).take
      (2 * i + 1) =
      (Project.HexStdio.Spec.encode input).take (2 * i + 1) := by
  rw [Project.HexEncodeStdio.Hex.take_set_succ]
  · rw [hprefix, Project.HexEncodeStdio.Hex.encode_take_twice input i hi.le]
    exact (Project.HexEncodeStdio.Hex.encode_take_high input i hi).symm
  · omega

theorem update_prefix_low (input out : List UInt8) (i : Nat)
    (hi : i < input.length) (hlen : out.length = 2 * input.length)
    (hprefix : out.take (2 * i + 1) =
      (Project.HexStdio.Spec.encode input).take (2 * i + 1)) :
    (out.set (2 * i + 1)
        (Project.HexStdio.Spec.hexDigit (input[i].toNat % 16))).take
      (2 * i + 2) =
      (Project.HexStdio.Spec.encode input).take (2 * i + 2) := by
  rw [Project.HexEncodeStdio.Hex.take_set_succ]
  · rw [hprefix, Project.HexEncodeStdio.Hex.encode_take_high input i hi]
    rw [Project.HexEncodeStdio.Hex.encode_take_low input i hi]
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      Project.HexEncodeStdio.Hex.encode_prefix_low input i hi
  · omega

/-- Every hexadecimal digit takes the one-byte UTF-8 fast path. This lemma
isolates exactly the nested classification blocks at the head of the loop. -/
theorem func6_ascii_classify {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (result outLen stackPtr oldLen oldAscii oldDest tmp1 tmp2 : UInt32)
    (digit : UInt8) (n : Nat) (hdigit : digit = Project.HexStdio.Spec.hexDigit n)
    (hn : n < 16)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    WP (.running
        ⟨encodeLocals result outLen digit.toUInt32 stackPtr 1 1 oldDest tmp1 tmp2,
          encodeLoopAfterClassify, arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨encodeLocals result outLen digit.toUInt32 stackPtr oldLen oldAscii oldDest
          tmp1 tmp2,
        encodeLoopBody, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro Hfinish
  subst digit
  simp only [encodeLoopBody, encodeOuterBody, Project.HexStdio.func6,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop_succ_cons,
    List.drop_zero, encodeLoopAfterClassify]
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltU (result := 1) (by
    simp [Project.HexEncodeStdio.Hex.hexDigit_toUInt32_lt_128 n hn])
  iapply twp_localTee rfl
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_br (by rfl)
  simp [encodeLocals, List.set]
  iexact Hfinish

/-- Common part of an encoding iteration: classify an ASCII digit, verify the
preallocated capacity, store the byte, update the vector length, and arrive at
the iterator call. -/
theorem func6_ascii_store {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (result stackPtr output capacity position : UInt32)
    (oldLen oldAscii oldDest tmp1 tmp2 : UInt32)
    (digit oldByte : UInt8) (out : List UInt8) (i n : Nat)
    (hdigit : digit = Project.HexStdio.Spec.hexDigit n) (hn : n < 16)
    (hpos : i < out.length)
    (hposition : position = UInt32.ofNat i)
    (hnext : position + 1 = UInt32.ofNat (i + 1))
    (hroom : (1 : UInt32) ≤ capacity - position)
    (hstack : stackPtr.toNat + 20 < UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 0 (stackPtr + 4) capacity ∗
      pointsTo_u32 0 (stackPtr + 8) output ∗
      pointsTo_u32 0 (stackPtr + 12) position ∗
      pointsToBytes 0 output out ∗
      (pointsTo_u32 0 (stackPtr + 4) capacity -∗
        pointsTo_u32 0 (stackPtr + 8) output -∗
        pointsTo_u32 0 (stackPtr + 12) (position + 1) -∗
        pointsToBytes 0 output (out.set i digit) -∗
        WP (.running
          ⟨encodeLocals result (position + 1) digit.toUInt32 stackPtr 1 1
              (output + position) tmp1 tmp2 [.i32 (stackPtr + 16)],
            encodeLoopCallTail, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨encodeLocals result position digit.toUInt32 stackPtr oldLen oldAscii
            oldDest tmp1 tmp2,
          encodeLoopBody, arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }] := by
  obtain ⟨p4, p5, p6, p7⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 4 (by omega)
  obtain ⟨p8, p9, p10, p11⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 8 (by omega)
  obtain ⟨p12, p13, p14, p15⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 12 (by omega)
  iintro ⟨Hcap, HoutputPtr, Hlength, Hout, Hfinish⟩
  iapply func6_ascii_classify result position stackPtr oldLen oldAscii oldDest
    tmp1 tmp2 digit n
    hdigit hn
  simp only [encodeLoopAfterClassify, encodeLoopCallTail, encodeLoopBody,
    encodeOuterBody, Project.HexStdio.func6, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.drop_succ_cons, List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_localSet rfl
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 capacity p4 p5 p6 p7 $$ Hcap
  iintro Hcap
  iapply twp_localGet rfl
  iapply twp_sub
  iapply hdtwp_leU (result := 1) (by simp [hroom])
  iapply twp_brIf (by decide) rfl
  iapply twp_localGet rfl
  iapply twp_load32 output p8 p9 p10 p11 $$ HoutputPtr
  iintro HoutputPtr
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_localSet rfl
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_brIf (by decide) rfl
  have hnext' : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
    simpa [hposition] using hnext
  rw [hposition]
  simp only [encodeLocals, List.set, UInt32.add_comm (UInt32.ofNat i) output]
  ihave Hfocus := Project.HexEncodeStdio.Helpers.pointsToBytes_focus_update
    (0 : Nat) output out i hpos $$ Hout
  icases Hfocus with ⟨%actual, Hbyte, Hput, %hactual⟩
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Project.HexEncodeStdio.TotalHelpers.twp_store8_zero actual $$ Hbyte
  iintro Hbyte
  have hdigit8 : digit.toUInt32.toUInt8 = digit := by
    apply UInt8.toNat_inj.mp
    simp
  ihave Hbyte' : (⟨0, output + UInt32.ofNat i⟩ ↦w digit) $$ [Hbyte]
  · simp only [hdigit8]
    iassumption
  ispecialize Hput $$ %digit
  ihave Hout := Hput $$ Hbyte'
  iapply twp_exitControl rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_localTee rfl
  iapply twp_store32 (UInt32.ofNat i) p12 p13 p14 p15 $$ Hlength
  iintro Hlength
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [hnext']
  simp [encodeLocals, List.set, UInt32.add_comm (16 : UInt32) stackPtr]
  iapply Hfinish $$ Hcap HoutputPtr Hlength Hout

/-- Even-position loop leg.  The iterator already contains the saved low
digit; after storing the current high digit it returns that saved digit and
branches back with the sentinel restored. -/
theorem func6_encode_loop_step_even {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (result stackPtr output capacity position : UInt32)
    (oldLen oldAscii oldDest tmp1 tmp2 : UInt32)
    (digit : UInt8) (digitIndex : Nat) (saved : UInt32)
    (out : List UInt8) (i : Nat)
    (hdigit : digit = Project.HexStdio.Spec.hexDigit digitIndex)
    (hdigitIndex : digitIndex < 16)
    (hpos : i < out.length)
    (hposition : position = UInt32.ofNat i)
    (hnext : position + 1 = UInt32.ofNat (i + 1))
    (hroom : (1 : UInt32) ≤ capacity - position)
    (hstack : stackPtr.toNat + 20 < UInt32.size)
    (hsaved : saved ≠ Project.HexEncodeStdio.TotalIterator.sentinel)
    {arity : Nat} {remainder : List Value}
    {afterLoop : Program} {controls : List ControlFrame} {calls : List CallFrame}
    {Frame : IProp (WasmHeapGF α)} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      pointsTo_u32 0 (stackPtr + 4) capacity ∗
      pointsTo_u32 0 (stackPtr + 8) output ∗
      pointsTo_u32 0 (stackPtr + 12) position ∗
      pointsTo_u32 0 (stackPtr + 16) saved ∗
      pointsToBytes 0 output out ∗
      Frame ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        pointsTo_u32 0 (stackPtr + 4) capacity -∗
        pointsTo_u32 0 (stackPtr + 8) output -∗
        pointsTo_u32 0 (stackPtr + 12) (position + 1) -∗
        pointsTo_u32 0 (stackPtr + 16) Project.HexEncodeStdio.TotalIterator.sentinel -∗
        pointsToBytes 0 output (out.set i digit) -∗
        Frame -∗
        WP (.running
          ⟨encodeLocals result (position + 1) saved stackPtr 1 1
              (output + position) tmp1 tmp2,
            encodeLoopBody, arity, remainder,
            encodeLoopFrame afterLoop :: controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨encodeLocals result position digit.toUInt32 stackPtr oldLen oldAscii
            oldDest tmp1 tmp2,
          encodeLoopBody, arity, remainder,
          encodeLoopFrame afterLoop :: controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcap, HoutputPtr, Hlength, Hiter, Hout, Hframe, Hnext⟩
  iapply func6_ascii_store result stackPtr output capacity position
    oldLen oldAscii oldDest tmp1 tmp2 digit digit out i digitIndex
    hdigit hdigitIndex hpos hposition hnext hroom hstack
  isplitl [Hcap]
  · iexact Hcap
  isplitl [HoutputPtr]
  · iexact HoutputPtr
  isplitl [Hlength]
  · iexact Hlength
  isplitl [Hout]
  · iexact Hout
  iintro Hcap HoutputPtr Hlength Hout
  simp only [encodeLoopCallTail, encodeLoopBody, encodeOuterBody,
    Project.HexStdio.func6, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.drop_succ_cons, List.drop_zero]
  iapply Project.HexEncodeStdio.TotalIterator.twp_call_func18_low (stackPtr + 16) saved hsaved
    (by
      rw [show (16 : UInt32) = UInt32.ofNat 16 by rfl,
        UInt32.add_ofNat_toNat_noWrap stackPtr 16 (by decide) (by
          have hlt : stackPtr.toNat + 16 < stackPtr.toNat + 20 := by omega
          exact lt_trans hlt hstack)]
      simpa only [Nat.add_assoc] using hstack)
    (callerLocals := encodeLocals result (position + 1) digit.toUInt32
      stackPtr 1 1 (output + position) tmp1 tmp2)
    (stack := [])
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hiter]
  · iexact Hiter
  iintro Hruntime Hiter
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_ne (result := 1) (by simpa [Project.HexEncodeStdio.TotalIterator.sentinel] using hsaved)
  iapply twp_brIf (by decide) rfl
  simp only [encodeLocals, encodeLoopFrame, List.set, List.take_zero,
    List.nil_append]
  simp only [encodeLoopBody, encodeOuterBody, Project.HexStdio.func6,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  iapply Hnext $$ Hruntime Hcap HoutputPtr Hlength Hiter Hout Hframe

/-- Odd-position loop leg when another source byte remains.  Storing the saved
low digit is followed by consuming the next byte; the iterator saves its low
digit and returns its high digit for the next iteration. -/
theorem func6_encode_loop_step_odd_more {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (result stackPtr output capacity position source : UInt32)
    (oldLen oldAscii oldDest tmp1 tmp2 : UInt32)
    (digit : UInt8) (digitIndex : Nat)
    (out input : List UInt8) (outIndex inputIndex : Nat)
    (hdigit : digit = Project.HexStdio.Spec.hexDigit digitIndex)
    (hdigitIndex : digitIndex < 16)
    (houtIndex : outIndex < out.length)
    (hposition : position = UInt32.ofNat outIndex)
    (hnext : position + 1 = UInt32.ofNat (outIndex + 1))
    (hroom : (1 : UInt32) ≤ capacity - position)
    (hstack : stackPtr.toNat + 32 < UInt32.size)
    (hsource : source.toNat + input.length + 1 < UInt32.size)
    (hmore : inputIndex + 1 < input.length)
    {arity : Nat} {remainder : List Value} {afterLoop : Program}
    {controls : List ControlFrame} {calls : List CallFrame}
    {Frame : IProp (WasmHeapGF α)} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      pointsTo_u32 0 (stackPtr + 4) capacity ∗
      pointsTo_u32 0 (stackPtr + 8) output ∗
      pointsTo_u32 0 (stackPtr + 12) position ∗
      pointsTo_u32 0 (stackPtr + 16) Project.HexEncodeStdio.TotalIterator.sentinel ∗
      pointsTo_u32 0 (stackPtr + 20)
        (source + UInt32.ofNat (inputIndex + 1)) ∗
      pointsTo_u32 0 (stackPtr + 24)
        (source + UInt32.ofNat input.length) ∗
      pointsTo_u32 0 (stackPtr + 28) 1048576 ∗
      pointsToBytes 0 source input ∗
      pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable ∗
      pointsToBytes 0 output out ∗
      Frame ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        pointsTo_u32 0 (stackPtr + 4) capacity -∗
        pointsTo_u32 0 (stackPtr + 8) output -∗
        pointsTo_u32 0 (stackPtr + 12) (position + 1) -∗
        pointsTo_u32 0 (stackPtr + 16)
          (Project.HexStdio.Spec.hexDigit
            (input[inputIndex + 1].toNat % 16)).toUInt32 -∗
        pointsTo_u32 0 (stackPtr + 20)
          (source + UInt32.ofNat (inputIndex + 2)) -∗
        pointsTo_u32 0 (stackPtr + 24)
          (source + UInt32.ofNat input.length) -∗
        pointsTo_u32 0 (stackPtr + 28) 1048576 -∗
        pointsToBytes 0 source input -∗
        pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable -∗
        pointsToBytes 0 output (out.set outIndex digit) -∗
        Frame -∗
        WP (.running
          ⟨encodeLocals result (position + 1)
              (Project.HexStdio.Spec.hexDigit
                (input[inputIndex + 1].toNat / 16)).toUInt32
              stackPtr 1 1 (output + position) tmp1 tmp2,
            encodeLoopBody, arity, remainder,
            encodeLoopFrame afterLoop :: controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨encodeLocals result position digit.toUInt32 stackPtr oldLen oldAscii
            oldDest tmp1 tmp2,
          encodeLoopBody, arity, remainder,
          encodeLoopFrame afterLoop :: controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcap, HoutputPtr, Hlength, Hcurrent, Hcursor, Hend,
    HtablePtr, Hsource, Htable, Hout, Hframe, Hnext⟩
  iapply func6_ascii_store result stackPtr output capacity position
    oldLen oldAscii oldDest tmp1 tmp2 digit digit out outIndex digitIndex
    hdigit hdigitIndex houtIndex hposition hnext hroom
    (by
      have hlt : stackPtr.toNat + 20 < stackPtr.toNat + 32 := by omega
      exact lt_trans hlt hstack)
  isplitl [Hcap]
  · iexact Hcap
  isplitl [HoutputPtr]
  · iexact HoutputPtr
  isplitl [Hlength]
  · iexact Hlength
  isplitl [Hout]
  · iexact Hout
  iintro Hcap HoutputPtr Hlength Hout
  simp only [encodeLoopCallTail, encodeLoopBody, encodeOuterBody,
    Project.HexStdio.func6, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.drop_succ_cons, List.drop_zero]
  iapply Project.HexEncodeStdio.TotalIterator.twp_call_func18_high_at (stackPtr + 16) source
    input (inputIndex + 1) hmore
    (by
      rw [show (16 : UInt32) = UInt32.ofNat 16 by rfl,
        UInt32.add_ofNat_toNat_noWrap stackPtr 16 (by decide) (by
          have hlt : stackPtr.toNat + 16 < stackPtr.toNat + 32 := by omega
          exact lt_trans hlt hstack)]
      simpa only [Nat.add_assoc] using hstack)
    hsource
    (callerLocals := encodeLocals result (position + 1) digit.toUInt32
      stackPtr 1 1 (output + position) tmp1 tmp2)
    (stack := [])
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hcurrent]
  · iexact Hcurrent
  isplitl [Hcursor]
  · rw [show stackPtr + 16 + 4 = stackPtr + 20 by bv_decide]
    iexact Hcursor
  isplitl [Hend]
  · rw [show stackPtr + 16 + 8 = stackPtr + 24 by bv_decide]
    iexact Hend
  isplitl [HtablePtr]
  · rw [show stackPtr + 16 + 12 = stackPtr + 28 by bv_decide]
    iexact HtablePtr
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htable]
  · iexact Htable
  iintro Hruntime Hcurrent Hcursor Hend HtablePtr Hsource Htable
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_ne (result := 1) (by
    simp [Project.HexEncodeStdio.Hex.hexDigit_toUInt32_ne_sentinel])
  iapply twp_brIf (by decide) rfl
  simp only [encodeLocals, encodeLoopFrame, List.set, List.take_zero,
    List.nil_append]
  simp only [encodeLoopBody, encodeOuterBody, Project.HexStdio.func6,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  ihave Hcursor' : pointsTo_u32 0 (stackPtr + 20)
      (source + UInt32.ofNat (inputIndex + 2)) $$ [Hcursor]
  · rw [show stackPtr + 16 + 4 = stackPtr + 20 by bv_decide,
      show inputIndex + 1 + 1 = inputIndex + 2 by omega]
    iexact Hcursor
  ihave Hend' : pointsTo_u32 0 (stackPtr + 24)
      (source + UInt32.ofNat input.length) $$ [Hend]
  · rw [show stackPtr + 16 + 8 = stackPtr + 24 by bv_decide]
    iexact Hend
  ihave HtablePtr' : pointsTo_u32 0 (stackPtr + 28) 1048576 $$ [HtablePtr]
  · rw [show stackPtr + 16 + 12 = stackPtr + 28 by bv_decide]
    iexact HtablePtr
  iapply Hnext $$ Hruntime Hcap HoutputPtr Hlength Hcurrent Hcursor' Hend'
    HtablePtr' Hsource Htable Hout Hframe

/-- Odd-position loop leg for the final source byte.  The iterator returns its
sentinel, so `br_if 0` falls through and the loop control frame exits. -/
theorem func6_encode_loop_step_odd_end {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (result stackPtr output capacity position source finish : UInt32)
    (oldLen oldAscii oldDest tmp1 tmp2 : UInt32)
    (digit : UInt8) (digitIndex : Nat)
    (out input : List UInt8) (outIndex : Nat)
    (hdigit : digit = Project.HexStdio.Spec.hexDigit digitIndex)
    (hdigitIndex : digitIndex < 16)
    (houtIndex : outIndex < out.length)
    (hposition : position = UInt32.ofNat outIndex)
    (hnext : position + 1 = UInt32.ofNat (outIndex + 1))
    (hroom : (1 : UInt32) ≤ capacity - position)
    (hstack : stackPtr.toNat + 32 < UInt32.size)
    {arity : Nat} {remainder : List Value} {afterLoop : Program}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      pointsTo_u32 0 (stackPtr + 4) capacity ∗
      pointsTo_u32 0 (stackPtr + 8) output ∗
      pointsTo_u32 0 (stackPtr + 12) position ∗
      pointsTo_u32 0 (stackPtr + 16) Project.HexEncodeStdio.TotalIterator.sentinel ∗
      pointsTo_u32 0 (stackPtr + 20) finish ∗
      pointsTo_u32 0 (stackPtr + 24) finish ∗
      pointsTo_u32 0 (stackPtr + 28) 1048576 ∗
      pointsToBytes 0 source input ∗
      pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable ∗
      pointsToBytes 0 output out ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        pointsTo_u32 0 (stackPtr + 4) capacity -∗
        pointsTo_u32 0 (stackPtr + 8) output -∗
        pointsTo_u32 0 (stackPtr + 12) (position + 1) -∗
        pointsTo_u32 0 (stackPtr + 16) Project.HexEncodeStdio.TotalIterator.sentinel -∗
        pointsTo_u32 0 (stackPtr + 20) finish -∗
        pointsTo_u32 0 (stackPtr + 24) finish -∗
        pointsTo_u32 0 (stackPtr + 28) 1048576 -∗
        pointsToBytes 0 source input -∗
        pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable -∗
        pointsToBytes 0 output (out.set outIndex digit) -∗
        WP (.running
          ⟨encodeLocals result (position + 1) Project.HexEncodeStdio.TotalIterator.sentinel
              stackPtr 1 1 (output + position) tmp1 tmp2,
            afterLoop, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨encodeLocals result position digit.toUInt32 stackPtr oldLen oldAscii
            oldDest tmp1 tmp2,
          encodeLoopBody, arity, remainder,
          encodeLoopFrame afterLoop :: controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcap, HoutputPtr, Hlength, Hcurrent, Hcursor, Hend,
    HtablePtr, Hsource, Htable, Hout, Hnext⟩
  iapply func6_ascii_store result stackPtr output capacity position
    oldLen oldAscii oldDest tmp1 tmp2 digit digit out outIndex digitIndex
    hdigit hdigitIndex houtIndex hposition hnext hroom
    (by
      have hlt : stackPtr.toNat + 20 < stackPtr.toNat + 32 := by omega
      exact lt_trans hlt hstack)
  isplitl [Hcap]
  · iexact Hcap
  isplitl [HoutputPtr]
  · iexact HoutputPtr
  isplitl [Hlength]
  · iexact Hlength
  isplitl [Hout]
  · iexact Hout
  iintro Hcap HoutputPtr Hlength Hout
  simp only [encodeLoopCallTail, encodeLoopBody, encodeOuterBody,
    Project.HexStdio.func6, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.drop_succ_cons, List.drop_zero]
  iapply Project.HexEncodeStdio.TotalIterator.twp_call_func18_end (stackPtr + 16) finish
    (by
      rw [show (16 : UInt32) = UInt32.ofNat 16 by rfl,
        UInt32.add_ofNat_toNat_noWrap stackPtr 16 (by decide) (by
          have hlt : stackPtr.toNat + 16 < stackPtr.toNat + 32 := by omega
          exact lt_trans hlt hstack)]
      have hlt : stackPtr.toNat + 16 + 12 < stackPtr.toNat + 32 := by omega
      exact lt_trans hlt hstack)
    (callerLocals := encodeLocals result (position + 1) digit.toUInt32
      stackPtr 1 1 (output + position) tmp1 tmp2)
    (stack := [])
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hcurrent]
  · iexact Hcurrent
  isplitl [Hcursor]
  · rw [show stackPtr + 16 + 4 = stackPtr + 20 by bv_decide]
    iexact Hcursor
  isplitl [Hend]
  · rw [show stackPtr + 16 + 8 = stackPtr + 24 by bv_decide]
    iexact Hend
  iintro Hruntime Hcurrent Hcursor Hend
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_ne (result := 0) (by simp)
  iapply twp_brIfZero
  iapply twp_exitControl rfl
  simp only [encodeLocals, encodeLoopFrame, List.set, List.take_zero,
    List.nil_append]
  ihave Hcursor' : pointsTo_u32 0 (stackPtr + 20) finish $$ [Hcursor]
  · rw [show stackPtr + 16 + 4 = stackPtr + 20 by bv_decide]
    iexact Hcursor
  ihave Hend' : pointsTo_u32 0 (stackPtr + 24) finish $$ [Hend]
  · rw [show stackPtr + 16 + 8 = stackPtr + 24 by bv_decide]
    iexact Hend
  iapply Hnext $$ Hruntime Hcap HoutputPtr Hlength Hcurrent Hcursor' Hend'
    HtablePtr Hsource Htable Hout

/-- The complete family-indexed encode loop.  `Finish` is an arbitrary framed
resource needed by the caller after the last low digit is emitted. -/
theorem func6_encode_loop {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (result stackPtr output source : UInt32) (input : List UInt8)
    (initial : EncodeLoopState input)
    (Finish : IProp (WasmHeapGF α))
    (hcapacity : 2 * input.length < UInt32.size)
    (hstack : stackPtr.toNat + 32 < UInt32.size)
    (hsource : source.toNat + input.length + 1 < UInt32.size)
    {arity : Nat} {remainder : List Value} {afterLoop : Program}
    {controls : List ControlFrame} {calls : List CallFrame}
    (exit_closes : ∀ (state : EncodeLoopState input) (out : List UInt8),
      state.lowPhase = true → state.byteIndex + 1 = input.length →
      out.length = 2 * input.length →
      out.take (loopPosition state + 1) =
        (Project.HexStdio.Spec.encode input).take (loopPosition state + 1) →
      ⊢@{IProp (WasmHeapGF α)} (iprop%
        runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        pointsTo_u32 0 (stackPtr + 4)
          (UInt32.ofNat (encodeCapacityNat input)) -∗
        pointsTo_u32 0 (stackPtr + 8) output -∗
        pointsTo_u32 0 (stackPtr + 12)
          (UInt32.ofNat (2 * state.byteIndex + 1) + 1) -∗
        pointsTo_u32 0 (stackPtr + 16) Project.HexEncodeStdio.TotalIterator.sentinel -∗
        pointsTo_u32 0 (stackPtr + 20)
          (source + UInt32.ofNat input.length) -∗
        pointsTo_u32 0 (stackPtr + 24)
          (source + UInt32.ofNat input.length) -∗
        pointsTo_u32 0 (stackPtr + 28) 1048576 -∗
        pointsToBytes 0 source input -∗
        pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable -∗
        pointsToBytes 0 output out -∗ Finish -∗
        WP (.running
          ⟨encodeLocals result
              (UInt32.ofNat (2 * state.byteIndex + 1) + 1)
              Project.HexEncodeStdio.TotalIterator.sentinel stackPtr 1 1
              (output + UInt32.ofNat (2 * state.byteIndex + 1)) 0 0,
            afterLoop, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }])) :
    encodeLoopInvariant result stackPtr output source input Finish initial ⊢
      WP (.running
        ⟨loopLocals result stackPtr output initial,
          .loop 0 0 encodeLoopBody :: afterLoop,
          arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hinitial
  have hcapacity' : encodeCapacityNat input < UInt32.size := by
    simp only [encodeCapacityNat]
    omega
  iapply twp_loop_wf_family
    (measure := fun state : EncodeLoopState input =>
      2 * input.length - loopPosition state)
    (locals := fun state => loopLocals result stackPtr output state)
    (I := fun state =>
      encodeLoopInvariant result stackPtr output source input Finish state)
    (initial := initial)
    (initialLocals := loopLocals result stackPtr output initial)
    (body := encodeLoopBody)
    (code := afterLoop)
    (belowStack := [])
    rfl rfl
  intro state
  rcases state with ⟨byteIndex, hbyteIndex, lowPhase, dest, oldLen, oldAscii⟩
  simp only [Wasm.SmallStep.loopBodyExpr]
  cases lowPhase with
  | false =>
      iintro Hrec Hstate
      icases Hstate with ⟨Hruntime, Hcap, HoutputPtr, Hlength, Hcurrent, Hcursor,
        Hend, HtablePtr, Hsource, Htable, Hinv⟩
      icases Hinv with ⟨%out, Hout, %houtLen, %hprefix, Hfinish⟩
      let next : EncodeLoopState input :=
        ⟨byteIndex, hbyteIndex, true, output + UInt32.ofNat (2 * byteIndex),
          1, 1⟩
      have hpos : 2 * byteIndex < out.length := by omega
      have hnextU : UInt32.ofNat (2 * byteIndex) + 1 =
          UInt32.ofNat (2 * byteIndex + 1) :=
        u32_ofNat_succ (by omega)
      have hroom : (1 : UInt32) ≤
          UInt32.ofNat (encodeCapacityNat input) -
            UInt32.ofNat (2 * byteIndex) :=
        u32_room (by simp [encodeCapacityNat]; omega) hcapacity'
      ispecialize Hrec $$ %next %(by
        simp only [next, loopPosition]
        omega)
      simp only [loopLocals, loopPosition, loopDigit]
      have hposWord : (2 : UInt32) * UInt32.ofNat byteIndex =
          UInt32.ofNat (2 * byteIndex) := by
        simpa using (UInt32.ofNat_mul 2 byteIndex).symm
      iapply func6_encode_loop_step_even result stackPtr output
        (UInt32.ofNat (encodeCapacityNat input))
        (UInt32.ofNat (2 * byteIndex))
        oldLen oldAscii dest 0 0
        (Project.HexStdio.Spec.hexDigit (input[byteIndex].toNat / 16))
        (input[byteIndex].toNat / 16)
        (Project.HexStdio.Spec.hexDigit (input[byteIndex].toNat % 16)).toUInt32
        out (2 * byteIndex) rfl (Project.HexEncodeStdio.Hex.nibble_high_lt _)
        hpos rfl hnextU hroom (by omega)
        (Project.HexEncodeStdio.Hex.hexDigit_toUInt32_ne_sentinel _)
        (s := s) (E := E) (Φ := Φ) (arity := arity)
        (remainder := remainder) (afterLoop := afterLoop)
        (controls := controls) (calls := calls)
      isplitl [Hruntime]
      · iexact Hruntime
      isplitl [Hcap]
      · iexact Hcap
      isplitl [HoutputPtr]
      · iexact HoutputPtr
      isplitl [Hlength]
      · iexact Hlength
      isplitl [Hcurrent]
      · simp only [loopSaved]
        iexact Hcurrent
      isplitl [Hout]
      · iexact Hout
      isplitl [Hrec]
      · iexact Hrec
      iintro Hruntime Hcap HoutputPtr Hlength Hcurrent Hout Hrecursive
      simp only [next, loopLocals, loopPosition, loopDigit,
        encodeLoopFrame]
      rw [← hnextU]
      iapply Hrecursive
      simp only [encodeLoopInvariant]
      isplitl [Hruntime]
      · iexact Hruntime
      isplitl [Hcap]
      · iexact Hcap
      isplitl [HoutputPtr]
      · iexact HoutputPtr
      isplitl [Hlength]
      · rw [← hnextU]
        iexact Hlength
      isplitl [Hcurrent]
      · iexact Hcurrent
      isplitl [Hcursor]
      · iexact Hcursor
      isplitl [Hend]
      · iexact Hend
      isplitl [HtablePtr]
      · iexact HtablePtr
      isplitl [Hsource]
      · iexact Hsource
      isplitl [Htable]
      · iexact Htable
      iexists (out.set (2 * byteIndex)
        (Project.HexStdio.Spec.hexDigit (input[byteIndex].toNat / 16)))
      isplitl [Hout]
      · iexact Hout
      isplitr
      · ipureintro
        simpa only [List.length_set] using houtLen
      isplitr
      · ipureintro
        simpa only [next, loopPosition] using
          update_prefix_high input out byteIndex hbyteIndex houtLen hprefix
      · iexact Hfinish
  | true =>
      iintro Hrec Hstate
      icases Hstate with ⟨Hruntime, Hcap, HoutputPtr, Hlength, Hcurrent, Hcursor,
        Hend, HtablePtr, Hsource, Htable, Hinv⟩
      icases Hinv with ⟨%out, Hout, %houtLen, %hprefix, Hfinish⟩
      have hpos : 2 * byteIndex + 1 < out.length := by omega
      have hnextU : UInt32.ofNat (2 * byteIndex + 1) + 1 =
          UInt32.ofNat (2 * byteIndex + 1 + 1) :=
        u32_ofNat_succ (by omega)
      have hroom : (1 : UInt32) ≤ UInt32.ofNat (encodeCapacityNat input) -
          UInt32.ofNat (2 * byteIndex + 1) :=
        u32_room (by simp [encodeCapacityNat]; omega) hcapacity'
      have hposWord : (2 : UInt32) * UInt32.ofNat byteIndex + 1 =
          UInt32.ofNat (2 * byteIndex + 1) := by
        exact (congrArg (fun x : UInt32 => x + UInt32.ofNat 1)
          (UInt32.ofNat_mul 2 byteIndex)).symm.trans
            (UInt32.ofNat_add (2 * byteIndex) 1).symm
      by_cases hmore : byteIndex + 1 < input.length
      · let next : EncodeLoopState input :=
          ⟨byteIndex + 1, hmore, false,
            output + UInt32.ofNat (2 * byteIndex + 1), 1, 1⟩
        ispecialize Hrec $$ %next %(by
          simp only [next, loopPosition]
          omega)
        simp only [loopLocals, loopPosition, loopDigit]
        iapply func6_encode_loop_step_odd_more result stackPtr output
          (UInt32.ofNat (encodeCapacityNat input))
          (UInt32.ofNat (2 * byteIndex + 1)) source
          oldLen oldAscii dest 0 0
          (Project.HexStdio.Spec.hexDigit (input[byteIndex].toNat % 16))
          (input[byteIndex].toNat % 16) out input (2 * byteIndex + 1)
          byteIndex rfl (Project.HexEncodeStdio.Hex.nibble_low_lt _) hpos rfl hnextU
          hroom hstack hsource hmore
          (s := s) (E := E) (Φ := Φ) (arity := arity)
          (remainder := remainder) (afterLoop := afterLoop)
          (controls := controls) (calls := calls)
        isplitl [Hruntime]
        · iexact Hruntime
        isplitl [Hcap]
        · iexact Hcap
        isplitl [HoutputPtr]
        · iexact HoutputPtr
        isplitl [Hlength]
        · iexact Hlength
        isplitl [Hcurrent]
        · simp only [loopSaved]
          iexact Hcurrent
        isplitl [Hcursor]
        · iexact Hcursor
        isplitl [Hend]
        · iexact Hend
        isplitl [HtablePtr]
        · iexact HtablePtr
        isplitl [Hsource]
        · iexact Hsource
        isplitl [Htable]
        · iexact Htable
        isplitl [Hout]
        · iexact Hout
        isplitl [Hrec]
        · iexact Hrec
        iintro Hruntime Hcap HoutputPtr Hlength Hcurrent Hcursor Hend
          HtablePtr Hsource Htable Hout Hrecursive
        have hnextPos : UInt32.ofNat (2 * byteIndex + 1) + 1 =
            UInt32.ofNat (2 * (byteIndex + 1)) := by
          calc
            _ = UInt32.ofNat (2 * byteIndex + 1 + 1) := hnextU
            _ = _ := congrArg UInt32.ofNat (by omega)
        simp only [next, loopLocals, loopPosition, loopDigit,
          encodeLoopFrame]
        rw [← hnextPos]
        iapply Hrecursive
        simp only [encodeLoopInvariant]
        isplitl [Hruntime]
        · iexact Hruntime
        isplitl [Hcap]
        · iexact Hcap
        isplitl [HoutputPtr]
        · iexact HoutputPtr
        isplitl [Hlength]
        · rw [← hnextPos]
          iexact Hlength
        isplitl [Hcurrent]
        · iexact Hcurrent
        isplitl [Hcursor]
        · rw [show byteIndex + 1 + 1 = byteIndex + 2 by omega]
          iexact Hcursor
        isplitl [Hend]
        · iexact Hend
        isplitl [HtablePtr]
        · iexact HtablePtr
        isplitl [Hsource]
        · iexact Hsource
        isplitl [Htable]
        · iexact Htable
        iexists (out.set (2 * byteIndex + 1)
          (Project.HexStdio.Spec.hexDigit (input[byteIndex].toNat % 16)))
        isplitl [Hout]
        · iexact Hout
        isplitr
        · ipureintro
          simpa only [List.length_set] using houtLen
        isplitr
        · ipureintro
          simp only [next, loopPosition]
          rw [show 2 * (byteIndex + 1) = 2 * byteIndex + 2 by omega]
          exact update_prefix_low input out byteIndex hbyteIndex houtLen hprefix
        · iexact Hfinish
      · have hendIndex : byteIndex + 1 = input.length := by omega
        have hfinish : source + UInt32.ofNat (byteIndex + 1) =
            source + UInt32.ofNat input.length := by rw [hendIndex]
        ihave Hcursor' : pointsTo_u32 0 (stackPtr + 20)
            (source + UInt32.ofNat input.length) $$ [Hcursor]
        · rw [← hfinish]
          iexact Hcursor
        simp only [loopLocals, loopPosition, loopDigit]
        iapply func6_encode_loop_step_odd_end result stackPtr output
          (UInt32.ofNat (encodeCapacityNat input))
          (UInt32.ofNat (2 * byteIndex + 1)) source
          (source + UInt32.ofNat input.length)
          oldLen oldAscii dest 0 0
          (Project.HexStdio.Spec.hexDigit (input[byteIndex].toNat % 16))
          (input[byteIndex].toNat % 16) out input (2 * byteIndex + 1)
          rfl (Project.HexEncodeStdio.Hex.nibble_low_lt _) hpos rfl hnextU hroom hstack
          (s := s) (E := E) (Φ := Φ) (arity := arity)
          (remainder := remainder) (afterLoop := afterLoop)
          (controls := controls) (calls := calls)
        isplitl [Hruntime]
        · iexact Hruntime
        isplitl [Hcap]
        · iexact Hcap
        isplitl [HoutputPtr]
        · iexact HoutputPtr
        isplitl [Hlength]
        · iexact Hlength
        isplitl [Hcurrent]
        · simp only [loopSaved]
          iexact Hcurrent
        isplitl [Hcursor']
        · iexact Hcursor'
        isplitl [Hend]
        · iexact Hend
        isplitl [HtablePtr]
        · iexact HtablePtr
        isplitl [Hsource]
        · iexact Hsource
        isplitl [Htable]
        · iexact Htable
        isplitl [Hout]
        · iexact Hout
        iintro Hruntime Hcap HoutputPtr Hlength Hcurrent Hcursor Hend
          HtablePtr Hsource Htable Hout
        iapply exit_closes
          ⟨byteIndex, hbyteIndex, true, dest, oldLen, oldAscii⟩
          (out.set (2 * byteIndex + 1)
            (Project.HexStdio.Spec.hexDigit (input[byteIndex].toNat % 16)))
          rfl hendIndex
          (by simpa only [List.length_set] using houtLen)
          (by
            have hp := update_prefix_low input out byteIndex hbyteIndex
              houtLen hprefix
            simpa [loopPosition, hendIndex,
              Project.HexEncodeStdio.Hex.encode_length] using hp)
          $$ Hruntime Hcap HoutputPtr Hlength Hcurrent Hcursor Hend HtablePtr
            Hsource Htable Hout Hfinish
  iexact Hinitial

end Project.HexEncodeStdio.TotalEncodeLoop
