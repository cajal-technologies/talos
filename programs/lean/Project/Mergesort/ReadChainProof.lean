import Project.Mergesort.DriverInputProof

/-!
# Generated buffered read chain

This file continues `DriverInputProof.lean` below the driver's `read_line`
shim.  `readLine_call_to_inner_twp` stops exactly at the inner `.call 24`;
the chain underneath, in generated local functions, is

* `func22` (absolute call 24) — the `String::read_line` append guard: it
  records the string's current length, forwards to `read_until`, then
  validates the appended bytes as UTF-8 (absolute call 215) and runs the
  guard drop (absolute call 26);
* `func23` (absolute call 25) — the `read_until` entry shim, fixing the
  delimiter byte `10` (`b'\n'`);
* `func15` (absolute call 17) — the `read_until` fill/search/append loop:
  each iteration calls `fill_buf` (absolute call 18), searches the fresh
  bytes for the delimiter (absolute call 20), appends into the destination
  vector (absolute call 21) and consumes the used bytes (absolute call 22);
* `func16` (absolute call 18) — the `fill_buf` shim onto the `BufReader`
  internals (absolute call 40, `func38`), whose buffer-refill path bottoms
  out in `func27` (absolute call 29) → `func141` (absolute call 143) →
  `func133` (absolute call 135) → the `stdio.read` host import handled by
  `stdioReadWrapper_to_import_twp`.

Every rule here stops exactly at a generated call boundary, in the same seam
idiom as `DriverInputProof.lean`: nothing about the host read, the allocator,
or the memory search is assumed or hidden.
-/

namespace Project.Mergesort.ReadChainProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.DriverProof
open Project.Mergesort.StdIOWrapperProof
open Project.Mergesort.RangeProof
open Project.Mergesort.SplitAtProof
open Project.Mergesort.FormatProof
open Project.Mergesort.VectorProof
open Project.Mergesort.MemoryFillProof
open Project.Mergesort.DriverInputProof

/-! ## Stable names for the read-chain callees -/

theorem readUntilShim_index : «module».funcs[23]? = some func23Def := by rfl
theorem readUntilLoop_index : «module».funcs[15]? = some func15Def := by rfl
theorem fillBufShim_index : «module».funcs[16]? = some func16Def := by rfl
theorem fillBufImpl_index : «module».funcs[38]? = some func38Def := by rfl
theorem rawReadForward_index : «module».funcs[27]? = some func27Def := by rfl
theorem rawRead_index : «module».funcs[141]? = some func141Def := by rfl

/-! ## `read_line` append guard (`func22`, absolute call 24)

The generated body installs a 32-byte frame, saves the destination string and
its current length in the frame (the UTF-8 rollback guard `(string, oldLen)`),
and forwards `(result, reader, string)` to `read_until` at absolute call 25.
After that call returns it validates the appended suffix (absolute call 215)
and runs the guard finaliser (absolute call 26); both stay behind this rule's
stopping point. -/

def lineReadAtReadUntil : Program := func22.drop 19
def lineReadAfterReadUntil : Program := func22.drop 20

theorem func22_eq_readUntilPrefix :
    func22 =
      [.globalGet 0, .const 32, .sub, .localSet 3, .localGet 3, .globalSet 0,
       .localGet 1, .load32 8, .localSet 4,
       .localGet 3, .localGet 1, .store32 4,
       .localGet 3, .localGet 4, .store32 8,
       .localGet 0, .localGet 2, .localGet 3, .load32 4] ++
      lineReadAtReadUntil := by
  rfl

theorem lineReadAtReadUntil_eq :
    lineReadAtReadUntil = .call 25 :: lineReadAfterReadUntil := by
  rfl

/-- Exact body prefix of the `read_line` append guard: install the 32-byte
frame, record the rollback guard `(line, lineLen)` at `frame + 4`, and stop
right before the `read_until` call at absolute index 25 with
`(result, reader, line)` on the stack. -/
theorem lineRead_body_to_readUntil_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (result line reader stackTop : UInt32)
    (lineLen old4 old8 : UInt32)
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    (hlineRoom : line.toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (line + 8) lineLen ∗
      pointsTo_u32 ((stackTop - 32) + 4) old4 ∗
      pointsTo_u32 ((stackTop - 32) + 8) old8 ∗
      (globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        pointsTo_u32 (line + 8) lineLen -∗
        pointsTo_u32 ((stackTop - 32) + 4) line -∗
        pointsTo_u32 ((stackTop - 32) + 8) lineLen -∗
        WP (.running
          ⟨⟨[.i32 result, .i32 line, .i32 reader],
              [.i32 (stackTop - 32), .i32 lineLen, .i32 0, .i32 0, .i32 0,
               .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 line, .i32 reader, .i32 result]⟩,
            lineReadAtReadUntil, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 result, .i32 line, .i32 reader],
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
           .i32 0, .i32 0, .i32 0], []⟩,
        func22, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h40, h41, h42, h43⟩ :=
    descriptorSlot32Facts (stackTop - 32) 4 32 hframeRoom (by decide)
  obtain ⟨h80, h81, h82, h83⟩ :=
    descriptorSlot32Facts (stackTop - 32) 8 32 hframeRoom (by decide)
  obtain ⟨hl0, hl1, hl2, hl3⟩ :=
    descriptorSlot32Facts line 8 12 hlineRoom (by decide)
  iintro ⟨Hglobal, Hlen, H4, H8, Hcont⟩
  rw [func22_eq_readUntilPrefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_load32 lineLen hl0 hl1 hl2 hl3 $$ Hlen
  iintro Hlen
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old4 h40 h41 h42 h43 $$ H4
  iintro H4
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old8 h80 h81 h82 h83 $$ H8
  iintro H8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 line h40 h41 h42 h43 $$ H4
  iintro H4
  iapply Hcont $$ Hglobal Hlen H4 H8

/-- Composable entry rule for the `read_line` append guard at absolute index
24, stopping at the `read_until` boundary inside the freshly pushed callee
frame.  Its starting state is exactly where
`readLine_call_to_inner_twp` in `DriverInputProof.lean` stops. -/
theorem lineRead_call_to_readUntil_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (result line reader stackTop : UInt32)
    (lineLen old4 old8 : UInt32)
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    (hlineRoom : line.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (line + 8) lineLen ∗
      pointsTo_u32 ((stackTop - 32) + 4) old4 ∗
      pointsTo_u32 ((stackTop - 32) + 8) old8 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        pointsTo_u32 (line + 8) lineLen -∗
        pointsTo_u32 ((stackTop - 32) + 4) line -∗
        pointsTo_u32 ((stackTop - 32) + 8) lineLen -∗
        WP (.running
          ⟨⟨[.i32 result, .i32 line, .i32 reader],
              [.i32 (stackTop - 32), .i32 lineLen, .i32 0, .i32 0, .i32 0,
               .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 line, .i32 reader, .i32 result]⟩,
            lineReadAtReadUntil, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 reader, .i32 line, .i32 result] ++ stack },
        .call 24 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hlen, H4, H8, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 24 func22Def
      (by decide) lineReadImpl_index $$ Hruntime
  iintro Hruntime
  simp [func22Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := lineRead_body_to_readUntil_twp (α := α)
    result line reader stackTop lineLen old4 old8 hframeRoom hlineRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hlen]
  · iexact Hlen
  isplitl [H4]
  · iexact H4
  isplitl [H8]
  · iexact H8
  iintro Hglobal Hlen H4 H8
  iapply Hcont $$ Hruntime Hglobal Hlen H4 H8

/-! ## `read_until` entry shim (`func23`, absolute call 25)

The generated body forwards `(result, reader, line)` as
`(result, reader, 10, line)` — the newline delimiter appears here — to the
`read_until` loop at absolute call 17. -/

def readUntilShimAtLoop : Program := func23.drop 4

theorem func23_eq_loopPrefix :
    func23 = [.localGet 0, .localGet 1, .const 10, .localGet 2] ++
      readUntilShimAtLoop := by
  rfl

theorem readUntilShimAtLoop_eq :
    readUntilShimAtLoop = [.call 17, .ret] := by
  rfl

/-- Exact body prefix of the `read_until` entry shim, ending at the loop
call. -/
theorem readUntilShim_body_to_loop_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (result reader line : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 result, .i32 reader, .i32 line], [],
          [.i32 line, .i32 10, .i32 reader, .i32 result]⟩,
        readUntilShimAtLoop, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 result, .i32 reader, .i32 line], [], []⟩,
        func23, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  rw [func23_eq_loopPrefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iexact Hcont

/-- Composable entry rule for the `read_until` shim at absolute index 25,
stopping at the inner absolute call 17 inside the freshly pushed callee
frame. -/
theorem readUntilShim_call_to_loop_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (result reader line : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 result, .i32 reader, .i32 line], [],
              [.i32 line, .i32 10, .i32 reader, .i32 result]⟩,
            readUntilShimAtLoop, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 line, .i32 reader, .i32 result] ++ stack },
        .call 25 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 25 func23Def
      (by decide) readUntilShim_index $$ Hruntime
  iintro Hruntime
  simp [func23Def, Function.toLocals, Function.numParams]
  have Hbody := readUntilShim_body_to_loop_twp (α := α)
    result reader line (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-! ## `read_until` loop (`func15`, absolute call 17)

The generated body installs a 96-byte frame, zeroes the running byte count at
`frame + 16`, and enters a `block`/`loop` pair whose every iteration starts by
calling `fill_buf` (absolute call 18) with the scratch slot `frame + 20` and
the reader.  The rules below stop exactly at that call, with both control
frames explicit, so a later loop proof can continue with
`twp_loop_wf_family`-style reasoning without re-deriving the entry. -/

def readUntilEpilogue : Program := func15.drop 10

/-- The single generated loop inside `func15`'s outer block. -/
def readUntilLoopBody : Program :=
  match (func15.drop 9).head? with
  | some (Instruction.block _ _ [Instruction.loop _ _ body _ _] _ _) => body
  | _ => []

theorem func15_eq_loopStructure :
    func15 =
      [.globalGet 0, .const 96, .sub, .localSet 4, .localGet 4, .globalSet 0,
       .localGet 4, .const 0, .store32 16] ++
      .block 0 0 [.loop 0 0 readUntilLoopBody] :: readUntilEpilogue := by
  rfl

theorem readUntilEpilogue_eq :
    readUntilEpilogue =
      [.localGet 4, .const 96, .add, .globalSet 0, .ret] := by
  rfl

def readUntilAtFillBuf : Program := readUntilLoopBody.drop 4
def readUntilAfterFillBuf : Program := readUntilLoopBody.drop 5

theorem readUntilLoopBody_eq_fillBufPrefix :
    readUntilLoopBody =
      [.localGet 4, .const 20, .add, .localGet 1] ++ readUntilAtFillBuf := by
  rfl

theorem readUntilAtFillBuf_eq :
    readUntilAtFillBuf = .call 18 :: readUntilAfterFillBuf := by
  rfl

/-- Control frame of `func15`'s outer block, exactly as `twp_block` pushes
it when the operand stack is empty. -/
def readUntilBlockFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := [.loop 0 0 readUntilLoopBody]
    continuation := readUntilEpilogue
    belowStack := [] }

/-- Control frame of `func15`'s loop, exactly as `twp_loop` pushes it when
the operand stack is empty. -/
def readUntilLoopFrame : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := readUntilLoopBody
    continuation := []
    belowStack := [] }

/-- Exact body prefix of the `read_until` loop: install the 96-byte frame,
zero the running byte count at `frame + 16`, enter the block and the loop,
and stop right before the first `fill_buf` call at absolute index 18. -/
theorem readUntilLoop_body_to_fillBuf_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (result reader delim line stackTop : UInt32)
    (old16 : UInt32)
    (hframeRoom : (stackTop - 96).toNat + 96 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 96) + 16) old16 ∗
      (globalPointsTo 0 (.i32 (stackTop - 96)) -∗
        pointsTo_u32 ((stackTop - 96) + 16) 0 -∗
        WP (.running
          ⟨⟨[.i32 result, .i32 reader, .i32 delim, .i32 line],
              [.i32 (stackTop - 96), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
               .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 reader, .i32 (20 + (stackTop - 96))]⟩,
            readUntilAtFillBuf, 0, [],
            [readUntilLoopFrame, readUntilBlockFrame], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 result, .i32 reader, .i32 delim, .i32 line],
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
           .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        func15, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h160, h161, h162, h163⟩ :=
    descriptorSlot32Facts (stackTop - 96) 16 96 hframeRoom (by decide)
  iintro ⟨Hglobal, H16, Hcont⟩
  rw [func15_eq_loopStructure]
  simp only [List.cons_append, List.nil_append]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old16 h160 h161 h162 h163 $$ H16
  iintro H16
  iapply twp_block
  iapply twp_loop
  rw [readUntilLoopBody_eq_fillBufPrefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  rw [show (Instruction.localGet 4 :: Instruction.const 20 ::
      Instruction.add :: Instruction.localGet 1 :: readUntilAtFillBuf) =
      readUntilLoopBody from rfl]
  simp only [List.drop_zero]
  rw [show ControlFrame.mk ControlKind.loop 0 0 readUntilLoopBody [] [] =
        readUntilLoopFrame from rfl,
      show ControlFrame.mk ControlKind.block 0 0
          [Instruction.loop 0 0 readUntilLoopBody] readUntilEpilogue [] =
        readUntilBlockFrame from rfl]
  iapply Hcont $$ Hglobal H16

/-- Composable entry rule for the `read_until` loop at absolute index 17,
stopping at the first `fill_buf` boundary inside the freshly pushed callee
frame, with the block and loop control frames explicit. -/
theorem readUntilLoop_call_to_fillBuf_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (result reader delim line stackTop : UInt32)
    (old16 : UInt32)
    (hframeRoom : (stackTop - 96).toNat + 96 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 96) + 16) old16 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 96)) -∗
        pointsTo_u32 ((stackTop - 96) + 16) 0 -∗
        WP (.running
          ⟨⟨[.i32 result, .i32 reader, .i32 delim, .i32 line],
              [.i32 (stackTop - 96), .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
               .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
              [.i32 reader, .i32 (20 + (stackTop - 96))]⟩,
            readUntilAtFillBuf, 0, [],
            [readUntilLoopFrame, readUntilBlockFrame],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 line, .i32 delim, .i32 reader, .i32 result] ++ stack },
        .call 17 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, H16, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 17 func15Def
      (by decide) readUntilLoop_index $$ Hruntime
  iintro Hruntime
  simp [func15Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := readUntilLoop_body_to_fillBuf_twp (α := α)
    result reader delim line stackTop old16 hframeRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [H16]
  · iexact H16
  iintro Hglobal H16
  iapply Hcont $$ Hruntime Hglobal H16

/-! ## `fill_buf` shim (`func16`, absolute call 18)

The generated body forwards `(dst, reader)` as `(dst, reader, reader + 20)`
to the `BufReader` refill implementation at absolute call 40. -/

def fillBufShimAtImpl : Program := func16.drop 5

theorem func16_eq_implPrefix :
    func16 = [.localGet 0, .localGet 1, .localGet 1, .const 20, .add] ++
      fillBufShimAtImpl := by
  rfl

theorem fillBufShimAtImpl_eq :
    fillBufShimAtImpl = [.call 40, .ret] := by
  rfl

/-- Exact body prefix of the `fill_buf` shim, ending at the refill call. -/
theorem fillBufShim_body_to_impl_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst reader : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 dst, .i32 reader], [],
          [.i32 (20 + reader), .i32 reader, .i32 dst]⟩,
        fillBufShimAtImpl, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 dst, .i32 reader], [], []⟩,
        func16, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  rw [func16_eq_implPrefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iexact Hcont

/-- Composable entry rule for the `fill_buf` shim at absolute index 18,
stopping at the refill absolute call 40 inside the freshly pushed callee
frame. -/
theorem fillBufShim_call_to_impl_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst reader : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 dst, .i32 reader], [],
              [.i32 (20 + reader), .i32 reader, .i32 dst]⟩,
            fillBufShimAtImpl, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 reader, .i32 dst] ++ stack },
        .call 18 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 18 func16Def
      (by decide) fillBufShim_index $$ Hruntime
  iintro Hruntime
  simp [func16Def, Function.toLocals, Function.numParams]
  have Hbody := fillBufShim_body_to_impl_twp (α := α)
    dst reader (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-! ## Raw-read forwarder (`func27`, absolute call 29)

The generated body forwards its four arguments unchanged to the `Stdin` read
implementation at absolute call 143. -/

def rawReadForwardAtImpl : Program := func27.drop 4

theorem func27_eq_implPrefix :
    func27 = [.localGet 0, .localGet 1, .localGet 2, .localGet 3] ++
      rawReadForwardAtImpl := by
  rfl

theorem rawReadForwardAtImpl_eq :
    rawReadForwardAtImpl = [.call 143, .ret] := by
  rfl

/-- Exact body prefix of the raw-read forwarder, ending at the `Stdin` read
implementation call. -/
theorem rawReadForward_body_to_impl_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst env pointer length : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [],
          [.i32 length, .i32 pointer, .i32 env, .i32 dst]⟩,
        rawReadForwardAtImpl, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [], []⟩,
        func27, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  rw [func27_eq_implPrefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iexact Hcont

/-- Composable entry rule for the raw-read forwarder at absolute index 29,
stopping at the inner absolute call 143 inside the freshly pushed callee
frame. -/
theorem rawReadForward_call_to_impl_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst env pointer length : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [],
              [.i32 length, .i32 pointer, .i32 env, .i32 dst]⟩,
            rawReadForwardAtImpl, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 length, .i32 pointer, .i32 env, .i32 dst] ++ stack },
        .call 29 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 29 func27Def
      (by decide) rawReadForward_index $$ Hruntime
  iintro Hruntime
  simp [func27Def, Function.toLocals, Function.numParams]
  have Hbody := rawReadForward_body_to_impl_twp (α := α)
    dst env pointer length (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-! ## `Stdin` read implementation (`func141`, absolute call 143)

The generated body calls the `stdio.read` wrapper at absolute call 135 with
`(pointer, length)`, stores the returned byte count at `dst + 4`, and tags the
result `Ok` by writing discriminant byte `4` at `dst` — the same discriminant
the driver checks in `driver_read_check_success_twp`. -/

def rawReadAtWrapper : Program := func141.drop 3
def rawReadAfterWrapper : Program := func141.drop 4

theorem func141_eq_wrapperPrefix :
    func141 = [.localGet 0, .localGet 2, .localGet 3] ++ rawReadAtWrapper := by
  rfl

theorem rawReadAtWrapper_eq :
    rawReadAtWrapper = .call 135 :: rawReadAfterWrapper := by
  rfl

theorem rawReadAfterWrapper_eq :
    rawReadAfterWrapper =
      [.store32 4, .localGet 0, .const 4, .store8 0, .ret] := by
  rfl

/-- Exact body prefix of the `Stdin` read implementation, ending at the
`stdio.read` wrapper call with `(pointer, length)` prepared and `dst` kept
below them on the stack. -/
theorem rawRead_body_to_wrapper_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst env pointer length : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [],
          [.i32 length, .i32 pointer, .i32 dst]⟩,
        rawReadAtWrapper, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [], []⟩,
        func141, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  rw [func141_eq_wrapperPrefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iexact Hcont

/-- Exact epilogue of the `Stdin` read implementation: once the `stdio.read`
wrapper has returned the copied byte count, store it at `dst + 4` and tag the
result with the `Ok` discriminant byte `4` at `dst`. -/
theorem rawRead_epilogue_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst env pointer length copied : UInt32)
    (old4 : UInt32) (oldTag : UInt8)
    (hdstRoom : dst.toNat + 8 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u32 (dst + 4) old4 ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (dst + 0) (DFrac.own 1) (some oldTag) ∗
      (pointsTo_u32 (dst + 4) copied -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (dst + 0) (DFrac.own 1) (some (4 : UInt8)) -∗
        WP (.running
          ⟨⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [],
          [.i32 copied, .i32 dst]⟩,
        rawReadAfterWrapper, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h40, h41, h42, h43⟩ :=
    descriptorSlot32Facts dst 4 8 hdstRoom (by decide)
  have h00 : (dst + (0 : UInt32)).toNat = dst.toNat + (0 : UInt32).toNat := by
    simp
  iintro ⟨H4, Htag, Hcont⟩
  rw [rawReadAfterWrapper_eq]
  iapply twp_store32 old4 h40 h41 h42 h43 $$ H4
  iintro H4
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store8_owned oldTag h00 $$ Htag
  iintro Htag
  rw [show ((4 : UInt32).toUInt8) = (4 : UInt8) from rfl]
  iapply Hcont $$ H4 Htag

/-- Composable entry rule for the `Stdin` read implementation at absolute
index 143, stopping at the `stdio.read` wrapper boundary inside the freshly
pushed callee frame. -/
theorem rawRead_call_to_wrapper_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst env pointer length : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [],
              [.i32 length, .i32 pointer, .i32 dst]⟩,
            rawReadAtWrapper, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 length, .i32 pointer, .i32 env, .i32 dst] ++ stack },
        .call 143 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 143 func141Def
      (by decide) rawRead_index $$ Hruntime
  iintro Hruntime
  simp [func141Def, Function.toLocals, Function.numParams]
  have Hbody := rawRead_body_to_wrapper_twp (α := α)
    dst env pointer length (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-! ## `stdio.read` wrapper boundary (`func133`, absolute call 135) -/

def stdioReadAtImport : Program := func133.drop 2

theorem stdioReadAtImport_eq :
    stdioReadAtImport = [.call 0, .ret] := by
  rfl

/-- Composable entry rule for the `stdio.read` wrapper at absolute index 135,
stopping exactly at the imported host call inside the freshly pushed callee
frame.  This is the call-shaped form of `stdioReadWrapper_to_import_twp`. -/
theorem stdioRead_call_to_import_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (pointer length : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 pointer, .i32 length], [], [.i32 length, .i32 pointer]⟩,
            stdioReadAtImport, 1, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 length, .i32 pointer] ++ stack },
        .call 135 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 135 func133Def
      (by decide) stdioReadWrapper_index $$ Hruntime
  iintro Hruntime
  simp [func133Def, Function.toLocals, Function.numParams]
  have Hbody := stdioReadWrapper_to_import_twp (α := α)
    pointer length (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  rw [show func133.drop 2 = stdioReadAtImport from rfl]
  iapply Hcont $$ Hruntime

/-! ## Composed proven stretches

The two ends of the buffered read chain are now connected as far as the
generated code goes without entering the `BufReader` refill internals
(`func38`, absolute call 40) or the vector-append/allocator path:

* from the driver-side `.call 24` down to the first `fill_buf` boundary
  inside the `read_until` loop, three call frames deep;
* from the refill-side `.call 143` down to the `stdio.read` host import
  boundary, two call frames deep. -/

/-- Suspended `read_line` frame as it sits below the `read_until` call. -/
def lineReadCallFrame (result line reader stackTop lineLen : UInt32) :
    CallFrame :=
  { locals :=
      ⟨[.i32 result, .i32 line, .i32 reader],
        [.i32 (stackTop - 32), .i32 lineLen, .i32 0, .i32 0, .i32 0,
         .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩
    continuation := lineReadAfterReadUntil
    resultArity := 0
    callerRemainder := []
    control := [] }

/-- Suspended `read_until` shim frame as it sits below the loop call. -/
def readUntilShimCallFrame (result reader line : UInt32) : CallFrame :=
  { locals := ⟨[.i32 result, .i32 reader, .i32 line], [], []⟩
    continuation := [.ret]
    resultArity := 0
    callerRemainder := []
    control := [] }

/-- Proven stretch from the driver-side `.call 24` down to the exact first
`fill_buf` call (absolute 18) inside the `read_until` loop.  The delimiter is
the concrete newline byte `10` fixed by the shim, and all three suspended
frames on the way down are explicit. -/
theorem lineRead_call_to_fillBuf_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (result line reader stackTop : UInt32)
    (lineLen old4 old8 old16 : UInt32)
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    (hlineRoom : line.toNat + 12 ≤ UInt32.size)
    (hloopFrameRoom : ((stackTop - 32) - 96).toNat + 96 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (line + 8) lineLen ∗
      pointsTo_u32 ((stackTop - 32) + 4) old4 ∗
      pointsTo_u32 ((stackTop - 32) + 8) old8 ∗
      pointsTo_u32 (((stackTop - 32) - 96) + 16) old16 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 ((stackTop - 32) - 96)) -∗
        pointsTo_u32 (line + 8) lineLen -∗
        pointsTo_u32 ((stackTop - 32) + 4) line -∗
        pointsTo_u32 ((stackTop - 32) + 8) lineLen -∗
        pointsTo_u32 (((stackTop - 32) - 96) + 16) 0 -∗
        WP (.running
          ⟨⟨[.i32 result, .i32 reader, .i32 10, .i32 line],
              [.i32 ((stackTop - 32) - 96), .i32 0, .i32 0, .i32 0, .i32 0,
               .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
               .i32 0],
              [.i32 reader, .i32 (20 + ((stackTop - 32) - 96))]⟩,
            readUntilAtFillBuf, 0, [],
            [readUntilLoopFrame, readUntilBlockFrame],
            readUntilShimCallFrame result reader line ::
              lineReadCallFrame result line reader stackTop lineLen ::
              { locals := { callerLocals with values := stack }
                continuation := code
                resultArity := arity
                callerRemainder := remainder
                control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 reader, .i32 line, .i32 result] ++ stack },
        .call 24 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hlen, H4, H8, H16, Hcont⟩
  have Hstep1 := lineRead_call_to_readUntil_twp (α := α)
    result line reader stackTop lineLen old4 old8 hframeRoom hlineRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals := callerLocals) (stack := stack) (code := code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls)
  iapply Hstep1
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hlen]
  · iexact Hlen
  isplitl [H4]
  · iexact H4
  isplitl [H8]
  · iexact H8
  iintro Hruntime Hglobal Hlen H4 H8
  rw [lineReadAtReadUntil_eq]
  have Hstep2 := readUntilShim_call_to_loop_twp (α := α)
    result reader line (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[.i32 result, .i32 line, .i32 reader],
        [.i32 (stackTop - 32), .i32 lineLen, .i32 0, .i32 0, .i32 0,
         .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩)
    (stack := []) (code := lineReadAfterReadUntil) (arity := 0)
    (remainder := []) (controls := [])
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [List.append_nil] at Hstep2
  iapply Hstep2
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  rw [readUntilShimAtLoop_eq]
  have Hstep3 := readUntilLoop_call_to_fillBuf_twp (α := α)
    result reader 10 line (stackTop - 32) old16 hloopFrameRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals := ⟨[.i32 result, .i32 reader, .i32 line], [], []⟩)
    (stack := []) (code := [.ret]) (arity := 0)
    (remainder := []) (controls := [])
    (calls :=
      lineReadCallFrame result line reader stackTop lineLen ::
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls } :: calls)
  simp only [List.append_nil] at Hstep3
  rw [show CallFrame.mk
        ⟨[.i32 result, .i32 line, .i32 reader],
          [.i32 (stackTop - 32), .i32 lineLen, .i32 0, .i32 0, .i32 0,
           .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩
        lineReadAfterReadUntil 0 [] [] =
      lineReadCallFrame result line reader stackTop lineLen from rfl]
  iapply Hstep3
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [H16]
  · iexact H16
  iintro Hruntime Hglobal H16
  rw [show CallFrame.mk
        ⟨[.i32 result, .i32 reader, .i32 line], [], []⟩
        [.ret] 0 [] [] =
      readUntilShimCallFrame result reader line from rfl]
  iapply Hcont $$ Hruntime Hglobal Hlen H4 H8 H16

/-- Suspended `Stdin` read frame as it sits below the `stdio.read` wrapper
call. -/
def rawReadCallFrame (dst env pointer length : UInt32) : CallFrame :=
  { locals :=
      ⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [], [.i32 dst]⟩
    continuation := rawReadAfterWrapper
    resultArity := 0
    callerRemainder := []
    control := [] }

/-- Proven stretch from the refill-side `.call 143` down to the exact
imported `stdio.read` call, with both suspended frames explicit.  Together
with `rawRead_epilogue_twp` this pins the whole `Stdin::read` implementation
to the host boundary: the only unproven step left between them is the host
import itself. -/
theorem rawRead_call_to_import_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst env pointer length : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 pointer, .i32 length], [], [.i32 length, .i32 pointer]⟩,
            stdioReadAtImport, 1, [], [],
            rawReadCallFrame dst env pointer length ::
              { locals := { callerLocals with values := stack }
                continuation := code
                resultArity := arity
                callerRemainder := remainder
                control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 length, .i32 pointer, .i32 env, .i32 dst] ++ stack },
        .call 143 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  have Hstep1 := rawRead_call_to_wrapper_twp (α := α)
    dst env pointer length (s := s) (E := E) (Φ := Φ)
    (callerLocals := callerLocals) (stack := stack) (code := code)
    (arity := arity) (remainder := remainder) (controls := controls)
    (calls := calls)
  iapply Hstep1
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  rw [rawReadAtWrapper_eq]
  have Hstep2 := stdioRead_call_to_import_twp (α := α)
    pointer length (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [], []⟩)
    (stack := [.i32 dst]) (code := rawReadAfterWrapper) (arity := 0)
    (remainder := []) (controls := [])
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [List.cons_append, List.nil_append] at Hstep2
  iapply Hstep2
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  rw [show CallFrame.mk
        ⟨[.i32 dst, .i32 env, .i32 pointer, .i32 length], [], [.i32 dst]⟩
        rawReadAfterWrapper 0 [] [] =
      rawReadCallFrame dst env pointer length from rfl]
  iapply Hcont $$ Hruntime

end Project.Mergesort.ReadChainProof
