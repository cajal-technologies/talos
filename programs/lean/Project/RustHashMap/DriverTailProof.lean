import Project.RustHashMap.DriverTail
import Project.RustHashMap.Func55Proof
import Project.RustHashMap.Func30Proof
import Project.RustHashMap.ImportProofs

/-!
# The tail of the `map_len` driver: the proof

`Project.RustHashMap.DriverTail.DriverTailSpec` is the contract of
everything after the read loop.  This module proves it from the three call
contracts that the tail depends on.

The proof follows the block structure of
`Project.RustHashMap.DriverTail`, one lemma per control block, from the
innermost outward.  Every lemma names its control frames, because
`branchTarget?` reads them.

## The three frames

`outerFrame` is the block that every path leaves.  Its continuation is the
stack epilogue, so a `br` to it restores the stack pointer and returns.
`okFrame` is the block that the decoder `Err` path leaves; its continuation
is the error epilogue.  `replyFrame` is the block that the reply leaves
when the allocator returns zero; the allocator never does, so its
continuation is dead code.

## Why the table drop needs no reasoning

Both branches of each guard in `replyBody` reach `outerFrame`.  The
addresses that the drop computes are unsigned and wrap, and the free goes
through `Project.RustHashMap.DeallocNoop.Func57NoopSpec`, whose body is
empty.  So the drop needs neither a bound on the bucket count nor a token
for the block.
-/

namespace Project.RustHashMap.DriverTailProof

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.DeallocNoop
open Project.RustHashMap.Func55Proof
open Project.RustHashMap.Func30Proof
open Project.RustHashMap.ImportProofs
open Project.RustHashMap.DriverTail
open Project.RustHashMap.ReadAll
open scoped Wasm.SmallStep.Outcome

/-! ## The control frames of the tail -/

/-- The outermost block of the tail.  Its continuation is the stack
epilogue, so every path that leaves it returns. -/
def outerFrame (afterTail : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := outerBody, continuation := stackEpilogue ++ afterTail,
    belowStack := [] }

theorem outerFrame_literal (afterTail : Program) :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := outerBody, continuation := stackEpilogue ++ afterTail,
       belowStack := [] } : ControlFrame) = outerFrame afterTail := rfl

/-- The block that the decoder `Err` path leaves.  Its continuation is the
error epilogue. -/
def okFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := okBlock, continuation := errEpilogue, belowStack := [] }

theorem okFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := okBlock, continuation := errEpilogue,
       belowStack := [] } : ControlFrame) = okFrame := rfl

/-- The capacity read and the outer block, which is what follows the call
of the decoder. -/
def afterDecode (afterTail : Program) : Program :=
  .localGet 0 :: .load32 292 :: .localSet 4 ::
    .block 0 0 outerBody :: (stackEpilogue ++ afterTail)

/-- The tail of the driver in cons form, with the decoder call exposed. -/
theorem func19AfterRead_cons (afterTail : Program) :
    ReadAll.func19AfterRead ++ afterTail =
      .localGet 0 :: .localGet 1 :: .store32 284 :: .localGet 0 ::
        .localGet 3 :: .store32 280 :: .localGet 0 :: .const 288 :: .add ::
        .localGet 0 :: .const 280 :: .add :: .call 4 ::
        afterDecode afterTail := rfl

/-- The block that the reply leaves when the allocator returns zero.  The
allocator never returns zero, so the continuation is dead. -/
def replyFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := replyBody,
    continuation := [.const 1, .const 1024, .call 99, .unreachable],
    belowStack := [] }

/-- The block entry step builds the reply frame as a literal.  This folds
it back. -/
theorem replyFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := replyBody,
       continuation := [.const 1, .const 1024, .call 99, .unreachable],
       belowStack := [] } : ControlFrame) = replyFrame := rfl

/-! ## The steps of the reply

The reply block runs five calls in a row.  Each call needs the code that
follows it as an explicit argument, so each suffix gets a name. -/

/-- The drop of the hash table, which ends the reply. -/
def tableDrop : Program :=
  [.localGet 0, .load32 28, .localTee 1, .eqz, .br_if 2, .localGet 1,
    .const 3, .shl, .localTee 3, .localGet 1, .add, .const 17, .add,
    .localTee 1, .eqz, .br_if 2, .localGet 0, .load32 24, .localGet 3,
    .sub, .const 4294967288, .add, .localGet 1, .const 8, .call 60, .br 2]

/-- The free of the reply buffer, and the table drop after it. -/
def replyFree : Program :=
  .localGet 1 :: .const 1024 :: .const 1 :: .call 60 :: tableDrop

/-- The write of the four count bytes to the output stream. -/
def replyWrite : Program :=
  .localGet 1 :: .const 4 :: .call 64 :: replyFree

/-- The store of the count in the first four bytes of the buffer. -/
def replyStore : Program :=
  .localGet 1 :: .localGet 3 :: .store32 0 :: replyWrite

/-- The null check of the allocation result. -/
def replyAfterAlloc : Program :=
  .localTee 1 :: .eqz :: .br_if 0 :: replyStore

theorem replyBody_shape :
    replyBody = .const 1024 :: .const 1 :: .call 58 :: replyAfterAlloc := rfl

/-- The item count read, the marker call and the reply block. -/
def collectTail : Program :=
  [.localGet 0, .load32 36, .localSet 3, .call 33, .block 0 0 replyBody,
    .const 1, .const 1024, .call 99, .unreachable]

theorem collectAndReply_shape :
    collectAndReply = .localGet 0 :: .const 24 :: .add :: .localGet 0 ::
      .const 12 :: .add :: .call 5 :: collectTail := rfl

/-- The block that releases the input byte vector before the collect
call. -/
def freeInputFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := freeInput, continuation := collectAndReply, belowStack := [] }

theorem freeInputFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := freeInput, continuation := collectAndReply,
       belowStack := [] } : ControlFrame) = freeInputFrame := rfl

/-- The store of the decoded vector header, the release of the input
bytes, and the collect call. -/
def okReply : Program :=
  .localGet 0 :: .localGet 7 :: .store32 20 :: .localGet 0 :: .localGet 8 ::
    .store32 16 :: .localGet 0 :: .localGet 5 :: .store32 12 ::
    .block 0 0 freeInput :: collectAndReply

theorem okPath_shape :
    okPath = .localGet 0 :: .load32 296 :: .localSet 6 ::
      .block 0 0 decodeOutcome :: okReply := rfl

/-- The block that the decoder guard leaves when the decode succeeded.  Its
continuation is the accepting path. -/
def okGuardFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := okGuard, continuation := okPath, belowStack := [] }

theorem okGuardFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := okGuard, continuation := okPath,
       belowStack := [] } : ControlFrame) = okGuardFrame := rfl

/-! ## The steps of the decode outcome -/

/-- The fall-through of the decode outcome.  It moves the decoded length,
the capacity and the buffer into the reply registers. -/
def decodeTail : Program :=
  [.localGet 0, .load32 300, .localSet 7, .localGet 4, .localSet 5,
    .localGet 6, .localSet 8]

theorem decodeOutcome_shape :
    decodeOutcome = .block 0 0 notAllReadBody :: decodeTail := rfl

/-- The block that chooses between the "not all bytes read" error and the
decoded vector.  Its continuation is the reply. -/
def decodeFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := decodeOutcome, continuation := okReply, belowStack := [] }

theorem decodeFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := decodeOutcome, continuation := okReply,
       belowStack := [] } : ControlFrame) = decodeFrame := rfl

/-- The branch that ends the "not all bytes read" path.  The error word is
never the success tag, so the branch is always taken and the `br 1` after
it is dead. -/
def notAllReadTail : Program :=
  [.localGet 1, .const 2147483649, .ne, .br_if 2, .br 1]

/-- The four error words, the drop of the decoded pair buffer, and the
branch into the error epilogue. -/
def notAllReadRead : Program :=
  .localGet 0 :: .load32 36 :: .localSet 7 :: .localGet 0 :: .load32 32 ::
    .localSet 8 :: .localGet 0 :: .load32 28 :: .localSet 5 ::
    .localGet 0 :: .load32 24 :: .localSet 1 ::
    .block 0 0 dropDecoded :: notAllReadTail

/-- The error path of the "not all bytes read" branch.  It builds the
`io::Error` in the map slot. -/
def notAllReadError : Program :=
  .localGet 0 :: .const 24 :: .add :: .const 12 :: .const 1049107 ::
    .const 18 :: .call 55 :: notAllReadRead

theorem notAllReadBody_shape :
    notAllReadBody =
      .localGet 0 :: .load32 284 :: .eqz :: .br_if 0 :: notAllReadError := rfl

/-- The block that the test leaves when the decoder read every byte.  Its
continuation is the fall-through of the decode outcome. -/
def notAllReadFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := notAllReadBody, continuation := decodeTail, belowStack := [] }

theorem notAllReadFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := notAllReadBody, continuation := decodeTail,
       belowStack := [] } : ControlFrame) = notAllReadFrame := rfl

/-- The block that drops the decoded pair buffer on the error path. -/
def dropDecodedFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := dropDecoded, continuation := notAllReadTail, belowStack := [] }

theorem dropDecodedFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := dropDecoded, continuation := notAllReadTail,
       belowStack := [] } : ControlFrame) = dropDecodedFrame := rfl

/-- What every path of the tail proves once the stack pointer is back.  The
locals differ per path, so the caller supplies them.  `finalOutput` is the
output stream that the path leaves; the error paths write nothing, and the
reply path writes the entry count. -/
def TailDone [WasmSmallStepGS hlc Universal.State]
    (finalOutput : List UInt8)
    (afterTail : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ finalLocals : Locals,
    RuntimeContext -∗
    StackPointer entryStackTop -∗
    Streams [] finalOutput false -∗
    WP (.running ⟨finalLocals, afterTail, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }])

/-! ## The stack epilogue -/

/-- The stack pointer restore that ends every path. -/
theorem twp_stack_epilogue [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 l6 l7 l8 : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩,
            stackEpilogue ++ afterTail, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  isimp only [StackPointer] at Hsp
  isimp only [TailDone] at Hcont
  simp only [stackEpilogue, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (304 : UInt32) + func19Base = entryStackTop by decide]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer entryStackTop $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iapply Hcont $$ %(⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3,
    .i32 l4, .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩ : Locals)
    Hruntime Hsp Hstreams

/-! ## The error epilogue -/

/-- The free of the input byte vector.  Both error paths reach it, and it
runs just before the stack epilogue. -/
theorem twp_free_input [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 l6 l7 l8 : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩,
            [.localGet 2, .eqz, .br_if 0, .localGet 3, .localGet 2, .const 1,
              .call 60],
            arity, remainder, outerFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  by_cases hcapacity : l2 = 0
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by simp [hcapacity])
    iapply twp_brIf (by decide) (by rfl)
    simp only [outerFrame, List.take_zero, List.nil_append]
    iapply twp_stack_epilogue
    iframe
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by simp [hcapacity])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l3 l2 1
      (callerLocals :=
        ⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
          .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls := outerFrame afterTail :: controls) (calls := calls)
      (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [outerFrame, List.take_zero, List.nil_append]
      iapply twp_stack_epilogue
      iframe

/-- The error epilogue.  It drops the error string, frees the input byte
vector and restores the stack pointer. -/
theorem twp_err_epilogue [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 l6 l7 l8 : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩,
            errEpilogue, arity, remainder,
            outerFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  simp only [errEpilogue]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero, freeErrString]
  wasm_twp_pures [twp_localGet twp_const twp_or twp_const]
  by_cases hstring : (l1 ||| (2147483648 : UInt32)) = 2147483648
  · iapply twp_eq (result := 1) (by simp [hstring])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    iapply twp_free_input
    iframe
  · iapply twp_eq (result := 0) (by simp [hstring])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l5 l1 1
      (callerLocals :=
        ⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
          .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        { kind := .block, paramArity := 0, resultArity := 0,
          body := [.localGet 1, .const 2147483648, .or, .const 2147483648,
            .eq, .br_if 0, .localGet 5, .localGet 1, .const 1, .call 60],
          continuation := [.localGet 2, .eqz, .br_if 0, .localGet 3,
            .localGet 2, .const 1, .call 60],
          belowStack := [] } :: outerFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [List.take_zero, List.nil_append]
      iapply twp_free_input
      iframe

/-! ## The table drop -/

/-- The drop of the hash table, which is the last step of the reply.  Both
arms of both guards reach `outerFrame`, so neither guard has to be
decided.  The free goes through the empty body of absolute `func 60`, so
the drop needs no token for the block.  The addresses that it computes are
unsigned and wrap, so they need no bound either. -/
theorem twp_table_drop [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 l6 l7 l8 ctrl mask : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      Streams [] finalOutput false ∗
      pointsTo_u32 0 (func19Base + 24) ctrl ∗
      pointsTo_u32 0 (func19Base + 28) mask ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩,
            tableDrop, arity, remainder,
            replyFrame :: okFrame :: outerFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hctrl, Hmask, Hcont⟩
  simp only [tableDrop]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func19Base) (offset := 28) mask
    (by decide) (by decide) (by decide) (by decide) with Hmask
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  by_cases hmask : mask = 0
  · iapply twp_eqz (result := 1) (by simp [hmask])
    iapply twp_brIf (by decide) (by rfl)
    simp only [outerFrame, List.take_zero, List.nil_append]
    iapply twp_stack_epilogue
    iframe
  · iapply twp_eqz (result := 0) (by simp [hmask])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_const twp_shl]
      rewriting [show (3 : UInt32) % 32 = 3 by decide]
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet twp_add twp_const twp_add]
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    by_cases hsize : (17 : UInt32) + (mask + mask <<< 3) = 0
    · iapply twp_eqz (result := 1) (by simp [hsize])
      iapply twp_brIf (by decide) (by rfl)
      simp only [outerFrame, List.take_zero, List.nil_append]
      iapply twp_stack_epilogue
      iframe
    · iapply twp_eqz (result := 0) (by simp [hsize])
      wasm_twp_pures [twp_brIfZero twp_localGet]
      wasm_twp_rebind twp_load32 (address := func19Base) (offset := 24) ctrl
        (by decide) (by decide) (by decide) (by decide) with Hctrl
      wasm_twp_pures [twp_localGet twp_sub twp_const twp_add twp_localGet
        twp_const]
      have Hfree := func57_noop_correct (hlc := hlc)
        ((4294967288 : UInt32) + (ctrl - mask <<< 3))
        ((17 : UInt32) + (mask + mask <<< 3)) 8
        (callerLocals :=
          ⟨[], [Value.i32 func19Base, .i32 ((17 : UInt32) + (mask + mask <<< 3)),
            .i32 l2, .i32 (mask <<< 3), .i32 l4, .i32 l5, .i32 l6, .i32 l7,
            .i32 l8], []⟩)
        (stack := []) (code := [.br 2]) (arity := arity)
        (remainder := remainder)
        (controls :=
          replyFrame :: okFrame :: outerFrame afterTail :: controls)
        (calls := calls) (s := s) (E := E) (Φ := Φ)
      unfold CallContract callExpr at Hfree
      simp only [List.cons_append, List.nil_append] at Hfree
      iapply Hfree
      isplitl_exact Hruntime
      · iintro Hruntime
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        iapply twp_br (by rfl)
        simp only [outerFrame, List.take_zero, List.nil_append]
        iapply twp_stack_epilogue
        iframe

/-! ## The header words of the table -/

/-- A table owns its four header words.  The driver reads three of them:
the control pointer at offset 0, the bucket mask at offset 4 and the item
count at offset 12.  The values of the first two do not matter, because
both arms of both guards of the drop reach the same block. -/
theorem TableAt_header_words [WasmHeapGS Universal.State]
    (base : UInt32) (t : HashMap.Table UInt32 UInt32) :
    HashMap.Table.TableAt (α := Universal.State) 0 base t ⊢
      iprop(∃ ctrl : UInt32, ∃ mask : UInt32,
        pointsTo_u32 0 base ctrl ∗ pointsTo_u32 0 (base + 4) mask ∗
        pointsTo_u32 0 (base + 12) (UInt32.ofNat t.items)) := by
  iintro Htable
  isimp only [HashMap.Table.TableAt] at Htable
  icases Htable with ⟨%ctrl, Hbody⟩
  icases Hbody with (Hsingleton | ⟨%_hbuckets, Hallocated⟩)
  · isimp only [HashMap.Table.SingletonBody, HashMap.Table.tableHeader]
      at Hsingleton
    icases Hsingleton with ⟨%hfacts, ⟨H0, H4, H8, H12⟩, Hctrl⟩
    iexists ctrl, (0 : UInt32)
    isplitl_exacts [H0 H4]
    irw_exact [show UInt32.ofNat t.items = 0 by rw [hfacts.2.1]; rfl] with H12
  · isimp only [HashMap.Table.TableBody, HashMap.Table.tableHeader]
      at Hallocated
    icases Hallocated with ⟨%_hctrlBound, ⟨H0, H4, H8, H12⟩, Hbytes, Hslots⟩
    iexists ctrl, (UInt32.ofNat (t.buckets - 1))
    isplitl_exacts [H0 H4]
    iexact H12

/-- The same three words of a map value. -/
theorem MapAt_header_words [WasmHeapGS Universal.State]
    (base : UInt32) (k0 k1 : UInt64)
    (entries : HashMap.Map UInt32 UInt32) :
    HashMap.Table.MapAt (α := Universal.State) 0 base k0 k1 entries ⊢
      iprop(∃ ctrl : UInt32, ∃ mask : UInt32,
        pointsTo_u32 0 base ctrl ∗ pointsTo_u32 0 (base + 4) mask ∗
        pointsTo_u32 0 (base + 12)
          (UInt32.ofNat
            (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
              entries).items)) := by
  iintro Hmap
  isimp only [HashMap.Table.MapAt, HashMap.Table.HashMapAt] at Hmap
  icases Hmap with ⟨Htable, Hk0, Hk1⟩
  iapply TableAt_header_words
  iexact Htable

/-! ## The reply -/

/-- The reply block.  It allocates 1024 bytes with alignment 1, stores the
entry count in the first four of them, writes those four bytes to the
output stream, frees the buffer and drops the table.  The null check after
the allocation is dead, because a live block never starts at address
zero. -/
theorem twp_reply [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 count l4 l5 l6 l7 l8 ctrl mask : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      pointsTo_u32 0 (func19Base + 24) ctrl ∗
      pointsTo_u32 0 (func19Base + 28) mask ∗
      TailDone (output ++ Borsh.u32 count) afterTail arity remainder
        controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 count, .i32 l4,
              .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩,
            replyBody, arity, remainder,
            replyFrame :: okFrame :: outerFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbump, Hstreams, Hctrl, Hmask, Hcont, Hoom⟩
  simp only [replyBody_shape]
  wasm_twp_pures [twp_const twp_const]
  have Halloc := func55_correct (hlc := hlc) 1024 1
    { size := 1024, alignment := 1 } heapId storedCursor frontier history
    [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 count, .i32 l4,
        .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩)
    (stack := []) (code := replyAfterAlloc) (arity := arity)
    (remainder := remainder)
    (controls := replyFrame :: okFrame :: outerFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Halloc
  simp only [List.cons_append, List.nil_append] at Halloc
  iapply Halloc
  isplitl_exacts [Hruntime Hbump Hstreams]
  have hmatches : AllocLayout.Matches { size := 1024, alignment := 1 } 1024 1 :=
    ⟨by decide, by decide⟩
  have hvalid : AllocLayout.Valid { size := 1024, alignment := 1 } :=
    ⟨by decide, by decide, ⟨0, rfl⟩, by decide, by decide, by decide, by decide⟩
  isplitl_pureexact ⟨hmatches, hvalid, Or.inl trivial⟩
  cases hdecision : classifyBump frontier { size := 1024, alignment := 1 } with
  | oom =>
      isimp only [AllocContinuation, hdecision]
      iintro Hbump Hstreams
      iapply Hoom
      isimp only [ExportOOM]
      iexists ([] : List UInt8), output
      iexact Hstreams
  | success base finish =>
      isimp only [AllocContinuation, hdecision]
      isplit
      · iintro %bytes Hruntime Hbump Hblock Hstreams
        isimp only [ResumeWP, resumeExpr, List.nil_append, List.append_nil]
        iunfold LiveBlock at Hblock
        icases Hblock with ⟨Htoken, Hbytes, %hfacts⟩
        obtain ⟨hlength, hnonnull, _⟩ := hfacts
        have hbytes : bytes.length = 1024 := hlength
        obtain ⟨_, _, _, hbound, _, _⟩ :=
          classifyBump_success_align1 frontier 1024 base finish hdecision
        have hnowrap : base.toNat + 4 < UInt32.size := by omega
        have h0_1 : (base + 1).toNat = base.toNat + 1 := by
          simpa using Slices.byteOffset_toNat base 1 (by omega)
        have h0_2 : (base + 2).toNat = base.toNat + 2 := by
          simpa using Slices.byteOffset_toNat base 2 (by omega)
        have h0_3 : (base + 3).toNat = base.toNat + 3 := by
          simpa using Slices.byteOffset_toNat base 3 (by omega)
        simp only [replyAfterAlloc]
        wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        iapply twp_eqz (result := 0) (by simp [hnonnull])
        wasm_twp_pures [twp_brIfZero]
        simp only [replyStore]
        wasm_twp_pures [twp_localGet twp_localGet]
        have hsplit : bytes.take 4 ++ bytes.drop 4 = bytes :=
          List.take_append_drop 4 bytes
        have htake : (bytes.take 4).length = 4 := by simp [hbytes]
        ihave ⟨Hhead, Hrest⟩ := (Slices.ByteSlice_append 0 base
          (bytes.take 4) (bytes.drop 4)).mp $$ [Hbytes]
        · irw_exact [hsplit] with Hbytes
        ihave ⟨Hword, Hclose⟩ := Slices.ByteSlice_storeWordFocus 0 base
          (bytes.take 4) count htake hnowrap $$ Hhead
        ihave Hword' : pointsTo_u32 0 (base + 0)
            (WordCodec.decodeU32 (bytes.take 4)) $$ [Hword]
        · irw_exact [show base + 0 = base by simp] with Hword
        iapply twp_store32 (address := base) (offset := 0)
          (WordCodec.decodeU32 (bytes.take 4)) (by simp)
          (by simpa using h0_1) (by simpa using h0_2)
          (by simpa using h0_3) $$ Hword'
        iintro Hword
        isimp only [UInt32.add_zero] at Hword
        ihave Hslice := Hclose $$ Hword
        simp only [replyWrite]
        wasm_twp_pures [twp_localGet twp_const]
        have Hwrite := func61_correct (hlc := hlc) base 4
          (WordCodec.u32le.serialize [count]) [] output false
          (callerLocals :=
            ⟨[], [Value.i32 func19Base, .i32 base, .i32 l2, .i32 count,
              .i32 l4, .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩)
          (stack := []) (code := replyFree) (arity := arity)
          (remainder := remainder)
          (controls :=
            replyFrame :: okFrame :: outerFrame afterTail :: controls)
          (calls := calls) (s := s) (E := E) (Φ := Φ)
        unfold CallContract callExpr at Hwrite
        simp only [List.cons_append, List.nil_append] at Hwrite
        iapply Hwrite
        isplitl_exacts [Hruntime Hstreams Hslice]
        isplitl_pureexact ⟨by simp, by decide⟩
        iintro Hruntime Hstreams Hslice
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        simp only [replyFree]
        wasm_twp_pures [twp_localGet twp_const twp_const]
        have Hfree := func57_noop_correct (hlc := hlc) base 1024 1
          (callerLocals :=
            ⟨[], [Value.i32 func19Base, .i32 base, .i32 l2, .i32 count,
              .i32 l4, .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩)
          (stack := []) (code := tableDrop) (arity := arity)
          (remainder := remainder)
          (controls :=
            replyFrame :: okFrame :: outerFrame afterTail :: controls)
          (calls := calls) (s := s) (E := E) (Φ := Φ)
        unfold CallContract callExpr at Hfree
        simp only [List.cons_append, List.nil_append] at Hfree
        iapply Hfree
        isplitl_exact Hruntime
        · iintro Hruntime
          isimp only [ResumeWP, resumeExpr, List.nil_append]
          ihave Hstreams : Streams [] (output ++ Borsh.u32 count) false $$
              [Hstreams]
          · irw_exact [show WordCodec.u32le.serialize [count]
              = Borsh.u32 count by simp [Borsh.u32]] with Hstreams
          iapply twp_table_drop
          iframe
      · iintro Hbump Hstreams
        iapply Hoom
        isimp only [ExportOOM]
        iexists ([] : List UInt8), output
        iexact Hstreams

/-! ## The collect call and the reply -/

/-- The tail of the accepting path: `collect_entries`, the marker call and
the reply block.  The entry count that the reply writes is the one the
collect contract equates with `HashMap.len`, which is the count that
`Project.RustHashMap.Spec.lenOutput` names. -/
theorem twp_collect_reply [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : Func2Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len : UInt32)
    (entries : HashMap.Map UInt32 UInt32)
    (payload spare mapBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l1 l2 l3 l4 l5 l6 l7 l8 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hmapBefore : mapBefore.length = 32)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload = entryCodec.serialize entries)
    (hentries : entries.length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat)) :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      StackBelow func19Base collectDepth below ∗
      Slices.ByteSlice 0 (func19Base + 24) mapBefore ∗
      pointsTo_u32 0 (func19Base + 12) cap ∗
      pointsTo_u32 0 (func19Base + 16) bufPtr ∗
      pointsTo_u32 0 (func19Base + 20) len ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.u32
          (UInt32.ofNat (HashMap.len (HashMap.ofEntries entries))))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩,
            collectAndReply, arity, remainder,
            okFrame :: outerFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hmap, Hcap, Hptr, Hlen, Hbuf, Hkeys, Hbump,
    Hstreams, Hcont, Hoom⟩
  ihave Hptr : pointsTo_u32 0 (func19Base + 12 + 4) bufPtr $$ [Hptr]
  · irw_exact [show func19Base + 12 + 4 = func19Base + 16 by decide] with Hptr
  ihave Hlen : pointsTo_u32 0 (func19Base + 12 + 8) len $$ [Hlen]
  · irw_exact [show func19Base + 12 + 8 = func19Base + 20 by decide] with Hlen
  simp only [collectAndReply_shape]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add]
    rewriting [show (24 : UInt32) + func19Base = func19Base + 24 by decide,
      show (12 : UInt32) + func19Base = func19Base + 12 by decide]
  have Hcollect := hfunc2 func19Base (func19Base + 24) (func19Base + 12)
    cap bufPtr len heapId entries payload spare mapBefore keysBefore below
    storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
        .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩)
    (stack := []) (code := collectTail) (arity := arity)
    (remainder := remainder)
    (controls := okFrame :: outerFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hcollect
  simp only [List.cons_append, List.nil_append] at Hcollect
  iapply Hcollect
  isplitl_exacts [Hruntime Hsp Hbelow Hmap Hcap Hptr Hlen Hbuf Hkeys Hbump
    Hstreams]
  isplitl_pureexact ⟨hmapBefore, hkeys, hpayload, hentries, hcap, hspare,
    by decide, by decide, by decide⟩
  isplit
  · iintro %k0 %k1 %below' %keysAfter %storedCursor' %frontier' %history'
      Hruntime Hsp Hbelow Hmapv Hcap Hptr Hlen Hkeys Hbump Hstreams %hfacts
    isimp only [ResumeWP, resumeExpr, List.nil_append, List.append_nil]
    obtain ⟨_, hitems⟩ := hfacts
    ihave Hheader := MapAt_header_words (func19Base + 24) k0 k1 entries $$ Hmapv
    icases Hheader with ⟨%ctrl, %mask, Hctrl, Hmask, Hitems⟩
    isimp only [show func19Base + 24 + 4 = func19Base + 28 by decide] at Hmask
    isimp only [show func19Base + 24 + 12 = func19Base + 36 by decide,
      hitems] at Hitems
    simp only [collectTail]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func19Base) (offset := 36)
      (UInt32.ofNat (HashMap.len (HashMap.ofEntries entries)))
      (by decide) (by decide) (by decide) (by decide) with Hitems
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    have Hmarker := func30_correct (hlc := hlc)
      (callerLocals :=
        ⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2,
          .i32 (UInt32.ofNat (HashMap.len (HashMap.ofEntries entries))),
          .i32 l4, .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩)
      (stack := [])
      (code := [.block 0 0 replyBody, .const 1, .const 1024, .call 99,
        .unreachable])
      (arity := arity) (remainder := remainder)
      (controls := okFrame :: outerFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hmarker
    simp only [List.nil_append] at Hmarker
    iapply Hmarker
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [replyFrame_literal]
      iapply twp_reply heapId storedCursor' frontier' history' output
      iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams

/-! ## The accepting path -/

/-- The end of the accepting path: the three header stores, the release of
the input byte vector and the collect call.  Local 5 holds the decoded
capacity, local 8 the decoded buffer and local 7 the decoded entry
count. -/
theorem twp_ok_reply [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : Func2Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len oldCap oldPtr oldLen : UInt32)
    (entries : HashMap.Map UInt32 UInt32)
    (payload spare mapBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l1 l2 l3 l4 l6 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hmapBefore : mapBefore.length = 32)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload = entryCodec.serialize entries)
    (hentries : entries.length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat)) :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      StackBelow func19Base collectDepth below ∗
      pointsTo_u32 0 (func19Base + 12) oldCap ∗
      pointsTo_u32 0 (func19Base + 16) oldPtr ∗
      pointsTo_u32 0 (func19Base + 20) oldLen ∗
      Slices.ByteSlice 0 (func19Base + 24) mapBefore ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.u32
          (UInt32.ofNat (HashMap.len (HashMap.ofEntries entries))))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 cap, .i32 l6, .i32 len, .i32 bufPtr], []⟩,
            okReply, arity, remainder,
            okFrame :: outerFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hcapw, Hptrw, Hlenw, Hmap, Hbuf, Hkeys,
    Hbump, Hstreams, Hcont, Hoom⟩
  simp only [okReply]
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := func19Base) (offset := 20) oldLen
    (by decide) (by decide) (by decide) (by decide) with Hlenw
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := func19Base) (offset := 16) oldPtr
    (by decide) (by decide) (by decide) (by decide) with Hptrw
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := func19Base) (offset := 12) oldCap
    (by decide) (by decide) (by decide) (by decide) with Hcapw
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [freeInputFrame_literal]
  simp only [freeInput]
  by_cases hcapacity : l2 = 0
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by simp [hcapacity])
    iapply twp_brIf (by decide) (by rfl)
    simp only [freeInputFrame, List.take_zero, List.nil_append]
    iapply twp_collect_reply hfunc2 heapId cap bufPtr len entries payload
      spare mapBefore keysBefore below storedCursor frontier history output
      hmapBefore hkeys hpayload hentries hcap hspare
    iframe
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by simp [hcapacity])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l3 l2 1
      (callerLocals :=
        ⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
          .i32 cap, .i32 l6, .i32 len, .i32 bufPtr], []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        freeInputFrame :: okFrame :: outerFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [freeInputFrame, List.take_zero, List.nil_append]
      iapply twp_collect_reply hfunc2 heapId cap bufPtr len entries payload
        spare mapBefore keysBefore below storedCursor frontier history output
        hmapBefore hkeys hpayload hentries hcap hspare
      iframe

/-! ## The "not all bytes read" error -/

/-- A sixteen-byte slot that holds four little-endian words is four cells.
The error path reads all four of them out of the map slot. -/
theorem ByteSlice_four_words [WasmHeapGS Universal.State]
    (ptr : UInt32) (w0 w1 w2 w3 : UInt32) :
    Slices.ByteSlice (α := Universal.State) 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2, w3]) ⊢
      iprop(pointsTo_u32 0 ptr w0 ∗ pointsTo_u32 0 (ptr + 4) w1 ∗
        pointsTo_u32 0 (ptr + 4 + 4) w2 ∗
        pointsTo_u32 0 (ptr + 4 + 4 + 4) w3) := by
  iintro Hbytes
  isimp only [Slices.ByteSlice] at Hbytes
  icases Hbytes with ⟨%_hnowrap, Hbytes⟩
  ihave Harray :=
    (Slices.arrayAt_eq_wordCells (α := Universal.State) 0 ptr
      [w0, w1, w2, w3]).mpr $$ Hbytes
  isimp only [arrayAt] at Harray
  icases Harray with ⟨H0, H1, H2, H3, _Hemp⟩
  isplitl_exacts [H0 H1 H2]
  iexact H3

/-- The error path of the "not all bytes read" branch.  It builds the
`io::Error` with the static message at 1049107, reads the four error words
out of the map slot, drops the decoded pair buffer, and joins the error
epilogue.  It writes nothing to the output stream. -/
theorem twp_not_all_read [WasmSmallStepGS hlc Universal.State]
    (hfunc52 : Func52Spec (hlc := hlc))
    (heapId : GName) (errSlot below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l1 l2 l3 l4 l5 l6 l7 l8 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (herrSlot : errSlot.length = 16) :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      StackBelow func19Base errorNewDepth below ∗
      Slices.ByteSlice 0 (func19Base + 24) errSlot ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone output afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩,
            notAllReadError, arity, remainder,
            notAllReadFrame :: decodeFrame :: okFrame ::
              outerFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hslot, Hbump, Hstreams, Hcont, Hoom⟩
  simp only [notAllReadError]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_const twp_const twp_const]
    rewriting [show (24 : UInt32) + func19Base = func19Base + 24 by decide]
  have Herr := hfunc52 func19Base (func19Base + 24) 12 1049107 18 heapId
    errSlot below storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
        .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩)
    (stack := []) (code := notAllReadRead) (arity := arity)
    (remainder := remainder)
    (controls :=
      notAllReadFrame :: decodeFrame :: okFrame ::
        outerFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Herr
  simp only [List.cons_append, List.nil_append] at Herr
  iapply Herr
  isplitl_exacts [Hruntime Hsp Hbelow Hslot Hbump Hstreams]
  isplitl_pureexact ⟨herrSlot, by decide, by decide⟩
  isplit
  · iintro %word0 %word1 %word2 %word3 %below' %storedCursor' %frontier'
      %history' Hruntime Hsp Hbelow Hslot Hbump Hstreams %hword0
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    have hne : word0 ≠ (2147483649 : UInt32) := by simpa [okTag] using hword0
    ihave ⟨Hw0, Hw1, Hw2, Hw3⟩ :=
      ByteSlice_four_words (func19Base + 24) word0 word1 word2 word3 $$ Hslot
    isimp only [show func19Base + 24 + 4 = func19Base + 28 by decide] at Hw1
    isimp only [show func19Base + 24 + 4 + 4 = func19Base + 32 by decide] at Hw2
    isimp only [show func19Base + 24 + 4 + 4 + 4 = func19Base + 36 by decide]
      at Hw3
    simp only [notAllReadRead]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func19Base) (offset := 36) word3
      (by decide) (by decide) (by decide) (by decide) with Hw3
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func19Base) (offset := 32) word2
      (by decide) (by decide) (by decide) (by decide) with Hw2
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func19Base) (offset := 28) word1
      (by decide) (by decide) (by decide) (by decide) with Hw1
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func19Base) (offset := 24) word0
      (by decide) (by decide) (by decide) (by decide) with Hw0
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [dropDecodedFrame_literal]
    simp only [dropDecoded]
    by_cases hcount : l4 = 0
    · wasm_twp_pures [twp_localGet]
      iapply twp_eqz (result := 1) (by simp [hcount])
      iapply twp_brIf (by decide) (by rfl)
      simp only [dropDecodedFrame, List.take_zero, List.nil_append,
        notAllReadTail]
      wasm_twp_pures [twp_localGet twp_const]
      iapply twp_ne (result := 1) (by simp [hne])
      iapply twp_brIf (by decide) (by rfl)
      simp only [okFrame, List.take_zero, List.nil_append]
      iapply twp_err_epilogue
      iframe
    · wasm_twp_pures [twp_localGet]
      iapply twp_eqz (result := 0) (by simp [hcount])
      wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const twp_shl]
        rewriting [show (3 : UInt32) % 32 = 3 by decide]
      wasm_twp_pures [twp_const]
      have Hfree := func57_noop_correct (hlc := hlc) l6 (l4 <<< 3) 4
        (callerLocals :=
          ⟨[], [Value.i32 func19Base, .i32 word0, .i32 l2, .i32 l3, .i32 l4,
            .i32 word1, .i32 l6, .i32 word3, .i32 word2], []⟩)
        (stack := []) (code := []) (arity := arity) (remainder := remainder)
        (controls :=
          dropDecodedFrame :: notAllReadFrame :: decodeFrame :: okFrame ::
            outerFrame afterTail :: controls)
        (calls := calls) (s := s) (E := E) (Φ := Φ)
      unfold CallContract callExpr at Hfree
      simp only [List.cons_append, List.nil_append] at Hfree
      iapply Hfree
      isplitl_exact Hruntime
      · iintro Hruntime
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        wasm_twp_pures [twp_exitControl]
        simp only [dropDecodedFrame, List.take_zero, List.nil_append,
          notAllReadTail]
        wasm_twp_pures [twp_localGet twp_const]
        iapply twp_ne (result := 1) (by simp [hne])
        iapply twp_brIf (by decide) (by rfl)
        simp only [okFrame, List.take_zero, List.nil_append]
        iapply twp_err_epilogue
        iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams

/-! ## The decode outcome -/

/-- The block that chooses between the "not all bytes read" error and the
decoded vector.  The word at offset 284 is what the decoder left of the
input length.  A zero means that the decoder consumed every byte, and only
then does the driver build the hash map and write the count.

`finalOutput` is the output stream that the chosen path leaves.  The two
hypotheses fix it on each arm, because the error arm writes nothing. -/
theorem twp_decode_outcome [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : Func2Spec (hlc := hlc)) (hfunc52 : Func52Spec (hlc := hlc))
    (heapId : GName)
    (cap bufPtr count remaining oldCap oldPtr oldLen : UInt32)
    (entries : HashMap.Map UInt32 UInt32)
    (payload spare mapBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output finalOutput : List UInt8)
    {l1 l2 l3 l5 l7 l8 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hmapBefore : mapBefore.length = 32)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload = entryCodec.serialize entries)
    (hentries : entries.length = count.toNat)
    (hcap : count.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - count.toNat))
    (hok : remaining = 0 → finalOutput = output ++ Borsh.u32
      (UInt32.ofNat (HashMap.len (HashMap.ofEntries entries))))
    (herr : remaining ≠ 0 → finalOutput = output) :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      StackBelow func19Base collectDepth below ∗
      pointsTo_u32 0 (func19Base + 284) remaining ∗
      pointsTo_u32 0 (func19Base + 300) count ∗
      pointsTo_u32 0 (func19Base + 12) oldCap ∗
      pointsTo_u32 0 (func19Base + 16) oldPtr ∗
      pointsTo_u32 0 (func19Base + 20) oldLen ∗
      Slices.ByteSlice 0 (func19Base + 24) mapBefore ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 cap,
              .i32 l5, .i32 bufPtr, .i32 l7, .i32 l8], []⟩,
            decodeOutcome, arity, remainder,
            decodeFrame :: okFrame :: outerFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hrem, Hcount, Hcapw, Hptrw, Hlenw, Hmap,
    Hbuf, Hkeys, Hbump, Hstreams, Hcont, Hoom⟩
  simp only [decodeOutcome_shape]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [notAllReadFrame_literal]
  simp only [notAllReadBody_shape]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func19Base) (offset := 284) remaining
    (by decide) (by decide) (by decide) (by decide) with Hrem
  by_cases hremaining : remaining = 0
  · rw [hok hremaining]
    iapply twp_eqz (result := 1) (by simp [hremaining])
    iapply twp_brIf (by decide) (by rfl)
    simp only [notAllReadFrame, List.take_zero, List.nil_append, decodeTail]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func19Base) (offset := 300) count
      (by decide) (by decide) (by decide) (by decide) with Hcount
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_exitControl]
    simp only [decodeFrame, List.take_zero, List.nil_append]
    iclear Hrem Hcount
    iapply twp_ok_reply hfunc2 heapId cap bufPtr count oldCap oldPtr oldLen
      entries payload spare mapBefore keysBefore below storedCursor frontier
      history output hmapBefore hkeys hpayload hentries hcap hspare
    iframe
  · rw [herr hremaining]
    iapply twp_eqz (result := 0) (by simp [hremaining])
    wasm_twp_pures [twp_brIfZero]
    ihave ⟨Hlow, Hbelow⟩ :=
      StackBelow_split func19Base collectDepth errorNewDepth below
        (by decide) (by decide) $$ Hbelow
    have hsplit : mapBefore.take 16 ++ mapBefore.drop 16 = mapBefore :=
      List.take_append_drop _ _
    have htake : (mapBefore.take 16).length = 16 := by
      simp [hmapBefore]
    ihave ⟨Hslot, Hrest⟩ :=
      (Slices.ByteSlice_append 0 (func19Base + 24) (mapBefore.take 16)
        (mapBefore.drop 16)).mp $$ [Hmap]
    · irw_exact [hsplit] with Hmap
    iclear Hlow Hrest Hbuf Hkeys Hrem Hcount Hcapw Hptrw Hlenw
    iapply twp_not_all_read hfunc52 heapId (mapBefore.take 16)
      (below.drop (collectDepth - errorNewDepth)) storedCursor frontier
      history output htake
    iframe

/-! ## The decoder guard -/

/-- The `Err` path of the decoder.  The first word of the output slot is a
`String` capacity, so the guard fails, and the driver moves the message
pointer into local 5 and joins the error epilogue.  It writes nothing. -/
theorem twp_ok_reject [WasmSmallStepGS hlc Universal.State]
    (word0 word1 : UInt32) (output : List UInt8)
    {l1 l2 l3 l5 l6 l7 l8 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hword0 : word0 ≠ okTag) :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      pointsTo_u32 0 (func19Base + 288) word0 ∗
      Streams [] output false ∗
      TailDone output afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 word1,
              .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩,
            okBlock, arity, remainder,
            okFrame :: outerFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Htag, Hstreams, Hcont⟩
  have hne : word0 ≠ (2147483649 : UInt32) := by simpa [okTag] using hword0
  simp only [okBlock]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [okGuardFrame_literal]
  simp only [okGuard]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func19Base) (offset := 288) word0
    (by decide) (by decide) (by decide) (by decide) with Htag
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  iapply twp_eq (result := 0) (by simp [hne])
  wasm_twp_pures [twp_brIfZero twp_localGet]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_br (by rfl)
  simp only [okFrame, List.take_zero, List.nil_append]
  iclear Htag
  iapply twp_err_epilogue
  iframe

/-- The accepting path of the decoder.  The guard holds, the driver moves
the decoded buffer pointer into local 6, and the decode outcome block
follows. -/
theorem twp_ok_accept [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : Func2Spec (hlc := hlc)) (hfunc52 : Func52Spec (hlc := hlc))
    (heapId : GName)
    (cap bufPtr count remaining oldCap oldPtr oldLen : UInt32)
    (entries : HashMap.Map UInt32 UInt32)
    (payload spare mapBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output finalOutput : List UInt8)
    {l1 l2 l3 l5 l6 l7 l8 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hmapBefore : mapBefore.length = 32)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload = entryCodec.serialize entries)
    (hentries : entries.length = count.toNat)
    (hcap : count.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - count.toNat))
    (hok : remaining = 0 → finalOutput = output ++ Borsh.u32
      (UInt32.ofNat (HashMap.len (HashMap.ofEntries entries))))
    (herr : remaining ≠ 0 → finalOutput = output) :
    iprop(RuntimeContext ∗ StackPointer func19Base ∗
      StackBelow func19Base collectDepth below ∗
      pointsTo_u32 0 (func19Base + 284) remaining ∗
      pointsTo_u32 0 (func19Base + 288) okTag ∗
      pointsTo_u32 0 (func19Base + 296) bufPtr ∗
      pointsTo_u32 0 (func19Base + 300) count ∗
      pointsTo_u32 0 (func19Base + 12) oldCap ∗
      pointsTo_u32 0 (func19Base + 16) oldPtr ∗
      pointsTo_u32 0 (func19Base + 20) oldLen ∗
      Slices.ByteSlice 0 (func19Base + 24) mapBefore ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func19Base, .i32 l1, .i32 l2, .i32 l3, .i32 cap,
              .i32 l5, .i32 l6, .i32 l7, .i32 l8], []⟩,
            okBlock, arity, remainder,
            okFrame :: outerFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hrem, Htag, Hbufw, Hcount, Hcapw, Hptrw,
    Hlenw, Hmap, Hbuf, Hkeys, Hbump, Hstreams, Hcont, Hoom⟩
  simp only [okBlock]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [okGuardFrame_literal]
  simp only [okGuard]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func19Base) (offset := 288) okTag
    (by decide) (by decide) (by decide) (by decide) with Htag
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  iapply twp_eq (result := 1) (by simp [okTag])
  iapply twp_brIf (by decide) (by rfl)
  simp only [okGuardFrame, List.take_zero, List.nil_append, okPath_shape]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func19Base) (offset := 296) bufPtr
    (by decide) (by decide) (by decide) (by decide) with Hbufw
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [decodeFrame_literal]
  iclear Htag Hbufw
  iapply twp_decode_outcome hfunc2 hfunc52 heapId cap bufPtr count remaining
    oldCap oldPtr oldLen entries payload spare mapBefore keysBefore below
    storedCursor frontier history output finalOutput hmapBefore hkeys hpayload
    hentries hcap hspare hok herr
  iframe

/-! ## From the decoder outcome to the public output

`Project.RustHashMap.Spec.lenOutput` names the output of `map_len`.  The
three lemmas below say what it is on each path, through
`Wasm.RustStd.HashMap.BorshBridge`.  The remaining length that the decoder
leaves decides between them. -/

/-- The remaining length is zero exactly when the input holds nothing after
the last pair.  Neither subtraction wraps, because the payload that the
header announces fits in the input. -/
theorem remaining_eq_zero_iff (bytes : List UInt8) (len : UInt32)
    (hlen : bytes.length = len.toNat) (haccept : DecodeAccepts bytes) :
    len - 4 - 8 * headerWord bytes = 0 ↔
      bytes.length = 4 + 8 * (headerWord bytes).toNat := by
  obtain ⟨hfour, hpayload⟩ := haccept
  have hsize : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hlt : len.toNat < 2 ^ 32 := len.toNat_lt
  have h0 : (0 : UInt32).toNat = 0 := rfl
  have h4 : (4 : UInt32).toNat = 4 := rfl
  have h8 : (8 : UInt32).toNat = 8 := rfl
  have hmul : ((8 : UInt32) * headerWord bytes).toNat
      = 8 * (headerWord bytes).toNat := by
    rw [UInt32.toNat_mul, h8]
    exact Nat.mod_eq_of_lt (by omega)
  have hle4 : (4 : UInt32) ≤ len := UInt32.le_iff_toNat_le.mpr (by omega)
  have hsub4 : (len - 4).toNat = len.toNat - 4 :=
    UInt32.toNat_sub_of_le len 4 hle4
  have hle8 : (8 : UInt32) * headerWord bytes ≤ len - 4 :=
    UInt32.le_iff_toNat_le.mpr (by omega)
  have hsub8 : (len - 4 - 8 * headerWord bytes).toNat
      = len.toNat - 4 - 8 * (headerWord bytes).toNat := by
    rw [UInt32.toNat_sub_of_le _ _ hle8, hsub4, hmul]
  constructor
  · intro h
    have hzero : (len - 4 - 8 * headerWord bytes).toNat = 0 := by
      rw [h]; exact h0
    rw [hsub8] at hzero
    omega
  · intro h
    refine UInt32.toNat_inj.mp ?_
    rw [hsub8, h0]
    omega

/-- The output of `map_len` on an input that the driver accepts. -/
theorem lenOutput_of_accepts (bytes : List UInt8)
    (haccept : DecodeAccepts bytes)
    (hexact : bytes.length = 4 + 8 * (headerWord bytes).toNat) :
    Project.RustHashMap.Spec.lenOutput bytes =
      Borsh.u32 (UInt32.ofNat
        (HashMap.len (HashMap.ofEntries (HashMap.BorshBridge.wireEntries
          bytes)))) := by
  unfold Project.RustHashMap.Spec.lenOutput Project.RustHashMap.Spec.mapOf
  rw [HashMap.BorshBridge.hashMap?_eq_some_of_accepts bytes haccept hexact]

/-- The output of `map_len` on an input that the decoder rejects. -/
theorem lenOutput_of_rejects (bytes : List UInt8)
    (hreject : ¬ DecodeAccepts bytes) :
    Project.RustHashMap.Spec.lenOutput bytes = [] := by
  unfold Project.RustHashMap.Spec.lenOutput Project.RustHashMap.Spec.mapOf
  rw [HashMap.BorshBridge.hashMap?_eq_none_of_not_accepts bytes hreject]

/-- The output of `map_len` on an input with bytes left over. -/
theorem lenOutput_of_trailing (bytes : List UInt8)
    (haccept : DecodeAccepts bytes)
    (htrailing : bytes.length ≠ 4 + 8 * (headerWord bytes).toNat) :
    Project.RustHashMap.Spec.lenOutput bytes = [] := by
  unfold Project.RustHashMap.Spec.lenOutput Project.RustHashMap.Spec.mapOf
  rw [HashMap.BorshBridge.hashMap?_eq_none_of_trailing bytes haccept htrailing]

/-! ## The initialized bytes of a vector -/

/-- The decoder reads the input through the vector data pointer.  It takes
the initialized bytes only, which both arms of `VecStorage` give. -/
theorem VecStorage_bytes [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32) (initialized : List UInt8) :
    VecStorage heapId capacity ptr initialized ⊢
      Slices.ByteSlice 0 ptr initialized := by
  iintro Hstorage
  isimp only [VecStorage] at Hstorage
  icases Hstorage with (%hempty | ⟨%_allocationId, %allBytes, %spare, %hfacts,
    Hblock⟩)
  · obtain ⟨_, _, hinit⟩ := hempty
    subst hinit
    isimp only [Slices.ByteSlice]
    isplitl_pureexact (by simpa [UInt32.size] using ptr.toBitVec.isLt)
    · iapply (pointsToBytes_nil 0 ptr).mpr
      itrivial
  · obtain ⟨_, _, hall, _⟩ := hfacts
    subst hall
    iunfold LiveBlock at Hblock
    icases Hblock with ⟨_Htoken, Hbytes, %_hfields⟩
    ihave ⟨Hinit, _Hspare⟩ :=
      (Slices.ByteSlice_append 0 ptr initialized spare).mp $$ Hbytes
    iexact Hinit

/-! ## The tail -/

/-- The tail of the `map_len` driver, from the end of the read loop to the
return.  The proof takes the three call contracts as hypotheses, so the
driver is proved before the three bodies are. -/
theorem twp_driver_tail [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc)) (hfunc2 : Func2Spec (hlc := hlc))
    (hfunc52 : Func52Spec (hlc := hlc)) :
    DriverTailSpec (hlc := hlc) := by
  unfold DriverTailSpec
  intro heapId capacity ptr aux4 input output reserve head chunk slice tail
    extra keysBefore storedCursor frontier history afterTail arity remainder
    controls calls s E Φ
  iintro ⟨HafterRead, Hextra, Hkeys, %hsizes, Hcont, Hoom⟩
  obtain ⟨hextra, hkeys, hinput⟩ := hsizes
  isimp only [AfterRead] at HafterRead
  icases HafterRead with ⟨Hruntime, Hsp, Hreserve, Hhead, Hchunk, Hslice,
    Hvec, Htail, Hbump, Hstreams, %hshape⟩
  obtain ⟨hhead, hchunk, hslice, htail, _hpush⟩ := hshape
  have hlenNat : (UInt32.ofNat input.length).toNat = input.length :=
    UInt32.toNat_ofNat_of_lt' hinput
  ihave Hcont : TailDone (output ++ Project.RustHashMap.Spec.lenOutput input)
      afterTail arity remainder controls calls s E Φ $$ [Hcont]
  · isimp only [TailDone]
    iexact Hcont
  ihave Hbelow : StackBelow func19Base decoderDepth (extra ++ reserve) $$
      [Hextra Hreserve]
  · rw [driverDepth_decoder]
    iapply StackBelow_of_reserve extra reserve hextra
    iframe
  icases (ByteSlice_split_at func19Base 12 head (by simp [hhead])).mp $$ Hhead
    with ⟨_Hhead0, Hhead1⟩
  isimp only [UInt32.reduceToNat] at Hhead1
  ihave Hwords := ByteSlice_header_as_words (func19Base + 12) (head.drop 12)
    (by simp [hhead]) (by decide) $$ Hhead1
  icases Hwords with ⟨%oldCap, %oldPtr, %oldLen, Hcapw, Hptrw, Hlenw⟩
  isimp only [show func19Base + 12 + 4 = func19Base + 16 by decide] at Hptrw
  isimp only [show func19Base + 12 + 8 = func19Base + 20 by decide] at Hlenw
  icases (ByteSlice_split_at (func19Base + 24) 32 chunk (by simp [hchunk])).mp
    $$ Hchunk with ⟨Hmap, _Hchunkrest⟩
  isimp only [UInt32.reduceToNat] at Hmap
  icases (ByteSlice_split_at (func19Base + 280) 4 slice
    (by simp [hslice])).mp $$ Hslice with ⟨Hs0, Hs1⟩
  isimp only [UInt32.reduceToNat] at Hs0
  isimp only [UInt32.reduceToNat,
    show func19Base + 280 + 4 = func19Base + 284 by decide] at Hs1
  ihave Hs0 := (Slices.ByteSlice_four_as_word 0 (func19Base + 280)
    (slice.take 4) (by simp [hslice]) (by decide)).mp $$ Hs0
  ihave Hs1 := (Slices.ByteSlice_four_as_word 0 (func19Base + 284)
    (slice.drop 4) (by simp [hslice]) (by decide)).mp $$ Hs1
  ihave ⟨Hheader, Hstorage⟩ :=
    (VecU8_as_headerBytes_storage heapId (func19Base + 288) capacity ptr input
      (by decide)).mp $$ Hvec
  ihave Hinput := VecStorage_bytes heapId capacity ptr input $$ Hstorage
  ihave Hout : Slices.ByteSlice 0 (func19Base + 288)
      (vecHeaderBytes capacity ptr input ++ tail) $$ [Hheader Htail]
  · iapply (Slices.ByteSlice_append 0 (func19Base + 288)
      (vecHeaderBytes capacity ptr input) tail).mpr
    isplitl_exact Hheader
    · irw_exact [show func19Base + 288
        + UInt32.ofNat (vecHeaderBytes capacity ptr input).length
          = func19Base + 300 by rw [vecHeaderBytes_length]; decide] with Htail
  simp only [func19AfterRead_cons, afterReadLocals]
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := func19Base) (offset := 284)
    (WordCodec.decodeU32 (slice.drop 4))
    (by decide) (by decide) (by decide) (by decide) with Hs1
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := func19Base) (offset := 280)
    (WordCodec.decodeU32 (slice.take 4))
    (by decide) (by decide) (by decide) (by decide) with Hs0
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add]
    rewriting [show (288 : UInt32) + func19Base = func19Base + 288 by decide,
      show (280 : UInt32) + func19Base = func19Base + 280 by decide]
  ihave Hs1 : pointsTo_u32 0 (func19Base + 280 + 4)
      (UInt32.ofNat input.length) $$ [Hs1]
  · irw_exact [show func19Base + 280 + 4 = func19Base + 284 by decide] with Hs1
  have Hdecode := hfunc1 func19Base (func19Base + 288) (func19Base + 280) ptr
    (UInt32.ofNat input.length) heapId input
    (vecHeaderBytes capacity ptr input ++ tail) (extra ++ reserve)
    storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func19Base, .i32 (UInt32.ofNat input.length),
        .i32 capacity, .i32 ptr, .i32 aux4, .i32 0, .i32 0, .i32 0,
        .i32 0], []⟩)
    (stack := []) (code := afterDecode afterTail) (arity := arity)
    (remainder := remainder) (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hdecode
  simp only [List.cons_append, List.nil_append] at Hdecode
  iapply Hdecode
  isplitl_exacts [Hruntime Hsp Hbelow Hout Hs0 Hs1 Hinput Hbump Hstreams]
  isplitl_pureexact ⟨by simp [htail], hlenNat.symm, by decide, by decide,
    by decide⟩
  isplit
  · iintro %cap' %buffer %payload %spare' %below' %storedCursor' %frontier'
      %history' %haccept Hruntime Hsp Hbelow Hout Hs0 Hs1 Hbytes Hbuf Hbump
      Hstreams %hfacts2
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    obtain ⟨hpayloadEq, hcapBound, hspareLen, _hzero⟩ := hfacts2
    obtain ⟨hfour, hfits⟩ := haccept
    have hprefixLen : (input.take (4 + 8 * (headerWord input).toNat)).length
        = 4 + 8 * (headerWord input).toNat := by
      rw [List.length_take]; omega
    have hprefixHead :
        headerWord (input.take (4 + 8 * (headerWord input).toNat))
          = headerWord input := by
      unfold headerWord
      rw [List.take_take, Nat.min_eq_left (by omega)]
    have hprefixAccept :
        DecodeAccepts (input.take (4 + 8 * (headerWord input).toNat)) := by
      unfold DecodeAccepts
      rw [hprefixLen, hprefixHead]
      omega
    have hprefixExact :
        (input.take (4 + 8 * (headerWord input).toNat)).length
          = 4 + 8 * (headerWord
              (input.take (4 + 8 * (headerWord input).toNat))).toNat := by
      rw [hprefixLen, hprefixHead]
    have hdropTake :
        (input.take (4 + 8 * (headerWord input).toNat)).drop 4
          = (input.drop 4).take (8 * (headerWord input).toNat) := by
      rw [List.drop_take]
      congr 1
      omega
    have hserialize : entryCodec.serialize
        (HashMap.BorshBridge.wireEntries
          (input.take (4 + 8 * (headerWord input).toNat))) = payload := by
      unfold entryCodec
      rw [HashMap.BorshBridge.serialize_wireEntries _ hprefixExact, hdropTake,
        hpayloadEq]
    have hentriesLen : (HashMap.BorshBridge.wireEntries
        (input.take (4 + 8 * (headerWord input).toNat))).length
          = (headerWord input).toNat := by
      rw [HashMap.BorshBridge.length_wireEntries]
      show (headerWord (input.take (4 + 8 * (headerWord input).toNat))).toNat
        = (headerWord input).toNat
      rw [hprefixHead]
    have hok : UInt32.ofNat input.length - 4 - 8 * headerWord input = 0 →
        output ++ Project.RustHashMap.Spec.lenOutput input
          = output ++ Borsh.u32 (UInt32.ofNat (HashMap.len (HashMap.ofEntries
              (HashMap.BorshBridge.wireEntries
                (input.take (4 + 8 * (headerWord input).toNat)))))) := by
      intro hzero
      have hexact := (remaining_eq_zero_iff input (UInt32.ofNat input.length)
        hlenNat.symm ⟨hfour, hfits⟩).mp hzero
      have hself : input.take (4 + 8 * (headerWord input).toNat) = input := by
        rw [← hexact, List.take_length]
      rw [hself, lenOutput_of_accepts input ⟨hfour, hfits⟩ hexact]
    have herr : UInt32.ofNat input.length - 4 - 8 * headerWord input ≠ 0 →
        output ++ Project.RustHashMap.Spec.lenOutput input = output := by
      intro hnonzero
      have htrailing : input.length ≠ 4 + 8 * (headerWord input).toNat := by
        intro h
        exact hnonzero ((remaining_eq_zero_iff input
          (UInt32.ofNat input.length) hlenNat.symm ⟨hfour, hfits⟩).mpr h)
      rw [lenOutput_of_trailing input ⟨hfour, hfits⟩ htrailing, List.append_nil]
    ihave ⟨H288, H292, H296, H300⟩ :=
      ByteSlice_four_words (func19Base + 288) okTag cap' buffer
        (headerWord input) $$ Hout
    isimp only [show func19Base + 288 + 4 = func19Base + 292 by decide] at H292
    isimp only [show func19Base + 288 + 4 + 4 = func19Base + 296 by decide]
      at H296
    isimp only [show func19Base + 288 + 4 + 4 + 4 = func19Base + 300 by decide]
      at H300
    isimp only [show func19Base + 280 + 4 = func19Base + 284 by decide] at Hs1
    simp only [afterDecode]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func19Base) (offset := 292) cap'
      (by decide) (by decide) (by decide) (by decide) with H292
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [outerFrame_literal]
    simp only [outerBody]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [okFrame_literal]
    ihave ⟨_Hlow, Hbelow⟩ :=
      StackBelow_split func19Base decoderDepth collectDepth below'
        (by decide) (by decide) $$ Hbelow
    iapply twp_ok_accept hfunc2 hfunc52 heapId cap' buffer (headerWord input)
      (UInt32.ofNat input.length - 4 - 8 * headerWord input)
      oldCap oldPtr oldLen
      (HashMap.BorshBridge.wireEntries
        (input.take (4 + 8 * (headerWord input).toNat)))
      payload spare' (chunk.take 32) keysBefore
      (below'.drop (decoderDepth - collectDepth))
      storedCursor' frontier' history' output
      (output ++ Project.RustHashMap.Spec.lenOutput input)
      (by simp [hchunk]) hkeys hserialize.symm hentriesLen hcapBound hspareLen
      hok herr
    iframe
  · isplit
    · iintro %word0 %word1 %word2 %word3 %ptr' %len' %below' %storedCursor'
        %frontier' %history' %hreject Hruntime Hsp Hbelow Hout Hs0 Hs1 Hbytes
        Hbump Hstreams %hword0
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      ihave ⟨H288, H292, H296, H300⟩ :=
        ByteSlice_four_words (func19Base + 288) word0 word1 word2 word3 $$ Hout
      isimp only [show func19Base + 288 + 4 = func19Base + 292 by decide]
        at H292
      simp only [afterDecode]
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func19Base) (offset := 292) word1
        (by decide) (by decide) (by decide) (by decide) with H292
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [outerFrame_literal]
      simp only [outerBody]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [okFrame_literal, lenOutput_of_rejects input hreject, List.append_nil]
      iapply twp_ok_reject word0 word1 output hword0
      iframe
    · iintro %remaining' Hstreams
      iapply Hoom
      isimp only [ExportOOM]
      iexists remaining', output
      iexact Hstreams

end Project.RustHashMap.DriverTailProof
