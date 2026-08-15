import Project.Mergesort.DriverProof
import Project.Mergesort.StdIOWrapperProof
import Project.Mergesort.DriverSortProof
import Project.Mergesort.MemoryFillProof

/-!
# Generated driver input path

This file isolates the input half of exported `func127`, from the state right
after the 384-byte frame prologue (`export_frame_prefix_twp` in
`DriverProof.lean`) down to the exact instruction where the collected input
vector is measured (`driverAtVecLen` in `DriverSortProof.lean`).

Two generated callees are handled here as well:

* local `func135` (the buffered-I/O constructor, called at absolute index 137)
  is decomposed into exact segments that stop at its two generated
  sub-constructor calls (absolute 138 and 139, both allocator-backed), plus a
  fully proven descriptor-copy epilogue;
* local `func37` (`read_line`, called at absolute index 39) is a pure
  forwarding shim whose rule stops at its inner call (absolute 24), the first
  step of the chain that bottoms out at `stdioReadWrapper_to_import_twp`.

Every allocator- or iterator-backed callee is deliberately left as an explicit
call boundary in the same seam idiom as the `.call 107` contract described in
`DriverSortProof.lean`: the rules stop exactly at the generated call, so the
owners of those internals can discharge precisely that contract later.
-/

namespace Project.Mergesort.DriverInputProof

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
open Project.Mergesort.DriverSortProof
open Project.Mergesort.VectorProof
open Project.Mergesort.MemoryFillProof

private theorem twp_eq
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs = rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .eq :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  Wasm.SmallStep.twp_pureStep _ _ _ (fun _ => Step.eq hresult)

/-! ## Stable names for the remaining buffered-I/O constructor callees -/

theorem bufReaderCtor_index : «module».funcs[136]? = some func136Def := by rfl
theorem bufWriterCtor_index : «module».funcs[137]? = some func137Def := by rfl
theorem lineReadImpl_index : «module».funcs[22]? = some func22Def := by rfl

/-! ## Buffered-I/O constructor (`func135`, absolute call 137)

`func135` installs a 48-byte frame, builds the `BufReader` descriptor at
`frame + 12` (absolute call 138) and the `BufWriter` descriptor at
`frame + 32` (absolute call 139), and copies both into the caller-provided
36-byte destination.  Both sub-constructors allocate, so they stay as explicit
call boundaries. -/

def bufferedAtReaderCtor : Program := func135.drop 10
def bufferedAfterReaderCtor : Program := func135.drop 11
def bufferedAtWriterCtor : Program := func135.drop 15
def bufferedAfterWriterCtor : Program := func135.drop 16

theorem func135_eq_readerCtorPrefix :
    func135 =
      [.globalGet 0, .const 48, .sub, .localSet 1, .localGet 1, .globalSet 0,
       .call 136, .localGet 1, .const 12, .add] ++ bufferedAtReaderCtor := by
  rfl

theorem bufferedAtReaderCtor_eq :
    bufferedAtReaderCtor = .call 138 :: bufferedAfterReaderCtor := by
  rfl

theorem bufferedAfterReaderCtor_eq :
    bufferedAfterReaderCtor =
      [.call 136, .localGet 1, .const 32, .add] ++ bufferedAtWriterCtor := by
  rfl

theorem bufferedAtWriterCtor_eq :
    bufferedAtWriterCtor = .call 139 :: bufferedAfterWriterCtor := by
  rfl

/-- Exact prefix of the buffered-I/O constructor: install the 48-byte frame,
run the generated no-op wrapper, and stop right before the `BufReader`
sub-constructor at absolute index 138 with `frame + 12` on the stack. -/
theorem buffered_to_readerCtor_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst stackTop : UInt32)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 (stackTop - 48), .i32 0],
              [.i32 (12 + (stackTop - 48))]⟩,
            bufferedAtReaderCtor, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 dst], [.i32 0, .i32 0], []⟩,
        func135, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hcont⟩
  rw [func135_eq_readerCtorPrefix]
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceSub,
    List.set]
  have Hnoop := stdioNoopWrapper_call_twp (α := α)
    (s := s) (E := E) (Φ := Φ)
    (callerLocals := ⟨[.i32 dst], [.i32 (stackTop - 48), .i32 0], []⟩)
    (stack := [])
    (code := .localGet 1 :: .const 12 :: .add :: bufferedAtReaderCtor)
    (arity := 0) (remainder := []) (controls := []) (calls := calls)
  iapply Hnoop
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply Hcont $$ Hruntime Hglobal

/-- Exact middle of the buffered-I/O constructor: after the `BufReader`
sub-constructor returns, run the second no-op wrapper and stop right before
the `BufWriter` sub-constructor at absolute index 139 with `frame + 32` on
the stack. -/
theorem buffered_between_ctors_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst frame : UInt32)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 frame, .i32 0], [.i32 (32 + frame)]⟩,
            bufferedAtWriterCtor, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 dst], [.i32 frame, .i32 0], []⟩,
        bufferedAfterReaderCtor, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  rw [bufferedAfterReaderCtor_eq]
  simp only [List.cons_append, List.nil_append]
  have Hnoop := stdioNoopWrapper_call_twp (α := α)
    (s := s) (E := E) (Φ := Φ)
    (callerLocals := ⟨[.i32 dst], [.i32 frame, .i32 0], []⟩)
    (stack := [])
    (code := .localGet 1 :: .const 32 :: .add :: bufferedAtWriterCtor)
    (arity := 0) (remainder := []) (controls := []) (calls := calls)
  iapply Hnoop
  isplitl [Hruntime]
  · iexact Hruntime
  iintro Hruntime
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply Hcont $$ Hruntime

theorem bufferedAfterWriterCtor_eq :
    bufferedAfterWriterCtor =
      [.localGet 0, .localGet 1, .load32 28, .store32 16,
       .localGet 0, .localGet 1, .load64 20, .store64 8,
       .localGet 0, .localGet 1, .load64 12, .store64 0,
       .localGet 0, .const 20, .add, .localSet 2,
       .localGet 2, .localGet 1, .load64 40, .store64 8,
       .localGet 2, .localGet 1, .load64 32, .store64 0,
       .localGet 1, .const 48, .add, .globalSet 0] ++ [.ret] := by
  rfl

/-! Exact epilogue of the buffered-I/O constructor: copy the `BufReader`
descriptor built at `frame + 12` and the `BufWriter` descriptor built at
`frame + 32` into the caller-provided destination, pop the frame, and
return. -/
set_option maxHeartbeats 4000000 in
theorem buffered_epilogue_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst frame : UInt32)
    (reader0 reader8 writer0 writer8 : UInt64) (reader16 : UInt32)
    (oldDst0 oldDst8 oldDst20 oldDst28 : UInt64) (oldDst16 : UInt32)
    (hframeRoom : frame.toNat + 48 ≤ UInt32.size)
    (hdstRoom : dst.toNat + 36 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u64 (frame + 12) reader0 ∗
      pointsTo_u64 (frame + 20) reader8 ∗
      pointsTo_u32 (frame + 28) reader16 ∗
      pointsTo_u64 (frame + 32) writer0 ∗
      pointsTo_u64 (frame + 40) writer8 ∗
      pointsTo_u64 (dst + 0) oldDst0 ∗
      pointsTo_u64 (dst + 8) oldDst8 ∗
      pointsTo_u32 (dst + 16) oldDst16 ∗
      pointsTo_u64 (dst + 20) oldDst20 ∗
      pointsTo_u64 (dst + 28) oldDst28 ∗
      (globalPointsTo 0 (.i32 (48 + frame)) -∗
        pointsTo_u64 (frame + 12) reader0 -∗
        pointsTo_u64 (frame + 20) reader8 -∗
        pointsTo_u32 (frame + 28) reader16 -∗
        pointsTo_u64 (frame + 32) writer0 -∗
        pointsTo_u64 (frame + 40) writer8 -∗
        pointsTo_u64 (dst + 0) reader0 -∗
        pointsTo_u64 (dst + 8) reader8 -∗
        pointsTo_u32 (dst + 16) reader16 -∗
        pointsTo_u64 (dst + 20) writer0 -∗
        pointsTo_u64 (dst + 28) writer8 -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 frame, .i32 (dst + 20)], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 dst], [.i32 frame, .i32 0], []⟩,
        bufferedAfterWriterCtor, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨hf120, hf121, hf122, hf123, hf124, hf125, hf126, hf127⟩ :=
    descriptorSlot64Facts frame 12 48 hframeRoom (by decide)
  obtain ⟨hf200, hf201, hf202, hf203, hf204, hf205, hf206, hf207⟩ :=
    descriptorSlot64Facts frame 20 48 hframeRoom (by decide)
  obtain ⟨hf280, hf281, hf282, hf283⟩ :=
    descriptorSlot32Facts frame 28 48 hframeRoom (by decide)
  obtain ⟨hf320, hf321, hf322, hf323, hf324, hf325, hf326, hf327⟩ :=
    descriptorSlot64Facts frame 32 48 hframeRoom (by decide)
  obtain ⟨hf400, hf401, hf402, hf403, hf404, hf405, hf406, hf407⟩ :=
    descriptorSlot64Facts frame 40 48 hframeRoom (by decide)
  obtain ⟨hd00, hd01, hd02, hd03, hd04, hd05, hd06, hd07⟩ :=
    descriptorSlot64Facts dst 0 36 hdstRoom (by decide)
  obtain ⟨hd80, hd81, hd82, hd83, hd84, hd85, hd86, hd87⟩ :=
    descriptorSlot64Facts dst 8 36 hdstRoom (by decide)
  obtain ⟨hd160, hd161, hd162, hd163⟩ :=
    descriptorSlot32Facts dst 16 36 hdstRoom (by decide)
  have hdst20Room : (dst + 20).toNat + 16 ≤ UInt32.size := by
    have h20 : (dst + (20 : UInt32)).toNat = dst.toNat + 20 :=
      (descriptorSlot32Facts dst 20 36 hdstRoom (by decide)).1
    rw [h20]
    simp only [UInt32.size] at hdstRoom ⊢
    omega
  obtain ⟨hz00, hz01, hz02, hz03, hz04, hz05, hz06, hz07⟩ :=
    descriptorSlot64Facts (dst + 20) 0 16 hdst20Room (by decide)
  obtain ⟨hz80, hz81, hz82, hz83, hz84, hz85, hz86, hz87⟩ :=
    descriptorSlot64Facts (dst + 20) 8 16 hdst20Room (by decide)
  iintro ⟨Hglobal, Hr0, Hr8, Hr16, Hw0, Hw8, Hd0, Hd8, Hd16, Hd20, Hd28,
    Hcont⟩
  rw [bufferedAfterWriterCtor_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 reader16 hf280 hf281 hf282 hf283 $$ Hr16
  iintro Hr16
  iapply twp_store32 oldDst16 hd160 hd161 hd162 hd163 $$ Hd16
  iintro Hd16
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 reader8 hf200 hf201 hf202 hf203 hf204 hf205 hf206
    hf207 $$ Hr8
  iintro Hr8
  iapply twp_store64 oldDst8 hd80 hd81 hd82 hd83 hd84 hd85 hd86 hd87 $$ Hd8
  iintro Hd8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 reader0 hf120 hf121 hf122 hf123 hf124 hf125 hf126
    hf127 $$ Hr0
  iintro Hr0
  iapply twp_store64 oldDst0 hd00 hd01 hd02 hd03 hd04 hd05 hd06 hd07 $$ Hd0
  iintro Hd0
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (20 : UInt32) + dst = dst + 20 from by bv_decide]
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceSub,
    List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 writer8 hf400 hf401 hf402 hf403 hf404 hf405 hf406
    hf407 $$ Hw8
  iintro Hw8
  ihave Hd28At : pointsTo_u64 ((dst + 20) + 8) oldDst28 $$ [Hd28]
  · rw [show (dst + 20) + 8 = dst + 28 from by bv_decide]
    iexact Hd28
  iapply twp_store64 oldDst28 hz80 hz81 hz82 hz83 hz84 hz85 hz86 hz87 $$
    Hd28At
  iintro Hd28At
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 writer0 hf320 hf321 hf322 hf323 hf324 hf325 hf326
    hf327 $$ Hw0
  iintro Hw0
  ihave Hd20At : pointsTo_u64 ((dst + 20) + 0) oldDst20 $$ [Hd20]
  · rw [UInt32.add_zero]
    iexact Hd20
  iapply twp_store64 oldDst20 hz00 hz01 hz02 hz03 hz04 hz05 hz06 hz07 $$
    Hd20At
  iintro Hd20At
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  isimp [UInt32.add_zero] at Hd20At
  ihave Hd28Out : pointsTo_u64 (dst + 28) writer8 $$ [Hd28At]
  · rw [show dst + 28 = (dst + 20) + 8 from by bv_decide]
    iexact Hd28At
  iapply Hcont $$ Hglobal Hr0 Hr8 Hr16 Hw0 Hw8 Hd0 Hd8 Hd16 Hd20At Hd28Out

/-- Composable entry rule for the buffered-I/O constructor at absolute index
137, stopping at the `BufReader` sub-constructor boundary inside the freshly
pushed callee frame. -/
theorem buffered_call_to_readerCtor_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst stackTop : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 48)) -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 (stackTop - 48), .i32 0],
              [.i32 (12 + (stackTop - 48))]⟩,
            bufferedAtReaderCtor, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 dst :: stack },
        .call 137 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 137 func135Def
      (by decide) buffered_index $$ Hruntime
  iintro Hruntime
  simp [func135Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := buffered_to_readerCtor_twp (α := α)
    dst stackTop (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hruntime Hglobal
  iapply Hcont $$ Hruntime Hglobal

/-! ## `read_line` (`func37`, absolute call 39)

The generated body forwards `(result, line, reader)` as
`(result, reader, line)` to absolute call 24, whose chain eventually reaches
the `stdio.read` import through `stdioReadWrapper_to_import_twp`. -/

def readLineAtInner : Program := func37.drop 3

theorem func37_eq_innerPrefix :
    func37 = [.localGet 0, .localGet 2, .localGet 1] ++ readLineAtInner := by
  rfl

theorem readLineAtInner_eq :
    readLineAtInner = [.call 24, .ret] := by
  rfl

/-- Exact body prefix of generated `read_line`, ending at its inner call. -/
theorem readLine_body_to_inner_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (result line reader : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 result, .i32 line, .i32 reader], [],
          [.i32 line, .i32 reader, .i32 result]⟩,
        readLineAtInner, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 result, .i32 line, .i32 reader], [], []⟩,
        func37, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  rw [func37_eq_innerPrefix]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iexact Hcont

/-- Composable entry rule for `read_line` at absolute index 39, stopping at
the inner absolute call 24 inside the freshly pushed callee frame. -/
theorem readLine_call_to_inner_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (result line reader : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 result, .i32 line, .i32 reader], [],
              [.i32 line, .i32 reader, .i32 result]⟩,
            readLineAtInner, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 reader, .i32 line, .i32 result] ++ stack },
        .call 39 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 39 func37Def
      (by decide) readLine_index $$ Hruntime
  iintro Hruntime
  simp [func37Def, Function.toLocals, Function.numParams]
  have Hbody := readLine_body_to_inner_twp (α := α)
    result line reader (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-! ## Driver anchors between the constructor and the collected vector

Instruction offsets into `func127`, one anchor per generated call boundary on
the input path.  `driverAfterCollect` is exactly `driverAtVecLen`, the state
`DriverSortProof.lean` continues from. -/

def driverAtBufCtor : Program := func127.drop 9
def driverAfterBufCtor : Program := func127.drop 10
def driverAtStringNew : Program := func127.drop 39
def driverAfterStringNew : Program := func127.drop 40
def driverAtReadLine : Program := func127.drop 49
def driverAfterReadLine : Program := func127.drop 50
def driverAtReadCheck : Program := func127.drop 63
def driverAfterReadCheck : Program := func127.drop 64
def driverAtStringDeref : Program := func127.drop 70
def driverAfterStringDeref : Program := func127.drop 71
def driverAtSplit : Program := func127.drop 83
def driverAfterSplit : Program := func127.drop 84
def driverAtMap : Program := func127.drop 90
def driverAfterMap : Program := func127.drop 91
def driverAtCollect : Program := func127.drop 97
def driverAfterCollect : Program := func127.drop 98

theorem driverAtBufCtor_eq :
    driverAtBufCtor = .call 137 :: driverAfterBufCtor := by
  rfl

theorem driverAfterBufCtor_eq :
    driverAfterBufCtor =
      [.localGet 0, .localGet 0, .load32 108, .store32 64,
       .localGet 0, .localGet 0, .load64 100, .store64 56,
       .localGet 0, .localGet 0, .load64 92, .store64 48,
       .localGet 0, .const 92, .add, .const 20, .add, .localSet 1,
       .localGet 0, .localGet 1, .load64 8, .store64 80,
       .localGet 0, .localGet 1, .load64 0, .store64 72,
       .localGet 0, .const 128, .add] ++ driverAtStringNew := by
  rfl

theorem driverAtStringNew_eq :
    driverAtStringNew = .call 112 :: driverAfterStringNew := by
  rfl

theorem driverAfterStringNew_eq :
    driverAfterStringNew =
      [.localGet 0, .const 140, .add,
       .localGet 0, .const 48, .add,
       .localGet 0, .const 128, .add] ++ driverAtReadLine := by
  rfl

theorem driverAtReadLine_eq :
    driverAtReadLine = .call 39 :: driverAfterReadLine := by
  rfl

theorem driverAfterReadLine_eq :
    driverAfterReadLine =
      [.localGet 0, .load8U 140, .localSet 2,
       .const 4, .localSet 3,
       .localGet 2, .const 255, .and,
       .localGet 3, .const 255, .and,
       .eq, .localSet 4] ++ driverAtReadCheck := by
  rfl

theorem driverAtReadCheck_eq :
    driverAtReadCheck =
      .block 0 0 [
        .const 0, .const 1, .localGet 4, .const 1, .and, .select,
        .const 1, .and, .eqz, .br_if 0,
        .localGet 0, .localGet 0, .load64 140, .store64 360,
        .const 1049644, .const 43,
        .localGet 0, .const 360, .add,
        .const 1049628, .const 1050352,
        .call 241, .unreachable] :: driverAfterReadCheck := by
  rfl

theorem driverAfterReadCheck_eq :
    driverAfterReadCheck =
      [.localGet 0, .const 24, .add,
       .localGet 0, .const 128, .add] ++ driverAtStringDeref := by
  rfl

theorem driverAtStringDeref_eq :
    driverAtStringDeref = .call 121 :: driverAfterStringDeref := by
  rfl

theorem driverAfterStringDeref_eq :
    driverAfterStringDeref =
      [.localGet 0, .load32 28, .localSet 5,
       .localGet 0, .load32 24, .localSet 6,
       .localGet 0, .const 200, .add,
       .localGet 6, .localGet 5, .const 32] ++ driverAtSplit := by
  rfl

theorem driverAtSplit_eq :
    driverAtSplit = .call 84 :: driverAfterSplit := by
  rfl

theorem driverAfterSplit_eq :
    driverAfterSplit =
      [.localGet 0, .const 160, .add,
       .localGet 0, .const 200, .add] ++ driverAtMap := by
  rfl

theorem driverAtMap_eq :
    driverAtMap = .call 92 :: driverAfterMap := by
  rfl

theorem driverAfterMap_eq :
    driverAfterMap =
      [.localGet 0, .const 148, .add,
       .localGet 0, .const 160, .add] ++ driverAtCollect := by
  rfl

theorem driverAtCollect_eq :
    driverAtCollect = .call 93 :: driverAfterCollect := by
  rfl

/-- The instruction after the collect boundary is exactly where the sort-side
driver proof picks up. -/
theorem driverAfterCollect_eq_atVecLen :
    driverAfterCollect = driverAtVecLen := by
  rfl

/-- Local layout after the buffered-descriptor copy set local 1 to the
`BufWriter` half of the constructed descriptor pair. -/
def driverReaderLocals (frame : UInt32) : List Value :=
  (exportFramedLocals frame).set 1 (.i32 (frame + 112))

/-- Local layout after the successful read-result check recorded the `Ok`
discriminant and comparison scratch values. -/
def driverCheckLocals (frame : UInt32) : List Value :=
  (((driverReaderLocals frame).set 2 (.i32 4)).set 3 (.i32 4)).set 4 (.i32 1)

/-! ## Buffered-descriptor copy into the driver frame

Right after the constructor at absolute 137 returns, the driver copies the
`BufReader` half of the freshly built descriptor pair (at `frame + 92`) into
its scratch slots at `frame + 48` and the `BufWriter` half (at `frame + 112`)
into `frame + 72`, then prepares the `String::new` destination.  The segment
stops exactly at the generated `.call 112`. -/
set_option maxHeartbeats 6000000 in
theorem driver_after_bufCtor_to_stringNew_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame : UInt32)
    (reader0 reader8 writer0 writer8 : UInt64) (reader16 : UInt32)
    (old48 old56 old72 old80 : UInt64) (old64 : UInt32)
    (hframeRoom : frame.toNat + 384 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u64 (frame + 92) reader0 ∗
      pointsTo_u64 (frame + 100) reader8 ∗
      pointsTo_u32 (frame + 108) reader16 ∗
      pointsTo_u64 (frame + 112) writer0 ∗
      pointsTo_u64 (frame + 120) writer8 ∗
      pointsTo_u64 (frame + 48) old48 ∗
      pointsTo_u64 (frame + 56) old56 ∗
      pointsTo_u32 (frame + 64) old64 ∗
      pointsTo_u64 (frame + 72) old72 ∗
      pointsTo_u64 (frame + 80) old80 ∗
      (pointsTo_u64 (frame + 92) reader0 -∗
        pointsTo_u64 (frame + 100) reader8 -∗
        pointsTo_u32 (frame + 108) reader16 -∗
        pointsTo_u64 (frame + 112) writer0 -∗
        pointsTo_u64 (frame + 120) writer8 -∗
        pointsTo_u64 (frame + 48) reader0 -∗
        pointsTo_u64 (frame + 56) reader8 -∗
        pointsTo_u32 (frame + 64) reader16 -∗
        pointsTo_u64 (frame + 72) writer0 -∗
        pointsTo_u64 (frame + 80) writer8 -∗
        WP (.running
          ⟨⟨[], driverReaderLocals frame, [.i32 (128 + frame)]⟩,
            driverAtStringNew, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], exportFramedLocals frame, []⟩,
        driverAfterBufCtor, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h920, h921, h922, h923, h924, h925, h926, h927⟩ :=
    descriptorSlot64Facts frame 92 384 hframeRoom (by decide)
  obtain ⟨h1000, h1001, h1002, h1003, h1004, h1005, h1006, h1007⟩ :=
    descriptorSlot64Facts frame 100 384 hframeRoom (by decide)
  obtain ⟨h1080, h1081, h1082, h1083⟩ :=
    descriptorSlot32Facts frame 108 384 hframeRoom (by decide)
  obtain ⟨h480, h481, h482, h483, h484, h485, h486, h487⟩ :=
    descriptorSlot64Facts frame 48 384 hframeRoom (by decide)
  obtain ⟨h560, h561, h562, h563, h564, h565, h566, h567⟩ :=
    descriptorSlot64Facts frame 56 384 hframeRoom (by decide)
  obtain ⟨h640, h641, h642, h643⟩ :=
    descriptorSlot32Facts frame 64 384 hframeRoom (by decide)
  obtain ⟨h720, h721, h722, h723, h724, h725, h726, h727⟩ :=
    descriptorSlot64Facts frame 72 384 hframeRoom (by decide)
  obtain ⟨h800, h801, h802, h803, h804, h805, h806, h807⟩ :=
    descriptorSlot64Facts frame 80 384 hframeRoom (by decide)
  have h112room : (frame + 112).toNat + 16 ≤ UInt32.size := by
    have h112 : (frame + (112 : UInt32)).toNat = frame.toNat + 112 :=
      (descriptorSlot64Facts frame 112 384 hframeRoom (by decide)).1
    rw [h112]
    simp only [UInt32.size] at hframeRoom ⊢
    omega
  obtain ⟨hl00, hl01, hl02, hl03, hl04, hl05, hl06, hl07⟩ :=
    descriptorSlot64Facts (frame + 112) 0 16 h112room (by decide)
  obtain ⟨hl80, hl81, hl82, hl83, hl84, hl85, hl86, hl87⟩ :=
    descriptorSlot64Facts (frame + 112) 8 16 h112room (by decide)
  iintro ⟨Hr0, Hr8, Hr16, Hw0, Hw8, H48, H56, H64, H72, H80, Hcont⟩
  rw [driverAfterBufCtor_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 reader16 h1080 h1081 h1082 h1083 $$ Hr16
  iintro Hr16
  iapply twp_store32 old64 h640 h641 h642 h643 $$ H64
  iintro H64
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 reader8 h1000 h1001 h1002 h1003 h1004 h1005 h1006
    h1007 $$ Hr8
  iintro Hr8
  iapply twp_store64 old56 h560 h561 h562 h563 h564 h565 h566 h567 $$ H56
  iintro H56
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load64 reader0 h920 h921 h922 h923 h924 h925 h926 h927 $$ Hr0
  iintro Hr0
  iapply twp_store64 old48 h480 h481 h482 h483 h484 h485 h486 h487 $$ H48
  iintro H48
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_const
  iapply twp_add
  rw [show (20 : UInt32) + (92 + frame) = frame + 112 from by bv_decide]
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hw8At : pointsTo_u64 ((frame + 112) + 8) writer8 $$ [Hw8]
  · rw [show (frame + 112) + 8 = frame + 120 from by bv_decide]
    iexact Hw8
  iapply twp_load64 writer8 hl80 hl81 hl82 hl83 hl84 hl85 hl86 hl87 $$ Hw8At
  iintro Hw8At
  iapply twp_store64 old80 h800 h801 h802 h803 h804 h805 h806 h807 $$ H80
  iintro H80
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hw0At : pointsTo_u64 ((frame + 112) + 0) writer0 $$ [Hw0]
  · rw [UInt32.add_zero]
    iexact Hw0
  iapply twp_load64 writer0 hl00 hl01 hl02 hl03 hl04 hl05 hl06 hl07 $$ Hw0At
  iintro Hw0At
  iapply twp_store64 old72 h720 h721 h722 h723 h724 h725 h726 h727 $$ H72
  iintro H72
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  isimp [UInt32.add_zero] at Hw0At
  ihave Hw8Out : pointsTo_u64 (frame + 120) writer8 $$ [Hw8At]
  · rw [show frame + 120 = (frame + 112) + 8 from by bv_decide]
    iexact Hw8At
  isimp [driverReaderLocals, exportFramedLocals, exportZeroLocals] at Hcont
  isimp [driverReaderLocals, exportFramedLocals, exportZeroLocals]
  iapply Hcont $$ Hr0 Hr8 Hr16 Hw0At Hw8Out H48 H56 H64 H72 H80

/-! ## `String::new` (`func110`, absolute call 112)

The generated body is a leaf: it builds the empty-string descriptor
`(capacity 0, dangling pointer 1, length 0)` in a sixteen-byte red-zone
scratch area below the current stack top (no stack-pointer update) and copies
it to the caller-provided destination. -/

set_option maxHeartbeats 4000000 in
theorem stringNew_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst stackTop : UInt32)
    (oldScratch4 oldScratch8 oldScratch12 : UInt32)
    (oldDst0 oldDst4 oldDst8 : UInt32)
    (hscratchRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hdstRoom : dst.toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 4) oldScratch4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldScratch8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldScratch12 ∗
      pointsTo_u32 (dst + 0) oldDst0 ∗
      pointsTo_u32 (dst + 4) oldDst4 ∗
      pointsTo_u32 (dst + 8) oldDst8 ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        sliceDescriptorAt ((stackTop - 16) + 4) 0 1 -∗
        pointsTo_u32 ((stackTop - 16) + 12) 0 -∗
        vecDescriptorAt dst 0 1 0 -∗
        WP (.running
          ⟨⟨[.i32 dst], [.i32 (stackTop - 16)], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 dst], [.i32 0], []⟩,
        func110, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hf40, hf41, hf42, hf43⟩ :=
    descriptorSlot32Facts (stackTop - 16) 4 16 hscratchRoom (by decide)
  obtain ⟨hf80, hf81, hf82, hf83⟩ :=
    descriptorSlot32Facts (stackTop - 16) 8 16 hscratchRoom (by decide)
  obtain ⟨hf120, hf121, hf122, hf123⟩ :=
    descriptorSlot32Facts (stackTop - 16) 12 16 hscratchRoom (by decide)
  obtain ⟨hfw0, hfw1, hfw2, hfw3, hfw4, hfw5, hfw6, hfw7⟩ :=
    descriptorSlot64Facts (stackTop - 16) 4 16 hscratchRoom (by decide)
  obtain ⟨hd00, hd01, hd02, hd03⟩ :=
    descriptorSlot32Facts dst 0 12 hdstRoom (by decide)
  obtain ⟨hd80, hd81, hd82, hd83⟩ :=
    descriptorSlot32Facts dst 8 12 hdstRoom (by decide)
  obtain ⟨hdw0, hdw1, hdw2, hdw3, hdw4, hdw5, hdw6, hdw7⟩ :=
    descriptorSlot64Facts dst 0 12 hdstRoom (by decide)
  iintro ⟨Hglobal, Hs4, Hs8, Hs12, Hd0, Hd4, Hd8, Hcont⟩
  simp only [func110]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceSub,
    List.set]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldScratch4 hf40 hf41 hf42 hf43 $$ Hs4
  iintro Hs4
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldScratch8 hf80 hf81 hf82 hf83 $$ Hs8
  iintro Hs8
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldScratch12 hf120 hf121 hf122 hf123 $$ Hs12
  iintro Hs12
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 0 hf120 hf121 hf122 hf123 $$ Hs12
  iintro Hs12
  iapply twp_store32 oldDst8 hd80 hd81 hd82 hd83 $$ Hd8
  iintro Hd8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HscratchWord : pointsTo_u64 ((stackTop - 16) + 4) (packU32 0 1) $$
      [Hs4 Hs8]
  · iapply (sliceDescriptorAt_eq_u64 ((stackTop - 16) + 4) 0 1).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hs4]
    · iexact Hs4
    rw [show ((stackTop - 16) + 4) + 4 = (stackTop - 16) + 8 from by
      bv_decide]
    iexact Hs8
  iapply twp_load64 (packU32 0 1)
    hfw0 hfw1 hfw2 hfw3 hfw4 hfw5 hfw6 hfw7 $$ HscratchWord
  iintro HscratchWord
  ihave HdstWord : pointsTo_u64 (dst + 0) (packU32 oldDst0 oldDst4) $$
      [Hd0 Hd4]
  · iapply (sliceDescriptorAt_eq_u64 (dst + 0) oldDst0 oldDst4).mp
    isimp only [sliceDescriptorAt]
    isplitl [Hd0]
    · iexact Hd0
    rw [show (dst + 0) + 4 = dst + 4 from by bv_decide]
    iexact Hd4
  iapply twp_store64 (packU32 oldDst0 oldDst4)
    hdw0 hdw1 hdw2 hdw3 hdw4 hdw5 hdw6 hdw7 $$ HdstWord
  iintro HdstWord
  ihave HscratchDesc : sliceDescriptorAt ((stackTop - 16) + 4) 0 1 $$
      [HscratchWord]
  · iapply (sliceDescriptorAt_eq_u64 ((stackTop - 16) + 4) 0 1).mpr
    iexact HscratchWord
  ihave HdstDesc : vecDescriptorAt dst 0 1 0 $$ [HdstWord Hd8]
  · ihave Hhead : sliceDescriptorAt (dst + 0) 0 1 $$ [HdstWord]
    · iapply (sliceDescriptorAt_eq_u64 (dst + 0) 0 1).mpr
      iexact HdstWord
    isimp only [sliceDescriptorAt] at Hhead
    icases Hhead with ⟨Hcap, Hdata⟩
    isimp only [vecDescriptorAt]
    isplitl [Hcap]
    · iapply pointsTo_u32_add_zero
      iexact Hcap
    isplitl [Hdata]
    · rw [show dst + 4 = (dst + 0) + 4 from by bv_decide]
      iexact Hdata
    iexact Hd8
  iapply Hcont $$ Hglobal HscratchDesc Hs12 HdstDesc

/-- Composable call rule for generated `String::new` at absolute index 112. -/
theorem stringNew_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (dst stackTop : UInt32)
    (oldScratch4 oldScratch8 oldScratch12 : UInt32)
    (oldDst0 oldDst4 oldDst8 : UInt32)
    (hscratchRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    (hdstRoom : dst.toNat + 12 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 16) + 4) oldScratch4 ∗
      pointsTo_u32 ((stackTop - 16) + 8) oldScratch8 ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldScratch12 ∗
      pointsTo_u32 (dst + 0) oldDst0 ∗
      pointsTo_u32 (dst + 4) oldDst4 ∗
      pointsTo_u32 (dst + 8) oldDst8 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        sliceDescriptorAt ((stackTop - 16) + 4) 0 1 -∗
        pointsTo_u32 ((stackTop - 16) + 12) 0 -∗
        vecDescriptorAt dst 0 1 0 -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 dst :: stack },
        .call 112 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hs4, Hs8, Hs12, Hd0, Hd4, Hd8, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 112 func110Def
      (by decide) stringNew_index $$ Hruntime
  iintro Hruntime
  simp [func110Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := stringNew_body_twp (α := α)
    dst stackTop oldScratch4 oldScratch8 oldScratch12 oldDst0 oldDst4
    oldDst8 hscratchRoom hdstRoom (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  ihave Hd0At : pointsTo_u32 (dst + 0) oldDst0 $$ [Hd0]
  · rw [UInt32.add_zero]
    iexact Hd0
  iapply Hbody
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hs4]
  · iexact Hs4
  isplitl [Hs8]
  · iexact Hs8
  isplitl [Hs12]
  · iexact Hs12
  isplitl [Hd0At]
  · iexact Hd0At
  isplitl [Hd4]
  · iexact Hd4
  isplitl [Hd8]
  · iexact Hd8
  iintro Hglobal HscratchDesc Hs12 HdstDesc
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal HscratchDesc Hs12 HdstDesc

/-! ## Successful read-result check

After `read_line` returns, the driver inspects the one-byte discriminant it
wrote at `frame + 140`.  The generated success path requires the byte to be
exactly `4`; any other value falls through to the panic formatter at absolute
call 241.  This rule covers the successful branch only, so the discriminant
byte appears as an explicit `4` in the precondition. -/
set_option maxHeartbeats 4000000 in
theorem driver_read_check_success_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame : UInt32)
    (hframeRoom : frame.toNat + 384 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (frame + 140) (DFrac.own 1) (some (4 : UInt8)) ∗
      (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (frame + 140) (DFrac.own 1) (some (4 : UInt8)) -∗
        WP (.running
          ⟨⟨[], driverCheckLocals frame, []⟩,
            driverAfterReadCheck, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], driverReaderLocals frame, []⟩,
        driverAfterReadLine, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have h140 : (frame + (140 : UInt32)).toNat = frame.toNat + 140 :=
    (descriptorSlot32Facts frame 140 384 hframeRoom (by decide)).1
  iintro ⟨Hflag, Hcont⟩
  rw [driverAfterReadLine_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load8U_owned (4 : UInt8) h140 $$ Hflag
  iintro Hflag
  rw [show ((4 : UInt8).toUInt32) = (4 : UInt32) from by decide]
  iapply twp_localSet rfl
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (4 : UInt32) &&& 255 = 4 from by decide]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (4 : UInt32) &&& 255 = 4 from by decide]
  iapply twp_eq (result := 1) (by decide)
  iapply twp_localSet rfl
  rw [driverAtReadCheck_eq]
  iapply twp_block
  iapply twp_const
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 from by decide]
  iapply twp_selectI32 (selected := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 from by decide]
  iapply twp_eqz (result := 1) (by decide)
  iapply twp_brIf (by decide) rfl
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  isimp [driverCheckLocals, driverReaderLocals, exportFramedLocals,
    exportZeroLocals] at Hcont
  isimp [driverCheckLocals, driverReaderLocals, exportFramedLocals,
    exportZeroLocals]
  iapply Hcont $$ Hflag

/-! ## Pure argument-preparation segments -/

/-- Exact generated argument preparation for the `read_line` call: pushes the
read-result slot, the line buffer, and the `BufReader`, stopping at the
generated `.call 39`. -/
theorem driver_after_stringNew_to_readLine_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[], driverReaderLocals frame,
          [.i32 (128 + frame), .i32 (48 + frame), .i32 (140 + frame)]⟩,
        driverAtReadLine, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[], driverReaderLocals frame, []⟩,
        driverAfterStringNew, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro Hcont
  rw [driverAfterStringNew_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iexact Hcont

/-- Exact generated argument preparation for the `String::deref` call at
absolute index 121, stopping at the generated `.call 121`. -/
theorem driver_after_readCheck_to_stringDeref_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[], driverCheckLocals frame,
          [.i32 (128 + frame), .i32 (24 + frame)]⟩,
        driverAtStringDeref, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[], driverCheckLocals frame, []⟩,
        driverAfterReadCheck, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro Hcont
  rw [driverAfterReadCheck_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iexact Hcont

/-! ## Composed proven stretches

Everything between the constructor return and the `read_line` call is now
proven, as is everything between the `read_line` return and the
`String::deref` call.  The remaining boundaries on the input path are exactly
the generated `.call 137` (buffered constructor internals, allocator-owned),
`.call 39` (the buffered read chain down to the `stdio.read` import),
`.call 121` (already available as `stringDeref_call_twp`), and the
split/map/collect calls at absolute 84, 92, and 93. -/

/-! Proven driver stretch from the instruction after `.call 137` to the exact
generated `.call 39`, running the verified `String::new` in between. -/
set_option maxHeartbeats 6000000 in
theorem driver_after_bufCtor_to_readLine_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame : UInt32)
    (reader0 reader8 writer0 writer8 : UInt64) (reader16 : UInt32)
    (old48 old56 old72 old80 : UInt64) (old64 : UInt32)
    (oldScratch4 oldScratch8 oldScratch12 : UInt32)
    (oldLine0 oldLine4 oldLine8 : UInt32)
    (hframeRoom : frame.toNat + 384 ≤ UInt32.size)
    (hscratchRoom : (frame - 16).toNat + 16 ≤ UInt32.size)
    (hlineRoom : (128 + frame).toNat + 12 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u64 (frame + 92) reader0 ∗
      pointsTo_u64 (frame + 100) reader8 ∗
      pointsTo_u32 (frame + 108) reader16 ∗
      pointsTo_u64 (frame + 112) writer0 ∗
      pointsTo_u64 (frame + 120) writer8 ∗
      pointsTo_u64 (frame + 48) old48 ∗
      pointsTo_u64 (frame + 56) old56 ∗
      pointsTo_u32 (frame + 64) old64 ∗
      pointsTo_u64 (frame + 72) old72 ∗
      pointsTo_u64 (frame + 80) old80 ∗
      pointsTo_u32 ((frame - 16) + 4) oldScratch4 ∗
      pointsTo_u32 ((frame - 16) + 8) oldScratch8 ∗
      pointsTo_u32 ((frame - 16) + 12) oldScratch12 ∗
      pointsTo_u32 ((128 + frame) + 0) oldLine0 ∗
      pointsTo_u32 ((128 + frame) + 4) oldLine4 ∗
      pointsTo_u32 ((128 + frame) + 8) oldLine8 ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 frame) -∗
        pointsTo_u64 (frame + 92) reader0 -∗
        pointsTo_u64 (frame + 100) reader8 -∗
        pointsTo_u32 (frame + 108) reader16 -∗
        pointsTo_u64 (frame + 112) writer0 -∗
        pointsTo_u64 (frame + 120) writer8 -∗
        pointsTo_u64 (frame + 48) reader0 -∗
        pointsTo_u64 (frame + 56) reader8 -∗
        pointsTo_u32 (frame + 64) reader16 -∗
        pointsTo_u64 (frame + 72) writer0 -∗
        pointsTo_u64 (frame + 80) writer8 -∗
        sliceDescriptorAt ((frame - 16) + 4) 0 1 -∗
        pointsTo_u32 ((frame - 16) + 12) 0 -∗
        vecDescriptorAt (128 + frame) 0 1 0 -∗
        WP (.running
          ⟨⟨[], driverReaderLocals frame,
              [.i32 (128 + frame), .i32 (48 + frame), .i32 (140 + frame)]⟩,
            driverAtReadLine, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], exportFramedLocals frame, []⟩,
        driverAfterBufCtor, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hr0, Hr8, Hr16, Hw0, Hw8, H48, H56, H64, H72,
    H80, Hs4, Hs8, Hs12, Hl0, Hl4, Hl8, Hcont⟩
  have HS1 := driver_after_bufCtor_to_stringNew_twp (α := α)
    frame reader0 reader8 writer0 writer8 reader16
    old48 old56 old72 old80 old64 hframeRoom
    (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply HS1
  isplitl [Hr0]
  · iexact Hr0
  isplitl [Hr8]
  · iexact Hr8
  isplitl [Hr16]
  · iexact Hr16
  isplitl [Hw0]
  · iexact Hw0
  isplitl [Hw8]
  · iexact Hw8
  isplitl [H48]
  · iexact H48
  isplitl [H56]
  · iexact H56
  isplitl [H64]
  · iexact H64
  isplitl [H72]
  · iexact H72
  isplitl [H80]
  · iexact H80
  iintro Hr0 Hr8 Hr16 Hw0 Hw8 H48 H56 H64 H72 H80
  rw [driverAtStringNew_eq]
  have Hcall := stringNew_call_twp (α := α)
    (128 + frame) frame oldScratch4 oldScratch8 oldScratch12
    oldLine0 oldLine4 oldLine8 hscratchRoom hlineRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals := ⟨[], driverReaderLocals frame, []⟩)
    (stack := []) (code := driverAfterStringNew) (arity := 0)
    (remainder := []) (controls := []) (calls := calls)
  iapply Hcall
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hs4]
  · iexact Hs4
  isplitl [Hs8]
  · iexact Hs8
  isplitl [Hs12]
  · iexact Hs12
  isplitl [Hl0]
  · iexact Hl0
  isplitl [Hl4]
  · iexact Hl4
  isplitl [Hl8]
  · iexact Hl8
  iintro Hruntime Hglobal HscratchDesc Hs12 Hline
  have HS2 := driver_after_stringNew_to_readLine_twp (α := α)
    frame (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply HS2
  iapply Hcont $$ Hruntime Hglobal Hr0 Hr8 Hr16 Hw0 Hw8 H48 H56 H64 H72
    H80 HscratchDesc Hs12 Hline

/-- Proven driver stretch from the instruction after `.call 39` to the exact
generated `.call 121`, discharging the successful read-result check. -/
theorem driver_after_readLine_to_stringDeref_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (frame : UInt32)
    (hframeRoom : frame.toNat + 384 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (frame + 140) (DFrac.own 1) (some (4 : UInt8)) ∗
      (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (frame + 140) (DFrac.own 1) (some (4 : UInt8)) -∗
        WP (.running
          ⟨⟨[], driverCheckLocals frame,
              [.i32 (128 + frame), .i32 (24 + frame)]⟩,
            driverAtStringDeref, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], driverReaderLocals frame, []⟩,
        driverAfterReadLine, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hflag, Hcont⟩
  have Hcheck := driver_read_check_success_twp (α := α)
    frame hframeRoom (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hcheck
  isplitl [Hflag]
  · iexact Hflag
  iintro Hflag
  have Hargs := driver_after_readCheck_to_stringDeref_twp (α := α)
    frame (s := s) (E := E) (Φ := Φ) (calls := calls)
  iapply Hargs
  iapply Hcont $$ Hflag

end Project.Mergesort.DriverInputProof
