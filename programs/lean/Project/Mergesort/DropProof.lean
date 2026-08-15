import Project.Mergesort.Machine
import Project.Mergesort.FormatProof
import Project.Mergesort.RangeProof

/-!
# Generated destructor wrappers of the exported driver

The exported driver releases its resources through five generated `Drop`
implementations: local `func62` (`String`), `func68` (`Vec<u64>`), `func74`
(`vec::IntoIter<u64>`), `func78` (`BufReader<StdinRaw>`), and `func79`
(`BufWriter<StdoutRaw>`).  Their call graph (local indices; the generated
call immediate is two larger because of the two StdIO imports) is:

* `func62 → func63 → { func66 ; func67 → func70 → func111 }` — drop the
  element-in-place loop, then release the byte buffer through the `RawVec`
  deallocator;
* `func68 → { func69 ; func14 → func71 → func111 }` — the `u64` counterpart;
* `func74 → func75 → { func107 ; loop ; func61 → func13 }` — read the
  remaining-slice descriptor, drop the remainder in place, release the
  backing buffer;
* `func78 → func76 → func56 → func57` — release the internal read buffer;
* `func79 → { func80 ; func63 }` — flush-on-drop guard, then drop the
  internal `Vec<u8>` like a `String`.

Every one of these chains ends either in the dlmalloc free path (`func111`
and `func57` reach local `func113`, which forwards to the unproven `func129`
deallocator) or in the host write import (`func80`'s flush).  Following the
`.call 107` constructor contract of `DriverSortProof`, this file therefore
stops exactly at those generated call boundaries: each rule discharges the
wrapper's own instructions and hands the client a continuation at the exact
inner call, so no allocator or host effect is ever hidden or assumed.
-/

namespace Project.Mergesort.DropProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.FormatProof
open Project.Mergesort.RangeProof

/-! ## Local function indices of the interior destructor helpers -/

theorem dropStringFields_index : «module».funcs[63]? = some func63Def := by rfl
theorem dropElementsU8_index : «module».funcs[66]? = some func66Def := by rfl
theorem dropElementsU64_index : «module».funcs[69]? = some func69Def := by rfl
theorem dropStringBuffer_index : «module».funcs[67]? = some func67Def := by rfl
theorem rawVecDeallocU8_index : «module».funcs[70]? = some func70Def := by rfl
theorem rawVecDeallocU64_index : «module».funcs[71]? = some func71Def := by rfl
theorem dropVecBuffer_index : «module».funcs[14]? = some func14Def := by rfl
theorem dropIntoIterBox_index : «module».funcs[61]? = some func61Def := by rfl
theorem dropBufReaderInner_index : «module».funcs[76]? = some func76Def := by rfl
theorem dropBufReaderBuffer_index : «module».funcs[56]? = some func56Def := by rfl

/-! ## Seam programs

Each `…Seam` is the exact generated remainder of a destructor body starting
at its first interior call.  The `_eq` lemmas pin the split against the
generated instruction lists. -/

def dropStringSeam : Program := [.call 65, .ret]
def dropStringFieldsSeam : Program := [.call 68, .localGet 0, .call 69, .ret]
def dropStringBufferSeam : Program := [.call 72, .ret]
def rawVecDeallocSeam : Program := [.call 113, .ret]
def dropVecU64Seam : Program := [.call 71, .localGet 0, .call 16, .ret]
def dropVecBufferSeam : Program := [.call 73, .ret]
def dropIntoIterU64Seam : Program := [.call 77, .ret]
def dropIntoIterBoxSeam : Program := [.call 15, .ret]
def dropBufReaderSeam : Program := [.call 78, .ret]
def dropBufReaderInnerSeam : Program := [.call 58, .ret]
def dropBufReaderBufferSeam : Program := [.call 59, .ret]
def dropBufWriterSeam : Program := [.call 82, .localGet 0, .call 65, .ret]

theorem func62_seam_eq : func62 = .localGet 0 :: dropStringSeam := rfl
theorem func63_seam_eq : func63 = .localGet 0 :: dropStringFieldsSeam := rfl
theorem func67_seam_eq : func67 = .localGet 0 :: dropStringBufferSeam := rfl
theorem func70_seam_eq :
    func70 = .const 1 :: .localSet 1 :: .localGet 0 :: .localGet 1 ::
      .localGet 1 :: rawVecDeallocSeam := rfl
theorem func71_seam_eq :
    func71 = .const 8 :: .localSet 1 :: .localGet 0 :: .localGet 1 ::
      .localGet 1 :: rawVecDeallocSeam := rfl
theorem func68_seam_eq : func68 = .localGet 0 :: dropVecU64Seam := rfl
theorem func14_seam_eq : func14 = .localGet 0 :: dropVecBufferSeam := rfl
theorem func74_seam_eq : func74 = .localGet 0 :: dropIntoIterU64Seam := rfl
theorem func61_seam_eq : func61 = .localGet 0 :: dropIntoIterBoxSeam := rfl
theorem func78_seam_eq : func78 = .localGet 0 :: dropBufReaderSeam := rfl
theorem func76_seam_eq : func76 = .localGet 0 :: dropBufReaderInnerSeam := rfl
theorem func56_seam_eq : func56 = .localGet 0 :: dropBufReaderBufferSeam := rfl
theorem func79_seam_eq : func79 = .localGet 0 :: dropBufWriterSeam := rfl

/-! ## Shared forwarder shapes

Every wrapper above either stages only its single pointer argument, or (for
the two `RawVec` deallocators) additionally materializes the constant layout
pair.  The two private lemmas below discharge exactly those prefixes. -/

/-- A generated forwarder body: reload the single pointer parameter, then
continue at the interior call. -/
private theorem forward_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32) {seam : Program}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        seam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        .localGet 0 :: seam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  iapply twp_localGet rfl
  iexact Hcont

/-- A generated `RawVec` deallocator body: stage `(selfPtr, layout, layout)`
for the shared deallocation routine at absolute call 113, then stop. -/
private theorem rawVecDealloc_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr layout : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [.i32 layout],
          [.i32 layout, .i32 layout, .i32 selfPtr]⟩,
        rawVecDeallocSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [.i32 0], []⟩,
        .const layout :: .localSet 1 :: .localGet 0 :: .localGet 1 ::
          .localGet 1 :: rawVecDeallocSeam,
        0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  isimp
  iexact Hcont

/-! ## Body seam rules -/

/-- Exact body prefix of local `func62` (`String::drop`), ending at its
forward to the shared field destructor `func63` (absolute call 65). -/
theorem dropString_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropStringSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func62, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func62_seam_eq]
  exact forward_body_twp selfPtr

/-- Exact body prefix of local `func63` (shared `String`/`Vec<u8>` field
destructor), ending at the element loop `func66` (absolute call 68). -/
theorem dropStringFields_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropStringFieldsSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func63, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func63_seam_eq]
  exact forward_body_twp selfPtr

/-- Exact body prefix of local `func67`, ending at the byte `RawVec`
deallocator `func70` (absolute call 72). -/
theorem dropStringBuffer_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropStringBufferSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func67, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func67_seam_eq]
  exact forward_body_twp selfPtr

/-- Exact body prefix of local `func70` (`RawVec<u8>` deallocator shim),
ending at the shared deallocation routine `func111` (absolute call 113) with
alignment and element size one. -/
theorem rawVecDeallocU8_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [.i32 1], [.i32 1, .i32 1, .i32 selfPtr]⟩,
        rawVecDeallocSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [.i32 0], []⟩,
        func70, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func70_seam_eq]
  exact rawVecDealloc_body_twp selfPtr 1

/-- Exact body prefix of local `func71` (`RawVec<u64>` deallocator shim),
ending at the shared deallocation routine `func111` (absolute call 113) with
alignment and element size eight. -/
theorem rawVecDeallocU64_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [.i32 8], [.i32 8, .i32 8, .i32 selfPtr]⟩,
        rawVecDeallocSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [.i32 0], []⟩,
        func71, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func71_seam_eq]
  exact rawVecDealloc_body_twp selfPtr 8

/-- Exact body prefix of local `func68` (`Vec<u64>::drop`), ending at the
element loop `func69` (absolute call 71); the seam retains the buffer
release at absolute call 16. -/
theorem dropVecU64_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropVecU64Seam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func68, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func68_seam_eq]
  exact forward_body_twp selfPtr

/-- Exact body prefix of local `func14`, ending at the `u64` `RawVec`
deallocator `func71` (absolute call 73). -/
theorem dropVecBuffer_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropVecBufferSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func14, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func14_seam_eq]
  exact forward_body_twp selfPtr

/-- Exact body prefix of local `func74` (`vec::IntoIter<u64>::drop`), ending
at its forward to the iterator destructor `func75` (absolute call 77). -/
theorem dropIntoIterU64_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropIntoIterU64Seam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func74, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func74_seam_eq]
  exact forward_body_twp selfPtr

/-- Exact body prefix of local `func61` (the iterator's buffer release
guard), ending at `func13` (absolute call 15). -/
theorem dropIntoIterBox_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropIntoIterBoxSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func61, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func61_seam_eq]
  exact forward_body_twp selfPtr

/-- Exact body prefix of local `func78` (`BufReader::drop`), ending at its
forward to `func76` (absolute call 78). -/
theorem dropBufReader_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropBufReaderSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func78, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func78_seam_eq]
  exact forward_body_twp selfPtr

/-- Exact body prefix of local `func76`, ending at the buffer destructor
`func56` (absolute call 58). -/
theorem dropBufReaderInner_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropBufReaderInnerSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func76, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func76_seam_eq]
  exact forward_body_twp selfPtr

/-- Exact body prefix of local `func56`, ending at `func57` (absolute call
59), which releases the internal read buffer through absolute call 115. -/
theorem dropBufReaderBuffer_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropBufReaderBufferSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func56, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func56_seam_eq]
  exact forward_body_twp selfPtr

/-- Exact body prefix of local `func79` (`BufWriter::drop`), ending at the
flush-on-drop guard `func80` (absolute call 82); the seam retains the shared
field destructor at absolute call 65. -/
theorem dropBufWriter_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
        dropBufWriterSeam, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [], []⟩,
        func79, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func79_seam_eq]
  exact forward_body_twp selfPtr

/-! ## The element-drop loops

Local `func66` (`String`/`Vec<u8>`) and `func69` (`Vec<u64>`) are the
generated element-in-place destructor loops.  For `u8`/`u64` elements
dropping is a no-op, so at optimization level zero the generated code merely
counts a scratch slot in the red zone below the shadow stack pointer from
zero up to the vector length.  Unlike the destructor frames around them they
never move the stack pointer: they only write the scratch word at
`(stackTop - 16) + 12`.  The two bodies are literally identical, so a single
total proof serves both call rules. -/

theorem func69_eq_func66 : func69 = func66 := rfl

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

private theorem twp_dropValue
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value} {value : Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    WP (.running ⟨⟨params, localValues, values⟩,
      code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨⟨params, localValues, value :: values⟩,
      .drop :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.drop)

private theorem ofNat_succ_u32 (i : Nat) :
    UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
  rw [UInt32.ofNat_add]
  rfl

/-- One symbolic pass over the generated count-up loop shared by `func66`
and `func69`: from scratch value `i` with `i + k = len.toNat`, the loop
terminates with the scratch slot equal to `len`. -/
private theorem dropElements_loop_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr stackTop len : UInt32)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame}
    (k : Nat) :
    ∀ i : Nat, i + k = len.toNat →
    pointsTo_u32 ((stackTop - 16) + 12) (UInt32.ofNat i) ∗
      (pointsTo_u32 ((stackTop - 16) + 12) len -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [.i32 (stackTop - 16), .i32 len], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [.i32 (stackTop - 16), .i32 len], []⟩,
        [.localGet 1, .load32 12, .localGet 2, .eq, .const 1, .and,
         .br_if 1, .localGet 1, .localGet 1, .load32 12, .const 1, .add,
         .store32 12, .br 0],
        0, [],
        [{ kind := .loop, paramArity := 0, resultArity := 0,
           body := [.localGet 1, .load32 12, .localGet 2, .eq, .const 1,
             .and, .br_if 1, .localGet 1, .localGet 1, .load32 12, .const 1,
             .add, .store32 12, .br 0],
           continuation := [], belowStack := [] },
         { kind := .block, paramArity := 0, resultArity := 0,
           body := [.loop 0 0 [.localGet 1, .load32 12, .localGet 2, .eq,
             .const 1, .and, .br_if 1, .localGet 1, .localGet 1, .load32 12,
             .const 1, .add, .store32 12, .br 0]],
           continuation := [.ret], belowStack := [] }],
        calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hf0, hf1, hf2, hf3⟩ :=
    descriptorSlot32Facts (stackTop - 16) 12 16 hframeRoom (by decide)
  induction k with
  | zero =>
    intro i hi
    have hieq : i = len.toNat := by omega
    subst hieq
    iintro ⟨Hscratch, Hdone⟩
    iapply twp_localGet rfl
    iapply twp_load32 (UInt32.ofNat len.toNat) hf0 hf1 hf2 hf3 $$ Hscratch
    iintro Hscratch
    iapply twp_localGet rfl
    iapply twp_eq (result := 1) (by simp [UInt32.ofNat_toNat])
    iapply twp_const
    iapply twp_and
    rw [show (1 : UInt32) &&& 1 = 1 by decide]
    iapply twp_brIf (by decide) rfl
    simp only [List.take_zero, List.nil_append]
    ihave Hscratch' : pointsTo_u32 ((stackTop - 16) + 12) len $$ [Hscratch]
    · rw [UInt32.ofNat_toNat]
      iexact Hscratch
    iapply Hdone $$ Hscratch'
  | succ k ih =>
    intro i hi
    have hlt : i < len.toNat := by omega
    have hsize : i < UInt32.size := by
      have := len.toNat_lt_size
      omega
    have hne : UInt32.ofNat i ≠ len := by
      intro heq
      have htoNat := congrArg UInt32.toNat heq
      rw [UInt32.toNat_ofNat_of_lt' hsize] at htoNat
      omega
    iintro ⟨Hscratch, Hdone⟩
    iapply twp_localGet rfl
    iapply twp_load32 (UInt32.ofNat i) hf0 hf1 hf2 hf3 $$ Hscratch
    iintro Hscratch
    iapply twp_localGet rfl
    iapply twp_eq (result := 0) (by simp [hne])
    iapply twp_const
    iapply twp_and
    rw [show (0 : UInt32) &&& 1 = 0 by decide]
    iapply twp_brIfZero
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_load32 (UInt32.ofNat i) hf0 hf1 hf2 hf3 $$ Hscratch
    iintro Hscratch
    iapply twp_const
    iapply twp_add
    iapply twp_store32 (UInt32.ofNat i) hf0 hf1 hf2 hf3 $$ Hscratch
    iintro Hscratch
    iapply twp_br rfl
    simp only [List.take_zero, List.nil_append]
    ihave Hscratch' : pointsTo_u32 ((stackTop - 16) + 12)
        (UInt32.ofNat (i + 1)) $$ [Hscratch]
    · rw [show UInt32.ofNat (i + 1) = 1 + UInt32.ofNat i from by
        rw [← ofNat_succ_u32]; exact UInt32.add_comm _ _]
      rw [show (12 : UInt32) = UInt32.ofNat 12 by decide]
      iexact Hscratch
    have H := ih (i + 1) (by omega)
    iapply H
    isplitl [Hscratch']
    · iexact Hscratch'
    iexact Hdone

/-- Exact total body rule for the shared element-drop loop `func66`
(`func69` is literally the same program).  The self descriptor is read but
preserved; the loop leaves the red-zone scratch word below the shadow stack
pointer equal to the element count. -/
theorem dropElements_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr stackTop data len oldScratch : UInt32)
    (hselfRoom : selfPtr.toNat + 12 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (selfPtr + 4) data ∗
      pointsTo_u32 (selfPtr + 8) len ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldScratch ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (selfPtr + 4) data -∗
        pointsTo_u32 (selfPtr + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 12) len -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [.i32 (stackTop - 16), .i32 len], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [.i32 0, .i32 0], []⟩,
        func66, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨hs40, hs41, hs42, hs43⟩ :=
    descriptorSlot32Facts selfPtr 4 12 hselfRoom (by decide)
  obtain ⟨hs80, hs81, hs82, hs83⟩ :=
    descriptorSlot32Facts selfPtr 8 12 hselfRoom (by decide)
  obtain ⟨hf0, hf1, hf2, hf3⟩ :=
    descriptorSlot32Facts (stackTop - 16) 12 16 hframeRoom (by decide)
  iintro ⟨Hglobal, Hdata, Hlen, Hscratch, Hdone⟩
  simp only [func66]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_load32 data hs40 hs41 hs42 hs43 $$ Hdata
  iintro Hdata
  iapply twp_dropValue
  iapply twp_localGet rfl
  iapply twp_load32 len hs80 hs81 hs82 hs83 $$ Hlen
  iintro Hlen
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 oldScratch hf0 hf1 hf2 hf3 $$ Hscratch
  iintro Hscratch
  iapply twp_block
  iapply twp_loop
  isimp
  have Hloop := dropElements_loop_twp (α := α) selfPtr stackTop len
    hframeRoom (s := s) (E := E) (Φ := Φ) (calls := calls)
    len.toNat 0 (by omega)
  iapply Hloop
  isplitl [Hscratch]
  · iexact Hscratch
  iintro Hscratch
  iapply Hdone $$ Hglobal Hdata Hlen Hscratch

/-- The shared loop rule specialized to the generated `func69`. -/
theorem dropElementsU64_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr stackTop data len oldScratch : UInt32)
    (hselfRoom : selfPtr.toNat + 12 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (selfPtr + 4) data ∗
      pointsTo_u32 (selfPtr + 8) len ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldScratch ∗
      (globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (selfPtr + 4) data -∗
        pointsTo_u32 (selfPtr + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 12) len -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [.i32 (stackTop - 16), .i32 len], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 selfPtr], [.i32 0, .i32 0], []⟩,
        func69, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  rw [func69_eq_func66]
  exact dropElements_body_twp selfPtr stackTop data len oldScratch
    hselfRoom hframeRoom

/-- Composable total call rule for the `u8` element-drop loop at absolute
index 68.  It is a complete contract: the loop returns to the caller with
the descriptor preserved and only the red-zone scratch word changed. -/
theorem dropElementsU8_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr stackTop data len oldScratch : UInt32)
    (hselfRoom : selfPtr.toNat + 12 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (selfPtr + 4) data ∗
      pointsTo_u32 (selfPtr + 8) len ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldScratch ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (selfPtr + 4) data -∗
        pointsTo_u32 (selfPtr + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 12) len -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 68 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hdata, Hlen, Hscratch, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 68 func66Def
      (by decide) dropElementsU8_index $$ Hruntime
  iintro Hruntime
  simp [func66Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := dropElements_body_twp (α := α)
    selfPtr stackTop data len oldScratch hselfRoom hframeRoom
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
  isplitl [Hdata]
  · iexact Hdata
  isplitl [Hlen]
  · iexact Hlen
  isplitl [Hscratch]
  · iexact Hscratch
  iintro Hglobal Hdata Hlen Hscratch
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hdata Hlen Hscratch

/-- Composable total call rule for the `u64` element-drop loop at absolute
index 71. -/
theorem dropElementsU64_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr stackTop data len oldScratch : UInt32)
    (hselfRoom : selfPtr.toNat + 12 ≤ UInt32.size)
    (hframeRoom : (stackTop - 16).toNat + 16 ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (selfPtr + 4) data ∗
      pointsTo_u32 (selfPtr + 8) len ∗
      pointsTo_u32 ((stackTop - 16) + 12) oldScratch ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (selfPtr + 4) data -∗
        pointsTo_u32 (selfPtr + 8) len -∗
        pointsTo_u32 ((stackTop - 16) + 12) len -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 71 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hdata, Hlen, Hscratch, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 71 func69Def
      (by decide) dropElementsU64_index $$ Hruntime
  iintro Hruntime
  simp [func69Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := dropElementsU64_body_twp (α := α)
    selfPtr stackTop data len oldScratch hselfRoom hframeRoom
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
  isplitl [Hdata]
  · iexact Hdata
  isplitl [Hlen]
  · iexact Hlen
  isplitl [Hscratch]
  · iexact Hscratch
  iintro Hglobal Hdata Hlen Hscratch
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hglobal Hdata Hlen Hscratch

/-! ## Composable call rules

Each rule enters the generated destructor from an arbitrary caller and stops
at the wrapper's seam.  The continuation receives the exact callee-frame
state (with the caller frame pushed), so a client discharges it with the
interior call rules above (or, at the deallocator/flush boundaries, with the
corresponding linear contract) and finishes with
`twp_returnFromCallExplicit`. -/

/-- Composable total call rule for `String::drop` at absolute index 64. -/
theorem dropString_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropStringSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 64 func62Def
      (by decide) dropString_index $$ Hruntime
  iintro Hruntime
  simp [func62Def, Function.toLocals, Function.numParams]
  have Hbody := dropString_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for the shared `String`/`Vec<u8>` field
destructor at absolute index 65. -/
theorem dropStringFields_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropStringFieldsSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 65 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 65 func63Def
      (by decide) dropStringFields_index $$ Hruntime
  iintro Hruntime
  simp [func63Def, Function.toLocals, Function.numParams]
  have Hbody := dropStringFields_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for the byte-buffer destructor at absolute
index 69. -/
theorem dropStringBuffer_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropStringBufferSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 69 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 69 func67Def
      (by decide) dropStringBuffer_index $$ Hruntime
  iintro Hruntime
  simp [func67Def, Function.toLocals, Function.numParams]
  have Hbody := dropStringBuffer_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for the byte `RawVec` deallocator shim at
absolute index 72.  The continuation sits at the shared deallocation routine
(absolute call 113) with `(selfPtr, 1, 1)` staged. -/
theorem rawVecDeallocU8_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [.i32 1], [.i32 1, .i32 1, .i32 selfPtr]⟩,
            rawVecDeallocSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 72 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 72 func70Def
      (by decide) rawVecDeallocU8_index $$ Hruntime
  iintro Hruntime
  simp [func70Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := rawVecDeallocU8_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for the `u64` `RawVec` deallocator shim at
absolute index 73.  The continuation sits at the shared deallocation routine
(absolute call 113) with `(selfPtr, 8, 8)` staged. -/
theorem rawVecDeallocU64_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [.i32 8], [.i32 8, .i32 8, .i32 selfPtr]⟩,
            rawVecDeallocSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 73 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 73 func71Def
      (by decide) rawVecDeallocU64_index $$ Hruntime
  iintro Hruntime
  simp [func71Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := rawVecDeallocU64_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for `Vec<u64>::drop` at absolute index 70. -/
theorem dropVecU64_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropVecU64Seam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 70 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 70 func68Def
      (by decide) dropVecU64_index $$ Hruntime
  iintro Hruntime
  simp [func68Def, Function.toLocals, Function.numParams]
  have Hbody := dropVecU64_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for the `u64` buffer release forward at
absolute index 16. -/
theorem dropVecBuffer_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropVecBufferSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 16 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 16 func14Def
      (by decide) dropVecBuffer_index $$ Hruntime
  iintro Hruntime
  simp [func14Def, Function.toLocals, Function.numParams]
  have Hbody := dropVecBuffer_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for `vec::IntoIter<u64>::drop` at absolute
index 76. -/
theorem dropIntoIterU64_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropIntoIterU64Seam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 76 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 76 func74Def
      (by decide) dropIntoIterU64_index $$ Hruntime
  iintro Hruntime
  simp [func74Def, Function.toLocals, Function.numParams]
  have Hbody := dropIntoIterU64_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for the iterator's buffer release guard at
absolute index 63. -/
theorem dropIntoIterBox_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropIntoIterBoxSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 63 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 63 func61Def
      (by decide) dropIntoIterBox_index $$ Hruntime
  iintro Hruntime
  simp [func61Def, Function.toLocals, Function.numParams]
  have Hbody := dropIntoIterBox_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for `BufReader::drop` at absolute index
80. -/
theorem dropBufReader_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropBufReaderSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 80 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 80 func78Def
      (by decide) dropBufReader_index $$ Hruntime
  iintro Hruntime
  simp [func78Def, Function.toLocals, Function.numParams]
  have Hbody := dropBufReader_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for the reader's interior destructor at
absolute index 78. -/
theorem dropBufReaderInner_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropBufReaderInnerSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 78 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 78 func76Def
      (by decide) dropBufReaderInner_index $$ Hruntime
  iintro Hruntime
  simp [func76Def, Function.toLocals, Function.numParams]
  have Hbody := dropBufReaderInner_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for the reader's buffer destructor at
absolute index 58. -/
theorem dropBufReaderBuffer_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropBufReaderBufferSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 58 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 58 func56Def
      (by decide) dropBufReaderBuffer_index $$ Hruntime
  iintro Hruntime
  simp [func56Def, Function.toLocals, Function.numParams]
  have Hbody := dropBufReaderBuffer_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

/-- Composable total call rule for `BufWriter::drop` at absolute index 81.
The seam keeps the generated flush-on-drop guard (absolute call 82, which
reaches the host write import) and the following field destructor (absolute
call 65) explicit. -/
theorem dropBufWriter_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (selfPtr : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨⟨[.i32 selfPtr], [], [.i32 selfPtr]⟩,
            dropBufWriterSeam, 0, [], [],
            { locals := { callerLocals with values := stack }
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls } :: calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := .i32 selfPtr :: stack },
        .call 81 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 81 func79Def
      (by decide) dropBufWriter_index $$ Hruntime
  iintro Hruntime
  simp [func79Def, Function.toLocals, Function.numParams]
  have Hbody := dropBufWriter_body_twp (α := α) selfPtr
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  iapply Hcont $$ Hruntime

end Project.Mergesort.DropProof
