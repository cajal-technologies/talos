import Project.Mergesort.FormatProof
import Project.Mergesort.MemoryCopyProof
import Project.Mergesort.MemoryFillProof

/-!
# Generated buffered writer

The fallback formatter reaches the buffered writer through the static
`&dyn fmt::Write` vtable at 1048856: slot `+12` holds table index 5, whose
element is absolute function 48 (local `func46`).  That adapter forwards to
local `func35`, which either appends to the `BufWriter` buffer (fast path,
local `func41`, one `memory.copy`) or flushes through the host import (slow
path, local `func39`).  This file verifies the complete non-flush path:
under the byte-level `bufWriterAt` descriptor no host call happens, the
bytes are appended, and the recorded length grows by the string length.

The flush path is kept an explicit boundary: its branch is never entered
because every contract here carries the generated fast-path guard
`strLen < capacity - len` as a hypothesis.
-/

namespace Project.Mergesort.BufferedWriterProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.FormatProof
open Project.Mergesort.MemoryCopyProof
open Project.Mergesort.MemoryFillProof

theorem bufferAppend_index : «module».funcs[41]? = some func41Def := by rfl

theorem bufferWrite_index : «module».funcs[35]? = some func35Def := by rfl

theorem writeStrAdapter_index : «module».funcs[46]? = some func46Def := by rfl

/-! ## The instantiated indirect-call table

The module owns one 44-entry funcref table.  Its active element segment
writes absolute function indices starting at slot 1; slot 0 stays null. -/

def mergesortTable : TableInst :=
  .funcref none ::
    ([211, 235, 252, 62, 48, 46, 49, 34, 181, 122, 123, 201, 202, 160,
      152, 192, 191, 199, 189, 186, 184, 185, 153, 183, 195, 194, 198,
      180, 190, 196, 197, 188, 187, 179, 242, 243, 212, 238, 239, 248,
      219, 246, 254].map fun n => Value.funcref (some n))

/-- Slot 5 is the `write_str` entry of the static writer vtable. -/
theorem mergesortTable_writeStr :
    mergesortTable[5]? = some (.funcref (some 48)) := by rfl

/-- Slot 1 is the `<u64 as Display>::fmt` formatter used by the driver's
argument descriptor. -/
theorem mergesortTable_displayU64 :
    mergesortTable[1]? = some (.funcref (some 211)) := by rfl

/-! ## Total entry rule for `call_indirect`

The direct-call rule `Wasm.SmallStep.twp_call` resolves the callee from the
runtime module alone; an indirect call additionally consults the physical
table, so this rule also owns the table fragment (read-only). -/

theorem twp_callIndirect
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (runtimeModule : Module) (typeIndex tableIndex : Nat)
    (table : TableInst) (elementIndex functionIndex : Nat)
    (fn : Function) (signature expected : FuncType)
    (selector : UInt32)
    (hselector : (Value.i32 selector).addrNat? = some elementIndex)
    (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
    (himports : ¬functionIndex < runtimeModule.imports.length)
    (hnotforeign : isForeignFunctionIndex
      runtimeModule.imports.length functionIndex = false)
    (hfn : runtimeModule.funcs[
      functionIndex - runtimeModule.imports.length]? = some fn)
    (hsignature : runtimeModule.funcSig? functionIndex = some signature)
    (hexpected : runtimeModule.types[typeIndex]? = some expected)
    (htype : runtimeModule.indirectCallTypeOk
      functionIndex typeIndex signature expected = true)
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    let caller : CallFrame :=
      { locals := ⟨params, localValues, values.drop fn.numParams⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls }
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 selector :: values⟩,
        .callIndirect typeIndex tableIndex :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨fn.toLocals (values.take fn.numParams).reverse,
        fn.body, fn.results.length, [], [], caller :: calls⟩
    runtimeModuleOwn runtimeModule -∗
    tablePointsTo tableIndex table -∗
    (runtimeModuleOwn runtimeModule -∗
      tablePointsTo tableIndex table -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hruntime Htable Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hmodule : ⌜store.runtime.module = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns obs nt
      runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  ihave %Hphysical :
      ⌜store.wasm.tables[tableIndex]? = some table⌝ $$ [Hσ Htable]
  · imod stateInterp_table_facts_frame store ns obs nt
        tableIndex table $$ [$Hσ $Htable] with
      ⟨Hσ, Htable, %Hphysical⟩
    ipureintro
    exact Hphysical
  have himports' :
      ¬functionIndex < store.runtime.module.imports.length := by
    simpa only [Hmodule] using himports
  have hnotforeign' : isForeignFunctionIndex
      store.runtime.module.imports.length functionIndex = false := by
    simpa only [Hmodule] using hnotforeign
  have hfn' : store.runtime.module.funcs[
      functionIndex - store.runtime.module.imports.length]? = some fn := by
    simpa only [Hmodule] using hfn
  have hsignature' :
      store.runtime.module.funcSig? functionIndex = some signature := by
    simpa only [Hmodule] using hsignature
  have hexpected' :
      store.runtime.module.types[typeIndex]? = some expected := by
    simpa only [Hmodule] using hexpected
  have htype' : store.runtime.module.indirectCallTypeOk
      functionIndex typeIndex signature expected = true := by
    simpa only [Hmodule] using htype
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨fn.toLocals (values.take fn.numParams).reverse,
          fn.body, fn.results.length, [], [],
          { locals := ⟨params, localValues, values.drop fn.numParams⟩
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls } :: calls⟩,
      store, [], ⟨rfl, .instruction (.callIndirect typeIndex tableIndex),
        rfl,
        Step.callIndirect hselector Hphysical helement himports'
          hnotforeign' hfn' hsignature' hexpected' htype'⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic
      (Step.callIndirect (α := α) hselector Hphysical helement himports'
        hnotforeign' hfn' hsignature' hexpected' htype') wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Htwp $$ Hruntime Htable

/-! ## Byte-level `BufWriter` descriptor

The generated `BufWriter` stores its capacity at `+0`, the heap buffer
pointer at `+4`, and the used length at `+8` (`func135` builds it, `func35`
and `func41` consume it).  Ownership covers both the descriptor words and
the buffer bytes, split into the used prefix and the free tail. -/
def bufWriterAt [WasmHeapGS] (writer bufPtr capacity : UInt32)
    (bytes free : List UInt8) : IProp WasmHeapGF :=
  iprop% pointsTo_u32 writer capacity ∗
    pointsTo_u32 (writer + 4) bufPtr ∗
    pointsTo_u32 (writer + 8) (UInt32.ofNat bytes.length) ∗
    bytesAt bufPtr 0 bytes ∗
    bytesAt bufPtr bytes.length free

private theorem pointsTo_u32_at_eq
    [WasmSmallStepGS hlc] {address address' value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 address value ⊢ pointsTo_u32 address' value := by
  rw [haddress]

def bufferAppendFinalLocals (bufPtr len : UInt32)
    (usedLength : Nat) : List Value :=
  [.i32 (UInt32.ofNat usedLength),
   .i32 (bufPtr + UInt32.ofNat usedLength),
   .i32 len,
   .i32 (len + UInt32.ofNat usedLength)]

/-- Move a `bytesAt` offset into its base pointer. -/
private theorem bytesAt_shift [WasmHeapGS] (base : UInt32) (offset : Nat)
    (bs : List UInt8) :
    bytesAt base offset bs ⊣⊢
      bytesAt (base + UInt32.ofNat offset) 0 bs := by
  have h := bytesAt_rebase base offset 0 bs
  rw [Nat.add_zero] at h
  exact h.symm

private theorem bytesAt_congr_offset [WasmHeapGS] {base : UInt32}
    {offset offset' : Nat} (h : offset = offset') (bs : List UInt8) :
    bytesAt base offset bs ⊢ bytesAt base offset' bs := by
  rw [h]

private theorem pointsTo_byte_at_eq
    [WasmSmallStepGS hlc] {address address' : UInt32} {byte : UInt8}
    (haddress : address = address') :
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) (some byte) ⊢
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address' (DFrac.own 1) (some byte) := by
  rw [haddress]

/-- Exact total body rule for generated local `func41`: append `src` to the
buffer through one `memory.copy` and grow the recorded length.  No host call
occurs. -/
theorem bufferAppend_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (writer bufPtr capacity srcPtr len : UInt32)
    (bytes free src : List UInt8)
    (hsrcNe : src ≠ [])
    (hlen : len.toNat = src.length)
    (hfits : src.length ≤ free.length)
    (hwriterRoom : writer.toNat + 12 ≤ UInt32.size)
    (hbufRoom : bufPtr.toNat + (bytes.length + free.length) ≤ UInt32.size)
    (hsrcRoom : srcPtr.toNat + src.length ≤ UInt32.size)
    {calls : List CallFrame} :
    bufWriterAt writer bufPtr capacity bytes free ∗
      bytesAt srcPtr 0 src ∗
      (bufWriterAt writer bufPtr capacity (bytes ++ src)
          (free.drop src.length) -∗
        bytesAt srcPtr 0 src -∗
        WP (.running
          ⟨⟨[.i32 writer, .i32 srcPtr, .i32 len],
              bufferAppendFinalLocals bufPtr len bytes.length, []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 writer, .i32 srcPtr, .i32 len],
          List.replicate 4 (.i32 0), []⟩,
        func41, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h40, h41, h42, h43⟩ :=
    descriptorSlot32Facts writer 4 12 hwriterRoom (by decide)
  obtain ⟨h80, h81, h82, h83⟩ :=
    descriptorSlot32Facts writer 8 12 hwriterRoom (by decide)
  have hfreeNe : 1 ≤ free.length := by
    cases src with
    | nil => exact (hsrcNe rfl).elim
    | cons b bs => exact Nat.le_trans (by simp) hfits
  have hdestNat :
      (bufPtr + UInt32.ofNat bytes.length).toNat =
        bufPtr.toNat + bytes.length := by
    apply UInt32.add_ofNat_toNat_noWrap
    · simp only [UInt32.size] at hbufRoom ⊢
      omega
    · simp only [UInt32.size] at hbufRoom ⊢
      omega
  have hlenNe : len ≠ 0 := by
    intro hzero
    have : len.toNat = 0 := by rw [hzero]; rfl
    cases src with
    | nil => exact hsrcNe rfl
    | cons b bs => simp [hlen] at this
  have htake : (free.take src.length).length = src.length := by
    simp [List.length_take, Nat.min_eq_left hfits]
  iintro ⟨Hwriter, Hsrc, Hdone⟩
  isimp only [bufWriterAt] at Hwriter
  icases Hwriter with ⟨Hcap, Hbuf, Hused, Hbytes, Hfree⟩
  simp only [func41, List.replicate_succ, List.replicate_zero]
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat bytes.length) h80 h81 h82 h83 $$ Hused
  iintro Hused
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 bufPtr h40 h41 h42 h43 $$ Hbuf
  iintro Hbuf
  iapply twp_add
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_shl
  rw [show len <<< ((0 : UInt32) % 32) = len by bv_decide]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_eqz (value := len) (result := 0) (by simp [hlenNe])
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  -- Focus the destination window of the free tail.
  ihave Hfree' : bytesAt bufPtr bytes.length
      (free.take src.length ++ free.drop src.length) $$ [Hfree]
  · rw [List.take_append_drop]
    iexact Hfree
  icases (bytesAt_append bufPtr bytes.length
      (free.take src.length) (free.drop src.length)).mp $$ Hfree' with
    ⟨Hdest, Htail⟩
  ihave HdestAt : bytesAt (bufPtr + UInt32.ofNat bytes.length) 0
      (free.take src.length) $$ [Hdest]
  · iapply (bytesAt_shift bufPtr bytes.length (free.take src.length)).mp
    iexact Hdest
  iapply twp_memoryCopy_owned_bytes (sourceBytes := src)
      (destinationBytes := free.take src.length) hsrcNe hlen
      (by rw [htake])
      hsrcRoom
      (by rw [htake, hdestNat]; omega) $$
      [Hsrc HdestAt]
  · iframe
  iintro ⟨Hsrc, HdestAt⟩
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 (UInt32.ofNat bytes.length) h80 h81 h82 h83 $$ Hused
  iintro Hused
  -- Reassemble the descriptor around the extended byte prefix.
  ihave Hdest : bytesAt bufPtr bytes.length src $$ [HdestAt]
  · iapply (bytesAt_shift bufPtr bytes.length src).mpr
    iexact HdestAt
  ihave Hbytes' : bytesAt bufPtr 0 (bytes ++ src) $$ [Hbytes Hdest]
  · iapply (bytesAt_append bufPtr 0 bytes src).mpr
    isplitl [Hbytes]
    · iexact Hbytes
    · iapply bytesAt_congr_offset
        (show bytes.length = 0 + bytes.length by omega) src
      iexact Hdest
  ihave Htail' : bytesAt bufPtr (bytes ++ src).length
      (free.drop src.length) $$ [Htail]
  · iapply bytesAt_congr_offset
      (show bytes.length + (free.take src.length).length =
          (bytes ++ src).length by
        rw [htake, List.length_append]) (free.drop src.length)
    iexact Htail
  have hword : len + UInt32.ofNat bytes.length =
      UInt32.ofNat (bytes ++ src).length := by
    rw [List.length_append, ← hlen, UInt32.ofNat_add,
      UInt32.ofNat_toNat]
    exact UInt32.add_comm len (UInt32.ofNat bytes.length)
  ihave Hused' : pointsTo_u32 (writer + 8)
      (UInt32.ofNat (bytes ++ src).length) $$ [Hused]
  · rw [← hword]
    iexact Hused
  ihave Hwriter : bufWriterAt writer bufPtr capacity (bytes ++ src)
      (free.drop src.length) $$ [Hcap Hbuf Hused' Hbytes' Htail']
  · isimp only [bufWriterAt]
    iframe
  isimp only [bufferAppendFinalLocals] at Hdone
  iapply Hdone $$ Hwriter Hsrc

/-- Composable total call rule for `func41` at absolute Wasm index `43`. -/
theorem bufferAppend_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (writer bufPtr capacity srcPtr len : UInt32)
    (bytes free src : List UInt8)
    (hsrcNe : src ≠ [])
    (hlen : len.toNat = src.length)
    (hfits : src.length ≤ free.length)
    (hwriterRoom : writer.toNat + 12 ≤ UInt32.size)
    (hbufRoom : bufPtr.toNat + (bytes.length + free.length) ≤ UInt32.size)
    (hsrcRoom : srcPtr.toNat + src.length ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      bufWriterAt writer bufPtr capacity bytes free ∗
      bytesAt srcPtr 0 src ∗
      (runtimeModuleOwn «module» -∗
        bufWriterAt writer bufPtr capacity (bytes ++ src)
          (free.drop src.length) -∗
        bytesAt srcPtr 0 src -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 len, .i32 srcPtr, .i32 writer] ++ stack },
        .call 43 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hwriter, Hsrc, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 43 func41Def
      (by decide) bufferAppend_index $$ Hruntime
  iintro Hruntime
  simp [func41Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := bufferAppend_body_twp (α := α)
    writer bufPtr capacity srcPtr len bytes free src
    hsrcNe hlen hfits hwriterRoom hbufRoom hsrcRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [List.replicate_succ, List.replicate_zero] at Hbody
  iapply Hbody
  isplitl [Hwriter]
  · iexact Hwriter
  isplitl [Hsrc]
  · iexact Hsrc
  iintro Hwriter Hsrc
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Hdone $$ Hruntime Hwriter Hsrc

/-- The outer generated block of local `func35`. -/
def bufferWriteOuterBody : Program :=
  match func35 with
  | .block _ _ body :: _ => body
  | _ => []

/-- Exact total body rule for generated local `func35`, restricted to the
generated fast path `strLen < capacity - len`: the string is appended to the
buffer and the result byte is set to 4 (`Ok(())`), with no host call.  The
flush branch is never entered under this guard, keeping the host boundary
explicit. -/
theorem bufferWrite_fast_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr writer bufPtr capacity srcPtr len : UInt32)
    (bytes free src : List UInt8) (oldResult : UInt8)
    (hsrcNe : src ≠ [])
    (hlen : len.toNat = src.length)
    (hfast : src.length < free.length)
    (hcap : capacity.toNat = bytes.length + free.length)
    (hwriterRoom : writer.toNat + 12 ≤ UInt32.size)
    (hbufRoom : bufPtr.toNat + (bytes.length + free.length) ≤ UInt32.size)
    (hsrcRoom : srcPtr.toNat + src.length ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      bufWriterAt writer bufPtr capacity bytes free ∗
      bytesAt srcPtr 0 src ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (resultPtr + 0) (DFrac.own 1) (some oldResult) ∗
      (runtimeModuleOwn «module» -∗
        bufWriterAt writer bufPtr capacity (bytes ++ src)
          (free.drop src.length) -∗
        bytesAt srcPtr 0 src -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          (resultPtr + 0) (DFrac.own 1) (some (4 : UInt8)) -∗
        WP (.running
          ⟨⟨[.i32 resultPtr, .i32 writer, .i32 srcPtr, .i32 len],
              [], []⟩,
            [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 resultPtr, .i32 writer, .i32 srcPtr, .i32 len], [], []⟩,
        func35, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h00, h01, h02, h03⟩ :=
    descriptorSlot32Facts writer 0 12 hwriterRoom (by decide)
  obtain ⟨h80, h81, h82, h83⟩ :=
    descriptorSlot32Facts writer 8 12 hwriterRoom (by decide)
  have hfreeSize : free.length < UInt32.size := by
    have := capacity.toNat_lt_size
    omega
  have hsubEq : capacity - UInt32.ofNat bytes.length =
      UInt32.ofNat free.length := by
    have hcancel : ∀ x y : UInt32, x + y - x = y := by
      intro x y
      bv_decide
    rw [show capacity = UInt32.ofNat (bytes.length + free.length) by
        rw [← hcap]; exact UInt32.ofNat_toNat.symm,
      UInt32.ofNat_add]
    exact hcancel _ _
  have hlt : len < UInt32.ofNat free.length := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hfreeSize, hlen]
    exact hfast
  iintro ⟨Hruntime, Hwriter, Hsrc, Hresult, Hdone⟩
  isimp only [bufWriterAt] at Hwriter
  icases Hwriter with ⟨Hcap, Hbuf, Hused, Hbytes, Hfree⟩
  simp only [func35]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HcapAt : pointsTo_u32 (writer + 0) capacity $$ [Hcap]
  · iapply pointsTo_u32_at_eq (show writer = writer + 0 by bv_decide)
    iexact Hcap
  iapply twp_load32 capacity h00 h01 h02 h03 $$ HcapAt
  iintro HcapAt
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat bytes.length) h80 h81 h82 h83 $$ Hused
  iintro Hused
  iapply twp_sub
  rw [hsubEq]
  iapply twp_ltU (result := 1) (by simp [hlt])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hcap' : pointsTo_u32 writer capacity $$ [HcapAt]
  · iapply pointsTo_u32_at_eq (show writer + 0 = writer by bv_decide)
    iexact HcapAt
  ihave Hwriter : bufWriterAt writer bufPtr capacity bytes free $$
      [Hcap' Hbuf Hused Hbytes Hfree]
  · isimp only [bufWriterAt]
    iframe
  have Hcall := bufferAppend_call_twp (α := α)
    writer bufPtr capacity srcPtr len bytes free src
    hsrcNe hlen (Nat.le_of_lt hfast) hwriterRoom hbufRoom hsrcRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[.i32 resultPtr, .i32 writer, .i32 srcPtr, .i32 len], [], []⟩)
    (stack := [])
    (code := [.localGet 0, .const 4, .store8 0])
    (arity := 0) (remainder := [])
    (controls :=
      [{ kind := .block
         paramArity := 0
         resultArity := 0
         body := bufferWriteOuterBody
         continuation := [.ret]
         belowStack := [] }])
    (calls := calls)
  simp only [List.append_nil, bufferWriteOuterBody, func35] at Hcall
  iapply Hcall
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hwriter]
  · iexact Hwriter
  isplitl [Hsrc]
  · iexact Hsrc
  iintro Hruntime Hwriter Hsrc
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store8_owned oldResult
    (show (resultPtr + 0).toNat = resultPtr.toNat + (0 : UInt32).toNat by
      simp) $$ Hresult
  iintro Hresult
  rw [show (4 : UInt32).toUInt8 = (4 : UInt8) by decide]
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply Hdone $$ Hruntime Hwriter Hsrc Hresult

/-- Composable total call rule for the `func35` fast path at absolute Wasm
index `37`. -/
theorem bufferWrite_fast_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr writer bufPtr capacity srcPtr len : UInt32)
    (bytes free src : List UInt8) (oldResult : UInt8)
    (hsrcNe : src ≠ [])
    (hlen : len.toNat = src.length)
    (hfast : src.length < free.length)
    (hcap : capacity.toNat = bytes.length + free.length)
    (hwriterRoom : writer.toNat + 12 ≤ UInt32.size)
    (hbufRoom : bufPtr.toNat + (bytes.length + free.length) ≤ UInt32.size)
    (hsrcRoom : srcPtr.toNat + src.length ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      bufWriterAt writer bufPtr capacity bytes free ∗
      bytesAt srcPtr 0 src ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        resultPtr (DFrac.own 1) (some oldResult) ∗
      (runtimeModuleOwn «module» -∗
        bufWriterAt writer bufPtr capacity (bytes ++ src)
          (free.drop src.length) -∗
        bytesAt srcPtr 0 src -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          resultPtr (DFrac.own 1) (some (4 : UInt8)) -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 len, .i32 srcPtr, .i32 writer, .i32 resultPtr] ++ stack },
        .call 37 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hwriter, Hsrc, Hresult, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 37 func35Def
      (by decide) bufferWrite_index $$ Hruntime
  iintro Hruntime
  simp [func35Def, Function.toLocals, Function.numParams]
  have Hbody := bufferWrite_fast_body_twp (α := α)
    resultPtr writer bufPtr capacity srcPtr len bytes free src oldResult
    hsrcNe hlen hfast hcap hwriterRoom hbufRoom hsrcRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  ihave HresultAt : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      (resultPtr + 0) (DFrac.own 1) (some oldResult) $$ [Hresult]
  · iapply pointsTo_byte_at_eq
      (show resultPtr = resultPtr + 0 by bv_decide)
    iexact Hresult
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hwriter]
  · iexact Hwriter
  isplitl [Hsrc]
  · iexact Hsrc
  isplitl [HresultAt]
  · iexact HresultAt
  iintro Hruntime Hwriter Hsrc HresultAt
  ihave Hresult : pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
      resultPtr (DFrac.own 1) (some (4 : UInt8)) $$ [HresultAt]
  · iapply pointsTo_byte_at_eq
      (show resultPtr + 0 = resultPtr by bv_decide)
    iexact HresultAt
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Hdone $$ Hruntime Hwriter Hsrc Hresult

def writeStrAdapterFinalLocals (frame writerPtr : UInt32) : List Value :=
  [.i32 frame, .i32 writerPtr, .i32 4, .i32 4, .i32 1, .i32 0]

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

/-- Exact total body rule for generated local `func46`, the static-vtable
`write_str` adapter, along the buffered fast path: it forwards to `func35`,
observes the success byte, and returns 0. -/
theorem writeStrAdapter_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (adapter writerPtr bufPtr capacity srcPtr len stackTop : UInt32)
    (bytes free src : List UInt8) (oldResult oldFlag : UInt8)
    (hsrcNe : src ≠ [])
    (hlen : len.toNat = src.length)
    (hfast : src.length < free.length)
    (hcap : capacity.toNat = bytes.length + free.length)
    (hadapterRoom : adapter.toNat + 12 ≤ UInt32.size)
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    (hwriterRoom : writerPtr.toNat + 12 ≤ UInt32.size)
    (hbufRoom : bufPtr.toNat + (bytes.length + free.length) ≤ UInt32.size)
    (hsrcRoom : srcPtr.toNat + src.length ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (adapter + 8) writerPtr ∗
      bufWriterAt writerPtr bufPtr capacity bytes free ∗
      bytesAt srcPtr 0 src ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        ((stackTop - 32) + 16) (DFrac.own 1) (some oldResult) ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        ((stackTop - 32) + 15) (DFrac.own 1) (some oldFlag) ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (adapter + 8) writerPtr -∗
        bufWriterAt writerPtr bufPtr capacity (bytes ++ src)
          (free.drop src.length) -∗
        bytesAt srcPtr 0 src -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          ((stackTop - 32) + 16) (DFrac.own 1) (some (4 : UInt8)) -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          ((stackTop - 32) + 15) (DFrac.own 1) (some (0 : UInt8)) -∗
        WP (.running
          ⟨⟨[.i32 adapter, .i32 srcPtr, .i32 len],
              writeStrAdapterFinalLocals (stackTop - 32) writerPtr,
              [.i32 0]⟩,
            [.ret], 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 adapter, .i32 srcPtr, .i32 len],
          List.replicate 6 (.i32 0), []⟩,
        func46, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h80, h81, h82, h83⟩ :=
    descriptorSlot32Facts adapter 8 12 hadapterRoom (by decide)
  have hf15 : ((stackTop - 32) + 15).toNat = (stackTop - 32).toNat + 15 := by
    apply UInt32.add_ofNat_toNat_noWrap
    · decide
    · simp only [UInt32.size] at hframeRoom ⊢
      omega
  have hf16 : ((stackTop - 32) + 16).toNat = (stackTop - 32).toNat + 16 := by
    apply UInt32.add_ofNat_toNat_noWrap
    · decide
    · simp only [UInt32.size] at hframeRoom ⊢
      omega
  iintro ⟨Hruntime, Hglobal, Hadapter, Hwriter, Hsrc, Hresult, Hflag,
    Hdone⟩
  simp only [func46, List.replicate_succ, List.replicate_zero]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_load32 writerPtr h80 h81 h82 h83 $$ Hadapter
  iintro Hadapter
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 16 (stackTop - 32)]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  have Hcall := bufferWrite_fast_call_twp (α := α)
    ((stackTop - 32) + 16) writerPtr bufPtr capacity srcPtr len
    bytes free src oldResult
    hsrcNe hlen hfast hcap hwriterRoom hbufRoom hsrcRoom
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      ⟨[.i32 adapter, .i32 srcPtr, .i32 len],
        [.i32 (stackTop - 32), .i32 writerPtr, .i32 0, .i32 0,
         .i32 0, .i32 0], []⟩)
    (stack := [])
    (code := func46.drop 16)
    (arity := 1) (remainder := []) (controls := []) (calls := calls)
  simp only [List.append_nil, func46, List.drop] at Hcall
  iapply Hcall
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hwriter]
  · iexact Hwriter
  isplitl [Hsrc]
  · iexact Hsrc
  isplitl [Hresult]
  · iexact Hresult
  iintro Hruntime Hwriter Hsrc Hresult
  iapply twp_localGet rfl
  iapply twp_load8U_owned 4 hf16 $$ Hresult
  iintro Hresult
  rw [show (4 : UInt8).toUInt32 = (4 : UInt32) by decide]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_const
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (4 : UInt32) &&& 255 = 4 by decide]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (4 : UInt32) &&& 255 = 4 by decide]
  iapply twp_eq (result := 1) (by decide)
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_const
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_selectI32 (selected := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (value := 0) (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store8_owned oldFlag hf15 $$ Hflag
  iintro Hflag
  rw [show (0 : UInt32).toUInt8 = (0 : UInt8) by decide]
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load8U_owned 0 hf15 $$ Hflag
  iintro Hflag
  rw [show (0 : UInt8).toUInt32 = (0 : UInt32) by decide]
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_localSet rfl
  simp only [List.length, List.set, Nat.reduceAdd, Nat.reduceSub]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 32 (stackTop - 32),
    show (stackTop - 32) + 32 = stackTop by bv_decide]
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  isimp only [writeStrAdapterFinalLocals] at Hdone
  iapply Hdone $$ Hruntime Hglobal Hadapter Hwriter Hsrc Hresult Hflag

/-- Composable rule for the exact vtable dispatch the formatter performs:
`call_indirect` on type 3 with table selector 5 (the `write_str` slot of the
static vtable at 1048856) reaches `func46` and, on the buffered fast path,
appends `src` and pushes result 0. -/
theorem writeStrAdapter_callIndirect_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (adapter writerPtr bufPtr capacity srcPtr len stackTop : UInt32)
    (bytes free src : List UInt8) (oldResult oldFlag : UInt8)
    (hsrcNe : src ≠ [])
    (hlen : len.toNat = src.length)
    (hfast : src.length < free.length)
    (hcap : capacity.toNat = bytes.length + free.length)
    (hadapterRoom : adapter.toNat + 12 ≤ UInt32.size)
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    (hwriterRoom : writerPtr.toNat + 12 ≤ UInt32.size)
    (hbufRoom : bufPtr.toNat + (bytes.length + free.length) ≤ UInt32.size)
    (hsrcRoom : srcPtr.toNat + src.length ≤ UInt32.size)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      tablePointsTo 0 mergesortTable ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 (adapter + 8) writerPtr ∗
      bufWriterAt writerPtr bufPtr capacity bytes free ∗
      bytesAt srcPtr 0 src ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        ((stackTop - 32) + 16) (DFrac.own 1) (some oldResult) ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        ((stackTop - 32) + 15) (DFrac.own 1) (some oldFlag) ∗
      (runtimeModuleOwn «module» -∗
        tablePointsTo 0 mergesortTable -∗
        globalPointsTo 0 (.i32 stackTop) -∗
        pointsTo_u32 (adapter + 8) writerPtr -∗
        bufWriterAt writerPtr bufPtr capacity (bytes ++ src)
          (free.drop src.length) -∗
        bytesAt srcPtr 0 src -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          ((stackTop - 32) + 16) (DFrac.own 1) (some (4 : UInt8)) -∗
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          ((stackTop - 32) + 15) (DFrac.own 1) (some (0 : UInt8)) -∗
        WP (.running
          ⟨{ callerLocals with values := [.i32 0] ++ stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 5, .i32 len, .i32 srcPtr, .i32 adapter] ++ stack },
        .callIndirect 3 0 :: code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Htable, Hglobal, Hadapter, Hwriter, Hsrc, Hresult,
    Hflag, Hdone⟩
  simp only [List.cons_append, List.nil_append]
  iapply twp_callIndirect (α := α) «module» 3 0 mergesortTable 5 48
      func46Def
      { params := [.i32, .i32, .i32], results := [.i32] }
      { params := [.i32, .i32, .i32], results := [.i32] }
      5 rfl mergesortTable_writeStr (by decide) (by rfl)
      writeStrAdapter_index (by rfl) (by rfl) (by rfl) $$ Hruntime Htable
  iintro Hruntime Htable
  simp [func46Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := writeStrAdapter_body_twp (α := α)
    adapter writerPtr bufPtr capacity srcPtr len stackTop
    bytes free src oldResult oldFlag
    hsrcNe hlen hfast hcap hadapterRoom hframeRoom hwriterRoom
    hbufRoom hsrcRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  simp only [List.replicate_succ, List.replicate_zero] at Hbody
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hadapter]
  · iexact Hadapter
  isplitl [Hwriter]
  · iexact Hwriter
  isplitl [Hsrc]
  · iexact Hsrc
  isplitl [Hresult]
  · iexact Hresult
  isplitl [Hflag]
  · iexact Hflag
  iintro Hruntime Hglobal Hadapter Hwriter Hsrc Hresult Hflag
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append, List.cons_append]
  iapply Hdone $$ Hruntime Htable Hglobal Hadapter Hwriter Hsrc
    Hresult Hflag

end Project.Mergesort.BufferedWriterProof
