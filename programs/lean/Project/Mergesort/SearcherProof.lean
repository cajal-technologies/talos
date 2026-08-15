import Project.Mergesort.InputIteratorProof

/-!
# Character-searcher leaves for `Split::next`

Total contracts for the leaves consulted by the generated character
searcher (`func86`):

* `func253` (absolute call `255`) is the C-style `memcmp`; the searcher
  only ever compares the one-byte space delimiter, so the single-byte
  equal contract is proved exactly;
* `func18` (absolute call `20`) is the byte `memchr` used to locate the
  next delimiter inside the pending haystack window.  Windows shorter
  than eight bytes take the exact generated linear scan proved here.
-/

namespace Project.Mergesort.SearcherProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.MemoryCopyProof
open Project.Mergesort.MemoryFillProof

/-! ## Local instruction rules

Deterministic one-step rules for the generated comparison instructions not
yet provided by `Machine.lean` or the shared total lifting layer. -/

private theorem twp_ne
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≠ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .ne :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.ne hresult)

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
  twp_pureStep _ _ _ (fun _ => Step.eq hresult)

private theorem twp_geU
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≥ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .geU :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.geU hresult)

private theorem twp_returnFromCallFallthrough
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset} {Φ : List Value → IProp WasmHeapGF}
    {calleeLocals callerLocals : Locals} {calleeArity callerArity : Nat}
    {calleeRemainder callerRemainder : List Value}
    {callerCode : Program} {callerControls : List ControlFrame}
    {calls : List CallFrame} :
    let caller : CallFrame :=
      { locals := callerLocals
        continuation := callerCode
        resultArity := callerArity
        callerRemainder := callerRemainder
        control := callerControls }
    WP (.running
      ⟨{ callerLocals with
          values := calleeLocals.values.take calleeArity ++ callerLocals.values },
        callerCode, callerArity, callerRemainder, callerControls, calls⟩ :
        Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨calleeLocals, [], calleeArity, calleeRemainder, [], caller :: calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  dsimp only
  exact twp_pureStep _ _ _ (fun _ => Step.returnFromCallFallthrough)

private theorem pointsToByte_add_zero [WasmHeapGS]
    (base : UInt32) (byte : UInt8) :
    (base ↦w byte) ⊢ ((base + 0) ↦w byte) := by
  rw [UInt32.add_zero]

private theorem pointsToByte_remove_zero [WasmHeapGS]
    (base : UInt32) (byte : UInt8) :
    ((base + 0) ↦w byte) ⊢ (base ↦w byte) := by
  rw [UInt32.add_zero]

private theorem pointsToByte_congr [WasmHeapGS]
    (lhs rhs : UInt32) (lhsByte rhsByte : UInt8)
    (haddr : lhs = rhs) (hbyte : lhsByte = rhsByte) :
    (lhs ↦w lhsByte) ⊢ (rhs ↦w rhsByte) := by
  rw [haddr, hbyte]

/-! ## `func253` (`memcmp`, absolute call `255`) on one equal byte

The searcher validates a candidate delimiter position by comparing the
single delimiter byte against the matched haystack byte; both sides are
equal by construction, so only the equal one-byte path is on the verified
execution. -/

private theorem memcmp_index : «module».funcs[253]? = some func253Def := by
  rfl

/-- Exact body rule for `func253` comparing one equal byte: the generated
loop runs a single iteration and falls through with result `0`. -/
theorem memcmpOneEqual_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (leftPtr rightPtr : UInt32) (byte : UInt8)
    {calls : List CallFrame} :
    (leftPtr ↦w byte) ∗ (rightPtr ↦w byte) ∗
      ((leftPtr ↦w byte) -∗ (rightPtr ↦w byte) -∗
        WP (.running
          ⟨⟨[.i32 (1 + leftPtr), .i32 (1 + rightPtr), .i32 0],
              [.i32 0, .i32 byte.toUInt32, .i32 byte.toUInt32],
              [.i32 0]⟩,
            [], 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 leftPtr, .i32 rightPtr, .i32 1],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func253, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hleft, Hright, Hdone⟩
  simp only [func253]
  iapply twp_const
  iapply twp_localSet rfl
  iapply twp_block
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set, List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_block
  iapply twp_loop
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  ihave HleftAt : ((leftPtr + 0) ↦w byte) $$ [Hleft]
  · iapply pointsToByte_add_zero
    iexact Hleft
  iapply twp_load8U_owned (α := α) (address := leftPtr) (offset := 0)
    byte (by simp) $$ HleftAt
  iintro HleftAt
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HrightAt : ((rightPtr + 0) ↦w byte) $$ [Hright]
  · iapply pointsToByte_add_zero
    iexact Hright
  iapply twp_load8U_owned (α := α) (address := rightPtr) (offset := 0)
    byte (by simp) $$ HrightAt
  iintro HrightAt
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_ne (result := 0) (by simp)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  rw [show (4294967295 : UInt32) + 1 = 0 by decide]
  iapply twp_localGet rfl
  iapply twp_eqz (result := 1) (by decide)
  iapply twp_brIf (condition := 1) (depth := 2) (by decide) rfl
  simp only [List.take_nil, List.append_nil]
  iapply twp_localGet rfl
  ihave Hleft' : (leftPtr ↦w byte) $$ [HleftAt]
  · iapply pointsToByte_remove_zero
    iexact HleftAt
  ihave Hright' : (rightPtr ↦w byte) $$ [HrightAt]
  · iapply pointsToByte_remove_zero
    iexact HrightAt
  iapply Hdone $$ Hleft' Hright'

/-- Composable absolute-index-`255` rule for `memcmp` on one equal byte:
the call returns `0` and both bytes are preserved. -/
theorem memcmpOneEqual_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (leftPtr rightPtr : UInt32) (byte : UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (leftPtr ↦w byte) ∗ (rightPtr ↦w byte) ∗
      (runtimeModuleOwn «module» -∗
        (leftPtr ↦w byte) -∗ (rightPtr ↦w byte) -∗
        WP (.running
          ⟨{ callerLocals with values := .i32 0 :: stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 1, .i32 rightPtr, .i32 leftPtr] ++ stack },
        .call 255 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hleft, Hright, Hdone⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 255 func253Def
      (by decide) memcmp_index $$ Hruntime
  iintro Hruntime
  simp [func253Def, Function.toLocals, Function.numParams, ValueType.zero]
  have Hbody := memcmpOneEqual_body_twp (α := α) leftPtr rightPtr byte
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := { callerLocals with values := stack }
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls } :: calls)
  iapply Hbody
  isplitl [Hleft]
  · iexact Hleft
  isplitl [Hright]
  · iexact Hright
  iintro Hleft Hright
  iapply twp_returnFromCallFallthrough (α := α)
  simp only [List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append]
  iapply Hdone $$ Hruntime Hleft Hright

/-! ## `func18` (byte `memchr`, absolute call `20`) on short windows

The searcher hands `func18` the pending haystack window and the one
delimiter byte.  Windows shorter than eight bytes take the generated
byte-by-byte scan (longer windows dispatch to the word-at-a-time
`func244`, outside this file's scope). -/

private def leadingBlockBody (program : Program) : Program :=
  match program with
  | .block 0 0 body :: _ => body
  | _ => []

private def leadingLoopBody (program : Program) : Program :=
  match program with
  | .loop 0 0 body :: _ => body
  | _ => []

/-- Body of the outer result block of `func18`. -/
def charSearchOuterBody : Program := leadingBlockBody (func18.drop 6)

/-- Body of the window block wrapping the generated scan loop. -/
def charSearchWindowBody : Program :=
  leadingBlockBody (charSearchOuterBody.drop 4)

/-- The generated linear scan loop of `func18`. -/
def charSearchLoopBody : Program := leadingLoopBody charSearchWindowBody

/-- Common epilogue of `func18`: publish `(flag, index)` and return. -/
def charSearchEpilogue : Program := func18.drop 7

/-- Operand frame of the scan loop. -/
def charSearchLoopFrame : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := charSearchLoopBody
    continuation := charSearchWindowBody.drop 1
    belowStack := [] }

/-- Control context below the scan loop: the window block and the outer
result block, whose continuation is the shared epilogue. -/
def charSearchControls : List ControlFrame :=
  [ { kind := .block
      paramArity := 0
      resultArity := 0
      body := charSearchWindowBody
      continuation := []
      belowStack := [] },
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := charSearchOuterBody
      continuation := charSearchEpilogue
      belowStack := [] } ]

def charSearchParams (resultPtr : UInt32) (needle : UInt8)
    (hayPtr : UInt32) (length : Nat) : List Value :=
  [.i32 resultPtr, .i32 needle.toUInt32, .i32 hayPtr,
    .i32 (UInt32.ofNat length)]

def charSearchLocals (frame l6 l7 l8 : UInt32) : List Value :=
  [.i32 frame, .i32 0, .i32 l6, .i32 l7, .i32 l8, .i32 0]

/-- Focus one owned byte out of an owned byte range. -/
private theorem bytesAt_get [WasmHeapGS] (base : UInt32)
    (bs : List UInt8) (i : Nat) (hi : i < bs.length) :
    bytesAt base 0 bs ⊢
      (iprop% ((base + UInt32.ofNat i) ↦w bs[i]) ∗
        (((base + UInt32.ofNat i) ↦w bs[i]) -∗ bytesAt base 0 bs)) := by
  have hsplit : bs = bs.take i ++ bs[i] :: bs.drop (i + 1) := by
    rw [List.getElem_cons_drop hi, List.take_append_drop]
  rw [hsplit]
  rw [show bytesAt base 0 (bs.take i ++ bs[i] :: bs.drop (i + 1)) ⊣⊢
      bytesAt base 0 (bs.take i) ∗
        bytesAt base (0 + (bs.take i).length)
          (bs[i] :: bs.drop (i + 1)) from
    bytesAt_append base 0 (bs.take i) (bs[i] :: bs.drop (i + 1))]
  have hlen : (bs.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [hlen]
  simp only [Nat.zero_add, bytesAt]
  iintro ⟨Hprefix, Hbyte, Hsuffix⟩
  isplitl [Hbyte]
  · iexact Hbyte
  iintro Hbyte
  iframe

private theorem ofNat_lt_ofNat {a b : Nat} (hlt : a < b)
    (hb : b < 4294967296) :
    UInt32.ofNat a < UInt32.ofNat b := by
  simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat]
  omega

private theorem uint8_toUInt32_ne {a b : UInt8} (hne : a ≠ b) :
    a.toUInt32 ≠ b.toUInt32 := by
  intro h
  apply hne
  have := congrArg UInt32.toNat h
  simp only [UInt8.toNat_toUInt32] at this
  exact UInt8.eq_of_toNat_eq this

/-- One non-matching iteration of the generated scan loop: the byte at the
current index differs from the needle, so the index advances and the loop
takes its backedge. -/
theorem charSearchLoop_miss_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr hayPtr stackTop : UInt32) (needle c : UInt8)
    (bs : List UInt8) (i : Nat) (l8 : UInt32)
    (hbyte : bs[i]? = some c) (hmiss : c ≠ needle)
    (hshort : bs.length < 8)
    (hframeRoom : (stackTop - 32).toNat + 32 ≤ UInt32.size)
    {calls : List CallFrame} :
    pointsTo_u32 ((stackTop - 32) + 28) (UInt32.ofNat i) ∗
      bytesAt hayPtr 0 bs ∗
      (pointsTo_u32 ((stackTop - 32) + 28) (UInt32.ofNat (i + 1)) -∗
        bytesAt hayPtr 0 bs -∗
        WP (.running
          ⟨⟨charSearchParams resultPtr needle hayPtr bs.length,
              charSearchLocals (stackTop - 32) 0 0 (UInt32.ofNat i), []⟩,
            charSearchLoopBody, 0, [],
            charSearchLoopFrame :: charSearchControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨charSearchParams resultPtr needle hayPtr bs.length,
          charSearchLocals (stackTop - 32) 0 0 l8, []⟩,
        charSearchLoopBody, 0, [],
        charSearchLoopFrame :: charSearchControls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hi : i < bs.length := by
    have := List.getElem?_eq_some_iff.mp hbyte
    exact this.1
  have hc : bs[i] = c := by
    have := List.getElem?_eq_some_iff.mp hbyte
    exact this.2
  obtain ⟨h280, h281, h282, h283⟩ :=
    descriptorSlot32Facts (stackTop - 32) 28 32 hframeRoom (by decide)
  iintro ⟨Hindex, Hbytes, Hrec⟩
  simp only [charSearchLoopBody, charSearchWindowBody, charSearchOuterBody,
    leadingBlockBody, leadingLoopBody, func18, List.drop,
    charSearchParams, charSearchLocals]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat i) h280 h281 h282 h283 $$ Hindex
  iintro Hindex
  iapply twp_localGet rfl
  iapply twp_ltU (result := 1)
    (by simp [ofNat_lt_ofNat hi (by omega)])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (condition := 1) (depth := 0) (by decide) rfl
  simp only [List.take_nil, List.append_nil]
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat i) h280 h281 h282 h283 $$ Hindex
  iintro Hindex
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_block
  iapply twp_block
  iapply twp_block
  simp only [List.drop_zero]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ltU (result := 1)
    (by simp [ofNat_lt_ofNat hi (by omega)])
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
  ihave Hfocus := bytesAt_get hayPtr bs i hi $$ Hbytes
  icases Hfocus with ⟨Hbyte, Hclose⟩
  ihave HbyteAt : (((UInt32.ofNat i + hayPtr) + 0) ↦w c) $$ [Hbyte]
  · iapply pointsToByte_congr (hayPtr + UInt32.ofNat i)
      ((UInt32.ofNat i + hayPtr) + 0) bs[i] c
      (by rw [UInt32.add_zero, UInt32.add_comm]) hc
    iexact HbyteAt
  iapply twp_load8U_owned (α := α) (address := UInt32.ofNat i + hayPtr)
    (offset := 0) c (by simp) $$ HbyteAt
  iintro HbyteAt
  iapply twp_const
  iapply twp_and
  rw [show c.toUInt32 &&& 255 = c.toUInt32 by bv_decide]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show needle.toUInt32 &&& 255 = needle.toUInt32 by bv_decide]
  iapply twp_eq (result := 0) (by simp [uint8_toUInt32_ne hmiss])
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_br (depth := 1) rfl
  simp only [List.take_nil, List.append_nil]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 (UInt32.ofNat i) h280 h281 h282 h283 $$ Hindex
  iintro Hindex
  iapply twp_const
  iapply twp_add
  rw [show (1 : UInt32) + UInt32.ofNat i = UInt32.ofNat (i + 1) by
    rw [UInt32.ofNat_add, UInt32.add_comm]; rfl]
  iapply twp_store32 (UInt32.ofNat i) h280 h281 h282 h283 $$ Hindex
  iintro Hindex
  iapply twp_br (depth := 1) rfl
  simp only [List.take_nil, List.append_nil]
  ihave Hbytes' : bytesAt hayPtr 0 bs $$ [HbyteAt Hclose]
  · iapply Hclose
    iapply pointsToByte_congr ((UInt32.ofNat i + hayPtr) + 0)
      (hayPtr + UInt32.ofNat i) c bs[i]
      (by rw [UInt32.add_zero, UInt32.add_comm]) hc.symm
    iexact HbyteAt
  isimp only [charSearchLoopBody, charSearchWindowBody, charSearchOuterBody,
    leadingBlockBody, leadingLoopBody, func18, List.drop,
    charSearchParams, charSearchLocals] at Hrec
  iapply Hrec $$ Hindex Hbytes'

end Project.Mergesort.SearcherProof
