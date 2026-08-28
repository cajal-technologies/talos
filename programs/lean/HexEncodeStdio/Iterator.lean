import Mathlib
import CodeLib
import Project.HexStdio.Program
import HexEncodeStdio.Helpers
import HexEncodeStdio.Hex

namespace Project.HexEncodeStdio.Iterator

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep
open Project.HexStdio.Spec

abbrev sentinel : UInt32 := 1114112

private abbrev iterLocals (ptr first second : UInt32) (values : List Value := []) : Locals :=
  ⟨[.i32 ptr], [.i32 first, .i32 second], values⟩

private theorem wp_shrU32 {hlc : HasLC} {α : Type} [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    ▷ WP (.running
      ⟨⟨params, localValues, .i32 (lhs >>> (rhs % 32)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .shrU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} :=
  wp_pureStep _ _ _ (fun _ => Step.shrU)

private theorem wp_load8U_zero {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value} {address : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} (byte : UInt8) :
    ▷ (⟨0, address⟩ ↦w byte) -∗
    ▷ ((⟨0, address⟩ ↦w byte) -∗
      WP (.running ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }}) -∗
    WP (.running ⟨⟨params, localValues, .i32 address :: values⟩,
      .load8U 0 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} := by
  simpa only [UInt32.add_zero] using
    (wp_load8U (α := α) (s := s) (E := E) (Φ := Φ)
      (address := address) (offset := 0) byte (by simp))

/-- The CodeLib release has the explicit-return lifting rule but not the
fallthrough twin. This is the same framed rule for a callee whose body reaches
the empty instruction list. -/
private theorem wp_returnFromCallFallthrough' {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {calleeLocals callerLocals : Locals} {callerCode : Program}
    {calleeArity callerArity : Nat} {calleeRemainder callerRemainder : List Value}
    {callerControls : List ControlFrame} {returningInstance : ModuleInstanceId}
    {module : Module} {calls : List CallFrame} :
    let caller : CallFrame :=
      { locals := callerLocals, continuation := callerCode,
        resultArity := callerArity, callerRemainder := callerRemainder,
        control := callerControls, returningInstance := returningInstance }
    let current : ThreadState α :=
      ⟨calleeLocals, [], calleeArity, calleeRemainder, [], caller :: calls⟩
    let next : ThreadState α :=
      ⟨{ callerLocals with
          values := calleeLocals.values.take calleeArity ++ callerLocals.values },
        callerCode, callerArity, callerRemainder, callerControls, calls⟩
    ▷ runtimeModuleOwn returningInstance module -∗
    ▷ (runtimeModuleOwn returningInstance module -∗
      WP (Expr.running next : Expr α) @ s; E {{ Φ }}) -∗
    WP (Expr.running current : Expr α) @ s; E {{ Φ }} := by
  dsimp only
  iintro >Hruntime Hwp
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  ihave %Hentry : ⌜store.runtime.entry = returningInstance⌝ $$ [Hσ HinstanceOwn]
  · imod stateInterp_currentInstance_agree store ns (obs ++ obs') nt
      returningInstance $$ [$Hσ $HinstanceOwn] with %Hentry
    ipureintro
    exact Hentry
  have hsame : returningInstance = store.runtime.entry := Hentry.symm
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact ⟨[], _, store, [],
      ⟨rfl, _, rfl, Step.returnFromCallFallthrough hsame⟩⟩
  iintro !> %e₂ %store₂ %forks %Hstep Hcredit
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst obs
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.returnFromCallFallthrough (α := α) hsame) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  simp only [List.length_nil, Nat.add_zero, Iris.Algebra.BigOpL.bigOpL_nil,
    resumeCaller]
  imod Hclose
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hwp HruntimeElem HinstanceOwn]
  · iapply Hwp
    isplitl [HruntimeElem]
    · iexact HruntimeElem
    · iexact HinstanceOwn
  · itrivial

private theorem wordAccessFacts (ptr : UInt32) (offset : Nat)
    (hfit : ptr.toNat + offset + 4 < UInt32.size) :
    (ptr + UInt32.ofNat offset).toNat = ptr.toNat + offset ∧
    ((ptr + UInt32.ofNat offset) + 1).toNat =
      (ptr + UInt32.ofNat offset).toNat + 1 ∧
    ((ptr + UInt32.ofNat offset) + 2).toNat =
      (ptr + UInt32.ofNat offset).toNat + 2 ∧
    ((ptr + UInt32.ofNat offset) + 3).toNat =
      (ptr + UInt32.ofNat offset).toNat + 3 := by
  have hadd (n : Nat) (hn : n ≤ offset + 3) :
      (ptr + UInt32.ofNat n).toNat = ptr.toNat + n :=
    Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap ptr n
      (by norm_num [UInt32.size] at hfit ⊢; omega)
      (by norm_num [UInt32.size] at hfit ⊢; omega)
  refine ⟨hadd offset (by omega), ?_, ?_, ?_⟩
  · rw [show (1 : UInt32) = UInt32.ofNat 1 by rfl,
      UInt32.add_assoc, ← UInt32.ofNat_add, hadd (offset + 1) (by omega),
      hadd offset (by omega)]
    omega
  · rw [show (2 : UInt32) = UInt32.ofNat 2 by rfl,
      UInt32.add_assoc, ← UInt32.ofNat_add, hadd (offset + 2) (by omega),
      hadd offset (by omega)]
    omega
  · rw [show (3 : UInt32) = UInt32.ofNat 3 by rfl,
      UInt32.add_assoc, ← UInt32.ofNat_add, hadd (offset + 3) (by omega),
      hadd offset (by omega)]
    omega

/-- The second half of the iterator's two-state protocol: a saved low nibble
is returned and the sentinel is restored. -/
theorem func18_low_body {hlc : HasLC} {α : Type} [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (ptr saved : UInt32) (hsaved : saved ≠ sentinel)
    (hptr : ptr.toNat + 4 < UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 0 ptr saved ∗
      (pointsTo_u32 0 ptr sentinel -∗
      WP (.running ⟨⟨[.i32 ptr], [.i32 saved, .i32 0], [.i32 saved]⟩,
        [], 1, [], controls, calls⟩ :
        Expr α) @ s; E {{ Φ }}) ⊢
      WP (.running ⟨iterLocals ptr 0 0, Project.HexStdio.func18,
        1, [], controls, calls⟩ : Expr α) @ s; E {{ Φ }} := by
  have h0 : (ptr + 0).toNat = ptr.toNat + (0 : UInt32).toNat := by simp
  have h1 : ((ptr + 0) + 1).toNat = (ptr + 0).toNat + 1 := by
    simpa using Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap ptr 1 (by omega)
      (by simp [UInt32.size] at hptr ⊢; omega)
  have h2 : ((ptr + 0) + 2).toNat = (ptr + 0).toNat + 2 := by
    simpa using Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap ptr 2 (by omega)
      (by simp [UInt32.size] at hptr ⊢; omega)
  have h3 : ((ptr + 0) + 3).toNat = (ptr + 0).toNat + 3 := by
    simpa using Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap ptr 3 (by omega)
      (by simp [UInt32.size] at hptr ⊢; omega)
  iintro ⟨Hstate, Hfinish⟩
  ihave Hstate0 : pointsTo_u32 0 (ptr + 0) saved $$ [Hstate]
  · rw [UInt32.add_zero]
    iexact Hstate
  simp only [Project.HexStdio.func18]
  iapply wp_localGet rfl
  inext
  iapply wp_load32 saved h0 h1 h2 h3 $$ Hstate0
  inext
  iintro Hstate0
  iapply wp_localSet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_const
  inext
  iapply wp_store32 saved h0 h1 h2 h3 $$ Hstate0
  inext
  iintro Hstate0
  iapply wp_block
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_const
  inext
  iapply wp_ne (result := 1) (by
    simpa [sentinel] using hsaved)
  inext
  iapply wp_brIf (by decide) rfl
  inext
  iapply wp_localGet rfl
  inext
  simp [iterLocals, List.set]
  iapply Hfinish
  unfold sentinel
  iexact Hstate0

/-- The first half of the iterator protocol consumes one source byte, saves
its low hexadecimal digit in the iterator state, and returns its high digit. -/
theorem func18_high_body {hlc : HasLC} {α : Type} [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (ptr index finish : UInt32) (byte : UInt8)
    (hne : index ≠ finish)
    (hptr : ptr.toNat + 16 < UInt32.size)
    (hindex : index.toNat + 1 < UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 0 ptr sentinel ∗
      pointsTo_u32 0 (ptr + 4) index ∗
      pointsTo_u32 0 (ptr + 8) finish ∗
      pointsTo_u32 0 (ptr + 12) 1048576 ∗
      (⟨0, index⟩ ↦w byte) ∗
      pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable ∗
      (pointsTo_u32 0 ptr (hexDigit (byte.toNat % 16)).toUInt32 -∗
        pointsTo_u32 0 (ptr + 4) (index + 1) -∗
        pointsTo_u32 0 (ptr + 8) finish -∗
        pointsTo_u32 0 (ptr + 12) 1048576 -∗
        (⟨0, index⟩ ↦w byte) -∗
        pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable -∗
        WP (.running
          ⟨⟨[.i32 ptr],
              [.i32 (hexDigit (byte.toNat / 16)).toUInt32, .i32 byte.toUInt32],
              [.i32 (hexDigit (byte.toNat / 16)).toUInt32]⟩,
            [], 1, [], controls, calls⟩ : Expr α) @ s; E {{ Φ }}) ⊢
      WP (.running ⟨iterLocals ptr 0 0, Project.HexStdio.func18,
        1, [], controls, calls⟩ : Expr α) @ s; E {{ Φ }} := by
  obtain ⟨p0, p1, p2, p3⟩ := wordAccessFacts ptr 0 (by omega)
  obtain ⟨p4, p5, p6, p7⟩ := wordAccessFacts ptr 4 (by omega)
  obtain ⟨p8, p9, p10, p11⟩ := wordAccessFacts ptr 8 (by omega)
  obtain ⟨p12, p13, p14, p15⟩ := wordAccessFacts ptr 12 (by omega)
  have hi0 : (index + 0).toNat = index.toNat + (0 : UInt32).toNat := by simp
  have hnext : index + 1 = UInt32.ofNat (index.toNat + 1) := by
    apply UInt32.toNat_inj.mp
    have hl : (index + 1).toNat = index.toNat + 1 := by
      simpa using Wasm.SepLogic.UInt32.add_ofNat_toNat_noWrap index 1 (by omega)
        (by norm_num [UInt32.size] at hindex ⊢; omega)
    have hr : (UInt32.ofNat (index.toNat + 1)).toNat = index.toNat + 1 :=
      UInt32.toNat_ofNat_of_lt' (by
        norm_num [UInt32.size] at hindex ⊢; omega)
    exact hl.trans hr.symm
  iintro ⟨Hcurrent, Hindex, Hend, HtablePtr, Hinput, Htable, Hfinish⟩
  ihave Hcurrent0 : pointsTo_u32 0 (ptr + 0) sentinel $$ [Hcurrent]
  · rw [UInt32.add_zero]
    iexact Hcurrent
  ihave Hinput0 : (⟨0, index + 0⟩ ↦w byte) $$ [Hinput]
  · rw [UInt32.add_zero]
    iexact Hinput
  ihave HlowFocus := Project.HexEncodeStdio.Helpers.pointsToBytes_focus
    (0 : Nat) (1048576 : UInt32) Project.HexEncodeStdio.Hex.asciiTable
    (byte.toNat % 16) (Project.HexEncodeStdio.Hex.nibble_low_lt byte) $$ Htable
  icases HlowFocus with ⟨%lowByte, Hlow, HputLow, %hlowGet⟩
  have hlowByte : lowByte = hexDigit (byte.toNat % 16) := by
    exact Option.some.inj
      (hlowGet.symm.trans
        (Project.HexEncodeStdio.Hex.asciiTable_getElem?_hexDigit _
          (Project.HexEncodeStdio.Hex.nibble_low_lt byte)))
  subst lowByte
  simp only [Project.HexStdio.func18]
  iapply wp_localGet rfl
  inext
  iapply wp_load32 sentinel p0 p1 p2 p3 $$ Hcurrent0
  inext
  iintro Hcurrent0
  iapply wp_localSet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_const
  inext
  iapply wp_store32 sentinel p0 p1 p2 p3 $$ Hcurrent0
  inext
  iintro Hcurrent0
  iapply wp_block
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_const
  inext
  iapply wp_ne (result := 0) (by rfl)
  inext
  iapply wp_brIfZero
  inext
  iapply wp_const
  inext
  iapply wp_localSet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_load32 index p4 p5 p6 p7 $$ Hindex
  inext
  iintro Hindex
  iapply wp_localTee rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_load32 finish p8 p9 p10 p11 $$ Hend
  inext
  iintro Hend
  iapply wp_eq (result := 0) (by simp [hne])
  inext
  iapply wp_brIfZero
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_const
  inext
  iapply wp_add
  inext
  iapply wp_store32 index p4 p5 p6 p7 $$ Hindex
  inext
  iintro Hindex
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_load32 1048576 p12 p13 p14 p15 $$ HtablePtr
  inext
  iintro HtablePtr
  iapply wp_localTee rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_load8U byte hi0 $$ Hinput0
  inext
  iintro Hinput0
  iapply wp_localTee rfl
  inext
  iapply wp_const
  inext
  iapply wp_and
  inext
  rw [Project.HexEncodeStdio.Hex.low_nibble_u32 byte]
  iapply wp_add
  inext
  simp [iterLocals, List.set]
  ihave HlowActual :
      (⟨0, UInt32.ofNat (byte.toNat % 16) + 1048576⟩ ↦w
        hexDigit (byte.toNat % 16)) $$ [Hlow]
  · rw [UInt32.add_comm (UInt32.ofNat (byte.toNat % 16)) 1048576]
    iexact Hlow
  iapply wp_load8U_zero (address := UInt32.ofNat (byte.toNat % 16) + 1048576)
    (hexDigit (byte.toNat % 16)) $$ HlowActual
  inext
  iintro Hlow
  ihave HcurrentAt0 : pointsTo_u32 0 (ptr + 0) (1114112 : UInt32) $$ [Hcurrent0]
  · rw [UInt32.add_zero]
    iexact Hcurrent0
  iapply wp_store32 (1114112 : UInt32) p0 p1 p2 p3 $$ HcurrentAt0
  inext
  iintro Hcurrent0
  ihave HlowCanonical :
      (⟨0, 1048576 + UInt32.ofNat (byte.toNat % 16)⟩ ↦w
        hexDigit (byte.toNat % 16)) $$ [Hlow]
  · rw [UInt32.add_comm 1048576 (UInt32.ofNat (byte.toNat % 16))]
    iexact Hlow
  ihave Htable := HputLow $$ HlowCanonical
  ihave HhighFocus := Project.HexEncodeStdio.Helpers.pointsToBytes_focus
    (0 : Nat) (1048576 : UInt32) Project.HexEncodeStdio.Hex.asciiTable
    (byte.toNat / 16) (Project.HexEncodeStdio.Hex.nibble_high_lt byte) $$ Htable
  icases HhighFocus with ⟨%highByte, Hhigh, HputHigh, %hhighGet⟩
  have hhighByte : highByte = hexDigit (byte.toNat / 16) := by
    exact Option.some.inj
      (hhighGet.symm.trans
        (Project.HexEncodeStdio.Hex.asciiTable_getElem?_hexDigit _
          (Project.HexEncodeStdio.Hex.nibble_high_lt byte)))
  subst highByte
  iapply wp_localGet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_const
  inext
  iapply wp_shrU32
  inext
  rw [show (4 : UInt32) % 32 = 4 by decide]
  rw [Project.HexEncodeStdio.Hex.high_nibble_u32 byte]
  iapply wp_add
  inext
  simp [iterLocals, List.set]
  ihave HhighActual :
      (⟨0, UInt32.ofNat (byte.toNat / 16) + 1048576⟩ ↦w
        hexDigit (byte.toNat / 16)) $$ [Hhigh]
  · rw [UInt32.add_comm (UInt32.ofNat (byte.toNat / 16)) 1048576]
    iexact Hhigh
  iapply wp_load8U_zero (address := UInt32.ofNat (byte.toNat / 16) + 1048576)
    (hexDigit (byte.toNat / 16)) $$ HhighActual
  inext
  iintro Hhigh
  ihave HhighCanonical :
      (⟨0, 1048576 + UInt32.ofNat (byte.toNat / 16)⟩ ↦w
        hexDigit (byte.toNat / 16)) $$ [Hhigh]
  · rw [UInt32.add_comm 1048576 (UInt32.ofNat (byte.toNat / 16))]
    iexact Hhigh
  ihave Htable := HputHigh $$ HhighCanonical
  iapply wp_localSet rfl
  inext
  iapply wp_exitControl rfl
  inext
  iapply wp_localGet rfl
  inext
  simp [iterLocals, List.set]
  ihave HindexNext : pointsTo_u32 0 (ptr + 4) (index + 1) $$ [Hindex]
  · rw [UInt32.add_comm index 1]
    iexact Hindex
  iapply Hfinish $$ Hcurrent0 HindexNext Hend HtablePtr Hinput0 Htable

/-- When the input cursor has reached the end, the iterator returns its
sentinel without touching the source buffer or lookup table. -/
theorem func18_end_body {hlc : HasLC} {α : Type} [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (ptr finish : UInt32)
    (hptr : ptr.toNat + 12 < UInt32.size)
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 0 ptr sentinel ∗
      pointsTo_u32 0 (ptr + 4) finish ∗
      pointsTo_u32 0 (ptr + 8) finish ∗
      (pointsTo_u32 0 ptr sentinel -∗
        pointsTo_u32 0 (ptr + 4) finish -∗
        pointsTo_u32 0 (ptr + 8) finish -∗
        WP (.running
          ⟨⟨[.i32 ptr], [.i32 sentinel, .i32 finish], [.i32 sentinel]⟩,
            [], 1, [], controls, calls⟩ : Expr α) @ s; E {{ Φ }}) ⊢
      WP (.running ⟨iterLocals ptr 0 0, Project.HexStdio.func18,
        1, [], controls, calls⟩ : Expr α) @ s; E {{ Φ }} := by
  obtain ⟨p0, p1, p2, p3⟩ := wordAccessFacts ptr 0 (by omega)
  obtain ⟨p4, p5, p6, p7⟩ := wordAccessFacts ptr 4 (by omega)
  obtain ⟨p8, p9, p10, p11⟩ := wordAccessFacts ptr 8 (by omega)
  iintro ⟨Hcurrent, Hindex, Hend, Hfinish⟩
  ihave Hcurrent0 : pointsTo_u32 0 (ptr + 0) sentinel $$ [Hcurrent]
  · rw [UInt32.add_zero]
    iexact Hcurrent
  simp only [Project.HexStdio.func18]
  iapply wp_localGet rfl
  inext
  iapply wp_load32 sentinel p0 p1 p2 p3 $$ Hcurrent0
  inext
  iintro Hcurrent0
  iapply wp_localSet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_const
  inext
  iapply wp_store32 sentinel p0 p1 p2 p3 $$ Hcurrent0
  inext
  iintro Hcurrent0
  iapply wp_block
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_const
  inext
  iapply wp_ne (result := 0) (by rfl)
  inext
  iapply wp_brIfZero
  inext
  iapply wp_const
  inext
  iapply wp_localSet rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_load32 finish p4 p5 p6 p7 $$ Hindex
  inext
  iintro Hindex
  iapply wp_localTee rfl
  inext
  iapply wp_localGet rfl
  inext
  iapply wp_load32 finish p8 p9 p10 p11 $$ Hend
  inext
  iintro Hend
  iapply wp_eq (result := 1) (by simp)
  inext
  iapply wp_brIf (by decide) rfl
  inext
  iapply wp_localGet rfl
  inext
  simp [iterLocals, List.set]
  iapply Hfinish $$ Hcurrent0 Hindex Hend

/-- Caller-side contract for the saved-low-digit branch of WAT function 21. -/
theorem wp_call_func18_low {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (ptr saved : UInt32) (hsaved : saved ≠ sentinel)
    (hptr : ptr.toNat + 4 < UInt32.size)
    {callerLocals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      pointsTo_u32 0 ptr saved ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        pointsTo_u32 0 ptr sentinel -∗
        WP (.running ⟨{ callerLocals with values := .i32 saved :: stack },
          code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }}) ⊢
    WP (.running ⟨{ callerLocals with values := .i32 ptr :: stack },
      .call 21 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} := by
  iintro ⟨Hruntime, Hstate, Hcont⟩
  ihave HruntimeLater : ▷ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply Wasm.SmallStep.wp_call Project.HexStdio.«module» 21
    Project.HexStdio.func18Def (by decide) (by rfl) $$ HruntimeLater
  inext
  iintro Hruntime
  simp [Project.HexStdio.func18Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  iapply func18_low_body ptr saved hsaved hptr (controls := [])
    (calls :=
      { locals := { callerLocals with values := stack }, continuation := code,
        resultArity := arity, callerRemainder := remainder, control := controls,
        returningInstance := ⟨0⟩ } :: calls)
  isplitl [Hstate]
  · iexact Hstate
  iintro Hstate
  ihave HruntimeLater : ▷ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply wp_returnFromCallFallthrough' $$ HruntimeLater
  inext
  iintro Hruntime
  simp only [List.take_succ_cons, List.take_zero, List.nil_append,
    List.cons_append]
  iapply Hcont $$ Hruntime Hstate

/-- Caller-side contract for consuming a fresh source byte. -/
theorem wp_call_func18_high {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (ptr index finish : UInt32) (byte : UInt8) (hne : index ≠ finish)
    (hptr : ptr.toNat + 16 < UInt32.size)
    (hindex : index.toNat + 1 < UInt32.size)
    {callerLocals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      pointsTo_u32 0 ptr sentinel ∗
      pointsTo_u32 0 (ptr + 4) index ∗
      pointsTo_u32 0 (ptr + 8) finish ∗
      pointsTo_u32 0 (ptr + 12) 1048576 ∗
      (⟨0, index⟩ ↦w byte) ∗
      pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        pointsTo_u32 0 ptr (hexDigit (byte.toNat % 16)).toUInt32 -∗
        pointsTo_u32 0 (ptr + 4) (index + 1) -∗
        pointsTo_u32 0 (ptr + 8) finish -∗
        pointsTo_u32 0 (ptr + 12) 1048576 -∗
        (⟨0, index⟩ ↦w byte) -∗
        pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable -∗
        WP (.running
          ⟨{ callerLocals with
              values := .i32 (hexDigit (byte.toNat / 16)).toUInt32 :: stack },
            code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }}) ⊢
    WP (.running ⟨{ callerLocals with values := .i32 ptr :: stack },
      .call 21 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} := by
  iintro ⟨Hruntime, Hcurrent, Hindex, Hend, HtablePtr, Hinput, Htable, Hcont⟩
  ihave HruntimeLater : ▷ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply Wasm.SmallStep.wp_call Project.HexStdio.«module» 21
    Project.HexStdio.func18Def (by decide) (by rfl) $$ HruntimeLater
  inext
  iintro Hruntime
  simp [Project.HexStdio.func18Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  iapply func18_high_body ptr index finish byte hne hptr hindex
    (controls := [])
    (calls :=
      { locals := { callerLocals with values := stack }, continuation := code,
        resultArity := arity, callerRemainder := remainder, control := controls,
        returningInstance := ⟨0⟩ } :: calls)
  isplitl [Hcurrent]
  · iexact Hcurrent
  isplitl [Hindex]
  · iexact Hindex
  isplitl [Hend]
  · iexact Hend
  isplitl [HtablePtr]
  · iexact HtablePtr
  isplitl [Hinput]
  · iexact Hinput
  isplitl [Htable]
  · iexact Htable
  iintro Hcurrent Hindex Hend HtablePtr Hinput Htable
  ihave HruntimeLater : ▷ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply wp_returnFromCallFallthrough' $$ HruntimeLater
  inext
  iintro Hruntime
  simp only [List.take_succ_cons, List.take_zero, List.nil_append,
    List.cons_append]
  iapply Hcont $$ Hruntime Hcurrent Hindex Hend HtablePtr Hinput Htable

/-- Caller-side contract for the iterator's end sentinel. -/
theorem wp_call_func18_end {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (ptr finish : UInt32) (hptr : ptr.toNat + 12 < UInt32.size)
    {callerLocals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      pointsTo_u32 0 ptr sentinel ∗
      pointsTo_u32 0 (ptr + 4) finish ∗
      pointsTo_u32 0 (ptr + 8) finish ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        pointsTo_u32 0 ptr sentinel -∗
        pointsTo_u32 0 (ptr + 4) finish -∗
        pointsTo_u32 0 (ptr + 8) finish -∗
        WP (.running
          ⟨{ callerLocals with values := .i32 sentinel :: stack },
            code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }}) ⊢
    WP (.running ⟨{ callerLocals with values := .i32 ptr :: stack },
      .call 21 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} := by
  iintro ⟨Hruntime, Hcurrent, Hindex, Hend, Hcont⟩
  ihave HruntimeLater : ▷ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply Wasm.SmallStep.wp_call Project.HexStdio.«module» 21
    Project.HexStdio.func18Def (by decide) (by rfl) $$ HruntimeLater
  inext
  iintro Hruntime
  simp [Project.HexStdio.func18Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  iapply func18_end_body ptr finish hptr (controls := [])
    (calls :=
      { locals := { callerLocals with values := stack }, continuation := code,
        resultArity := arity, callerRemainder := remainder, control := controls,
        returningInstance := ⟨0⟩ } :: calls)
  isplitl [Hcurrent]
  · iexact Hcurrent
  isplitl [Hindex]
  · iexact Hindex
  isplitl [Hend]
  · iexact Hend
  iintro Hcurrent Hindex Hend
  ihave HruntimeLater : ▷ runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply wp_returnFromCallFallthrough' $$ HruntimeLater
  inext
  iintro Hruntime
  simp only [List.take_succ_cons, List.take_zero, List.nil_append,
    List.cons_append]
  iapply Hcont $$ Hruntime Hcurrent Hindex Hend

/-- Indexed form of the fresh-byte call contract. It borrows the current byte
from the complete source buffer and restores that buffer before returning. -/
theorem wp_call_func18_high_at {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (iter source : UInt32) (input : List UInt8) (i : Nat)
    (hi : i < input.length)
    (hiter : iter.toNat + 16 < UInt32.size)
    (hsource : source.toNat + input.length + 1 < UInt32.size)
    {callerLocals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      pointsTo_u32 0 iter sentinel ∗
      pointsTo_u32 0 (iter + 4) (source + UInt32.ofNat i) ∗
      pointsTo_u32 0 (iter + 8) (source + UInt32.ofNat input.length) ∗
      pointsTo_u32 0 (iter + 12) 1048576 ∗
      pointsToBytes 0 source input ∗
      pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        pointsTo_u32 0 iter
          (hexDigit (input[i].toNat % 16)).toUInt32 -∗
        pointsTo_u32 0 (iter + 4) (source + UInt32.ofNat (i + 1)) -∗
        pointsTo_u32 0 (iter + 8) (source + UInt32.ofNat input.length) -∗
        pointsTo_u32 0 (iter + 12) 1048576 -∗
        pointsToBytes 0 source input -∗
        pointsToBytes 0 1048576 Project.HexEncodeStdio.Hex.asciiTable -∗
        WP (.running
          ⟨{ callerLocals with
              values := .i32 (hexDigit (input[i].toNat / 16)).toUInt32 :: stack },
            code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }}) ⊢
    WP (.running ⟨{ callerLocals with values := .i32 iter :: stack },
      .call 21 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      {{ Φ }} := by
  have hiNat :
      (source + UInt32.ofNat i).toNat = source.toNat + i :=
    UInt32.add_ofNat_toNat_noWrap source i
      (by
        have hsize : UInt32.size = 4294967296 := by decide
        rw [hsize] at hsource
        omega)
      (by norm_num [UInt32.size] at hsource ⊢; omega)
  have hlenNat :
      (source + UInt32.ofNat input.length).toNat =
        source.toNat + input.length :=
    UInt32.add_ofNat_toNat_noWrap source input.length
      (by norm_num [UInt32.size] at hsource ⊢; omega)
      (by norm_num [UInt32.size] at hsource ⊢; omega)
  have hne : source + UInt32.ofNat i ≠
      source + UInt32.ofNat input.length := by
    intro h
    have := congrArg UInt32.toNat h
    rw [hiNat, hlenNat] at this
    omega
  have hindex : (source + UInt32.ofNat i).toNat + 1 < UInt32.size := by
    rw [hiNat]
    omega
  have hnext : (source + UInt32.ofNat i) + 1 =
      source + UInt32.ofNat (i + 1) := by
    apply UInt32.toNat_inj.mp
    have hl : ((source + UInt32.ofNat i) + 1).toNat =
        (source + UInt32.ofNat i).toNat + 1 := by
      simpa using UInt32.add_ofNat_toNat_noWrap
        (source + UInt32.ofNat i) 1 (by decide)
          (by norm_num [UInt32.size] at hindex ⊢; omega)
    have hr : (source + UInt32.ofNat (i + 1)).toNat =
        source.toNat + (i + 1) :=
      UInt32.add_ofNat_toNat_noWrap source (i + 1)
        (by norm_num [UInt32.size] at hsource ⊢; omega)
        (by norm_num [UInt32.size] at hsource ⊢; omega)
    rw [hl, hiNat, hr]
    omega
  iintro ⟨Hruntime, Hcurrent, Hindex, Hend, HtablePtr, Hsource, Htable, Hcont⟩
  ihave Hfocus := Project.HexEncodeStdio.Helpers.pointsToBytes_focus
    (0 : Nat) source input i hi $$ Hsource
  icases Hfocus with ⟨%byte, Hbyte, Hput, %hbyte⟩
  have hbyteEq : byte = input[i] := by
    exact Option.some.inj (hbyte.symm.trans (List.getElem?_eq_getElem hi))
  subst byte
  iapply wp_call_func18_high iter (source + UInt32.ofNat i)
    (source + UInt32.ofNat input.length) input[i] hne hiter hindex
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hcurrent]
  · iexact Hcurrent
  isplitl [Hindex]
  · iexact Hindex
  isplitl [Hend]
  · iexact Hend
  isplitl [HtablePtr]
  · iexact HtablePtr
  isplitl [Hbyte]
  · iexact Hbyte
  isplitl [Htable]
  · iexact Htable
  iintro Hruntime Hcurrent Hindex Hend HtablePtr Hbyte Htable
  ihave Hsource := Hput $$ Hbyte
  ihave HindexNext :
      pointsTo_u32 0 (iter + 4) (source + UInt32.ofNat (i + 1)) $$ [Hindex]
  · rw [← hnext]
    iexact Hindex
  iapply Hcont $$ Hruntime Hcurrent HindexNext Hend HtablePtr Hsource Htable

end Project.HexEncodeStdio.Iterator
