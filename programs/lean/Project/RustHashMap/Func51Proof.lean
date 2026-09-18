import Project.RustHashMap.DropErrorContracts
import CodeLib.SepLogic.SmallStepTotalLiftingBytesTerminal

/-!
# Proof of the byte comparison of the decode-error conversion

Local `func51` (absolute index 54) is the smallest body of the subtree
below the conversion.  It loads one byte from each of its two arguments,
masks both with 255, and returns 1 when the bytes are equal.  It keeps no
frame and it calls nothing, so the proof needs the runtime context and the
two bytes and nothing else.

The mask is the identity on a byte, and `UInt8.toUInt32` is injective, so
the result is the comparison of the two bytes themselves.
-/

namespace Project.RustHashMap.Func51Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

/-- A byte survives the mask with 255. -/
private theorem byte_and_255 (byte : UInt8) :
    byte.toUInt32 &&& 255 = byte.toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and]
  have hbyte : byte.toUInt32.toNat < 256 := by
    rw [UInt8.toNat_toUInt32]
    exact byte.toNat_lt_size
  have h255 : (255 : UInt32).toNat = 2 ^ 8 - 1 := by decide
  rw [h255, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The body compares the masked bytes and masks the answer again.  Both
masks are the identity here. -/
private theorem compare_result (byteA byteB : UInt8) :
    (if byteA.toUInt32 &&& 255 = byteB.toUInt32 &&& 255 then (1 : UInt32)
      else 0) &&& 1 = if byteA = byteB then 1 else 0 := by
  rw [byte_and_255, byte_and_255]
  by_cases hsame : byteA = byteB
  · subst hsame
    rw [if_pos rfl, if_pos rfl]
    decide
  · rw [if_neg hsame, if_neg (fun heq => hsame (UInt8.toUInt32_inj.mp heq))]
    decide

private theorem func51_index :
    Project.RustHashMap.«module».funcs[51]? =
      some Project.RustHashMap.func51Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The comparison returns 1 exactly when the two bytes are equal. -/
theorem func51_correct [WasmSmallStepGS hlc Universal.State] :
    Func51Spec (hlc := hlc) := by
  unfold Func51Spec CallContract callExpr
  intro ptrA ptrB byteA byteB callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, HsliceA, HsliceB, Hcont⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 54
      Project.RustHashMap.func51Def (by decide) func51_index with Hmodule
  simp [Project.RustHashMap.func51Def, Project.RustHashMap.func51,
    Function.toLocals, Function.numParams]
  ihave ⟨%hboundA, HbyteA⟩ :=
    (Slices.ByteSlice_singleton 0 ptrA byteA).mp $$ HsliceA
  ihave ⟨%hboundB, HbyteB⟩ :=
    (Slices.ByteSlice_singleton 0 ptrB byteB).mp $$ HsliceB
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load8U_addr_gen byteA with HbyteA
  wasm_twp_pures [twp_const twp_and twp_localGet]
  wasm_twp_rebind twp_load8U_addr_gen byteB with HbyteB
  wasm_twp_pures [twp_const twp_and twp_eq twp_const twp_and]
  isimp only [compare_result]
  wasm_twp_return_from_call Hmodule [List.take_succ_cons, List.take_zero,
    List.cons_append, List.nil_append]
  ihave HsliceA := (Slices.ByteSlice_singleton 0 ptrA byteA).mpr $$
    [HbyteA]
  · isplitl_pureexact hboundA
    iexact HbyteA
  ihave HsliceB := (Slices.ByteSlice_singleton 0 ptrB byteB).mpr $$
    [HbyteB]
  · isplitl_pureexact hboundB
    iexact HbyteB
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.cons_append,
    List.nil_append] at Hcont
  iapply Hcont $$ [Hmodule Henv] HsliceA HsliceB
  · isplitl_exact Hmodule
    · iexact Henv

end Project.RustHashMap.Func51Proof
