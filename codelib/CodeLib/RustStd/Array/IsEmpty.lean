import CodeLib.RustStd.Array.Basic

/-! Contextual iris-lean chunk for `&[T]::is_empty`. -/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

abbrev isEmptyValue (len : UInt32) : UInt32 :=
  if len = 0 then 1 else 0

theorem isEmptyValue_and_one (len : UInt32) :
    1 &&& isEmptyValue len = isEmptyValue len := by
  unfold isEmptyValue
  by_cases h : len = 0 <;> simp [h]

/-- The emitted zero-test and bool mask compute the canonical `0`/`1` result
and resume an arbitrary iris-lean continuation. -/
theorem isEmpty_chunk :
    UnChunk (T := UInt32)
      [.const 0, .eq, .const 1, .and] isEmptyValue := by
  intro α hlc inst s E Φ params localValues rest arity remainder
    controls calls len vs
  simp only [toV_u32, List.cons_append, List.nil_append]
  by_cases hlen : len = 0
  · simp only [isEmptyValue, hlen, if_true]
    iintro Hwp
    iapply Wasm.SmallStep.wp_const
    inext
    iapply Wasm.SmallStep.wp_eq (result := 1) (by simp)
    inext
    iapply Wasm.SmallStep.wp_const
    inext
    iapply Wasm.SmallStep.wp_and
    rw [show (1 &&& 1 : UInt32) = 1 by decide]
    inext
    iexact Hwp
  · simp only [isEmptyValue, hlen, if_false]
    iintro Hwp
    iapply Wasm.SmallStep.wp_const
    inext
    iapply Wasm.SmallStep.wp_eq (result := 0) (by simp [hlen])
    inext
    iapply Wasm.SmallStep.wp_const
    inext
    iapply Wasm.SmallStep.wp_and
    rw [show (0 &&& 1 : UInt32) = 0 by decide]
    inext
    iexact Hwp

end Wasm.RustStd.Array
