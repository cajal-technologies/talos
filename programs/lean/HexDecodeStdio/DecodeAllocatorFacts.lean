import HexDecodeStdio.DecodeLoopPairInvalidLowOperational
import HexDecodeStdio.ReadToEndInitial

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

theorem allocatorRequiredPages_eight_toNat (bump : UInt32)
    (hbump : bump ≠ 0)
    (hsmall : 65535 + (bump.toNat + 8) < UInt32.size) :
    (allocatorRequiredPages 8 1 bump).toNat =
      (65535 + (bump.toNat + 8)) / 65536 := by
  have hfinish : (allocatorFinish 8 1 bump).toNat = bump.toNat + 8 := by
    rw [allocatorFinish_one_eq_comm 8 bump hbump, UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by
      norm_num [UInt32.size] at hsmall ⊢
      omega)]
  have hadd : ((65535 : UInt32) + allocatorFinish 8 1 bump).toNat =
      65535 + (allocatorFinish 8 1 bump).toNat := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by
      rw [hfinish]
      norm_num [UInt32.size] at hsmall ⊢
      omega)]
  rw [allocatorRequiredPages, UInt32.toNat_shiftRight, hadd, hfinish]
  change (65535 + (bump.toNat + 8)) >>> 16 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem ByteGrowSuccess.fresh_eight_finish_bound
    {store final : MachineStore Universal.State} {oldPtr bump : UInt32}
    (h : ByteGrowSuccess store 0 oldPtr 8 bump final)
    (hbump : bump ≠ 0)
    (hsmall : 65535 + (bump.toNat + 8) < UInt32.size)
    (hpages : store.wasm.mem.pages < UInt32.size) :
    bump.toNat + 8 ≤ final.wasm.mem.pages * 65536 := by
  cases h with
  | freshNoGrow hzero hfit =>
      simp only [allocatorBumpStore]
      apply ceil_pages_bound
      rw [← allocatorRequiredPages_eight_toNat bump hbump hsmall]
      have hn := UInt32.le_iff_toNat_le.mp hfit
      rw [UInt32.toNat_ofNat_of_lt' hpages] at hn
      exact hn
  | freshGrow hzero memory previousPages hgrow =>
      simp only [allocatorBumpStore, allocatorGrownStore]
      have hfacts := mem_grow_some_facts store.wasm.mem memory
        (allocatorRequiredPages 8 1 bump - UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) previousPages hgrow
      have hpagesNat : (UInt32.ofNat store.wasm.mem.pages).toNat =
          store.wasm.mem.pages := UInt32.toNat_ofNat_of_lt' hpages
      have hrequiredSmall : (allocatorRequiredPages 8 1 bump).toNat <
          UInt32.size := UInt32.toNat_lt_size _
      have hcover : (allocatorRequiredPages 8 1 bump).toNat ≤ memory.pages := by
        rw [hfacts.2]
        by_cases hle : store.wasm.mem.pages ≤
            (allocatorRequiredPages 8 1 bump).toNat
        · have hleU : UInt32.ofNat store.wasm.mem.pages ≤
              allocatorRequiredPages 8 1 bump := by
            apply UInt32.le_iff_toNat_le.mpr
            rw [hpagesNat]
            exact hle
          rw [UInt32.toNat_sub_of_le _ _ hleU, hpagesNat]
          omega
        · omega
      apply le_trans (ceil_pages_bound (pages :=
        (allocatorRequiredPages 8 1 bump).toNat) (by
          rw [allocatorRequiredPages_eight_toNat bump hbump hsmall]))
      exact Nat.mul_le_mul_right 65536 hcover
  | reallocNoGrow hnonzero hfit => contradiction
  | reallocGrow hnonzero memory previousPages hgrow => contradiction

theorem ByteGrowSuccess.fresh_preserves_readBytes_disjoint
    {store final : MachineStore Universal.State}
    {oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store 0 oldPtr newCapacity oldBump final)
    (off len : Nat)
    (haddr : off + len ≤ 1053960 ∨ 1053964 ≤ off) :
    final.wasm.mem.readBytes off len = store.wasm.mem.readBytes off len := by
  cases h with
  | freshNoGrow hzero hfit =>
      exact Mem.readBytes_write32_disjoint _ _ _ _ _ haddr
  | freshGrow hzero memory previousPages hgrow =>
      simp only [allocatorBumpStore, allocatorGrownStore]
      rw [Mem.readBytes_write32_disjoint _ _ _ _ _ haddr]
      simp only [Mem.readBytes, Mem.grow_success_bytes_eq _ _ _ _ _ hgrow]
  | reallocNoGrow hnonzero hfit => contradiction
  | reallocGrow hnonzero memory previousPages hgrow => contradiction

/-- The fixed eight-byte allocation used to seed the decoder either succeeds
with a nonnegative, nonwrapping end pointer, or follows the allocator's OOM
path.  The generic allocator summary deliberately forgets this guard, so the
decoder keeps it explicitly. -/
theorem allocator_eight_call_outcome
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295)
    (hbump : oldBump ≠ 0) (hbumpSmall : oldBump.toNat < 2 ^ 31) :
    ((oldBump.toNat + 8 < 2 ^ 31) ∧
      ((allocatorRequiredPages 8 1 oldBump ≤
            UInt32.ofNat store.wasm.mem.pages) ∧ Reaches
          ⟨.running
            ⟨⟨params, localValues, [.i32 1, .i32 8] ++ stack⟩,
              [.call 15] ++ code, arity, remainder, controls, calls⟩,
            store⟩
          ⟨.running
            ⟨⟨params, localValues,
                .i32 (allocatorPtr oldBump 1) :: stack⟩,
              code, arity, remainder, controls, calls⟩,
            allocatorBumpStore store (allocatorFinish 8 1 oldBump)⟩ ∨
        ∃ memory previousPages,
          store.wasm.mem.grow
              (allocatorRequiredPages 8 1 oldBump -
                UInt32.ofNat store.wasm.mem.pages)
              (store.wasm.memoryCap store.runtime.currentModule 0) =
                some (memory, previousPages) ∧
          Reaches
            ⟨.running
              ⟨⟨params, localValues, [.i32 1, .i32 8] ++ stack⟩,
                [.call 15] ++ code, arity, remainder, controls, calls⟩,
              store⟩
            ⟨.running
              ⟨⟨params, localValues,
                  .i32 (allocatorPtr oldBump 1) :: stack⟩,
                code, arity, remainder, controls, calls⟩,
              allocatorBumpStore (allocatorGrownStore store memory)
                (allocatorFinish 8 1 oldBump)⟩)) ∨
      TrapsWith
        ⟨.running
          ⟨⟨params, localValues, [.i32 1, .i32 8] ++ stack⟩,
            [.call 15] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        (.host OOM.trapMessage)
        (fun final => final.wasm.host.oom.raised = true) := by
  have hfirst : ¬ ((if oldBump = 0 then 1054000 else oldBump) +
        ((0xffffffff : UInt32) + 1)) < ((0xffffffff : UInt32) + 1) := by
    simp [hbump]
  have hfinishNat : (allocatorFinish 8 1 oldBump).toNat =
      oldBump.toNat + 8 := by
    rw [allocatorFinish_one_eq_comm 8 oldBump hbump, UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    norm_num [UInt32.size] at hbumpSmall ⊢
    omega
  have hsecond : ¬
      8 + (((if oldBump = 0 then 1054000 else oldBump) +
        ((0xffffffff : UInt32) + 1)) &&& (0 - 1)) <
      (((if oldBump = 0 then 1054000 else oldBump) +
        ((0xffffffff : UInt32) + 1)) &&& (0 - 1)) := by
    simpa [allocatorPtr, allocatorFinish, allocatorBase, hbump] using
      (show ¬allocatorFinish 8 1 oldBump < allocatorPtr oldBump 1 by
        rw [allocatorPtr_one_eq oldBump hbump]
        intro hlt
        have hn := UInt32.lt_iff_toNat_lt.mp hlt
        rw [hfinishNat] at hn
        omega)
  by_cases hsafe : oldBump.toNat + 8 < 2 ^ 31
  · have hout := allocator_call_outcome store params localValues stack code arity
      remainder controls calls 8 1 oldBump hmod henv hread hbound hpages
    rcases hout with ⟨_hfinish, hsuccess⟩ | htrap
    · exact Or.inl ⟨hsafe, hsuccess⟩
    · exact Or.inr htrap
  · right
    have hnegative :
        (allocatorFinish 8 1 oldBump).toInt32 < UInt32.toInt32 0 := by
      by_contra hn
      have hsigned := UInt32.toNat_lt_signed_limit_of_not_negative
        (allocatorFinish 8 1 oldBump) hn
      rw [hfinishNat] at hsigned
      exact hsafe hsigned
    exact allocator_signed_limit_traps store params localValues stack code
      arity remainder controls calls 8 1 oldBump hmod henv hread hbound
      hfirst hsecond (by
        simpa [allocatorFinish, allocatorPtr, allocatorBase, hbump] using
          hnegative)

end Submission.HexDecodeStdio
