import CodeLib.RustStd.MemArray
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# A verified copy loop over a `u32` array

The companion to `MemFillLoop`: the canonical word-by-word copy loop reads each
of the `n` `u32` words of `[src, src+4n)` and writes it to `[dst, dst+4n)`, and
afterwards the destination view equals the (unchanged) source view —

```
st'.mem.words32 dst n = st.mem.words32 src n
```

for all `n`, given the two regions are disjoint, while every byte outside
`[dst, dst+4n)` is left untouched (the frame condition, so the theorem composes
with facts about neighbouring memory). This is the shape LLVM emits
for a small `copy_from_slice` at `opt-level = 0` (a `load`/`store` loop, not a
`memory.copy`), and the direct analogue of `merge_sort`'s copy helpers. It
exercises the invariant/variant loop rule together with the `words32` view and
`MemRegion` disjointness. -/

namespace Wasm

/-- Copy loop. Params `dst : i32`, `src : i32`, `n : i32`; local `i : i32`.
Copies `mem[src + 4*i]` to `mem[dst + 4*i]` for `i = 0 … n-1`. -/
def CopyWords : Program := [
  .const 0, .localSet 3,
  .loop 0 0 [
    .block 0 0 [
      .block 0 0 [
        .localGet 3, .localGet 2, .ltU, .br_if 0,
        .br 1
      ],
      .localGet 0, .localGet 3, .const 2, .shl, .add,
      .localGet 1, .localGet 3, .const 2, .shl, .add,
      .load32 0, .store32 0,
      .localGet 3, .const 1, .add, .localSet 3,
      .br 1 ] ]
]

set_option maxHeartbeats 1000000 in
/-- Running `CopyWords` on a store where the two `u32` arrays are addressable,
within the wasm32 page cap (no wraparound), and **disjoint** terminates with the
destination holding a copy of the source, the source unchanged. -/
theorem copyWords_spec (m : Module) (st : Store Unit) (dst src n : UInt32)
    (hsrc : src.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hdst : dst.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hpages : st.mem.pages ≤ 65536)
    (hdisj : MemRegion.Disjoint ⟨dst, 4 * n.toNat⟩ ⟨src, 4 * n.toNat⟩) :
    wp m CopyWords
        (fun c => ∃ st' s', c = .Fallthrough st' s'
          ∧ st'.mem.words32 dst n.toNat = st.mem.words32 src n.toNat
          ∧ st'.mem.words32 src n.toNat = st.mem.words32 src n.toNat
          ∧ st'.mem.pages = st.mem.pages
          ∧ ∀ a : Nat, (a < dst.toNat ∨ dst.toNat + 4 * n.toNat ≤ a) →
              st'.mem.bytes a = st.mem.bytes a)
        st { params := [.i32 dst, .i32 src, .i32 n], locals := [.i32 0], values := [] } := by
  have hcap : st.mem.pages * 65536 ≤ 4294967296 := by
    have := Nat.mul_le_mul_right 65536 hpages; omega
  have hdisj : dst.toNat + 4 * n.toNat ≤ src.toNat ∨ src.toNat + 4 * n.toNat ≤ dst.toNat := hdisj
  unfold CopyWords
  wp_run
  simp
  apply wp_loop_cons
    (Inv := fun st' s' => ∃ i : UInt32,
      s' = ⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩
      ∧ i.toNat ≤ n.toNat
      ∧ st'.mem.words32 dst i.toNat = st'.mem.words32 src i.toNat
      ∧ st'.mem.words32 src n.toNat = st.mem.words32 src n.toNat
      ∧ st'.mem.pages = st.mem.pages
      ∧ ∀ a : Nat, (a < dst.toNat ∨ dst.toNat + 4 * n.toNat ≤ a) →
          st'.mem.bytes a = st.mem.bytes a)
    (μ := fun _ s' => match s'.locals.headD (.i32 0) with | .i32 i => n.toNat - i.toNat | _ => 0)
  · exact ⟨0, rfl, by simp, by simp [Mem.words32], rfl, rfl, fun a _ => rfl⟩
  · rintro st' s' ⟨i, rfl, hile, hcopy, hsrceq, hpg, hframe⟩
    apply wp_block_cons
    apply wp_block_cons
    wp_run
    simp
    by_cases hlt : i < n
    · -- body: copy word i
      have hilt : i.toNat < n.toNat := hlt
      have hoi : UInt32.ofNat i.toNat = i := by simp [UInt32.ofNat_toNat]
      have hshlU : i <<< 2 = 4 * i := MemRegion.shl2_eq_mul4 i
      have hmod1 : (1 + i.toNat) % 4294967296 = i.toNat + 1 := by
        rw [Nat.mod_eq_of_lt (by have := n.toNat_lt; omega)]; omega
      have hshlN : i.toNat <<< 2 = i.toNat * 4 := by rw [Nat.shiftLeft_eq]
      have haddr_d : 4 * i + dst = dst + 4 * UInt32.ofNat i.toNat := by
        rw [hoi]; exact UInt32.add_comm _ _
      have haddr_s : 4 * i + src = src + 4 * UInt32.ofNat i.toNat := by
        rw [hoi]; exact UInt32.add_comm _ _
      have hda : (dst + 4 * UInt32.ofNat i.toNat).toNat = dst.toNat + 4 * i.toNat :=
        Mem.words32_slotAddr_toNat dst i.toNat (by omega)
      simp only [hlt, ↓reduceIte, hshlU, hshlN, hmod1, haddr_d, haddr_s]
      set w : UInt32 := st'.mem.read32 (src + 4 * UInt32.ofNat i.toNat) with hw
      refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [Nat.mod_eq_of_lt (by omega)]; omega      -- load in bounds
      · rw [Nat.mod_eq_of_lt (by omega)]; omega      -- store in bounds
      · omega                                        -- i+1 ≤ n
      · -- words32 dst (i+1) = words32 src (i+1) at the new store
        rw [Mem.words32_write32_snoc st'.mem dst i.toNat w (by omega),
            Mem.words32_write32_outside st'.mem src (i.toNat + 1)
              (dst + 4 * UInt32.ofNat i.toNat) w (by omega) (by rw [hda]; omega),
            Mem.words32_succ, hcopy]
      · -- words32 src n unchanged
        rw [Mem.words32_write32_outside st'.mem src n.toNat
              (dst + 4 * UInt32.ofNat i.toNat) w (by omega) (by rw [hda]; omega), hsrceq]
      · exact hpg                                    -- pages
      · -- frame: the write lands in `[dst, dst+4n)`, so bytes outside are kept
        intro a ha
        rw [Mem.write32_bytes_of_disjoint st'.mem (dst + 4 * UInt32.ofNat i.toNat) w a
              (by rw [hda]; omega)]
        exact hframe a ha
      · omega                                        -- variant
    · -- exit: i = n, dst view already equals src view
      have hin : i.toNat = n.toNat := by
        have : ¬ i.toNat < n.toNat := hlt
        omega
      simp only [hlt, ↓reduceIte]
      rw [hin] at hcopy
      exact ⟨hcopy.trans hsrceq, hsrceq, hpg, hframe⟩

end Wasm
