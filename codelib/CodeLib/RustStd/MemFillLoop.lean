import CodeLib.RustStd.MemArray
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# A universally-quantified loop-over-memory proof

Every memory example in `interpreter/.../Examples/` is a concrete
`native_decide` check, because symbolic memory framing lives here in `CodeLib`,
downstream of the interpreter. This file closes that gap with the first proof
that a **loop** establishes a property of a **whole memory region for all `n`**:
the canonical fill loop writes `v` to each of the `n` `u64` slots of
`[base, base + 8n)`, and afterwards `mem.words64 base n = replicate n v` while
every byte *outside* `[base, base + 8n)` is left untouched (the frame
condition, so the theorem composes with facts about neighbouring memory).

It exercises the invariant/variant loop rule (`wp_loop_cons`), the `MemRegion`
framing algebra, and the `words64` view together — the exact shape a
memory-mutating corpus proof (e.g. `merge_sort`) needs. -/

namespace Wasm

/-- Fill loop. Params `base : i32`, `n : i32`, `v : i64`; local `i : i32`.
Writes `v` to `mem[base + 8*i]` for `i = 0 … n-1`. Structure mirrors the
`SimpleLoop` example's while-loop idiom. -/
def FillWords : Program := [
  .const 0, .localSet 3,
  .loop 0 0 [
    .block 0 0 [
      .block 0 0 [
        .localGet 3, .localGet 1, .ltU, .br_if 0,
        .br 1
      ],
      .localGet 0, .localGet 3, .const 3, .shl, .add,
      .localGet 2, .store64 0,
      .localGet 3, .const 1, .add, .localSet 3,
      .br 1 ] ]
]

set_option maxHeartbeats 1000000 in
/-- Running `FillWords` on a store whose memory is large enough to hold the
array (and within the wasm32 page cap, so element addresses do not wrap)
terminates with `[base, base + 8n)` filled with `v` — stated over the whole
region via `Mem.words64` — and every byte outside the region left unchanged. -/
theorem fillWords_spec (m : Module) (st : Store Unit) (base n : UInt32) (v : UInt64)
    (hbnd : base.toNat + 8 * n.toNat ≤ st.mem.pages * 65536)
    (hpages : st.mem.pages ≤ 65536) :
    wp m FillWords
        (fun c => ∃ st' s', c = .Fallthrough st' s'
          ∧ st'.mem.words64 base n.toNat = List.replicate n.toNat v
          ∧ st'.mem.pages = st.mem.pages
          ∧ ∀ a : Nat, (a < base.toNat ∨ base.toNat + 8 * n.toNat ≤ a) →
              st'.mem.bytes a = st.mem.bytes a)
        st { params := [.i32 base, .i32 n, .i64 v], locals := [.i32 0], values := [] } := by
  have hcap : st.mem.pages * 65536 ≤ 4294967296 := by
    have := Nat.mul_le_mul_right 65536 hpages; omega
  unfold FillWords
  wp_run
  simp
  apply wp_loop_cons
    (Inv := fun st' s' => ∃ i : UInt32,
      s' = ⟨[.i32 base, .i32 n, .i64 v], [.i32 i], []⟩
      ∧ i.toNat ≤ n.toNat
      ∧ st'.mem.words64 base i.toNat = List.replicate i.toNat v
      ∧ st'.mem.pages = st.mem.pages
      ∧ ∀ a : Nat, (a < base.toNat ∨ base.toNat + 8 * n.toNat ≤ a) →
          st'.mem.bytes a = st.mem.bytes a)
    (μ := fun _ s' => match s'.locals.headD (.i32 0) with | .i32 i => n.toNat - i.toNat | _ => 0)
  · -- initial: i = 0, region empty, memory untouched
    exact ⟨0, rfl, by simp, by simp [Mem.words64], rfl, fun a _ => rfl⟩
  · -- step
    rintro st' s' ⟨i, rfl, hile, hfill, hpg, hframe⟩
    apply wp_block_cons
    apply wp_block_cons
    wp_run
    simp
    by_cases hlt : i < n
    · -- body: write slot i, increment
      have hilt : i.toNat < n.toNat := hlt
      have hoi : UInt32.ofNat i.toNat = i := by simp [UInt32.ofNat_toNat]
      have hmod1 : (1 + i.toNat) % 4294967296 = i.toNat + 1 := by
        rw [Nat.mod_eq_of_lt (by have := n.toNat_lt; omega)]; omega
      have hshlN : i.toNat <<< 3 = i.toNat * 8 := by rw [Nat.shiftLeft_eq]
      -- The `(const 3) shl` address computation is the `MemRegion` slot bridge.
      have hshlU : i <<< 3 = 8 * i := MemRegion.shl3_eq_mul8 i
      have haddrU : i <<< 3 + base = base + 8 * UInt32.ofNat i.toNat := by
        rw [hshlU, hoi]; bv_decide
      have haddrN : (i <<< 3 + base).toNat = base.toNat + 8 * i.toNat := by
        rw [haddrU]; exact Mem.words64_slotAddr_toNat base i.toNat (by omega)
      simp only [hlt, ↓reduceIte, hshlN, hmod1]
      refine ⟨?_, ⟨?_, ?_, hpg, ?_⟩, ?_⟩
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · omega
      · rw [haddrU]
        exact Mem.words64_write64_extend st'.mem base i.toNat v (by omega) hfill
      · -- frame: the write lands in `[base, base+8n)`, so bytes outside are kept
        intro a ha
        rw [Mem.write64_bytes_of_disjoint st'.mem (i <<< 3 + base) v a (by rw [haddrN]; omega)]
        exact hframe a ha
      · omega
    · -- exit: i ≥ n, so i = n; region already fully filled
      have hin : i.toNat = n.toNat := by
        have : ¬ i.toNat < n.toNat := hlt
        omega
      simp only [hlt, ↓reduceIte]
      refine ⟨?_, hpg, hframe⟩
      rw [← hin]; exact hfill

end Wasm
