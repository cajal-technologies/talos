import Project.EncodeDecode.Program
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `encode_decode`

A *frame* is a 4-byte little-endian `u32` length followed by that many payload
bytes. `encode` writes a frame; `decode` reads one back. The exports are proved
bottom-up, reusing the `RustStd/Mem.lean` framing trunk (including the new
`memory.copy` read-back lemmas).

`func0`/`func1` are the `load32`/`store32` helpers that opt-0 outlines from
`read_unaligned`/`write_unaligned`; `func3` = `encode`, `func2` = `decode`.
-/

namespace Project.EncodeDecode.Spec

open Wasm

set_option maxRecDepth 1048576
set_option linter.unusedSimpArgs false

/-- `func1` — the `store32` helper (`write_unaligned`): stores the `u32` `p1` at
address `p0`, roundtripping through a scratch slot at `global0 - 4`. -/
theorem func1_store (env : HostEnv Unit) (st : Store Unit) (p0 p1 p2 g0 : UInt32)
    (hg   : st.globals.globals[0]? = some (.i32 g0))
    (hg16 : 16 ≤ g0.toNat)
    (hgB  : g0.toNat ≤ st.mem.pages * 65536)
    (hp0  : p0.toNat + 4 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 1 st [.i32 p2, .i32 p1, .i32 p0]
      (fun st' rs => rs = []
        ∧ st'.mem = (st.mem.write32 (g0 - 16 + 12) p1).write32 p0 p1
        ∧ st'.globals = st.globals) := by
  refine TerminatesWith.of_returns_wp (f := func1Def) (rs := []) rfl rfl ?_ rfl
  simp only [func1Def]
  unfold func1 Returns
  have hle16 : (16 : UInt32) ≤ g0 := UInt32.le_iff_toNat_le.mpr (by simpa using hg16)
  have hsub16 : (g0 - 16).toNat = g0.toNat - 16 := UInt32.toNat_sub_of_le g0 16 hle16
  have h0 : (0 : UInt32).toNat = 0 := rfl
  have h12 : (12 : UInt32).toNat = 12 := rfl
  have hnt12 : ¬ ((g0 - 16).toNat + 12 + 4 > st.mem.pages * 65536) := by rw [hsub16]; omega
  have hnt0 : ¬ (p0.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte,
    hg, h0, h12, hnt12, hnt0, Mem.write32_pages, Mem.read32_write32_same]
  refine ⟨_, rfl, ?_, rfl⟩
  simp only [UInt32.add_zero]

/-- `func0` — the `load32` helper (`read_unaligned`): returns the `u32` at `p0`,
roundtripping through scratch slots at `global0 - 8` and `global0 - 4`. -/
theorem func0_load (env : HostEnv Unit) (st : Store Unit) (p0 p1 g0 : UInt32)
    (hg   : st.globals.globals[0]? = some (.i32 g0))
    (hg16 : 16 ≤ g0.toNat)
    (hgB  : g0.toNat ≤ st.mem.pages * 65536)
    (hp0  : p0.toNat + 4 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 0 st [.i32 p1, .i32 p0]
      (fun st' rs => rs = [.i32 (st.mem.read32 p0)]
        ∧ st'.mem = (st.mem.write32 (g0 - 16 + 8) (st.mem.read32 p0)).write32
            (g0 - 16 + 12) (st.mem.read32 p0)
        ∧ st'.globals = st.globals) := by
  refine TerminatesWith.of_returns_wp (f := func0Def) (rs := [.i32 (st.mem.read32 p0)]) rfl rfl ?_ rfl
  simp only [func0Def]
  unfold func0 Returns
  have hle16 : (16 : UInt32) ≤ g0 := UInt32.le_iff_toNat_le.mpr (by simpa using hg16)
  have hsub16 : (g0 - 16).toNat = g0.toNat - 16 := UInt32.toNat_sub_of_le g0 16 hle16
  have h0 : (0 : UInt32).toNat = 0 := rfl
  have h8 : (8 : UInt32).toNat = 8 := rfl
  have h12 : (12 : UInt32).toNat = 12 := rfl
  have hnt0 : ¬ (p0.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
  have hnt8 : ¬ ((g0 - 16).toNat + 8 + 4 > st.mem.pages * 65536) := by rw [hsub16]; omega
  have hnt12 : ¬ ((g0 - 16).toNat + 12 + 4 > st.mem.pages * 65536) := by rw [hsub16]; omega
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte,
    hg, h0, h8, h12, hnt0, hnt8, hnt12, Mem.write32_pages, Mem.read32_write32_same,
    UInt32.add_zero]
  exact ⟨_, rfl, rfl, rfl⟩

/-- No UInt32 wraparound: `(a + b).toNat = a.toNat + b.toNat` when the sum fits. -/
theorem toNat_add_of_lt (a b : UInt32) (h : a.toNat + b.toNat < 4294967296) :
    (a + b).toNat = a.toNat + b.toNat := by
  simp only [UInt32.toNat_add]; omega

/-- **`encode` is correct.** Writes the length prefix (`store32`, via `func1`)
then the payload (`memory.copy`), returning `4 + src_len`. -/
theorem encode_correct (env : HostEnv Unit) (st : Store Unit) (src_ptr src_len dst_ptr : UInt32)
    (hg   : st.globals.globals[0]? = some (.i32 1048576))
    (hpg  : st.mem.pages ≤ 65536)
    (hdB  : dst_ptr.toNat + 4 + src_len.toNat ≤ st.mem.pages * 65536)
    (hsB  : src_ptr.toNat + src_len.toNat ≤ st.mem.pages * 65536)
    (hd   : 1048576 ≤ dst_ptr.toNat)
    (hs   : 1048576 ≤ src_ptr.toNat)
    (hdisj : src_ptr.toNat + src_len.toNat ≤ dst_ptr.toNat
             ∨ dst_ptr.toNat + 4 + src_len.toNat ≤ src_ptr.toNat) :
    TerminatesWith env «module» 3 st [.i32 dst_ptr, .i32 src_len, .i32 src_ptr]
      (fun st' rs => rs = [.i32 (4 + src_len)]
        ∧ st'.mem.read32 dst_ptr = src_len
        ∧ (∀ k : UInt32, k.toNat < src_len.toNat →
            st'.mem.read8 (dst_ptr + 4 + k) = st.mem.read8 (src_ptr + k))
        ∧ st'.globals = st.globals) := by
  refine TerminatesWith.of_returns_wp (f := func3Def) (rs := [.i32 (4 + src_len)]) rfl rfl ?_ rfl
  simp only [func3Def]
  unfold func3 Returns
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
  have h1m : (1048576 : UInt32).toNat = 1048576 := by decide
  refine wp_call_tw
    (func1_store env st dst_ptr src_len 1048624 1048576 hg (by decide) (by omega) (by omega)) ?_
  rintro st1 vs1 ⟨rfl, hmem1, hglob1⟩
  simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
  apply wp_block_cons
  by_cases hz : src_len = 0
  · subst hz
    simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
    refine ⟨_, rfl, ?_, ?_, hglob1⟩
    · rw [hmem1]; exact Mem.read32_write32_same _ _ _
    · intro k hk
      simp only [show (0 : UInt32).toNat = 0 from rfl] at hk
      omega
  · have hsl : src_len.toNat ≠ 0 := fun h => hz (UInt32.toNat.inj (by simpa using h))
    have hscr : (1048576 - 16 + 12 : UInt32).toNat = 1048572 := by decide
    have ha : (4 + dst_ptr).toNat = dst_ptr.toNat + 4 := by
      simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; omega
    have hp1 : st1.mem.pages = st.mem.pages := by rw [hmem1]; rfl
    have hntC : ¬ ((4 + dst_ptr).toNat + src_len.toNat > st.mem.pages * 65536
        ∨ src_ptr.toNat + src_len.toNat > st.mem.pages * 65536) := by rw [ha]; omega
    simp only [wp_simp, wp_entry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte, hz, hp1,
      hntC]
    refine ⟨_, rfl, ?_, ?_, hglob1⟩
    · rw [Mem.read32_copy_disjoint _ dst_ptr (4 + dst_ptr).toNat src_ptr.toNat src_len.toNat
            (Or.inl (le_of_eq ha.symm)), hmem1, Mem.read32_write32_same]
    · intro k hk
      have hdk : (dst_ptr + 4 + k).toNat = dst_ptr.toNat + 4 + k.toNat := by
        simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; omega
      have hsk : (src_ptr + k).toNat = src_ptr.toNat + k.toNat := by
        simp only [UInt32.toNat_add]; omega
      rw [Mem.read8_copy_inside _ (dst_ptr + 4 + k) (4 + dst_ptr).toNat src_ptr.toNat src_len.toNat
            (by rw [hdk, ha]; omega), hdk, ha,
          show dst_ptr.toNat + 4 + k.toNat - (dst_ptr.toNat + 4) = k.toNat from by omega, hmem1,
          Mem.write32_bytes_outside _ dst_ptr src_len (src_ptr.toNat + k.toNat) (by omega),
          Mem.write32_bytes_outside _ (1048576 - 16 + 12) src_len (src_ptr.toNat + k.toNat)
            (by rw [hscr]; omega),
          Mem.read8, hsk]

end Project.EncodeDecode.Spec
