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
  have hnt12 : ¬ ((g0 - 16).toNat + 12 + 4 > st.mem.pages * 65536) := by rw [hsub16]; omega
  have hnt0 : ¬ (p0.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
  simp only [wp_simp, wp_entry, wp_reduce, hg, hnt12, hnt0,
    Mem.write32_pages, Mem.read32_write32_same]
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
  have hnt0 : ¬ (p0.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
  have hnt8 : ¬ ((g0 - 16).toNat + 8 + 4 > st.mem.pages * 65536) := by rw [hsub16]; omega
  have hnt12 : ¬ ((g0 - 16).toNat + 12 + 4 > st.mem.pages * 65536) := by rw [hsub16]; omega
  simp only [wp_simp, wp_entry, wp_reduce, hg, hnt0, hnt8, hnt12,
    Mem.write32_pages, Mem.read32_write32_same, UInt32.add_zero]
  exact ⟨_, rfl, rfl, rfl⟩

/-- **`encode` is correct.** Writes the length prefix (`store32`, via `func1`)
then the payload (`memory.copy`), returning `4 + src_len`.

The `hdisj` precondition says the source and destination frames do not overlap
(`copy_nonoverlapping`'s contract); the addressability + `pages ≤ 65536` bounds
rule out `UInt32` address wraparound; global 0 is the shadow-stack pointer at
its initial value. -/
@[spec_of "rust-exported" "encode_decode::encode"]
def EncodeSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (src_ptr src_len dst_ptr : UInt32),
    st.globals.globals[0]? = some (.i32 1048576) →
    st.mem.pages ≤ 65536 →
    dst_ptr.toNat + 4 + src_len.toNat ≤ st.mem.pages * 65536 →
    src_ptr.toNat + src_len.toNat ≤ st.mem.pages * 65536 →
    1048576 ≤ dst_ptr.toNat →
    1048576 ≤ src_ptr.toNat →
    (src_ptr.toNat + src_len.toNat ≤ dst_ptr.toNat
      ∨ dst_ptr.toNat + 4 + src_len.toNat ≤ src_ptr.toNat) →
    TerminatesWith env «module» 3 st [.i32 dst_ptr, .i32 src_len, .i32 src_ptr]
      (fun st' rs => rs = [.i32 (4 + src_len)]
        ∧ st'.mem.read32 dst_ptr = src_len
        ∧ (∀ k : UInt32, k.toNat < src_len.toNat →
            st'.mem.read8 (dst_ptr + 4 + k) = st.mem.read8 (src_ptr + k))
        ∧ st'.globals = st.globals
        ∧ st'.mem.pages = st.mem.pages)

@[proves Project.EncodeDecode.Spec.EncodeSpec]
theorem encode_correct : EncodeSpec := by
  intro env st src_ptr src_len dst_ptr hg hpg hdB hsB hd hs hdisj
  refine TerminatesWith.of_returns_wp (f := func3Def) (rs := [.i32 (4 + src_len)]) rfl rfl ?_ rfl
  simp only [func3Def]
  unfold func3 Returns
  simp only [wp_simp, wp_entry, wp_reduce]
  have h1m : (1048576 : UInt32).toNat = 1048576 := by decide
  refine wp_call_tw
    (func1_store env st dst_ptr src_len 1048624 1048576 hg (by decide) (by omega) (by omega)) ?_
  rintro st1 vs1 ⟨rfl, hmem1, hglob1⟩
  simp only [wp_simp, wp_entry, wp_reduce]
  apply wp_block_cons
  by_cases hz : src_len = 0
  · subst hz
    simp only [wp_simp, wp_entry, wp_reduce]
    refine ⟨_, rfl, ?_, ?_, hglob1, ?_⟩
    · rw [hmem1]; exact Mem.read32_write32_same _ _ _
    · intro k hk; omega
    · simp only [Mem.copy_pages, Mem.write32_pages, hmem1]
  · have hsl : src_len.toNat ≠ 0 := fun h => hz (UInt32.toNat.inj (by simpa using h))
    have hscr : (1048576 - 16 + 12 : UInt32).toNat = 1048572 := by decide
    have ha : (4 + dst_ptr).toNat = dst_ptr.toNat + 4 := by
      simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; omega
    have hp1 : st1.mem.pages = st.mem.pages := by rw [hmem1]; rfl
    have hntC : ¬ ((4 + dst_ptr).toNat + src_len.toNat > st.mem.pages * 65536
        ∨ src_ptr.toNat + src_len.toNat > st.mem.pages * 65536) := by rw [ha]; omega
    simp only [wp_simp, wp_entry, wp_reduce, hz, hp1, hntC]
    refine ⟨_, rfl, ?_, ?_, hglob1, ?_⟩
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
    · rw [Mem.copy_pages]; exact hp1

/-- **`decode` is correct.** Reads the length prefix (`load32`, via `func0`),
validates the frame, and copies the payload (`memory.copy`), returning the
payload length. Error branches are dead under the frame-valid preconditions:
`h4`/`hn` say the frame's length prefix is present and consistent, `hnd` that
the destination has capacity, and the addressability bounds keep every access
in range. -/
@[spec_of "rust-exported" "encode_decode::decode"]
def DecodeSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (src_ptr src_len dst_ptr dst_cap : UInt32),
    st.globals.globals[0]? = some (.i32 1048576) →
    st.mem.pages ≤ 65536 →
    4 ≤ src_len.toNat →
    (st.mem.read32 src_ptr).toNat + 4 ≤ src_len.toNat →
    (st.mem.read32 src_ptr).toNat ≤ dst_cap.toNat →
    src_ptr.toNat + src_len.toNat ≤ st.mem.pages * 65536 →
    dst_ptr.toNat + (st.mem.read32 src_ptr).toNat ≤ st.mem.pages * 65536 →
    1048576 ≤ src_ptr.toNat →
    1048576 ≤ dst_ptr.toNat →
    TerminatesWith env «module» 2 st [.i32 dst_cap, .i32 dst_ptr, .i32 src_len, .i32 src_ptr]
      (fun st' rs => rs = [.i64 (UInt64.ofNat (st.mem.read32 src_ptr).toNat)]
        ∧ (∀ k : UInt32, k.toNat < (st.mem.read32 src_ptr).toNat →
            st'.mem.read8 (dst_ptr + k) = st.mem.read8 (src_ptr + 4 + k))
        ∧ st'.globals = st.globals
        ∧ st'.mem.pages = st.mem.pages)

@[proves Project.EncodeDecode.Spec.DecodeSpec]
theorem decode_correct : DecodeSpec := by
  intro env st src_ptr src_len dst_ptr dst_cap hg hpg h4 hn hnd hsB hdB hs hd
  refine TerminatesWith.of_returns_wp (f := func2Def)
    (rs := [.i64 (UInt64.ofNat (st.mem.read32 src_ptr).toNat)]) rfl rfl ?_ rfl
  simp only [func2Def]
  unfold func2 Returns
  have hsub : (1048576 : UInt32) - 16 = 1048560 := by decide
  simp only [wp_simp, wp_entry, wp_reduce, hg, hsub]
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  have hle4 : (4 : UInt32) ≤ src_len := UInt32.le_iff_toNat_le.mpr (by simpa using h4)
  have hlt4 : ¬ (src_len < 4) := by
    simp only [UInt32.lt_iff_toNat_lt, show (4 : UInt32).toNat = 4 from rfl]; omega
  have hand0 : (1 : UInt32) &&& 0 = 0 := by decide
  have h60 : (1048560 : UInt32).toNat = 1048560 := by decide
  obtain ⟨hlen, heq⟩ := List.getElem?_eq_some_iff.mp hg
  simp only [wp_simp, wp_entry, wp_reduce, hlt4, hand0]
  refine wp_call_tw (func0_load env _ src_ptr 1048608 1048560 ?_ ?_ ?_ ?_) ?_
  · show (st.globals.globals.set 0 (.i32 1048560))[0]? = some (.i32 1048560)
    simp only [List.getElem?_set_self hlen]
  · decide
  · show (1048560 : UInt32).toNat ≤ st.mem.pages * 65536
    rw [h60]; omega
  · show src_ptr.toNat + 4 ≤ st.mem.pages * 65536
    omega
  rintro st2 vs2 ⟨rfl, hmem2, hglob2⟩
  have hsub4 : (src_len - 4).toNat = src_len.toNat - 4 := UInt32.toNat_sub_of_le src_len 4 hle4
  have hgt1 : ¬ (src_len - 4 < st.mem.read32 src_ptr) := by
    simp only [UInt32.lt_iff_toNat_lt, hsub4]; omega
  have hgt2 : ¬ (dst_cap < st.mem.read32 src_ptr) := by
    simp only [UInt32.lt_iff_toNat_lt]; omega
  simp only [wp_simp, wp_entry, wp_reduce, hgt1, hgt2, hand0]
  apply wp_block_cons
  have hp2 : st2.mem.pages = st.mem.pages := by rw [hmem2]; rfl
  have hgf : (st.globals.globals.set 0 (Value.i32 1048560)).set 0 (Value.i32 1048576)
      = st.globals.globals := by rw [List.set_set, ← heq]; exact List.set_getElem_self hlen
  have hg2 : st2.globals.globals[0]? = some (.i32 1048560) := by
    rw [hglob2]; simp only [List.getElem?_set_self hlen]
  have hnt64 : ¬ (1048576 > st2.mem.pages * 65536) := by rw [hp2]; omega
  by_cases hz : st.mem.read32 src_ptr = 0
  · simp only [wp_simp, wp_entry, wp_reduce, hz, hg2, hglob2, hgf,
      Mem.write64_pages, hnt64, Mem.read64_write64_same, List.getElem?_set_self hlen]
    refine ⟨_, rfl, fun k hk => (Nat.not_lt_zero _ hk).elim, rfl, ?_⟩
    rw [Mem.write64_pages]; exact hp2
  · have hn0 : (st.mem.read32 src_ptr).toNat ≠ 0 := fun h => hz (UInt32.toNat.inj (by simpa using h))
    have ha4 : (4 + src_ptr).toNat = src_ptr.toNat + 4 := by
      simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; omega
    have hntC : ¬ (dst_ptr.toNat + (st.mem.read32 src_ptr).toNat > st2.mem.pages * 65536
        ∨ (4 + src_ptr).toNat + (st.mem.read32 src_ptr).toNat > st2.mem.pages * 65536) := by
      rw [hp2, ha4]; omega
    simp only [wp_simp, wp_entry, wp_reduce, hz, hg2, hglob2, hgf,
      Mem.copy_pages, Mem.write64_pages, hnt64, hntC, Mem.read64_write64_same,
      List.getElem?_set_self hlen]
    refine ⟨_, rfl, ?_, rfl, ?_⟩
    rotate_left
    · rw [Mem.write64_pages, Mem.copy_pages]; exact hp2
    intro k hk
    have hdk : (dst_ptr + k).toNat = dst_ptr.toNat + k.toNat := by
      simp only [UInt32.toNat_add]; omega
    have hsk : (src_ptr + 4 + k).toNat = src_ptr.toNat + 4 + k.toNat := by
      simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; omega
    have hframe : ∀ j : Nat, 1048560 ≤ j → st2.mem.bytes j = st.mem.bytes j := fun j hj => by
      rw [hmem2, Mem.write32_bytes_outside _ _ _ _ (by simp only [wp_reduce]; omega),
        Mem.write32_bytes_outside _ _ _ _ (by simp only [wp_reduce]; omega)]
    rw [Mem.read8_write64_disjoint _ (dst_ptr + k) 1048568 _ (by rw [hdk]; simp only [wp_reduce]; omega),
      Mem.read8_copy_inside _ (dst_ptr + k) dst_ptr.toNat (4 + src_ptr).toNat
        (st.mem.read32 src_ptr).toNat (by rw [hdk]; omega),
      hdk, ha4,
      show src_ptr.toNat + 4 + (dst_ptr.toNat + k.toNat - dst_ptr.toNat) = src_ptr.toNat + 4 + k.toNat
        from by omega,
      hframe _ (by omega), Mem.read8, hsk]

end Project.EncodeDecode.Spec
