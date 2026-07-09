import CodeLib.Entry
import CodeLib.Wp
import CodeLib.UInt32
import CodeLib.RustStd.Frame
import CodeLib.RustStd.Mem
import Interpreter.Wasm.Wp.Call

/-!
# `CodeLib.Codec.Frame` — a reusable, module-parametric frame codec

The length-prefixed frame codec (`encode` writes `[len_le32][payload]`, `decode`
reads it back) proved **once**, keyed on the function body rather than a fixed
module. Any wasm module that links the codec — the `encode_decode` crate itself,
or any *client* crate that calls it — reuses these theorems by discharging the
shape hypotheses with `rfl` and crossing its `call` with them. The internal
`encode → store32` / `decode → load32` calls are themselves crossed with the leaf
`store32Terminates` / `load32Terminates`, so the whole codec is compositional.

This is the memory-program analogue of the `RustStd/U64` value-op corpus: a
client proof over the codec is a couple of `wp_call_tw`s, not a fresh memory
proof.
-/

namespace Wasm.Codec

set_option maxRecDepth 1048576
set_option linter.unusedSimpArgs false

/-- `decode`'s function body, parametric over the index `loadIdx` of the `load32`
helper it calls. `«module»`'s `decode` is `decodeBody 0`; a client module that
links the codec gets `decodeBody k` for whatever index its linker assigns — the
only cross-module difference. Keying the reusable theorem on this lets any such
module reuse `decodeTerminates`. -/
def decodeBody (loadIdx : Nat) : List Instruction :=
  [.globalGet 0, .const (16 : UInt32), .sub, .localSet 4, .localGet 4, .globalSet 0,
   .block 0 0 [
     .block 0 0 [
       .block 0 0 [
         .block 0 0 [
           .block 0 0 [
             .block 0 0 [
               .localGet 1, .const (4 : UInt32), .ltU, .const (1 : UInt32), .and, .br_if 0,
               .localGet 0, .const (1048608 : UInt32), .call loadIdx, .localSet 5,
               .localGet 5, .localGet 1, .const (4 : UInt32), .sub, .gtU, .const (1 : UInt32),
               .and, .br_if 2, .br 1],
             .localGet 4, .constI64 (18446744073709551615 : UInt64), .store64 (8 : UInt32), .br 4],
           .localGet 5, .localGet 3, .gtU, .const (1 : UInt32), .and, .br_if 2, .br 1],
         .localGet 4, .constI64 (18446744073709551614 : UInt64), .store64 (8 : UInt32), .br 2],
       .localGet 0, .const (4 : UInt32), .add, .localSet 6,
       .block 0 0 [
         .localGet 5, .eqz, .br_if 0, .localGet 2, .localGet 6, .localGet 5, .memoryCopy],
       .localGet 4, .localGet 5, .extendUI32, .store64 (8 : UInt32), .br 1],
     .localGet 4, .constI64 (18446744073709551613 : UInt64), .store64 (8 : UInt32)],
   .localGet 4, .load64 (8 : UInt32), .localSet 7, .localGet 4, .const (16 : UInt32), .add,
   .globalSet 0, .localGet 7, .ret]

/-- The `store32` / `load32` leaf helper bodies (no internal calls, identical in
every module). -/
def store32Body : List Instruction :=
  [.globalGet 0, .const (16 : UInt32), .sub, .localSet 3, .localGet 3, .localGet 1,
   .store32 (12 : UInt32), .localGet 0, .localGet 3, .load32 (12 : UInt32),
   .store32 (0 : UInt32), .ret]

def load32Body : List Instruction :=
  [.globalGet 0, .const (16 : UInt32), .sub, .localSet 2, .localGet 2, .localGet 0,
   .load32 (0 : UInt32), .store32 (8 : UInt32), .localGet 2, .localGet 2,
   .load32 (8 : UInt32), .store32 (12 : UInt32), .localGet 2, .load32 (12 : UInt32), .ret]

/-- `encode`'s body, parametric over the `store32` helper index `storeIdx`. -/
def encodeBody (storeIdx : Nat) : List Instruction :=
  [.localGet 2, .localGet 1, .const (1048624 : UInt32), .call storeIdx,
   .localGet 2, .const (4 : UInt32), .add, .localSet 3,
   .block 0 0 [
     .localGet 1, .eqz, .br_if 0, .localGet 3, .localGet 0, .localGet 1, .memoryCopy],
   .localGet 1, .const (4 : UInt32), .add, .ret]

/-- Reusable, **module-parametric** `store32` helper: any module function whose
body/params/locals are the `write_unaligned` outline stores `p1` at `p0` (through
a scratch slot at `global0 - 4`) and terminates. Keyed on the body like the
`Array` corpus' `isEmptyBodyTerminates`, so a *client* module that calls this
helper reuses it via `wp_call_tw` instead of re-proving it. -/
theorem store32Terminates {env : HostEnv Unit} {m : Module} {id : Nat} {f : Function}
    (st : Store Unit) (p0 p1 p2 g0 : UInt32)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hp : f.params = [.i32, .i32, .i32])
    (hl : f.locals = [.i32])
    (hb : f.body = store32Body)
    (hr : f.results = [])
    (hg   : st.globals.globals[0]? = some (.i32 g0))
    (hg16 : 16 ≤ g0.toNat)
    (hgB  : g0.toNat ≤ st.mem.pages * 65536)
    (hp0  : p0.toNat + 4 ≤ st.mem.pages * 65536)
    (hImp : m.imports[id]? = none := by rfl) :
    TerminatesWith env m id st [.i32 p2, .i32 p1, .i32 p0]
      (fun st' rs => rs = []
        ∧ st'.mem = (st.mem.write32 (g0 - 16 + 12) p1).write32 p0 p1
        ∧ st'.globals = st.globals) := by
  have hnp : f.numParams = 3 := by simp only [Function.numParams, hp]; rfl
  refine (TerminatesWith.of_returns_wp (rs := []) (P := fun st' =>
      st'.mem = (st.mem.write32 (g0 - 16 + 12) p1).write32 p0 p1 ∧ st'.globals = st.globals)
      hf (by simp [hr]) ?_ hImp).mono ?_
  · rw [hb]
    have hle16 : (16 : UInt32) ≤ g0 := UInt32.le_iff_toNat_le.mpr (by simpa using hg16)
    have hsub16 : (g0 - 16).toNat = g0.toNat - 16 := UInt32.toNat_sub_of_le g0 16 hle16
    have hnt12 : ¬ ((g0 - 16).toNat + 12 + 4 > st.mem.pages * 65536) := by rw [hsub16]; omega
    have hnt0 : ¬ (p0.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
    simp only [store32Body, Returns, wp_simp, wp_entry, wp_reduce, hp, hl, hg, hnt12, hnt0,
      Mem.write32_pages, Mem.read32_write32_same]
    refine ⟨_, rfl, ?_, rfl⟩
    simp only [UInt32.add_zero]
  · intro st' vs h
    refine ⟨?_, h.2⟩
    rw [h.1, hnp]; rfl

/-- Reusable, **module-parametric** `load32` helper: any module function whose
body is the `read_unaligned` outline returns the `u32` at `p0`. The callee twin
of `store32Terminates`, reused across a client `call`. -/
theorem load32Terminates {env : HostEnv Unit} {m : Module} {id : Nat} {f : Function}
    (st : Store Unit) (p0 p1 g0 : UInt32)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hp : f.params = [.i32, .i32])
    (hl : f.locals = [.i32])
    (hb : f.body = load32Body)
    (hr : f.results = [.i32])
    (hg   : st.globals.globals[0]? = some (.i32 g0))
    (hg16 : 16 ≤ g0.toNat)
    (hgB  : g0.toNat ≤ st.mem.pages * 65536)
    (hp0  : p0.toNat + 4 ≤ st.mem.pages * 65536)
    (hImp : m.imports[id]? = none := by rfl) :
    TerminatesWith env m id st [.i32 p1, .i32 p0]
      (fun st' rs => rs = [.i32 (st.mem.read32 p0)]
        ∧ st'.mem = (st.mem.write32 (g0 - 16 + 8) (st.mem.read32 p0)).write32
            (g0 - 16 + 12) (st.mem.read32 p0)
        ∧ st'.globals = st.globals) := by
  have hnp : f.numParams = 2 := by simp only [Function.numParams, hp]; rfl
  refine (TerminatesWith.of_returns_wp (rs := [.i32 (st.mem.read32 p0)]) (P := fun st' =>
      st'.mem = (st.mem.write32 (g0 - 16 + 8) (st.mem.read32 p0)).write32
        (g0 - 16 + 12) (st.mem.read32 p0) ∧ st'.globals = st.globals)
      hf (by simp [hr]) ?_ hImp).mono ?_
  · rw [hb]
    have hle16 : (16 : UInt32) ≤ g0 := UInt32.le_iff_toNat_le.mpr (by simpa using hg16)
    have hsub16 : (g0 - 16).toNat = g0.toNat - 16 := UInt32.toNat_sub_of_le g0 16 hle16
    have hnt0 : ¬ (p0.toNat + 0 + 4 > st.mem.pages * 65536) := by omega
    have hnt8 : ¬ ((g0 - 16).toNat + 8 + 4 > st.mem.pages * 65536) := by rw [hsub16]; omega
    have hnt12 : ¬ ((g0 - 16).toNat + 12 + 4 > st.mem.pages * 65536) := by rw [hsub16]; omega
    simp only [load32Body, Returns, wp_simp, wp_entry, wp_reduce, hp, hl, hg, hnt0, hnt8, hnt12,
      Mem.write32_pages, Mem.read32_write32_same, UInt32.add_zero]
    exact ⟨_, rfl, rfl, rfl⟩
  · intro st' vs h
    refine ⟨?_, h.2⟩
    rw [h.1, hnp]; rfl

/-- **Module-parametric `decode`.** Any module whose function `id` is
`decodeBody loadIdx` (calling a `load32` helper at `loadIdx` whose body is
`load32Body`) decodes a frame correctly, reusing `load32Terminates` across the
internal `call`. A *client* module that links the codec reuses THIS across its
own `call` to `decode`. -/
theorem decodeTerminates {env : HostEnv Unit} {m : Module} {id loadIdx : Nat}
    {f floadf : Function} (st : Store Unit) (src_ptr src_len dst_ptr dst_cap : UInt32)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hp : f.params = [.i32, .i32, .i32, .i32])
    (hl : f.locals = [.i32, .i32, .i32, .i64])
    (hb : f.body = decodeBody loadIdx)
    (hr : f.results = [.i64])
    (hfl : m.funcs[loadIdx - m.imports.length]? = some floadf)
    (hpl : floadf.params = [.i32, .i32])
    (hll : floadf.locals = [.i32])
    (hbl : floadf.body = load32Body)
    (hrl : floadf.results = [.i32])
    (hImpl : m.imports[loadIdx]? = none)
    (hg   : st.globals.globals[0]? = some (.i32 1048576))
    (hpg  : st.mem.pages ≤ 65536)
    (h4   : 4 ≤ src_len.toNat)
    (hn   : (st.mem.read32 src_ptr).toNat + 4 ≤ src_len.toNat)
    (hnd  : (st.mem.read32 src_ptr).toNat ≤ dst_cap.toNat)
    (hsB  : src_ptr.toNat + src_len.toNat ≤ st.mem.pages * 65536)
    (hdB  : dst_ptr.toNat + (st.mem.read32 src_ptr).toNat ≤ st.mem.pages * 65536)
    (hs   : 1048576 ≤ src_ptr.toNat)
    (hd   : 1048576 ≤ dst_ptr.toNat)
    (hImp : m.imports[id]? = none := by rfl) :
    TerminatesWith env m id st [.i32 dst_cap, .i32 dst_ptr, .i32 src_len, .i32 src_ptr]
      (fun st' rs => rs = [.i64 (UInt64.ofNat (st.mem.read32 src_ptr).toNat)]
        ∧ (∀ k : UInt32, k.toNat < (st.mem.read32 src_ptr).toNat →
            st'.mem.read8 (dst_ptr + k) = st.mem.read8 (src_ptr + 4 + k))
        ∧ st'.globals = st.globals
        ∧ st'.mem.pages = st.mem.pages) := by
  have hnp : f.numParams = 4 := by simp only [Function.numParams, hp]; rfl
  refine (TerminatesWith.of_returns_wp (rs := [.i64 (UInt64.ofNat (st.mem.read32 src_ptr).toNat)])
      (P := fun st' => (∀ k : UInt32, k.toNat < (st.mem.read32 src_ptr).toNat →
            st'.mem.read8 (dst_ptr + k) = st.mem.read8 (src_ptr + 4 + k))
          ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages)
      hf (by simp [hr]) ?_ hImp).mono ?_
  · rw [hb]
    have hsub : (1048576 : UInt32) - 16 = 1048560 := by decide
    simp only [decodeBody, Returns, wp_simp, wp_entry, wp_reduce, hp, hl, hg, hsub]
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
    refine wp_call_tw (load32Terminates _ src_ptr 1048608 1048560
      hfl hpl hll hbl hrl ?_ ?_ ?_ ?_ hImpl) ?_
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
    · have hn0 : (st.mem.read32 src_ptr).toNat ≠ 0 :=
        fun h => hz (UInt32.toNat.inj (by simpa using h))
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
      rw [Mem.read8_write64_disjoint _ (dst_ptr + k) 1048568 _
          (by rw [hdk]; simp only [wp_reduce]; omega),
        Mem.read8_copy_inside _ (dst_ptr + k) dst_ptr.toNat (4 + src_ptr).toNat
          (st.mem.read32 src_ptr).toNat (by rw [hdk]; omega),
        hdk, ha4,
        show src_ptr.toNat + 4 + (dst_ptr.toNat + k.toNat - dst_ptr.toNat) = src_ptr.toNat + 4 + k.toNat
          from by omega,
        hframe _ (by omega), Mem.read8, hsk]
  · intro st' vs h
    refine ⟨?_, h.2⟩
    rw [h.1, hnp]; rfl

/-- **Module-parametric `encode`.** Any module whose function `id` is
`encodeBody storeIdx` (calling a `store32` helper at `storeIdx`) frames a payload
correctly, reusing `store32Terminates` across the internal `call`. -/
theorem encodeTerminates {env : HostEnv Unit} {m : Module} {id storeIdx : Nat}
    {f fstoref : Function} (st : Store Unit) (src_ptr src_len dst_ptr : UInt32)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hp : f.params = [.i32, .i32, .i32])
    (hl : f.locals = [.i32])
    (hb : f.body = encodeBody storeIdx)
    (hr : f.results = [.i32])
    (hfs : m.funcs[storeIdx - m.imports.length]? = some fstoref)
    (hps : fstoref.params = [.i32, .i32, .i32])
    (hls : fstoref.locals = [.i32])
    (hbs : fstoref.body = store32Body)
    (hrs : fstoref.results = [])
    (hImps : m.imports[storeIdx]? = none)
    (hg   : st.globals.globals[0]? = some (.i32 1048576))
    (hpg  : st.mem.pages ≤ 65536)
    (hdB  : dst_ptr.toNat + 4 + src_len.toNat ≤ st.mem.pages * 65536)
    (hsB  : src_ptr.toNat + src_len.toNat ≤ st.mem.pages * 65536)
    (hd   : 1048576 ≤ dst_ptr.toNat)
    (hs   : 1048576 ≤ src_ptr.toNat)
    (hdisj : src_ptr.toNat + src_len.toNat ≤ dst_ptr.toNat
      ∨ dst_ptr.toNat + 4 + src_len.toNat ≤ src_ptr.toNat)
    (hImp : m.imports[id]? = none := by rfl) :
    TerminatesWith env m id st [.i32 dst_ptr, .i32 src_len, .i32 src_ptr]
      (fun st' rs => rs = [.i32 (4 + src_len)]
        ∧ st'.mem.read32 dst_ptr = src_len
        ∧ (∀ k : UInt32, k.toNat < src_len.toNat →
            st'.mem.read8 (dst_ptr + 4 + k) = st.mem.read8 (src_ptr + k))
        ∧ st'.globals = st.globals
        ∧ st'.mem.pages = st.mem.pages) := by
  have hnp : f.numParams = 3 := by simp only [Function.numParams, hp]; rfl
  refine (TerminatesWith.of_returns_wp (rs := [.i32 (4 + src_len)])
      (P := fun st' => st'.mem.read32 dst_ptr = src_len
          ∧ (∀ k : UInt32, k.toNat < src_len.toNat →
              st'.mem.read8 (dst_ptr + 4 + k) = st.mem.read8 (src_ptr + k))
          ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages)
      hf (by simp [hr]) ?_ hImp).mono ?_
  · rw [hb]
    simp only [encodeBody, Returns, wp_simp, wp_entry, wp_reduce, hp, hl]
    have h1m : (1048576 : UInt32).toNat = 1048576 := by decide
    refine wp_call_tw
      (store32Terminates _ dst_ptr src_len 1048624 1048576 hfs hps hls hbs hrs hg
        (by decide) (by omega) (by omega) hImps) ?_
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
        rw [Mem.read8_copy_inside _ (dst_ptr + 4 + k) (4 + dst_ptr).toNat src_ptr.toNat
              src_len.toNat (by rw [hdk, ha]; omega), hdk, ha,
            show dst_ptr.toNat + 4 + k.toNat - (dst_ptr.toNat + 4) = k.toNat from by omega, hmem1,
            Mem.write32_bytes_outside _ dst_ptr src_len (src_ptr.toNat + k.toNat) (by omega),
            Mem.write32_bytes_outside _ (1048576 - 16 + 12) src_len (src_ptr.toNat + k.toNat)
              (by rw [hscr]; omega),
            Mem.read8, hsk]
      · rw [Mem.copy_pages]; exact hp1
  · intro st' vs h
    refine ⟨?_, h.2⟩
    rw [h.1, hnp]; rfl

end Wasm.Codec
