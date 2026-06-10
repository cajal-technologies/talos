import Project.RustOption.Program

/-!
# Specifications for the `rust_option` crate

Each exported function is given a `TerminatesWith` spec at the raw
`UInt64` level (i.e. in terms of the C-ABI sentinel encoding). The
shared helpers — most importantly `sentinel` and the `encode` lifting —
live in `CodeLib.RustStd.Option` so downstream corpora using the same
convention can reuse them.

The crate is compiled at `opt-level=0`, so every export is a thin
wrapper around an inner function, and every function routes its
arguments through a shadow-stack frame in linear memory (`global 0` is
the shadow-stack pointer). Because the bodies genuinely load and store
linear memory, the specs are pinned to the module's canonical
instantiation `initial = «module».initialStore` (16 pages, stack
pointer `1048576`); under an adversarial store the frames would be out
of bounds and the bodies would trap.

The proof is compositional: each internal function gets a
`TerminatesWith` lemma at an arbitrary store satisfying the shadow-stack
frame invariant (pages = 16, `global 0 = g`, `g` in range), and calls
are threaded through `Wasm.wp_call_at`.
-/

namespace Project.RustOption.Spec

open Wasm
open Wasm.RustStd.Option (sentinel encode)

set_option maxRecDepth 1048576

/-! ## Memory framing lemmas

64-bit analogues of the 32-bit read-after-write algebra: a `read64`
sees the value of a same-address `write64`, and is unchanged by writes
to disjoint footprints. Generic facts about the function-model `Mem`;
they belong eventually in the interpreter. -/

/-- A byte outside the 8-byte footprint of a `write64` is unchanged. -/
theorem write64_bytes_of_disjoint (m : Mem) (a : UInt32) (v : UInt64) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 8 ≤ i) :
    (m.write64 a v).bytes i = m.bytes i := by
  simp only [Mem.write64]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  have h4 : i ≠ a.toNat + 4 := by omega
  have h5 : i ≠ a.toNat + 5 := by omega
  have h6 : i ≠ a.toNat + 6 := by omega
  have h7 : i ≠ a.toNat + 7 := by omega
  simp [h0, h1, h2, h3, h4, h5, h6, h7]

/-- A 64-bit read sees the value of a same-address 64-bit write. -/
theorem read64_write64_same (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).read64 a = v := by
  simp only [Mem.read64, Mem.write64]
  have e1 : a.toNat + 1 ≠ a.toNat := by omega
  have e2 : a.toNat + 2 ≠ a.toNat := by omega
  have e3 : a.toNat + 3 ≠ a.toNat := by omega
  have e4 : a.toNat + 4 ≠ a.toNat := by omega
  have e5 : a.toNat + 5 ≠ a.toNat := by omega
  have e6 : a.toNat + 6 ≠ a.toNat := by omega
  have e7 : a.toNat + 7 ≠ a.toNat := by omega
  have e21 : a.toNat + 2 ≠ a.toNat + 1 := by omega
  have e31 : a.toNat + 3 ≠ a.toNat + 1 := by omega
  have e41 : a.toNat + 4 ≠ a.toNat + 1 := by omega
  have e51 : a.toNat + 5 ≠ a.toNat + 1 := by omega
  have e61 : a.toNat + 6 ≠ a.toNat + 1 := by omega
  have e71 : a.toNat + 7 ≠ a.toNat + 1 := by omega
  have e32 : a.toNat + 3 ≠ a.toNat + 2 := by omega
  have e42 : a.toNat + 4 ≠ a.toNat + 2 := by omega
  have e52 : a.toNat + 5 ≠ a.toNat + 2 := by omega
  have e62 : a.toNat + 6 ≠ a.toNat + 2 := by omega
  have e72 : a.toNat + 7 ≠ a.toNat + 2 := by omega
  have e43 : a.toNat + 4 ≠ a.toNat + 3 := by omega
  have e53 : a.toNat + 5 ≠ a.toNat + 3 := by omega
  have e63 : a.toNat + 6 ≠ a.toNat + 3 := by omega
  have e73 : a.toNat + 7 ≠ a.toNat + 3 := by omega
  have e54 : a.toNat + 5 ≠ a.toNat + 4 := by omega
  have e64 : a.toNat + 6 ≠ a.toNat + 4 := by omega
  have e74 : a.toNat + 7 ≠ a.toNat + 4 := by omega
  have e65 : a.toNat + 6 ≠ a.toNat + 5 := by omega
  have e75 : a.toNat + 7 ≠ a.toNat + 5 := by omega
  have e76 : a.toNat + 7 ≠ a.toNat + 6 := by omega
  simp only [e1, e2, e3, e4, e5, e6, e7, e21, e31, e41, e51, e61, e71,
    e32, e42, e52, e62, e72, e43, e53, e63, e73, e54, e64, e74, e65, e75, e76,
    if_true, if_false]
  bv_decide

/-- A 64-bit read is unaffected by a 64-bit write to a disjoint 8-byte
range. -/
theorem read64_write64_disjoint (m : Mem) (a b : UInt32) (v : UInt64)
    (h : b.toNat + 8 ≤ a.toNat ∨ a.toNat + 8 ≤ b.toNat) :
    (m.write64 a v).read64 b = m.read64 b := by
  simp only [Mem.read64]
  rw [write64_bytes_of_disjoint m a v b.toNat (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 3) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 4) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 5) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 6) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 7) (by omega)]

/-- A byte outside the 4-byte footprint of a `write32` is unchanged. -/
theorem write32_bytes_of_disjoint (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

/-- A 64-bit read is unaffected by a 32-bit write to a disjoint 4-byte
range. -/
theorem read64_write32_disjoint (m : Mem) (a b : UInt32) (v : UInt32)
    (h : b.toNat + 8 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read64 b = m.read64 b := by
  simp only [Mem.read64]
  rw [write32_bytes_of_disjoint m a v b.toNat (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 4) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 5) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 6) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 7) (by omega)]

/-- A 64-bit read depends only on its eight bytes: if two memories agree
on `[a, a+8)` they agree on `read64 a`. -/
theorem read64_eq_of_bytes_range (m m' : Mem) (a : UInt32)
    (h : ∀ i, a.toNat ≤ i → i < a.toNat + 8 → m'.bytes i = m.bytes i) :
    m'.read64 a = m.read64 a := by
  simp only [Mem.read64]
  rw [h a.toNat (by omega) (by omega),
      h (a.toNat + 1) (by omega) (by omega),
      h (a.toNat + 2) (by omega) (by omega),
      h (a.toNat + 3) (by omega) (by omega),
      h (a.toNat + 4) (by omega) (by omega),
      h (a.toNat + 5) (by omega) (by omega),
      h (a.toNat + 6) (by omega) (by omega),
      h (a.toNat + 7) (by omega) (by omega)]

@[simp] theorem write64_pages (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).pages = m.pages := rfl

@[simp] theorem write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

/-- Masking a 0/1-valued i32 with `1` is the identity. The codegen emits
this mask after every boolean-producing comparison. -/
theorem one_and_ite (c : Prop) [Decidable c] :
    (1 &&& if c then (1 : UInt32) else 0) = if c then 1 else 0 := by
  split <;> decide

/-! ## The shadow-stack frame invariant -/

/-- The state every internal function sees on entry and re-establishes
on exit: the canonical 16-page memory and the shadow-stack pointer `g`
in `global 0`. -/
def Frame (g : UInt32) (st : Store Unit) : Prop :=
  st.mem.pages = 16 ∧ st.globals.globals[0]? = some (.i32 g)

theorem Frame.pages {g : UInt32} {st : Store Unit} (h : Frame g st) :
    st.mem.pages = 16 := h.1

theorem Frame.global0 {g : UInt32} {st : Store Unit} (h : Frame g st) :
    st.globals.globals[0]? = some (.i32 g) := h.2

/-- Step a `call` against a `TerminatesWith` of the callee at the
*current* store — `Wasm.wp_call_at` with the success-run hypothesis
packaged as the fuel-free predicate. -/
private theorem wp_call_of_terminates {α : Type} {env : HostEnv α} {m : Module}
    {id : Nat} {Q : Assertion α} {rest : Program} {st : Store α} {s : Locals}
    {P : Store α → List Value → Prop}
    (h : TerminatesWith env m id st s.values P)
    (hPost : ∀ st' vs, P st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env :=
  Wasm.wp_call_at h hPost

/-! ## Per-function lemmas: leaves -/

/-- `func1` is `Option::unwrap_or` at the (tag, payload) pair level:
returns `p` when the tag's low bit is set, else the default `s`. -/
theorem func1_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32) (t p s : UInt64)
    (hfr : Frame g st0)
    (hlo : 32 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 1 st0 [.i64 s, .i64 p, .i64 t]
      (fun st' vs => Frame g st' ∧
        vs = [.i64 (if 1 &&& t.toUInt32 = 0 then s else p)]) := by
  obtain ⟨hpg, hg⟩ := hfr
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i64, .i64], [.i32], func1, [.i64]⟩) rfl
  unfold func1
  wp_run
  simp [hg, hpg]
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simpa using hlo)]
    rfl
  refine ⟨by omega, by omega, by omega, ?_⟩
  have h8 : (g - 32 + 8).toNat = g.toNat - 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h16 : (g - 32 + 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h24 : (g - 32 + 24).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  have hrd0 : (((st0.mem.write64 (g - 32) t).write64 (g - 32 + 8) p).write64 (g - 32 + 24)
      s).read64 (g - 32) = t := by
    rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  have hrd8 : (((st0.mem.write64 (g - 32) t).write64 (g - 32 + 8) p).write64 (g - 32 + 24)
      s).read64 (g - 32 + 8) = p := by
    rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  have hwrap : UInt32.ofNat (t.toNat % 4294967296) = t.toUInt32 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide)), UInt64.toNat_toUInt32]
  simp [hpg, hrd0, hrd8, hwrap]
  refine ⟨by omega, ?_⟩
  by_cases hc : 1 &&& t.toUInt32 = 0
  · simp [hc, hpg, Frame, hg, read64_write64_same]
    omega
  · simp [hc, hpg, Frame, hg, read64_write64_same]
    omega

/-- `func3` packs the sentinel-encoded `v` into a (tag, payload) pair at
`ptr`: tag 0 for `None` (payload junk), tag 1 with payload `v` for
`Some`. Bytes outside its scratch `[g-16, g)` and the pair
`[ptr, ptr+16)` are untouched. -/
theorem func3_spec (env : HostEnv Unit) (st0 : Store Unit) (g ptr : UInt32) (v : UInt64)
    (hfr : Frame g st0)
    (hlo : 16 ≤ g.toNat) (hhi : g.toNat ≤ 1048576)
    (hptr : ptr.toNat + 16 ≤ 1048576) :
    TerminatesWith env «module» 3 st0 [.i64 v, .i32 ptr]
      (fun st' vs => Frame g st' ∧ vs = [] ∧
        st'.mem.read64 ptr = (if v = sentinel then 0 else 1) ∧
        (v ≠ sentinel → st'.mem.read64 (ptr + 8) = v) ∧
        (∀ i : Nat, (i < g.toNat - 16 ∨ g.toNat ≤ i) →
          (i < ptr.toNat ∨ ptr.toNat + 16 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hpg, hg⟩ := hfr
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32, .i64], [.i32], func3, []⟩) rfl
  unfold func3
  wp_run
  simp [hg, hpg]
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simpa using hlo)]
    rfl
  have h8 : (g - 16 + 8).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hp8 : (ptr + 8).toNat = ptr.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  refine ⟨by omega, ?_⟩
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  by_cases hv : v = (9223372036854775808 : UInt64)
  · simp [hv, hpg, Frame, hg, read64_write64_same]
    refine ⟨by omega, ?_⟩
    intro i hi hip
    rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega)]
  · simp [hv, hpg, Frame, hg, read64_write64_same]
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
    · intro i hi hip
      rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega)]

/-- `func5` is the predicate `|x| > 0` on the payload stored at `ptr`:
returns `1` iff the i64 at `ptr` is strictly positive. Its only write is
4 scratch bytes at `[g-4, g)`, so reads at or above `g` are preserved. -/
theorem func5_spec (env : HostEnv Unit) (st0 : Store Unit) (g ptr : UInt32)
    (hfr : Frame g st0)
    (hlo : 16 ≤ g.toNat) (hhi : g.toNat ≤ 1048576)
    (hptr : g.toNat ≤ ptr.toNat) (hptrhi : ptr.toNat + 8 ≤ 1048576) :
    TerminatesWith env «module» 5 st0 [.i32 ptr]
      (fun st' vs => Frame g st' ∧
        vs = [.i32 (if 0 < (st0.mem.read64 ptr).toInt64 then 1 else 0)] ∧
        (∀ i : Nat, (i < g.toNat - 16 ∨ g.toNat ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hpg, hg⟩ := hfr
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32], [.i32], func5, [.i32]⟩) rfl
  unfold func5
  wp_run
  simp [hg, hpg]
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simpa using hlo)]
    rfl
  have h12 : (g - 16 + 12).toNat = g.toNat - 4 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hrd : ((st0.mem.write32 (g - 16 + 12) ptr).read64 ptr) = st0.mem.read64 ptr := by
    rw [read64_write32_disjoint _ _ _ _ (by omega)]
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · simp [Frame, hpg, hg]
  · simp [hrd, one_and_ite]
  · intro i hi
    exact write32_bytes_of_disjoint _ _ _ _ (by omega)

/-- `func7` is `Option::unwrap_or_default` at the (tag, payload) pair
level: returns `p` when the tag's low bit is set, else `0`. -/
theorem func7_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32) (t p : UInt64)
    (hfr : Frame g st0)
    (hlo : 32 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 7 st0 [.i64 p, .i64 t]
      (fun st' vs => Frame g st' ∧
        vs = [.i64 (if 1 &&& t.toUInt32 = 0 then 0 else p)]) := by
  obtain ⟨hpg, hg⟩ := hfr
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i64], [.i32], func7, [.i64]⟩) rfl
  unfold func7
  wp_run
  simp [hg, hpg]
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simpa using hlo)]
    rfl
  have h8 : (g - 32 + 8).toNat = g.toNat - 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h16 : (g - 32 + 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h24 : (g - 32 + 24).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, by omega, ?_⟩
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  have hrd8 : ((st0.mem.write64 (g - 32 + 8) t).write64 (g - 32 + 16)
      p).read64 (g - 32 + 8) = t := by
    rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  have hrd16 : ((st0.mem.write64 (g - 32 + 8) t).write64 (g - 32 + 16)
      p).read64 (g - 32 + 16) = p := by
    rw [read64_write64_same]
  have hwrap : UInt32.ofNat (t.toNat % 4294967296) = t.toUInt32 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide)), UInt64.toNat_toUInt32]
  simp [hpg, hrd8, hrd16, hwrap]
  refine ⟨by omega, ?_⟩
  by_cases hc : 1 &&& t.toUInt32 = 0
  · simp [hc, hpg, Frame, hg, read64_write64_same]
    omega
  · simp [hc, hpg, Frame, hg, read64_write64_same]
    omega

/-- `func9` is `Option::or` at the (tag, payload) pair level: writes the
first pair at `ptr` when its tag's low bit is set, else the second. -/
theorem func9_spec (env : HostEnv Unit) (st0 : Store Unit) (g ptr : UInt32)
    (t1 p1 t2 p2 : UInt64)
    (hfr : Frame g st0)
    (hlo : 32 ≤ g.toNat) (hhi : g.toNat ≤ 1048576)
    (hptr : ptr.toNat + 16 ≤ 1048576) :
    TerminatesWith env «module» 9 st0 [.i64 p2, .i64 t2, .i64 p1, .i64 t1, .i32 ptr]
      (fun st' vs => Frame g st' ∧ vs = [] ∧
        st'.mem.read64 ptr = (if 1 &&& t1.toUInt32 = 0 then t2 else t1) ∧
        st'.mem.read64 (ptr + 8) = (if 1 &&& t1.toUInt32 = 0 then p2 else p1)) := by
  obtain ⟨hpg, hg⟩ := hfr
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i64, .i64, .i64, .i64], [.i32], func9, []⟩) rfl
  unfold func9
  wp_run
  simp [hg, hpg]
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simpa using hlo)]
    rfl
  have h8 : (g - 32 + 8).toNat = g.toNat - 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h16 : (g - 32 + 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h24 : (g - 32 + 24).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hp8 : (ptr + 8).toNat = ptr.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  have hwrap : UInt32.ofNat (t1.toNat % 4294967296) = t1.toUInt32 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide)), UInt64.toNat_toUInt32]
  simp [hpg, hwrap]
  by_cases hc : 1 &&& t1.toUInt32 = 0
  · simp [hc, hpg, Frame, hg, read64_write64_same]
    refine ⟨by omega, by omega, ?_⟩
    rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · simp [hc, hpg, Frame, hg, read64_write64_same]
    refine ⟨by omega, by omega, ?_⟩
    rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]

/-- `func12` is `Option::is_some` at the pair level, reading the tag at
`ptr` and comparing its low 32 bits with `1`. -/
theorem func12_spec (env : HostEnv Unit) (st0 : Store Unit) (g ptr : UInt32)
    (hfr : Frame g st0)
    (hlo : 16 ≤ g.toNat) (hhi : g.toNat ≤ 1048576)
    (hptr : g.toNat ≤ ptr.toNat) (hptrhi : ptr.toNat + 8 ≤ 1048576) :
    TerminatesWith env «module» 12 st0 [.i32 ptr]
      (fun st' vs => Frame g st' ∧
        vs = [.i32 (if (st0.mem.read64 ptr).toUInt32 = 1 then 1 else 0)]) := by
  obtain ⟨hpg, hg⟩ := hfr
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32], [.i32], func12, [.i32]⟩) rfl
  unfold func12
  wp_run
  simp [hg, hpg]
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simpa using hlo)]
    rfl
  have h12 : (g - 16 + 12).toNat = g.toNat - 4 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hrd : ((st0.mem.write32 (g - 16 + 12) ptr).read64 ptr) = st0.mem.read64 ptr := by
    rw [read64_write32_disjoint _ _ _ _ (by omega)]
  have hwrap : UInt32.ofNat ((st0.mem.read64 ptr).toNat % 4294967296)
      = (st0.mem.read64 ptr).toUInt32 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide)), UInt64.toNat_toUInt32]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · simp [Frame, hpg, hg]
  · simp [hrd, hwrap, one_and_ite]

/-- `func15` is the `map_add` closure body: adds the captured `k` (the
i64 at the environment pointer `envp`) to its argument. -/
theorem func15_spec (env : HostEnv Unit) (st0 : Store Unit) (g envp : UInt32) (x : UInt64)
    (tail : List Value)
    (hfr : Frame g st0)
    (hlo : 32 ≤ g.toNat) (hhi : g.toNat ≤ 1048576)
    (henv : g.toNat ≤ envp.toNat) (henvhi : envp.toNat + 8 ≤ 1048576) :
    TerminatesWith env «module» 15 st0 ([.i64 x, .i32 envp] ++ tail)
      (fun st' vs => Frame g st' ∧
        vs = .i64 (x + st0.mem.read64 envp) :: tail) := by
  obtain ⟨hpg, hg⟩ := hfr
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32, .i64], [.i32, .i64], func15, [.i64]⟩) rfl
  unfold func15
  wp_run
  simp [hg, hpg]
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simpa using hlo)]
    rfl
  have h4 : (g - 32 + 4).toNat = g.toNat - 28 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h8 : (g - 32 + 8).toNat = g.toNat - 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h16 : (g - 32 + 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h24 : (g - 32 + 24).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hrd : (((st0.mem.write32 (g - 32 + 4) envp).write64 (g - 32 + 8) x).read64 envp)
      = st0.mem.read64 envp := by
    rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write32_disjoint _ _ _ _ (by omega)]
  simp [hrd, Frame, hpg, hg]
  omega

/-! ## Per-function lemmas: one level up (single direct callee) -/

/-- `func0` packs a (tag, payload) pair back into the sentinel encoding
via `func1(t, p, sentinel)`: `p` when the tag's low bit is set, else the
sentinel. -/
theorem func0_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32) (t p : UInt64)
    (hfr : Frame g st0)
    (hlo : 48 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 0 st0 [.i64 p, .i64 t]
      (fun st' vs => Frame g st' ∧
        vs = [.i64 (if 1 &&& t.toUInt32 = 0 then sentinel else p)]) := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i64], [.i32, .i64], func0, [.i64]⟩) rfl
  unfold func0
  wp_run
  simp [hg, hpg]
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  refine ⟨by omega, by omega, ?_⟩
  apply wp_call_of_terminates (func1_spec env _ (g - 16) t p sentinel
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩ (by omega) (by omega))
  rintro st' vs ⟨⟨hpg', hg'⟩, rfl⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  have hback : 16 + (g - 16) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]
    simp
    omega
  wp_run
  simp [hg', hback, Frame, hpg', List.getElem?_set_self hglen']

/-- `func4` is `Option::filter(|x| x > 0)` at the (tag, payload) pair
level, writing the filtered pair at `ptr`: keeps the pair (tag 1,
payload `p`) iff the input tag's low bit is set and `p` is strictly
positive, else writes tag 0. -/
theorem func4_spec (env : HostEnv Unit) (st0 : Store Unit) (g ptr : UInt32) (t p : UInt64)
    (hfr : Frame g st0)
    (hlo : 48 ≤ g.toNat) (hhi : g.toNat ≤ 1048576)
    (hptrlo : g.toNat ≤ ptr.toNat) (hptr : ptr.toNat + 16 ≤ 1048576) :
    TerminatesWith env «module» 4 st0 [.i64 p, .i64 t, .i32 ptr]
      (fun st' vs => Frame g st' ∧ vs = [] ∧
        st'.mem.read64 ptr
          = (if 1 &&& t.toUInt32 = 0 then 0 else if 0 < p.toInt64 then 1 else 0) ∧
        (1 &&& t.toUInt32 ≠ 0 → 0 < p.toInt64 → st'.mem.read64 (ptr + 8) = p)) := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i64, .i64], [.i32], func4, []⟩) rfl
  unfold func4
  wp_run
  simp [hg, hpg]
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h8 : (g - 32 + 8).toNat = g.toNat - 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h16 : (g - 32 + 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have ha16 : (16 + (g - 32)).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hp8 : (ptr + 8).toNat = ptr.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  have hback : 32 + (g - 32) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, by omega, ?_⟩
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  have hrdt : ((st0.mem.write64 (g - 32) t).write64 (g - 32 + 8) p).read64 (g - 32) = t := by
    rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  have hwrap : UInt32.ofNat (t.toNat % 4294967296) = t.toUInt32 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide)), UInt64.toNat_toUInt32]
  simp [hpg, hrdt, hwrap]
  by_cases hc : 1 &&& t.toUInt32 = 0
  · -- tag bit clear: input is `None`, write tag 0 and exit
    simp [hc, hpg, Frame, List.getElem?_set_self hglen, hback, read64_write64_same]
    omega
  · -- tag bit set: load the payload, test positivity via `func5`
    simp [hc]
    have hrdp : ((st0.mem.write64 (g - 32) t).write64 (g - 32 + 8) p).read64 (g - 32 + 8)
        = p := read64_write64_same _ _ _
    rw [show (16 : UInt32) + (g - 32) = g - 32 + 16 by rw [UInt32.add_comm]]
    refine ⟨by omega, by omega, by omega, ?_⟩
    apply wp_call_of_terminates (func5_spec env _ (g - 32) (g - 32 + 16)
      ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
      (by omega) (by omega) (by omega) (by omega))
    rintro st5 vs5 ⟨⟨hpg5, hg5⟩, rfl, hpres5⟩
    obtain ⟨hglen5, -⟩ := List.getElem?_eq_some_iff.mp hg5
    have hrd16 : st5.mem.read64 (g - 32 + 16) = p := by
      rw [read64_eq_of_bytes_range _ _ _ (fun i h1 h2 => hpres5 i (by omega))]
      rw [hrdp, read64_write64_same]
    wp_run
    simp [hrdp, read64_write64_same]
    by_cases hpos : 0 < p.toInt64
    · -- payload positive: keep the pair
      simp [hpos, hpg5, hg5, hrd16, Frame, List.getElem?_set_self hglen5, hback]
      refine ⟨by omega, by omega, by omega, ?_⟩
      rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
    · -- payload not positive: filtered out, write tag 0
      simp [hpos, hpg5, hg5, Frame, List.getElem?_set_self hglen5, hback]
      exact ⟨by omega, Int64.not_lt.mp hpos⟩

/-- `func14` is `Option::map(|x| x + k)` at the pair level, where `k` is
the i64 captured in the closure environment at `envp`: writes the mapped
pair at `ptr`. -/
theorem func14_spec (env : HostEnv Unit) (st0 : Store Unit) (g ptr envp : UInt32)
    (t p : UInt64)
    (hfr : Frame g st0)
    (hlo : 64 ≤ g.toNat) (hhi : g.toNat ≤ 1048576)
    (henv : g.toNat ≤ envp.toNat) (henvhi : envp.toNat + 8 ≤ 1048576)
    (hptrlo : g.toNat ≤ ptr.toNat) (hptr : ptr.toNat + 16 ≤ 1048576) :
    TerminatesWith env «module» 14 st0 [.i32 envp, .i64 p, .i64 t, .i32 ptr]
      (fun st' vs => Frame g st' ∧ vs = [] ∧
        st'.mem.read64 ptr = (if 1 &&& t.toUInt32 = 0 then 0 else 1) ∧
        (1 &&& t.toUInt32 ≠ 0 →
          st'.mem.read64 (ptr + 8) = p + st0.mem.read64 envp)) := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i64, .i64, .i32], [.i32, .i64], func14, []⟩) rfl
  unfold func14
  wp_run
  simp [hg, hpg]
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h8 : (g - 32 + 8).toNat = g.toNat - 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h20 : (g - 32 + 20).toNat = g.toNat - 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h24 : (g - 32 + 24).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hp8 : (ptr + 8).toNat = ptr.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  have hback : 32 + (g - 32) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  have hrdt : (((st0.mem.write64 (g - 32) t).write64 (g - 32 + 8) p).write32 (g - 32 + 20)
      envp).read64 (g - 32) = t := by
    rw [read64_write32_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  have hrdp : (((st0.mem.write64 (g - 32) t).write64 (g - 32 + 8) p).write32 (g - 32 + 20)
      envp).read64 (g - 32 + 8) = p := by
    rw [read64_write32_disjoint _ _ _ _ (by omega), read64_write64_same]
  have hwrap : UInt32.ofNat (t.toNat % 4294967296) = t.toUInt32 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide)), UInt64.toNat_toUInt32]
  simp [hpg, hrdt, hrdp, hwrap]
  by_cases hc : 1 &&& t.toUInt32 = 0
  · -- tag bit clear: `None` maps to `None`
    simp [hc, hpg, Frame, List.getElem?_set_self hglen, hback, read64_write64_same]
    omega
  · -- tag bit set: run the closure body on the payload
    simp [hc]
    have hrdk : ((((st0.mem.write64 (g - 32) t).write64 (g - 32 + 8) p).write32 (g - 32 + 20)
        envp).write64 (g - 32 + 24) p).read64 envp = st0.mem.read64 envp := by
      rw [read64_write64_disjoint _ _ _ _ (by omega),
          read64_write32_disjoint _ _ _ _ (by omega),
          read64_write64_disjoint _ _ _ _ (by omega),
          read64_write64_disjoint _ _ _ _ (by omega)]
    refine ⟨by omega, by omega, by omega, ?_⟩
    apply wp_call_of_terminates (func15_spec env _ (g - 32) envp p [.i32 ptr]
      ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
      (by omega) (by omega) (by omega) (by omega))
    rintro st15 vs15 ⟨⟨hpg15, hg15⟩, rfl⟩
    obtain ⟨hglen15, -⟩ := List.getElem?_eq_some_iff.mp hg15
    wp_run
    simp [hrdk, hpg15, hg15, Frame, List.getElem?_set_self hglen15, hback,
      read64_write64_same]
    refine ⟨by omega, by omega, ?_⟩
    rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]

/-! ## Per-function lemmas: the inner implementations -/

/-- `func2` is the inner `filter_positive`: unpack, filter by `> 0`,
repack. -/
theorem func2_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32) (opt : UInt64)
    (hfr : Frame g st0)
    (hlo : 96 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 2 st0 [.i64 opt]
      (fun st' vs => Frame g st' ∧
        vs = [.i64 (if 0 < opt.toInt64 then opt else sentinel)]) := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64], [.i32, .i64, .i64, .i64], func2, [.i64]⟩) rfl
  unfold func2
  wp_run
  simp [hg, hpg]
  have hsub : (g - 48).toNat = g.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le g 48 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h16 : (g - 48 + 16).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h24 : (g - 48 + 24).toNat = g.toNat - 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h32 : (g - 48 + 32).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h40 : (g - 48 + 40).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h168 : g - 48 + 16 + 8 = g - 48 + 24 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, h16, h24]; simp; omega
  have h328 : g - 48 + 32 + 8 = g - 48 + 40 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, h32, h40]; simp; omega
  have hback : 48 + (g - 48) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, ?_⟩
  rw [show (16 : UInt32) + (g - 48) = g - 48 + 16 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func3_spec env _ (g - 48) (g - 48 + 16) opt
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
    (by omega) (by omega) (by omega))
  rintro st3 vs3 ⟨⟨hpg3, hg3⟩, rfl, htag, hpay, -⟩
  rw [h168] at hpay
  wp_run
  simp [hpg3]
  refine ⟨by omega, by omega, ?_⟩
  rw [show (32 : UInt32) + (g - 48) = g - 48 + 32 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func4_spec env st3 (g - 48) (g - 48 + 32)
    (st3.mem.read64 (g - 48 + 16)) (st3.mem.read64 (g - 48 + 24))
    ⟨hpg3, hg3⟩ (by omega) (by omega) (by omega) (by omega))
  rintro st4 vs4 ⟨⟨hpg4, hg4⟩, rfl, htag4, hpay4⟩
  rw [h328] at hpay4
  wp_run
  simp [hpg4]
  refine ⟨by omega, by omega, ?_⟩
  apply wp_call_of_terminates (func0_spec env st4 (g - 48)
    (st4.mem.read64 (g - 48 + 32)) (st4.mem.read64 (g - 48 + 40))
    ⟨hpg4, hg4⟩ (by omega) (by omega))
  rintro st5 vs5 ⟨⟨hpg5, hg5⟩, rfl⟩
  obtain ⟨hglen5, -⟩ := List.getElem?_eq_some_iff.mp hg5
  wp_run
  simp [hg5, hback, Frame, hpg5, List.getElem?_set_self hglen5]
  -- close the value chain by case analysis on the input
  by_cases hopt : opt = (9223372036854775808 : UInt64)
  · -- `None` in: tag 0 all the way down, sentinel out
    simp [hopt] at htag
    rw [htag] at htag4
    simp at htag4
    rw [htag4]
    simp [hopt]
  · -- `Some` in: tag 1, payload `opt`
    simp [hopt] at htag hpay
    rw [htag, hpay] at hpay4
    rw [htag, hpay] at htag4
    simp at htag4 hpay4
    by_cases hp : 0 < opt.toInt64
    · simp [hp] at htag4
      rw [htag4, hpay4 hp]
      simp [hp]
    · simp [hp] at htag4
      rw [htag4]
      simp [hp]

/-- `func6` is the inner `unwrap_or_default`: unpack, then `func7`. -/
theorem func6_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32) (opt : UInt64)
    (hfr : Frame g st0)
    (hlo : 64 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 6 st0 [.i64 opt]
      (fun st' vs => Frame g st' ∧
        vs = [.i64 (if opt = sentinel then 0 else opt)]) := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64], [.i32, .i64], func6, [.i64]⟩) rfl
  unfold func6
  wp_run
  simp [hg, hpg]
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h16 : (g - 32 + 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h24 : (g - 32 + 24).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h168 : g - 32 + 16 + 8 = g - 32 + 24 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, h16, h24]; simp; omega
  have hback : 32 + (g - 32) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, ?_⟩
  rw [show (16 : UInt32) + (g - 32) = g - 32 + 16 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func3_spec env _ (g - 32) (g - 32 + 16) opt
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
    (by omega) (by omega) (by omega))
  rintro st3 vs3 ⟨⟨hpg3, hg3⟩, rfl, htag, hpay, -⟩
  rw [h168] at hpay
  wp_run
  simp [hpg3]
  refine ⟨by omega, by omega, ?_⟩
  apply wp_call_of_terminates (func7_spec env st3 (g - 32)
    (st3.mem.read64 (g - 32 + 16)) (st3.mem.read64 (g - 32 + 24))
    ⟨hpg3, hg3⟩ (by omega) (by omega))
  rintro st7 vs7 ⟨⟨hpg7, hg7⟩, rfl⟩
  obtain ⟨hglen7, -⟩ := List.getElem?_eq_some_iff.mp hg7
  wp_run
  simp [hg7, hback, Frame, hpg7, List.getElem?_set_self hglen7]
  by_cases hopt : opt = (9223372036854775808 : UInt64)
  · simp [hopt] at htag
    rw [htag]
    simp [hopt]
  · simp [hopt] at htag hpay
    rw [htag, hpay]
    simp [hopt]

/-- `func10` is the inner `wrap`: pack `(1, v)`, i.e. the identity on
the sentinel encoding. -/
theorem func10_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32) (v : UInt64)
    (hfr : Frame g st0)
    (hlo : 64 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 10 st0 [.i64 v]
      (fun st' vs => Frame g st' ∧ vs = [.i64 v]) := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64], [.i32, .i64], func10, [.i64]⟩) rfl
  unfold func10
  wp_run
  simp [hg, hpg]
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have hback : 16 + (g - 16) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, ?_⟩
  apply wp_call_of_terminates (func0_spec env _ (g - 16) 1 v
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩ (by omega) (by omega))
  rintro st' vs ⟨⟨hpg', hg'⟩, rfl⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  wp_run
  simp [hg', hback, Frame, hpg', List.getElem?_set_self hglen']

/-- `func11` is the inner `is_some`: pack at `sp+8`, then test the tag
via `func12`. -/
theorem func11_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32) (opt : UInt64)
    (hfr : Frame g st0)
    (hlo : 64 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 11 st0 [.i64 opt]
      (fun st' vs => Frame g st' ∧
        vs = [.i32 (if opt = sentinel then 0 else 1)]) := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64], [.i32, .i32], func11, [.i32]⟩) rfl
  unfold func11
  wp_run
  simp [hg, hpg]
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h8 : (g - 32 + 8).toNat = g.toNat - 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 32 + (g - 32) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, ?_⟩
  rw [show (8 : UInt32) + (g - 32) = g - 32 + 8 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func3_spec env _ (g - 32) (g - 32 + 8) opt
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
    (by omega) (by omega) (by omega))
  rintro st3 vs3 ⟨⟨hpg3, hg3⟩, rfl, htag, -, -⟩
  wp_run
  simp
  rw [show (8 : UInt32) + (g - 32) = g - 32 + 8 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func12_spec env st3 (g - 32) (g - 32 + 8)
    ⟨hpg3, hg3⟩ (by omega) (by omega) (by omega) (by omega))
  rintro st12 vs12 ⟨⟨hpg12, hg12⟩, rfl⟩
  obtain ⟨hglen12, -⟩ := List.getElem?_eq_some_iff.mp hg12
  wp_run
  simp [hg12, hback, Frame, hpg12, List.getElem?_set_self hglen12]
  by_cases hopt : opt = (9223372036854775808 : UInt64)
  · simp [hopt] at htag
    rw [htag]
    simp [hopt]
  · simp [hopt] at htag
    rw [htag]
    simp [hopt]

/-- `func16` is the inner `unwrap_or`: pack `a` at `sp+16`, then
`func1(tag, payload, b)`. -/
theorem func16_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32) (a b : UInt64)
    (hfr : Frame g st0)
    (hlo : 64 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 16 st0 [.i64 b, .i64 a]
      (fun st' vs => Frame g st' ∧
        vs = [.i64 (if a = sentinel then b else a)]) := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i64], [.i32, .i64], func16, [.i64]⟩) rfl
  unfold func16
  wp_run
  simp [hg, hpg]
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h16 : (g - 32 + 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h24 : (g - 32 + 24).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h168 : g - 32 + 16 + 8 = g - 32 + 24 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, h16, h24]; simp; omega
  have hback : 32 + (g - 32) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, by omega, ?_⟩
  rw [show (16 : UInt32) + (g - 32) = g - 32 + 16 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func3_spec env _ (g - 32) (g - 32 + 16) a
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
    (by omega) (by omega) (by omega))
  rintro st3 vs3 ⟨⟨hpg3, hg3⟩, rfl, htag, hpay, -⟩
  rw [h168] at hpay
  wp_run
  simp [hpg3]
  refine ⟨by omega, by omega, ?_⟩
  apply wp_call_of_terminates (func1_spec env st3 (g - 32)
    (st3.mem.read64 (g - 32 + 16)) (st3.mem.read64 (g - 32 + 24)) b
    ⟨hpg3, hg3⟩ (by omega) (by omega))
  rintro st1 vs1 ⟨⟨hpg1, hg1⟩, rfl⟩
  obtain ⟨hglen1, -⟩ := List.getElem?_eq_some_iff.mp hg1
  wp_run
  simp [hg1, hback, Frame, hpg1, List.getElem?_set_self hglen1]
  by_cases hopt : a = (9223372036854775808 : UInt64)
  · simp [hopt] at htag
    rw [htag]
    simp [hopt]
  · simp [hopt] at htag hpay
    rw [htag, hpay]
    simp [hopt]

/-- `func8` is the inner `or`: pack both options, select with `func9`,
repack with `func0`. -/
theorem func8_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32) (a b : UInt64)
    (hfr : Frame g st0)
    (hlo : 112 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 8 st0 [.i64 b, .i64 a]
      (fun st' vs => Frame g st' ∧
        vs = [.i64 (if a = sentinel then b else a)]) := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i64], [.i32, .i64, .i64, .i64, .i64, .i64], func8, [.i64]⟩) rfl
  unfold func8
  wp_run
  simp [hg, hpg]
  have hsub : (g - 64).toNat = g.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le g 64 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h16 : (g - 64 + 16).toNat = g.toNat - 48 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h24 : (g - 64 + 24).toNat = g.toNat - 40 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h32 : (g - 64 + 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h40 : (g - 64 + 40).toNat = g.toNat - 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h48 : (g - 64 + 48).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h56 : (g - 64 + 56).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h168 : g - 64 + 16 + 8 = g - 64 + 24 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, h16, h24]; simp; omega
  have h328 : g - 64 + 32 + 8 = g - 64 + 40 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, h32, h40]; simp; omega
  have h488 : g - 64 + 48 + 8 = g - 64 + 56 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, h48, h56]; simp; omega
  have hback : 64 + (g - 64) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, by omega, ?_⟩
  rw [show (16 : UInt32) + (g - 64) = g - 64 + 16 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func3_spec env _ (g - 64) (g - 64 + 16) a
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
    (by omega) (by omega) (by omega))
  rintro st3 vs3 ⟨⟨hpg3, hg3⟩, rfl, htagA, hpayA, -⟩
  rw [h168] at hpayA
  wp_run
  simp [hpg3]
  refine ⟨by omega, by omega, ?_⟩
  rw [show (32 : UInt32) + (g - 64) = g - 64 + 32 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func3_spec env st3 (g - 64) (g - 64 + 32) b
    ⟨hpg3, hg3⟩ (by omega) (by omega) (by omega))
  rintro st3b vs3b ⟨⟨hpg3b, hg3b⟩, rfl, htagB, hpayB, -⟩
  rw [h328] at hpayB
  wp_run
  simp [hpg3b]
  refine ⟨by omega, by omega, ?_⟩
  rw [show (48 : UInt32) + (g - 64) = g - 64 + 48 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func9_spec env st3b (g - 64) (g - 64 + 48)
    (st3.mem.read64 (g - 64 + 16)) (st3.mem.read64 (g - 64 + 24))
    (st3b.mem.read64 (g - 64 + 32)) (st3b.mem.read64 (g - 64 + 40))
    ⟨hpg3b, hg3b⟩ (by omega) (by omega) (by omega))
  rintro st9 vs9 ⟨⟨hpg9, hg9⟩, rfl, htag9, hpay9⟩
  rw [h488] at hpay9
  wp_run
  simp [hpg9]
  refine ⟨by omega, by omega, ?_⟩
  apply wp_call_of_terminates (func0_spec env st9 (g - 64)
    (st9.mem.read64 (g - 64 + 48)) (st9.mem.read64 (g - 64 + 56))
    ⟨hpg9, hg9⟩ (by omega) (by omega))
  rintro st5 vs5 ⟨⟨hpg5, hg5⟩, rfl⟩
  obtain ⟨hglen5, -⟩ := List.getElem?_eq_some_iff.mp hg5
  wp_run
  simp [hg5, hback, Frame, hpg5, List.getElem?_set_self hglen5]
  by_cases ha : a = (9223372036854775808 : UInt64)
  · -- first operand `None`: the second pair is selected
    simp [ha] at htagA
    rw [htagA] at htag9 hpay9
    simp at htag9 hpay9
    by_cases hb : b = (9223372036854775808 : UInt64)
    · simp [hb] at htagB
      rw [htagB] at htag9
      rw [htag9]
      simp [ha, hb]
    · simp [hb] at htagB hpayB
      rw [htagB] at htag9
      rw [hpayB] at hpay9
      rw [htag9, hpay9]
      simp [ha]
  · -- first operand `Some`: it is kept
    simp [ha] at htagA hpayA
    rw [htagA] at htag9 hpay9
    rw [hpayA] at hpay9
    simp at htag9 hpay9
    rw [htag9, hpay9]
    simp [ha]

/-- `func13` is the inner `map_add`: pack, map the closure `+k` over the
pair via `func14`, repack. -/
theorem func13_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32) (opt k : UInt64)
    (hfr : Frame g st0)
    (hlo : 112 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 13 st0 [.i64 k, .i64 opt]
      (fun st' vs => Frame g st' ∧
        vs = [.i64 (if opt = sentinel then sentinel else opt + k)]) := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i64], [.i32, .i64, .i64, .i64], func13, [.i64]⟩) rfl
  unfold func13
  wp_run
  simp [hg, hpg]
  have hsub : (g - 48).toNat = g.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le g 48 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h8 : (g - 48 + 8).toNat = g.toNat - 40 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h16 : (g - 48 + 16).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h24 : (g - 48 + 24).toNat = g.toNat - 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h32 : (g - 48 + 32).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h40 : (g - 48 + 40).toNat = g.toNat - 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have h168 : g - 48 + 16 + 8 = g - 48 + 24 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, h16, h24]; simp; omega
  have h328 : g - 48 + 32 + 8 = g - 48 + 40 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, h32, h40]; simp; omega
  have hback : 48 + (g - 48) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, by omega, ?_⟩
  rw [show (16 : UInt32) + (g - 48) = g - 48 + 16 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func3_spec env _ (g - 48) (g - 48 + 16) opt
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
    (by omega) (by omega) (by omega))
  rintro st3 vs3 ⟨⟨hpg3, hg3⟩, rfl, htag, hpay, hpres3⟩
  rw [h168] at hpay
  -- the captured `k` at `sp` survives the pack (disjoint from its
  -- scratch and the pair)
  have hrdk : st3.mem.read64 (g - 48) = k := by
    rw [read64_eq_of_bytes_range _ _ _ (fun i hi1 hi2 => hpres3 i (by omega) (by omega))]
    rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  wp_run
  simp [hpg3]
  refine ⟨by omega, by omega, ?_⟩
  rw [show (32 : UInt32) + (g - 48) = g - 48 + 32 by rw [UInt32.add_comm]]
  apply wp_call_of_terminates (func14_spec env st3 (g - 48) (g - 48 + 32) (g - 48)
    (st3.mem.read64 (g - 48 + 16)) (st3.mem.read64 (g - 48 + 24))
    ⟨hpg3, hg3⟩ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  rintro st14 vs14 ⟨⟨hpg14, hg14⟩, rfl, htag14, hpay14⟩
  rw [h328] at hpay14
  rw [hrdk] at hpay14
  wp_run
  simp [hpg14]
  refine ⟨by omega, by omega, ?_⟩
  apply wp_call_of_terminates (func0_spec env st14 (g - 48)
    (st14.mem.read64 (g - 48 + 32)) (st14.mem.read64 (g - 48 + 40))
    ⟨hpg14, hg14⟩ (by omega) (by omega))
  rintro st5 vs5 ⟨⟨hpg5, hg5⟩, rfl⟩
  obtain ⟨hglen5, -⟩ := List.getElem?_eq_some_iff.mp hg5
  wp_run
  simp [hg5, hback, Frame, hpg5, List.getElem?_set_self hglen5]
  by_cases hopt : opt = (9223372036854775808 : UInt64)
  · simp [hopt] at htag
    rw [htag] at htag14
    simp at htag14
    rw [htag14]
    simp [hopt]
  · simp [hopt] at htag hpay
    rw [htag] at htag14 hpay14
    rw [hpay] at hpay14
    simp at htag14 hpay14
    rw [htag14, hpay14]
    simp [hopt]

/-! ## Wasm-level specs (raw `UInt64` view)

The exports are thin wrappers (indices 17–23) that spill their
arguments to a fresh shadow-stack frame and call the inner
implementation. Because the bodies genuinely use linear memory, each
spec is pinned to the canonical instantiation
`initial = «module».initialStore`. -/

/-- Facts about the canonical store shared by every wrapper proof. -/
private theorem initial_pages : («module».initialStore : Store Unit).mem.pages = 16 := rfl

private theorem initial_global0 :
    («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := rfl

private theorem initial_glen :
    0 < («module».initialStore : Store Unit).globals.globals.length := by
  decide

/-- The exported `filter_positive` returns `opt` when its `i64` argument
encodes a strictly-positive `Some`, and the sentinel `None` otherwise.

Informal spec:
For any `opt : UInt64`, the wasm export `filter_positive` (run from the
module's canonical instantiation) terminates and leaves a single i64 on
the value stack equal to `opt` if `opt.toInt64 > 0` and to the
`None`-sentinel (`i64::MIN`) otherwise. The "filtered out" and "already
None" cases share the same answer — the sentinel `i64::MIN < 0` is
never `> 0`. -/
@[spec_of "rust-exported" "rust_option::filter_positive"]
def FilterPositiveSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (opt : UInt64),
    initial = «module».initialStore →
    TerminatesWith env «module» 17 initial [.i64 opt]
      (fun _ rs => rs = [.i64 (if opt.toInt64 > 0 then opt else sentinel)])

@[proves Project.RustOption.Spec.FilterPositiveSpec]
theorem filter_positive_correct : FilterPositiveSpec := by
  intro env initial opt hinit
  subst hinit
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64], [.i32, .i64], func17, [.i64]⟩) rfl
  unfold func17
  wp_run
  simp [initial_global0, initial_pages]
  apply wp_call_of_terminates (func2_spec env _ (1048576 - 16) opt
    ⟨by simp [initial_pages], by simp [List.getElem?_set_self initial_glen]⟩
    (by decide) (by decide))
  rintro st' vs ⟨⟨hpg', hg'⟩, rfl⟩
  wp_run
  simp [hg']

/-- The exported `unwrap_or_default` returns `opt` when it is `Some`,
and `0` (the `Default::default()` value for `i64`) when it is `None`.

Informal spec:
For any `opt : UInt64`, the wasm export `unwrap_or_default` (run from
the module's canonical instantiation) terminates and leaves a single
i64 on the value stack equal to `0` if `opt = sentinel` (i.e. encodes
`None`) and to `opt` otherwise. -/
@[spec_of "rust-exported" "rust_option::unwrap_or_default"]
def UnwrapOrDefaultSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (opt : UInt64),
    initial = «module».initialStore →
    TerminatesWith env «module» 22 initial [.i64 opt]
      (fun _ rs => rs = [.i64 (if opt = sentinel then 0 else opt)])

@[proves Project.RustOption.Spec.UnwrapOrDefaultSpec]
theorem unwrap_or_default_correct : UnwrapOrDefaultSpec := by
  intro env initial opt hinit
  subst hinit
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64], [.i32, .i64], func22, [.i64]⟩) rfl
  unfold func22
  wp_run
  simp [initial_global0, initial_pages]
  apply wp_call_of_terminates (func6_spec env _ (1048576 - 16) opt
    ⟨by simp [initial_pages], by simp [List.getElem?_set_self initial_glen]⟩
    (by decide) (by decide))
  rintro st' vs ⟨⟨hpg', hg'⟩, rfl⟩
  wp_run
  simp [hg']

/-- The exported `or` returns `a` when it is `Some`, otherwise `b`.

Informal spec:
For any `a b : UInt64`, the wasm export `or` (run from the module's
canonical instantiation) terminates and leaves a single i64 on the
value stack equal to `b` if `a = sentinel` (i.e. `a` encodes `None`)
and to `a` otherwise. -/
@[spec_of "rust-exported" "rust_option::or"]
def OrSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    initial = «module».initialStore →
    TerminatesWith env «module» 20 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (if a = sentinel then b else a)])

@[proves Project.RustOption.Spec.OrSpec]
theorem or_correct : OrSpec := by
  intro env initial a b hinit
  subst hinit
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i64], [.i32, .i64], func20, [.i64]⟩) rfl
  unfold func20
  wp_run
  simp [initial_global0, initial_pages]
  apply wp_call_of_terminates (func8_spec env _ (1048576 - 16) a b
    ⟨by simp [initial_pages], by simp [List.getElem?_set_self initial_glen]⟩
    (by decide) (by decide))
  rintro st' vs ⟨⟨hpg', hg'⟩, rfl⟩
  wp_run
  simp [hg']

/-- The exported `unwrap_or` computes the same function as `or`, through
a different inner call chain (`func16`/`func1` rather than
`func8`/`func9`).

Informal spec:
For any `a b : UInt64`, the wasm export `unwrap_or` (run from the
module's canonical instantiation) terminates and leaves a single i64 on
the value stack equal to `b` if `a = sentinel` and to `a` otherwise. -/
@[spec_of "rust-exported" "rust_option::unwrap_or"]
def UnwrapOrSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    initial = «module».initialStore →
    TerminatesWith env «module» 21 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (if a = sentinel then b else a)])

@[proves Project.RustOption.Spec.UnwrapOrSpec]
theorem unwrap_or_correct : UnwrapOrSpec := by
  intro env initial a b hinit
  subst hinit
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i64], [.i32, .i64], func21, [.i64]⟩) rfl
  unfold func21
  wp_run
  simp [initial_global0, initial_pages]
  apply wp_call_of_terminates (func16_spec env _ (1048576 - 16) a b
    ⟨by simp [initial_pages], by simp [List.getElem?_set_self initial_glen]⟩
    (by decide) (by decide))
  rintro st' vs ⟨⟨hpg', hg'⟩, rfl⟩
  wp_run
  simp [hg']

/-- The exported `wrap` lifts an unwrapped `i64` into the `Some`
encoding — the identity, since `Some(v)` is encoded as `v` itself.

Informal spec:
For any `v : UInt64`, the wasm export `wrap` (run from the module's
canonical instantiation) terminates and leaves the input value on the
value stack unchanged. -/
@[spec_of "rust-exported" "rust_option::wrap"]
def WrapSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (v : UInt64),
    initial = «module».initialStore →
    TerminatesWith env «module» 23 initial [.i64 v]
      (fun _ rs => rs = [.i64 v])

@[proves Project.RustOption.Spec.WrapSpec]
theorem wrap_correct : WrapSpec := by
  intro env initial v hinit
  subst hinit
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64], [.i32, .i64], func23, [.i64]⟩) rfl
  unfold func23
  wp_run
  simp [initial_global0, initial_pages]
  apply wp_call_of_terminates (func10_spec env _ (1048576 - 16) v
    ⟨by simp [initial_pages], by simp [List.getElem?_set_self initial_glen]⟩
    (by decide) (by decide))
  rintro st' vs ⟨⟨hpg', hg'⟩, rfl⟩
  wp_run
  simp [hg']

/-- The exported `is_some` returns `1 : i32` when `opt ≠ sentinel`,
else `0`.

Informal spec:
For any `opt : UInt64`, the wasm export `is_some` (run from the
module's canonical instantiation) terminates and leaves a single i32 on
the value stack equal to `0` if `opt = sentinel` and to `1`
otherwise. -/
@[spec_of "rust-exported" "rust_option::is_some"]
def IsSomeSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (opt : UInt64),
    initial = «module».initialStore →
    TerminatesWith env «module» 18 initial [.i64 opt]
      (fun _ rs => rs = [.i32 (if opt = sentinel then 0 else 1)])

@[proves Project.RustOption.Spec.IsSomeSpec]
theorem is_some_correct : IsSomeSpec := by
  intro env initial opt hinit
  subst hinit
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64], [.i32, .i32], func18, [.i32]⟩) rfl
  unfold func18
  wp_run
  simp [initial_global0, initial_pages]
  apply wp_call_of_terminates (func11_spec env _ (1048576 - 16) opt
    ⟨by simp [initial_pages], by simp [List.getElem?_set_self initial_glen]⟩
    (by decide) (by decide))
  rintro st' vs ⟨⟨hpg', hg'⟩, rfl⟩
  wp_run
  simp [hg']

/-- The exported `map_add` propagates the sentinel and otherwise adds
`k` (wrapping) to the contained value.

Informal spec:
For any `opt k : UInt64`, the wasm export `map_add` (run from the
module's canonical instantiation) terminates and leaves a single i64 on
the value stack equal to the sentinel if `opt = sentinel`, else to
`opt + k` (UInt64 wrapping addition, which models
`i64::wrapping_add`). -/
@[spec_of "rust-exported" "rust_option::map_add"]
def MapAddSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (opt k : UInt64),
    initial = «module».initialStore →
    TerminatesWith env «module» 19 initial [.i64 k, .i64 opt]
      (fun _ rs => rs = [.i64 (if opt = sentinel then sentinel else opt + k)])

@[proves Project.RustOption.Spec.MapAddSpec]
theorem map_add_correct : MapAddSpec := by
  intro env initial opt k hinit
  subst hinit
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i64], [.i32, .i64], func19, [.i64]⟩) rfl
  unfold func19
  wp_run
  simp [initial_global0, initial_pages]
  apply wp_call_of_terminates (func13_spec env _ (1048576 - 16) opt k
    ⟨by simp [initial_pages], by simp [List.getElem?_set_self initial_glen]⟩
    (by decide) (by decide))
  rintro st' vs ⟨⟨hpg', hg'⟩, rfl⟩
  wp_run
  simp [hg']

/-! ## `Option`-level lifts

These restate the wasm specs in terms of `Option Int64`, under the side
condition that no input is `some Int64.minValue` (which would collide
with the sentinel encoding). -/

open Wasm.RustStd.Option

theorem is_some_lifted (env : HostEnv Unit) (initial : Store Unit) (o : Option Int64)
    (hinit : initial = «module».initialStore) (h : o ≠ some Int64.minValue) :
    TerminatesWith env «module» 18 initial [.i64 (encode o)]
      (fun _ rs => rs = [.i32 (if o.isSome then 1 else 0)]) := by
  refine (is_some_correct env initial (encode o) hinit).mono ?_
  intro _ rs hrs; rw [hrs]; congr 1
  cases o with
  | none => simp
  | some x =>
    have hne : encode (some x) ≠ sentinel :=
      encode_ne_sentinel_of_some (by simpa using h)
    rw [if_neg hne]; simp

theorem unwrap_or_lifted (env : HostEnv Unit) (initial : Store Unit) (o : Option Int64)
    (d : UInt64) (hinit : initial = «module».initialStore)
    (h : o ≠ some Int64.minValue) :
    TerminatesWith env «module» 20 initial [.i64 d, .i64 (encode o)]
      (fun _ rs => rs = [.i64 (match o with | some x => x.toUInt64 | none => d)]) := by
  refine (or_correct env initial (encode o) d hinit).mono ?_
  intro _ rs hrs; rw [hrs]; congr 1
  cases o with
  | none => simp
  | some x =>
    have hne : encode (some x) ≠ sentinel :=
      encode_ne_sentinel_of_some (by simpa using h)
    rw [if_neg hne]; simp

end Project.RustOption.Spec
