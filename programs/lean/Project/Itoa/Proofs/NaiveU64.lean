import Project.Itoa.Proofs.Base

/-!
# Naive u64 formatter core and export-wrapper bridges

The export wrappers (`func28`/`func29`/`func31`/`func32`), the conditional
top-level theorems, read-over-write framing, and the naive u64 side:
`func6` (count/write loops + `func6_spec`), `func5_spec`, `func7_spec`.
See `Project.Itoa.Proofs` for the overall proof structure.
-/

namespace Project.Itoa.Proofs

open Wasm

/-! ## Export wrappers (`opt-level=0` shadow-stack chain)

Under the unoptimized pipeline `check_i64` is `func31` and `check_u64`
is `func32`. Each is a 16-byte shadow-stack wrapper that spills its
`(n, cap)` arguments into its frame (debug spills, never read back) and
forwards to a second wrapper of exactly the same shape (`func28` /
`func29`), which forwards to the actual harness (`func21` / `func23`).
The bridge lemmas below peel both hops, reducing `CheckI64Spec` /
`CheckU64Spec` to `HarnessSpec 21` / `HarnessSpec 23` — the still-open
no-trap specs of the equivalence harnesses themselves. -/

@[simp] theorem write64_pages (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).pages = m.pages := rfl

theorem write32_bytes_of_disjoint (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  rw [read32_write32_bytes, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

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

/-- The state every internal function sees on entry and re-establishes
on exit: the canonical 17-page memory and the shadow-stack pointer `g`
in `global 0`. -/
def Frame (g : UInt32) (st : Store Unit) : Prop :=
  st.mem.pages = 17 ∧ st.globals.globals[0]? = some (.i32 g)

/-- The read-only data region — everything at or above the shadow-stack
base `1048576`, in particular the `DIGIT_TABLE` at `digitTableBase` —
agrees with the canonical initial store. The shadow-stack frames all
live strictly below `1048576`, so every function in the module
preserves this. -/
def DataIntact (st : Store Unit) : Prop :=
  ∀ i : Nat, 1048576 ≤ i →
    st.mem.bytes i = («module».initialStore (α := Unit)).mem.bytes i

/-- Shape of the harness specs the wrapper bridges consume: from any
frame state with intact data and enough shadow-stack headroom, the
harness `idx` terminates without trapping, leaves an empty stack, and
restores the frame. `HarnessSpec 21` (`check_i64`'s inner body) and
`HarnessSpec 23` (`check_u64`'s) are precisely the equivalence claims
between the `itoa`-crate formatter and the naive oracle. -/
def HarnessSpec (idx : Nat) : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (g : UInt32) (n : UInt64) (cap : UInt32),
    Frame g st → DataIntact st → 65536 ≤ g.toNat → g.toNat ≤ 1048576 →
    TerminatesWith env «module» idx st [.i32 cap, .i64 n]
      (fun st' rs => rs = [] ∧ Frame g st')

private theorem initial_global0 :
    («module».initialStore (α := Unit)).globals.globals[0]? = some (.i32 1048576) := by
  native_decide

/-- The middle wrapper `func28`: spill `(n, cap)` to a fresh 16-byte
frame, forward to the harness `func21`, restore the stack pointer. -/
theorem func28_spec (hh : HarnessSpec 21) (env : HostEnv Unit) (st0 : Store Unit)
    (g : UInt32) (n : UInt64) (cap : UInt32)
    (hfr : Frame g st0) (hdi : DataIntact st0)
    (hlo : 65552 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 28 st0 [.i32 cap, .i64 n]
      (fun st' rs => rs = [] ∧ Frame g st') := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i32], [.i32], func28, []⟩) rfl
  unfold func28
  wp_run
  simp [hg, hpg]
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h12 : (g - 16 + 12).toNat = g.toNat - 4 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 16 + (g - 16) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, by omega, ?_⟩
  apply wp_call_of_terminates (hh env _ (g - 16) n cap
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
    (fun i hi => by
      rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega)]
      exact hdi i hi)
    (by omega) (by omega))
  rintro st' vs ⟨rfl, hpg', hg'⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  wp_run
  simp [hg', hback, Frame, hpg', List.getElem?_set_self hglen']

/-- The middle wrapper `func29`: same shape as `func28`, forwarding to
the `u64` harness `func23`. -/
theorem func29_spec (hh : HarnessSpec 23) (env : HostEnv Unit) (st0 : Store Unit)
    (g : UInt32) (n : UInt64) (cap : UInt32)
    (hfr : Frame g st0) (hdi : DataIntact st0)
    (hlo : 65552 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 29 st0 [.i32 cap, .i64 n]
      (fun st' rs => rs = [] ∧ Frame g st') := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i32], [.i32], func29, []⟩) rfl
  unfold func29
  wp_run
  simp [hg, hpg]
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h12 : (g - 16 + 12).toNat = g.toNat - 4 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 16 + (g - 16) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, by omega, ?_⟩
  apply wp_call_of_terminates (hh env _ (g - 16) n cap
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
    (fun i hi => by
      rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega)]
      exact hdi i hi)
    (by omega) (by omega))
  rintro st' vs ⟨rfl, hpg', hg'⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  wp_run
  simp [hg', hback, Frame, hpg', List.getElem?_set_self hglen']

/-- The exported wrapper `func31` (`check_i64`). -/
theorem func31_spec (hh : HarnessSpec 21) (env : HostEnv Unit) (st0 : Store Unit)
    (g : UInt32) (n : UInt64) (cap : UInt32)
    (hfr : Frame g st0) (hdi : DataIntact st0)
    (hlo : 65568 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 31 st0 [.i32 cap, .i64 n]
      (fun st' rs => rs = [] ∧ Frame g st') := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i32], [.i32], func31, []⟩) rfl
  unfold func31
  wp_run
  simp [hg, hpg]
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h12 : (g - 16 + 12).toNat = g.toNat - 4 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 16 + (g - 16) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, by omega, ?_⟩
  apply wp_call_of_terminates (func28_spec hh env _ (g - 16) n cap
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
    (fun i hi => by
      rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega)]
      exact hdi i hi)
    (by omega) (by omega))
  rintro st' vs ⟨rfl, hpg', hg'⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  wp_run
  simp [hg', hback, Frame, hpg', List.getElem?_set_self hglen']

/-- The exported wrapper `func32` (`check_u64`). -/
theorem func32_spec (hh : HarnessSpec 23) (env : HostEnv Unit) (st0 : Store Unit)
    (g : UInt32) (n : UInt64) (cap : UInt32)
    (hfr : Frame g st0) (hdi : DataIntact st0)
    (hlo : 65568 ≤ g.toNat) (hhi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 32 st0 [.i32 cap, .i64 n]
      (fun st' rs => rs = [] ∧ Frame g st') := by
  obtain ⟨hpg, hg⟩ := hfr
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i32], [.i32], func32, []⟩) rfl
  unfold func32
  wp_run
  simp [hg, hpg]
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have h12 : (g - 16 + 12).toNat = g.toNat - 4 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 16 + (g - 16) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  refine ⟨by omega, by omega, ?_⟩
  apply wp_call_of_terminates (func29_spec hh env _ (g - 16) n cap
    ⟨by simp [hpg], by simp [List.getElem?_set_self hglen]⟩
    (fun i hi => by
      rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega)]
      exact hdi i hi)
    (by omega) (by omega))
  rintro st' vs ⟨rfl, hpg', hg'⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  wp_run
  simp [hg', hback, Frame, hpg', List.getElem?_set_self hglen']

/-! ## Conditional top-level theorems

The same logical endpoint as the pre-migration file: `CheckI64Spec` /
`CheckU64Spec` reduced to the harness specs. Discharging `HarnessSpec
21` / `HarnessSpec 23` (fast formatter ≡ naive oracle, composed through
`func24`/`func22`, `func3`/`func5` and the byte-compare loop) is the
remaining open proof obligation. -/

theorem check_i64_correct_of_harness_spec (hh : HarnessSpec 21) :
    Project.Itoa.Spec.CheckI64Spec := by
  intro env initial n cap hinit
  subst hinit
  refine (func31_spec hh env _ 1048576 n cap
    ⟨initial_mem_pages, initial_global0⟩ (fun i _ => rfl)
    (by decide) (by decide)).mono ?_
  exact fun st vs h => h.1

theorem check_u64_correct_of_harness_spec (hh : HarnessSpec 23) :
    Project.Itoa.Spec.CheckU64Spec := by
  intro env initial n cap hinit
  subst hinit
  refine (func32_spec hh env _ 1048576 n cap
    ⟨initial_mem_pages, initial_global0⟩ (fun i _ => rfl)
    (by decide) (by decide)).mono ?_
  exact fun st vs h => h.1


/-! Restructured development of `func6_spec` (naive u64 formatter core),
parametric in the shadow-stack pointer `g` (frame `[g−64, g)`) and the
output buffer base `out` (buffer `[out, out+32)`, above the frame and
below the shadow-stack base `1048576`), as required by the ∀-`g`
quantification of `HarnessSpec`.

The two memory-routed loops are proven as STANDALONE lemmas over an
abstract continuation `Q` and abstract trailing program `rest`, so the
per-iteration `simp` passes never traverse the surrounding function
body's weakest-precondition term. `func6_spec` then glues prologue →
count loop → success tail → write loop → epilogue. -/

/-- `(a + b).toNat = a.toNat + b.toNat` when the sum does not wrap. -/
theorem toNat_add_of_lt (a b : UInt32) (h : a.toNat + b.toNat < 4294967296) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt h

/-! ## Read-over-write framing (shape from `NumInteger`) -/

@[simp] theorem read64_write64_same (m : Mem) (a : UInt32) (v : UInt64) :
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

@[simp] theorem read64_write64_disjoint (m : Mem) (a b : UInt32) (v : UInt64)
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

@[simp] theorem read64_write32_disjoint (m : Mem) (a b v32 : UInt32)
    (hd : b.toNat + 8 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v32).read64 b = m.read64 b := by
  simp only [Mem.read64]
  rw [write32_bytes_of_disjoint m a v32 b.toNat (by omega),
      write32_bytes_of_disjoint m a v32 (b.toNat + 1) (by omega),
      write32_bytes_of_disjoint m a v32 (b.toNat + 2) (by omega),
      write32_bytes_of_disjoint m a v32 (b.toNat + 3) (by omega),
      write32_bytes_of_disjoint m a v32 (b.toNat + 4) (by omega),
      write32_bytes_of_disjoint m a v32 (b.toNat + 5) (by omega),
      write32_bytes_of_disjoint m a v32 (b.toNat + 6) (by omega),
      write32_bytes_of_disjoint m a v32 (b.toNat + 7) (by omega)]

@[simp] theorem read32_write32_same' (m : Mem) (a v : UInt32) :
    (m.write32 a v).read32 a = v := by
  simp only [Mem.read32, Mem.write32]
  have e1 : a.toNat + 1 ≠ a.toNat := by omega
  have e2 : a.toNat + 2 ≠ a.toNat := by omega
  have e3 : a.toNat + 3 ≠ a.toNat := by omega
  have e21 : a.toNat + 2 ≠ a.toNat + 1 := by omega
  have e31 : a.toNat + 3 ≠ a.toNat + 1 := by omega
  have e32 : a.toNat + 3 ≠ a.toNat + 2 := by omega
  simp only [e1, e2, e3, e21, e31, e32, if_true, if_false]
  bv_decide

@[simp] theorem read32_write64_disjoint (m : Mem) (a b : UInt32) (v : UInt64)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 8 ≤ b.toNat) :
    (m.write64 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write64_bytes_of_disjoint m a v b.toNat (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

@[simp] theorem read32_write32_disjoint' (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_of_disjoint m a v b.toNat (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

@[simp] theorem read64_write8_disjoint (m : Mem) (a b : UInt32) (v : UInt8)
    (h : a.toNat < b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    (m.write8 a v).read64 b = m.read64 b := by
  simp only [Mem.read64, Mem.write8]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] theorem read32_write8_disjoint (m : Mem) (a b : UInt32) (v : UInt8)
    (h : a.toNat < b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write8 a v).read32 b = m.read32 b := by
  simp only [Mem.read32, Mem.write8]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## The write loop, standalone

Counts the index at `fp+36` down from `c` to `0`, writing the digit
byte `'0' + (n / 10^(c-1-p)) % 10` at `out + p` on the way (the
value being peeled lives at `fp+24`). Exits by storing the digit
count (slot `fp+12`) into the result slot `fp+8` and `br 2` —
which surfaces as `.Break 0` at the loop-instruction level. -/

set_option maxHeartbeats 1600000 in
private theorem func6_write_loop (env : HostEnv Unit) (n : UInt64) (cap : UInt32)
    (c : Nat) (B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st2 : Store Unit) (fp out : UInt32)
    (hfp_hi : fp.toNat + 64 ≤ out.toNat)
    (hout_hi : out.toNat + 32 ≤ 1048576)
    (_hcap : cap.toNat ≤ 32) (_hcle : c ≤ cap.toNat) (hc20 : c ≤ 20)
    (hpg2 : st2.mem.pages = 17)
    (hidx : st2.mem.read32 (fp + 36) = UInt32.ofNat c)
    (hval : st2.mem.read64 (fp + 24) = n)
    (hcnt : st2.mem.read32 (fp + 12) = UInt32.ofNat c)
    (hpres : ∀ j : Nat, j < fp.toNat ∨ (fp.toNat + 64 ≤ j ∧ j < out.toNat) ∨
        out.toNat + 32 ≤ j →
      st2.mem.bytes j = B j)
    (hexit : ∀ (st' : Store Unit) (w5 w6 : Value),
      st'.mem.pages = 17 →
      st'.globals = st2.globals →
      st'.mem.read32 (fp + 8) = UInt32.ofNat c →
      (∀ p : Nat, p < c →
        st'.mem.bytes (out.toNat + p) = UInt8.ofNat (48 + n.toNat / 10 ^ (c - 1 - p) % 10)) →
      (∀ j : Nat, j < fp.toNat ∨ (fp.toNat + 64 ≤ j ∧ j < out.toNat) ∨
          out.toNat + 32 ≤ j →
        st'.mem.bytes j = B j) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 fp, w5, w6, Value.i32 0], values := [] })) :
    wp «module»
      (.loop 0 0 [
        .block 0 0 [
          .localGet 4, .load32 (36 : UInt32), .const (0 : UInt32), .gtU,
          .const (1 : UInt32), .and, .br_if 0,
          .localGet 4, .localGet 4, .load32 (12 : UInt32), .store32 (8 : UInt32),
          .br 2 ],
        .localGet 4, .localGet 4, .load32 (36 : UInt32), .const (1 : UInt32), .sub,
        .store32 (36 : UInt32),
        .localGet 4, .load64 (24 : UInt32), .constI64 (10 : UInt64), .remUI64, .wrapI64,
        .localSet 5,
        .localGet 4, .load32 (36 : UInt32), .localSet 6,
        .block 0 0 [
          .localGet 6, .localGet 2, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
          .localGet 1, .localGet 6, .add, .localGet 5, .const (48 : UInt32), .add,
          .store8 (0 : UInt32),
          .localGet 4, .localGet 4, .load64 (24 : UInt32), .constI64 (10 : UInt64),
          .divUI64, .store64 (24 : UInt32),
          .br 1 ]
      ] :: rest) Q st2
      { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
        locals := [Value.i32 fp, Value.i32 0, Value.i32 0, Value.i32 0],
        values := [] } env := by
  have t8 : (fp + 8).toNat = fp.toNat + 8 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have t12 : (fp + 12).toNat = fp.toNat + 12 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have t24 : (fp + 24).toNat = fp.toNat + 24 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have t36 : (fp + 36).toNat = fp.toNat + 36 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals = st2.globals ∧
      (∃ i : Nat, i ≤ c ∧
        st'.mem.read32 (fp + 36) = UInt32.ofNat i ∧
        st'.mem.read64 (fp + 24) = UInt64.ofNat (n.toNat / 10 ^ (c - i)) ∧
        st'.mem.read32 (fp + 12) = UInt32.ofNat c ∧
        (∀ p : Nat, i ≤ p → p < c → st'.mem.bytes (out.toNat + p) =
            UInt8.ofNat (48 + n.toNat / 10 ^ (c - 1 - p) % 10)) ∧
        (∀ j : Nat, j < fp.toNat ∨ (fp.toNat + 64 ≤ j ∧ j < out.toNat) ∨
            out.toNat + 32 ≤ j →
            st'.mem.bytes j = B j)) ∧
      (∃ w5 w6 : Value,
        s' = { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
               locals := [Value.i32 fp, w5, w6, Value.i32 0], values := [] }))
    (μ := fun st' _ => (st'.mem.read32 (fp + 36)).toNat)
  · -- entry invariant: `i = c`, value slot holds `n`
    refine ⟨hpg2, rfl, ⟨c, le_rfl, hidx, ?_, hcnt,
      fun p hp1 hp2 => absurd hp1 (by omega), hpres⟩, Value.i32 0, Value.i32 0, rfl⟩
    rw [Nat.sub_self, pow_zero, Nat.div_one, UInt64.ofNat_toNat]
    exact hval
  · -- step
    rintro st3 s3 ⟨hpg3, hgl3, ⟨i, hiC, hidx3, hval3, hcnt3, hdig3, hpres3⟩, w5, w6, rfl⟩
    have hfpB : fp.toNat + 64 ≤ 1114112 := by omega
    have g8 : ¬ (1114112 < fp.toNat + 8 + 4) := by omega
    have g12 : ¬ (1114112 < fp.toNat + 12 + 4) := by omega
    have g24 : ¬ (1114112 < fp.toNat + 24 + 8) := by omega
    have g36 : ¬ (1114112 < fp.toNat + 36 + 4) := by omega
    have q8 : fp.toNat ≤ 1114100 := by omega
    have q12 : fp.toNat ≤ 1114096 := by omega
    have q24 : fp.toNat ≤ 1114080 := by omega
    have q36 : fp.toNat ≤ 1114072 := by omega
    apply wp_block_cons
    wp_run
    simp [hpg3, hidx3, hcnt3, g8, g12, g24, g36]
    have hofi : (UInt32.ofNat i).toNat = i := by
      rw [UInt32.toNat_ofNat_of_lt']
      simp [UInt32.size]; omega
    by_cases hi0 : i = 0
    · -- exit: store the digit count into the result slot, `br 2`
      have hz : UInt32.ofNat i = 0 := by rw [hi0]; rfl
      simp [hz]
      apply hexit
      · simp [hpg3]
      · simpa using hgl3
      · rw [read32_write32_same']
      · intro p hp
        rw [read32_write32_bytes, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
        exact hdig3 p (by omega) hp
      · intro j hj
        rw [read32_write32_bytes, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
        exact hpres3 j hj
    · -- one more digit to write
      have hpos2 : (0 : UInt32) < UInt32.ofNat i := by
        rw [UInt32.lt_iff_toNat_lt, hofi]
        exact Nat.pos_of_ne_zero hi0
      simp [hpos2]
      apply wp_block_cons
      wp_run
      have him1 : UInt32.ofNat i - 1 = UInt32.ofNat (i - 1) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_sub_of_le _ _ (by
          rw [UInt32.le_iff_toNat_le]
          simpa [hofi] using Nat.pos_of_ne_zero hi0), hofi]
        rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        rfl
      have hofim1 : (UInt32.ofNat (i - 1)).toNat = i - 1 := by
        rw [UInt32.toNat_ofNat_of_lt']
        simp [UInt32.size]; omega
      have hguard : UInt32.ofNat (i - 1) < 32 := by
        rw [UInt32.lt_iff_toNat_lt, hofim1]
        simp; omega
      have haddr : (UInt32.ofNat (i - 1) + out).toNat = out.toNat + (i - 1) := by
        rw [UInt32.toNat_add, hofim1]
        have : (i - 1) + out.toNat < UInt32.size := by simp [UInt32.size]; omega
        rw [Nat.mod_eq_of_lt this]
        omega
      have hnb : ¬ (1114112 ≤ out.toNat + (i - 1)) := by omega
      have hd64 : n.toNat / 10 ^ (c - i) < 18446744073709551616 := by
        have h1 : n.toNat / 10 ^ (c - i) ≤ n.toNat := Nat.div_le_self _ _
        have h2 := UInt64.toNat_lt_size n
        simp [UInt64.size] at h2
        omega
      have hd : n.toNat / 10 ^ (c - i) % 18446744073709551616 % 10 % 4294967296 =
          n.toNat / 10 ^ (c - i) % 10 := by
        rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt (by omega)]
      have hrv : (st3.mem.write32 (fp + 36) (UInt32.ofNat (i - 1))).read64 (fp + 24) =
          UInt64.ofNat (n.toNat / 10 ^ (c - i)) := by
        rw [read64_write32_disjoint _ _ _ _ (by omega)]
        exact hval3
      simp [him1, hguard, hrv, hd, haddr, hpg3, hnb, g24]
      -- `hd`'s nested-mod shape makes every later `omega` pathologically
      -- slow (minutes each); drop it now that the simp consumed it.
      clear hd
      refine ⟨⟨hgl3, ⟨i - 1, by omega, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
      · rw [read32_write64_disjoint _ _ _ _ (by omega),
          read32_write8_disjoint _ _ _ _ (by omega), read32_write32_same']
      · rw [read64_write8_disjoint _ _ _ _ (by omega),
          read64_write32_disjoint _ _ _ _ (by omega), hval3]
        apply UInt64.toNat.inj
        have hsz : UInt64.size = 18446744073709551616 := rfl
        rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' (by omega),
          UInt64.toNat_ofNat_of_lt' (by
            have h1 : n.toNat / 10 ^ (c - (i - 1)) ≤ n.toNat / 10 ^ (c - i) := by
              rw [show c - (i - 1) = (c - i) + 1 from by omega, pow_succ,
                ← Nat.div_div_eq_div_mul]
              exact Nat.div_le_self _ _
            omega)]
        rw [show c - (i - 1) = (c - i) + 1 from by omega, pow_succ,
          ← Nat.div_div_eq_div_mul]
        rfl
      · rw [read32_write64_disjoint _ _ _ _ (by omega),
          read32_write8_disjoint _ _ _ _ (by omega),
          read32_write32_disjoint' _ _ _ _ (by omega), hcnt3]
      · intro p hp1 hp2
        rw [write64_bytes_of_disjoint _ _ _ _ (by omega)]
        by_cases hpe : p = i - 1
        · subst hpe
          rw [read8_write8_bytes, if_pos (by omega),
            show c - 1 - (i - 1) = c - i from by omega]
        · rw [read8_write8_bytes, if_neg (by omega),
            write32_bytes_of_disjoint _ _ _ _ (by omega),
            hdig3 p (by omega) hp2]
          exact (digit_add8 _ (Nat.mod_lt _ (by norm_num))).symm
      · intro j hj
        rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
          read8_write8_bytes, if_neg (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega)]
        exact hpres3 j (by omega)
      · rw [read32_write64_disjoint _ _ _ _ (by omega),
          read32_write8_disjoint _ _ _ _ (by omega), read32_write32_same', hofim1,
          Nat.mod_eq_of_lt (by omega)]
        omega

/-! ## The count loop, standalone

Counts the decimal digits of `n`: slot `fp+12` walks `1, 2, …` while
slot `fp+16` peels `n/10, n/100, …`. Exits with `.Break 0` (success:
`numDigits n.toNat ≤ cap`, via `br 2`) or `.Break 1` (capacity
exceeded, via `br_if 3`) at the loop-instruction level. -/

set_option maxHeartbeats 1600000 in
private theorem func6_count_loop (env : HostEnv Unit) (n : UInt64) (cap : UInt32)
    (B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st1 : Store Unit) (fp out : UInt32)
    (hfp_hi : fp.toNat + 64 ≤ 1048576)
    (hcap : cap.toNat ≤ 32)
    (hpg : st1.mem.pages = 17)
    (hslot12 : st1.mem.read32 (fp + 12) = 1)
    (hslot16 : st1.mem.read64 (fp + 16) = UInt64.ofNat (n.toNat / 10))
    (hpres : ∀ i : Nat, i < fp.toNat ∨ fp.toNat + 64 ≤ i → st1.mem.bytes i = B i)
    (hsucc : ∀ st' : Store Unit,
      st'.mem.pages = 17 →
      st'.globals = st1.globals →
      numDigits n.toNat ≤ cap.toNat →
      st'.mem.read32 (fp + 12) = UInt32.ofNat (numDigits n.toNat) →
      (∀ i : Nat, i < fp.toNat ∨ fp.toNat + 64 ≤ i → st'.mem.bytes i = B i) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 fp, Value.i32 0, Value.i32 0, Value.i32 0],
          values := [] }))
    (hfail : ∀ st' : Store Unit,
      st'.mem.pages = 17 →
      st'.globals = st1.globals →
      cap.toNat < numDigits n.toNat →
      (∀ i : Nat, i < fp.toNat ∨ fp.toNat + 64 ≤ i → st'.mem.bytes i = B i) →
      Q (.Break 1 st'
        { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 fp, Value.i32 0, Value.i32 0, Value.i32 0],
          values := [] })) :
    wp «module»
      (.loop 0 0 [
        .block 0 0 [
          .localGet 4, .load64 (16 : UInt32), .constI64 (0 : UInt64), .gtUI64,
          .const (1 : UInt32), .and, .br_if 0,
          .localGet 4, .load32 (12 : UInt32), .localGet 3, .gtS,
          .const (1 : UInt32), .and, .br_if 3,
          .br 2 ],
        .localGet 4, .localGet 4, .load32 (12 : UInt32), .const (1 : UInt32), .add,
        .store32 (12 : UInt32),
        .localGet 4, .localGet 4, .load64 (16 : UInt32), .constI64 (10 : UInt64),
        .divUI64, .store64 (16 : UInt32),
        .br 0 ] :: rest) Q st1
      { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
        locals := [Value.i32 fp, Value.i32 0, Value.i32 0, Value.i32 0],
        values := [] } env := by
  have t12 : (fp + 12).toNat = fp.toNat + 12 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have t16 : (fp + 16).toNat = fp.toNat + 16 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals = st1.globals ∧
      (∃ c : Nat, 1 ≤ c ∧ c ≤ numDigits n.toNat ∧
        st'.mem.read32 (fp + 12) = UInt32.ofNat c ∧
        st'.mem.read64 (fp + 16) = UInt64.ofNat (n.toNat / 10 ^ c)) ∧
      (∀ i : Nat, i < fp.toNat ∨ fp.toNat + 64 ≤ i → st'.mem.bytes i = B i) ∧
      s' = { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
             locals := [Value.i32 fp, Value.i32 0, Value.i32 0, Value.i32 0],
             values := [] })
    (μ := fun st' _ => (st'.mem.read64 (fp + 16)).toNat)
  · -- entry invariant: `c = 1`
    refine ⟨hpg, rfl, ⟨1, le_rfl, numDigits_pos n.toNat, by simpa using hslot12, ?_⟩,
      hpres, rfl⟩
    rw [pow_one]
    exact hslot16
  · -- step
    rintro st' s' ⟨hpg', hgl', ⟨c, hc1, hcL, hslot12', hslot16'⟩, hpres', rfl⟩
    have g12 : ¬ (1114112 < fp.toNat + 12 + 4) := by omega
    have g16 : ¬ (1114112 < fp.toNat + 16 + 8) := by omega
    have q12 : fp.toNat ≤ 1114096 := by omega
    have q16 : fp.toNat ≤ 1114088 := by omega
    apply wp_block_cons
    wp_run
    simp [hpg', hslot12', hslot16', g12, g16]
    have hvsz : n.toNat / 10 ^ c < 18446744073709551616 := by
      have h1 : n.toNat / 10 ^ c ≤ n.toNat := Nat.div_le_self _ _
      have h2 := UInt64.toNat_lt_size n
      simp [UInt64.size] at h2
      omega
    have hofv : (UInt64.ofNat (n.toNat / 10 ^ c)).toNat = n.toNat / 10 ^ c :=
      UInt64.toNat_ofNat_of_lt' hvsz
    by_cases hv : n.toNat / 10 ^ c = 0
    · -- count loop exits: `v = 0`, so `c` is exactly the digit count
      have hvz : UInt64.ofNat (n.toNat / 10 ^ c) = 0 := by
        apply UInt64.toNat.inj; rw [hofv, hv]; rfl
      simp [hvz]
      have hL : c = numDigits n.toNat := by
        have h10 : n.toNat < 10 ^ c := by
          by_contra hge
          have hb : 0 < 10 ^ c := Nat.pow_pos (by norm_num)
          have : 0 < n.toNat / 10 ^ c := Nat.div_pos (by omega) hb
          omega
        rcases Nat.eq_zero_or_pos n.toNat with h0 | h1
        · have : numDigits n.toNat = 1 := by rw [h0]; exact numDigits_lt_ten (by norm_num)
          omega
        · have hlow := ten_pow_numDigits_le n.toNat h1
          have hlt : 10 ^ (numDigits n.toNat - 1) < 10 ^ c := lt_of_le_of_lt hlow h10
          have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hlt
          omega
      have hc20 : c ≤ 20 := hL ▸ numDigits_toNat_le n
      have hofc : (UInt32.ofNat c).toNat = c := by
        rw [UInt32.toNat_ofNat_of_lt']
        simp [UInt32.size]; omega
      have hcmp : (cap.toInt32 < Int32.ofNat c) ↔ cap.toNat < c := by
        rw [show Int32.ofNat c = (UInt32.ofNat c).toInt32 from rfl,
            ltS_small cap (UInt32.ofNat c) (by omega) (by rw [hofc]; omega), hofc]
      by_cases hgt : cap.toNat < c
      · -- digit count exceeds `cap`: `br_if 3` fires
        simp [hcmp, hgt]
        exact hfail st' hpg' hgl' (by omega) hpres'
      · -- fits: `br 2`
        simp [hcmp, hgt]
        exact hsucc st' hpg' hgl' (by omega) (hL ▸ hslot12') hpres'
    · -- count loop continues
      have hpos : (0 : UInt64) < UInt64.ofNat (n.toNat / 10 ^ c) := by
        rw [UInt64.lt_iff_toNat_lt, hofv]
        exact Nat.pos_of_ne_zero hv
      simp [hpos]
      have h10c : 10 ^ c ≤ n.toNat := by
        by_contra hlt
        exact hv (Nat.div_eq_of_lt (by omega))
      have hclt : c < numDigits n.toNat := by
        have hup := lt_ten_pow_numDigits n.toNat
        have : 10 ^ c < 10 ^ numDigits n.toNat := by omega
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp this
      refine ⟨⟨hgl', ⟨c + 1, by omega, by omega, ?_, ?_⟩, ?_⟩, ?_⟩
      · rw [read32_write64_disjoint _ _ _ _ (by omega), read32_write32_same']
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt', UInt32.toNat_ofNat_of_lt']
        · simp
          have := numDigits_toNat_le n
          omega
        · have := numDigits_toNat_le n
          simp [UInt32.size]; omega
        · have := numDigits_toNat_le n
          simp [UInt32.size]; omega
      · rw [read64_write32_disjoint _ _ _ _ (by omega), hslot16']
        apply UInt64.toNat.inj
        rw [UInt64.toNat_div, hofv, UInt64.toNat_ofNat_of_lt' (by
          have h1 : n.toNat / 10 ^ (c + 1) ≤ n.toNat / 10 ^ c := by
            rw [pow_succ, ← Nat.div_div_eq_div_mul]
            exact Nat.div_le_self _ _
          have hsz : UInt64.size = 18446744073709551616 := rfl
          omega)]
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
        rfl
      · intro i hi
        rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
            write32_bytes_of_disjoint _ _ _ _ (by omega)]
        exact hpres' i hi
      · rw [read64_write32_disjoint _ _ _ _ (by omega), hslot16', hofv,
          Nat.mod_eq_of_lt hvsz]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hv) (by norm_num)

/-! ## `func6_spec`: prologue → count loop → success tail → write loop → epilogue -/

set_option maxHeartbeats 1600000 in
theorem func6_spec (env : HostEnv Unit) (st0 : Store Unit) (g out : UInt32)
    (n : UInt64) (cap : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg64 : 64 ≤ g.toNat) (hgout : g.toNat ≤ out.toNat)
    (hout : out.toNat + 32 ≤ 1048576)
    (hcap : cap.toNat ≤ 32) :
    TerminatesWith env «module» 6 st0 [.i32 cap, .i32 32, .i32 out, .i64 n]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 (if numDigits n.toNat ≤ cap.toNat
                    then UInt32.ofNat (numDigits n.toNat) else 4294967295)] ∧
        (numDigits n.toNat ≤ cap.toNat → HasDigitsAt st'.mem out.toNat n.toNat) ∧
        (∀ i : Nat, i < g.toNat - 64 ∨ (g.toNat ≤ i ∧ i < out.toNat) ∨
            out.toNat + 32 ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hfp : (g - 64).toNat = g.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le g 64 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 64 + 8).toNat = g.toNat - 64 + 8 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t12 : (g - 64 + 12).toNat = g.toNat - 64 + 12 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t16 : (g - 64 + 16).toNat = g.toNat - 64 + 16 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t24 : (g - 64 + 24).toNat = g.toNat - 64 + 24 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t36 : (g - 64 + 36).toNat = g.toNat - 64 + 36 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t40 : (g - 64 + 40).toNat = g.toNat - 64 + 40 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t52 : (g - 64 + 52).toNat = g.toNat - 64 + 52 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t56 : (g - 64 + 56).toNat = g.toNat - 64 + 56 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t60 : (g - 64 + 60).toNat = g.toNat - 64 + 60 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have hback : 64 + (g - 64) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hfp]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 64 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 64 + 12 + 4) := by omega
  have p16 : ¬ (1114112 < g.toNat - 64 + 16 + 8) := by omega
  have p24 : ¬ (1114112 < g.toNat - 64 + 24 + 8) := by omega
  have p36 : ¬ (1114112 < g.toNat - 64 + 36 + 4) := by omega
  have p40 : ¬ (1114112 < g.toNat - 64 + 40 + 8) := by omega
  have p52 : ¬ (1114112 < g.toNat - 64 + 52 + 4) := by omega
  have p56 : ¬ (1114112 < g.toNat - 64 + 56 + 4) := by omega
  have p60 : ¬ (1114112 < g.toNat - 64 + 60 + 4) := by omega
  have q8 : g.toNat - 64 ≤ 1114100 := by omega
  have q12 : g.toNat - 64 ≤ 1114096 := by omega
  have q16 : g.toNat - 64 ≤ 1114088 := by omega
  have q24 : g.toNat - 64 ≤ 1114080 := by omega
  have q36 : g.toNat - 64 ≤ 1114072 := by omega
  have q40 : g.toNat - 64 ≤ 1114064 := by omega
  have q52 : g.toNat - 64 ≤ 1114056 := by omega
  have q56 : g.toNat - 64 ≤ 1114052 := by omega
  have q60 : g.toNat - 64 ≤ 1114048 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i32, .i32, .i32], func6, [.i32]⟩) rfl
  unfold func6
  wp_run
  simp [hg, hpg, hfp, p12, p16, p40, p52, p56, p60]
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply func6_count_loop env n cap st0.mem.bytes _ (g - 64) out (by omega) hcap
  · -- pages after prologue
    simp [hpg]
  · -- slot 12 = 1 after prologue
    rw [read32_write64_disjoint _ _ _ _ (by omega), read32_write32_same']
  · -- slot 16 = n / 10 after prologue
    rw [read64_write64_same]
    apply UInt64.toNat.inj
    rw [UInt64.toNat_ofNat_of_lt']
    · exact UInt64.toNat_div n 10
    · have := UInt64.toNat_lt_size n
      have : n.toNat / 10 ≤ n.toNat := Nat.div_le_self _ _
      omega
  · -- bytes outside the frame untouched by the prologue
    intro i hi
    rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega)]
  · -- success: store value & digit count, run the write loop, epilogue
    intro st' hpg' hgl' hfits hslot12' hpres'
    simp only []
    wp_run
    simp [hpg', hfp, p12, p24, p36]
    apply func6_write_loop env n cap (numDigits n.toNat) st0.mem.bytes _ (g - 64) out
      (by omega) hout hcap hfits (numDigits_toNat_le n)
    · simp [hpg']
    · -- index slot = c
      rw [read32_write32_same', read32_write64_disjoint _ _ _ _ (by omega)]
      exact hslot12'
    · -- value slot = n
      rw [read64_write32_disjoint _ _ _ _ (by omega), read64_write64_same]
    · -- count slot = c
      rw [read32_write32_disjoint' _ _ _ _ (by omega),
          read32_write64_disjoint _ _ _ _ (by omega)]
      exact hslot12'
    · -- preservation through the two stores
      intro j hj
      rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega)]
      exact hpres' j (by omega)
    · -- write-loop exit: epilogue
      intro st2 w5 w6 hpg2 hgl2 hres hdig hpres2
      simp only []
      wp_run
      simp [hpg2, hres, hgl2, hgl', hback, hfp, q8,
        List.getElem?_set_self (by simpa using hglen)]
      refine ⟨fun h => absurd h (by omega), fun _ j hj => hdig j hj, ?_⟩
      intro i hi
      exact hpres2 i (by omega)
  · -- failure: store `-1`, epilogue
    intro st' hpg' hgl' hover hpres'
    simp only []
    wp_run
    simp [hpg', hgl', hback, hfp, p8,
      List.getElem?_set_self (by simpa using hglen)]
    refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), ?_⟩
    intro i hi
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hpres' i (by omega)

/-! ## `func5_spec`: the naive u64 wrapper

A 32-byte shadow-stack wrapper: spill `(n, out, outLen, cap)` into a
fresh frame, forward to `func6`, restore the stack pointer. -/

set_option maxHeartbeats 1600000 in
theorem func5_spec (env : HostEnv Unit) (st0 : Store Unit) (g out : UInt32)
    (n : UInt64) (cap : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg96 : 96 ≤ g.toNat) (hgout : g.toNat ≤ out.toNat)
    (hout : out.toNat + 32 ≤ 1048576)
    (hcap : cap.toNat ≤ 32) :
    TerminatesWith env «module» 5 st0 [.i32 cap, .i32 32, .i32 out, .i64 n]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 (if numDigits n.toNat ≤ cap.toNat
                    then UInt32.ofNat (numDigits n.toNat) else 4294967295)] ∧
        (numDigits n.toNat ≤ cap.toNat → HasDigitsAt st'.mem out.toNat n.toNat) ∧
        (∀ i : Nat, i < g.toNat - 96 ∨ (g.toNat ≤ i ∧ i < out.toNat) ∨
            out.toNat + 32 ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 32 + 8).toNat = g.toNat - 32 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t20 : (g - 32 + 20).toNat = g.toNat - 32 + 20 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t24 : (g - 32 + 24).toNat = g.toNat - 32 + 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t28 : (g - 32 + 28).toNat = g.toNat - 32 + 28 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 32 + (g - 32) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 32 + 8 + 8) := by omega
  have p20 : ¬ (1114112 < g.toNat - 32 + 20 + 4) := by omega
  have p24 : ¬ (1114112 < g.toNat - 32 + 24 + 4) := by omega
  have p28 : ¬ (1114112 < g.toNat - 32 + 28 + 4) := by omega
  have q8 : g.toNat - 32 ≤ 1114096 := by omega
  have q20 : g.toNat - 32 ≤ 1114088 := by omega
  have q24 : g.toNat - 32 ≤ 1114084 := by omega
  have q28 : g.toNat - 32 ≤ 1114080 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i32], func5, [.i32]⟩) rfl
  unfold func5
  wp_run
  simp [hg, hpg, hsub, p8, p20, p24, p28]
  apply wp_call_of_terminates (func6_spec env _ (g - 32) out n cap
    (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
    (by omega) (by omega) hout hcap)
  rintro st' vs ⟨hpg', hg', hrs, hdig, hpres⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  subst hrs
  wp_run
  simp [hg', hback, hpg', List.getElem?_set_self hglen']
  refine ⟨hdig, ?_⟩
  intro i hi
  have hstep := hpres i (by omega)
  rw [hstep]
  rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write64_bytes_of_disjoint _ _ _ _ (by omega)]

/-! ## `func7_spec`: the capacity clamp

`func7(v, lo, hi, loc)` clamps `v` (signed) into `[lo, hi]`, with a
(dead, since `lo ≤ hi` at the harness call site) panic branch. Pinned
to the harness arguments `lo = 0`, `hi = 32`, `loc = 1049032`. -/

/-- A `u32` whose signed value lies in `[0, 32]` has `toNat ≤ 32`. -/
private theorem toNat_le_32_of_signed_range (cap : UInt32)
    (h0 : ¬ cap.toInt32 < (0 : Int32)) (h32 : ¬ (32 : Int32) < cap.toInt32) :
    cap.toNat ≤ 32 := by
  rw [Int32.lt_iff_toInt_lt] at h0 h32
  by_cases hsm : cap.toNat < 2147483648
  · rw [toInt32_toInt_small cap hsm] at h32
    rw [show ((32 : Int32)).toInt = 32 from by decide] at h32
    omega
  · exfalso
    apply h0
    have hb : cap.toNat < 4294967296 := by
      have := UInt32.toNat_lt cap; simpa [UInt32.size] using this
    have he : cap.toInt32.toInt = (cap.toNat : Int) - 4294967296 := by
      rw [show cap.toInt32.toInt = cap.toBitVec.toInt from rfl,
        BitVec.toInt_eq_toNat_bmod,
        show cap.toBitVec.toNat = cap.toNat from rfl, Int.bmod]
      simp
      omega
    rw [he, show ((0 : Int32)).toInt = 0 from rfl]
    omega

set_option maxHeartbeats 1600000 in
theorem func7_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (cap : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg96 : 96 ≤ g.toNat) (hghi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 7 st0 [.i32 1049032, .i32 32, .i32 0, .i32 cap]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        (∃ r : UInt32, rs = [.i32 r] ∧ r.toNat ≤ 32) ∧
        (∀ i : Nat, i < g.toNat - 96 ∨ g.toNat ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 96).toNat = g.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le g 96 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t12 : (g - 96 + 12).toNat = g.toNat - 96 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t76 : (g - 96 + 76).toNat = g.toNat - 96 + 76 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t80 : (g - 96 + 80).toNat = g.toNat - 96 + 80 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t84 : (g - 96 + 84).toNat = g.toNat - 96 + 84 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t88 : (g - 96 + 88).toNat = g.toNat - 96 + 88 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 96 + (g - 96) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p12 : ¬ (1114112 < g.toNat - 96 + 12 + 4) := by omega
  have p76 : ¬ (1114112 < g.toNat - 96 + 76 + 4) := by omega
  have p80 : ¬ (1114112 < g.toNat - 96 + 80 + 4) := by omega
  have p84 : ¬ (1114112 < g.toNat - 96 + 84 + 4) := by omega
  have p88 : ¬ (1114112 < g.toNat - 96 + 88 + 4) := by omega
  have q12 : g.toNat - 96 ≤ 1114096 := by omega
  have q76 : g.toNat - 96 ≤ 1114032 := by omega
  have q80 : g.toNat - 96 ≤ 1114028 := by omega
  have q84 : g.toNat - 96 ≤ 1114024 := by omega
  have q88 : g.toNat - 96 ≤ 1114020 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32], func7, [.i32]⟩) rfl
  unfold func7
  wp_run
  simp [hg, hpg, hsub, p76, p80, p84, p88]
  apply wp_block_cons
  wp_run
  simp
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  by_cases hlt : cap.toInt32 < (0 : Int32)
  · -- cap <s 0: clamp to 0
    simp [hlt, hback, hpg, hsub, p12, List.getElem?_set_self hglen]
    intro i hi
    repeat rw [if_neg (by omega)]
  · by_cases hgt : (32 : Int32) < cap.toInt32
    · -- cap >s 32: clamp to 32
      simp [hlt, hgt, hback, hpg, hsub, p12, List.getElem?_set_self hglen]
      intro i hi
      repeat rw [if_neg (by omega)]
    · -- in range: keep cap
      simp [hlt, hgt, hback, hpg, hsub, p12, List.getElem?_set_self hglen]
      refine ⟨toNat_le_32_of_signed_range cap hlt hgt, ?_⟩
      intro i hi
      repeat rw [if_neg (by omega)]

end Project.Itoa.Proofs
