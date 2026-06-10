import Project.ReverseInplace.Program

/-!
# Specification for `reverse_inplace`

The exported `check(seed, len)` runs two in-place reversers on
identically-seeded buffers — one via the swap-from-both-ends pattern,
one via copy-reversed-into-scratch-then-back — and traps via
`unreachable` iff they disagree on any element. Proving the wasm
export terminates without trapping for every input is therefore the
same as proving the two reversers compute the same permutation on
every seeded buffer.

At `opt-level=0` the live call graph is

```
func8 (exported `check` wrapper, frame 1048560)
  └─ func6 (seed both buffers, reverse each, compare; frame 1048224)
       ├─ func7 (checked slice constructor wrapper, frame 1048192)
       │    └─ func1 (slice ctor, frame 1048160)
       │         └─ func0 (range check `0 ≤ count ≤ 32`, frame 1048112)
       ├─ func2 (swap-from-both-ends reverse; frame 1048192)
       └─ func3 (copy-reversed-into-scratch-then-back; frame 1048064)
```

Every function carries the unoptimized shadow-stack discipline: the
prologue claims a frame below `global 0` and spills every intermediate
to linear memory at fixed frame offsets, and the epilogue restores
`global 0`. With the canonical instantiation (`global 0 = 1048576`,
17 pages of memory) all frames are in bounds, and the two 128-byte
buffers `A`/`B` live in `func6`'s frame at `1048256` / `1048384`.
The Rust-level slice bounds checks are live `br_if`s guarding `call 61`
panic paths; they always pass because the element count is clamped to
`min(len, 32)`.
-/

namespace Project.ReverseInplace.Spec

open Wasm

set_option maxRecDepth 1048576

/-! ## Top spec -/

/-- The exported `check` terminates without trapping (and returns no
values) on every `(seed, len)` input, when run from the module's
canonical instantiation.

The `initial = «module».initialStore` hypothesis is load-bearing: the
unoptimized body spills everything to the shadow stack below
`global 0 = 1048576`, so under an adversarial store (e.g.
`mem.pages = 0`) the very first spill would trap. The canonical store
provides 17 pages (`1114112` bytes), so every frame access is in
bounds.

Informal spec:
For any `seed len : UInt32`, the wasm export `check` terminates and
leaves an empty value stack. Termination-without-trapping is the whole
content of the spec — the body traps via `unreachable` iff the
swap-from-both-ends and copy-reversed reversers disagree on some
element, so this property *is* the equivalence claim between the two
implementations. -/
@[spec_of "rust-exported" "reverse_inplace::check"]
def CheckSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (seed len : UInt32),
    initial = «module».initialStore →
    -- Args in stack order (top first): the Wasm caller pushes `seed`
    -- then `len`, and `run` reverses on entry to make local 0 = seed.
    TerminatesWith env «module» 8 initial [.i32 len, .i32 seed]
      (fun _ rs => rs = [])

/-! ## Memory framing lemmas

The proof needs read-after-write algebra over the function-model
`Mem`: a 32-bit read sees the value of a same-address 32-bit write,
and is unchanged by a disjoint write or fill. The disjointness side
conditions are stated on `toNat` byte ranges; for the (many)
concrete-numeral frame slots `simp` discharges them on its own, while
the symbolic buffer-cell addresses get explicit `omega` discharges. -/

/-- A 32-bit read sees the value of a same-address 32-bit write. -/
@[simp] theorem read32_write32_same (m : Mem) (a v : UInt32) :
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

/-- A 32-bit read is unaffected by a 32-bit write to a disjoint 4-byte
range. -/
@[simp] theorem read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_of_disjoint m a v b.toNat (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

/-- A byte outside a `fill` range is unchanged. -/
theorem fill_bytes_of_disjoint (m : Mem) (off len : Nat) (val : UInt8) (i : Nat)
    (h : i < off ∨ off + len ≤ i) :
    (m.fill off len val).bytes i = m.bytes i := by
  simp only [Mem.fill]
  have : ¬ (off ≤ i ∧ i < off + len) := by omega
  simp [this]

/-- A 32-bit read is unaffected by a `fill` over a disjoint range. -/
theorem read32_fill_disjoint (m : Mem) (off len : Nat) (val : UInt8) (b : UInt32)
    (h : b.toNat + 4 ≤ off ∨ off + len ≤ b.toNat) :
    (m.fill off len val).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [fill_bytes_of_disjoint m off len val b.toNat (by omega),
      fill_bytes_of_disjoint m off len val (b.toNat + 1) (by omega),
      fill_bytes_of_disjoint m off len val (b.toNat + 2) (by omega),
      fill_bytes_of_disjoint m off len val (b.toNat + 3) (by omega)]

/-- A 32-bit read depends only on its four bytes: if two memories agree
on `[a, a+4)` they agree on `read32 a`. -/
theorem read32_eq_of_bytes (m m' : Mem) (a : UInt32)
    (h0 : m'.bytes a.toNat = m.bytes a.toNat)
    (h1 : m'.bytes (a.toNat + 1) = m.bytes (a.toNat + 1))
    (h2 : m'.bytes (a.toNat + 2) = m.bytes (a.toNat + 2))
    (h3 : m'.bytes (a.toNat + 3) = m.bytes (a.toNat + 3)) :
    m'.read32 a = m.read32 a := by
  simp only [Mem.read32, h0, h1, h2, h3]

@[simp] theorem write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

@[simp] theorem fill_pages (m : Mem) (off len : Nat) (val : UInt8) :
    (m.fill off len val).pages = m.pages := rfl

/-! ## UInt32 ↔ Nat bridges for buffer-cell addresses -/

/-- The `toNat` of an in-buffer pointer `base + 4*k` is exactly
`base.toNat + 4*k` (no `UInt32` wraparound), given the 4-byte cell at
that offset fits in the 17-page memory. -/
theorem toNat_base_add (base : UInt32) (k : Nat)
    (hk : base.toNat + 4 * k + 4 ≤ 1114112) :
    (base + 4 * UInt32.ofNat k).toNat = base.toNat + 4 * k := by
  simp [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat]
  omega

/-- A left shift by the constant 2 is multiplication by 4. -/
theorem shl_two (x : UInt32) : x <<< (2 : UInt32) = 4 * x := by
  bv_decide

/-- Discharge a byte-preservation goal
`(… stack of write32/fill …).bytes j = m.bytes j` by peeling the
writes one at a time; each side condition is concrete-vs-`omega`
disjointness (using whatever range facts about `j` are in context). -/
macro "peel_writes" : tactic =>
  `(tactic| (repeat first
      | rw [write32_bytes_of_disjoint _ _ _ _ (by simp; omega)]
      | rw [fill_bytes_of_disjoint _ _ _ _ _ (by simp; omega)]))

/-- Resolve a `read32` through a stack of `write32`/`fill`s: a
same-address write returns its value, a disjoint write is skipped
(side condition by `simp`-normalizing `toNat` and `omega`, which can
use whatever range facts are in context). -/
macro "peel_reads" : tactic =>
  `(tactic| (repeat first
      | rw [read32_write32_same]
      | rw [read32_write32_disjoint _ _ _ _ (by simp; omega)]
      | rw [read32_fill_disjoint _ _ _ _ _ (by simp; omega)]))

/-- Decide the index checks, literal address arithmetic and
literal-condition `if`s that `wp_run` leaves behind, without touching
anything symbolic. -/
macro "wp_norm" : tactic =>
  `(tactic| simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceMul,
      UInt32.reduceToNat, UInt32.reduceAdd, gt_iff_lt, reduceIte])

/-! ## A store-specific `call` rule

`wp_call_cons` consumes a `FuncSpec`, which quantifies over *all*
initial stores. That is unusable here: every function in the live call
graph spills to linear memory and traps on a too-small store, so no
total `FuncSpec` exists for any of them. We step `call` against a
`TerminatesWith` *at the concrete current store* instead
(`wp_call_at` is the interpreter-side core of this). -/

private theorem wp_call_of_terminates {α : Type} {env : HostEnv α} {m : Module}
    {id : Nat} {Q : Assertion α} {rest : Program} {st : Store α} {s : Locals}
    {P : Store α → List Value → Prop}
    (h : TerminatesWith env m id st s.values P)
    (hPost : ∀ st' vs, P st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env :=
  wp_call_at h hPost

/-! ## The slice-constructor chain: `func7` → `func1` → `func0`

`check` builds each `&mut [u32]` slice through a chain of three
wrappers. `func0` performs the live range check `0 ≤ count ∧
count ≤ 32` (panicking via `call 58` otherwise) and returns the
`(ptr, len)` pair through an out-pointer; `func1` and `func7` shuffle
it outward through their own frames. On the live path `count ≤ 32`
always holds, so the chain is a glorified identity: it writes
`(buf, count)` to the caller's out-slot and touches nothing above
`1048224` except that 8-byte slot. -/

/-- `func0`: the live `0 ≤ count ≤ 32` range check. Called (on the live
path) with out-pointer `1048168`, `start = 0`, `end = count`,
`ptr = buf`, `cap = 32` and a panic-location pointer. Writes
`(buf, count)` to `[1048168, 1048176)`, clobbers only its own frame
`[1048112, 1048160)` besides that, and restores `global 0`. -/
theorem func0_at (env : HostEnv Unit) (st0 : Store Unit) (buf count loc : UInt32)
    (hcount : count.toNat ≤ 32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048160, .i32 1050149, .i32 1050160]) :
    TerminatesWith env «module» 0 st0
      [.i32 loc, .i32 32, .i32 buf, .i32 count, .i32 0, .i32 1048168]
      (fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048160, .i32 1050149, .i32 1050160] ∧
        st'.mem.read32 1048168 = buf ∧ st'.mem.read32 1048172 = count ∧
        ∀ j : Nat, j < 1048112 ∨ 1048176 ≤ j → st'.mem.bytes j = st0.mem.bytes j) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32, .i32, .i32], [.i32, .i32, .i32], func0, []⟩) rfl
  unfold func0
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  apply wp_block_cons   -- A: success tail after it
  apply wp_block_cons   -- B
  apply wp_block_cons   -- C
  apply wp_block_cons   -- D: the two range tests
  wp_run
  have hc32 : count ≤ 32 := by
    rw [UInt32.le_iff_toNat_le]; simpa using hcount
  simp [hpg, hc32]
  intro j hj
  peel_writes

/-- `func1`: forwards the range-checked `(buf, count)` pair from
`func0`'s out-slot to its own caller's out-slot at `1048192`. -/
theorem func1_at (env : HostEnv Unit) (st0 : Store Unit) (buf count loc : UInt32)
    (hcount : count.toNat ≤ 32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048192, .i32 1050149, .i32 1050160]) :
    TerminatesWith env «module» 1 st0
      [.i32 loc, .i32 32, .i32 buf, .i32 count, .i32 1048192]
      (fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048192, .i32 1050149, .i32 1050160] ∧
        st'.mem.read32 1048192 = buf ∧ st'.mem.read32 1048196 = count ∧
        ∀ j : Nat, j < 1048112 ∨ 1048200 ≤ j → st'.mem.bytes j = st0.mem.bytes j) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32, .i32], [.i32, .i32, .i32], func1, []⟩) rfl
  unfold func1
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  refine wp_call_of_terminates
    (func0_at env _ buf count loc hcount (by simp [hpg]) (by simp)) ?_
  rintro st1 vs1 ⟨rfl, hpg1, hgl1, hrb, hrc, hbytes⟩
  wp_run
  simp [hgl1, hpg1, hrb, hrc]
  intro j hj
  peel_writes
  rw [hbytes j (by omega)]
  peel_writes

/-- `func7`: the outermost slice-constructor wrapper, called by `check`
with a symbolic out-pointer (`1048232` for buffer `A`, `1048240` for
`B`). Writes `(buf, count)` to `[out, out+8)`, clobbers only
`[1048112, 1048224)` besides that, and restores `global 0 = 1048224`. -/
theorem func7_at (env : HostEnv Unit) (st0 : Store Unit) (out buf count loc : UInt32)
    (hcount : count.toNat ≤ 32)
    (hout : 1048224 ≤ out.toNat ∧ out.toNat + 8 ≤ 1114112)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048224, .i32 1050149, .i32 1050160]) :
    TerminatesWith env «module» 7 st0
      [.i32 loc, .i32 count, .i32 buf, .i32 out]
      (fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048224, .i32 1050149, .i32 1050160] ∧
        st'.mem.read32 out = buf ∧ st'.mem.read32 (out + 4) = count ∧
        ∀ j : Nat, j < 1048112 ∨ 1048224 ≤ j →
          j < out.toNat ∨ out.toNat + 8 ≤ j →
          st'.mem.bytes j = st0.mem.bytes j) := by
  have hout4 : (out + 4).toNat = out.toNat + 4 := by
    rw [UInt32.toNat_add]
    simp only [show (4 : UInt32).toNat = 4 from rfl]
    omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32, .i32], func7, []⟩) rfl
  unfold func7
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  refine wp_call_of_terminates
    (func1_at env _ buf count loc hcount (by simp [hpg]) (by simp)) ?_
  rintro st1 vs1 ⟨rfl, hpg1, hgl1, hrb, hrc, hbytes⟩
  wp_run
  simp [hgl1, hpg1, hrb, hrc]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [read32_write32_disjoint _ _ _ _ (Or.inr (by simp only [hout4]; omega)),
        read32_write32_same]
  · intro j hj1 hj2
    rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by simp only [hout4]; omega),
        hbytes j (by omega)]
    peel_writes

/-! ## `func2`: swap-from-both-ends reverse

`func2(ptr, count)` reverses the `count` 32-bit cells at `ptr` in
place with two pointers walking inward, all loop state living in its
shadow-stack frame `[1048192, 1048224)`: the ascending index `i` at
`1048196`, the descending index `j` at `1048200`, and the two swap
temporaries at `1048216`/`1048220`. Each buffer access re-checks
`index < count` (a live Rust bounds check guarding a `call 61` panic);
the checks always pass because `i < j ≤ count - 1`. On the live path
`ptr = 1048256` (buffer `A` in `func6`'s frame). -/

/-- After `s` swap iterations of the two-pointer reversal of a length-`n`
buffer, cell `i` holds the original cell `mirrorIdx n s i`: the mirror
`n-1-i` once `i` falls into the already-swapped prefix `[0,s)` or suffix
`[n-s, n)`, and its original self in the still-untouched middle. -/
def mirrorIdx (n s i : Nat) : Nat := if i < s ∨ n - s ≤ i then n - 1 - i else i

set_option maxHeartbeats 1000000 in
theorem func2_at (env : HostEnv Unit) (st0 : Store Unit) (count : UInt32)
    (hcount : count.toNat ≤ 32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048224, .i32 1050149, .i32 1050160]) :
    TerminatesWith env «module» 2 st0 [.i32 count, .i32 1048256]
      (fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048224, .i32 1050149, .i32 1050160] ∧
        (∀ i, i < count.toNat →
          st'.mem.read32 (1048256 + 4 * UInt32.ofNat i)
            = st0.mem.read32 (1048256 + 4 * UInt32.ofNat (count.toNat - 1 - i))) ∧
        ∀ j : Nat, (j < 1048192 ∨ 1048224 ≤ j) →
          (j < 1048256 ∨ 1048256 + 4 * count.toNat ≤ j) →
          st'.mem.bytes j = st0.mem.bytes j) := by
  have hofNat : ∀ k : Nat, k ≤ 33 → (UInt32.ofNat k).toNat = k := fun k hk => by
    simp; omega
  have hcell : ∀ k : Nat, k ≤ 32 →
      ((1048256 : UInt32) + 4 * UInt32.ofNat k).toNat = 1048256 + 4 * k := fun k hk =>
    toNat_base_add _ _ (by simp; omega)
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32, .i32, .i32, .i32, .i32, .i32], func2, []⟩) rfl
  unfold func2
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  apply wp_block_cons   -- OUTER
  wp_run
  by_cases hc0 : count = 0
  · -- `count = 0`: the early `br_if 0` exits; nothing was reversed
    -- because there is nothing to reverse.
    subst hc0
    simp [hpg]
    intro j _ _
    peel_writes
  · -- `count ≥ 1`: seed `i = 0`, `j = count - 1` and run the swap loop.
    have hc1 : 1 ≤ count.toNat := by
      rcases Nat.eq_zero_or_pos count.toNat with h | h
      · exact absurd (UInt32.toNat.inj (by rw [h]; rfl)) hc0
      · exact h
    simp [hc0, hpg]
    have hj0 : count - 1 = UInt32.ofNat (count.toNat - 1 - 0) := by
      apply UInt32.toNat.inj
      rw [UInt32.toNat_sub, hofNat (count.toNat - 1 - 0) (by omega)]
      simp only [show (1 : UInt32).toNat = 1 from rfl]
      omega
    apply wp_loop_cons
      (Inv := fun st' s' => ∃ (t : Nat) (w3 w4 w5 w6 w7 w8 : Value),
        2 * t ≤ count.toNat ∧
        s' = { params := [.i32 1048256, .i32 count],
               locals := [.i32 1048192, w3, w4, w5, w6, w7, w8],
               values := [] } ∧
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048192, .i32 1050149, .i32 1050160] ∧
        st'.mem.read32 1048196 = UInt32.ofNat t ∧
        st'.mem.read32 1048200 = UInt32.ofNat (count.toNat - 1 - t) ∧
        (∀ i, i < count.toNat →
          st'.mem.read32 (1048256 + 4 * UInt32.ofNat i)
            = st0.mem.read32 (1048256 + 4 * UInt32.ofNat (mirrorIdx count.toNat t i))) ∧
        (∀ j : Nat, (j < 1048192 ∨ 1048224 ≤ j) →
          (j < 1048256 ∨ 1048256 + 4 * count.toNat ≤ j) →
          st'.mem.bytes j = st0.mem.bytes j))
      (μ := fun st' _ => (st'.mem.read32 1048200).toNat)
    · -- invariant on entry (`t = 0`)
      refine ⟨0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, by omega, rfl,
        by simp [hpg], rfl, by simp, by rw [← hj0]; simp, ?_, ?_⟩
      · intro i hi
        have : mirrorIdx count.toNat 0 i = i := by
          simp only [mirrorIdx]; rw [if_neg (by omega)]
        rw [this]
        have hci := hcell i (by omega)
        iterate 5 rw [read32_write32_disjoint _ _ _ _ (by simp [hci]; omega)]
      · intro j hj1 hj2
        peel_writes
    · -- one iteration preserves the invariant / establishes the post
      rintro st s ⟨t, w3, w4, w5, w6, w7, w8, ht, rfl, hpg', hgl', hI, hJ, hbuf, hfr⟩
      have htn : t ≤ 32 := by omega
      have hmt : count.toNat - 1 - t ≤ 32 := by omega
      have hIt : (UInt32.ofNat t).toNat = t := hofNat t (by omega)
      have hJt : (UInt32.ofNat (count.toNat - 1 - t)).toNat = count.toNat - 1 - t :=
        hofNat _ (by omega)
      have hcellt : ((1048256 : UInt32) + 4 * UInt32.ofNat t).toNat = 1048256 + 4 * t :=
        hcell t htn
      have hcellj : ((1048256 : UInt32) + 4 * UInt32.ofNat (count.toNat - 1 - t)).toNat
          = 1048256 + 4 * (count.toNat - 1 - t) := hcell _ hmt
      wp_run
      simp [hI, hJ, hpg']
      by_cases hcond : (UInt32.ofNat t : UInt32) < UInt32.ofNat (count.toNat - 1 - t)
      · -- continue: swap cells `t` and `count-1-t`, re-establish at `t+1`
        have hlt : 2 * t + 2 ≤ count.toNat := by
          have := UInt32.lt_iff_toNat_lt.mp hcond
          rw [hIt, hJt] at this
          omega
        have hiltc : (UInt32.ofNat t : UInt32) < count := by
          rw [UInt32.lt_iff_toNat_lt, hIt]; omega
        have hjltc : (UInt32.ofNat (count.toNat - 1 - t) : UInt32) < count := by
          rw [UInt32.lt_iff_toNat_lt, hJt]; omega
        have haddrt : UInt32.ofNat t <<< (2 : UInt32) + 1048256
            = 1048256 + 4 * UInt32.ofNat t := by
          rw [shl_two]; exact UInt32.add_comm _ _
        have haddrj : UInt32.ofNat (count.toNat - 1 - t) <<< (2 : UInt32) + 1048256
            = 1048256 + 4 * UInt32.ofNat (count.toNat - 1 - t) := by
          rw [shl_two]; exact UInt32.add_comm _ _
        -- arithmetic battery: in-bounds and slot-disjointness facts for the
        -- two buffer cells touched this iteration, in the `Nat`-normalized
        -- shapes `simp` produces.
        have hle1 : 1048256 + 4 * t ≤ 1114108 := by omega
        have hle2 : 1048256 + 4 * (count.toNat - 1 - t) ≤ 1114108 := by omega
        have hmod1 : (1048256 + 4 * t) % 4294967296 = 1048256 + 4 * t := by omega
        have hmod2 : (1048256 + 4 * (count.toNat - 1 - t)) % 4294967296
            = 1048256 + 4 * (count.toNat - 1 - t) := by omega
        have hd1 : 1048200 ≤ 1048256 + 4 * t := by omega
        have hd2 : 1048204 ≤ 1048256 + 4 * t := by omega
        have hd3 : 1048200 ≤ 1048256 + 4 * (count.toNat - 1 - t) := by omega
        have hd4 : 1048204 ≤ 1048256 + 4 * (count.toNat - 1 - t) := by omega
        have hd5 : 1048220 ≤ 1048256 + 4 * t := by omega
        have hd6 : 1048220 ≤ 1048256 + 4 * (count.toNat - 1 - t) := by omega
        have hd7 : 1048224 ≤ 1048256 + 4 * t := by omega
        have hd8 : 1048224 ≤ 1048256 + 4 * (count.toNat - 1 - t) := by omega
        simp only [hcond, if_pos]
        norm_num
        apply wp_block_cons -- b1
        apply wp_block_cons -- b2
        apply wp_block_cons -- b3
        apply wp_block_cons -- b4
        apply wp_block_cons -- b5
        apply wp_block_cons -- b6
        apply wp_block_cons -- b7
        wp_run
        simp [hiltc, hjltc, hpg', hI, hJ, haddrt, haddrj, hcellt, hcellj,
          hle1, hle2, hd1, hd2, hd3, hd4, hd6]
        refine ⟨⟨t + 1, by omega, hgl', ?_, ?_, ?_, ?_⟩, ?_⟩
        · -- `i` slot: `1 + t = t + 1` on the UInt32 view
          apply UInt32.toNat.inj
          rw [UInt32.toNat_add, hIt, hofNat (t + 1) (by omega)]
          simp; omega
        · -- `j` slot: `(count-1-t) - 1 = count-1-(t+1)` on the UInt32 view
          apply UInt32.toNat.inj
          rw [UInt32.toNat_sub, hJt, hofNat (count.toNat - 1 - (t + 1)) (by omega)]
          simp; omega
        · -- buffer contents after the two swaps = the (t+1)-partial reversal
          intro i hi
          have hci : ((1048256 : UInt32) + 4 * UInt32.ofNat i).toNat = 1048256 + 4 * i :=
            hcell i (by omega)
          by_cases hit : i = t
          · subst hit
            peel_reads
            have hm : mirrorIdx count.toNat (i + 1) i = count.toNat - 1 - i := by
              simp only [mirrorIdx]; rw [if_pos (by omega)]
            rw [hm, hbuf (count.toNat - 1 - i) (by omega)]
            have hm2 : mirrorIdx count.toNat i (count.toNat - 1 - i) = count.toNat - 1 - i := by
              simp only [mirrorIdx]; rw [if_neg (by omega)]
            rw [hm2]
          · by_cases hic : i = count.toNat - 1 - t
            · subst hic
              peel_reads
              have hm : mirrorIdx count.toNat (t + 1) (count.toNat - 1 - t) = t := by
                simp only [mirrorIdx]; rw [if_pos (by omega)]; omega
              rw [hm, hbuf t (by omega)]
              have hm2 : mirrorIdx count.toNat t t = t := by
                simp only [mirrorIdx]; rw [if_neg (by omega)]
              rw [hm2]
            · peel_reads
              rw [hbuf i hi]
              have hm : mirrorIdx count.toNat (t + 1) i = mirrorIdx count.toNat t i := by
                simp only [mirrorIdx]
                by_cases h1 : i < t ∨ count.toNat - t ≤ i
                · rw [if_pos h1, if_pos (by omega)]
                · rw [if_neg h1, if_neg (by omega)]
              rw [hm]
        · -- bytes outside the frame and the buffer are untouched
          intro j hj1 hj2
          peel_writes
          exact hfr j hj1 hj2
        · -- the `j` slot strictly decreases: the measure shrinks
          rw [UInt32.toNat_sub, hJt]
          simp; omega
      · -- exit: `i ≥ j`, the buffer is fully reversed
        have hge : count.toNat ≤ 2 * t + 1 := by
          rcases Nat.lt_or_ge (2 * t + 1) count.toNat with h | h
          · exact absurd (UInt32.lt_iff_toNat_lt.mpr (by rw [hIt, hJt]; omega)) hcond
          · exact h
        simp [hcond, hgl']
        refine ⟨fun i hi => ?_, hfr⟩
        have : mirrorIdx count.toNat t i = count.toNat - 1 - i := by
          simp only [mirrorIdx]; split
          · rfl
          · omega
        rw [← this]
        exact hbuf i hi

/-! ## `func3`: copy-reversed-into-scratch-then-back

`func3(ptr, count)` reverses the `count` 32-bit cells at `ptr` by
copying them in reverse order into a 128-byte scratch buffer inside
its own shadow-stack frame (`[1048076, 1048204)`), then copying the
scratch back over the buffer. Loop state again lives in frame slots:
the phase-1 index at `1048204`, the phase-2 index at `1048208`. The
live Rust bounds checks (`index < count` on the buffer,
`index < 32` on the scratch) always pass because `count ≤ 32`. On the
live path `ptr = 1048384` (buffer `B` in `func6`'s frame). -/

set_option maxHeartbeats 2000000 in
theorem func3_at (env : HostEnv Unit) (st0 : Store Unit) (count : UInt32)
    (hcount : count.toNat ≤ 32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048224, .i32 1050149, .i32 1050160]) :
    TerminatesWith env «module» 3 st0 [.i32 count, .i32 1048384]
      (fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048224, .i32 1050149, .i32 1050160] ∧
        (∀ i, i < count.toNat →
          st'.mem.read32 (1048384 + 4 * UInt32.ofNat i)
            = st0.mem.read32 (1048384 + 4 * UInt32.ofNat (count.toNat - 1 - i))) ∧
        ∀ j : Nat, (j < 1048064 ∨ 1048224 ≤ j) →
          (j < 1048384 ∨ 1048384 + 4 * count.toNat ≤ j) →
          st'.mem.bytes j = st0.mem.bytes j) := by
  have hofNat : ∀ k : Nat, k ≤ 33 → (UInt32.ofNat k).toNat = k := fun k hk => by
    simp; omega
  have hcellB : ∀ k : Nat, k ≤ 32 →
      ((1048384 : UInt32) + 4 * UInt32.ofNat k).toNat = 1048384 + 4 * k := fun k hk =>
    toNat_base_add _ _ (by simp; omega)
  have hcellS : ∀ k : Nat, k ≤ 32 →
      ((1048076 : UInt32) + 4 * UInt32.ofNat k).toNat = 1048076 + 4 * k := fun k hk =>
    toNat_base_add _ _ (by simp; omega)
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32],
           [.i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32], func3, []⟩) rfl
  unfold func3
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  apply wp_block_cons   -- OUTER
  -- Phase 1: copy `ptr[count-1-k]` into `scratch[k]` for `k = 0 .. count-1`.
  apply wp_loop_cons
    (Inv := fun st' s' => ∃ (k : Nat) (w3 w4 w5 w6 w7 w8 w9 w10 : Value),
      k ≤ count.toNat ∧
      s' = { params := [.i32 1048384, .i32 count],
             locals := [.i32 1048064, w3, w4, w5, w6, w7, w8, w9, w10],
             values := [] } ∧
      st'.mem.pages = 17 ∧
      st'.globals.globals = [.i32 1048064, .i32 1050149, .i32 1050160] ∧
      st'.mem.read32 1048204 = UInt32.ofNat k ∧
      (∀ jj, jj < k →
        st'.mem.read32 (1048076 + 4 * UInt32.ofNat jj)
          = st0.mem.read32 (1048384 + 4 * UInt32.ofNat (count.toNat - 1 - jj))) ∧
      (∀ j : Nat, (j < 1048064 ∨ 1048224 ≤ j) → st'.mem.bytes j = st0.mem.bytes j))
    (μ := fun st' _ => count.toNat + 1 - (st'.mem.read32 1048204).toNat)
  · -- invariant on entry (`k = 0`)
    refine ⟨0, .i32 128, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
      by omega, rfl, by simp [hpg], rfl, by simp, fun jj hjj => by omega, ?_⟩
    intro j hj
    peel_writes
  · -- one phase-1 iteration (or, once `k = count`, all of phase 2)
    rintro st s ⟨k, w3, w4, w5, w6, w7, w8, w9, w10, hk, rfl, hpg', hgl', hK, hscr, hfr⟩
    have hKt : (UInt32.ofNat k).toNat = k := hofNat k (by omega)
    apply wp_block_cons -- W
    apply wp_block_cons -- X
    apply wp_block_cons -- Y
    apply wp_block_cons -- Z
    apply wp_block_cons -- V
    wp_run
    simp [hK, hpg']
    by_cases hkc : (UInt32.ofNat k : UInt32) < count
    · -- `k < count`: copy one cell into the scratch and re-establish.
      have hklt : k < count.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp hkc; rw [hKt] at this; exact this
      have hsubk : count - 1 - UInt32.ofNat k = UInt32.ofNat (count.toNat - 1 - k) := by
        apply UInt32.toNat.inj
        rw [hofNat (count.toNat - 1 - k) (by omega)]
        simp [UInt32.toNat_sub, hKt]
        omega
      have hjlt : (UInt32.ofNat (count.toNat - 1 - k) : UInt32) < count := by
        rw [UInt32.lt_iff_toNat_lt, hofNat (count.toNat - 1 - k) (by omega)]; omega
      have hk32 : (UInt32.ofNat k : UInt32) < 32 := by
        rw [UInt32.lt_iff_toNat_lt, hKt]
        simp only [show (32 : UInt32).toNat = 32 from rfl]
        omega
      have haddrB : UInt32.ofNat (count.toNat - 1 - k) <<< (2 : UInt32) + 1048384
          = 1048384 + 4 * UInt32.ofNat (count.toNat - 1 - k) := by
        rw [shl_two]; exact UInt32.add_comm _ _
      have haddrS : UInt32.ofNat k <<< (2 : UInt32) + 1048076
          = 1048076 + 4 * UInt32.ofNat k := by
        rw [shl_two]; exact UInt32.add_comm _ _
      have hcellb := hcellB (count.toNat - 1 - k) (by omega)
      have hcells := hcellS k (by omega)
      have hle1 : 1048384 + 4 * (count.toNat - 1 - k) ≤ 1114108 := by omega
      have hle2 : 1048076 + 4 * k ≤ 1114108 := by omega
      have hmod1 : (1048384 + 4 * (count.toNat - 1 - k)) % 4294967296
          = 1048384 + 4 * (count.toNat - 1 - k) := by omega
      have hmod2 : (1048076 + 4 * k) % 4294967296 = 1048076 + 4 * k := by omega
      have hd1 : 1048076 + 4 * k + 4 ≤ 1048204 := by omega
      -- the copied value is the original buffer cell (the frame writes so
      -- far never touch the buffer)
      have hval : st.mem.read32 (1048384 + 4 * UInt32.ofNat (count.toNat - 1 - k))
          = st0.mem.read32 (1048384 + 4 * UInt32.ofNat (count.toNat - 1 - k)) :=
        read32_eq_of_bytes _ _ _
          (hfr _ (by rw [hcellb]; omega)) (hfr _ (by rw [hcellb]; omega))
          (hfr _ (by rw [hcellb]; omega)) (hfr _ (by rw [hcellb]; omega))
      simp [hkc, hsubk, hjlt, hk32, haddrB, haddrS, hcells,
        hd1, hK, hval]
      refine ⟨by simp [Nat.shiftLeft_eq]; omega, by simp [Nat.shiftLeft_eq]; omega,
        ⟨k + 1, by omega, hgl', ?_, ?_, ?_⟩, by omega⟩
      · -- index slot incremented
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, hKt, hofNat (k + 1) (by omega)]
        simp; omega
      · -- scratch prefix extended by one
        intro jj hjj
        have hcj := hcellS jj (by omega)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjj with hlt | rfl
        · peel_reads
          exact hscr jj hlt
        · peel_reads
      · -- frame framing preserved
        intro j hj
        peel_writes
        exact hfr j hj
    · -- `k = count`: phase 2, copy the scratch back over the buffer.
      have hkeq : k = count.toNat := by
        have : ¬ k < count.toNat := fun h =>
          hkc (UInt32.lt_iff_toNat_lt.mpr (by rw [hKt]; exact h))
        omega
      subst hkeq
      simp
      apply wp_loop_cons
        (Inv := fun st' s' => ∃ (q : Nat) (w3 w4 w5 w6 w7 w8 w9 w10 : Value),
          q ≤ count.toNat ∧
          s' = { params := [.i32 1048384, .i32 count],
                 locals := [.i32 1048064, w3, w4, w5, w6, w7, w8, w9, w10],
                 values := [] } ∧
          st'.mem.pages = 17 ∧
          st'.globals.globals = [.i32 1048064, .i32 1050149, .i32 1050160] ∧
          st'.mem.read32 1048208 = UInt32.ofNat q ∧
          (∀ jj, jj < count.toNat →
            st'.mem.read32 (1048076 + 4 * UInt32.ofNat jj)
              = st0.mem.read32 (1048384 + 4 * UInt32.ofNat (count.toNat - 1 - jj))) ∧
          (∀ i, i < q →
            st'.mem.read32 (1048384 + 4 * UInt32.ofNat i)
              = st0.mem.read32 (1048384 + 4 * UInt32.ofNat (count.toNat - 1 - i))) ∧
          (∀ j : Nat, (j < 1048064 ∨ 1048224 ≤ j) →
            (j < 1048384 ∨ 1048384 + 4 * count.toNat ≤ j) →
            st'.mem.bytes j = st0.mem.bytes j))
        (μ := fun st' _ => count.toNat + 1 - (st'.mem.read32 1048208).toNat)
      · -- phase-2 entry (`q = 0`): the scratch is fully populated
        refine ⟨0, w3, w4, w5, w6, w7, w8, w9, w10, by omega, rfl, by simp [hpg'],
          hgl', by simp, fun jj hjj => ?_, fun i hi => by omega, fun j hj1 hj2 => ?_⟩
        · have hcj := hcellS jj (by omega)
          peel_reads
          exact hscr jj hjj
        · peel_writes
          exact hfr j hj1
      · -- one phase-2 iteration / the function epilogue
        rintro stp sp ⟨q, x3, x4, x5, x6, x7, x8, x9, x10, hq, rfl, hpg2, hgl2,
          hQ, hscr2, hdone, hfr2⟩
        have hQt : (UInt32.ofNat q).toNat = q := hofNat q (by omega)
        apply wp_block_cons -- the loop-exit test block
        wp_run
        simp [hQ, hpg2]
        by_cases hqc : (UInt32.ofNat q : UInt32) < count
        · -- `q < count`: write `scratch[q]` to `ptr[q]`, re-establish.
          have hqlt : q < count.toNat := by
            have := UInt32.lt_iff_toNat_lt.mp hqc; rw [hQt] at this; exact this
          have hq32 : (UInt32.ofNat q : UInt32) < 32 := by
            rw [UInt32.lt_iff_toNat_lt, hQt]
            simp only [show (32 : UInt32).toNat = 32 from rfl]
            omega
          have haddrB : UInt32.ofNat q <<< (2 : UInt32) + 1048384
              = 1048384 + 4 * UInt32.ofNat q := by
            rw [shl_two]; exact UInt32.add_comm _ _
          have haddrS : UInt32.ofNat q <<< (2 : UInt32) + 1048076
              = 1048076 + 4 * UInt32.ofNat q := by
            rw [shl_two]; exact UInt32.add_comm _ _
          have hcellb := hcellB q (by omega)
          have hcells := hcellS q (by omega)
          have hle1 : 1048384 + 4 * q ≤ 1114108 := by omega
          have hle2 : 1048076 + 4 * q ≤ 1114108 := by omega
          have hmod1 : (1048384 + 4 * q) % 4294967296 = 1048384 + 4 * q := by omega
          have hmod2 : (1048076 + 4 * q) % 4294967296 = 1048076 + 4 * q := by omega
          have hd1 : 1048076 + 4 * q + 4 ≤ 1048208 := by omega
          have hd2 : 1048208 + 4 ≤ 1048384 + 4 * q := by omega
          simp only [hqc, if_pos]
          norm_num
          simp
          apply wp_block_cons
          apply wp_block_cons
          apply wp_block_cons
          wp_run
          simp [hqc, hq32, hQ, haddrB, haddrS, hcellb, hcells,
            hle1, hle2, hd2, hpg2]
          refine ⟨⟨q + 1, by omega, hgl2, ?_, ?_, ?_, ?_⟩, ?_⟩
          · -- index slot incremented
            apply UInt32.toNat.inj
            rw [UInt32.toNat_add, hQt, hofNat (q + 1) (by omega)]
            simp; omega
          · -- scratch contents undisturbed
            intro jj hjj
            have hcj := hcellS jj (by omega)
            peel_reads
            exact hscr2 jj hjj
          · -- reversed prefix extended by one
            intro i hi
            have hci := hcellB i (by omega)
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
            · peel_reads
              exact hdone i hlt
            · peel_reads
              exact hscr2 i (by omega)
          · -- framing preserved
            intro j hj1 hj2
            peel_writes
            exact hfr2 j hj1 hj2
          · -- measure decreases
            omega
        · -- `q = count`: restore `global 0` and return; buffer is reversed.
          have hqeq : q = count.toNat := by
            have : ¬ q < count.toNat := fun h =>
              hqc (UInt32.lt_iff_toNat_lt.mpr (by rw [hQt]; exact h))
            omega
          subst hqeq
          simp [hgl2]
          exact ⟨fun i hi => hdone i hi, hfr2⟩

/-! ## `func6`: the `check` body

`func6(seed, len)` clamps `count = min(len, 32)`, zero-fills the two
128-byte buffers `A = [1048256, 1048384)` and `B = [1048384, 1048512)`
in its frame, seeds them identically (`A[i] = B[i] = seed*(i+1) + i`),
builds a checked slice over each (`func7` chain), reverses `A` with
`func2` and `B` with `func3`, and compares element-wise — hitting
`unreachable` iff some `A[i] ≠ B[i]`. Since both reversers produce the
same permutation of equal arrays, the comparison always passes.

The body after the `count`-clamping `block` is split off as an opaque
[`tail6`] so the two clamp branches (`len > 32` / `len ≤ 32`) can share
one symbolic-execution proof, parametric in `count`. -/

/-- Everything in `func6` after the prologue and the `count`-clamping
block (13 instructions). -/
def tail6 : Wasm.Program := func6.drop 13

private theorem func6_split : func6 = func6.take 13 ++ tail6 := by
  unfold tail6; exact (List.take_append_drop 13 func6).symm

set_option maxHeartbeats 8000000 in
/-- The shared tail of `func6`, parametric in the clamped `count` (held
in the frame slot `1048252`) and in the continuation `Q`: the tail
always leaves via `ret` with an empty stack, `global 0` restored to
`1048560` and 17 pages. -/
private theorem tail6_wp (env : HostEnv Unit) (st1 : Store Unit)
    (seed len count : UInt32) (Q : Assertion Unit)
    (hcount : count.toNat ≤ 32)
    (hpg : st1.mem.pages = 17)
    (hgl : st1.globals.globals = [.i32 1048224, .i32 1050149, .i32 1050160])
    (hcnt : st1.mem.read32 1048252 = count)
    (hQ : ∀ st' : Store Unit, st'.mem.pages = 17 →
      st'.globals.globals = [.i32 1048560, .i32 1050149, .i32 1050160] →
      Q (.Return st' [])) :
    wp «module» tail6 Q st1
      { params := [.i32 seed, .i32 len],
        locals := [.i32 1048224, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                   .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
                   .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [] } env := by
  have hofNat : ∀ k : Nat, k ≤ 33 → (UInt32.ofNat k).toNat = k := fun k hk => by
    simp; omega
  have hcellA : ∀ k : Nat, k ≤ 32 →
      ((1048256 : UInt32) + 4 * UInt32.ofNat k).toNat = 1048256 + 4 * k := fun k hk =>
    toNat_base_add _ _ (by simp; omega)
  have hcellB : ∀ k : Nat, k ≤ 32 →
      ((1048384 : UInt32) + 4 * UInt32.ofNat k).toNat = 1048384 + 4 * k := fun k hk =>
    toNat_base_add _ _ (by simp; omega)
  unfold tail6 func6
  wp_run
  simp [hcnt, hpg]
  apply wp_block_cons   -- OUTER
  -- The seed loop: `A[k] = B[k] = seed*(k+1) + k` for `k = 0 .. count-1`;
  -- the calls / comparison live in its `k = count` exit branch.
  apply wp_loop_cons
    (Inv := fun st' s' => ∃ (k : Nat)
        (w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : Value),
      k ≤ count.toNat ∧
      s' = { params := [.i32 seed, .i32 len],
             locals := [.i32 1048224, .i32 count, w4, w5, w6, w7, w8, w9, w10, w11,
                        w12, w13, w14, w15, w16, w17, w18, w19, w20, w21],
             values := [] } ∧
      st'.mem.pages = 17 ∧
      st'.globals.globals = [.i32 1048224, .i32 1050149, .i32 1050160] ∧
      st'.mem.read32 1048512 = UInt32.ofNat k ∧
      (∀ i, i < k →
        st'.mem.read32 (1048256 + 4 * UInt32.ofNat i)
          = st'.mem.read32 (1048384 + 4 * UInt32.ofNat i)))
    (μ := fun st' _ => count.toNat + 1 - (st'.mem.read32 1048512).toNat)
  · -- seed-loop entry (`k = 0`)
    exact ⟨0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      by omega, rfl, by simp [hpg], by simp [hgl], by simp,
      fun i hi => by omega⟩
  · rintro st s ⟨k, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17,
      w18, w19, w20, w21, hk, rfl, hpg', hgl', hK, hAB⟩
    have hKt : (UInt32.ofNat k).toNat = k := hofNat k (by omega)
    apply wp_block_cons -- C1
    apply wp_block_cons -- C2
    apply wp_block_cons -- C3
    apply wp_block_cons -- C4
    apply wp_block_cons -- C5
    wp_run
    simp (config := { maxSteps := 5000000 }) [hK, hpg']
    by_cases hkc : (UInt32.ofNat k : UInt32) < count
    · -- `k < count`: seed `A[k]` and `B[k]` with the same value.
      have hklt : k < count.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp hkc; rw [hKt] at this; exact this
      have hk32 : (UInt32.ofNat k : UInt32) < 32 := by
        rw [UInt32.lt_iff_toNat_lt, hKt]
        simp only [show (32 : UInt32).toNat = 32 from rfl]
        omega
      have haddrA : UInt32.ofNat k <<< (2 : UInt32) + 1048256
          = 1048256 + 4 * UInt32.ofNat k := by
        rw [shl_two]; exact UInt32.add_comm _ _
      have haddrB : UInt32.ofNat k <<< (2 : UInt32) + 1048384
          = 1048384 + 4 * UInt32.ofNat k := by
        rw [shl_two]; exact UInt32.add_comm _ _
      have hcella := hcellA k (by omega)
      have hcellb := hcellB k (by omega)
      have hle1 : 1048256 + 4 * k ≤ 1114108 := by omega
      have hle2 : 1048384 + 4 * k ≤ 1114108 := by omega
      have hmod1 : (1048256 + 4 * k) % 4294967296 = 1048256 + 4 * k := by omega
      have hmod2 : (1048384 + 4 * k) % 4294967296 = 1048384 + 4 * k := by omega
      have hd1 : 1048256 + 4 * k + 4 ≤ 1048512 := by omega
      have hd2 : 1048384 + 4 * k + 4 ≤ 1048512 := by omega
      have hd3 : 1048256 + 4 * k + 4 ≤ 1048384 := by omega
      simp [hkc, hk32, hK, haddrA, haddrB, hcella, hcellb,
        hd1, hd2]
      rw [if_neg (by simp [Nat.shiftLeft_eq]; omega),
          if_neg (by simp [Nat.shiftLeft_eq]; omega)]
      refine ⟨⟨k + 1, by omega, hgl', ?_, ?_⟩, by omega⟩
      · -- index slot incremented
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, hKt, hofNat (k + 1) (by omega)]
        simp; omega
      · -- `A = B` prefix extended by one
        intro i hi
        have hci := hcellA i (by omega)
        have hcbi := hcellB i (by omega)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · peel_reads
          exact hAB i hlt
        · peel_reads
    · -- `k = count`: build the slices, reverse `A` and `B`, compare.
      have hkeq : k = count.toNat := by
        have : ¬ k < count.toNat := fun h =>
          hkc (UInt32.lt_iff_toNat_lt.mpr (by rw [hKt]; exact h))
        omega
      subst hkeq
      rw [if_neg hkc]
      simp only [show ((1 : UInt32) &&& 0) = 0 from rfl]
      -- slice over A through the `func7` chain
      refine wp_call_of_terminates
        (func7_at env _ 1048232 1048256 count 1048732 hcount (by simp) (by simp [hpg'])
          (by simp [hgl'])) ?_
      rintro st2 vs2 ⟨rfl, hpg2, hgl2, hrdA, hrcA, hbytes2⟩
      -- the seeded `A = B` facts survive `func7` (it writes below the buffers)
      have hAB2 : ∀ i, i < count.toNat →
          st2.mem.read32 (1048256 + 4 * UInt32.ofNat i)
            = st2.mem.read32 (1048384 + 4 * UInt32.ofNat i) := by
        intro i hi
        have hci := hcellA i (by omega)
        have hcbi := hcellB i (by omega)
        have hA : st2.mem.read32 (1048256 + 4 * UInt32.ofNat i)
            = st.mem.read32 (1048256 + 4 * UInt32.ofNat i) :=
          read32_eq_of_bytes _ _ _
            (hbytes2 _ (by rw [hci]; omega) (by rw [hci]; simp only [UInt32.reduceToNat]; omega))
            (hbytes2 _ (by rw [hci]; omega) (by rw [hci]; simp only [UInt32.reduceToNat]; omega))
            (hbytes2 _ (by rw [hci]; omega) (by rw [hci]; simp only [UInt32.reduceToNat]; omega))
            (hbytes2 _ (by rw [hci]; omega) (by rw [hci]; simp only [UInt32.reduceToNat]; omega))
        have hB : st2.mem.read32 (1048384 + 4 * UInt32.ofNat i)
            = st.mem.read32 (1048384 + 4 * UInt32.ofNat i) :=
          read32_eq_of_bytes _ _ _
            (hbytes2 _ (by rw [hcbi]; omega) (by rw [hcbi]; simp only [UInt32.reduceToNat]; omega))
            (hbytes2 _ (by rw [hcbi]; omega) (by rw [hcbi]; simp only [UInt32.reduceToNat]; omega))
            (hbytes2 _ (by rw [hcbi]; omega) (by rw [hcbi]; simp only [UInt32.reduceToNat]; omega))
            (hbytes2 _ (by rw [hcbi]; omega) (by rw [hcbi]; simp only [UInt32.reduceToNat]; omega))
        rw [hA, hB]
        exact hAB i hi
      have hrcA' : st2.mem.read32 1048236 = count := by simpa using hrcA
      wp_run
      wp_norm
      simp only [hpg2, Nat.reduceMul, Nat.reduceLT, reduceIte, hrcA', hrdA]
      -- reverse A in place
      refine wp_call_of_terminates
        (func2_at env _ count hcount hpg2 hgl2) ?_
      rintro st3 vs3 ⟨rfl, hpg3, hgl3, hrevA, hbytes3⟩
      wp_run
      wp_norm
      -- slice over B through the `func7` chain
      refine wp_call_of_terminates
        (func7_at env _ 1048240 1048384 count 1048748 hcount (by simp) (by simp [hpg3])
          (by simp [hgl3])) ?_
      rintro st4 vs4 ⟨rfl, hpg4, hgl4, hrdB, hrcB, hbytes4⟩
      have hrcB' : st4.mem.read32 1048244 = count := by simpa using hrcB
      wp_run
      wp_norm
      simp only [hpg4, Nat.reduceMul, Nat.reduceLT, reduceIte, hrcB', hrdB]
      -- reverse B in place
      refine wp_call_of_terminates
        (func3_at env _ count hcount hpg4 hgl4) ?_
      rintro st5 vs5 ⟨rfl, hpg5, hgl5, hrevB, hbytes5⟩
      -- both reversals of equal arrays are equal, cell by cell
      have hABr : ∀ i, i < count.toNat →
          st5.mem.read32 (1048256 + 4 * UInt32.ofNat i)
            = st5.mem.read32 (1048384 + 4 * UInt32.ofNat i) := by
        intro i hi
        have hci := hcellA i (by omega)
        have hcbi := hcellB i (by omega)
        have hcm := hcellA (count.toNat - 1 - i) (by omega)
        have hcbm := hcellB (count.toNat - 1 - i) (by omega)
        -- A side: untouched by func3/func7#2, reversed by func2
        have hA5 : st5.mem.read32 (1048256 + 4 * UInt32.ofNat i)
            = st4.mem.read32 (1048256 + 4 * UInt32.ofNat i) :=
          read32_eq_of_bytes _ _ _
            (hbytes5 _ (by rw [hci]; omega) (by rw [hci]; omega))
            (hbytes5 _ (by rw [hci]; omega) (by rw [hci]; omega))
            (hbytes5 _ (by rw [hci]; omega) (by rw [hci]; omega))
            (hbytes5 _ (by rw [hci]; omega) (by rw [hci]; omega))
        have hA4 : st4.mem.read32 (1048256 + 4 * UInt32.ofNat i)
            = st3.mem.read32 (1048256 + 4 * UInt32.ofNat i) :=
          read32_eq_of_bytes _ _ _
            (hbytes4 _ (by rw [hci]; omega) (by rw [hci]; simp only [UInt32.reduceToNat]; omega))
            (hbytes4 _ (by rw [hci]; omega) (by rw [hci]; simp only [UInt32.reduceToNat]; omega))
            (hbytes4 _ (by rw [hci]; omega) (by rw [hci]; simp only [UInt32.reduceToNat]; omega))
            (hbytes4 _ (by rw [hci]; omega) (by rw [hci]; simp only [UInt32.reduceToNat]; omega))
        -- B side: untouched by func2/func7#2 (relative to st2), reversed by func3
        have hB4 : st4.mem.read32 (1048384 + 4 * UInt32.ofNat (count.toNat - 1 - i))
            = st3.mem.read32 (1048384 + 4 * UInt32.ofNat (count.toNat - 1 - i)) :=
          read32_eq_of_bytes _ _ _
            (hbytes4 _ (by rw [hcbm]; omega) (by rw [hcbm]; simp only [UInt32.reduceToNat]; omega))
            (hbytes4 _ (by rw [hcbm]; omega) (by rw [hcbm]; simp only [UInt32.reduceToNat]; omega))
            (hbytes4 _ (by rw [hcbm]; omega) (by rw [hcbm]; simp only [UInt32.reduceToNat]; omega))
            (hbytes4 _ (by rw [hcbm]; omega) (by rw [hcbm]; simp only [UInt32.reduceToNat]; omega))
        have hB3 : st3.mem.read32 (1048384 + 4 * UInt32.ofNat (count.toNat - 1 - i))
            = st2.mem.read32 (1048384 + 4 * UInt32.ofNat (count.toNat - 1 - i)) :=
          read32_eq_of_bytes _ _ _
            (hbytes3 _ (by rw [hcbm]; omega) (by rw [hcbm]; omega))
            (hbytes3 _ (by rw [hcbm]; omega) (by rw [hcbm]; omega))
            (hbytes3 _ (by rw [hcbm]; omega) (by rw [hcbm]; omega))
            (hbytes3 _ (by rw [hcbm]; omega) (by rw [hcbm]; omega))
        rw [hA5, hA4, hrevA i hi, hrevB i hi, hB4, hB3]
        exact hAB2 (count.toNat - 1 - i) (by omega)
      wp_run
      wp_norm
      simp only [hpg5, Nat.reduceMul, Nat.reduceLT, reduceIte]
      -- the comparison loop: `A[q] = B[q]` for every `q`, so the
      -- `unreachable` is never reached and the `ret` fires at `q = count`.
      apply wp_loop_cons
        (Inv := fun st' s' => ∃ (q : Nat)
            (x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : Value),
          q ≤ count.toNat ∧
          s' = { params := [.i32 seed, .i32 len],
                 locals := [.i32 1048224, .i32 count, x4, x5, x6, x7, x8, x9, x10, x11,
                            x12, x13, x14, x15, x16, x17, x18, x19, x20, x21],
                 values := [] } ∧
          st'.mem.pages = 17 ∧
          st'.globals.globals = [.i32 1048224, .i32 1050149, .i32 1050160] ∧
          st'.mem.read32 1048516 = UInt32.ofNat q ∧
          (∀ i, i < count.toNat →
            st'.mem.read32 (1048256 + 4 * UInt32.ofNat i)
              = st'.mem.read32 (1048384 + 4 * UInt32.ofNat i)))
        (μ := fun st' _ => count.toNat + 1 - (st'.mem.read32 1048516).toNat)
      · refine ⟨0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          by omega, rfl, by simp [hpg5], by simp [hgl5], by simp, ?_⟩
        intro i hi
        have hci := hcellA i (by omega)
        have hcbi := hcellB i (by omega)
        peel_reads
        exact hABr i hi
      · rintro stq sq ⟨q, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16,
          x17, x18, x19, x20, x21, hq, rfl, hpgq, hglq, hQq, hABq⟩
        have hQt : (UInt32.ofNat q).toNat = q := hofNat q (by omega)
        apply wp_block_cons
        wp_run
        simp [hQq, hpgq]
        by_cases hqc : (UInt32.ofNat q : UInt32) < count
        · -- `q < count`: the cells agree, so step to `q + 1`.
          have hqlt : q < count.toNat := by
            have := UInt32.lt_iff_toNat_lt.mp hqc; rw [hQt] at this; exact this
          have hq32 : (UInt32.ofNat q : UInt32) < 32 := by
            rw [UInt32.lt_iff_toNat_lt, hQt]
            simp only [show (32 : UInt32).toNat = 32 from rfl]
            omega
          have haddrA : UInt32.ofNat q <<< (2 : UInt32) + 1048256
              = 1048256 + 4 * UInt32.ofNat q := by
            rw [shl_two]; exact UInt32.add_comm _ _
          have haddrB : UInt32.ofNat q <<< (2 : UInt32) + 1048384
              = 1048384 + 4 * UInt32.ofNat q := by
            rw [shl_two]; exact UInt32.add_comm _ _
          have hcella := hcellA q (by omega)
          have hcellb := hcellB q (by omega)
          have hle1 : 1048256 + 4 * q ≤ 1114108 := by omega
          have hle2 : 1048384 + 4 * q ≤ 1114108 := by omega
          have hmod1 : (1048256 + 4 * q) % 4294967296 = 1048256 + 4 * q := by omega
          have hmod2 : (1048384 + 4 * q) % 4294967296 = 1048384 + 4 * q := by omega
          have hval := hABq q hqlt
          simp only [hqc, if_pos]
          norm_num
          simp
          apply wp_block_cons
          apply wp_block_cons
          apply wp_block_cons
          apply wp_block_cons
          apply wp_block_cons
          wp_run
          have hbA : ¬ (1114112 < 1048256 + 4 * q + 4) := by omega
          have hbB : ¬ (1114112 < 1048384 + 4 * q + 4) := by omega
          simp [hq32, hQq, haddrA, haddrB, hcella, hcellb,
            hval, hpgq, hbA, hbB]
          refine ⟨⟨q + 1, by omega, hglq, ?_, ?_⟩, by omega⟩
          · -- index slot incremented
            apply UInt32.toNat.inj
            rw [UInt32.toNat_add, hQt, hofNat (q + 1) (by omega)]
            simp; omega
          · -- the `A = B` facts survive the slot write
            intro i hi
            have hci := hcellA i (by omega)
            have hcbi := hcellB i (by omega)
            peel_reads
            exact hABq i hi
        · -- `q = count`: restore `global 0 = 1048560` and return.
          simp [hqc, hglq]
          exact hQ _ (by simp [hpgq]) (by simp)

/-- `func6` (the `check` body) terminates with an empty stack, restoring
`global 0 = 1048560` and the 17 pages, for every `(seed, len)`. The
`count`-clamping branch is dispatched here; both arms feed [`tail6_wp`]
with `count = 32` resp. `count = len`. -/
theorem func6_at (env : HostEnv Unit) (st0 : Store Unit) (seed len : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048560, .i32 1050149, .i32 1050160]) :
    TerminatesWith env «module» 6 st0 [.i32 len, .i32 seed]
      (fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048560, .i32 1050149, .i32 1050160]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32],
           [.i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32,
            .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32], func6, []⟩) rfl
  rw [func6_split]
  simp only [func6, List.take, List.cons_append, List.nil_append]
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  apply wp_block_cons   -- the count-clamping block
  apply wp_block_cons
  wp_run
  by_cases hgt : len > 32
  · -- `len > 32`: `count = 32`
    simp [hgt, hpg]
    refine tail6_wp env _ seed len 32 _ (by simp) (by simp [hpg]) (by simp)
      (by simp) ?_
    intro st' h1 h2
    simp [h1, h2]
  · -- `len ≤ 32`: `count = len`
    have hlen32 : len.toNat ≤ 32 := by
      rcases Nat.lt_or_ge 32 len.toNat with h | h
      · exact absurd (UInt32.lt_iff_toNat_lt.mpr (by simpa using h)) hgt
      · exact h
    simp [hgt, hpg]
    refine tail6_wp env _ seed len len _ hlen32 (by simp [hpg]) (by simp)
      (by simp) ?_
    intro st' h1 h2
    simp [h1, h2]

/-! ## The export wrapper (`func8` = `check`) -/

@[proves Project.ReverseInplace.Spec.CheckSpec]
theorem check_correct : CheckSpec := by
  intro env initial seed len hinit
  subst hinit
  have hpg : («module».initialStore : Store Unit).mem.pages = 17 := by rfl
  have hgl : («module».initialStore : Store Unit).globals.globals
      = [.i32 1048576, .i32 1050149, .i32 1050160] := by rfl
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32, .i32], [.i32], func8, []⟩) rfl
  unfold func8
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  refine wp_call_of_terminates (func6_at env _ seed len (by simp [hpg]) (by simp)) ?_
  rintro st' vs ⟨rfl, hpg', hgl'⟩
  wp_run
  simp [hgl']

end Project.ReverseInplace.Spec
