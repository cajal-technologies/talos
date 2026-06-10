import Project.XorSum.Program

/-!
# Specification for `xor_sum`

The exported `check(seed, len)` seeds a length-`min(len,32)` buffer from
`seed`, XOR-folds it both ways — left-to-right (the implementation under
test) and right-to-left (the obviously-correct oracle) — and traps via
`unreachable` iff they disagree. Proving the wasm export terminates
without trapping for every `(seed, len)` is therefore the same as
proving the forward and backward XOR-folds agree on every seeded
buffer, which is the associativity-and-commutativity content of `xor`.

At `opt-level=0` the live call graph is

```
func6 (exported `check` wrapper, frame at 1048560)
  └─ func3 (seed buffer, compare folds; frame at 1048368, buffer at
     [1048392, 1048520), loop counter spilled to 1048520)
       ├─ func0 (slice-view helper: bounds-checks `cl ≤ 32` and writes
       │        the `(ptr, len)` pair to `dst`/`dst+4`; frame at 1048288)
       ├─ func4 (forward fold over the buffer; frame at 1048352, the
       │        accumulator lives at 1048352 and the index at 1048356)
       └─ func5 (backward fold, same frame discipline as func4)
```

Every function carries the unoptimized shadow-stack discipline: the
prologue claims a frame below `global 0` and spills values to linear
memory at fixed frame offsets, and the epilogue restores `global 0`.
Unlike the pure-arithmetic examples, the rustc bounds checks on the
buffer reads/writes are *live* code here — they are discharged by the
loop invariants (`index < min(len,32) ≤ 32`), not by constant folding.
-/

namespace Project.XorSum.Spec

open Wasm

set_option maxRecDepth 1048576

/-- The exported `check` terminates without trapping (and returns no
values) on every `(seed, len)` input, when run from the module's
canonical instantiation.

The `initial = «module».initialStore` hypothesis is load-bearing: every
function in the live call graph spills to the shadow stack below
`global 0` and the body iterates over a 128-byte buffer at
`[1048392, 1048520)`. That is in-bounds precisely because the canonical
store sets `global 0 = 1048576` and allocates `17` pages
(`17 · 65536 = 1114112` bytes). Under an adversarial store (e.g.
`mem.pages = 0`) the very first spill would trap, so this property
genuinely needs the canonical store — unlike the pure-arithmetic
equivalence checks, which hold for every store.

Informal spec:
For `seed len : UInt32`, the wasm export `check` (funcIdx 6) terminates
and leaves an empty value stack. Termination-without-trapping is the
whole content of the spec — the body traps via `unreachable` iff the
forward and backward XOR-folds disagree, so this property *is* the
associativity-and-commutativity claim for `xor` over the seeded
buffer. -/
@[spec_of "rust-exported" "xor_sum::check"]
def CheckSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (seed len : UInt32),
    initial = «module».initialStore →
    TerminatesWith env «module» 6 initial [.i32 len, .i32 seed]
      (fun _ rs => rs = [])

/-! ## XOR fold and its order-independence

`xorFwd m ptr n` is the forward (left-to-right) XOR fold of the `n`
little-endian `u32` words at `ptr, ptr+4, …, ptr+4*(n-1)`. The forward
loop (`func4`) computes this directly. The backward loop (`func5`)
reads the same words high-to-low; because `xor` is commutative,
associative and self-inverse, it lands on the *same* value — that
order-independence is the entire mathematical content of the check. -/

def xorFwd (m : Mem) (ptr : UInt32) : Nat → UInt32
  | 0     => 0
  | n + 1 => xorFwd m ptr n ^^^ m.read32 (ptr + 4 * UInt32.ofNat n)

@[simp] lemma xorFwd_zero (m : Mem) (ptr : UInt32) : xorFwd m ptr 0 = 0 := rfl

lemma xorFwd_succ (m : Mem) (ptr : UInt32) (n : Nat) :
    xorFwd m ptr (n + 1) = xorFwd m ptr n ^^^ m.read32 (ptr + 4 * UInt32.ofNat n) := rfl

/-- Order-independence step: folding the top element in undoes the two
copies of `M` that the running accumulator and the suffix fold share. -/
private lemma xor_shuffle (M X Y : UInt32) : M ^^^ (X ^^^ (Y ^^^ M)) = X ^^^ Y := by
  rw [← UInt32.xor_assoc X Y M, UInt32.xor_comm (X ^^^ Y) M,
      ← UInt32.xor_assoc M M (X ^^^ Y), UInt32.xor_self, UInt32.zero_xor]

/-! ## UInt32 ↔ Nat bridges for the loop counters -/

private lemma toNat_ofNat32 {j : Nat} (h : j < 4294967296) :
    (UInt32.ofNat j).toNat = j := UInt32.toNat_ofNat_of_lt' h

private lemma ofNat_lt_iff {j : Nat} {cl : UInt32} (h : j < 4294967296) :
    UInt32.ofNat j < cl ↔ j < cl.toNat := by
  rw [UInt32.lt_iff_toNat_lt, toNat_ofNat32 h]

private lemma one_add_ofNat {j : Nat} (h : j + 1 < 4294967296) :
    (1 : UInt32) + UInt32.ofNat j = UInt32.ofNat (j + 1) := by
  apply UInt32.toNat.inj
  have h1 : (1 : UInt32).toNat = 1 := rfl
  rw [UInt32.toNat_add, toNat_ofNat32 (by omega), toNat_ofNat32 h, h1]
  omega

private lemma ofNat_sub_one {r : Nat} (h0 : 0 < r) (h : r < 4294967296) :
    UInt32.ofNat r - 1 = UInt32.ofNat (r - 1) := by
  apply UInt32.toNat.inj
  have h1 : (1 : UInt32).toNat = 1 := rfl
  have hle : (1 : UInt32) ≤ UInt32.ofNat r := by
    rw [UInt32.le_iff_toNat_le, h1, toNat_ofNat32 h]; omega
  rw [UInt32.toNat_sub_of_le _ _ hle, h1, toNat_ofNat32 h, toNat_ofNat32 (by omega)]

private lemma zero_lt_ofNat_iff {r : Nat} (h : r < 4294967296) :
    (0 : UInt32) < UInt32.ofNat r ↔ 0 < r := by
  rw [UInt32.lt_iff_toNat_lt, toNat_ofNat32 h]
  simp

/-- `i32.shl` by 2 is multiplication by 4. -/
private lemma shl_two (x : UInt32) : x <<< 2 = x * 4 := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_mul, Nat.shiftLeft_eq]
  norm_num [UInt32.toNat_ofNat]

/-- The buffer word address as the loop computes it (`(j << 2) + base`)
equals the canonical `base + 4 * j` form used by `xorFwd`. -/
private lemma buf_addr_eq (j : Nat) :
    (UInt32.ofNat j <<< 2) + 1048392 = 1048392 + 4 * UInt32.ofNat j := by
  rw [shl_two, UInt32.mul_comm 4 (UInt32.ofNat j), UInt32.add_comm]

private lemma buf_addr_toNat {j : Nat} (h : j < 32) :
    ((1048392 : UInt32) + 4 * UInt32.ofNat j).toNat = 1048392 + 4 * j := by
  have h4 : (4 : UInt32).toNat = 4 := rfl
  have hb : (1048392 : UInt32).toNat = 1048392 := rfl
  rw [UInt32.toNat_add, UInt32.toNat_mul, toNat_ofNat32 (by omega), h4, hb]
  omega

/-! ## Memory framing lemmas

The shadow-stack code spills values to fixed frame offsets and reads
them back; the buffer at `[1048392, 1048520)` must additionally survive
the callees' frame writes (which all land strictly below `1048392`).
Besides the usual read-after-write facts we therefore carry pointwise
byte-preservation (`∀ i ≥ 1048392, bytes unchanged`) through every
call, and transport `xorFwd` along it. -/

@[simp] private theorem write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

@[simp] private theorem fill_pages (m : Mem) (o l : Nat) (v : UInt8) :
    (m.fill o l v).pages = m.pages := rfl

/-- A 32-bit read sees the value of a same-address 32-bit write. -/
@[simp] private theorem read32_write32_same (m : Mem) (a v : UInt32) :
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

private theorem write32_bytes_of_disjoint (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [Mem.write32, h0, h1, h2, h3]

/-- Specialization of [`write32_bytes_of_disjoint`] for frame writes
strictly below the buffer: a write whose 4 bytes end at or before
`1048392` cannot touch a byte at or above `1048392`. The bound is
stated so `decide` discharges it for literal addresses, keeping
buffer-preservation proofs to a single `repeat rw`. -/
private theorem bytes_write32_below {m : Mem} {a v : UInt32} {i : Nat}
    (ha : a.toNat + 4 ≤ 1048392) (hi : 1048392 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i :=
  write32_bytes_of_disjoint m a v i (by omega)

/-- Variant of [`bytes_write32_below`] for the fold functions' frames,
which end at `1048368` (the byte range they must not touch starts at
their caller's frame, one slot below the buffer). -/
private theorem bytes_write32_frame {m : Mem} {a v : UInt32} {i : Nat}
    (ha : a.toNat + 4 ≤ 1048368) (hi : 1048368 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i :=
  write32_bytes_of_disjoint m a v i (by omega)

/-- A 32-bit read is unaffected by a 32-bit write to a disjoint range. -/
@[simp] private theorem read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_of_disjoint m a v b.toNat (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

/-- Two memories that agree byte-for-byte from `lo` up agree on every
32-bit read whose address sits at or above `lo`. -/
private theorem read32_congr {m1 m2 : Mem} {lo : Nat} (a : UInt32)
    (h : ∀ i : Nat, lo ≤ i → m1.bytes i = m2.bytes i) (ha : lo ≤ a.toNat) :
    m1.read32 a = m2.read32 a := by
  simp only [Mem.read32]
  rw [h a.toNat (by omega), h (a.toNat + 1) (by omega),
      h (a.toNat + 2) (by omega), h (a.toNat + 3) (by omega)]

/-- `xorFwd` over the buffer at `1048392` only looks at bytes at or
above `1048392`, so byte-preservation there transports the fold. -/
private theorem xorFwd_congr {m1 m2 : Mem}
    (h : ∀ i : Nat, 1048392 ≤ i → m1.bytes i = m2.bytes i)
    (n : Nat) (hn : n ≤ 32) :
    xorFwd m1 1048392 n = xorFwd m2 1048392 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [xorFwd_succ, xorFwd_succ, ih (by omega),
        read32_congr _ h (by rw [buf_addr_toNat (by omega : k < 32)]; omega)]

/-! ## `func0`: the slice-view helper

`func0(dst, ptr, cl, loc)` is the unoptimized `RawVec`/slice plumbing:
it spills everything to its own 80-byte frame at `1048288`, performs
the *live* bounds check `cl ≤ 32` (panicking through `func56` when it
fails — never, at our call sites), and writes the slice view `(ptr, cl)`
to `dst`/`dst+4`. It is called by `func3` with `dst ∈ {1048368,
1048376}`, both inside `func3`'s frame and strictly below the buffer. -/

set_option maxHeartbeats 4000000 in
private theorem func0_at (env : HostEnv Unit) (st0 : Store Unit)
    (buf cl loc dst : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000])
    (hcl : cl.toNat ≤ 32)
    (hdst : dst = 1048368 ∨ dst = 1048376) :
    TerminatesWith env «module» 0 st0 [.i32 loc, .i32 cl, .i32 buf, .i32 dst]
      (fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000] ∧
        st'.mem.read32 dst = buf ∧ st'.mem.read32 (dst + 4) = cl ∧
        ∀ i : Nat, 1048392 ≤ i → st'.mem.bytes i = st0.mem.bytes i) := by
  have hcl32 : cl ≤ (32 : UInt32) := by
    rw [UInt32.le_iff_toNat_le]
    simpa using hcl
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32], func0, []⟩) rfl
  unfold func0
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  apply wp_block_cons
  wp_run
  simp [hcl32, hpg]
  rcases hdst with rfl | rfl <;>
  · simp
    intro i hi
    repeat rw [bytes_write32_below (by decide) hi]

/-! ## `func4`: the forward fold

`func4(ptr, cl)` XOR-folds the `cl` words at `ptr` left-to-right. Its
loop state lives in linear memory — the accumulator at `1048352` and
the index at `1048356`, both inside its 16-byte frame — so the loop
invariant speaks about `read32` of those addresses rather than locals.
The rustc per-iteration bounds check (`index < cl`, panicking through
`func59`) is live code, discharged by the invariant. We only prove it
for the call site's buffer `ptr = 1048392` (with `cl ≤ 32` the reads
stay inside `[1048392, 1048520)`), which keeps every frame address
concrete. -/

set_option maxHeartbeats 4000000 in
private theorem func4_at (env : HostEnv Unit) (st0 : Store Unit)
    (cl : UInt32) (tail : List Value)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000])
    (hcl : cl.toNat ≤ 32) :
    TerminatesWith env «module» 4 st0 (.i32 cl :: .i32 1048392 :: tail)
      (fun st' vs => vs = .i32 (xorFwd st0.mem 1048392 cl.toNat) :: tail ∧
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000] ∧
        ∀ i : Nat, 1048392 ≤ i → st'.mem.bytes i = st0.mem.bytes i) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32, .i32], func4, [.i32]⟩) rfl
  unfold func4
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals.globals = [.i32 1048352, .i32 1049997, .i32 1050000] ∧
      (∀ i : Nat, 1048368 ≤ i → st'.mem.bytes i = st0.mem.bytes i) ∧
      ∃ (j : Nat) (v3 v4 : Value),
        j ≤ cl.toNat ∧
        st'.mem.read32 1048356 = UInt32.ofNat j ∧
        st'.mem.read32 1048352 = xorFwd st0.mem 1048392 j ∧
        s' = { params := [.i32 1048392, .i32 cl],
               locals := [.i32 1048352, v3, v4], values := [] })
    (μ := fun st' _ => cl.toNat - (st'.mem.read32 1048356).toNat)
  · -- Invariant on entry: j = 0, accumulator 0.
    refine ⟨by simp [hpg], by simp, ?_, 0, .i32 0, .i32 0, by omega, by simp, by simp, rfl⟩
    intro i hi
    dsimp only
    repeat rw [bytes_write32_frame (by decide) hi]
  · -- One iteration.
    rintro st' s' ⟨hpg', hgl', hpres, j, v3, v4, hj, hcnt, hacc, rfl⟩
    have hj32 : j < 4294967296 := by omega
    apply wp_block_cons
    wp_run
    simp [hcnt, hpg']
    by_cases hlt : UInt32.ofNat j < cl
    · -- index < cl: accumulate word j and continue.
      have hjlt : j < cl.toNat := (ofNat_lt_iff hj32).mp hlt
      simp only [hlt, if_true]
      apply wp_block_cons
      wp_run
      simp [hlt, hcnt, hpg']
      -- The buffer read: rewrite the address into `xorFwd`'s canonical
      -- form, bring it back to the entry store, and discharge bounds.
      rw [buf_addr_eq j]
      have haddr : ((1048392 : UInt32) + 4 * UInt32.ofNat j).toNat = 1048392 + 4 * j :=
        buf_addr_toNat (by omega)
      have hrd : st'.mem.read32 (1048392 + 4 * UInt32.ofNat j)
          = st0.mem.read32 (1048392 + 4 * UInt32.ofNat j) :=
        read32_congr _ (fun i hi => hpres i (by omega)) (by rw [haddr]; omega)
      refine ⟨by simp [Nat.shiftLeft_eq]; omega, ⟨hgl', ?_,
        j + 1, by omega, one_add_ofNat (by omega), ?_⟩, by omega⟩
      · -- Buffer bytes survive the two frame writes.
        intro i hi
        rw [bytes_write32_frame (by decide) hi, bytes_write32_frame (by decide) hi]
        exact hpres i hi
      · -- The new accumulator is the (j+1)-fold.
        rw [hrd, hacc, xorFwd_succ]
        exact UInt32.xor_comm _ _
    · -- index ≥ cl: the fold is complete; return the accumulator.
      have hje : j = cl.toNat := by
        have := (ofNat_lt_iff (cl := cl) hj32).not.mp hlt
        omega
      simp only [hlt, if_false]
      simp only [hacc, hgl']
      simp [hje]
      exact fun i hi => hpres i (by omega)

/-! ## `func5`: the backward fold

`func5(ptr, cl)` XOR-folds the same words right-to-left: the counter at
`1048356` starts at `cl` and counts down, and each iteration folds word
`counter − 1` into the accumulator at `1048352`. The invariant says the
accumulator always equals `full-fold ^^^ fold-of-the-unprocessed-prefix`
— so when the counter hits `0` it has converged to the *forward* fold,
which is exactly the order-independence content of the check
([`xor_shuffle`] discharges the step). The post-condition is therefore
stated with `xorFwd`, the same function `func4` returns. -/

set_option maxHeartbeats 4000000 in
private theorem func5_at (env : HostEnv Unit) (st0 : Store Unit)
    (cl : UInt32) (tail : List Value)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000])
    (hcl : cl.toNat ≤ 32) :
    TerminatesWith env «module» 5 st0 (.i32 cl :: .i32 1048392 :: tail)
      (fun st' vs => vs = .i32 (xorFwd st0.mem 1048392 cl.toNat) :: tail ∧
        st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32, .i32], func5, [.i32]⟩) rfl
  unfold func5
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals.globals = [.i32 1048352, .i32 1049997, .i32 1050000] ∧
      (∀ i : Nat, 1048368 ≤ i → st'.mem.bytes i = st0.mem.bytes i) ∧
      ∃ (r : Nat) (v3 v4 : Value),
        r ≤ cl.toNat ∧
        st'.mem.read32 1048356 = UInt32.ofNat r ∧
        st'.mem.read32 1048352
          = xorFwd st0.mem 1048392 cl.toNat ^^^ xorFwd st0.mem 1048392 r ∧
        s' = { params := [.i32 1048392, .i32 cl],
               locals := [.i32 1048352, v3, v4], values := [] })
    (μ := fun st' _ => (st'.mem.read32 1048356).toNat)
  · -- Invariant on entry: r = cl, accumulator 0 = full ^^^ full.
    refine ⟨by simp [hpg], by simp, ?_, cl.toNat, .i32 0, .i32 0, by omega,
      by simp, by simp, rfl⟩
    intro i hi
    dsimp only
    repeat rw [bytes_write32_frame (by decide) hi]
  · -- One iteration.
    rintro st' s' ⟨hpg', hgl', hpres, r, v3, v4, hr, hcnt, hacc, rfl⟩
    have hr32 : r < 4294967296 := by omega
    apply wp_block_cons
    wp_run
    simp [hcnt, hpg']
    by_cases hr0 : r = 0
    · -- counter = 0: the accumulator has converged to the forward fold.
      simp [hacc, hgl', hr0]
    · -- counter > 0: fold word (r − 1) in and continue.
      have hpos : (0 : UInt32) < UInt32.ofNat r := (zero_lt_ofNat_iff hr32).mpr (by omega)
      simp only [hpos, if_true, ofNat_sub_one (by omega : 0 < r) hr32]
      apply wp_block_cons
      wp_run
      have hltc : UInt32.ofNat (r - 1) < cl := (ofNat_lt_iff (by omega)).mpr (by omega)
      simp [hltc, hpg']
      rw [buf_addr_eq (r - 1)]
      have haddr : ((1048392 : UInt32) + 4 * UInt32.ofNat (r - 1)).toNat
          = 1048392 + 4 * (r - 1) := buf_addr_toNat (by omega)
      have hrd : ∀ m : Mem, (∀ i : Nat, 1048368 ≤ i → m.bytes i = st0.mem.bytes i) →
          m.read32 (1048392 + 4 * UInt32.ofNat (r - 1))
            = st0.mem.read32 (1048392 + 4 * UInt32.ofNat (r - 1)) :=
        fun m hm => read32_congr _ (fun i hi => hm i (by omega)) (by rw [haddr]; omega)
      have hpres1 : ∀ i : Nat, 1048368 ≤ i →
          (st'.mem.write32 1048356 (UInt32.ofNat (r - 1))).bytes i = st0.mem.bytes i := by
        intro i hi
        rw [bytes_write32_frame (by decide) hi]
        exact hpres i hi
      have hsucc : xorFwd st0.mem 1048392 r
          = xorFwd st0.mem 1048392 (r - 1)
            ^^^ st0.mem.read32 (1048392 + 4 * UInt32.ofNat (r - 1)) := by
        conv_lhs => rw [show r = (r - 1) + 1 by omega]
        exact xorFwd_succ _ _ _
      refine ⟨?_, ⟨hgl', ?_, r - 1, by omega, ?_, ?_⟩, ?_⟩
      · simp [Nat.shiftLeft_eq]; omega
      · intro i hi
        rw [bytes_write32_frame (by decide) hi, bytes_write32_frame (by decide) hi]
        exact hpres i hi
      · simp
      · rw [hrd _ hpres1, hacc, hsucc]
        exact xor_shuffle _ _ _
      · omega

/-! ## `func3`: seed, fold both ways, compare

`func3(seed, len)` is the inner `check`. After clamping `cl :=
min(len, 32)` (a two-way `block` split handled in [`func3_at`]), the
suffix below — everything from the `cl` reload onward — zeroes the
128-byte buffer at `1048392`, seeds `cl` words in a loop (with a live
`index < 32` bounds check guarding the store), then builds two slice
views via `func0`, folds forward via `func4` and backward via `func5`,
and hits `unreachable` iff they differ. [`func3_main`] proves the
suffix against any store with the clamp spilled at `1048388`; the two
clamp branches of [`func3_at`] then share it. -/

private def func3Main : Wasm.Program :=
  [
  .block 0 0 [
    .loop 0 0 [
      .block 0 0 [
        .block 0 0 [
          .block 0 0 [
            .block 0 0 [
              .localGet 2,
              .load32 (152 : UInt32),
              .localGet 3,
              .ltU,
              .const (1 : UInt32),
              .and,
              .br_if 0,
              .const (1048596 : UInt32),
              .localSet 6,
              .localGet 2,
              .localGet 2,
              .const (24 : UInt32),
              .add,
              .localGet 3,
              .localGet 6,
              .call 0,
              .localGet 2,
              .load32 (4 : UInt32),
              .localSet 7,
              .localGet 2,
              .load32 (0 : UInt32),
              .localGet 7,
              .call 4,
              .localSet 8,
              .const (1048612 : UInt32),
              .localSet 9,
              .localGet 2,
              .const (8 : UInt32),
              .add,
              .localGet 2,
              .const (24 : UInt32),
              .add,
              .localGet 3,
              .localGet 9,
              .call 0,
              .localGet 2,
              .load32 (12 : UInt32),
              .localSet 10,
              .localGet 8,
              .localGet 2,
              .load32 (8 : UInt32),
              .localGet 10,
              .call 5,
              .ne,
              .const (1 : UInt32),
              .and,
              .br_if 2,
              .br 1
            ],
            .localGet 2,
            .load32 (152 : UInt32),
            .localSet 11,
            .localGet 2,
            .localGet 11,
            .store32 (176 : UInt32),
            .localGet 2,
            .const (1 : UInt32),
            .store32 (180 : UInt32),
            .localGet 11,
            .const (1 : UInt32),
            .add,
            .localSet 12,
            .localGet 2,
            .localGet 0,
            .store32 (184 : UInt32),
            .localGet 2,
            .localGet 12,
            .store32 (188 : UInt32),
            .localGet 0,
            .localGet 12,
            .mul,
            .localSet 13,
            .localGet 2,
            .load32 (152 : UInt32),
            .localSet 14,
            .localGet 2,
            .localGet 13,
            .store32 (168 : UInt32),
            .localGet 2,
            .localGet 14,
            .store32 (172 : UInt32),
            .localGet 13,
            .localGet 14,
            .add,
            .localSet 15,
            .localGet 2,
            .load32 (152 : UInt32),
            .localSet 16,
            .localGet 16,
            .const (32 : UInt32),
            .ltU,
            .const (1 : UInt32),
            .and,
            .br_if 2,
            .br 4
          ],
          .localGet 2,
          .const (192 : UInt32),
          .add,
          .globalSet 0,
          .ret
        ],
        .call 2,
        .unreachable
      ],
      .localGet 2,
      .const (24 : UInt32),
      .add,
      .localGet 16,
      .const (2 : UInt32),
      .shl,
      .add,
      .localGet 15,
      .store32 (0 : UInt32),
      .localGet 2,
      .localGet 2,
      .load32 (152 : UInt32),
      .const (1 : UInt32),
      .add,
      .store32 (152 : UInt32),
      .br 0
    ]
  ],
  .localGet 16,
  .const (32 : UInt32),
  .const (1048628 : UInt32),
  .call 59,
  .unreachable
]

set_option maxHeartbeats 4000000 in
/-- The suffix of `func3` after the clamp: zero the buffer, seed `cl`
words, fold both ways and compare. Holds at any 17-page store whose
stack pointer has been moved to `1048368` by `func3`'s prologue and
whose clamp slot `1048388` holds `cl ≤ 32`. The continuation `Q` only
needs to accept a `Return` with an empty stack, restored stack pointer
and untouched page count. -/
private theorem func3_main (env : HostEnv Unit) (st1 : Store Unit) (Q : Assertion Unit)
    (seed len cl : UInt32)
    (hpg : st1.mem.pages = 17)
    (hgl : st1.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000])
    (hcnt0 : st1.mem.read32 1048520 = 0)
    (hcl : cl.toNat ≤ 32)
    (hQ : ∀ st'' : Store Unit, st''.mem.pages = 17 →
        st''.globals.globals = [.i32 1048560, .i32 1049997, .i32 1050000] →
        Q (.Return st'' [])) :
    wp «module» func3Main Q st1
      { params := [.i32 seed, .i32 len],
        locals := [.i32 1048368, .i32 cl, .i32 128, .i32 0, .i32 0, .i32 0, .i32 0,
                   .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        values := [] } env := by
  unfold func3Main
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000] ∧
      ∃ (j : Nat) (v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : Value),
        j ≤ cl.toNat ∧
        st'.mem.read32 1048520 = UInt32.ofNat j ∧
        s' = { params := [.i32 seed, .i32 len],
               locals := [.i32 1048368, .i32 cl, v4, v5, v6, v7, v8, v9, v10,
                          v11, v12, v13, v14, v15, v16],
               values := [] })
    (μ := fun st' _ => cl.toNat - (st'.mem.read32 1048520).toNat)
  · -- Invariant on entry: counter 0.
    exact ⟨hpg, hgl, 0, .i32 128, .i32 0, .i32 0, .i32 0, .i32 0,
      .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
      by omega, by simp [hcnt0], rfl⟩
  · -- One iteration: seed word j, or (when j = cl) compare the folds.
    rintro st' s' ⟨hpg', hgl', j, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14,
      v15, v16, hj, hcnt, rfl⟩
    have hj32 : j < 4294967296 := by omega
    apply wp_block_cons
    apply wp_block_cons
    apply wp_block_cons
    apply wp_block_cons
    wp_run
    simp [hcnt, hpg']
    by_cases hlt : UInt32.ofNat j < cl
    · -- Seeding path: write `seed·(j+1)+j` to buffer word j, bump the counter.
      have hjlt : j < cl.toNat := (ofNat_lt_iff hj32).mp hlt
      have hj32lt : UInt32.ofNat j < 32 := by
        rw [ofNat_lt_iff hj32, show (32 : UInt32).toNat = 32 from rfl]
        omega
      simp [hlt, hj32lt]
      -- Buffer store in bounds; counter survives it (the word lands at
      -- `1048392 + 4j ≤ 1048516`, strictly below the counter at `1048520`).
      rw [if_neg (by simp [Nat.shiftLeft_eq]; omega), buf_addr_eq j]
      have haddr : ((1048392 : UInt32) + 4 * UInt32.ofNat j).toNat = 1048392 + 4 * j :=
        buf_addr_toNat (by omega)
      rw [read32_write32_disjoint _ _ _ _
        (Or.inr (by rw [haddr, show (1048520 : UInt32).toNat = 1048520 from rfl]; omega))]
      simp [hcnt, hgl', one_add_ofNat (show j + 1 < 4294967296 by omega)]
      exact ⟨⟨j + 1, by omega,
        by rw [UInt32.add_comm]; exact one_add_ofNat (by omega)⟩, by omega⟩
    · -- Comparison path: j = cl; build the views, fold both ways, return.
      have hje : j = cl.toNat := by
        have := (ofNat_lt_iff (cl := cl) hj32).not.mp hlt
        omega
      simp only [hlt, if_false]
      simp
      -- First slice view: `func0` writes `(1048392, cl)` to `1048368/1048372`.
      refine wp_call_at
        (Post := fun st2 vs => vs = [] ∧ st2.mem.pages = 17 ∧
          st2.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000] ∧
          st2.mem.read32 1048368 = 1048392 ∧ st2.mem.read32 (1048368 + 4) = cl ∧
          ∀ i : Nat, 1048392 ≤ i → st2.mem.bytes i = st'.mem.bytes i)
        (func0_at env _ 1048392 cl 1048596 1048368 hpg' hgl' hcl (Or.inl rfl)) ?_
      rintro st2 vs ⟨rfl, hpg2, hgl2, hr0, hr4, hb2⟩
      have hr4' : st2.mem.read32 1048372 = cl := by
        rw [show (1048372 : UInt32) = 1048368 + 4 from rfl]
        exact hr4
      wp_run
      simp [hr0, hr4', hpg2]
      -- Forward fold.
      refine wp_call_at
        (Post := fun st3 vs => vs = [.i32 (xorFwd st2.mem 1048392 cl.toNat)] ∧
          st3.mem.pages = 17 ∧
          st3.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000] ∧
          ∀ i : Nat, 1048392 ≤ i → st3.mem.bytes i = st2.mem.bytes i)
        (func4_at env _ cl [] hpg2 hgl2 hcl) ?_
      rintro st3 vs ⟨rfl, hpg3, hgl3, hb3⟩
      wp_run
      simp
      -- Second slice view, at `1048376/1048380`.
      refine wp_call_at
        (Post := fun st4 vs => vs = [] ∧ st4.mem.pages = 17 ∧
          st4.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000] ∧
          st4.mem.read32 1048376 = 1048392 ∧ st4.mem.read32 (1048376 + 4) = cl ∧
          ∀ i : Nat, 1048392 ≤ i → st4.mem.bytes i = st3.mem.bytes i)
        (func0_at env _ 1048392 cl 1048612 1048376 hpg3 hgl3 hcl (Or.inr rfl)) ?_
      rintro st4 vs ⟨rfl, hpg4, hgl4, hs0, hs4, hb4⟩
      have hs4' : st4.mem.read32 1048380 = cl := by
        rw [show (1048380 : UInt32) = 1048376 + 4 from rfl]
        exact hs4
      wp_run
      simp [hs0, hs4', hpg4]
      -- Backward fold; its value is the forward fold of *its* entry store.
      refine wp_call_at
        (Post := fun st5 vs => vs = [.i32 (xorFwd st4.mem 1048392 cl.toNat),
            .i32 (xorFwd st2.mem 1048392 cl.toNat)] ∧
          st5.mem.pages = 17 ∧
          st5.globals.globals = [.i32 1048368, .i32 1049997, .i32 1050000])
        (func5_at env _ cl [.i32 (xorFwd st2.mem 1048392 cl.toNat)] hpg4 hgl4 hcl) ?_
      rintro st5 vs ⟨rfl, hpg5, hgl5⟩
      -- The two folds agree: the buffer never changed between the calls.
      have hbb : xorFwd st4.mem 1048392 cl.toNat = xorFwd st2.mem 1048392 cl.toNat :=
        xorFwd_congr (fun i hi => (hb4 i hi).trans (hb3 i hi)) cl.toNat hcl
      wp_run
      simp [hbb, hgl5]
      exact hQ _ (by simp [hpg5]) (by simp)

set_option maxHeartbeats 4000000 in
/-- `func3` (the inner `check`): clamp `cl := min(len, 32)`, then run
[`func3_main`]. Terminates with an empty stack, the stack pointer
restored to `1048560` and the page count untouched. -/
private theorem func3_at (env : HostEnv Unit) (st0 : Store Unit) (seed len : UInt32)
    (hpg : st0.mem.pages = 17)
    (hgl : st0.globals.globals = [.i32 1048560, .i32 1049997, .i32 1050000]) :
    TerminatesWith env «module» 3 st0 [.i32 len, .i32 seed]
      (fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
        st'.globals.globals = [.i32 1048560, .i32 1049997, .i32 1050000]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32],
           [.i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32,
            .i32, .i32, .i32], func3, []⟩) rfl
  unfold func3
  wp_run
  simp only [hgl, hpg]
  simp [hpg]
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  simp [hpg]
  by_cases h32 : (32 : UInt32) < len
  · -- len > 32: the clamp stores 32.
    simp only [h32, if_true, show (1 &&& 1 : UInt32) = 1 from rfl]
    apply func3_main env _ _ seed len 32 (by simp [hpg]) (by simp) (by simp) (by decide)
    exact fun st'' h1 h2 => ⟨h1, h2⟩
  · -- len ≤ 32: the clamp stores len itself.
    have hlen : len.toNat ≤ 32 := by
      have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp h32)
      rw [show (32 : UInt32).toNat = 32 from rfl] at this
      exact this
    simp only [h32, if_false, show (1 &&& 0 : UInt32) = 0 from rfl]
    apply func3_main env _ _ seed len len (by simp [hpg]) (by simp) (by simp) hlen
    exact fun st'' h1 h2 => ⟨h1, h2⟩

@[proves Project.XorSum.Spec.CheckSpec]
theorem check_correct : CheckSpec := by
  intro env initial seed len hinit
  subst hinit
  have hp : («module».initialStore : Store Unit).mem.pages = 17 := by rfl
  have hg : («module».initialStore : Store Unit).globals.globals
      = [.i32 1048576, .i32 1049997, .i32 1050000] := by rfl
  -- `func6` is the exported `check` wrapper: claim a 16-byte frame,
  -- spill both arguments, forward to `func3`, release the frame.
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32, .i32], [.i32], func6, []⟩) rfl
  unfold func6
  wp_run
  simp only [hg, hp]
  simp [hp]
  refine wp_call_at
    (Post := fun st' vs => vs = [] ∧ st'.mem.pages = 17 ∧
      st'.globals.globals = [.i32 1048560, .i32 1049997, .i32 1050000])
    (func3_at env _ seed len (by simp [hp]) (by simp)) ?_
  rintro st' vs ⟨rfl, hpg', hgl'⟩
  wp_run
  simp [hgl']

end Project.XorSum.Spec
