import Project.NumInteger.Program

/-!
# Specification for `gcd_u64`

The exported `gcd_u64` function implements the binary GCD (Stein's
algorithm) on `u64` operands. By the `num-integer` convention the function
returns `0` on `(0, 0)`.

Unoptimized (`opt-level=0`) pipeline: the export `gcd_u64` is `func2`,
which spills its arguments to a shadow-stack frame and calls `func0`;
`func0` in turn spills the arguments to its own frame and calls `func1`
with *pointers* into linear memory; `func1` runs the whole Stein loop
through `load64`/`store64` at frame offsets instead of locals.
-/

namespace Project.NumInteger.Spec

open Wasm

set_option maxRecDepth 1048576

/-- Local aliases for the `UInt64` ↔ `Nat` bridge lemmas used in this
proof. The actual content lives in `CodeLib.UInt64`. -/
private alias uint64_shr_ctz_odd    := UInt64.shr_ctz_toNat_odd
private alias uint64_shr_ctz_pos    := UInt64.shr_ctz_ne_zero
private alias uint64_recombine_loop := UInt64.recombine_loop
private alias uint64_loop_step_x    := UInt64.stein_step_x
private alias uint64_loop_step_y    := UInt64.stein_step_y

/-! ## Top spec -/

/-- The exported `gcd_u64` returns the greatest common divisor of two
`u64` operands, computed by the binary-GCD (Stein's) algorithm.

The `initial = «module».initialStore` hypothesis is load-bearing: the
unoptimized code spills every intermediate to a shadow-stack frame in
linear memory (`global 0` is the stack pointer, initialized to
`1048576`; the module allocates 16 pages = `1048576` bytes). Under an
adversarial store (e.g. `mem.pages = 0` or a garbage stack pointer) the
very first spill would trap, so the spec genuinely needs the canonical
instantiation — unlike the old locals-only build, which held for every
store.

Informal spec:
For any inputs `a b : UInt64`, the wasm export `gcd_u64` terminates and
leaves a single i64 on the value stack equal to `Nat.gcd a.toNat b.toNat`
(coerced back into `UInt64`). The `num-integer` convention `gcd(0, 0) = 0`
is preserved. -/
@[spec_of "rust-exported" "num_integer::gcd_u64"]
def GcdU64Spec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    initial = «module».initialStore →
    -- Args are passed in stack order (top first). The Wasm caller pushes
    -- `a` then `b`, so the operand stack handed to `run` is `[b, a]` —
    -- which `run` reverses on entry to make local 0 = a, local 1 = b.
    TerminatesWith env «module» 2 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])

/-! ## Memory framing lemmas

`func1` keeps the whole Stein state in its 128-byte shadow-stack frame,
so the proof needs read-after-write algebra over the function-model
`Mem` for 64-bit (and the 32-bit scratch slots holding `ctz` shift
counts). The disjointness side conditions are stated on `toNat` byte
ranges; in this proof every address is a concrete numeral, so `simp`
discharges them and the lemmas can act as (conditional) `simp` rewrites
that resolve any read through the stack of frame writes. -/

@[simp] private theorem write64_pages (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).pages = m.pages := rfl

@[simp] private theorem write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

private theorem write64_bytes_of_disjoint (m : Mem) (a : UInt32) (v : UInt64) (i : Nat)
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

private theorem write32_bytes_of_disjoint (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

/-- A 64-bit read sees the value of a same-address 64-bit write. -/
@[simp] private theorem read64_write64_same (m : Mem) (a : UInt32) (v : UInt64) :
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

/-- A 64-bit read is unaffected by a 64-bit write to a disjoint 8-byte range. -/
@[simp] private theorem read64_write64_disjoint (m : Mem) (a b : UInt32) (v : UInt64)
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

/-- A 64-bit read is unaffected by a 32-bit write to a disjoint 4-byte range. -/
@[simp] private theorem read64_write32_disjoint (m : Mem) (a b v32 : UInt32)
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

/-- A 32-bit read is unaffected by a 64-bit write to a disjoint 8-byte range. -/
@[simp] private theorem read32_write64_disjoint (m : Mem) (a b : UInt32) (v : UInt64)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 8 ≤ b.toNat) :
    (m.write64 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write64_bytes_of_disjoint m a v b.toNat (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

/-- A 32-bit read is unaffected by a 32-bit write to a disjoint 4-byte range. -/
@[simp] private theorem read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_of_disjoint m a v b.toNat (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

/-! ## A store-specific `call` rule

`wp_call_cons` consumes a `FuncSpec`, which quantifies over *all*
initial stores. That is unusable here: `func0`/`func1` spill to linear
memory and trap on a too-small store, so no total `FuncSpec` exists for
them. We step `call` against a `TerminatesWith` *at the concrete current
store* instead (`wp_call_at` is the interpreter-side core of this). -/

private theorem wp_call_of_terminates {α : Type} {env : HostEnv α} {m : Module}
    {id : Nat} {Q : Assertion α} {rest : Program} {st : Store α} {s : Locals}
    {P : Store α → List Value → Prop}
    (h : TerminatesWith env m id st s.values P)
    (hPost : ∀ st' vs, P st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env :=
  wp_call_at h hPost

/-! ## Bridging the `opt-level=0` shift plumbing

The unoptimized code routes every `ctz` shift count through
`wrapI64` → `i32.and 63` → `extendUI32` before shifting. For a nonzero
operand `ctz64 64 v < 64`, so that round-trip is the identity and the
shift amount collapses to the `UInt64.ofNat (ctz64 64 v) % 64` shape the
`CodeLib.UInt64` Stein lemmas are stated in. -/

private theorem shift_amt_eq (v : UInt64) (hv : v ≠ 0) :
    ((63 : UInt64) &&& UInt64.ofNat (ctz64 64 v % 4294967296)) % 64
      = UInt64.ofNat (ctz64 64 v) % 64 := by
  have hc : ctz64 64 v < 64 := UInt64.ctz64_lt v hv
  have hsz64 : UInt64.size = 18446744073709551616 := rfl
  rw [Nat.mod_eq_of_lt (by omega : ctz64 64 v < 4294967296)]
  congr 1
  apply UInt64.toNat.inj
  have h1 : (UInt64.ofNat (ctz64 64 v)).toNat = ctz64 64 v :=
    UInt64.toNat_ofNat_of_lt' (by omega)
  rw [UInt64.toNat_and, h1]
  have h63 : (63 : UInt64).toNat = 63 := rfl
  rw [h63, Nat.and_comm]
  have hmask : ctz64 64 v &&& 63 = ctz64 64 v % 64 := by
    have h := Nat.and_two_pow_sub_one_eq_mod (ctz64 64 v) 6
    norm_num at h
    exact h
  rw [hmask, Nat.mod_eq_of_lt hc]

/-- `Nat`-level mirror of `shift_amt_eq`, in the shape `simp` leaves after
pushing `toNat` through the shift plumbing. -/
private theorem nat_shift_amt_eq (v : UInt64) (hv : v ≠ 0) :
    (63 &&& ctz64 64 v % 4294967296 % 18446744073709551616) % 64 = ctz64 64 v % 64 := by
  have hc : ctz64 64 v < 64 := UInt64.ctz64_lt v hv
  rw [Nat.mod_eq_of_lt (by omega : ctz64 64 v < 4294967296),
      Nat.mod_eq_of_lt (by omega : ctz64 64 v < 18446744073709551616),
      Nat.and_comm]
  have hmask := Nat.and_two_pow_sub_one_eq_mod (ctz64 64 v) 6
  norm_num at hmask
  rw [hmask]
  omega

/-- `UInt64` or is commutative (the code computes `a ||| b`; the
`CodeLib.UInt64` recombination lemmas are stated with `b ||| a`). -/
private theorem uint64_or_comm (a b : UInt64) : a ||| b = b ||| a := by
  bv_decide

private theorem sub_ne_zero_of_ne (x y : UInt64) (h : x ≠ y) : x - y ≠ 0 := by
  bv_decide

/-- `a ||| b ≠ 0` when `a ≠ 0`. -/
private theorem or_ne_zero_left (a b : UInt64) (ha : a ≠ 0) : a ||| b ≠ 0 := by
  bv_decide

/-! ## `func1`: the Stein loop over the shadow-stack frame

`func1` receives two *pointers* (i32 addresses `1048544`, `1048552` at
the single call site), allocates a 128-byte red-zone frame at
`global 0 − 128 = 1048416`, copies the pointees to frame offsets
16 / 24, and runs the subtract-and-halve loop entirely through
`load64`/`store64` on those two slots (offsets 36–124 are write-only
scratch bookkeeping). -/

theorem func1_terminates (env : HostEnv Unit) (st1 : Store Unit) (a b : UInt64)
    (hpg : st1.mem.pages = 16)
    (hg0 : st1.globals.globals[0]? = some (.i32 1048544))
    (hra : st1.mem.read64 1048544 = a)
    (hrb : st1.mem.read64 1048552 = b) :
    TerminatesWith env «module» 1 st1 [.i32 1048552, .i32 1048544]
      (fun st' vs => st'.globals = st1.globals ∧
        vs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32],
           [.i32, .i64, .i32, .i64, .i32, .i64, .i32, .i64, .i64, .i32, .i64, .i64, .i32],
           func1, [.i64]⟩) rfl
  unfold func1
  wp_run
  simp [hg0, hpg, hra, hrb]
  -- Enter OUTER, MIDDLE, INNER blocks.
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  simp
  by_cases ha0 : a = 0
  · -- a = 0: first br_if fires; MIDDLE tail stores a ||| b = b at offset 8, br 1 exits.
    subst ha0
    simp
    simp [hpg]
  · simp [ha0]
    by_cases hb0 : b = 0
    · -- b = 0: second br_if doesn't fire; INNER falls through to the same tail.
      subst hb0
      simp
      simp [hpg]
    · -- Both nonzero: br_if 1 fires; enter the Stein setup, then the loop.
      simp [hb0]
      simp only [hpg]
      refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num, by norm_num, ?_⟩
      -- Loop invariant: the frame slots at offsets 16/24 hold odd, nonzero
      -- values whose gcd is the gcd of the odd parts of `a` and `b`; the
      -- scratch slots (l9–l14 and frame offsets 48–124) are unconstrained.
      apply wp_loop_cons
        (Inv := fun st' s' =>
          st'.mem.pages = 16 ∧ st'.globals = st1.globals ∧
          ∃ (x y : UInt64) (w9 w10 w11 w12 w13 w14 : Value),
            st'.mem.read64 1048432 = x ∧
            st'.mem.read64 1048440 = y ∧
            x ≠ 0 ∧ y ≠ 0 ∧ x.toNat % 2 = 1 ∧ y.toNat % 2 = 1 ∧
            Nat.gcd x.toNat y.toNat
              = Nat.gcd (a.toNat >>> (ctz64 64 a % 64)) (b.toNat >>> (ctz64 64 b % 64)) ∧
            s' = { params := [.i32 1048544, .i32 1048552],
                   locals := [.i32 1048416, .i64 (a ||| b),
                              .i32 (UInt32.ofNat (ctz64 64 (a ||| b) % 4294967296)),
                              .i64 a, .i32 (UInt32.ofNat (ctz64 64 a % 4294967296)),
                              .i64 b, .i32 (UInt32.ofNat (ctz64 64 b % 4294967296)),
                              w9, w10, w11, w12, w13, w14],
                   values := [] })
        (μ := fun st' _ => (st'.mem.read64 1048432).toNat + (st'.mem.read64 1048440).toNat)
      · -- Initial invariant: x = a-odd, y = b-odd.
        refine ⟨by simp [hpg], rfl,
          a >>> (UInt64.ofNat (ctz64 64 a) % 64),
          b >>> (UInt64.ofNat (ctz64 64 b) % 64),
          .i64 0, .i64 0, .i32 0, .i64 0, .i64 0, .i32 0,
          ?_, ?_, uint64_shr_ctz_pos a ha0, uint64_shr_ctz_pos b hb0,
          uint64_shr_ctz_odd a ha0, uint64_shr_ctz_odd b hb0, ?_, rfl⟩
        · simp [shift_amt_eq a ha0]
        · simp [shift_amt_eq b hb0]
        · simp [UInt64.toNat_shiftRight]
      · -- Per-iteration step.
        rintro st' s' ⟨hpg', hgl', x, y, w9, w10, w11, w12, w13, w14,
          hx, hy, hxne, hyne, hxodd, hyodd, hgcd, rfl⟩
        apply wp_block_cons
        wp_run
        simp [hpg', hx, hy]
        by_cases hxy : x = y
        · -- Loop exits: slots are equal; recombine with the saved ctz(a|||b).
          simp [hxy, hgl']
          rw [shift_amt_eq (a ||| b) (or_ne_zero_left a b ha0), uint64_or_comm a b]
          rw [hxy] at hgcd
          exact uint64_recombine_loop a b y ha0 hb0 hgcd
        · -- Loop continues: enter the comparison block.
          simp [hxy]
          apply wp_block_cons
          wp_run
          simp [hpg', hx, hy]
          by_cases hlt : y < x
          · -- x > y: subtract y from the offset-16 slot and halve it.
            simp [hlt]
            obtain ⟨hxne', hxodd', hgcd', hdec⟩ :=
              uint64_loop_step_x x y hxne hyne hxodd hyodd hlt
            have hsub_ne : x - y ≠ 0 := sub_ne_zero_of_ne x y hxy
            rw [shift_amt_eq _ hsub_ne, nat_shift_amt_eq _ hsub_ne]
            exact ⟨⟨hgl', hxne', hyne, hxodd', hyodd, hgcd'.trans hgcd⟩, hdec⟩
          · -- x < y: subtract x from the offset-24 slot and halve it.
            simp [hlt]
            obtain ⟨hyne', hyodd', hgcd', hdec⟩ :=
              uint64_loop_step_y x y hxne hyne hxodd hyodd hlt hxy
            have hsub_ne : y - x ≠ 0 := sub_ne_zero_of_ne y x (fun h => hxy h.symm)
            rw [shift_amt_eq _ hsub_ne, nat_shift_amt_eq _ hsub_ne]
            exact ⟨⟨hgl', hxne, hyne', hxodd, hyodd', hgcd'.trans hgcd⟩, hdec⟩

/-! ## `func0`: spill args to the frame and call `func1` -/

theorem func0_terminates (env : HostEnv Unit) (st0 : Store Unit) (a b : UInt64)
    (hpg : st0.mem.pages = 16)
    (hg0 : st0.globals.globals[0]? = some (.i32 1048560)) :
    TerminatesWith env «module» 0 st0 [.i64 b, .i64 a]
      (fun st' vs => 0 < st'.globals.globals.length ∧
        vs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  have hlen : 0 < st0.globals.globals.length := by
    rcases List.getElem?_eq_some_iff.mp hg0 with ⟨h, _⟩
    omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i64], [.i32, .i64], func0, [.i64]⟩) rfl
  unfold func0
  wp_run
  simp [hg0, hpg]
  apply wp_call_of_terminates
    (func1_terminates env _ a b (by simp [hpg]) (by simp [hlen]) (by simp)
      (by simp))
  rintro st' vs ⟨hgl, rfl⟩
  wp_run
  simp [hgl, List.length_set]
  simp [hlen]

/-! ## The export wrapper (`func2` = `gcd_u64`) -/

@[proves Project.NumInteger.Spec.GcdU64Spec]
theorem gcd_u64_correct : GcdU64Spec := by
  intro env initial a b hinit
  subst hinit
  have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := by
    rfl
  have hp : («module».initialStore : Store Unit).mem.pages = 16 := by rfl
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i64], [.i32, .i64], func2, [.i64]⟩) rfl
  unfold func2
  wp_run
  simp [hg, hp]
  apply wp_call_of_terminates
    (func0_terminates env _ a b (by simp [hp]) (by simp [List.getElem?_set]; decide))
  rintro st' vs ⟨hgl, rfl⟩
  wp_run
  simp [List.getElem?_eq_getElem hgl]

end Project.NumInteger.Spec
