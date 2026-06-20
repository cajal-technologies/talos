import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Std.Tactic.BVDecide

/-! ## Bignum predicates over `∀ n : ℕ†` (memory-backed)

    Convention (fixed): a natural number is a little-endian base-2³² limb
    array living in linear memory. A function takes scalars `(base : i32,
    len : i32)`; the `len` limbs are the 32-bit words at `base, base+4, …`.
    `len = 0` is the number 0. Because there is no top-limb-nonzero
    precondition, quantifying over all limb arrays quantifies over `ℕ†`.

    **`ℕ†` (the representable naturals) — non-standard notation, introduced
    here.** Pointers and lengths are fixed width: `len : UInt32`, so a number
    has at most `2³² − 1` limbs and hence `n < 2 ^ (32 · (2³² − 1))`. `ℕ†` is
    this prefix of `ℕ` — every natural that fits in the pointer width. The
    proofs bound the value only by this structural ceiling; within `ℕ†`,
    coverage is total. `ℕ† ⊊ ℕ`.

    Step 1: `natTrue`, the do-nothing program. It has
    the right signature `(base, len)` and always returns `1`, regardless of
    memory. It exists to pin down the calling convention and the proof
    harness before we read any limbs. -/

namespace Wasm

/-- The do-nothing predicate: ignore the bignum, always return `1`. -/
def natTrue : Program := [.const 1]

/-- `natTrue` returns `1` on top of the stack for every `(base, len)` and
    every store — the memory is never touched. -/
theorem natTrue_spec (m : Module) (st : Store Unit) (base len : UInt32) :
    wp m natTrue
        (fun c => c = .Fallthrough st
                    { params := [.i32 base, .i32 len], locals := [],
                      values := [.i32 1] })
        st { params := [.i32 base, .i32 len], locals := [], values := [] } := by
  unfold natTrue
  wp_run

/-! ### Step 2: is-even = low bit of the first limb.

    Read the byte at `base`, mask its low bit, and `eqz`. The execution spec
    `natIsEven_exec` requires only that the byte at `base` is in-bounds (rules
    out the load trap), and states the result purely in terms of that byte.
    Step 3 then ties it to the *number's* parity — every higher limb
    contributes a multiple of `2³²`, which is even, so the number is even iff
    its lowest byte is — which is where the first-limb requirement (`1 ≤ len`)
    enters. -/

def natIsEven : Program := [.localGet 0, .load8U 0, .const 1, .and, .eqz]

/-- Execution spec: `natIsEven` returns `1` exactly when the low bit of the
    byte at `base` is clear, `0` otherwise. Mirrors `isEvenSpec`, but the
    operand comes from memory rather than a register. -/
theorem natIsEven_exec (m : Module) (st : Store Unit) (base len : UInt32)
    (hbase : base.toNat + 1 ≤ st.mem.pages * 65536) :
    wp m natIsEven
        (fun c => c = .Fallthrough st
                    { params := [.i32 base, .i32 len], locals := [],
                      values := [.i32 (if (1 : UInt32) &&& (st.mem.read8 base).toUInt32 = 0
                                       then 1 else 0)] })
        st { params := [.i32 base, .i32 len], locals := [], values := [] } := by
  unfold natIsEven
  wp_run
  have hnt : ¬ (base.toNat + 0 + 1 > st.mem.pages * 65536) := by omega
  simp [hnt]

/-! ### Step 3: closing the loop — the program decides parity of the number.

    `denote` (`⟦·⟧`) is the reusable abstraction: the little-endian base-2³²
    value of a limb list, head = least significant. The folding lemmas are
    its interface. Then we read the limbs out of memory (`memLimbs`) and
    prove `natIsEven` returns `1` exactly when `⟦limbs⟧` is even. -/

/-- `⟦·⟧`: little-endian base-2³² value of a limb list (head = least significant). -/
def denote : List UInt32 → Nat
  | []      => 0
  | x :: xs => x.toNat + 2 ^ 32 * denote xs

@[simp] theorem denote_nil : denote [] = 0 := rfl

theorem denote_cons (x : UInt32) (xs : List UInt32) :
    denote (x :: xs) = x.toNat + 2 ^ 32 * denote xs := rfl

/-- Folding in a most-significant limb: `⟦xs ++ [hi]⟧ = ⟦xs⟧ + hi·2^(32·|xs|)`. -/
theorem denote_append_singleton (xs : List UInt32) (hi : UInt32) :
    denote (xs ++ [hi]) = denote xs + hi.toNat * 2 ^ (32 * xs.length) := by
  induction xs with
  | nil => simp [denote_cons]
  | cons x xs ih =>
      simp only [List.cons_append, denote_cons, ih, List.length_cons]
      rw [Nat.mul_succ, pow_add]
      ring

/-- Parity of the whole number is the parity of its least-significant limb:
    every higher limb contributes a multiple of `2³²`, which is even. -/
theorem denote_cons_mod_two (x : UInt32) (xs : List UInt32) :
    denote (x :: xs) % 2 = x.toNat % 2 := by
  rw [denote_cons]
  have h : (2 : Nat) ^ 32 = 2 * 2147483648 := by norm_num
  rw [h]
  omega

/-- The limb list held in memory: `len` little-endian 32-bit words at `base`. -/
def memLimbs (mem : Mem) (base : UInt32) : Nat → List UInt32
  | 0       => []
  | len + 1 => mem.read32 base :: memLimbs mem (base + 4) len

/-- For a `UInt32`, `% 2 = 0` is exactly the cleared low bit. -/
theorem u32_even_iff (v : UInt32) : v.toNat % 2 = 0 ↔ v &&& 1 = 0 := by
  have hlow : v.toNat % 2 = (v &&& 1).toNat := by
    rw [UInt32.toNat_and, show (1 : UInt32).toNat = 1 from rfl, Nat.and_one_is_mod]
  rw [hlow, show (0 : Nat) = (0 : UInt32).toNat from rfl, UInt32.toNat_inj]

/-- Low bit of a little-endian 32-bit load = low bit of its first byte; the
    higher three bytes are shifted past bit 0, so they can't affect parity. -/
theorem read32_low_eq_read8 (mem : Mem) (a : UInt32) :
    (mem.read32 a &&& 1 = 0) ↔ (1 : UInt32) &&& (mem.read8 a).toUInt32 = 0 := by
  unfold Mem.read32 Mem.read8; bv_decide

/-- Parity of the in-memory number (with at least one limb) ↔ the program's
    low-bit test on the first byte. The bridge from `⟦limbs⟧` to the load. -/
theorem even_memLimbs_succ_iff (st : Store Unit) (base : UInt32) (k : Nat) :
    Even (denote (memLimbs st.mem base (k + 1)))
      ↔ (1 : UInt32) &&& (st.mem.read8 base).toUInt32 = 0 := by
  show Even (denote (st.mem.read32 base :: memLimbs st.mem (base + 4) k)) ↔ _
  rw [Nat.even_iff, denote_cons_mod_two, u32_even_iff, read32_low_eq_read8]

/-- The value `natIsEven`/`natIsEvenTotal` produce on the low-bit test equals
    the parity verdict, whenever there is a first limb (`len.toNat = k + 1`). -/
theorem byteTest_eq_evenVerdict (st : Store Unit) (base : UInt32) (k : Nat) :
    (if (1 : UInt32) &&& (st.mem.read8 base).toUInt32 = 0 then (1 : UInt32) else 0)
      = (if Even (denote (memLimbs st.mem base (k + 1))) then 1 else 0) := by
  by_cases h : (1 : UInt32) &&& (st.mem.read8 base).toUInt32 = 0
  · rw [if_pos h, if_pos ((even_memLimbs_succ_iff st base k).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((even_memLimbs_succ_iff st base k).mp hh))]

/-- **Closing the loop (≥ 1 limb).** `natIsEven` returns `1` exactly when the
    number held in memory — `⟦limbs⟧` for the `len` limbs at `base` — is even.
    `1 ≤ len` gives a first limb; `hbase` rules out the load trap. -/
theorem natIsEven_correct (m : Module) (st : Store Unit) (base len : UInt32)
    (hlen : 1 ≤ len.toNat)
    (hbase : base.toNat + 1 ≤ st.mem.pages * 65536) :
    wp m natIsEven
        (fun c => c = .Fallthrough st
                    { params := [.i32 base, .i32 len], locals := [],
                      values := [.i32 (if Even (denote (memLimbs st.mem base len.toNat))
                                       then 1 else 0)] })
        st { params := [.i32 base, .i32 len], locals := [], values := [] } := by
  obtain ⟨k, hk⟩ : ∃ k, len.toNat = k + 1 := ⟨len.toNat - 1, by omega⟩
  rw [hk, ← byteTest_eq_evenVerdict st base k]
  exact natIsEven_exec m st base len hbase

/-! ### Step 4: total over all `n : ℕ†` — guard the `len = 0` case.

    A structured `if` on `len == 0` returns `1` for the empty number `0`
    (which is even) and otherwise runs the low-bit test. Crucially the load
    sits in the `else` arm, so it never executes — and never traps — when
    there is no first limb. Now the in-bounds hypothesis is only needed when
    `len ≠ 0`, and the spec is unconditional over every `n : ℕ†`. -/

def natIsEvenTotal : Program := [
  .localGet 1, .eqz,
  .iff 0 1
    [.const 1]
    [.localGet 0, .load8U 0, .const 1, .and, .eqz]
]

theorem natIsEvenTotal_correct (m : Module) (st : Store Unit) (base len : UInt32)
    (hbase : len ≠ 0 → base.toNat + 1 ≤ st.mem.pages * 65536) :
    wp m natIsEvenTotal
        (fun c => c = .Fallthrough st
                    { params := [.i32 base, .i32 len], locals := [],
                      values := [.i32 (if Even (denote (memLimbs st.mem base len.toNat))
                                       then 1 else 0)] })
        st { params := [.i32 base, .i32 len], locals := [], values := [] } := by
  unfold natIsEvenTotal
  wp_run
  apply wp_iff_cons (c := if len = 0 then (1 : UInt32) else 0) (vs := []) rfl
  by_cases hlen0 : len = 0
  · -- `len = 0`: the number is `0`, which is even, so we must return `1`.
    subst hlen0
    simp only [ne_eq, if_true]
    wp_run
    simp [memLimbs]
  · -- `len ≠ 0`: run the low-bit test; the load is in bounds by `hbase`.
    have hne : len.toNat ≠ 0 := by
      intro h; exact hlen0 (UInt32.toNat_inj.mp (by simp [h]))
    obtain ⟨k, hk⟩ : ∃ k, len.toNat = k + 1 := ⟨len.toNat - 1, by omega⟩
    have hb : base.toNat + 1 ≤ st.mem.pages * 65536 := hbase hlen0
    simp only [if_neg hlen0, ne_eq, not_true_eq_false, if_false]
    wp_run
    have hnt : ¬ (base.toNat + 0 + 1 > st.mem.pages * 65536) := by omega
    rw [hk]
    simp [hnt, ← byteTest_eq_evenVerdict st base k]

/-! ### Step 5: is-zero — the first loop over limbs.

    `n = 0 ↔ every limb is 0`. The program ORs all limbs into an accumulator
    and returns `eqz acc`. The loop carries a pointer `p` and a remaining
    count `c` in the two params, the OR accumulator in local 2, and exits when
    `c = 0`. This establishes the loop-over-limbs invariant pattern the rest of
    the steps reuse.

    The invariant decouples two concerns:
    * **bounds** `p.toNat + 4·c ≤ pages·65536` — keeps every `load32` in range;
    * **answer** `⟦whole⟧ = 0 ↔ (acc = 0 ∧ ⟦remaining limbs⟧ = 0)` — at exit
      (`c = 0`, no limbs left) this collapses to `⟦whole⟧ = 0 ↔ acc = 0`. -/

/-- `a ||| b = 0` iff both are `0`: ORing in a limb keeps the accumulator zero
    exactly when the limb was zero too. -/
theorem u32_or_eq_zero (a b : UInt32) : (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := by
  bv_decide

/-- A `UInt32` is `0` iff its `toNat` is. -/
theorem u32_toNat_eq_zero (v : UInt32) : v.toNat = 0 ↔ v = 0 := by
  rw [show (0 : Nat) = (0 : UInt32).toNat from rfl, UInt32.toNat_inj]

/-- `⟦read32 p :: rest⟧ = 0` iff the head limb and the rest are both `0`. -/
theorem denote_cons_eq_zero (x : UInt32) (xs : List UInt32) :
    denote (x :: xs) = 0 ↔ (x = 0 ∧ denote xs = 0) := by
  rw [denote_cons, ← u32_toNat_eq_zero]
  constructor
  · intro h; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; omega

def natIsZero : Program := [
  .const 0, .localSet 2,                                      -- acc := 0
  .loop 0 0 [
    .block 0 0 [
      .localGet 1, .eqz, .br_if 0,                            -- if c == 0, exit loop
      .localGet 2, .localGet 0, .load32 0, .or, .localSet 2,  -- acc |= load32(p)
      .localGet 0, .const 4, .add, .localSet 0,               -- p += 4
      .localGet 1, .const 1, .sub, .localSet 1,               -- c -= 1
      .br 1                                                   -- continue loop
    ]
  ],
  .localGet 2, .eqz                                           -- return eqz acc
]

/-- **is-zero correct over `ℕ†`.** `natIsZero` returns `1` iff the number held
    in memory is `0`. `hbound` says the whole limb region is in bounds (which,
    with `len : UInt32`, also bounds the number — this is the `ℕ†` ceiling). -/
theorem natIsZero_correct (m : Module) (st : Store Unit) (base len : UInt32)
    (hbound : base.toNat + 4 * len.toNat ≤ st.mem.pages * 65536) :
    wp m natIsZero
        (fun c => ∃ st' s', c = .Fallthrough st' s' ∧ st' = st ∧
            s'.values = [.i32 (if denote (memLimbs st.mem base len.toNat) = 0 then 1 else 0)])
        st { params := [.i32 base, .i32 len], locals := [.i32 0], values := [] } := by
  unfold natIsZero
  wp_run
  apply wp_loop_cons
    (Inv := fun st' s' => st' = st ∧ ∃ p c acc : UInt32,
       s' = ⟨[.i32 p, .i32 c], [.i32 acc], []⟩ ∧
       p.toNat + 4 * c.toNat ≤ st.mem.pages * 65536 ∧
       (denote (memLimbs st.mem base len.toNat) = 0 ↔
          (acc = 0 ∧ denote (memLimbs st.mem p c.toNat) = 0)))
    (μ := fun _ s' => match s'.params with | [_, .i32 c] => c.toNat | _ => 0)
  · -- initial: p = base, c = len, acc = 0
    exact ⟨rfl, base, len, 0, rfl, hbound, by simp⟩
  · -- step
    rintro st₂ s₂ ⟨hst, p, c, acc, hs, hb, hans⟩
    subst hst; subst hs
    apply wp_block_cons
    wp_run
    simp
    by_cases hc : c = 0
    · -- c = 0: exit the loop and return `eqz acc`
      have hthis : denote (memLimbs st₂.mem base len.toNat) = 0 ↔ acc = 0 := by
        have hc0 : c.toNat = 0 := by rw [hc]; rfl
        rw [hc0] at hans; simpa [memLimbs] using hans
      rw [if_pos hc]
      show (if acc = 0 then (1 : UInt32) else 0)
           = if denote (memLimbs st₂.mem base len.toNat) = 0 then 1 else 0
      by_cases hz : acc = 0
      · rw [if_pos hz, if_pos (hthis.mpr hz)]
      · rw [if_neg hz, if_neg (fun h => hz (hthis.mp h))]
    · -- c ≠ 0: consume one limb, continue the loop
      have hcn : c.toNat ≠ 0 := fun h => hc (UInt32.toNat_inj.mp (by simp [h]))
      have hsub : (c - 1).toNat = c.toNat - 1 := by
        rw [UInt32.toNat_sub]; simp only [show (1 : UInt32).toNat = 1 from rfl]
        have := c.toNat_lt; omega
      -- the remaining number splits into the head limb and the tail
      have hsplit : denote (memLimbs st₂.mem p c.toNat) = 0
          ↔ (st₂.mem.read32 p = 0 ∧ denote (memLimbs st₂.mem (4 + p) (c.toNat - 1)) = 0) := by
        obtain ⟨j, hj⟩ : ∃ j, c.toNat = j + 1 := ⟨c.toNat - 1, by omega⟩
        rw [hj]
        show denote (st₂.mem.read32 p :: memLimbs st₂.mem (p + 4) j) = 0 ↔ _
        rw [denote_cons_eq_zero, show (p : UInt32) + 4 = 4 + p from by bv_decide,
            Nat.add_sub_cancel]
      rw [if_neg hc]
      refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
      · -- the load is in bounds (no trap)
        omega
      · -- bounds invariant preserved
        rw [hsub]; have := p.toNat_lt; omega
      · -- answer invariant preserved
        rw [hsub, hans, hsplit]
        constructor
        · rintro ⟨ha, hL, hr⟩; exact ⟨⟨ha, hL⟩, hr⟩
        · rintro ⟨⟨ha, hL⟩, hr⟩; exact ⟨ha, hL, hr⟩
      · -- measure decreases
        rw [hsub]; omega

/-! ### Step 6: divisible-by-3 — the digit-sum trick.

    Because `2³² ≡ 1 (mod 3)`, every limb's place value is `≡ 1`, so
    `n ≡ Σ limbs (mod 3)`. The program walks the limbs keeping a running
    residue `acc = (Σ consumed limbs) mod 3` (reduced each step so it stays
    in `{0,1,2}` and never overflows), and returns `eqz acc`. Same loop shape
    as is-zero; only the accumulator and the invariant's arithmetic change. -/

def natIsDivBy3 : Program := [
  .const 0, .localSet 2,                                       -- acc := 0
  .loop 0 0 [
    .block 0 0 [
      .localGet 1, .eqz, .br_if 0,                             -- if c == 0, exit
      .localGet 2,                                             -- acc
      .localGet 0, .load32 0, .const 3, .remU,                 -- load32(p) % 3
      .add, .const 3, .remU, .localSet 2,                      -- acc := (acc + that) % 3
      .localGet 0, .const 4, .add, .localSet 0,                -- p += 4
      .localGet 1, .const 1, .sub, .localSet 1,                -- c -= 1
      .br 1                                                    -- continue
    ]
  ],
  .localGet 2, .eqz                                            -- return eqz acc
]

/-- **divisible-by-3 correct over `ℕ†`.** `natIsDivBy3` returns `1` iff the number
    held in memory is a multiple of `3`. -/
theorem natIsDivBy3_correct (m : Module) (st : Store Unit) (base len : UInt32)
    (hbound : base.toNat + 4 * len.toNat ≤ st.mem.pages * 65536) :
    wp m natIsDivBy3
        (fun c => ∃ st' s', c = .Fallthrough st' s' ∧ st' = st ∧
            s'.values = [.i32 (if denote (memLimbs st.mem base len.toNat) % 3 = 0 then 1 else 0)])
        st { params := [.i32 base, .i32 len], locals := [.i32 0], values := [] } := by
  unfold natIsDivBy3
  wp_run
  apply wp_loop_cons
    (Inv := fun st' s' => st' = st ∧ ∃ p c acc : UInt32,
       s' = ⟨[.i32 p, .i32 c], [.i32 acc], []⟩ ∧
       p.toNat + 4 * c.toNat ≤ st.mem.pages * 65536 ∧ acc.toNat < 3 ∧
       denote (memLimbs st.mem base len.toNat) % 3
         = (acc.toNat + denote (memLimbs st.mem p c.toNat)) % 3)
    (μ := fun _ s' => match s'.params with | [_, .i32 c] => c.toNat | _ => 0)
  · exact ⟨rfl, base, len, 0, rfl, hbound, by norm_num, by simp⟩
  · rintro st₂ s₂ ⟨hst, p, c, acc, hs, hb, hacc, hans⟩
    subst hst; subst hs
    apply wp_block_cons
    wp_run
    simp
    by_cases hc : c = 0
    · -- c = 0: exit; `eqz acc`, and `acc = ⟦n⟧ % 3` here
      have hw : denote (memLimbs st₂.mem base len.toNat) % 3 = acc.toNat := by
        have hc0 : c.toNat = 0 := by rw [hc]; rfl
        rw [hc0] at hans
        simp only [memLimbs, denote_nil, Nat.add_zero] at hans
        omega
      have hthis : denote (memLimbs st₂.mem base len.toNat) % 3 = 0 ↔ acc = 0 := by
        rw [hw, u32_toNat_eq_zero]
      rw [if_pos hc]
      show (if acc = 0 then (1 : UInt32) else 0)
           = if denote (memLimbs st₂.mem base len.toNat) % 3 = 0 then 1 else 0
      by_cases hz : acc = 0
      · rw [if_pos hz, if_pos (hthis.mpr hz)]
      · rw [if_neg hz, if_neg (fun h => hz (hthis.mp h))]
    · -- c ≠ 0: fold one more limb into the residue, continue
      have hcn : c.toNat ≠ 0 := fun h => hc (UInt32.toNat_inj.mp (by simp [h]))
      have hsub : (c - 1).toNat = c.toNat - 1 := by
        rw [UInt32.toNat_sub]; simp only [show (1 : UInt32).toNat = 1 from rfl]
        have := c.toNat_lt; omega
      -- value of the remaining number in terms of the head limb
      have hd : denote (memLimbs st₂.mem p c.toNat)
          = (st₂.mem.read32 p).toNat
            + 2 ^ 32 * denote (memLimbs st₂.mem (4 + p) (c.toNat - 1)) := by
        obtain ⟨j, hj⟩ : ∃ j, c.toNat = j + 1 := ⟨c.toNat - 1, by omega⟩
        rw [hj]
        show denote (st₂.mem.read32 p :: memLimbs st₂.mem (p + 4) j) = _
        rw [denote_cons, show (p : UInt32) + 4 = 4 + p from by bv_decide, Nat.add_sub_cancel]
      have hp := p.toNat_lt
      rw [if_neg hc]
      refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
      · -- load in bounds
        omega
      · -- bounds invariant preserved
        rw [hsub]; omega
      · -- accumulator stays a reduced residue (< 3)
        omega
      · -- residue invariant preserved (uses 2³² ≡ 1 mod 3)
        rw [hsub]; omega
      · -- measure decreases
        rw [hsub]; omega

/-! ### Memory-write lemma kit (new territory: a *mutated* store).

    Every step so far kept `st.mem` fixed. Squaring writes `P` into scratch, so
    the proofs must reason about `read32 (write32 …)`. Two facts close it: a
    write is observable when you read the *same* limb, and invisible when you
    read a *disjoint* limb. The frame lemma lifts disjointness to a whole limb
    region, so reads of the inputs `x`, `y` survive every write into `P`. -/

/-- **Read-after-write, same limb.** Reading the 32-bit word just written at
    `a` returns exactly the written value: the four bytes recombine to `v`. -/
theorem read32_write32_same (m : Mem) (a v : UInt32) :
    (m.write32 a v).read32 a = v := by
  unfold Mem.write32 Mem.read32
  have h1 : a.toNat + 1 ≠ a.toNat := by omega
  have h2 : a.toNat + 2 ≠ a.toNat := by omega
  have h3 : a.toNat + 3 ≠ a.toNat := by omega
  have h21 : a.toNat + 2 ≠ a.toNat + 1 := by omega
  have h31 : a.toNat + 3 ≠ a.toNat + 1 := by omega
  have h32 : a.toNat + 3 ≠ a.toNat + 2 := by omega
  simp only [h1, h2, h3, h21, h31, h32, if_true, if_false]
  bv_decide

/-- **Read-after-write, disjoint limbs.** If the 4-byte window written at `a`
    does not overlap the 4-byte window read at `b`, the read sees the old
    memory. (`toNat` interval disjointness; both windows are 4 bytes wide.) -/
theorem read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  unfold Mem.write32 Mem.read32
  simp only
  have e0 : ¬ (b.toNat = a.toNat) := by omega
  have e0a : ¬ (b.toNat = a.toNat + 1) := by omega
  have e0b : ¬ (b.toNat = a.toNat + 2) := by omega
  have e0c : ¬ (b.toNat = a.toNat + 3) := by omega
  have e1 : ¬ (b.toNat + 1 = a.toNat) := by omega
  have e1a : ¬ (b.toNat + 1 = a.toNat + 1) := by omega
  have e1b : ¬ (b.toNat + 1 = a.toNat + 2) := by omega
  have e1c : ¬ (b.toNat + 1 = a.toNat + 3) := by omega
  have e2 : ¬ (b.toNat + 2 = a.toNat) := by omega
  have e2a : ¬ (b.toNat + 2 = a.toNat + 1) := by omega
  have e2b : ¬ (b.toNat + 2 = a.toNat + 2) := by omega
  have e2c : ¬ (b.toNat + 2 = a.toNat + 3) := by omega
  have e3 : ¬ (b.toNat + 3 = a.toNat) := by omega
  have e3a : ¬ (b.toNat + 3 = a.toNat + 1) := by omega
  have e3b : ¬ (b.toNat + 3 = a.toNat + 2) := by omega
  have e3c : ¬ (b.toNat + 3 = a.toNat + 3) := by omega
  simp only [e0,e0a,e0b,e0c,e1,e1a,e1b,e1c,e2,e2a,e2b,e2c,e3,e3a,e3b,e3c, if_false]

/-- **Frame lemma.** A write at `a` leaves an in-bounds limb region disjoint
    from `a` unchanged. `a` lies entirely below the region or entirely above
    it; the in-bounds hypothesis keeps the pointer arithmetic wrap-free. This
    is what lets reads of `x`/`y` ignore every write into the `P` scratch. -/
theorem memLimbs_write32_disjoint (m : Mem) (a v base : UInt32) :
    ∀ len, base.toNat + 4 * len ≤ 2 ^ 32 →
      (a.toNat + 4 ≤ base.toNat ∨ base.toNat + 4 * len ≤ a.toNat) →
      memLimbs (m.write32 a v) base len = memLimbs m base len := by
  intro len
  induction len generalizing base with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro hb hd
    have hb4 : (base + 4).toNat = (base.toNat + 4) % 2 ^ 32 := by
      rw [UInt32.toNat_add]; simp only [show (4:UInt32).toNat = 4 from rfl]
    have hbl := base.toNat_lt
    unfold memLimbs
    rw [read32_write32_disjoint m a base v (by omega)]
    congr 1
    apply ih
    · rw [hb4]; omega
    · rw [hb4]; omega

/-! ### Warm-up: a write through the `wp` layer.

    Before the double loop, exercise the mutated store once: store `v` at
    `base`, then read it back. The post-state's memory is `write32 base v`,
    and the value read back is `v` (by `read32_write32_same`). This pins down
    how `store32` threads a changed `Store` through `wp` — the new ingredient
    every step below relies on. -/

def natStoreRead : Program :=
  [.localGet 0, .localGet 1, .store32 0, .localGet 0, .load32 0]

/-- Writing `v` at `base` then reading the same limb yields `v`, and the
    resulting store's memory is exactly `write32 base v`. -/
theorem natStoreRead_spec (m : Module) (st : Store Unit) (base v : UInt32)
    (hbase : base.toNat + 4 ≤ st.mem.pages * 65536) :
    wp m natStoreRead
        (fun c => ∃ st' s', c = .Fallthrough st' s' ∧
            st'.mem = st.mem.write32 base v ∧ s'.values = [.i32 v])
        st { params := [.i32 base, .i32 v], locals := [], values := [] } := by
  unfold natStoreRead
  wp_run
  simp
  exact ⟨hbase, hbase, read32_write32_same _ _ _⟩

/-! ### Step 7: bignum equality compare.

    `bigEq(aBase, bBase, n)` walks `n` limbs of each operand in lockstep,
    ANDing a flag that stays `1` exactly while every limb seen so far matched.
    Because base-2³² digits are unique (`denote_inj`), two equal-length limb
    lists denote the same number iff they are *equal as lists* — so the flag
    decides `⟦a⟧ = ⟦b⟧`. Operands of different lengths / trailing zeros are
    handled by the caller zero-padding both to a common limb count `n`
    (`denote` is insensitive to trailing zeros). Same single-loop shape as
    `natIsZero`, but reading two regions and accumulating equality. -/

/-- Length of a limb region read from memory is exactly the requested count. -/
theorem memLimbs_length (mem : Mem) (base : UInt32) :
    ∀ k, (memLimbs mem base k).length = k := by
  intro k; induction k generalizing base with
  | zero => rfl
  | succ n ih => simp [memLimbs, ih]

/-- **`denote` is injective on equal-length limb lists.** Base-2³² positional
    digits are unique because every limb is `< 2³²`. -/
theorem denote_inj : ∀ l1 l2 : List UInt32, l1.length = l2.length →
    (denote l1 = denote l2 ↔ l1 = l2) := by
  intro l1
  induction l1 with
  | nil => intro l2 hl; cases l2 with
    | nil => simp
    | cons y ys => simp at hl
  | cons x xs ih => intro l2 hl; cases l2 with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [denote_cons, denote_cons]
      have hx := x.toNat_lt
      have hy := y.toNat_lt
      constructor
      · intro h
        have hxy : x.toNat = y.toNat ∧ denote xs = denote ys := ⟨by omega, by omega⟩
        rw [UInt32.toNat_inj] at hxy
        rw [hxy.1, (ih ys hl).mp hxy.2]
      · intro h; rw [List.cons.injEq] at h; rw [h.1, (ih ys hl).mpr h.2]

/-- Splitting a one-longer comparison: two `(j+1)`-limb regions are equal iff
    their heads match and the `j`-limb tails match. -/
theorem memLimbs_eq_cons (mem : Mem) (pa pb : UInt32) (j : Nat) :
    (memLimbs mem pa (j+1) = memLimbs mem pb (j+1)) ↔
      (mem.read32 pa = mem.read32 pb ∧ memLimbs mem (pa+4) j = memLimbs mem (pb+4) j) := by
  simp [memLimbs, List.cons.injEq]

/-- `e &&& f = 1 ↔ e = 1 ∧ f = 1` for boolean (`0`/`1`) values. -/
theorem and_eq_one (e f : UInt32) (he : e = 0 ∨ e = 1) (hf : f = 0 ∨ f = 1) :
    (e &&& f = 1) ↔ (e = 1 ∧ f = 1) := by
  rcases he with h | h <;> rcases hf with h2 | h2 <;> subst h <;> subst h2 <;> bv_decide

/-- `&&&` of two boolean values stays boolean. -/
theorem and_zero_one (e f : UInt32) (he : e = 0 ∨ e = 1) (hf : f = 0 ∨ f = 1) :
    (e &&& f = 0 ∨ e &&& f = 1) := by
  rcases he with h | h <;> rcases hf with h2 | h2 <;> subst h <;> subst h2 <;> bv_decide

def bigEq : Program := [
  .const 1, .localSet 3,                                       -- flag := 1
  .loop 0 0 [
    .block 0 0 [
      .localGet 2, .eqz, .br_if 0,                             -- if c == 0, exit loop
      .localGet 3,                                             -- flag
      .localGet 0, .load32 0,                                  -- a-limb
      .localGet 1, .load32 0,                                  -- b-limb
      .eq, .and, .localSet 3,                                  -- flag := (a==b) & flag
      .localGet 0, .const 4, .add, .localSet 0,                -- pa += 4
      .localGet 1, .const 4, .add, .localSet 1,                -- pb += 4
      .localGet 2, .const 1, .sub, .localSet 2,                -- c -= 1
      .br 1                                                    -- continue loop
    ]
  ],
  .localGet 3                                                  -- return flag
]

/-- **bigEq correct.** Returns `1` iff the two `n`-limb numbers are equal. -/
theorem bigEq_correct (m : Module) (st : Store Unit) (aBase bBase n : UInt32)
    (ha : aBase.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hb : bBase.toNat + 4 * n.toNat ≤ st.mem.pages * 65536) :
    wp m bigEq
        (fun c => ∃ st' s', c = .Fallthrough st' s' ∧ st' = st ∧
            s'.values = [.i32 (if denote (memLimbs st.mem aBase n.toNat)
                                  = denote (memLimbs st.mem bBase n.toNat) then 1 else 0)])
        st { params := [.i32 aBase, .i32 bBase, .i32 n], locals := [.i32 0], values := [] } := by
  unfold bigEq
  wp_run
  apply wp_loop_cons
    (Inv := fun st' s' => st' = st ∧ ∃ pa pb c flag : UInt32,
       s' = ⟨[.i32 pa, .i32 pb, .i32 c], [.i32 flag], []⟩ ∧
       pa.toNat + 4 * c.toNat ≤ st.mem.pages * 65536 ∧
       pb.toNat + 4 * c.toNat ≤ st.mem.pages * 65536 ∧
       (flag = 0 ∨ flag = 1) ∧
       ((denote (memLimbs st.mem aBase n.toNat) = denote (memLimbs st.mem bBase n.toNat)) ↔
          (flag = 1 ∧ memLimbs st.mem pa c.toNat = memLimbs st.mem pb c.toNat)))
    (μ := fun _ s' => match s'.params with | [_, _, .i32 c] => c.toNat | _ => 0)
  · -- initial: pa = aBase, pb = bBase, c = n, flag = 1
    refine ⟨rfl, aBase, bBase, n, 1, rfl, ha, hb, Or.inr rfl, ?_⟩
    simp only [true_and]
    exact denote_inj _ _ (by rw [memLimbs_length, memLimbs_length])
  · -- step
    rintro st₂ s₂ ⟨hst, pa, pb, c, flag, hs, hba, hbb, hflag, hans⟩
    subst hst; subst hs
    apply wp_block_cons
    wp_run
    simp
    by_cases hc : c = 0
    · -- c = 0: exit, return flag, which now decides equality
      have hc0 : c.toNat = 0 := by rw [hc]; rfl
      have hthis : denote (memLimbs st₂.mem aBase n.toNat) = denote (memLimbs st₂.mem bBase n.toNat)
          ↔ flag = 1 := by rw [hc0] at hans; simpa [memLimbs] using hans
      rw [if_pos hc]
      show (flag) = if denote (memLimbs st₂.mem aBase n.toNat)
                       = denote (memLimbs st₂.mem bBase n.toNat) then (1 : UInt32) else 0
      rcases hflag with h0 | h1
      · rw [if_neg (fun h => by rw [hthis] at h; exact absurd h (by rw [h0]; decide)), h0]
      · rw [if_pos (hthis.mpr h1), h1]
    · -- c ≠ 0: consume one limb from each, update flag, continue
      have hcn : c.toNat ≠ 0 := fun h => hc (UInt32.toNat_inj.mp (by simp [h]))
      have hsub : (c - 1).toNat = c.toNat - 1 := by
        rw [UInt32.toNat_sub]; simp only [show (1 : UInt32).toNat = 1 from rfl]
        have := c.toNat_lt; omega
      have hpa := pa.toNat_lt
      have hpb := pb.toNat_lt
      obtain ⟨j, hj⟩ : ∃ j, c.toNat = j + 1 := ⟨c.toNat - 1, by omega⟩
      -- the eq-result the program computes
      set eqr : UInt32 := if st₂.mem.read32 pa = st₂.mem.read32 pb then 1 else 0 with heqr
      have heqr01 : eqr = 0 ∨ eqr = 1 := by rw [heqr]; split <;> [exact Or.inr rfl; exact Or.inl rfl]
      have e4a : (4:UInt32) + pa = pa + 4 := by bv_decide
      have e4b : (4:UInt32) + pb = pb + 4 := by bv_decide
      have hcj : (c - 1).toNat = j := by rw [hsub, hj]; omega
      have heqr1 : (eqr = 1) ↔ (st₂.mem.read32 pa = st₂.mem.read32 pb) := by
        rw [heqr]; split <;> simp_all
      rw [if_neg hc]
      refine ⟨by omega, by omega, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · -- new pa bound
        rw [hsub]; omega
      · -- new pb bound
        rw [hsub]; omega
      · -- new flag is still boolean
        exact and_zero_one eqr flag heqr01 hflag
      · -- answer invariant preserved
        rw [e4a, e4b, hcj, hans, hj, memLimbs_eq_cons,
            and_eq_one eqr flag heqr01 hflag, heqr1]
        tauto
      · -- measure decreases
        rw [hsub]; omega

/-! ### Step 8: bignum addition with carry.

    The carry-propagating core shared by every multiply: `bigAdd(a, b, r, n)`
    writes `r := a + b` (an `n+1`-limb result) and proves
    `⟦r⟧ = ⟦a⟧ + ⟦b⟧`. This is the first program here that **mutates** memory in
    a loop, so it exercises the whole new kit at once: `store32` through `wp`,
    the read-after-write frame (`memLimbs_write32_disjoint` keeps the inputs
    `a`, `b` stable while `r` is written), and the snoc/extend view that grows
    the in-memory result one limb per iteration. The loop invariant is the
    subtraction-free carry relation
    `⟦r[0..k)⟧ + Bᵏ·(carry + ⟦a[k..)⟧ + ⟦b[k..)⟧) = ⟦a⟧ + ⟦b⟧` (`B = 2³²`);
    at `k = n` the remaining inputs vanish and the final carry is stored as the
    top limb. Squaring (the multiply phase below) is repeated shifted
    multiply-adds with this exact invariant shape. -/

theorem ofNat_succ_u32 (n : Nat) : UInt32.ofNat (n+1) = UInt32.ofNat n + 1 := by
  rw [← UInt32.toNat_inj, UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      show (1:UInt32).toNat = 1 from rfl]
  omega

theorem memLimbs_snoc (mem : Mem) (base : UInt32) :
    ∀ k, memLimbs mem base (k+1)
        = memLimbs mem base k ++ [mem.read32 (base + 4 * (UInt32.ofNat k))] := by
  intro k
  induction k generalizing base with
  | zero => simp [memLimbs, show UInt32.ofNat 0 = 0 from rfl]
  | succ n ih =>
    have haddr : (base + 4) + 4 * UInt32.ofNat n = base + 4 * UInt32.ofNat (n+1) := by
      rw [ofNat_succ_u32]; bv_decide
    rw [show memLimbs mem base (n+1+1) = mem.read32 base :: memLimbs mem (base+4) (n+1) from rfl,
        ih (base+4),
        show memLimbs mem base (n+1) = mem.read32 base :: memLimbs mem (base+4) n from rfl]
    simp only [List.cons_append]; rw [haddr]

theorem memLimbs_write_extend (mem : Mem) (rBase : UInt32) (k : Nat) (w : UInt32)
    (hb : rBase.toNat + 4 * (k+1) ≤ 2^32) :
    memLimbs (mem.write32 (rBase + 4 * UInt32.ofNat k) w) rBase (k+1)
      = memLimbs mem rBase k ++ [w] := by
  have hbl := rBase.toNat_lt
  have hpr : (rBase + 4 * UInt32.ofNat k).toNat = rBase.toNat + 4 * k := by
    rw [UInt32.toNat_add, UInt32.toNat_mul, show (4:UInt32).toNat = 4 from rfl,
        UInt32.toNat_ofNat']; omega
  rw [memLimbs_snoc (mem.write32 (rBase + 4 * UInt32.ofNat k) w) rBase k,
      memLimbs_write32_disjoint mem _ w rBase k (by omega) (by omega), read32_write32_same]

def bigAdd : Program := [
  .loop 0 0 [
    .block 0 0 [
      .localGet 3, .eqz, .br_if 0,
      .localGet 0, .load32 0, .extendUI32,
      .localGet 1, .load32 0, .extendUI32, .addI64,
      .localGet 4, .extendUI32, .addI64, .localSet 5,
      .localGet 2, .localGet 5, .wrapI64, .store32 0,
      .localGet 5, .constI64 32, .shrUI64, .wrapI64, .localSet 4,
      .localGet 0, .const 4, .add, .localSet 0,
      .localGet 1, .const 4, .add, .localSet 1,
      .localGet 2, .const 4, .add, .localSet 2,
      .localGet 3, .const 1, .sub, .localSet 3,
      .br 1
    ]
  ],
  .localGet 2, .localGet 4, .store32 0
]

theorem bigAdd_correct (m : Module) (st : Store Unit) (aBase bBase rBase n : UInt32)
    (hmem : st.mem.pages * 65536 ≤ 2^32)
    (ha : aBase.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hb : bBase.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hr : rBase.toNat + 4 * (n.toNat + 1) ≤ st.mem.pages * 65536)
    (hdRA : rBase.toNat + 4*(n.toNat+1) ≤ aBase.toNat ∨ aBase.toNat + 4*n.toNat ≤ rBase.toNat)
    (hdRB : rBase.toNat + 4*(n.toNat+1) ≤ bBase.toNat ∨ bBase.toNat + 4*n.toNat ≤ rBase.toNat) :
    wp m bigAdd
        (fun cont => ∃ st' s', cont = .Fallthrough st' s' ∧ st'.mem.pages = st.mem.pages ∧
            denote (memLimbs st'.mem rBase (n.toNat + 1))
              = denote (memLimbs st.mem aBase n.toNat) + denote (memLimbs st.mem bBase n.toNat))
        st { params := [.i32 aBase, .i32 bBase, .i32 rBase, .i32 n],
             locals := [.i32 0, .i64 0], values := [] } := by
  unfold bigAdd
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = st.mem.pages ∧
      ∃ (k : Nat) (c carry : UInt32) (sumv : UInt64),
        s' = ⟨[.i32 (aBase + 4*UInt32.ofNat k), .i32 (bBase + 4*UInt32.ofNat k),
               .i32 (rBase + 4*UInt32.ofNat k), .i32 c],
              [.i32 carry, .i64 sumv], []⟩ ∧
        k + c.toNat = n.toNat ∧ (carry = 0 ∨ carry = 1) ∧
        denote (memLimbs st'.mem rBase k)
          + 2^(32*k) * (carry.toNat
              + denote (memLimbs st'.mem (aBase + 4*UInt32.ofNat k) c.toNat)
              + denote (memLimbs st'.mem (bBase + 4*UInt32.ofNat k) c.toNat))
          = denote (memLimbs st.mem aBase n.toNat) + denote (memLimbs st.mem bBase n.toNat))
    (μ := fun _ s' => match s'.params with | [_, _, _, .i32 c] => c.toNat | _ => 0)
  · -- init: k=0, c=n, carry=0
    refine ⟨rfl, 0, n, 0, 0, ?_, by simp, Or.inl rfl, ?_⟩
    · simp [show UInt32.ofNat 0 = 0 from rfl]
    · simp [show UInt32.ofNat 0 = 0 from rfl, memLimbs]
  · -- step
    rintro st₂ s₂ ⟨hpg, k, c, carry, sumv, hs, hkc, hcarry, hinv⟩
    subst hs
    apply wp_block_cons
    wp_run
    simp
    by_cases hc : c = 0
    · -- exit: store the final carry into r[n] (= limb n)
      rw [if_pos hc]
      simp
      have hc0 : c.toNat = 0 := by rw [hc]; rfl
      have hkn : k = n.toNat := by omega
      subst hkn
      refine ⟨by omega, hpg, ?_⟩
      rw [memLimbs_write_extend st₂.mem rBase n.toNat carry (by omega),
          denote_append_singleton, memLimbs_length]
      rw [hc] at hinv
      simp only [show ((0:UInt32)).toNat = 0 from rfl, memLimbs, denote_nil, Nat.add_zero] at hinv
      rw [← hinv]; ring
    · -- continue
      rw [if_neg hc]
      have haB := aBase.toNat_lt
      have hbB := bBase.toNat_lt
      have hrB := rBase.toNat_lt
      have hcle : carry.toNat ≤ 1 := by rcases hcarry with h|h <;> rw [h] <;> decide
      have hcn0 : c.toNat ≠ 0 := fun h => hc (UInt32.toNat_inj.mp (by simp [h]))
      obtain ⟨j, hj⟩ : ∃ j, c.toNat = j + 1 := ⟨c.toNat - 1, by omega⟩
      have hcj : (c - 1).toNat = j := by
        rw [UInt32.toNat_sub]; simp only [show (1:UInt32).toNat = 1 from rfl]
        have := c.toNat_lt; omega
      have hra := (st₂.mem.read32 (aBase + 4 * UInt32.ofNat k)).toNat_lt
      have hrb := (st₂.mem.read32 (bBase + 4 * UInt32.ofNat k)).toNat_lt
      have hAk : (aBase + 4 * UInt32.ofNat k).toNat = aBase.toNat + 4 * k := by
        rw [UInt32.toNat_add, UInt32.toNat_mul, show (4:UInt32).toNat = 4 from rfl,
            UInt32.toNat_ofNat']; omega
      have hBk : (bBase + 4 * UInt32.ofNat k).toNat = bBase.toNat + 4 * k := by
        rw [UInt32.toNat_add, UInt32.toNat_mul, show (4:UInt32).toNat = 4 from rfl,
            UInt32.toNat_ofNat']; omega
      have hRk : (rBase + 4 * UInt32.ofNat k).toNat = rBase.toNat + 4 * k := by
        rw [UInt32.toNat_add, UInt32.toNat_mul, show (4:UInt32).toNat = 4 from rfl,
            UInt32.toNat_ofNat']; omega
      have hAaddr : (aBase + 4 * UInt32.ofNat k) + 4 = aBase + 4 * UInt32.ofNat (k+1) := by
        rw [ofNat_succ_u32]; bv_decide
      have hBaddr : (bBase + 4 * UInt32.ofNat k) + 4 = bBase + 4 * UInt32.ofNat (k+1) := by
        rw [ofNat_succ_u32]; bv_decide
      set ak := st₂.mem.read32 (aBase + 4 * UInt32.ofNat k) with hak
      set bk := st₂.mem.read32 (bBase + 4 * UInt32.ofNat k) with hbk
      set snat := ak.toNat + bk.toNat + carry.toNat with hsnat
      set w : UInt32 := UInt32.ofNat (snat % 4294967296) with hwdef
      set mem' := st₂.mem.write32 (rBase + 4 * UInt32.ofNat k) w with hmem'
      set cn := (snat % 18446744073709551616) >>> 32 % 4294967296 with hcndef
      have h64 : snat % 18446744073709551616 = snat := Nat.mod_eq_of_lt (by omega)
      have hcn : cn = snat / 2 ^ 32 := by
        rw [hcndef, h64, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
      have hwn : w.toNat = snat % 2 ^ 32 := by rw [hwdef, UInt32.toNat_ofNat']; omega
      have hkey : w.toNat + 2 ^ 32 * cn = snat := by rw [hcn, hwn]; omega
      have hcombine : w.toNat + 2 ^ 32 * cn = ak.toNat + bk.toNat + carry.toNat := hkey.trans hsnat
      have hAfull : memLimbs mem' (aBase + 4 * UInt32.ofNat k) c.toNat
                  = memLimbs st₂.mem (aBase + 4 * UInt32.ofNat k) c.toNat := by
        rw [hmem']; apply memLimbs_write32_disjoint
        · rw [hAk]; omega
        · rw [hAk, hRk]; omega
      have hBfull : memLimbs mem' (bBase + 4 * UInt32.ofNat k) c.toNat
                  = memLimbs st₂.mem (bBase + 4 * UInt32.ofNat k) c.toNat := by
        rw [hmem']; apply memLimbs_write32_disjoint
        · rw [hBk]; omega
        · rw [hBk, hRk]; omega
      refine ⟨?_, ?_, ?_, ⟨?_, k+1, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · omega
      · omega
      · omega
      · exact hpg
      · rw [ofNat_succ_u32]; bv_decide
      · rw [ofNat_succ_u32]; bv_decide
      · rw [ofNat_succ_u32]; bv_decide
      · rw [hcj]; omega
      · rw [hcn]
        have hv : snat / 2 ^ 32 = 0 ∨ snat / 2 ^ 32 = 1 := by omega
        rcases hv with h|h <;> rw [h] <;> [exact Or.inl rfl; exact Or.inr rfl]
      · -- denote invariant
        rw [memLimbs_write_extend st₂.mem rBase k w (by omega), denote_append_singleton,
            memLimbs_length, hcj]
        have hAtail : memLimbs mem' (aBase + 4 * UInt32.ofNat (k+1)) j
                    = memLimbs st₂.mem (aBase + 4 * UInt32.ofNat (k+1)) j := by
          have h := hAfull; rw [hj] at h
          rw [show memLimbs mem' (aBase + 4 * UInt32.ofNat k) (j+1)
                = mem'.read32 (aBase + 4 * UInt32.ofNat k)
                  :: memLimbs mem' ((aBase + 4 * UInt32.ofNat k) + 4) j from rfl,
              show memLimbs st₂.mem (aBase + 4 * UInt32.ofNat k) (j+1)
                = st₂.mem.read32 (aBase + 4 * UInt32.ofNat k)
                  :: memLimbs st₂.mem ((aBase + 4 * UInt32.ofNat k) + 4) j from rfl,
              hAaddr] at h
          exact ((List.cons.injEq _ _ _ _).mp h).2
        have hBtail : memLimbs mem' (bBase + 4 * UInt32.ofNat (k+1)) j
                    = memLimbs st₂.mem (bBase + 4 * UInt32.ofNat (k+1)) j := by
          have h := hBfull; rw [hj] at h
          rw [show memLimbs mem' (bBase + 4 * UInt32.ofNat k) (j+1)
                = mem'.read32 (bBase + 4 * UInt32.ofNat k)
                  :: memLimbs mem' ((bBase + 4 * UInt32.ofNat k) + 4) j from rfl,
              show memLimbs st₂.mem (bBase + 4 * UInt32.ofNat k) (j+1)
                = st₂.mem.read32 (bBase + 4 * UInt32.ofNat k)
                  :: memLimbs st₂.mem ((bBase + 4 * UInt32.ofNat k) + 4) j from rfl,
              hBaddr] at h
          exact ((List.cons.injEq _ _ _ _).mp h).2
        rw [hAtail, hBtail]
        rw [hj, show memLimbs st₂.mem (aBase + 4 * UInt32.ofNat k) (j+1)
              = st₂.mem.read32 (aBase + 4 * UInt32.ofNat k)
                :: memLimbs st₂.mem ((aBase + 4 * UInt32.ofNat k) + 4) j from rfl,
            show memLimbs st₂.mem (bBase + 4 * UInt32.ofNat k) (j+1)
              = st₂.mem.read32 (bBase + 4 * UInt32.ofNat k)
                :: memLimbs st₂.mem ((bBase + 4 * UInt32.ofNat k) + 4) j from rfl,
            denote_cons, denote_cons, hAaddr, hBaddr] at hinv
        rw [← hinv]
        have e2 : (2:ℕ) ^ (32 * (k+1)) = 2 ^ (32 * k) * 2 ^ 32 := by
          rw [Nat.mul_succ, pow_add]
        rw [e2]
        generalize 2 ^ (32 * k) = Q
        generalize denote (memLimbs st₂.mem (aBase + 4 * UInt32.ofNat (k+1)) j) = A'
        generalize denote (memLimbs st₂.mem (bBase + 4 * UInt32.ofNat (k+1)) j) = B'
        generalize denote (memLimbs st₂.mem rBase k) = D
        calc D + w.toNat * Q + Q * 2 ^ 32 * (cn + A' + B')
            = D + Q * (w.toNat + 2 ^ 32 * cn) + Q * 2 ^ 32 * A' + Q * 2 ^ 32 * B' := by ring
          _ = D + Q * (ak.toNat + bk.toNat + carry.toNat) + Q * 2 ^ 32 * A' + Q * 2 ^ 32 * B' := by
                rw [hcombine]
          _ = D + Q * (carry.toNat + (ak.toNat + 2 ^ 32 * A') + (bk.toNat + 2 ^ 32 * B')) := by ring
      · rw [hcj]; omega

/-- `denote` of a concatenation: low part plus shifted high part. -/
theorem denote_append (xs ys : List UInt32) :
    denote (xs ++ ys) = denote xs + 2 ^ (32 * xs.length) * denote ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, denote_cons, ih, List.length_cons]
      rw [Nat.mul_succ, pow_add]; ring

/-- A limb list of length `k` denotes a value `< 2^(32k)`: positional digits. -/
theorem denote_lt (l : List UInt32) : denote l < 2 ^ (32 * l.length) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [denote_cons, List.length_cons, Nat.mul_succ, pow_add]
      have hx := x.toNat_lt
      have : (2 : Nat) ^ (32 * xs.length) ≥ 1 := Nat.one_le_two_pow
      nlinarith [ih]

/-- Splitting a memory limb region at `p`: first `p` limbs, then the rest. -/
theorem memLimbs_append (mem : Mem) (base : UInt32) (p q : Nat) :
    memLimbs mem base (p + q)
      = memLimbs mem base p ++ memLimbs mem (base + 4 * UInt32.ofNat p) q := by
  induction p generalizing base with
  | zero => simp [memLimbs, show UInt32.ofNat 0 = 0 from rfl]
  | succ k ih =>
      have haddr : (base + 4) + 4 * UInt32.ofNat k = base + 4 * UInt32.ofNat (k+1) := by
        rw [ofNat_succ_u32]; bv_decide
      rw [show k + 1 + q = (k + q) + 1 from by omega,
          show memLimbs mem base ((k+q)+1) = mem.read32 base :: memLimbs mem (base+4) (k+q) from rfl,
          show memLimbs mem base (k+1) = mem.read32 base :: memLimbs mem (base+4) k from rfl,
          ih (base+4)]
      simp only [List.cons_append]
      rw [haddr]

/-- Split a limb region at index `k` (`k < L`): low `k` limbs, the limb at `k`,
    and the high part. The positional-value decomposition. -/
theorem denote_memLimbs_split (mem : Mem) (base : UInt32) (L k : Nat) (hk : k < L) :
    denote (memLimbs mem base L)
      = denote (memLimbs mem base k)
        + 2 ^ (32 * k) * (mem.read32 (base + 4 * UInt32.ofNat k)).toNat
        + 2 ^ (32 * (k + 1)) * denote (memLimbs mem (base + 4 * UInt32.ofNat (k + 1)) (L - k - 1)) := by
  have haddr : (base + 4 * UInt32.ofNat k) + 4 = base + 4 * UInt32.ofNat (k + 1) := by
    rw [ofNat_succ_u32]; bv_decide
  conv_lhs =>
    rw [show L = k + (L - k) from by omega, memLimbs_append,
        show L - k = (L - k - 1) + 1 from by omega,
        show memLimbs mem (base + 4 * UInt32.ofNat k) ((L - k - 1) + 1)
          = mem.read32 (base + 4 * UInt32.ofNat k)
            :: memLimbs mem ((base + 4 * UInt32.ofNat k) + 4) (L - k - 1) from rfl,
        haddr, denote_append, memLimbs_length, denote_cons]
  rw [show (2 : ℕ) ^ (32 * (k + 1)) = 2 ^ (32 * k) * 2 ^ 32 from by rw [Nat.mul_succ, pow_add]]
  ring

/-- **Interior read-modify-write.** Overwriting the limb at index `p` (`p < L`)
    with `v` changes the region's value by `(v − old)·2^(32p)` — stated
    subtraction-free. The workhorse for schoolbook accumulation. -/
theorem memLimbs_write_interior (mem : Mem) (base : UInt32) (p L : Nat) (v : UInt32)
    (hp : p < L) (hbnd : base.toNat + 4 * L < 2 ^ 32) :
    denote (memLimbs (mem.write32 (base + 4 * UInt32.ofNat p) v) base L)
        + 2 ^ (32 * p) * (mem.read32 (base + 4 * UInt32.ofNat p)).toNat
      = denote (memLimbs mem base L) + 2 ^ (32 * p) * v.toNat := by
  have hbl := base.toNat_lt
  have hp32 : p < 2 ^ 32 := by omega
  have hp132 : p + 1 < 2 ^ 32 := by omega
  set a : UInt32 := base + 4 * UInt32.ofNat p with ha
  have hpa : a.toNat = base.toNat + 4 * p := by
    rw [ha, UInt32.toNat_add, UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl,
        UInt32.toNat_ofNat', Nat.mod_eq_of_lt hp32]; omega
  set mem' := mem.write32 a v with hmem'
  have hpa1 : (base + 4 * UInt32.ofNat (p + 1)).toNat = base.toNat + 4 * (p + 1) := by
    rw [UInt32.toNat_add, UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl,
        UInt32.toNat_ofNat', Nat.mod_eq_of_lt hp132]; omega
  have hpre : memLimbs mem' base p = memLimbs mem base p := by
    rw [hmem']; exact memLimbs_write32_disjoint mem a v base p (by omega) (by rw [hpa]; omega)
  have hsuf : memLimbs mem' (base + 4 * UInt32.ofNat (p + 1)) (L - p - 1)
            = memLimbs mem (base + 4 * UInt32.ofNat (p + 1)) (L - p - 1) := by
    rw [hmem']
    exact memLimbs_write32_disjoint mem a v (base + 4 * UInt32.ofNat (p + 1)) (L - p - 1)
      (by rw [hpa1]; omega) (by rw [hpa1, hpa]; omega)
  rw [denote_memLimbs_split mem' base L p hp, denote_memLimbs_split mem base L p hp, ← ha,
      hpre, hsuf, hmem', read32_write32_same]
  ring

/-- **High limbs vanish.** If a region's value is `< 2^(32k)` then its limb at
    index `k` is zero — a number below `Bᵏ` has no digit at position `k`. -/
theorem read32_high_zero (mem : Mem) (base : UInt32) (L k : Nat)
    (hk : k < L) (hlt : denote (memLimbs mem base L) < 2 ^ (32 * k)) :
    mem.read32 (base + 4 * UInt32.ofNat k) = 0 := by
  rw [← u32_toNat_eq_zero]
  by_contra h
  have h1 : 1 ≤ (mem.read32 (base + 4 * UInt32.ofNat k)).toNat := by omega
  have hsplit := denote_memLimbs_split mem base L k hk
  have hge : 2 ^ (32 * k) * 1 ≤ denote (memLimbs mem base L) := by
    rw [hsplit]
    have := Nat.mul_le_mul_left (2 ^ (32 * k)) h1
    omega
  simp at hge
  omega

/-- `exec` over a concatenation: run `p1`; if it falls through, continue `p2`. -/
theorem exec_append {α : Type} (fuel : Nat) (m : Module) (env : HostEnv α) :
    ∀ (p1 p2 : Program) (st : Store α) (s : Locals),
      exec fuel m st s (p1 ++ p2) env
        = (match exec fuel m st s p1 env with
           | .Fallthrough st' s' => exec fuel m st' s' p2 env
           | other => other) := by
  intro p1
  induction p1 with
  | nil => intro p2 st s; simp only [List.nil_append, exec]
  | cons inst rest ih =>
    intro p2 st s
    simp only [List.cons_append, exec]
    cases execOne fuel m st s inst env with
    | Fallthrough st' s' => exact ih p2 st' s'
    | OutOfFuel => rfl
    | Break k st' s' => rfl
    | Return st' vs => rfl
    | Trap st' msg => rfl
    | Invalid msg => rfl
    | ReturnCall fid st' vs => rfl
    | Throwing tag targs st' s' => rfl

/-- Sequencing rule: prove `p1` reaching a fall-through state from which `p2`
    satisfies `Q`; non-fall-through outcomes of `p1` must already satisfy `Q`. -/
theorem wp_seq {α : Type} {m : Module} {p1 p2 : Program} {Q : Assertion α}
    {st : Store α} {s : Locals} {env : HostEnv α}
    (h : wp m p1 (fun c => match c with
          | .Fallthrough st' s' => wp m p2 Q st' s' env
          | other => Q other) st s env) :
    wp m (p1 ++ p2) Q st s env := by
  unfold wp at h ⊢
  obtain ⟨N, hN⟩ := h
  by_cases hOOF : ∀ f ≥ N, exec f m st s p1 env = .OutOfFuel
  · refine ⟨N, fun fuel hfuel => ?_⟩
    have hpre := hN fuel hfuel
    rw [hOOF fuel hfuel] at hpre
    rw [exec_append, hOOF fuel hfuel]; exact hpre
  · push Not at hOOF
    obtain ⟨f₀, hf₀, hf₀_ne⟩ := hOOF
    have hk_stable : ∀ f' ≥ f₀, exec f' m st s p1 env = exec f₀ m st s p1 env := fun f' hf' =>
      exec_fuel_mono hf' hf₀_ne
    have hQ_at := hN f₀ hf₀
    cases hk : exec f₀ m st s p1 env with
    | OutOfFuel => exact absurd hk hf₀_ne
    | Fallthrough st' s' =>
      rw [hk] at hQ_at
      simp only at hQ_at
      obtain ⟨Nr, hNr⟩ := hQ_at
      refine ⟨max f₀ Nr, fun fuel hfuel => ?_⟩
      rw [exec_append, hk_stable fuel (by omega), hk]; exact hNr fuel (by omega)
    | Break k st' s' =>
      rw [hk] at hQ_at
      exact ⟨f₀, fun fuel hfuel => by rw [exec_append, hk_stable fuel hfuel, hk]; exact hQ_at⟩
    | Return st' vs =>
      rw [hk] at hQ_at
      exact ⟨f₀, fun fuel hfuel => by rw [exec_append, hk_stable fuel hfuel, hk]; exact hQ_at⟩
    | Trap st' msg =>
      rw [hk] at hQ_at
      exact ⟨f₀, fun fuel hfuel => by rw [exec_append, hk_stable fuel hfuel, hk]; exact hQ_at⟩
    | Invalid msg =>
      rw [hk] at hQ_at
      exact ⟨f₀, fun fuel hfuel => by rw [exec_append, hk_stable fuel hfuel, hk]; exact hQ_at⟩
    | ReturnCall fid st' vs =>
      rw [hk] at hQ_at
      exact ⟨f₀, fun fuel hfuel => by rw [exec_append, hk_stable fuel hfuel, hk]; exact hQ_at⟩
    | Throwing tag targs st' s' =>
      rw [hk] at hQ_at
      exact ⟨f₀, fun fuel hfuel => by rw [exec_append, hk_stable fuel hfuel, hk]; exact hQ_at⟩

theorem ofNat_add_u32 (a b : Nat) : UInt32.ofNat (a + b) = UInt32.ofNat a + UInt32.ofNat b := by
  rw [← UInt32.toNat_inj, UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      UInt32.toNat_ofNat']; omega

/-- Equal limb regions agree limb-by-limb: lets the loop read `x` from the
    mutated store yet equate it with the fixed reference store. -/
theorem read32_eq_of_memLimbs_eq : ∀ (L k : Nat) (m1 m2 : Mem) (base : UInt32),
    k < L → memLimbs m1 base L = memLimbs m2 base L →
    m1.read32 (base + 4 * UInt32.ofNat k) = m2.read32 (base + 4 * UInt32.ofNat k) := by
  intro L
  induction L with
  | zero => intro k _ _ _ hk _; omega
  | succ L ih =>
    intro k m1 m2 base hk heq
    rw [show memLimbs m1 base (L + 1) = m1.read32 base :: memLimbs m1 (base + 4) L from rfl,
        show memLimbs m2 base (L + 1) = m2.read32 base :: memLimbs m2 (base + 4) L from rfl,
        List.cons.injEq] at heq
    cases k with
    | zero => simpa [show UInt32.ofNat 0 = 0 from rfl] using heq.1
    | succ k' =>
      have hrec := ih k' m1 m2 (base + 4) (by omega) heq.2
      rwa [show (base + 4) + 4 * UInt32.ofNat k' = base + 4 * UInt32.ofNat (k' + 1) from by
            rw [ofNat_succ_u32]; bv_decide] at hrec

/-! ### Multiply phase: schoolbook square into scratch.

    Frame: params `[xBase, yBase, n, scratchBase]` (read-only); working locals
    4..12.  Computes `P := x²` (the `2n`-limb scratch region), assuming `P`
    starts zeroed.  Outer loop over `i`, inner multiply-accumulate over `j`. -/

def mulPhase : Program := [
  .localGet 2, .localSet 4,                               -- oc := n
  .localGet 0, .localSet 5,                               -- xi := xBase
  .localGet 3, .localSet 6,                               -- pr := scratchBase
  .loop 0 0 [ .block 0 0 [
    .localGet 4, .eqz, .br_if 0,                          -- oc == 0 → exit outer
    .localGet 5, .load32 0, .localSet 7,                  -- xiv := x[i]
    .const 0, .localSet 8,                                -- carry := 0
    .localGet 0, .localSet 9,                             -- xj := xBase
    .localGet 6, .localSet 10,                            -- pij := pr
    .localGet 2, .localSet 11,                            -- ic := n
    .loop 0 0 [ .block 0 0 [
      .localGet 11, .eqz, .br_if 0,                       -- ic == 0 → exit inner
      .localGet 10, .load32 0, .extendUI32,               -- P[i+j]  (u64)
      .localGet 7, .extendUI32,                           -- x[i]    (u64)
      .localGet 9, .load32 0, .extendUI32, .mulI64,       -- x[i]·x[j]
      .addI64,                                            -- P[i+j] + x[i]·x[j]
      .localGet 8, .extendUI32, .addI64, .localSet 12,    -- t := … + carry
      .localGet 10, .localGet 12, .wrapI64, .store32 0,   -- P[i+j] := t mod B
      .localGet 12, .constI64 32, .shrUI64, .wrapI64, .localSet 8, -- carry := t / B
      .localGet 9, .const 4, .add, .localSet 9,           -- xj += 4
      .localGet 10, .const 4, .add, .localSet 10,         -- pij += 4
      .localGet 11, .const 1, .sub, .localSet 11,         -- ic -= 1
      .br 1
    ]],
    .localGet 10, .localGet 8, .store32 0,                -- P[i+n] := carry
    .localGet 5, .const 4, .add, .localSet 5,             -- xi += 4
    .localGet 6, .const 4, .add, .localSet 6,             -- pr += 4
    .localGet 4, .const 1, .sub, .localSet 4,             -- oc -= 1
    .br 1
  ]]
]

theorem mulPhase_correct (m : Module) (st : Store Unit) (xBase yBase n scratchBase : UInt32)
    (hmem : st.mem.pages * 65536 ≤ 2 ^ 32)
    (hx : xBase.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hy : yBase.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hsc : scratchBase.toNat + 4 * (2 * n.toNat) < 2 ^ 32)
    (hscb : scratchBase.toNat + 4 * (2 * n.toNat) ≤ st.mem.pages * 65536)
    (hzero : denote (memLimbs st.mem scratchBase (2 * n.toNat)) = 0)
    (hdSX : scratchBase.toNat + 4 * (2 * n.toNat) ≤ xBase.toNat
            ∨ xBase.toNat + 4 * n.toNat ≤ scratchBase.toNat)
    (hdSY : scratchBase.toNat + 4 * (2 * n.toNat) ≤ yBase.toNat
            ∨ yBase.toNat + 4 * n.toNat ≤ scratchBase.toNat) :
    wp m mulPhase
        (fun cont => ∃ (st' : Store Unit) (q4 q5 q6 q7 q8 q9 q10 q11 : UInt32) (q12 : UInt64),
            cont = .Fallthrough st'
              ⟨[.i32 xBase, .i32 yBase, .i32 n, .i32 scratchBase],
               [.i32 q4, .i32 q5, .i32 q6, .i32 q7, .i32 q8, .i32 q9, .i32 q10, .i32 q11, .i64 q12],
               []⟩ ∧ st'.mem.pages = st.mem.pages ∧
            memLimbs st'.mem xBase n.toNat = memLimbs st.mem xBase n.toNat ∧
            memLimbs st'.mem yBase n.toNat = memLimbs st.mem yBase n.toNat ∧
            denote (memLimbs st'.mem scratchBase (2 * n.toNat))
              = denote (memLimbs st.mem xBase n.toNat) ^ 2)
        st { params := [.i32 xBase, .i32 yBase, .i32 n, .i32 scratchBase],
             locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0],
             values := [] } := by
  unfold mulPhase
  wp_run
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = st.mem.pages ∧
      ∃ (i : Nat) (oc a7 a8 a9 a10 a11 : UInt32) (a12 : UInt64),
        s' = ⟨[.i32 xBase, .i32 yBase, .i32 n, .i32 scratchBase],
              [.i32 oc, .i32 (xBase + 4 * UInt32.ofNat i), .i32 (scratchBase + 4 * UInt32.ofNat i),
               .i32 a7, .i32 a8, .i32 a9, .i32 a10, .i32 a11, .i64 a12], []⟩ ∧
        i + oc.toNat = n.toNat ∧
        memLimbs st'.mem xBase n.toNat = memLimbs st.mem xBase n.toNat ∧
        memLimbs st'.mem yBase n.toNat = memLimbs st.mem yBase n.toNat ∧
        denote (memLimbs st'.mem scratchBase (2 * n.toNat))
          = denote (memLimbs st.mem xBase i) * denote (memLimbs st.mem xBase n.toNat))
    (μ := fun _ s' => match s'.locals with | (.i32 oc :: _) => oc.toNat | _ => 0)
  · -- init: i = 0, oc = n
    refine ⟨rfl, 0, n, 0, 0, 0, 0, 0, 0, ?_, ?_, rfl, rfl, ?_⟩
    · simp [show UInt32.ofNat 0 = 0 from rfl]
    · simp
    · simp [memLimbs, hzero]
  · -- step
    rintro st₂ s₂ ⟨hpg, i, oc, a7, a8, a9, a10, a11, a12, hs, hioc, hxu, hyu, hinv⟩
    subst hs
    apply wp_block_cons
    wp_run
    simp
    by_cases hoc : oc = 0
    · -- exit outer: i = n, scratch holds x²
      rw [if_pos hoc]
      simp
      have hin : i = n.toNat := by
        have : oc.toNat = 0 := by rw [hoc]; rfl
        omega
      refine ⟨hpg, hxu, hyu, ?_⟩
      rw [hinv, hin, pow_two]
    · -- continue: run inner loop, reestablish for i+1
      rw [if_neg hoc]
      have hin : i < n.toNat := by
        have h1 : oc.toNat ≠ 0 := fun h => hoc (UInt32.toNat_inj.mp (by simp [h]))
        omega
      have hxiv : st₂.mem.read32 (xBase + 4 * UInt32.ofNat i)
                = st.mem.read32 (xBase + 4 * UInt32.ofNat i) :=
        read32_eq_of_memLimbs_eq n.toNat i st₂.mem st.mem xBase hin hxu
      have hxlt := xBase.toNat_lt
      refine ⟨?_, ?_⟩
      · -- x[i] load is in bounds
        have : (xBase.toNat + 4 * i) % 4294967296 = xBase.toNat + 4 * i := by
          apply Nat.mod_eq_of_lt; omega
        rw [hpg]; omega
      · -- inner loop
        apply wp_loop_cons
          (Inv := fun st' s' =>
            st'.mem.pages = st.mem.pages ∧
            ∃ (j : Nat) (ic carry : UInt32) (sv : UInt64),
              s' = ⟨[.i32 xBase, .i32 yBase, .i32 n, .i32 scratchBase],
                    [.i32 oc, .i32 (xBase + 4 * UInt32.ofNat i), .i32 (scratchBase + 4 * UInt32.ofNat i),
                     .i32 (st.mem.read32 (xBase + 4 * UInt32.ofNat i)), .i32 carry,
                     .i32 (xBase + 4 * UInt32.ofNat j),
                     .i32 (scratchBase + 4 * UInt32.ofNat (i + j)), .i32 ic, .i64 sv], []⟩ ∧
              j + ic.toNat = n.toNat ∧
              memLimbs st'.mem xBase n.toNat = memLimbs st.mem xBase n.toNat ∧
              memLimbs st'.mem yBase n.toNat = memLimbs st.mem yBase n.toNat ∧
              st'.mem.read32 (scratchBase + 4 * UInt32.ofNat (i + n.toNat)) = 0 ∧
              denote (memLimbs st'.mem scratchBase (2 * n.toNat))
                + 2 ^ (32 * (i + j))
                    * ((st.mem.read32 (xBase + 4 * UInt32.ofNat i)).toNat
                        * denote (memLimbs st.mem (xBase + 4 * UInt32.ofNat j) (n.toNat - j)) + carry.toNat)
                = denote (memLimbs st.mem xBase i) * denote (memLimbs st.mem xBase n.toNat)
                  + 2 ^ (32 * i) * (st.mem.read32 (xBase + 4 * UInt32.ofNat i)).toNat
                      * denote (memLimbs st.mem xBase n.toNat))
          (μ := fun _ s' => match s'.locals with
            | [_, _, _, _, _, _, _, .i32 ic, _] => ic.toNat | _ => 0)
        · -- inner init: j = 0, ic = n, carry = 0
          have hAi : denote (memLimbs st.mem xBase i) < 2 ^ (32 * i) := by
            have := denote_lt (memLimbs st.mem xBase i); rwa [memLimbs_length] at this
          have hX : denote (memLimbs st.mem xBase n.toNat) < 2 ^ (32 * n.toNat) := by
            have := denote_lt (memLimbs st.mem xBase n.toNat); rwa [memLimbs_length] at this
          refine ⟨hpg, 0, n, 0, a12, ?_, by simp, hxu, hyu, ?_, ?_⟩
          · -- locals match
            rw [hxiv]
            simp [show UInt32.ofNat 0 = (0 : UInt32) from rfl]
          · -- high limb zero
            apply read32_high_zero st₂.mem scratchBase (2 * n.toNat) (i + n.toNat) (by omega)
            rw [hinv]
            calc denote (memLimbs st.mem xBase i) * denote (memLimbs st.mem xBase n.toNat)
                < 2 ^ (32 * i) * 2 ^ (32 * n.toNat) := by gcongr
              _ = 2 ^ (32 * (i + n.toNat)) := by rw [← pow_add]; congr 1; ring
          · -- denote invariant at j = 0
            rw [show UInt32.ofNat 0 = (0 : UInt32) from rfl,
                show xBase + 4 * (0 : UInt32) = xBase from by bv_decide]
            simp only [Nat.sub_zero, Nat.add_zero, show ((0 : UInt32)).toNat = 0 from rfl]
            rw [hinv]; ring
        · -- inner step
          rintro st₃ s₃ ⟨hpg3, j, ic, carry, sv, hs3, hjic, hxu3, hyu3, hhz3, hden3⟩
          subst hs3
          apply wp_block_cons
          wp_run
          simp
          by_cases hic : ic = 0
          · -- inner exit (j = n): store carry, reestablish outer invariant
            rw [if_pos hic]
            simp
            have hicn : ic.toNat = 0 := by rw [hic]; rfl
            have hjn : j = n.toNat := by omega
            have hsub : (oc - 1).toNat = oc.toNat - 1 := by
              rw [UInt32.toNat_sub]; simp only [show (1 : UInt32).toNat = 1 from rfl]
              have := oc.toNat_lt; omega
            have hwlt : scratchBase.toNat + 4 * (i + j) < 2 ^ 32 := by omega
            have hwa : (scratchBase + 4 * UInt32.ofNat (i + j)).toNat = scratchBase.toNat + 4 * (i + j) := by
              have hsbl := scratchBase.toNat_lt
              rw [UInt32.toNat_add, UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl,
                  UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show i + j < 2 ^ 32 from by omega)]
              omega
            rw [← ofNat_add_u32]
            have hwrite := memLimbs_write_interior st₃.mem scratchBase (i + j) (2 * n.toNat) carry
              (by omega) hsc
            rw [← hjn] at hhz3
            rw [hhz3] at hwrite
            simp only [show ((0 : UInt32)).toNat = 0 from rfl, mul_zero, add_zero] at hwrite
            refine ⟨?_, ⟨hpg3, i + 1, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
            · -- x[i+n] store bound
              rw [hpg3]; omega
            · rw [ofNat_succ_u32]; bv_decide
            · rw [ofNat_succ_u32]; bv_decide
            · rw [hsub]; omega
            · -- x region unchanged
              rw [memLimbs_write32_disjoint st₃.mem _ carry xBase n.toNat (by omega)
                    (by rw [hwa]; omega), hxu3]
            · -- y region unchanged
              rw [memLimbs_write32_disjoint st₃.mem _ carry yBase n.toNat (by omega)
                    (by rw [hwa]; omega), hyu3]
            · -- denote: scratch now holds A(i+1)·X
              rw [hwrite]
              have hsnoc : denote (memLimbs st.mem xBase (i + 1))
                  = denote (memLimbs st.mem xBase i)
                    + (st.mem.read32 (xBase + 4 * UInt32.ofNat i)).toNat * 2 ^ (32 * i) := by
                rw [memLimbs_snoc, denote_append_singleton, memLimbs_length]
              have hd := hden3
              rw [hjn] at hd
              simp only [Nat.sub_self, memLimbs, denote_nil, mul_zero, zero_add] at hd
              rw [hsnoc, hjn, hd]; ring
            · rw [hsub]; omega
          · -- inner continue: multiply-accumulate one limb
            rw [if_neg hic]
            simp
            have hicn : ic.toNat ≠ 0 := fun h => hic (UInt32.toNat_inj.mp (by simp [h]))
            have hjlt : j < n.toNat := by omega
            have hij2n : i + j < 2 * n.toNat := by omega
            have hsubic : (ic - 1).toNat = ic.toNat - 1 := by
              rw [UInt32.toNat_sub]; simp only [show (1 : UInt32).toNat = 1 from rfl]
              have := ic.toNat_lt; omega
            have hsbl := scratchBase.toNat_lt
            have hxbl := xBase.toNat_lt
            have hbx : xBase.toNat + 4 * j < 2 ^ 32 := by omega
            have hbs : scratchBase.toNat + 4 * (i + j) < 2 ^ 32 := by omega
            have hxjv : st₃.mem.read32 (xBase + 4 * UInt32.ofNat j)
                      = st.mem.read32 (xBase + 4 * UInt32.ofNat j) :=
              read32_eq_of_memLimbs_eq n.toNat j st₃.mem st.mem xBase hjlt hxu3
            rw [show (UInt32.ofNat i + UInt32.ofNat j : UInt32) = UInt32.ofNat (i + j) from
                  (ofNat_add_u32 i j).symm]
            have hwa : (scratchBase + 4 * UInt32.ofNat (i + j)).toNat = scratchBase.toNat + 4 * (i + j) := by
              rw [UInt32.toNat_add, UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl,
                  UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show i + j < 2 ^ 32 from by omega)]; omega
            refine ⟨?_, ?_, ?_, ⟨hpg3, j + 1, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
            · rw [hpg3]; omega
            · rw [hpg3]; omega
            · rw [hpg3]; omega
            · rw [ofNat_succ_u32]; bv_decide
            · rw [show UInt32.ofNat (j + 1) = UInt32.ofNat j + 1 from ofNat_succ_u32 j,
                  show UInt32.ofNat (i + j) = UInt32.ofNat i + UInt32.ofNat j from ofNat_add_u32 i j]
              bv_decide
            · rw [hsubic]; omega
            · -- x region unchanged
              rw [memLimbs_write32_disjoint st₃.mem _ _ xBase n.toNat (by omega)
                    (by rw [hwa]; omega), hxu3]
            · -- y region unchanged
              rw [memLimbs_write32_disjoint st₃.mem _ _ yBase n.toNat (by omega)
                    (by rw [hwa]; omega), hyu3]
            · -- high limb still zero
              have hinaddr : (scratchBase + 4 * UInt32.ofNat (i + n.toNat)).toNat
                  = scratchBase.toNat + 4 * (i + n.toNat) := by
                rw [UInt32.toNat_add, UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl,
                    UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show i + n.toNat < 2 ^ 32 from by omega)]
                omega
              rw [show scratchBase + 4 * (UInt32.ofNat i + n)
                    = scratchBase + 4 * UInt32.ofNat (i + n.toNat) from by
                    rw [ofNat_add_u32, UInt32.ofNat_toNat],
                  read32_write32_disjoint st₃.mem _ _ _ (by rw [hwa, hinaddr]; omega), hhz3]
            · -- denote invariant at j+1
              rw [hxjv]
              have hPlt := (st₃.mem.read32 (scratchBase + 4 * UInt32.ofNat (i + j))).toNat_lt
              have hxivlt := (st.mem.read32 (xBase + 4 * UInt32.ofNat i)).toNat_lt
              have hxjvlt := (st.mem.read32 (xBase + 4 * UInt32.ofNat j)).toNat_lt
              have hclt := carry.toNat_lt
              set Pold := (st₃.mem.read32 (scratchBase + 4 * UInt32.ofNat (i + j))).toNat with hPoldd
              set xiv := (st.mem.read32 (xBase + 4 * UInt32.ofNat i)).toNat with hxivd
              set xjv := (st.mem.read32 (xBase + 4 * UInt32.ofNat j)).toNat with hxjvd
              set hsum : Nat := Pold + xiv * xjv + carry.toNat with hsumd
              have hsum64 : hsum % 18446744073709551616 = hsum := by
                have hmul : xiv * xjv ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
                apply Nat.mod_eq_of_lt; rw [hsumd]; omega
              have hwn : (UInt32.ofNat (hsum % 4294967296)).toNat = hsum % 2 ^ 32 := by
                rw [UInt32.toNat_ofNat']; omega
              set cn : Nat := (hsum % 18446744073709551616) >>> 32 % 4294967296 with hcnd
              have hcn : cn = hsum / 2 ^ 32 := by
                rw [hcnd, hsum64, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
              have hkey : (hsum % 2 ^ 32) + 2 ^ 32 * cn = hsum := by rw [hcn]; omega
              have eqI := memLimbs_write_interior st₃.mem scratchBase (i + j) (2 * n.toNat)
                (UInt32.ofNat (hsum % 4294967296)) hij2n hsc
              rw [hwn] at eqI
              have hxsplit : denote (memLimbs st.mem (xBase + 4 * UInt32.ofNat j) (n.toNat - j))
                  = xjv + 2 ^ 32 * denote (memLimbs st.mem (xBase + 4 * UInt32.ofNat (j + 1))
                      (n.toNat - (j + 1))) := by
                obtain ⟨q, hq⟩ : ∃ q, n.toNat - j = q + 1 := ⟨n.toNat - j - 1, by omega⟩
                rw [hq, show memLimbs st.mem (xBase + 4 * UInt32.ofNat j) (q + 1)
                      = st.mem.read32 (xBase + 4 * UInt32.ofNat j)
                        :: memLimbs st.mem ((xBase + 4 * UInt32.ofNat j) + 4) q from rfl,
                    denote_cons,
                    show (xBase + 4 * UInt32.ofNat j) + 4 = xBase + 4 * UInt32.ofNat (j + 1) from by
                      rw [ofNat_succ_u32]; bv_decide,
                    show q = n.toNat - (j + 1) from by omega]
              have e2 : (2 : ℕ) ^ (32 * (i + (j + 1))) = 2 ^ (32 * (i + j)) * 2 ^ 32 := by
                rw [show 32 * (i + (j + 1)) = 32 * (i + j) + 32 from by ring, pow_add]
              rw [e2]
              rw [hxsplit] at hden3
              set Q := 2 ^ (32 * (i + j)) with hQd
              set St' := denote (memLimbs st.mem (xBase + 4 * UInt32.ofNat (j + 1))
                (n.toNat - (j + 1))) with hStd
              set W := denote (memLimbs (st₃.mem.write32 (scratchBase + 4 * UInt32.ofNat (i + j))
                (UInt32.ofNat (hsum % 4294967296))) scratchBase (2 * n.toNat)) with hWd
              set D := denote (memLimbs st₃.mem scratchBase (2 * n.toNat)) with hDd
              have cancel : W + Q * 2 ^ 32 * (xiv * St' + cn) + Q * Pold
                  = denote (memLimbs st.mem xBase i) * denote (memLimbs st.mem xBase n.toNat)
                    + 2 ^ (32 * i) * xiv * denote (memLimbs st.mem xBase n.toNat) + Q * Pold := by
                calc W + Q * 2 ^ 32 * (xiv * St' + cn) + Q * Pold
                    = (W + Q * Pold) + Q * 2 ^ 32 * (xiv * St' + cn) := by ring
                  _ = (D + Q * (hsum % 2 ^ 32)) + Q * 2 ^ 32 * (xiv * St' + cn) := by rw [eqI]
                  _ = D + Q * ((hsum % 2 ^ 32) + 2 ^ 32 * cn) + Q * (2 ^ 32 * xiv * St') := by ring
                  _ = D + Q * hsum + Q * (2 ^ 32 * xiv * St') := by rw [hkey]
                  _ = D + Q * (xiv * (xjv + 2 ^ 32 * St') + carry.toNat) + Q * Pold := by
                        rw [hsumd]; ring
                  _ = _ := by rw [hden3]
              exact Nat.add_right_cancel cancel
            · rw [hsubic]; omega

/-- A `2n`-limb value equals an `n`-limb value iff the low half matches and the
    high half is zero. (`B = 2^(32n)`, both `Pl, Y < B`.) -/
theorem split_eq_iff (B Pl Ph Y : Nat) (_hPl : Pl < B) (hY : Y < B) :
    Pl + B * Ph = Y ↔ (Pl = Y ∧ Ph = 0) := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos Ph with h0 | hpos
    · subst h0; simp at h; exact ⟨h, rfl⟩
    · exfalso; have : B ≤ B * Ph := Nat.le_mul_of_pos_right B hpos; omega
  · rintro ⟨rfl, rfl⟩; simp

/-! ### Glue: compare low half with `y`, check high half is zero, AND the flags. -/

def squareEqGlue : Program := [
  -- compare low n limbs of P (at scratchBase) with y (at yBase) → flag1 (local 4)
  .const 1, .localSet 4,
  .localGet 3, .localSet 5,                      -- pc := scratchBase
  .localGet 1, .localSet 6,                      -- yc := yBase
  .localGet 2, .localSet 7,                      -- cc := n
  .loop 0 0 [ .block 0 0 [
    .localGet 7, .eqz, .br_if 0,
    .localGet 4, .localGet 5, .load32 0, .localGet 6, .load32 0, .eq, .and, .localSet 4,
    .localGet 5, .const 4, .add, .localSet 5,
    .localGet 6, .const 4, .add, .localSet 6,
    .localGet 7, .const 1, .sub, .localSet 7,
    .br 1 ]],
  -- check high n limbs of P (at scratchBase + 4n) are zero → acc (local 8)
  .const 0, .localSet 8,
  .localGet 3, .localGet 2, .const 4, .mul, .add, .localSet 9,    -- ph := scratchBase + n*4
  .localGet 2, .localSet 10,                     -- ch := n
  .loop 0 0 [ .block 0 0 [
    .localGet 10, .eqz, .br_if 0,
    .localGet 8, .localGet 9, .load32 0, .or, .localSet 8,
    .localGet 9, .const 4, .add, .localSet 9,
    .localGet 10, .const 1, .sub, .localSet 10,
    .br 1 ]],
  -- return flag1 & (acc == 0)
  .localGet 4, .localGet 8, .eqz, .and
]

theorem squareEqGlue_correct (m : Module) (st : Store Unit) (xBase yBase n scratchBase : UInt32)
    (g4 g5 g6 g7 g8 g9 g10 g11 : UInt32) (g12 : UInt64)
    (hmem : st.mem.pages * 65536 ≤ 2 ^ 32)
    (hy : yBase.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hsc : scratchBase.toNat + 4 * (2 * n.toNat) ≤ st.mem.pages * 65536) :
    wp m squareEqGlue
        (fun cont => ∃ st' s', cont = .Fallthrough st' s' ∧ st' = st ∧
            s'.values = [.i32 (if denote (memLimbs st.mem scratchBase (2 * n.toNat))
                                  = denote (memLimbs st.mem yBase n.toNat) then 1 else 0)])
        st { params := [.i32 xBase, .i32 yBase, .i32 n, .i32 scratchBase],
             locals := [.i32 g4, .i32 g5, .i32 g6, .i32 g7, .i32 g8, .i32 g9, .i32 g10, .i32 g11,
                        .i64 g12], values := [] } := by
  unfold squareEqGlue
  wp_run
  apply wp_loop_cons
    (Inv := fun st' s' => st' = st ∧ ∃ pc yc cc flag : UInt32,
       s' = ⟨[.i32 xBase, .i32 yBase, .i32 n, .i32 scratchBase],
             [.i32 flag, .i32 pc, .i32 yc, .i32 cc, .i32 g8, .i32 g9, .i32 g10, .i32 g11, .i64 g12],
             []⟩ ∧
       pc.toNat + 4 * cc.toNat ≤ st.mem.pages * 65536 ∧
       yc.toNat + 4 * cc.toNat ≤ st.mem.pages * 65536 ∧
       (flag = 0 ∨ flag = 1) ∧
       (denote (memLimbs st.mem scratchBase n.toNat) = denote (memLimbs st.mem yBase n.toNat) ↔
          (flag = 1 ∧ memLimbs st.mem pc cc.toNat = memLimbs st.mem yc cc.toNat)))
    (μ := fun _ s' => match s'.locals with
      | [_, _, _, .i32 cc, _, _, _, _, _] => cc.toNat | _ => 0)
  · -- init: pc = scratchBase, yc = yBase, cc = n, flag = 1
    refine ⟨rfl, scratchBase, yBase, n, 1, rfl, by omega, hy, Or.inr rfl, ?_⟩
    simp only [true_and]
    exact denote_inj _ _ (by rw [memLimbs_length, memLimbs_length])
  · -- step
    rintro st₂ s₂ ⟨hst, pc, yc, cc, flag, hs, hbpc, hbyc, hflag, hans⟩
    subst hst; subst hs
    apply wp_block_cons
    wp_run
    simp
    by_cases hcc : cc = 0
    · -- compare done; run zero-check loop then combine
      rw [if_pos hcc]
      simp
      have hcc0 : cc.toNat = 0 := by rw [hcc]; rfl
      have hflagm : (denote (memLimbs st₂.mem scratchBase n.toNat)
                      = denote (memLimbs st₂.mem yBase n.toNat)) ↔ flag = 1 := by
        rw [hcc0] at hans; simpa [memLimbs] using hans
      have hsbl := scratchBase.toNat_lt
      have hph : (4 * n + scratchBase) = scratchBase + 4 * UInt32.ofNat n.toNat := by
        rw [UInt32.ofNat_toNat]; bv_decide
      have hphn : (4 * n + scratchBase).toNat = scratchBase.toNat + 4 * n.toNat := by
        rw [UInt32.toNat_add, UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl]; omega
      apply wp_loop_cons
        (Inv := fun st' s' => st' = st₂ ∧ ∃ acc ph2 ch : UInt32,
           s' = ⟨[.i32 xBase, .i32 yBase, .i32 n, .i32 scratchBase],
                 [.i32 flag, .i32 pc, .i32 yc, .i32 cc, .i32 acc, .i32 ph2, .i32 ch, .i32 g11, .i64 g12],
                 []⟩ ∧
           ph2.toNat + 4 * ch.toNat ≤ st₂.mem.pages * 65536 ∧
           (denote (memLimbs st₂.mem (4 * n + scratchBase) n.toNat) = 0 ↔
              (acc = 0 ∧ denote (memLimbs st₂.mem ph2 ch.toNat) = 0)))
        (μ := fun _ s' => match s'.locals with
          | [_, _, _, _, _, _, .i32 ch, _, _] => ch.toNat | _ => 0)
      · -- init: acc = 0, ph2 = 4n+scratch, ch = n
        refine ⟨rfl, 0, 4 * n + scratchBase, n, rfl, by rw [hphn]; omega, ?_⟩
        simp
      · -- step (mirrors natIsZero)
        rintro st₃ s₃ ⟨hst3, acc, ph2, ch, hs3, hbph, hans2⟩
        subst hst3; subst hs3
        apply wp_block_cons
        wp_run
        simp
        by_cases hch : ch = 0
        · -- zero-check done: combine flag1 & (acc == 0)
          rw [if_pos hch]
          simp
          have hch0 : ch.toNat = 0 := by rw [hch]; rfl
          have hhighm : denote (memLimbs st₃.mem (4 * n + scratchBase) n.toNat) = 0 ↔ acc = 0 := by
            rw [hch0] at hans2; simpa [memLimbs] using hans2
          have hsplit2 : denote (memLimbs st₃.mem scratchBase (2 * n.toNat))
              = denote (memLimbs st₃.mem scratchBase n.toNat)
                + 2 ^ (32 * n.toNat) * denote (memLimbs st₃.mem (4 * n + scratchBase) n.toNat) := by
            rw [show 2 * n.toNat = n.toNat + n.toNat from by ring, memLimbs_append, hph,
                denote_append, memLimbs_length]
          have hPl : denote (memLimbs st₃.mem scratchBase n.toNat) < 2 ^ (32 * n.toNat) := by
            have := denote_lt (memLimbs st₃.mem scratchBase n.toNat); rwa [memLimbs_length] at this
          have hYl : denote (memLimbs st₃.mem yBase n.toNat) < 2 ^ (32 * n.toNat) := by
            have := denote_lt (memLimbs st₃.mem yBase n.toNat); rwa [memLimbs_length] at this
          have hverdict : (denote (memLimbs st₃.mem scratchBase (2 * n.toNat))
                            = denote (memLimbs st₃.mem yBase n.toNat))
                ↔ (flag = 1 ∧ acc = 0) := by
            rw [hsplit2, split_eq_iff _ _ _ _ hPl hYl, ← hflagm, ← hhighm]
          have hval : ((if acc = 0 then (1 : UInt32) else 0) &&& flag)
              = if (flag = 1 ∧ acc = 0) then 1 else 0 := by
            by_cases ha : acc = 0 <;> rcases hflag with hf | hf <;> subst hf <;>
              simp only [ha, if_true, if_false, true_and, and_true, and_self] <;> bv_decide
          rw [hval]; exact if_congr hverdict.symm rfl rfl
        · -- zero-check continue (mirrors natIsZero)
          rw [if_neg hch]
          simp
          have hchn : ch.toNat ≠ 0 := fun h => hch (UInt32.toNat_inj.mp (by simp [h]))
          have hsubc : (ch - 1).toNat = ch.toNat - 1 := by
            rw [UInt32.toNat_sub]; simp only [show (1 : UInt32).toNat = 1 from rfl]
            have := ch.toNat_lt; omega
          have hph2 := ph2.toNat_lt
          have hsplit : denote (memLimbs st₃.mem ph2 ch.toNat) = 0
              ↔ (st₃.mem.read32 ph2 = 0 ∧ denote (memLimbs st₃.mem (4 + ph2) (ch.toNat - 1)) = 0) := by
            obtain ⟨jj, hjj⟩ : ∃ jj, ch.toNat = jj + 1 := ⟨ch.toNat - 1, by omega⟩
            rw [hjj]
            show denote (st₃.mem.read32 ph2 :: memLimbs st₃.mem (ph2 + 4) jj) = 0 ↔ _
            rw [denote_cons_eq_zero, show (ph2 : UInt32) + 4 = 4 + ph2 from by bv_decide,
                Nat.add_sub_cancel]
          refine ⟨by omega, ⟨by rw [hsubc]; omega, ?_⟩, by rw [hsubc]; omega⟩
          rw [hsubc, hans2, hsplit]
          tauto
    · -- compare continue (mirrors bigEq)
      have hcn : cc.toNat ≠ 0 := fun h => hcc (UInt32.toNat_inj.mp (by simp [h]))
      have hsub : (cc - 1).toNat = cc.toNat - 1 := by
        rw [UInt32.toNat_sub]; simp only [show (1 : UInt32).toNat = 1 from rfl]
        have := cc.toNat_lt; omega
      have hpc := pc.toNat_lt
      have hyc := yc.toNat_lt
      obtain ⟨jj, hjj⟩ : ∃ jj, cc.toNat = jj + 1 := ⟨cc.toNat - 1, by omega⟩
      set eqr : UInt32 := if st₂.mem.read32 pc = st₂.mem.read32 yc then 1 else 0 with heqr
      have heqr01 : eqr = 0 ∨ eqr = 1 := by rw [heqr]; split <;> [exact Or.inr rfl; exact Or.inl rfl]
      have e4a : (4 : UInt32) + pc = pc + 4 := by bv_decide
      have e4b : (4 : UInt32) + yc = yc + 4 := by bv_decide
      have hcj : (cc - 1).toNat = jj := by rw [hsub, hjj]; omega
      have heqr1 : (eqr = 1) ↔ (st₂.mem.read32 pc = st₂.mem.read32 yc) := by
        rw [heqr]; split <;> simp_all
      rw [if_neg hcc]
      simp
      refine ⟨by omega, by omega,
        ⟨by rw [hsub]; omega, by rw [hsub]; omega, and_zero_one eqr flag heqr01 hflag, ?_⟩,
        by rw [hsub]; omega⟩
      rw [e4a, e4b, hcj, hans, hjj, memLimbs_eq_cons, and_eq_one eqr flag heqr01 hflag, heqr1]
      tauto

/-! ### The witness verifier: `returns 1 ↔ ⟦x⟧² = ⟦y⟧`. -/

def natSquareEq : Program := mulPhase ++ squareEqGlue

/-- **Square-witness verifier, correct over ℕ†.** Given `n`-limb numbers `x`
    (at `xBase`) and `y` (at `yBase`) and a zeroed `2n`-limb scratch region (at
    `scratchBase`, disjoint from both inputs), `natSquareEq` returns `1` exactly
    when `⟦x⟧² = ⟦y⟧`. Since `n` and the limb contents are arbitrary, this
    decides `y = x²` for every representable pair. -/
theorem natSquareEq_correct (m : Module) (st : Store Unit) (xBase yBase n scratchBase : UInt32)
    (hmem : st.mem.pages * 65536 ≤ 2 ^ 32)
    (hx : xBase.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hy : yBase.toNat + 4 * n.toNat ≤ st.mem.pages * 65536)
    (hsc : scratchBase.toNat + 4 * (2 * n.toNat) < 2 ^ 32)
    (hscb : scratchBase.toNat + 4 * (2 * n.toNat) ≤ st.mem.pages * 65536)
    (hzero : denote (memLimbs st.mem scratchBase (2 * n.toNat)) = 0)
    (hdSX : scratchBase.toNat + 4 * (2 * n.toNat) ≤ xBase.toNat
            ∨ xBase.toNat + 4 * n.toNat ≤ scratchBase.toNat)
    (hdSY : scratchBase.toNat + 4 * (2 * n.toNat) ≤ yBase.toNat
            ∨ yBase.toNat + 4 * n.toNat ≤ scratchBase.toNat) :
    wp m natSquareEq
        (fun cont => ∃ st' s', cont = .Fallthrough st' s' ∧
            s'.values = [.i32 (if denote (memLimbs st.mem xBase n.toNat) ^ 2
                                  = denote (memLimbs st.mem yBase n.toNat) then 1 else 0)])
        st { params := [.i32 xBase, .i32 yBase, .i32 n, .i32 scratchBase],
             locals := [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0],
             values := [] } := by
  apply wp_seq
  apply (mulPhase_correct m st xBase yBase n scratchBase hmem hx hy hsc hscb hzero hdSX hdSY).imp
  rintro c ⟨st', q4, q5, q6, q7, q8, q9, q10, q11, q12, rfl, hpages, hxu, hyu, hden⟩
  have hmem' : st'.mem.pages * 65536 ≤ 2 ^ 32 := by rw [hpages]; exact hmem
  have hy' : yBase.toNat + 4 * n.toNat ≤ st'.mem.pages * 65536 := by rw [hpages]; exact hy
  have hsc' : scratchBase.toNat + 4 * (2 * n.toNat) ≤ st'.mem.pages * 65536 := by
    rw [hpages]; exact hscb
  apply (squareEqGlue_correct m st' xBase yBase n scratchBase q4 q5 q6 q7 q8 q9 q10 q11 q12
    hmem' hy' hsc').imp
  rintro c' ⟨st'', s'', rfl, hsteq, hvals⟩
  subst hsteq
  refine ⟨st'', s'', rfl, ?_⟩
  rw [hvals, hden, show denote (memLimbs st''.mem yBase n.toNat)
        = denote (memLimbs st.mem yBase n.toNat) from by rw [hyu]]

end Wasm
