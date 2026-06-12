import Project.Itoa.Proofs

/-! # Dev scratch for `func40` (merged into Proofs.lean when done)

Clones of the private helpers from `Proofs.lean` that the development
needs (private decls are file-scoped). -/

namespace Project.Itoa.Proofs

open Wasm

/-- `(a + b).toNat = a.toNat + b.toNat` when the sum does not wrap. -/
private theorem toNat_add_of_lt (a b : UInt32) (h : a.toNat + b.toNat < 4294967296) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt h

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

@[simp] private theorem read32_write32_same' (m : Mem) (a v : UInt32) :
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

@[simp] private theorem read32_write64_disjoint (m : Mem) (a b : UInt32) (v : UInt64)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 8 ≤ b.toNat) :
    (m.write64 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write64_bytes_of_disjoint m a v b.toNat (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write64_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

@[simp] private theorem read32_write32_disjoint' (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [write32_bytes_of_disjoint m a v b.toNat (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

@[simp] private theorem read64_write8_disjoint (m : Mem) (a b : UInt32) (v : UInt8)
    (h : a.toNat < b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    (m.write8 a v).read64 b = m.read64 b := by
  simp only [Mem.read64, Mem.write8]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] private theorem read32_write8_disjoint (m : Mem) (a b : UInt32) (v : UInt8)
    (h : a.toNat < b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write8 a v).read32 b = m.read32 b := by
  simp only [Mem.read32, Mem.write8]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem write8_bytes_of_disjoint (m : Mem) (a : UInt32) (v : UInt8) (i : Nat)
    (h : i ≠ a.toNat) :
    (m.write8 a v).bytes i = m.bytes i := by
  simp [Mem.write8, h]

/-! ## `func40`: the `itoa`-crate u64 core

`func40 (n, out)` writes the decimal digits of `n` into the 20-byte
buffer at `out`, right-aligned (the last digit lands at `out+19`), and
returns the start offset `20 - numDigits n.toNat`. The chunk loop
peels four digits per iteration (`v % 10000`, split by the `/100`
magic divider `func38`, each two-digit pair read from the
`DIGIT_TABLE` via `func39`); the straight-line tails after the loop
handle the remaining 1-3 digits. -/

/-- `read32` only looks at four bytes. -/
private theorem read32_congr_bytes (m1 m2 : Mem) (a : UInt32)
    (h : ∀ i : Nat, a.toNat ≤ i → i < a.toNat + 4 → m1.bytes i = m2.bytes i) :
    m1.read32 a = m2.read32 a := by
  simp only [Mem.read32]
  rw [h a.toNat (by omega) (by omega), h (a.toNat + 1) (by omega) (by omega),
      h (a.toNat + 2) (by omega) (by omega), h (a.toNat + 3) (by omega) (by omega)]

/-- `read64` only looks at eight bytes. -/
private theorem read64_congr_bytes (m1 m2 : Mem) (a : UInt32)
    (h : ∀ i : Nat, a.toNat ≤ i → i < a.toNat + 8 → m1.bytes i = m2.bytes i) :
    m1.read64 a = m2.read64 a := by
  simp only [Mem.read64]
  rw [h a.toNat (by omega) (by omega), h (a.toNat + 1) (by omega) (by omega),
      h (a.toNat + 2) (by omega) (by omega), h (a.toNat + 3) (by omega) (by omega),
      h (a.toNat + 4) (by omega) (by omega), h (a.toNat + 5) (by omega) (by omega),
      h (a.toNat + 6) (by omega) (by omega), h (a.toNat + 7) (by omega) (by omega)]

/-- Reading the low 32-bit word of a freshly written 64-bit slot. -/
private theorem read32_write64_same_low (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).read32 a = v.toUInt32 := by
  simp only [Mem.read32, Mem.write64]
  have e1 : a.toNat + 1 ≠ a.toNat := by omega
  have e2 : a.toNat + 2 ≠ a.toNat := by omega
  have e3 : a.toNat + 3 ≠ a.toNat := by omega
  have e21 : a.toNat + 2 ≠ a.toNat + 1 := by omega
  have e31 : a.toNat + 3 ≠ a.toNat + 1 := by omega
  have e32 : a.toNat + 3 ≠ a.toNat + 2 := by omega
  simp only [e1, e2, e3, e21, e31, e32, if_true, if_false]
  bv_decide

/-- `numDigits` from a two-sided power-of-ten bound. -/
private theorem numDigits_eq_of_bounds (n d : Nat) (hd : 1 ≤ d)
    (hlo : 10 ^ (d - 1) ≤ n) (hhi : n < 10 ^ d) : numDigits n = d := by
  have h1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by norm_num)) hlo
  have hup := lt_ten_pow_numDigits n
  have hlow := ten_pow_numDigits_le n h1
  have hDd : numDigits n - 1 < d :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp (lt_of_le_of_lt hlow hhi)
  have hdD : d - 1 < numDigits n :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp (lt_of_le_of_lt hlo hup)
  have := numDigits_pos n
  omega

/-- `omega` preprocessing is exponential in the number of
`(fp + c).toNat = fp.toNat + c`-shaped context facts (each one triggers a
`UInt32`-add expansion; ~12 of them already cost seconds, ~19 minutes).
`Frozen` hides such facts from `omega`'s hypothesis scan (it only unfolds
reducible definitions); cite `h.out` at the use site to expose the fact
to exactly the call that needs it. -/
private def Frozen (p : Prop) : Prop := p

private theorem Frozen.mk {p : Prop} (h : p) : Frozen p := h
private theorem Frozen.out {p : Prop} (h : Frozen p) : p := h

/-- Loop invariant of `func40`'s chunk loop (named so `simp` passes over
the loop continuation leave it folded): after `k` peeled chunks the value
slot holds `n / 10^(4k)`, the position slot `20 - 4k`, the low `4k` digits
sit at `out + 20 - 4k ..`, and everything outside frame ∪ written-digits
is untouched. -/
private def func40ChunkInv (n : UInt64) (out fp : UInt32) (B : Nat → UInt8)
    (st' : Store Unit) (s' : Locals) : Prop :=
  st'.mem.pages = 17 ∧
  st'.globals.globals[0]? = some (.i32 fp) ∧
  (∃ k : Nat,
    (k = 0 ∨ 10 ^ (4 * k - 1) ≤ n.toNat) ∧
    st'.mem.read64 (fp + 24) = UInt64.ofNat (n.toNat / 10 ^ (4 * k)) ∧
    st'.mem.read32 (fp + 20) = UInt32.ofNat (20 - 4 * k) ∧
    (∀ p : Nat, 20 - 4 * k ≤ p → p < 20 →
      st'.mem.bytes (out.toNat + p) =
        UInt8.ofNat (48 + n.toNat / 10 ^ (19 - p) % 10)) ∧
    (∀ i : Nat, (i < fp.toNat - 48 ∨ fp.toNat + 176 ≤ i) →
      (i < out.toNat + (20 - 4 * k) ∨ out.toNat + 20 ≤ i) →
      st'.mem.bytes i = B i)) ∧
  (∃ w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
      w23 w24 : Value,
    s' = { params := [Value.i64 n, Value.i32 out],
           locals := [
             Value.i32 fp, w3, w4, w5, w6,
             w7, w8, w9, w10, w11,
             w12, w13, w14, w15, w16,
             w17, w18, w19, w20, w21,
             w22, w23, w24, Value.i32 0, Value.i32 0,
             Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0,
             Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0,
             Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0],
           values := [] })

/-- Termination measure of the chunk loop: the value being peeled. -/
private def func40ChunkMeasure (fp : UInt32) (st' : Store Unit) (_ : Locals) : Nat :=
  (st'.mem.read64 (fp + 24)).toNat

/-- The store8-value normal form of a table digit byte, folded back. -/
private theorem digit_byte_roundtrip (d : Nat) (h : d < 10) :
    (((48 : UInt32) + (UInt8.ofNat d).toUInt32) % 256).toUInt8 = UInt8.ofNat (48 + d) := by
  interval_cases d <;> decide

set_option maxHeartbeats 16000000 in
/-- The chunk loop of `func40`, standalone: while the running value
`v` (slot `fp+24`) exceeds 999, peel `v % 10000` and write its four
decimal digits at `out + pos - 4 .. out + pos - 1` (`pos` is the slot
`fp+20`, counting down from 20 in steps of 4). Exits via the `v ≤ 999`
`br_if 1`, which surfaces as `.Break 0` at the loop-instruction level. -/
private theorem func40_chunk_loop (env : HostEnv Unit) (n : UInt64) (out fp : UInt32)
    (B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st1 : Store Unit)
    (hfp48 : 48 ≤ fp.toNat)
    (hfp_out : fp.toNat + 176 ≤ out.toNat)
    (hout : out.toNat + 20 ≤ 1048576)
    (hpg : st1.mem.pages = 17)
    (hgl : st1.globals.globals[0]? = some (.i32 fp))
    (hv : st1.mem.read64 (fp + 24) = n)
    (hpos : st1.mem.read32 (fp + 20) = 20)
    (htab : ∀ t : Nat, t < 200 →
      B (1049408 + t) = («module».initialStore (α := Unit)).mem.bytes (1049408 + t))
    (hpres : ∀ i : Nat, i < fp.toNat - 48 ∨ fp.toNat + 176 ≤ i →
      st1.mem.bytes i = B i)
    (hexit : ∀ (st' : Store Unit) (k : Nat)
        (w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
          w23 w24 : Value),
      st'.mem.pages = 17 →
      st'.globals.globals[0]? = some (.i32 fp) →
      n.toNat / 10 ^ (4 * k) ≤ 999 →
      (k = 0 ∨ 10 ^ (4 * k - 1) ≤ n.toNat) →
      st'.mem.read64 (fp + 24) = UInt64.ofNat (n.toNat / 10 ^ (4 * k)) →
      st'.mem.read32 (fp + 20) = UInt32.ofNat (20 - 4 * k) →
      (∀ p : Nat, 20 - 4 * k ≤ p → p < 20 →
        st'.mem.bytes (out.toNat + p) =
          UInt8.ofNat (48 + n.toNat / 10 ^ (19 - p) % 10)) →
      (∀ i : Nat, (i < fp.toNat - 48 ∨ fp.toNat + 176 ≤ i) →
        (i < out.toNat + (20 - 4 * k) ∨ out.toNat + 20 ≤ i) →
        st'.mem.bytes i = B i) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 out],
          locals := [
            Value.i32 fp, w3, w4, w5, w6,
            w7, w8, w9, w10, w11,
            w12, w13, w14, w15, w16,
            w17, w18, w19, w20, w21,
            w22, w23, w24, Value.i32 0, Value.i32 0,
            Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0,
            Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0,
            Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0],
          values := [] })) :
    wp «module»
      (
      .loop 0 0 [
        .const (8 : UInt32),
        .const (1 : UInt32),
        .gtU,
        .const (1 : UInt32),
        .and,
        .eqz,
        .br_if 1,
        .localGet 2,
        .load64 (24 : UInt32),
        .localSet 3,
        .localGet 2,
        .const (48 : UInt32),
        .add,
        .const (999 : UInt32),
        .call 41,
        .localGet 3,
        .localGet 2,
        .load64 (48 : UInt32),
        .localGet 2,
        .load64 (56 : UInt32),
        .const (1049161 : UInt32),
        .const (52 : UInt32),
        .const (1049348 : UInt32),
        .call 42,
        .gtUI64,
        .const (1 : UInt32),
        .and,
        .eqz,
        .br_if 1,
        .localGet 2,
        .localGet 2,
        .load32 (20 : UInt32),
        .const (4 : UInt32),
        .sub,
        .store32 (20 : UInt32),
        .localGet 2,
        .const (80 : UInt32),
        .add,
        .const (10000 : UInt32),
        .call 41,
        .localGet 2,
        .load64 (80 : UInt32),
        .localGet 2,
        .load64 (88 : UInt32),
        .const (1049294 : UInt32),
        .const (52 : UInt32),
        .const (1049348 : UInt32),
        .call 42,
        .localSet 4,
        .localGet 2,
        .localGet 4,
        .store64 (96 : UInt32),
        .localGet 2,
        .load64 (24 : UInt32),
        .localSet 5,
        .block 0 0 [
          .block 0 0 [
            .block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .block 0 0 [
                    .block 0 0 [
                      .block 0 0 [
                        .block 0 0 [
                          .block 0 0 [
                            .block 0 0 [
                              .localGet 4,
                              .constI64 (0 : UInt64),
                              .eqI64,
                              .const (1 : UInt32),
                              .and,
                              .br_if 0,
                              .localGet 5,
                              .localGet 4,
                              .remUI64,
                              .localSet 6,
                              .localGet 2,
                              .localGet 6,
                              .store64 (104 : UInt32),
                              .localGet 4,
                              .constI64 (0 : UInt64),
                              .eqI64,
                              .const (1 : UInt32),
                              .and,
                              .br_if 2,
                              .br 1
                            ],
                            .const (1049348 : UInt32),
                            .call 115,
                            .unreachable
                          ],
                          .localGet 2,
                          .localGet 2,
                          .load64 (24 : UInt32),
                          .localGet 4,
                          .divUI64,
                          .store64 (24 : UInt32),
                          .localGet 2,
                          .localGet 6,
                          .wrapI64,
                          .call 38,
                          .localGet 2,
                          .load32 (4 : UInt32),
                          .localSet 7,
                          .localGet 2,
                          .load32 (0 : UInt32),
                          .localSet 8,
                          .localGet 2,
                          .localGet 8,
                          .store32 (112 : UInt32),
                          .localGet 2,
                          .localGet 7,
                          .store32 (116 : UInt32),
                          .localGet 2,
                          .load32 (20 : UInt32),
                          .const (0 : UInt32),
                          .add,
                          .localSet 9,
                          .localGet 9,
                          .const (20 : UInt32),
                          .ltU,
                          .const (1 : UInt32),
                          .and,
                          .br_if 1,
                          .br 2
                        ],
                        .const (1049348 : UInt32),
                        .call 114,
                        .unreachable
                      ],
                      .localGet 1,
                      .localGet 9,
                      .add,
                      .localSet 10,
                      .localGet 8,
                      .const (1 : UInt32),
                      .shl,
                      .const (0 : UInt32),
                      .add,
                      .localSet 11,
                      .const (1049408 : UInt32),
                      .const (200 : UInt32),
                      .localGet 11,
                      .const (1049348 : UInt32),
                      .call 39,
                      .load8U (0 : UInt32),
                      .localSet 12,
                      .localGet 2,
                      .localGet 10,
                      .store32 (144 : UInt32),
                      .localGet 2,
                      .localGet 12,
                      .store8 (151 : UInt32),
                      .localGet 10,
                      .localGet 12,
                      .store8 (0 : UInt32),
                      .localGet 2,
                      .load32 (20 : UInt32),
                      .const (1 : UInt32),
                      .add,
                      .localSet 13,
                      .localGet 13,
                      .const (20 : UInt32),
                      .ltU,
                      .const (1 : UInt32),
                      .and,
                      .br_if 1,
                      .br 2
                    ],
                    .localGet 9,
                    .const (20 : UInt32),
                    .const (1049348 : UInt32),
                    .call 102,
                    .unreachable
                  ],
                  .localGet 1,
                  .localGet 13,
                  .add,
                  .localSet 14,
                  .localGet 8,
                  .const (1 : UInt32),
                  .shl,
                  .const (1 : UInt32),
                  .add,
                  .localSet 15,
                  .const (1049408 : UInt32),
                  .const (200 : UInt32),
                  .localGet 15,
                  .const (1049348 : UInt32),
                  .call 39,
                  .load8U (0 : UInt32),
                  .localSet 16,
                  .localGet 2,
                  .localGet 14,
                  .store32 (136 : UInt32),
                  .localGet 2,
                  .localGet 16,
                  .store8 (143 : UInt32),
                  .localGet 14,
                  .localGet 16,
                  .store8 (0 : UInt32),
                  .localGet 2,
                  .load32 (20 : UInt32),
                  .const (2 : UInt32),
                  .add,
                  .localSet 17,
                  .localGet 17,
                  .const (20 : UInt32),
                  .ltU,
                  .const (1 : UInt32),
                  .and,
                  .br_if 1,
                  .br 2
                ],
                .localGet 13,
                .const (20 : UInt32),
                .const (1049348 : UInt32),
                .call 102,
                .unreachable
              ],
              .localGet 1,
              .localGet 17,
              .add,
              .localSet 18,
              .localGet 7,
              .const (1 : UInt32),
              .shl,
              .const (0 : UInt32),
              .add,
              .localSet 19,
              .const (1049408 : UInt32),
              .const (200 : UInt32),
              .localGet 19,
              .const (1049348 : UInt32),
              .call 39,
              .load8U (0 : UInt32),
              .localSet 20,
              .localGet 2,
              .localGet 18,
              .store32 (128 : UInt32),
              .localGet 2,
              .localGet 20,
              .store8 (135 : UInt32),
              .localGet 18,
              .localGet 20,
              .store8 (0 : UInt32),
              .localGet 2,
              .load32 (20 : UInt32),
              .const (3 : UInt32),
              .add,
              .localSet 21,
              .localGet 21,
              .const (20 : UInt32),
              .ltU,
              .const (1 : UInt32),
              .and,
              .br_if 1,
              .br 2
            ],
            .localGet 17,
            .const (20 : UInt32),
            .const (1049348 : UInt32),
            .call 102,
            .unreachable
          ],
          .localGet 1,
          .localGet 21,
          .add,
          .localSet 22,
          .localGet 7,
          .const (1 : UInt32),
          .shl,
          .const (1 : UInt32),
          .add,
          .localSet 23,
          .const (1049408 : UInt32),
          .const (200 : UInt32),
          .localGet 23,
          .const (1049348 : UInt32),
          .call 39,
          .load8U (0 : UInt32),
          .localSet 24,
          .localGet 2,
          .localGet 22,
          .store32 (120 : UInt32),
          .localGet 2,
          .localGet 24,
          .store8 (127 : UInt32),
          .localGet 22,
          .localGet 24,
          .store8 (0 : UInt32),
          .br 1
        ]
      ] :: rest) Q st1
      { params := [Value.i64 n, Value.i32 out],
        locals := [
          Value.i32 fp, Value.i64 0, Value.i64 0, Value.i64 0, Value.i64 0,
          Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0,
          Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0,
          Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0,
          Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0,
          Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0,
          Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0,
          Value.i32 0, Value.i32 0, Value.i32 0, Value.i32 0],
        values := [] } env := by
  have hglb : fp.toNat ≤ 1048556 := by omega
  have t4 : Frozen ((fp + 4).toNat = fp.toNat + 4) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t20 : Frozen ((fp + 20).toNat = fp.toNat + 20) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t24 : Frozen ((fp + 24).toNat = fp.toNat + 24) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t48 : Frozen ((fp + 48).toNat = fp.toNat + 48) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t56 : Frozen ((fp + 56).toNat = fp.toNat + 56) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t80 : Frozen ((fp + 80).toNat = fp.toNat + 80) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t88 : Frozen ((fp + 88).toNat = fp.toNat + 88) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t96 : Frozen ((fp + 96).toNat = fp.toNat + 96) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t104 : Frozen ((fp + 104).toNat = fp.toNat + 104) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t112 : Frozen ((fp + 112).toNat = fp.toNat + 112) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t116 : Frozen ((fp + 116).toNat = fp.toNat + 116) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t120 : Frozen ((fp + 120).toNat = fp.toNat + 120) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t127 : Frozen ((fp + 127).toNat = fp.toNat + 127) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t128 : Frozen ((fp + 128).toNat = fp.toNat + 128) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t135 : Frozen ((fp + 135).toNat = fp.toNat + 135) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t136 : Frozen ((fp + 136).toNat = fp.toNat + 136) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t143 : Frozen ((fp + 143).toNat = fp.toNat + 143) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t144 : Frozen ((fp + 144).toNat = fp.toNat + 144) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have t151 : Frozen ((fp + 151).toNat = fp.toNat + 151) :=
    Frozen.mk (by rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl)
  have h48c : (48 : UInt32) + fp = fp + 48 := by bv_decide
  have h56c : fp + 48 + 8 = fp + 56 := by bv_decide
  have h80c : (80 : UInt32) + fp = fp + 80 := by bv_decide
  have h88c : fp + 80 + 8 = fp + 88 := by bv_decide
  apply wp_loop_cons (Inv := func40ChunkInv n out fp B)
    (μ := func40ChunkMeasure fp)
  · -- entry: `k = 0`
    unfold func40ChunkInv
    refine ⟨hpg, hgl, ⟨0, Or.inl rfl, ?_, ?_,
        fun p hp1 hp2 => absurd hp1 (by omega), fun i h1 _ => hpres i h1⟩,
      .i64 0, .i64 0, .i64 0, .i64 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
      .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
      .i32 0, .i32 0, .i32 0, .i32 0, rfl⟩
    · simpa using hv
    · simpa using hpos
  · -- step
    intro st' s' hInv
    unfold func40ChunkInv at hInv
    obtain ⟨hpg', hgl', ⟨k, hk0, hv24, hp20, hdig, hfr⟩, hw⟩ := hInv
    obtain ⟨w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17,
      w18, w19, w20, w21, w22, w23, w24, rfl⟩ := hw
    obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hgl'
    have hnsz : n.toNat < 18446744073709551616 := by
      have := UInt64.toNat_lt_size n
      simpa [UInt64.size] using this
    have hmle : n.toNat / 10 ^ (4 * k) ≤ n.toNat := Nat.div_le_self _ _
    have hofm : (UInt64.ofNat (n.toNat / 10 ^ (4 * k))).toNat = n.toNat / 10 ^ (4 * k) :=
      UInt64.toNat_ofNat_of_lt'
        (by have hsz : UInt64.size = 18446744073709551616 := rfl; omega)
    have p24 : ¬ (1114112 < fp.toNat + 24 + 8) := by omega
    wp_run
    simp [hpg', hv24, p24]
    apply wp_call_of_terminates (func41_spec env _ fp (48 + fp) 999
      (by simpa using hpg') (by simpa using hgl') (by omega) (by omega)
      (by rw [h48c, t48.out]; omega) (by decide))
    rintro st2 vs2 ⟨hpg2, hgl2, hrs2, hr48, hr56, hfr2⟩
    obtain ⟨hglen2, -⟩ := List.getElem?_eq_some_iff.mp hgl2
    subst hrs2
    rw [h48c] at hr48 hfr2
    rw [h48c, h56c] at hr56
    rw [show ((999 : UInt32)).toUInt64 = 999 from by decide] at hr56
    have p48 : ¬ (1114112 < fp.toNat + 48 + 8) := by omega
    have p56 : ¬ (1114112 < fp.toNat + 56 + 8) := by omega
    wp_run
    simp [hpg2, hr48, hr56, p48, p56]
    apply wp_call_of_terminates_frame
      (args := [.i32 1049348, .i32 52, .i32 1049161, .i64 999, .i64 0])
      (rem := [.i64 (UInt64.ofNat (n.toNat / 10 ^ (4 * k)))])
      (f := ⟨[.i64, .i64, .i32, .i32, .i32], [.i32, .i64], func42, [.i64]⟩)
      rfl rfl rfl rfl
      (func42_spec env _ fp 0 999 1049161 52 1049348
        (by simpa using hpg2) (by simpa using hgl2) (by omega) (by omega) (by decide))
    rintro st3 vs3 ⟨hpg3, hgl3, hrs3, hfr3⟩
    obtain ⟨hglen3, -⟩ := List.getElem?_eq_some_iff.mp hgl3
    subst hrs3
    have hv24' : st3.mem.read64 (fp + 24) = UInt64.ofNat (n.toNat / 10 ^ (4 * k)) := by
      rw [read64_congr_bytes st3.mem st2.mem _
            (fun i h1 h2 => hfr3 i (by have a := t24.out; omega)),
          read64_congr_bytes st2.mem st'.mem _
            (fun i h1 h2 => hfr2 i (by have a := t24.out; omega)
              (by have a := t24.out; have b := t48.out; omega)),
          hv24]
    have hp20' : st3.mem.read32 (fp + 20) = UInt32.ofNat (20 - 4 * k) := by
      rw [read32_congr_bytes st3.mem st2.mem _
            (fun i h1 h2 => hfr3 i (by have a := t20.out; omega)),
          read32_congr_bytes st2.mem st'.mem _
            (fun i h1 h2 => hfr2 i (by have a := t20.out; omega)
              (by have a := t20.out; have b := t48.out; omega)),
          hp20]
    have hdig3 : ∀ p : Nat, 20 - 4 * k ≤ p → p < 20 →
        st3.mem.bytes (out.toNat + p) =
          UInt8.ofNat (48 + n.toNat / 10 ^ (19 - p) % 10) := fun p hp1 hp2 => by
      rw [hfr3 _ (by omega), hfr2 _ (by omega) (by have b := t48.out; omega)]
      exact hdig p hp1 hp2
    have hB3 : ∀ i : Nat, (i < fp.toNat - 48 ∨ fp.toNat + 176 ≤ i) →
        (i < out.toNat + (20 - 4 * k) ∨ out.toNat + 20 ≤ i) →
        st3.mem.bytes i = B i := fun i h1 h2 => by
      rw [hfr3 i (by omega), hfr2 i (by omega) (by have b := t48.out; omega)]
      exact hfr i h1 h2
    have hgtiff : ((999 : UInt64) < UInt64.ofNat (n.toNat / 10 ^ (4 * k))) ↔
        999 < n.toNat / 10 ^ (4 * k) := by
      rw [UInt64.lt_iff_toNat_lt, hofm]
      simp
    wp_run
    by_cases hgt : 999 < n.toNat / 10 ^ (4 * k)
    · -- `v > 999`: peel one more chunk of four digits
      have h1000 : 1000 * 10 ^ (4 * k) ≤ n.toNat := by
        have h1 : 1000 ≤ n.toNat / 10 ^ (4 * k) := by omega
        calc 1000 * 10 ^ (4 * k) ≤ n.toNat / 10 ^ (4 * k) * 10 ^ (4 * k) :=
              Nat.mul_le_mul_right _ h1
          _ ≤ n.toNat := Nat.div_mul_le_self _ _
      have hk4 : k ≤ 4 := by
        by_contra hk5
        have h20 : (20 : Nat) ≤ 4 * k := by omega
        have hpow : (10 : Nat) ^ 20 ≤ 10 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) h20
        have hlit : (10 : Nat) ^ 20 = 100000000000000000000 := by norm_num
        have h1 : (10 : Nat) ^ (4 * k) ≤ 1000 * 10 ^ (4 * k) :=
          Nat.le_mul_of_pos_left _ (by norm_num)
        omega
      have hof20 : (UInt32.ofNat (20 - 4 * k)).toNat = 20 - 4 * k :=
        UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
      have hof16 : (UInt32.ofNat (16 - 4 * k)).toNat = 16 - 4 * k :=
        UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
      have hsub4 : UInt32.ofNat (20 - 4 * k) - 4 = UInt32.ofNat (16 - 4 * k) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_sub_of_le _ 4 (by
              rw [UInt32.le_iff_toNat_le, hof20]; simp; omega), hof20, hof16]
        simp
        omega
      have p20 : ¬ (1114112 < fp.toNat + 20 + 4) := by omega
      simp [hgtiff, hgt, hpg3, hp20', p20, hsub4]
      apply wp_call_of_terminates (func41_spec env _ fp (80 + fp) 10000
        (by simpa using hpg3) (by simpa using hgl3) (by omega) (by omega)
        (by rw [h80c, t80.out]; omega) (by decide))
      rintro st4 vs4 ⟨hpg4, hgl4, hrs4, hr80, hr88, hfr4⟩
      obtain ⟨hglen4, -⟩ := List.getElem?_eq_some_iff.mp hgl4
      subst hrs4
      rw [h80c] at hr80 hfr4
      rw [h80c, h88c] at hr88
      rw [show ((10000 : UInt32)).toUInt64 = 10000 from by decide] at hr88
      have p80 : ¬ (1114112 < fp.toNat + 80 + 8) := by omega
      have p88 : ¬ (1114112 < fp.toNat + 88 + 8) := by omega
      wp_run
      simp [hpg4, hr80, hr88, p80, p88]
      apply wp_call_of_terminates (func42_spec env _ fp 0 10000 1049294 52 1049348
        (by simpa using hpg4) (by simpa using hgl4) (by omega) (by omega) (by decide))
      rintro st5 vs5 ⟨hpg5, hgl5, hrs5, hfr5⟩
      obtain ⟨hglen5, -⟩ := List.getElem?_eq_some_iff.mp hgl5
      subst hrs5
      have hv24_5 : st5.mem.read64 (fp + 24) = UInt64.ofNat (n.toNat / 10 ^ (4 * k)) := by
        rw [read64_congr_bytes st5.mem st4.mem _
              (fun i h1 h2 => hfr5 i (by have a := t24.out; omega)),
            read64_congr_bytes st4.mem _ _
              (fun i h1 h2 => hfr4 i (by have a := t24.out; omega)
                (by have a := t24.out; have b := t80.out; omega)),
            read64_write32_disjoint _ _ _ _
              (by have a := t20.out; have b := t24.out; omega), hv24']
      have hp20_5 : st5.mem.read32 (fp + 20) = UInt32.ofNat (16 - 4 * k) := by
        rw [read32_congr_bytes st5.mem st4.mem _
              (fun i h1 h2 => hfr5 i (by have a := t20.out; omega)),
            read32_congr_bytes st4.mem _ _
              (fun i h1 h2 => hfr4 i (by have a := t20.out; omega)
                (by have a := t20.out; have b := t80.out; omega)),
            read32_write32_same']
      have hdig5 : ∀ p : Nat, 20 - 4 * k ≤ p → p < 20 →
          st5.mem.bytes (out.toNat + p) =
            UInt8.ofNat (48 + n.toNat / 10 ^ (19 - p) % 10) := fun p hp1 hp2 => by
        rw [hfr5 _ (by omega), hfr4 _ (by omega) (by have b := t80.out; omega),
            write32_bytes_of_disjoint _ _ _ _ (by have a := t20.out; omega)]
        exact hdig3 p hp1 hp2
      have hB5 : ∀ i : Nat, (i < fp.toNat - 48 ∨ fp.toNat + 176 ≤ i) →
          (i < out.toNat + (16 - 4 * k) ∨ out.toNat + 20 ≤ i) →
          st5.mem.bytes i = B i := fun i h1 h2 => by
        rw [hfr5 i (by omega), hfr4 i (by omega) (by have b := t80.out; omega),
            write32_bytes_of_disjoint _ _ _ _ (by have a := t20.out; omega)]
        exact hB3 i h1 (by omega)
      have p96 : ¬ (1114112 < fp.toNat + 96 + 8) := by omega
      have p104 : ¬ (1114112 < fp.toNat + 104 + 8) := by omega
      have hv24_96 : (st5.mem.write64 (fp + 96) 10000).read64 (fp + 24) =
          UInt64.ofNat (n.toNat / 10 ^ (4 * k)) := by
        rw [read64_write64_disjoint _ _ _ _
              (by have a := t96.out; have b := t24.out; omega), hv24_5]
      wp_run
      simp [hpg5, hv24_96, p96]
      rw [if_neg p24]
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      have hrem : UInt64.ofNat (n.toNat / 10 ^ (4 * k)) % 10000 =
          UInt64.ofNat (n.toNat / 10 ^ (4 * k) % 10000) := by
        apply UInt64.toNat.inj
        rw [UInt64.toNat_mod, hofm,
            UInt64.toNat_ofNat_of_lt'
              (by have hsz : UInt64.size = 18446744073709551616 := rfl; omega)]
        rfl
      have hv24_104 : ((st5.mem.write64 (fp + 96) 10000).write64 (fp + 104)
            (UInt64.ofNat (n.toNat / 10 ^ (4 * k) % 10000))).read64 (fp + 24) =
          UInt64.ofNat (n.toNat / 10 ^ (4 * k)) := by
        rw [read64_write64_disjoint _ _ _ _
              (by have a := t104.out; have b := t24.out; omega), hv24_96]
      have hdiv : UInt64.ofNat (n.toNat / 10 ^ (4 * k)) / 10000 =
          UInt64.ofNat (n.toNat / 10 ^ (4 * k) / 10000) := by
        apply UInt64.toNat.inj
        rw [UInt64.toNat_div, hofm,
            UInt64.toNat_ofNat_of_lt'
              (by have hsz : UInt64.size = 18446744073709551616 := rfl
                  have := Nat.div_le_self (n.toNat / 10 ^ (4 * k)) 10000
                  omega)]
        rfl
      have hwrap : UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 % 4294967296) =
          UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000) := by
        rw [Nat.mod_eq_of_lt (by omega)]
      wp_run
      simp [hpg5, hrem, hv24_104, hdiv, hwrap, p104, p24]
      apply wp_call_of_terminates (func38_spec env _ fp fp
        (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000))
        (by simp [hpg5]) (by simpa using hgl5) (by omega) (by omega) (by omega))
      rintro st6 vs6 ⟨hpg6, hgl6, hrs6, hq0, hq4, hfr6⟩
      obtain ⟨hglen6, -⟩ := List.getElem?_eq_some_iff.mp hgl6
      subst hrs6
      have hofc : (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000)).toNat =
          n.toNat / 10 ^ (4 * k) % 10000 :=
        UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
      have hq32 : (5243 * UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000)) >>> 19 =
          UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100) := by
        apply UInt32.toNat.inj
        rw [UInt32.mul_comm, magic_div100_u32 _ (by rw [hofc]; omega), hofc,
            UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
      have hofq : (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100)).toNat =
          n.toNat / 10 ^ (4 * k) % 10000 / 100 :=
        UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
      have hsub100 : UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000) -
          100 * UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100) =
          UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 % 100) := by
        apply UInt32.toNat.inj
        have hmul : ((100 : UInt32) *
            UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100)).toNat =
            100 * (n.toNat / 10 ^ (4 * k) % 10000 / 100) := by
          rw [UInt32.toNat_mul, hofq, show ((100 : UInt32)).toNat = 100 from rfl,
              Nat.mod_eq_of_lt (by omega)]
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hmul, hofc]; omega),
            hmul, hofc, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        omega
      rw [hq32] at hq0 hq4
      rw [hsub100] at hq4
      have hp20_6 : st6.mem.read32 (fp + 20) = UInt32.ofNat (16 - 4 * k) := by
        rw [read32_congr_bytes st6.mem _ _
              (fun i h1 h2 => hfr6 i (by have a := t20.out; omega)
                (by have a := t20.out; omega)),
            read32_write64_disjoint _ _ _ _
              (by have a := t24.out; have b := t20.out; omega),
            read32_write64_disjoint _ _ _ _
              (by have a := t104.out; have b := t20.out; omega),
            read32_write64_disjoint _ _ _ _
              (by have a := t96.out; have b := t20.out; omega),
            hp20_5]
      have hp20a : ((st6.mem.write32 (fp + 112)
            (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100))).write32
            (fp + 116) (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 100))).read32
            (fp + 20) = UInt32.ofNat (16 - 4 * k) := by
        rw [read32_write32_disjoint' _ _ _ _
              (by have a := t116.out; have b := t20.out; omega),
            read32_write32_disjoint' _ _ _ _
              (by have a := t112.out; have b := t20.out; omega),
            hp20_6]
      have p0 : ¬ (1114112 < fp.toNat + 0 + 4) := by omega
      have p4 : ¬ (1114112 < fp.toNat + 4 + 4) := by omega
      have p112 : ¬ (1114112 < fp.toNat + 112 + 4) := by omega
      have p116 : ¬ (1114112 < fp.toNat + 116 + 4) := by omega
      have hlt9 : UInt32.ofNat (16 - 4 * k) < 20 := by
        rw [UInt32.lt_iff_toNat_lt, hof16]
        simp
        omega
      wp_run
      have hshl_q : UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100) <<< (1 : UInt32) =
          UInt32.ofNat (2 * (n.toNat / 10 ^ (4 * k) % 10000 / 100)) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_shiftLeft, hofq,
            UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp [Nat.shiftLeft_eq]
        omega
      simp [hpg6, hq0, hq4, hp20a, p0, p4, p112, p116, hlt9, p20]
      apply wp_call_of_terminates (func39_spec env _ fp 1049408 200
        (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100) <<< 1) 1049348
        (by simp [hpg6]) (by simpa using hgl6) (by omega) (by omega))
      rintro st7 vs7 ⟨hpg7, hgl7, hrs7, hfr7⟩
      obtain ⟨hglen7, -⟩ := List.getElem?_eq_some_iff.mp hgl7
      subst hrs7
      have hB6 : ∀ i : Nat, (i < fp.toNat - 48 ∨ fp.toNat + 176 ≤ i) →
          (i < out.toNat + (16 - 4 * k) ∨ out.toNat + 20 ≤ i) →
          st6.mem.bytes i = B i := fun i h1 h2 => by
        rw [hfr6 i (by omega) (by omega),
            write64_bytes_of_disjoint _ _ _ _ (by have a := t24.out; omega),
            write64_bytes_of_disjoint _ _ _ _ (by have a := t104.out; omega),
            write64_bytes_of_disjoint _ _ _ _ (by have a := t96.out; omega)]
        exact hB5 i h1 h2
      have hB7 : ∀ i : Nat, (i < fp.toNat - 48 ∨ fp.toNat + 176 ≤ i) →
          (i < out.toNat + (16 - 4 * k) ∨ out.toNat + 20 ≤ i) →
          st7.mem.bytes i = B i := fun i h1 h2 => by
        rw [hfr7 i (by omega),
            write32_bytes_of_disjoint _ _ _ _ (by have a := t116.out; omega),
            write32_bytes_of_disjoint _ _ _ _ (by have a := t112.out; omega)]
        exact hB6 i h1 h2
      have haddr1 : Frozen ((UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100) <<< 1 +
          1049408).toNat = 1049408 + 2 * (n.toNat / 10 ^ (4 * k) % 10000 / 100)) :=
        Frozen.mk (by
          rw [hshl_q,
              toNat_add_of_lt _ _ (by
                rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
                simp
                omega),
              UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
          simp
          omega)
      have hbyte1 : st7.mem.read8
          (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100) <<< 1 + 1049408) =
          UInt8.ofNat (48 + n.toNat / 10 ^ (4 * k) % 10000 / 1000) := by
        show st7.mem.bytes _ = _
        rw [haddr1.out, hB7 _ (by omega) (by omega), htab _ (by omega)]
        have h := digit_pair_table_high_tens_byte_lt10000
          (n.toNat / 10 ^ (4 * k) % 10000) (by omega)
        simpa [digitTableBase] using h
      have ptab1 : ¬ (1114112 <
          (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100) <<< 1 + 1049408).toNat
            + 0 + 1) := by
        have a := haddr1.out
        omega
      have haddr10 : Frozen ((UInt32.ofNat (16 - 4 * k) + out).toNat =
          out.toNat + (16 - 4 * k)) :=
        Frozen.mk (by rw [toNat_add_of_lt _ _ (by rw [hof16]; omega), hof16]; omega)
      have pout1 : ¬ (1114112 < (UInt32.ofNat (16 - 4 * k) + out).toNat + 0 + 1) := by
        have a := haddr10.out
        omega
      have p144 : ¬ (1114112 < fp.toNat + 144 + 4) := by omega
      have p151 : ¬ (1114112 < fp.toNat + 151 + 1) := by omega
      have hguard_tab1 : ¬ (1114112 ≤
          ((n.toNat / 10 ^ (4 * k) % 10000 / 100 % 4294967296) <<< 1 + 1049408) %
            4294967296) := by
        have e1 : n.toNat / 10 ^ (4 * k) % 10000 / 100 % 4294967296 =
            n.toNat / 10 ^ (4 * k) % 10000 / 100 := Nat.mod_eq_of_lt (by omega)
        rw [e1, Nat.shiftLeft_eq]
        omega
      have hguard_out1 : ¬ (1114112 ≤ (16 - 4 * k + out.toNat) % 4294967296) := by
        omega
      have hp20b : (((st7.mem.write32 (fp + 144)
            (UInt32.ofNat (16 - 4 * k) + out)).write8 (fp + 151)
            ((48 + (UInt8.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 1000)).toUInt32) %
              256).toUInt8).write8 (UInt32.ofNat (16 - 4 * k) + out)
            ((48 + (UInt8.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 1000)).toUInt32) %
              256).toUInt8).read32 (fp + 20) = UInt32.ofNat (16 - 4 * k) := by
        rw [read32_write8_disjoint _ _ _ _
              (by have a := haddr10.out; have b := t20.out; omega),
            read32_write8_disjoint _ _ _ _
              (by have a := t151.out; have b := t20.out; omega),
            read32_write32_disjoint' _ _ _ _
              (by have a := t144.out; have b := t20.out; omega),
            read32_congr_bytes st7.mem _ _
              (fun i h1 h2 => hfr7 i (by have a := t20.out; omega)),
            read32_write32_disjoint' _ _ _ _
              (by have a := t116.out; have b := t20.out; omega),
            read32_write32_disjoint' _ _ _ _
              (by have a := t112.out; have b := t20.out; omega),
            hp20_6]
      have h17 : (1 : UInt32) + UInt32.ofNat (16 - 4 * k) = UInt32.ofNat (17 - 4 * k) := by
        apply UInt32.toNat.inj
        rw [toNat_add_of_lt _ _ (by simp [hof16]; omega), hof16,
            UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp
        omega
      have hof17 : (UInt32.ofNat (17 - 4 * k)).toNat = 17 - 4 * k :=
        UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
      have hlt13 : UInt32.ofNat (17 - 4 * k) < 20 := by
        rw [UInt32.lt_iff_toNat_lt, hof17]
        simp
        omega
      wp_run
      simp [hpg7, hbyte1, p144, p151, hguard_tab1, hguard_out1, p20, hp20b, h17, hlt13]
      apply wp_call_of_terminates (func39_spec env _ fp 1049408 200
        ((1 : UInt32) + UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100) <<< 1) 1049348
        (by simp [hpg7]) (by simpa using hgl7) (by omega) (by omega))
      rintro st8 vs8 ⟨hpg8, hgl8, hrs8, hfr8⟩
      obtain ⟨hglen8, -⟩ := List.getElem?_eq_some_iff.mp hgl8
      subst hrs8
      have hone : (1 : UInt32) + UInt32.ofNat (2 * (n.toNat / 10 ^ (4 * k) % 10000 / 100)) =
          UInt32.ofNat (2 * (n.toNat / 10 ^ (4 * k) % 10000 / 100) + 1) := by
        apply UInt32.toNat.inj
        rw [toNat_add_of_lt _ _ (by
              rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
              simp
              omega),
            UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega),
            UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp
        omega
      have haddr2 : Frozen ((((1 : UInt32) + UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100) <<< 1) +
          1049408).toNat = 1049408 + (2 * (n.toNat / 10 ^ (4 * k) % 10000 / 100) + 1)) :=
        Frozen.mk (by
          rw [hshl_q, hone,
              toNat_add_of_lt _ _ (by
                rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
                simp
                omega),
              UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
          simp
          omega)
      have hB8 : ∀ i : Nat, (i < fp.toNat - 48 ∨ fp.toNat + 176 ≤ i) →
          (i < out.toNat + (16 - 4 * k) ∨ out.toNat + 20 ≤ i) →
          st8.mem.bytes i = B i := fun i h1 h2 => by
        rw [hfr8 i (by omega),
            write8_bytes_of_disjoint _ _ _ _ (by have a := haddr10.out; omega),
            write8_bytes_of_disjoint _ _ _ _ (by have a := t151.out; omega),
            write32_bytes_of_disjoint _ _ _ _ (by have a := t144.out; omega)]
        exact hB7 i h1 h2
      have hbyte2 : st8.mem.read8
          (((1 : UInt32) + UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100) <<< 1) + 1049408) =
          UInt8.ofNat (48 + n.toNat / 10 ^ (4 * k) % 10000 / 100 % 10) := by
        show st8.mem.bytes _ = _
        rw [haddr2.out, hB8 _ (by omega) (by omega), htab _ (by omega)]
        have h := digit_pair_table_high_ones_byte_lt10000
          (n.toNat / 10 ^ (4 * k) % 10000) (by omega)
        simpa [digitTableBase, Nat.add_assoc] using h
      have hguard_tab2 : ¬ (1114112 ≤
          (1 + (n.toNat / 10 ^ (4 * k) % 10000 / 100 % 4294967296) <<< 1 + 1049408) %
            4294967296) := by
        have e1 : n.toNat / 10 ^ (4 * k) % 10000 / 100 % 4294967296 =
            n.toNat / 10 ^ (4 * k) % 10000 / 100 := Nat.mod_eq_of_lt (by omega)
        rw [e1, Nat.shiftLeft_eq]
        omega
      have hguard_out2 : ¬ (1114112 ≤ (17 - 4 * k + out.toNat) % 4294967296) := by
        omega
      have haddr14 : Frozen ((UInt32.ofNat (17 - 4 * k) + out).toNat =
          out.toNat + (17 - 4 * k)) :=
        Frozen.mk (by rw [toNat_add_of_lt _ _ (by rw [hof17]; omega), hof17]; omega)
      have p136 : ¬ (1114112 < fp.toNat + 136 + 4) := by omega
      have p143 : ¬ (1114112 < fp.toNat + 143 + 1) := by omega
      have hp20_8 : st8.mem.read32 (fp + 20) = UInt32.ofNat (16 - 4 * k) := by
        rw [read32_congr_bytes st8.mem _ _
              (fun i h1 h2 => hfr8 i (by have a := t20.out; omega))]
        exact hp20b
      have hp20c : (((st8.mem.write32 (fp + 136)
            (UInt32.ofNat (17 - 4 * k) + out)).write8 (fp + 143)
            ((48 + (UInt8.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100 % 10)).toUInt32) %
              256).toUInt8).write8 (UInt32.ofNat (17 - 4 * k) + out)
            ((48 + (UInt8.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 100 % 10)).toUInt32) %
              256).toUInt8).read32 (fp + 20) = UInt32.ofNat (16 - 4 * k) := by
        rw [read32_write8_disjoint _ _ _ _
              (by have a := haddr14.out; have b := t20.out; omega),
            read32_write8_disjoint _ _ _ _
              (by have a := t143.out; have b := t20.out; omega),
            read32_write32_disjoint' _ _ _ _
              (by have a := t136.out; have b := t20.out; omega),
            hp20_8]
      have h18 : (2 : UInt32) + UInt32.ofNat (16 - 4 * k) = UInt32.ofNat (18 - 4 * k) := by
        apply UInt32.toNat.inj
        rw [toNat_add_of_lt _ _ (by simp [hof16]; omega), hof16,
            UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp
        omega
      have hof18 : (UInt32.ofNat (18 - 4 * k)).toNat = 18 - 4 * k :=
        UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
      have hlt17 : UInt32.ofNat (18 - 4 * k) < 20 := by
        rw [UInt32.lt_iff_toNat_lt, hof18]
        simp
        omega
      wp_run
      simp [hpg8, hbyte2, p136, p143, hguard_tab2, hguard_out2, p20, hp20c, h18, hlt17]
      -- digit 3: `DIGIT_TABLE[2 * (c % 100)]` at `out + (18 - 4k)`
      apply wp_call_of_terminates (func39_spec env _ fp 1049408 200
        (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 100) <<< 1) 1049348
        (by simp [hpg8]) (by simpa using hgl8) (by omega) (by omega))
      rintro st9 vs9 ⟨hpg9, hgl9, hrs9, hfr9⟩
      obtain ⟨hglen9, -⟩ := List.getElem?_eq_some_iff.mp hgl9
      subst hrs9
      have hofr : (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 100)).toNat =
          n.toNat / 10 ^ (4 * k) % 100 :=
        UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
      have hshl_r : UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 100) <<< (1 : UInt32) =
          UInt32.ofNat (2 * (n.toNat / 10 ^ (4 * k) % 100)) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_shiftLeft, hofr,
            UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp [Nat.shiftLeft_eq]
        omega
      have haddr3 : Frozen ((UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 100) <<< 1 +
          1049408).toNat = 1049408 + 2 * (n.toNat / 10 ^ (4 * k) % 100)) :=
        Frozen.mk (by
          rw [hshl_r,
              toNat_add_of_lt _ _ (by
                rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
                simp
                omega),
              UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
          simp
          omega)
      have hB9 : ∀ i : Nat, (i < fp.toNat - 48 ∨ fp.toNat + 176 ≤ i) →
          (i < out.toNat + (16 - 4 * k) ∨ out.toNat + 20 ≤ i) →
          st9.mem.bytes i = B i := fun i h1 h2 => by
        rw [hfr9 i (by omega),
            write8_bytes_of_disjoint _ _ _ _ (by have a := haddr14.out; omega),
            write8_bytes_of_disjoint _ _ _ _ (by have a := t143.out; omega),
            write32_bytes_of_disjoint _ _ _ _ (by have a := t136.out; omega)]
        exact hB8 i h1 h2
      have hbyte3 : st9.mem.read8
          (UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 100) <<< 1 + 1049408) =
          UInt8.ofNat (48 + n.toNat / 10 ^ (4 * k) % 10000 / 10 % 10) := by
        show st9.mem.bytes _ = _
        rw [haddr3.out, hB9 _ (by omega) (by omega), htab _ (by omega)]
        have h := digit_pair_table_low_tens_byte_lt10000
          (n.toNat / 10 ^ (4 * k) % 10000) (by omega)
        rw [show n.toNat / 10 ^ (4 * k) % 10000 % 100 = n.toNat / 10 ^ (4 * k) % 100
              from by omega] at h
        simpa [digitTableBase] using h
      have hguard_tab3 : ¬ (1114112 ≤
          ((n.toNat / 10 ^ (4 * k) % 100 % 4294967296) <<< 1 + 1049408) %
            4294967296) := by
        have e1 : n.toNat / 10 ^ (4 * k) % 100 % 4294967296 =
            n.toNat / 10 ^ (4 * k) % 100 := Nat.mod_eq_of_lt (by omega)
        rw [e1, Nat.shiftLeft_eq]
        omega
      have hguard_out3 : ¬ (1114112 ≤ (18 - 4 * k + out.toNat) % 4294967296) := by
        omega
      have haddr18 : Frozen ((UInt32.ofNat (18 - 4 * k) + out).toNat =
          out.toNat + (18 - 4 * k)) :=
        Frozen.mk (by rw [toNat_add_of_lt _ _ (by rw [hof18]; omega), hof18]; omega)
      have p128 : ¬ (1114112 < fp.toNat + 128 + 4) := by omega
      have p135 : ¬ (1114112 < fp.toNat + 135 + 1) := by omega
      have hp20_9 : st9.mem.read32 (fp + 20) = UInt32.ofNat (16 - 4 * k) := by
        rw [read32_congr_bytes st9.mem _ _
              (fun i h1 h2 => hfr9 i (by have a := t20.out; omega))]
        exact hp20c
      have hp20d : (((st9.mem.write32 (fp + 128)
            (UInt32.ofNat (18 - 4 * k) + out)).write8 (fp + 135)
            ((48 + (UInt8.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 10 % 10)).toUInt32) %
              256).toUInt8).write8 (UInt32.ofNat (18 - 4 * k) + out)
            ((48 + (UInt8.ofNat (n.toNat / 10 ^ (4 * k) % 10000 / 10 % 10)).toUInt32) %
              256).toUInt8).read32 (fp + 20) = UInt32.ofNat (16 - 4 * k) := by
        rw [read32_write8_disjoint _ _ _ _
              (by have a := haddr18.out; have b := t20.out; omega),
            read32_write8_disjoint _ _ _ _
              (by have a := t135.out; have b := t20.out; omega),
            read32_write32_disjoint' _ _ _ _
              (by have a := t128.out; have b := t20.out; omega),
            hp20_9]
      have h19 : (3 : UInt32) + UInt32.ofNat (16 - 4 * k) = UInt32.ofNat (19 - 4 * k) := by
        apply UInt32.toNat.inj
        rw [toNat_add_of_lt _ _ (by simp [hof16]; omega), hof16,
            UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp
        omega
      have hof19 : (UInt32.ofNat (19 - 4 * k)).toNat = 19 - 4 * k :=
        UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
      have hlt21 : UInt32.ofNat (19 - 4 * k) < 20 := by
        rw [UInt32.lt_iff_toNat_lt, hof19]
        simp
        omega
      wp_run
      simp [hpg9, hbyte3, p128, p135, hguard_tab3, hguard_out3, p20, hp20d, h19, hlt21]
      -- digit 4: `DIGIT_TABLE[2 * (c % 100) + 1]` at `out + (19 - 4k)`
      apply wp_call_of_terminates (func39_spec env _ fp 1049408 200
        ((1 : UInt32) + UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 100) <<< 1) 1049348
        (by simp [hpg9]) (by simpa using hgl9) (by omega) (by omega))
      rintro st10 vs10 ⟨hpg10, hgl10, hrs10, hfr10⟩
      obtain ⟨hglen10, -⟩ := List.getElem?_eq_some_iff.mp hgl10
      subst hrs10
      have hone3 : (1 : UInt32) + UInt32.ofNat (2 * (n.toNat / 10 ^ (4 * k) % 100)) =
          UInt32.ofNat (2 * (n.toNat / 10 ^ (4 * k) % 100) + 1) := by
        apply UInt32.toNat.inj
        rw [toNat_add_of_lt _ _ (by
              rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
              simp
              omega),
            UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega),
            UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp
        omega
      have haddr4 : Frozen ((((1 : UInt32) +
          UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 100) <<< 1) + 1049408).toNat =
          1049408 + (2 * (n.toNat / 10 ^ (4 * k) % 100) + 1)) :=
        Frozen.mk (by
          rw [hshl_r, hone3,
              toNat_add_of_lt _ _ (by
                rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
                simp
                omega),
              UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
          simp
          omega)
      have hB10 : ∀ i : Nat, (i < fp.toNat - 48 ∨ fp.toNat + 176 ≤ i) →
          (i < out.toNat + (16 - 4 * k) ∨ out.toNat + 20 ≤ i) →
          st10.mem.bytes i = B i := fun i h1 h2 => by
        rw [hfr10 i (by omega),
            write8_bytes_of_disjoint _ _ _ _ (by have a := haddr18.out; omega),
            write8_bytes_of_disjoint _ _ _ _ (by have a := t135.out; omega),
            write32_bytes_of_disjoint _ _ _ _ (by have a := t128.out; omega)]
        exact hB9 i h1 h2
      have hbyte4 : st10.mem.read8
          (((1 : UInt32) + UInt32.ofNat (n.toNat / 10 ^ (4 * k) % 100) <<< 1) + 1049408) =
          UInt8.ofNat (48 + n.toNat / 10 ^ (4 * k) % 10) := by
        show st10.mem.bytes _ = _
        rw [haddr4.out, hB10 _ (by omega) (by omega), htab _ (by omega)]
        have h := digit_pair_table_low_ones_byte_lt10000
          (n.toNat / 10 ^ (4 * k) % 10000) (by omega)
        rw [show n.toNat / 10 ^ (4 * k) % 10000 % 100 = n.toNat / 10 ^ (4 * k) % 100
              from by omega,
            show n.toNat / 10 ^ (4 * k) % 10000 % 10 = n.toNat / 10 ^ (4 * k) % 10
              from by omega] at h
        simpa [digitTableBase, Nat.add_assoc] using h
      have hguard_tab4 : ¬ (1114112 ≤
          (1 + (n.toNat / 10 ^ (4 * k) % 100 % 4294967296) <<< 1 + 1049408) %
            4294967296) := by
        have e1 : n.toNat / 10 ^ (4 * k) % 100 % 4294967296 =
            n.toNat / 10 ^ (4 * k) % 100 := Nat.mod_eq_of_lt (by omega)
        rw [e1, Nat.shiftLeft_eq]
        omega
      have hguard_out4 : ¬ (1114112 ≤ (19 - 4 * k + out.toNat) % 4294967296) := by
        omega
      have haddr22 : Frozen ((UInt32.ofNat (19 - 4 * k) + out).toNat =
          out.toNat + (19 - 4 * k)) :=
        Frozen.mk (by rw [toNat_add_of_lt _ _ (by rw [hof19]; omega), hof19]; omega)
      have p120 : ¬ (1114112 < fp.toNat + 120 + 4) := by omega
      have p127 : ¬ (1114112 < fp.toNat + 127 + 1) := by omega
      wp_run
      simp [hpg10, hbyte4, p120, p127, hguard_tab4, hguard_out4]
      sorry
    · -- `v ≤ 999`: exit the loop
      simp [hgtiff, hgt]
      exact hexit st3 k _ w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
        w19 w20 w21 w22 w23 w24 (by simpa using hpg3) (by simpa using hgl3)
        (by omega) hk0 hv24' hp20' hdig3 hB3

end Project.Itoa.Proofs
