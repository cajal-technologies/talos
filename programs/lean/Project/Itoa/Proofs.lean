import Project.Itoa.Spec

/-!
# Proof of `CheckI64Spec` / `CheckU64Spec`

The exported `check_*(n, cap)` runs the `itoa`-crate formatter and a
naive `% 10` oracle into two on-stack buffers and traps via `unreachable`
iff they disagree. No-trap is therefore the equivalence of the two
formatters; both compute the decimal representation of `n`.

Unoptimized (`opt-level=0`) pipeline: the export chains are
`check_i64 = func31 → func28 → func23` (harness) and
`check_u64 = func32 → func29 → func21`. Inside a harness, the fast
formatter is `func24`/`func22` (wrapping the `itoa` core) and the naive
oracle is `func3 → func4` (i64) / `func5 → func6` (u64); `func7` clamps
the capacity and a byte-compare loop traps on any disagreement.

This file is built bottom-up:

1. `wp_call_of_terminates` — step a `.call id` from a `TerminatesWith`
   proof of the callee *at the concrete current store*. (`FuncSpec`
   quantifies over all stores and so is unusable for callees that can
   trap on a small/garbage memory; the harness only ever runs from
   `«module».initialStore`.)
2. `decimalDigits` — the shared decimal-string reference both formatters
   are proven to produce, plus the byte-level framing, `DIGIT_TABLE`,
   and magic-division lemma layers (all carried over from the
   pre-migration proof; only the table base moved, to `1049400`).
3. export-wrapper bridges (`func31`/`func32` and `func28`/`func29`)
   peeling the shadow-stack hops, and the conditional top-level
   theorems reducing `CheckI64Spec` / `CheckU64Spec` to `HarnessSpec
   23` / `HarnessSpec 21`.

The pre-migration proofs of the *old* register-allocated function
bodies (naive formatters `func0`/`func1`, fast-formatter base cases
`func13`, slice packaging `func14`, checked memcpy `func56`) do not
transfer: under `opt-level=0` those functions were regenerated as
memory-routed code with new indices. The naive u64 core `func6` is
re-proven below (`func6_spec`, pinned to its top-level call site), with
its two memory-routed loops factored into standalone `wp` lemmas over
an abstract continuation so the per-iteration proofs stay small.
Re-proving the naive i64 core (`func4`) and the fast-formatter core
(`func40` and its helpers) — and then discharging the `HarnessSpec`
hypotheses — is the remaining open work.
-/

namespace Project.Itoa.Proofs

open Wasm

/-- Step a `.call id` whose callee is described by `TerminatesWith` at the
*concrete* current store `st` (with the current operand stack as args).
Structural analogue of `wp_call_cons` that sources the run from
`TerminatesWith` rather than a (∀-store) `FuncSpec`. -/
theorem wp_call_of_terminates {α : Type} {env : HostEnv α} {m : Module}
    {st : Store α} {s : Locals} {Q : Assertion α} {id : Nat} {rest : Program}
    {P : Store α → List Value → Prop}
    (hterm : TerminatesWith env m id st s.values P)
    (hPost : ∀ st' vs, P st' vs → wp m rest Q st' { s with values := vs } env) :
    wp m (.call id :: rest) Q st s env := by
  unfold wp
  unfold TerminatesWith at hterm
  obtain ⟨Ns, hNs⟩ := hterm
  obtain ⟨vs, st', hRun, hPost_vs⟩ := hNs Ns le_rfl
  have hRun_ne : run Ns m id st s.values env ≠ .OutOfFuel := by
    rw [hRun]; intro h; cases h
  have hwp_rest := hPost st' vs hPost_vs
  unfold wp at hwp_rest
  obtain ⟨Nr, hNr⟩ := hwp_rest
  refine ⟨max (Ns + 1) (Nr + 1), fun fuel hfuel => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hRun_f : run f m id st s.values env = .Success vs st' := by
    rw [run_fuel_mono (by omega : f ≥ Ns) hRun_ne]; exact hRun
  rw [exec_call_cons, hRun_f]
  exact hNr (f + 1) (by omega)

/-! ## The decimal-string reference

Both formatters are proven to write `decimalDigits n.toNat`: the most-
significant-first list of ASCII decimal bytes, with no leading zeros
(and `"0"` for zero). Equivalence of the two formatters then follows by
transitivity, so the byte-compare loop in the harness never traps. -/

/-- The decimal ASCII representation of `n`, most-significant digit first.
`decimalDigits 0 = ['0']`; otherwise no leading zeros. -/
def decimalDigits (n : Nat) : List UInt8 :=
  if n < 10 then [UInt8.ofNat (48 + n)]
  else decimalDigits (n / 10) ++ [UInt8.ofNat (48 + n % 10)]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

@[simp] theorem decimalDigits_lt_ten {n : Nat} (h : n < 10) :
    decimalDigits n = [UInt8.ofNat (48 + n)] := by
  rw [decimalDigits]; simp [h]

theorem decimalDigits_ge_ten {n : Nat} (h : 10 ≤ n) :
    decimalDigits n = decimalDigits (n / 10) ++ [UInt8.ofNat (48 + n % 10)] := by
  rw [decimalDigits]; simp [Nat.not_lt.mpr h]

/-- `decimalDigits` is never empty. -/
theorem decimalDigits_ne_nil (n : Nat) : decimalDigits n ≠ [] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 10 with h | h
    · simp [decimalDigits_lt_ten h]
    · simp [decimalDigits_ge_ten h]

/-- Number of decimal digits of `n` (= length of its decimal string). -/
def numDigits (n : Nat) : Nat := (decimalDigits n).length

theorem numDigits_pos (n : Nat) : 0 < numDigits n :=
  List.length_pos_of_ne_nil (decimalDigits_ne_nil n)

@[simp] theorem numDigits_lt_ten {n : Nat} (h : n < 10) : numDigits n = 1 := by
  simp [numDigits, decimalDigits_lt_ten h]

theorem numDigits_ge_ten {n : Nat} (h : 10 ≤ n) :
    numDigits n = numDigits (n / 10) + 1 := by
  simp [numDigits, decimalDigits_ge_ten h]

theorem length_decimalDigits (n : Nat) : (decimalDigits n).length = numDigits n := rfl

/-- `n` has fewer than `10 ^ numDigits n` — i.e. dividing by `10^L` zeroes it. -/
theorem lt_ten_pow_numDigits (n : Nat) : n < 10 ^ numDigits n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 10 with h | h
    · rw [numDigits_lt_ten h, pow_one]; exact h
    · rw [numDigits_ge_ten h, pow_succ]
      have hd : n / 10 < 10 ^ numDigits (n / 10) :=
        ih (n / 10) (Nat.div_lt_self (by omega) (by omega))
      have h2 : 10 * (n / 10 + 1) ≤ 10 * 10 ^ numDigits (n / 10) :=
        Nat.mul_le_mul_left 10 (by omega)
      omega

/-- Lower companion of `lt_ten_pow_numDigits`: `10^(numDigits m - 1) ≤ m` for `m ≥ 1`. -/
theorem ten_pow_numDigits_le (m : Nat) (hm : 1 ≤ m) : 10 ^ (numDigits m - 1) ≤ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 10 with h | h
    · rw [numDigits_lt_ten h]; simpa using hm
    · rw [numDigits_ge_ten h]
      have hd1 : 1 ≤ m / 10 := by omega
      have ihm := ih (m / 10) (Nat.div_lt_self (by omega) (by omega)) hd1
      have hpos : 1 ≤ numDigits (m / 10) := numDigits_pos _
      rw [show numDigits (m / 10) + 1 - 1 = (numDigits (m / 10) - 1) + 1 from by omega, pow_succ]
      have : 10 ^ (numDigits (m / 10) - 1) * 10 ≤ (m / 10) * 10 := Nat.mul_le_mul_right 10 ihm
      omega

/-- `numDigits` of a `u64` value is at most 20. -/
theorem numDigits_toNat_le (n : UInt64) : numDigits n.toNat ≤ 20 := by
  rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
  · rw [h0]; rw [numDigits_lt_ten (by norm_num : (0:Nat) < 10)]; norm_num
  · have hle : 10 ^ (numDigits n.toNat - 1) ≤ n.toNat := ten_pow_numDigits_le n.toNat h0
    have hn : n.toNat < 18446744073709551616 := by
      have := UInt64.toNat_lt n; simpa [UInt64.size] using this
    by_contra hbig
    have h20 : (10:Nat) ^ 20 ≤ 10 ^ (numDigits n.toNat - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have he : (10:Nat) ^ 20 = 100000000000000000000 := by norm_num
    omega

/-- The `j`-th decimal byte (MSB-first) of `n` is `'0' + (n / 10^(L-1-j)) % 10`,
where `L = numDigits n`. This is the per-position characterization the write
loops are matched against. -/
theorem decimalDigits_getElem? (n j : Nat) (hj : j < numDigits n) :
    (decimalDigits n)[j]? = some (UInt8.ofNat (48 + n / 10 ^ (numDigits n - 1 - j) % 10)) := by
  induction n using Nat.strong_induction_on generalizing j with
  | _ n ih =>
    rcases Nat.lt_or_ge n 10 with h | h
    · -- n < 10: single digit
      have hj0 : j = 0 := by
        have := hj; rw [numDigits_lt_ten h] at this; omega
      subst hj0
      simp [decimalDigits_lt_ten h, numDigits_lt_ten h, Nat.mod_eq_of_lt h]
    · -- n ≥ 10
      have hL : numDigits n = numDigits (n / 10) + 1 := numDigits_ge_ten h
      have hlen : (decimalDigits (n / 10)).length = numDigits (n / 10) := rfl
      have hdiv : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      rw [decimalDigits_ge_ten h]
      rcases Nat.lt_or_ge j (numDigits (n / 10)) with hjl | hjr
      · -- left part: recurse
        rw [List.getElem?_append_left (by rw [hlen]; exact hjl)]
        rw [ih (n / 10) hdiv j hjl]
        congr 2
        -- 48 + (n/10) / 10^(numDigits (n/10) - 1 - j) % 10
        --   = 48 + n / 10^(numDigits n - 1 - j) % 10
        have he : numDigits n - 1 - j = (numDigits (n / 10) - 1 - j) + 1 := by omega
        rw [he, pow_succ, Nat.div_div_eq_div_mul]
        ring_nf
      · -- right part: j = numDigits (n/10), the trailing digit
        have hjeq : j = numDigits (n / 10) := by omega
        subst hjeq
        rw [List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
        have : numDigits n - 1 - numDigits (n / 10) = 0 := by omega
        simp [this]

theorem numDigits_eq_four_of_lt10000_ge1000 (n : Nat) (hlo : 1000 ≤ n) (hhi : n < 10000) :
    numDigits n = 4 := by
  rw [numDigits_ge_ten (by omega : 10 ≤ n)]
  rw [numDigits_ge_ten (by omega : 10 ≤ n / 10)]
  rw [numDigits_ge_ten (by omega : 10 ≤ n / 10 / 10)]
  rw [numDigits_lt_ten (by omega : n / 10 / 10 / 10 < 10)]

/-! ## Naive formatter (`func1`, u64)

`func1(n, outPtr, outLen, cap)` writes `decimalDigits n` into
`[outPtr, outPtr + len)` and returns `len = numDigits n` when `len ≤ cap`;
otherwise returns `-1` and writes nothing. No-trap requires the digit
region to be in-bounds and `len ≤ outLen`. -/

/-! ### Signedness bridge (`i32` signed compares ↔ `toNat`, for small values) -/

/-- For `c` below `2^31`, the signed reinterpretation agrees with `toNat`. -/
theorem toInt32_toInt_small (c : UInt32) (h : c.toNat < 2147483648) :
    c.toInt32.toInt = (c.toNat : Int) := by
  rw [show c.toInt32.toInt = c.toBitVec.toInt from rfl, BitVec.toInt_eq_toNat_bmod,
    show c.toBitVec.toNat = c.toNat from rfl, Int.bmod]
  simp; omega

theorem ltS_small (a b : UInt32) (ha : a.toNat < 2147483648) (hb : b.toNat < 2147483648) :
    (a.toInt32 < b.toInt32) ↔ a.toNat < b.toNat := by
  rw [Int32.lt_iff_toInt_lt, toInt32_toInt_small a ha, toInt32_toInt_small b hb]; omega

theorem leS_small (a b : UInt32) (ha : a.toNat < 2147483648) (hb : b.toNat < 2147483648) :
    (a.toInt32 ≤ b.toInt32) ↔ a.toNat ≤ b.toNat := by
  rw [Int32.le_iff_toInt_le, toInt32_toInt_small a ha, toInt32_toInt_small b hb]; omega

set_option maxRecDepth 10000 in
/-- `n` (as i64) is non-negative iff its `toNat` is below `2^63`. -/
theorem i64_sign_bridge (n : UInt64) :
    (18446744073709551615 < n.toInt64) ↔ (n.toNat < 9223372036854775808) := by
  rw [Int64.lt_iff_toInt_lt, show (18446744073709551615 : Int64).toInt = -1 from by decide,
    show n.toInt64.toInt = n.toInt64.toBitVec.toInt from rfl, BitVec.toInt_eq_toNat_bmod,
    show n.toInt64.toBitVec.toNat = n.toNat from rfl, Int.bmod]
  have hb : n.toNat < 18446744073709551616 := by
    have := UInt64.toNat_lt n; simpa [UInt64.size] using this
  norm_num; omega

/-! ### Byte-level memory framing (reusable for every write loop) -/

@[simp] theorem read8_write8_bytes (m : Mem) (a : UInt32) (v : UInt8) (i : Nat) :
    (m.write8 a v).bytes i = if i = a.toNat then v else m.bytes i := rfl

@[simp] theorem write8_pages (m : Mem) (a : UInt32) (v : UInt8) :
    (m.write8 a v).pages = m.pages := rfl

@[simp] theorem read16_write16_bytes (m : Mem) (a : UInt32) (v : UInt32) (i : Nat) :
    (m.write16 a v).bytes i =
      if i = a.toNat then (v &&& 0xFF).toUInt8
      else if i = a.toNat + 1 then ((v >>> 8) &&& 0xFF).toUInt8
      else m.bytes i := rfl

@[simp] theorem write16_pages (m : Mem) (a : UInt32) (v : UInt32) :
    (m.write16 a v).pages = m.pages := rfl

@[simp] theorem read32_write32_bytes (m : Mem) (a : UInt32) (v : UInt32) (i : Nat) :
    (m.write32 a v).bytes i =
      if i = a.toNat then (v &&& 0xFF).toUInt8
      else if i = a.toNat + 1 then ((v >>> 8) &&& 0xFF).toUInt8
      else if i = a.toNat + 2 then ((v >>> 16) &&& 0xFF).toUInt8
      else if i = a.toNat + 3 then ((v >>> 24) &&& 0xFF).toUInt8
      else m.bytes i := rfl

@[simp] theorem write32_pages (m : Mem) (a : UInt32) (v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

theorem read8_write8_same (m : Mem) (a : UInt32) (v : UInt8) :
    (m.write8 a v).bytes a.toNat = v := by simp

theorem read8_write8_disjoint (m : Mem) (a : UInt32) (v : UInt8) (i : Nat)
    (h : i ≠ a.toNat) : (m.write8 a v).bytes i = m.bytes i := by simp [h]

theorem read16_write16_low (m : Mem) (a : UInt32) (v : UInt32) :
    (m.write16 a v).bytes a.toNat = (v &&& 0xFF).toUInt8 := by
  simp

theorem read16_write16_high (m : Mem) (a : UInt32) (v : UInt32) :
    (m.write16 a v).bytes (a.toNat + 1) = ((v >>> 8) &&& 0xFF).toUInt8 := by
  rw [read16_write16_bytes]
  rw [if_neg (by omega : a.toNat + 1 ≠ a.toNat), if_pos rfl]

theorem read16_write16_disjoint (m : Mem) (a : UInt32) (v : UInt32) (i : Nat)
    (h0 : i ≠ a.toNat) (h1 : i ≠ a.toNat + 1) :
    (m.write16 a v).bytes i = m.bytes i := by
  simp [h0, h1]

theorem read16_write16_disjoint_addr (m : Mem) (writeAddr : UInt32) (v : UInt32)
    (readAddr : UInt32)
    (h00 : readAddr.toNat ≠ writeAddr.toNat)
    (h01 : readAddr.toNat ≠ writeAddr.toNat + 1)
    (h10 : readAddr.toNat + 1 ≠ writeAddr.toNat)
    (h11 : readAddr.toNat + 1 ≠ writeAddr.toNat + 1) :
    (m.write16 writeAddr v).read16 readAddr = m.read16 readAddr := by
  unfold Mem.read16
  rw [read16_write16_disjoint m writeAddr v readAddr.toNat h00 h01]
  rw [read16_write16_disjoint m writeAddr v (readAddr.toNat + 1) h10 h11]

theorem outPtr_add_ne (outPtr : UInt32) {i j : Nat} (hi : i < 20) (hj : j < 20) (hne : i ≠ j) :
    (outPtr.toNat + i) % 4294967296 ≠ (j + outPtr.toNat) % 4294967296 := by
  intro h
  have hto :
      (outPtr + UInt32.ofNat i).toNat = (UInt32.ofNat j + outPtr).toNat := by
    rw [UInt32.toNat_add, UInt32.toNat_add]
    rw [UInt32.toNat_ofNat_of_lt', UInt32.toNat_ofNat_of_lt']
    · simpa [UInt32.size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    · simp [UInt32.size]
      omega
    · simp [UInt32.size]
      omega
  have heq : outPtr + UInt32.ofNat i = UInt32.ofNat j + outPtr := UInt32.toNat.inj hto
  have hnat := congrArg UInt32.toNat heq
  rw [UInt32.toNat_add, UInt32.toNat_add] at hnat
  rw [UInt32.toNat_ofNat_of_lt', UInt32.toNat_ofNat_of_lt'] at hnat
  · have hmodle_l : (outPtr.toNat + i) % UInt32.size ≤ outPtr.toNat + i := Nat.mod_le _ _
    have hmodle_r : (j + outPtr.toNat) % UInt32.size ≤ j + outPtr.toNat := Nat.mod_le _ _
    omega
  · simp [UInt32.size]
    omega
  · simp [UInt32.size]
    omega

theorem outPtr_add_toNat_of_before_table (outPtr : UInt32) (houtTable : outPtr.toNat + 20 ≤ 1049400)
    {k : Nat} (hk : k < 20) :
    (outPtr + UInt32.ofNat k).toNat = outPtr.toNat + k := by
  rw [UInt32.toNat_add]
  rw [UInt32.toNat_ofNat_of_lt']
  · have hlt : outPtr.toNat + k < UInt32.size := by
      simp [UInt32.size]
      omega
    rw [Nat.mod_eq_of_lt hlt]
  · simp [UInt32.size]
    omega

theorem outPtr_16_19_addr_facts_before_table (outPtr : UInt32)
    (houtTable : outPtr.toNat + 20 ≤ 1049400) :
    (outPtr + 17).toNat = (outPtr + 16).toNat + 1 ∧
    (outPtr + 19).toNat = (outPtr + 18).toNat + 1 ∧
    (outPtr + 16).toNat ≠ (outPtr + 18).toNat ∧
    (outPtr + 16).toNat ≠ (outPtr + 18).toNat + 1 ∧
    (outPtr + 17).toNat ≠ (outPtr + 18).toNat ∧
    (outPtr + 17).toNat ≠ (outPtr + 18).toNat + 1 := by
  have h16 : (outPtr + 16).toNat = outPtr.toNat + 16 := by
    simpa using outPtr_add_toNat_of_before_table outPtr houtTable (k := 16) (by norm_num)
  have h17 : (outPtr + 17).toNat = outPtr.toNat + 17 := by
    simpa using outPtr_add_toNat_of_before_table outPtr houtTable (k := 17) (by norm_num)
  have h18 : (outPtr + 18).toNat = outPtr.toNat + 18 := by
    simpa using outPtr_add_toNat_of_before_table outPtr houtTable (k := 18) (by norm_num)
  have h19 : (outPtr + 19).toNat = outPtr.toNat + 19 := by
    simpa using outPtr_add_toNat_of_before_table outPtr houtTable (k := 19) (by norm_num)
  omega

theorem read32_write32_disjoint (m : Mem) (a : UInt32) (v : UInt32) (i : Nat)
    (h0 : i ≠ a.toNat) (h1 : i ≠ a.toNat + 1) (h2 : i ≠ a.toNat + 2)
    (h3 : i ≠ a.toNat + 3) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp [h0, h1, h2, h3]

/-- ASCII digit byte: `'0' ||| d = '0' + d` for a decimal digit `d`. -/
theorem digit_byte (d : UInt32) (h : d.toNat < 10) :
    (48 : UInt32) ||| d = UInt32.ofNat (48 + d.toNat) := by
  have h16 : d < 16 := UInt32.lt_iff_toNat_lt.mpr (by simpa using (by omega : d.toNat < 16))
  rw [show (48 : UInt32) ||| d = 48 + d from by bv_decide]
  apply UInt32.toNat.inj
  have hsz : UInt32.size = 4294967296 := rfl
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' (by omega)]
  simp only [show (48 : UInt32).toNat = 48 from rfl]
  omega

/-- `UInt8` version of `digit_byte`. -/
theorem digit_byte8 (d : Nat) (h : d < 10) :
    (UInt8.ofNat d) ||| 48 = UInt8.ofNat (48 + d) := by
  interval_cases d <;> decide

theorem digit_add8 (d : Nat) (h : d < 10) :
    (48 : UInt8) + UInt8.ofNat d = UInt8.ofNat (48 + d) := by
  interval_cases d <;> decide

theorem digit_byte_ofNat_toUInt8 (d : Nat) (h : d < 10) :
    ((UInt32.ofNat d ||| 48).toUInt8) = UInt8.ofNat (48 + d) := by
  interval_cases d <;> native_decide

theorem packed_two_digits_low_byte (lo hi : Nat) (hlo : lo < 10) (hhi : hi < 10) :
    (((UInt32.ofNat (48 + lo) ||| (UInt32.ofNat (48 + hi) <<< (8 : UInt32))) &&&
        (0xFF : UInt32)).toUInt8) =
      UInt8.ofNat (48 + lo) := by
  interval_cases lo <;> interval_cases hi <;> native_decide

theorem packed_two_digits_high_byte (lo hi : Nat) (hlo : lo < 10) (hhi : hi < 10) :
    ((((UInt32.ofNat (48 + lo) ||| (UInt32.ofNat (48 + hi) <<< (8 : UInt32))) >>>
        (8 : UInt32)) &&& (0xFF : UInt32)).toUInt8) =
      UInt8.ofNat (48 + hi) := by
  interval_cases lo <;> interval_cases hi <;> native_decide

/-! ### `itoa` digit table in the canonical initial store -/

def digitTableBase : Nat := 1049400

def harnessFramePtr : Nat := 1048512

def fastFramePtr : Nat := 1048464

def fastDigitsPtr : Nat := 1048472

@[simp] theorem initial_mem_pages :
    («module».initialStore (α := Unit)).mem.pages = 17 := by
  native_decide

theorem initial_harness_frame_bound :
    harnessFramePtr + 64 ≤ («module».initialStore (α := Unit)).mem.pages * 65536 := by
  native_decide

theorem initial_harness_frame_before_table :
    harnessFramePtr + 64 ≤ digitTableBase := by
  native_decide

theorem initial_fast_frame_bound :
    fastFramePtr + 48 ≤ («module».initialStore (α := Unit)).mem.pages * 65536 := by
  native_decide

theorem initial_fast_digits_bound :
    fastDigitsPtr + 20 ≤ («module».initialStore (α := Unit)).mem.pages * 65536 := by
  native_decide

theorem initial_fast_digits_before_table :
    fastDigitsPtr + 20 ≤ digitTableBase := by
  native_decide

set_option maxHeartbeats 2000000 in
theorem digit_table_tens_byte (d : Nat) (h : d < 100) :
    («module».initialStore (α := Unit)).mem.bytes (digitTableBase + 2 * d) =
      UInt8.ofNat (48 + d / 10) := by
  interval_cases d <;> native_decide

set_option maxHeartbeats 2000000 in
theorem digit_table_ones_byte (d : Nat) (h : d < 100) :
    («module».initialStore (α := Unit)).mem.bytes (digitTableBase + 2 * d + 1) =
      UInt8.ofNat (48 + d % 10) := by
  interval_cases d <;> native_decide

set_option maxHeartbeats 2000000 in
theorem digit_table_read16_nat (d : Nat) (h : d < 100) :
    («module».initialStore (α := Unit)).mem.read16 (UInt32.ofNat (digitTableBase + 2 * d)) =
      (UInt32.ofNat (48 + d / 10)) ||| ((UInt32.ofNat (48 + d % 10)) <<< 8) := by
  interval_cases d <;> native_decide

set_option maxHeartbeats 2000000 in
theorem digit_table_read16_low_byte (d : Nat) (h : d < 100) :
    (((«module».initialStore (α := Unit)).mem.read16
        (UInt32.ofNat (digitTableBase + 2 * d))) &&& 0xFF).toUInt8 =
      UInt8.ofNat (48 + d / 10) := by
  rw [digit_table_read16_nat d h]
  interval_cases d <;> native_decide

set_option maxHeartbeats 2000000 in
theorem digit_table_read16_high_byte (d : Nat) (h : d < 100) :
    ((((«module».initialStore (α := Unit)).mem.read16
        (UInt32.ofNat (digitTableBase + 2 * d))) >>> 8) &&& 0xFF).toUInt8 =
      UInt8.ofNat (48 + d % 10) := by
  rw [digit_table_read16_nat d h]
  interval_cases d <;> native_decide

theorem digit_table_read16_u32 (d : UInt32) (h : d.toNat < 100) :
    («module».initialStore (α := Unit)).mem.read16 ((d <<< (1 : UInt32)) + 1049400) =
      (UInt32.ofNat (48 + d.toNat / 10)) ||| ((UInt32.ofNat (48 + d.toNat % 10)) <<< 8) := by
  have hshift : (d <<< (1 : UInt32)).toNat = 2 * d.toNat := by
    rw [UInt32.toNat_shiftLeft]
    simp only [show (1 : UInt32).toNat % 32 = 1 from rfl]
    rw [Nat.shiftLeft_eq]
    have hlt : d.toNat * 2 < UInt32.size := by
      have hsize : UInt32.size = 4294967296 := rfl
      omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have haddr : (d <<< (1 : UInt32)) + 1049400 =
      UInt32.ofNat (digitTableBase + 2 * d.toNat) := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hshift]
    simp only [show (1049400 : UInt32).toNat = 1049400 from rfl]
    rw [UInt32.toNat_ofNat_of_lt']
    · simp [digitTableBase]
      omega
    · simp [digitTableBase, UInt32.size]
      omega
  rw [haddr]
  exact digit_table_read16_nat d.toNat h

theorem digit_table_addr_u32_le (d : UInt32) (h : d.toNat < 100) :
    ((d <<< (1 : UInt32)) + 1049400).toNat ≤ 1049598 := by
  rw [UInt32.toNat_add, UInt32.toNat_shiftLeft]
  simp only [show (1 : UInt32).toNat % 32 = 1 from rfl,
    show (1049400 : UInt32).toNat = 1049400 from rfl]
  rw [Nat.shiftLeft_eq]
  have hlt : d.toNat * 2 < UInt32.size := by
    have hsize : UInt32.size = 4294967296 := rfl
    omega
  have hsumlt : d.toNat * 2 + 1049400 < UInt32.size := by
    have hsize : UInt32.size = 4294967296 := rfl
    omega
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hsumlt]
  omega

set_option maxHeartbeats 2000000 in
theorem digit_table_read16_u32_low_byte (d : UInt32) (h : d.toNat < 100) :
    (((«module».initialStore (α := Unit)).mem.read16
        ((d <<< (1 : UInt32)) + 1049400)) &&& 0xFF).toUInt8 =
      UInt8.ofNat (48 + d.toNat / 10) := by
  rw [digit_table_read16_u32 d h]
  interval_cases d.toNat <;> native_decide

set_option maxHeartbeats 2000000 in
theorem digit_table_read16_u32_high_byte (d : UInt32) (h : d.toNat < 100) :
    ((((«module».initialStore (α := Unit)).mem.read16
        ((d <<< (1 : UInt32)) + 1049400)) >>> 8) &&& 0xFF).toUInt8 =
      UInt8.ofNat (48 + d.toNat % 10) := by
  rw [digit_table_read16_u32 d h]
  interval_cases d.toNat <;> native_decide

theorem write16_digit_table_u32_low_byte (m : Mem) (a d : UInt32) (h : d.toNat < 100) :
    (m.write16 a ((«module».initialStore (α := Unit)).mem.read16
        ((d <<< (1 : UInt32)) + 1049400))).bytes a.toNat =
      UInt8.ofNat (48 + d.toNat / 10) := by
  rw [read16_write16_low]
  exact digit_table_read16_u32_low_byte d h

theorem write16_digit_table_u32_high_byte (m : Mem) (a d : UInt32) (h : d.toNat < 100) :
    (m.write16 a ((«module».initialStore (α := Unit)).mem.read16
        ((d <<< (1 : UInt32)) + 1049400))).bytes (a.toNat + 1) =
      UInt8.ofNat (48 + d.toNat % 10) := by
  rw [read16_write16_high]
  exact digit_table_read16_u32_high_byte d h

/-! ### Magic division used by the 4-digit chunk path -/

theorem magic_div100_nat (k : Nat) (hk : k < 10000) :
    (k * 5243) / 524288 = k / 100 := by
  let q := k / 100
  let r := k % 100
  have hkqr : k = q * 100 + r := by
    have : 100 * q + r = k := Nat.div_add_mod k 100
    omega
  have hr : r < 100 := Nat.mod_lt _ (by norm_num)
  have hq : q < 100 := by omega
  have hprod : k * 5243 = q * 524300 + r * 5243 := by
    rw [hkqr]
    ring
  apply Nat.div_eq_of_lt_le
  · rw [hprod]
    omega
  · rw [hprod]
    omega

theorem magic_div100_u32 (k : UInt32) (hk : k.toNat < 10000) :
    ((k * 5243) >>> (19 : UInt32)).toNat = k.toNat / 100 := by
  rw [UInt32.toNat_shiftRight, UInt32.toNat_mul]
  simp only [show (19 : UInt32).toNat % 32 = 19 from rfl,
    show (5243 : UInt32).toNat = 5243 from rfl]
  have hprodlt : k.toNat * 5243 < UInt32.size := by
    have hsize : UInt32.size = 4294967296 := rfl
    omega
  rw [Nat.mod_eq_of_lt hprodlt, Nat.shiftRight_eq_div_pow]
  simpa using magic_div100_nat k.toNat hk

theorem magic_div100_shift_lt1000 (n : UInt64) (hn : n.toNat < 1000) :
    (5243 * n.toNat % 4294967296) >>> 19 = n.toNat / 100 := by
  have hprodlt : 5243 * n.toNat < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hprodlt, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
  exact magic_div100_nat n.toNat (by omega)

theorem magic_div100_shift_lt10000 (n : UInt64) (hn : n.toNat < 10000) :
    (5243 * n.toNat % 4294967296) >>> 19 = n.toNat / 100 := by
  have hprodlt : 5243 * n.toNat < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hprodlt, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
  exact magic_div100_nat n.toNat hn

theorem leading_digit_byte_lt1000 (n : UInt64) (hn : n.toNat < 1000) :
    ((UInt32.ofNat ((5243 * n.toNat % 4294967296) >>> 19) ||| 48).toUInt8) =
      UInt8.ofNat (48 + n.toNat / 100) := by
  rw [magic_div100_shift_lt1000 n hn]
  exact digit_byte_ofNat_toUInt8 (n.toNat / 100) (by omega)

theorem u64_div10000_eq_zero_lt10000 (n : UInt64) (hn : n.toNat < 10000) :
    n / (10000 : UInt64) = 0 := by
  apply UInt64.toNat.inj
  rw [UInt64.toNat_div]
  simp only [show (10000 : UInt64).toNat = 10000 from rfl,
    show (0 : UInt64).toNat = 0 from rfl]
  omega

theorem u64_not_gt_9999999_lt10000 (n : UInt64) (hn : n.toNat < 10000) :
    ¬ (9999999 : UInt64) < n := by
  rw [UInt64.lt_iff_toNat_lt]
  simp only [show (9999999 : UInt64).toNat = 9999999 from rfl]
  omega

theorem u64_chunk_remainder_lt10000 (n : UInt64) (hn : n.toNat < 10000) :
    n - (n / (10000 : UInt64)) * (10000 : UInt64) = n := by
  rw [u64_div10000_eq_zero_lt10000 n hn]
  simp

theorem digit_table_quot_addr_le_lt10000 (n : UInt64) (hn : n.toNat < 10000) :
    ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400).toNat ≤ 1049598 := by
  have hd : (UInt32.ofNat (n.toNat / 100)).toNat < 100 := by
    rw [UInt32.toNat_ofNat_of_lt']
    · omega
    · simp [UInt32.size]
      omega
  exact digit_table_addr_u32_le (UInt32.ofNat (n.toNat / 100)) hd

theorem digit_table_quot_load16_bound_lt10000 (pages : Nat) (n : UInt64)
    (hn : n.toNat < 10000) (htable : 1049600 ≤ pages * 65536) :
    ¬ ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400).toNat + 0 + 2 >
      pages * 65536 := by
  have hle := digit_table_quot_addr_le_lt10000 n hn
  omega

theorem digit_table_quot_load16_bound_nat_lt10000 (pages : Nat) (n : UInt64)
    (hn : n.toNat < 10000) (htable : 1049600 ≤ pages * 65536) :
    ((5243 * n.toNat % 4294967296) >>> 19 <<< 1) % 4294967296 + 1049400 + 2 ≤
      pages * 65536 := by
  rw [magic_div100_shift_lt10000 n hn, Nat.shiftLeft_eq]
  have hlt : (n.toNat / 100) * 2 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

theorem magic_div100_nat_lt100 (n : Nat) (hn : n < 100) :
    (5243 * n % 4294967296) >>> 19 = 0 := by
  have hprodlt : 5243 * n < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hprodlt, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
  simpa [show n / 100 = 0 by omega] using magic_div100_nat n (by omega)

theorem two_digit_table_index_nat (n : Nat) (hn : n < 100) :
    (((n + 4294967196 * ((5243 * n % 4294967296) >>> 19)) % 4294967296) <<< 1) %
        4294967296 = 2 * n := by
  rw [magic_div100_nat_lt100 n hn]
  simp [Nat.shiftLeft_eq]
  have hlt : n * 2 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  ring

theorem digit_pair_table_index_nat (k : Nat) (hk : k < 10000) :
    (((k + 4294967196 * ((5243 * k % 4294967296) >>> 19)) % 4294967296) <<< 1) %
        4294967296 = 2 * (k % 100) := by
  have hprodlt : 5243 * k < 4294967296 := by omega
  have hq : (5243 * k % 4294967296) >>> 19 = k / 100 := by
    rw [Nat.mod_eq_of_lt hprodlt, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
    exact magic_div100_nat k hk
  let q := k / 100
  let r := k % 100
  have hkqr : k = q * 100 + r := by
    have : 100 * q + r = k := Nat.div_add_mod k 100
    omega
  have hr : r < 100 := Nat.mod_lt _ (by norm_num)
  have hr32 : r < 4294967296 := by omega
  have hinner : (k + 4294967196 * ((5243 * k % 4294967296) >>> 19)) % 4294967296 = r := by
    rw [hq, hkqr]
    have hq_lt : q < 100 := by omega
    have hdivq : (q * 100 + r) / 100 = q := by omega
    have hsum : q * 100 + r + 4294967196 * q = q * 4294967296 + r := by ring
    rw [hdivq]
    rw [hsum]
    rw [Nat.mul_comm q 4294967296]
    rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hr32,
      Nat.mod_eq_of_lt hr32]
  rw [hinner, Nat.shiftLeft_eq]
  have h2lt : r * 2 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt h2lt]
  ring

theorem two_digit_table_index_u32 (n : UInt64) (hn : n.toNat < 100) :
    ((UInt32.ofNat (n.toNat % 2 ^ 32) +
        4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) =
      UInt32.ofNat (2 * n.toNat) := by
  interval_cases n.toNat <;> native_decide

theorem two_digit_table_read_ones (n : UInt64) (hn : n.toNat < 100) :
    («module».initialStore (α := Unit)).mem.read8
        (((UInt32.ofNat (n.toNat % 2 ^ 32) +
          4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) +
          1049401) =
      UInt8.ofNat (48 + n.toNat % 10) := by
  rw [two_digit_table_index_u32 n hn]
  interval_cases n.toNat <;> native_decide

theorem two_digit_table_read_tens (n : UInt64) (hn : n.toNat < 100) :
    («module».initialStore (α := Unit)).mem.read8
        (((UInt32.ofNat (n.toNat % 2 ^ 32) +
          4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) +
          1049400) =
      UInt8.ofNat (48 + n.toNat / 10) := by
  rw [two_digit_table_index_u32 n hn]
  interval_cases n.toNat <;> native_decide

theorem digit_pair_table_tens_byte_lt1000 (n : Nat) (_hn : n < 1000) :
    («module».initialStore (α := Unit)).mem.bytes (digitTableBase + 2 * (n % 100)) =
      UInt8.ofNat (48 + n / 10 % 10) := by
  rw [digit_table_tens_byte (n % 100) (Nat.mod_lt _ (by norm_num))]
  have htens : n % 100 / 10 = n / 10 % 10 := by omega
  rw [htens]

theorem digit_pair_table_ones_byte_lt1000 (n : Nat) (_hn : n < 1000) :
    («module».initialStore (α := Unit)).mem.bytes (digitTableBase + 2 * (n % 100) + 1) =
      UInt8.ofNat (48 + n % 10) := by
  rw [digit_table_ones_byte (n % 100) (Nat.mod_lt _ (by norm_num))]
  have hones : n % 100 % 10 = n % 10 := by omega
  rw [hones]

theorem digit_pair_table_high_tens_byte_lt10000 (n : Nat) (hn : n < 10000) :
    («module».initialStore (α := Unit)).mem.bytes (digitTableBase + 2 * (n / 100)) =
      UInt8.ofNat (48 + n / 1000) := by
  have hpair : n / 100 < 100 := by omega
  rw [digit_table_tens_byte (n / 100) hpair]
  have htens : n / 100 / 10 = n / 1000 := by omega
  rw [htens]

theorem digit_pair_table_high_ones_byte_lt10000 (n : Nat) (hn : n < 10000) :
    («module».initialStore (α := Unit)).mem.bytes (digitTableBase + 2 * (n / 100) + 1) =
      UInt8.ofNat (48 + n / 100 % 10) := by
  have hpair : n / 100 < 100 := by omega
  exact digit_table_ones_byte (n / 100) hpair

theorem digit_pair_table_low_tens_byte_lt10000 (n : Nat) (_hn : n < 10000) :
    («module».initialStore (α := Unit)).mem.bytes (digitTableBase + 2 * (n % 100)) =
      UInt8.ofNat (48 + n / 10 % 10) := by
  rw [digit_table_tens_byte (n % 100) (Nat.mod_lt _ (by norm_num))]
  have htens : n % 100 / 10 = n / 10 % 10 := by omega
  rw [htens]

theorem digit_pair_table_low_ones_byte_lt10000 (n : Nat) (_hn : n < 10000) :
    («module».initialStore (α := Unit)).mem.bytes (digitTableBase + 2 * (n % 100) + 1) =
      UInt8.ofNat (48 + n % 10) := by
  rw [digit_table_ones_byte (n % 100) (Nat.mod_lt _ (by norm_num))]
  have hones : n % 100 % 10 = n % 10 := by omega
  rw [hones]

theorem digit_pair_table_high_read16_lt10000 (n : Nat) (hn : n < 10000) :
    («module».initialStore (α := Unit)).mem.read16
        (UInt32.ofNat (digitTableBase + 2 * (n / 100))) =
      (UInt32.ofNat (48 + n / 1000)) ||| ((UInt32.ofNat (48 + n / 100 % 10)) <<< 8) := by
  rw [digit_table_read16_nat (n / 100) (by omega)]
  have htens : n / 100 / 10 = n / 1000 := by omega
  rw [htens]

theorem digit_pair_table_low_read16_lt10000 (n : Nat) (_hn : n < 10000) :
    («module».initialStore (α := Unit)).mem.read16
        (UInt32.ofNat (digitTableBase + 2 * (n % 100))) =
      (UInt32.ofNat (48 + n / 10 % 10)) ||| ((UInt32.ofNat (48 + n % 10)) <<< 8) := by
  rw [digit_table_read16_nat (n % 100) (Nat.mod_lt _ (by norm_num))]
  have htens : n % 100 / 10 = n / 10 % 10 := by omega
  have hones : n % 100 % 10 = n % 10 := by omega
  rw [htens, hones]

theorem digit_pair_table_high_read16_u32_lt10000 (n : UInt64) (hn : n.toNat < 10000) :
    («module».initialStore (α := Unit)).mem.read16
        ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400) =
      (UInt32.ofNat (48 + n.toNat / 1000)) |||
        ((UInt32.ofNat (48 + n.toNat / 100 % 10)) <<< 8) := by
  have haddr :
      (UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400 =
        UInt32.ofNat (digitTableBase + 2 * (n.toNat / 100)) := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, UInt32.toNat_shiftLeft]
    simp only [show (1 : UInt32).toNat % 32 = 1 from rfl,
      show (1049400 : UInt32).toNat = 1049400 from rfl]
    rw [Nat.shiftLeft_eq]
    rw [UInt32.toNat_ofNat_of_lt', UInt32.toNat_ofNat_of_lt']
    · simp [digitTableBase]
      have hlt : (n.toNat / 100) * 2 < UInt32.size := by
        have hsize : UInt32.size = 4294967296 := rfl
        omega
      have hsumlt : (n.toNat / 100) * 2 + 1049400 < UInt32.size := by
        have hsize : UInt32.size = 4294967296 := rfl
        omega
      rw [Nat.mod_eq_of_lt hsumlt]
      omega
    · simp [digitTableBase, UInt32.size]
      omega
    · simp [UInt32.size]
      omega
  rw [haddr]
  exact digit_pair_table_high_read16_lt10000 n.toNat hn

theorem digit_pair_table_index_u32_lt10000 (n : UInt64) (hn : n.toNat < 10000) :
    ((UInt32.ofNat (n.toNat % 2 ^ 32) +
        4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) =
      UInt32.ofNat (2 * (n.toNat % 100)) := by
  apply UInt32.toNat.inj
  have hwrap :
      (UInt32.ofNat (n.toNat % 2 ^ 32)).toNat = n.toNat := by
    rw [Nat.mod_eq_of_lt (by omega : n.toNat < 2 ^ 32)]
    exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  have hq :
      (((5243 : UInt32) * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32)).toNat =
        n.toNat / 100 := by
    rw [UInt32.toNat_shiftRight, UInt32.toNat_mul]
    simp only [show (19 : UInt32).toNat % 32 = 19 from rfl,
      show (5243 : UInt32).toNat = 5243 from rfl]
    rw [hwrap]
    have hprodlt : 5243 * n.toNat < UInt32.size := by
      have hsize : UInt32.size = 4294967296 := rfl
      omega
    rw [Nat.mod_eq_of_lt hprodlt, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
    simpa using magic_div100_nat n.toNat (by omega)
  rw [UInt32.toNat_shiftLeft]
  simp only [show (1 : UInt32).toNat % 32 = 1 from rfl]
  rw [Nat.shiftLeft_eq]
  rw [UInt32.toNat_add, UInt32.toNat_mul]
  simp only [show (4294967196 : UInt32).toNat = 4294967196 from rfl]
  rw [hwrap, hq]
  rw [UInt32.toNat_ofNat_of_lt']
  · have hidx := digit_pair_table_index_nat n.toNat (by omega)
    simp [Nat.shiftLeft_eq] at hidx
    have hmodMul :
        (n.toNat + 4294967196 * (n.toNat / 100) % UInt32.size) % UInt32.size =
          (n.toNat + 4294967196 * (n.toNat / 100)) % UInt32.size := by
      conv_lhs => rw [Nat.add_mod, Nat.mod_mod]
      conv_rhs => rw [Nat.add_mod]
    simpa [UInt32.size, hmodMul, magic_div100_shift_lt10000 n hn] using hidx
  · simp [UInt32.size]
    omega

theorem digit_pair_table_low_read16_u32_lt10000 (n : UInt64) (hn : n.toNat < 10000) :
    («module».initialStore (α := Unit)).mem.read16
        (((UInt32.ofNat (n.toNat % 2 ^ 32) +
          4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) +
          1049400) =
      (UInt32.ofNat (48 + n.toNat / 10 % 10)) |||
        ((UInt32.ofNat (48 + n.toNat % 10)) <<< 8) := by
  rw [digit_pair_table_index_u32_lt10000 n hn]
  rw [show UInt32.ofNat (2 * (n.toNat % 100)) + 1049400 =
      UInt32.ofNat (digitTableBase + 2 * (n.toNat % 100)) by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add]
    simp only [show (1049400 : UInt32).toNat = 1049400 from rfl]
    rw [UInt32.toNat_ofNat_of_lt', UInt32.toNat_ofNat_of_lt']
    · simp [digitTableBase]
      omega
    · simp [digitTableBase, UInt32.size]
      omega
    · simp [UInt32.size]
      omega]
  exact digit_pair_table_low_read16_lt10000 n.toNat hn

theorem read16_low_pair_after_output_write16_lt10000 (n : UInt64) (outPtr word : UInt32)
    (_hn : n.toNat < 10000) (houtTable : outPtr.toNat + 20 ≤ digitTableBase) :
    ((«module».initialStore (α := Unit)).mem.write16 (outPtr + 16) word).read16
        (UInt32.ofNat (digitTableBase + 2 * (n.toNat % 100))) =
      («module».initialStore (α := Unit)).mem.read16
        (UInt32.ofNat (digitTableBase + 2 * (n.toNat % 100))) := by
  have hwriteEq : (outPtr + 16).toNat = outPtr.toNat + 16 := by
    rw [UInt32.toNat_add]
    simp only [show (16 : UInt32).toNat = 16 from rfl]
    have hlt : outPtr.toNat + 16 < UInt32.size := by
      simp [UInt32.size]
      have houtSmall : outPtr.toNat + 20 ≤ 1049400 := by
        simpa [digitTableBase] using houtTable
      omega
    rw [Nat.mod_eq_of_lt hlt]
  have hwrite0 : (outPtr + 16).toNat < digitTableBase := by
    rw [hwriteEq]
    omega
  have hwrite1 : (outPtr + 16).toNat + 1 < digitTableBase := by
    rw [hwriteEq]
    omega
  apply read16_write16_disjoint_addr
  · rw [UInt32.toNat_ofNat_of_lt']
    · omega
    · simp [digitTableBase, UInt32.size]
      omega
  · rw [UInt32.toNat_ofNat_of_lt']
    · omega
    · simp [digitTableBase, UInt32.size]
      omega
  · rw [UInt32.toNat_ofNat_of_lt']
    · omega
    · simp [digitTableBase, UInt32.size]
      omega
  · rw [UInt32.toNat_ofNat_of_lt']
    · omega
    · simp [digitTableBase, UInt32.size]
      omega

theorem read16_low_pair_after_output_write16_u32_lt10000 (n : UInt64) (outPtr word : UInt32)
    (hn : n.toNat < 10000) (houtTable : outPtr.toNat + 20 ≤ digitTableBase) :
    ((«module».initialStore (α := Unit)).mem.write16 (outPtr + 16) word).read16
        (((UInt32.ofNat (n.toNat % 2 ^ 32) +
          4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) +
          1049400) =
      («module».initialStore (α := Unit)).mem.read16
        (((UInt32.ofNat (n.toNat % 2 ^ 32) +
          4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) +
          1049400) := by
  rw [digit_pair_table_index_u32_lt10000 n hn]
  rw [show UInt32.ofNat (2 * (n.toNat % 100)) + 1049400 =
      UInt32.ofNat (digitTableBase + 2 * (n.toNat % 100)) by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add]
    simp only [show (1049400 : UInt32).toNat = 1049400 from rfl]
    rw [UInt32.toNat_ofNat_of_lt', UInt32.toNat_ofNat_of_lt']
    · simp [digitTableBase]
      omega
    · simp [digitTableBase, UInt32.size]
      omega
    · simp [UInt32.size]
      omega]
  exact read16_low_pair_after_output_write16_lt10000 n outPtr word hn houtTable

theorem write16_two_pairs_digits_lt10000 (m : Mem) (outPtr : UInt32) (n : UInt64)
    (_hn : n.toNat < 10000)
    (h17 : (outPtr + 17).toNat = (outPtr + 16).toNat + 1)
    (h19 : (outPtr + 19).toNat = (outPtr + 18).toNat + 1)
    (h1618ne : (outPtr + 16).toNat ≠ (outPtr + 18).toNat)
    (h1619ne : (outPtr + 16).toNat ≠ (outPtr + 18).toNat + 1)
    (h1718ne : (outPtr + 17).toNat ≠ (outPtr + 18).toNat)
    (h1719ne : (outPtr + 17).toNat ≠ (outPtr + 18).toNat + 1)
    (hhi :
      (((m.read16 ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400)) &&& 0xFF).toUInt8 =
        UInt8.ofNat (48 + n.toNat / 1000)))
    (hhi' :
      ((((m.read16 ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400)) >>> 8) &&& 0xFF).toUInt8 =
        UInt8.ofNat (48 + n.toNat / 100 % 10)))
    (hlo :
      (((m.write16 (outPtr + 16)
          (m.read16 ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400))).read16
            (((UInt32.ofNat (n.toNat % 2 ^ 32) +
              4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) +
              1049400)) &&& 0xFF).toUInt8 =
        UInt8.ofNat (48 + n.toNat / 10 % 10))
    (hlo' :
      ((((m.write16 (outPtr + 16)
          (m.read16 ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400))).read16
            (((UInt32.ofNat (n.toNat % 2 ^ 32) +
              4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) +
              1049400)) >>> 8) &&& 0xFF).toUInt8 =
        UInt8.ofNat (48 + n.toNat % 10)) :
    let m' :=
      (m.write16 (outPtr + 16)
        (m.read16 ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400))).write16
          (outPtr + 18)
          ((m.write16 (outPtr + 16)
            (m.read16 ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400))).read16
              (((UInt32.ofNat (n.toNat % 2 ^ 32) +
                4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) +
                1049400))
    m'.bytes (outPtr + 16).toNat = UInt8.ofNat (48 + n.toNat / 1000) ∧
    m'.bytes (outPtr + 17).toNat = UInt8.ofNat (48 + n.toNat / 100 % 10) ∧
    m'.bytes (outPtr + 18).toNat = UInt8.ofNat (48 + n.toNat / 10 % 10) ∧
    m'.bytes (outPtr + 19).toNat = UInt8.ofNat (48 + n.toNat % 10) := by
  intro m'
  unfold m'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [read16_write16_disjoint]
    · rw [read16_write16_low]
      exact hhi
    · exact h1618ne
    · exact h1619ne
  · rw [read16_write16_disjoint]
    · rw [h17, read16_write16_high]
      exact hhi'
    · exact h1718ne
    · exact h1719ne
  · rw [read16_write16_low]
    exact hlo
  · rw [h19, read16_write16_high]
    exact hlo'

theorem write16_two_pairs_digits_lt10000_initial (outPtr : UInt32) (n : UInt64)
    (hn : n.toNat < 10000) (houtTable : outPtr.toNat + 20 ≤ digitTableBase) :
    let m := («module».initialStore (α := Unit)).mem
    let m' :=
      (m.write16 (outPtr + 16)
        (m.read16 ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400))).write16
          (outPtr + 18)
          ((m.write16 (outPtr + 16)
            (m.read16 ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400))).read16
              (((UInt32.ofNat (n.toNat % 2 ^ 32) +
                4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)) +
                1049400))
    m'.bytes (outPtr + 16).toNat = UInt8.ofNat (48 + n.toNat / 1000) ∧
    m'.bytes (outPtr + 17).toNat = UInt8.ofNat (48 + n.toNat / 100 % 10) ∧
    m'.bytes (outPtr + 18).toNat = UInt8.ofNat (48 + n.toNat / 10 % 10) ∧
    m'.bytes (outPtr + 19).toNat = UInt8.ofNat (48 + n.toNat % 10) := by
  intro m m'
  have haddr := outPtr_16_19_addr_facts_before_table outPtr houtTable
  obtain ⟨h17, h19, h1618, h1619, h1718, h1719⟩ := haddr
  refine write16_two_pairs_digits_lt10000 m outPtr n hn
    h17 h19 h1618 h1619 h1718 h1719 ?_ ?_ ?_ ?_
  · rw [digit_pair_table_high_read16_u32_lt10000 n hn]
    exact packed_two_digits_low_byte (n.toNat / 1000) (n.toNat / 100 % 10) (by omega) (by omega)
  · rw [digit_pair_table_high_read16_u32_lt10000 n hn]
    exact packed_two_digits_high_byte (n.toNat / 1000) (n.toNat / 100 % 10) (by omega) (by omega)
  · rw [read16_low_pair_after_output_write16_u32_lt10000 n outPtr
      (m.read16 ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400)) hn houtTable]
    rw [digit_pair_table_low_read16_u32_lt10000 n hn]
    exact packed_two_digits_low_byte (n.toNat / 10 % 10) (n.toNat % 10) (by omega)
      (Nat.mod_lt _ (by norm_num))
  · rw [read16_low_pair_after_output_write16_u32_lt10000 n outPtr
      (m.read16 ((UInt32.ofNat (n.toNat / 100) <<< (1 : UInt32)) + 1049400)) hn houtTable]
    rw [digit_pair_table_low_read16_u32_lt10000 n hn]
    exact packed_two_digits_high_byte (n.toNat / 10 % 10) (n.toNat % 10) (by omega)
      (Nat.mod_lt _ (by norm_num))

def twoDigitIndex (n : UInt64) : UInt32 :=
  (UInt32.ofNat (n.toNat % 2 ^ 32) +
    4294967196 * ((5243 * UInt32.ofNat (n.toNat % 2 ^ 32)) >>> (19 : UInt32))) <<< (1 : UInt32)

/-! ## Fast formatter core (`func13`), base cases -/

theorem digit_byte_wrap64_toUInt8 (n : UInt64) (hn : n.toNat < 10) :
    (((UInt32.ofNat (n.toNat % 2 ^ 32)) ||| 48).toUInt8) =
      UInt8.ofNat (48 + n.toNat) := by
  have hmod : n.toNat % 2 ^ 32 = n.toNat := by
    have hn32 : n.toNat < 2 ^ 32 := by omega
    exact Nat.mod_eq_of_lt hn32
  rw [hmod]
  interval_cases n.toNat <;> native_decide

/-- `m` holds the decimal string of `n` in the bytes `[b, b + numDigits n)`. -/
def HasDigitsAt (m : Mem) (b n : Nat) : Prop :=
  ∀ j, j < numDigits n →
    m.bytes (b + j) = UInt8.ofNat (48 + n / 10 ^ (numDigits n - 1 - j) % 10)

/-! ## Naive i64 formatter (`func0`)

For non-negative `n` (`< 2^63`) it delegates to `func1`. For negative `n`
it emits `'-'` then formats the magnitude `(0 - n)`. -/

/-- Magnitude of the i64 carried by `n`. -/
def i64mag (n : UInt64) : Nat :=
  if 9223372036854775808 ≤ n.toNat then (0 - n).toNat else n.toNat

/-- Length of the i64 decimal string (with sign). -/
def i64len (n : UInt64) : Nat :=
  numDigits (i64mag n) + (if 9223372036854775808 ≤ n.toNat then 1 else 0)

/-- The i64 decimal string of `n` sits in `[b, b + i64len n)`. -/
def HasDigitsI64 (m : Mem) (b : Nat) (n : UInt64) : Prop :=
  if 9223372036854775808 ≤ n.toNat then
    m.bytes b = 45 ∧ HasDigitsAt m (b + 1) (i64mag n)
  else HasDigitsAt m b (i64mag n)

@[simp] theorem mem_copy_zero (m : Mem) (dst src : Nat) :
    m.copy dst src 0 = m := by
  cases m
  simp [Mem.copy]
  funext i
  by_cases h : dst ≤ i ∧ i < dst
  · omega
  · simp [h]

/-! ## Export wrappers (`opt-level=0` shadow-stack chain)

Under the unoptimized pipeline `check_i64` is `func31` and `check_u64`
is `func32`. Each is a 16-byte shadow-stack wrapper that spills its
`(n, cap)` arguments into its frame (debug spills, never read back) and
forwards to a second wrapper of exactly the same shape (`func28` /
`func29`), which forwards to the actual harness (`func23` / `func21`).
The bridge lemmas below peel both hops, reducing `CheckI64Spec` /
`CheckU64Spec` to `HarnessSpec 23` / `HarnessSpec 21` — the still-open
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
restores the frame. `HarnessSpec 23` (`check_i64`'s inner body) and
`HarnessSpec 21` (`check_u64`'s) are precisely the equivalence claims
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
frame, forward to the harness `func23`, restore the stack pointer. -/
theorem func28_spec (hh : HarnessSpec 23) (env : HostEnv Unit) (st0 : Store Unit)
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
the `u64` harness `func21`. -/
theorem func29_spec (hh : HarnessSpec 21) (env : HostEnv Unit) (st0 : Store Unit)
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
theorem func31_spec (hh : HarnessSpec 23) (env : HostEnv Unit) (st0 : Store Unit)
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
theorem func32_spec (hh : HarnessSpec 21) (env : HostEnv Unit) (st0 : Store Unit)
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
23` / `HarnessSpec 21` (fast formatter ≡ naive oracle, composed through
`func24`/`func22`, `func3`/`func5` and the byte-compare loop) is the
remaining open proof obligation. -/

theorem check_i64_correct_of_harness_spec (hh : HarnessSpec 23) :
    Project.Itoa.Spec.CheckI64Spec := by
  intro env initial n cap hinit
  subst hinit
  refine (func31_spec hh env _ 1048576 n cap
    ⟨initial_mem_pages, initial_global0⟩ (fun i _ => rfl)
    (by decide) (by decide)).mono ?_
  exact fun st vs h => h.1

theorem check_u64_correct_of_harness_spec (hh : HarnessSpec 21) :
    Project.Itoa.Spec.CheckU64Spec := by
  intro env initial n cap hinit
  subst hinit
  refine (func32_spec hh env _ 1048576 n cap
    ⟨initial_mem_pages, initial_global0⟩ (fun i _ => rfl)
    (by decide) (by decide)).mono ?_
  exact fun st vs h => h.1


/-! Restructured development of `func6_spec` (naive u64 formatter core,
pinned to the harness call site: frame pointer `1048416`, frame base
`1048352`, output buffer `1048480`, buffer length 32).

The two memory-routed loops are proven as STANDALONE lemmas over an
abstract continuation `Q` and abstract trailing program `rest`, so the
per-iteration `simp` passes never traverse the surrounding function
body's weakest-precondition term. `func6_spec` then glues prologue →
count loop → success tail → write loop → epilogue. -/

/-! ## Read-over-write framing (shape from `NumInteger`) -/

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

/-! ## The write loop, standalone

Counts the index at `1048388` down from `c` to `0`, writing the digit
byte `'0' + (n / 10^(c-1-p)) % 10` at `1048480 + p` on the way (the
value being peeled lives at `1048376`). Exits by storing the digit
count (slot `1048364`) into the result slot `1048360` and `br 2` —
which surfaces as `.Break 0` at the loop-instruction level. -/

set_option maxHeartbeats 1600000 in
private theorem func6_write_loop (env : HostEnv Unit) (n : UInt64) (cap : UInt32)
    (c : Nat) (B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st2 : Store Unit)
    (_hcap : cap.toNat ≤ 32) (_hcle : c ≤ cap.toNat) (hc20 : c ≤ 20)
    (hpg2 : st2.mem.pages = 17)
    (hidx : st2.mem.read32 1048388 = UInt32.ofNat c)
    (hval : st2.mem.read64 1048376 = n)
    (hcnt : st2.mem.read32 1048364 = UInt32.ofNat c)
    (hpres : ∀ j : Nat, j < 1048352 ∨ (1048416 ≤ j ∧ j < 1048480) ∨ 1048512 ≤ j →
      st2.mem.bytes j = B j)
    (hexit : ∀ (st' : Store Unit) (w5 w6 : Value),
      st'.mem.pages = 17 →
      st'.globals = st2.globals →
      st'.mem.read32 1048360 = UInt32.ofNat c →
      (∀ p : Nat, p < c →
        st'.mem.bytes (1048480 + p) = UInt8.ofNat (48 + n.toNat / 10 ^ (c - 1 - p) % 10)) →
      (∀ j : Nat, j < 1048352 ∨ (1048416 ≤ j ∧ j < 1048480) ∨ 1048512 ≤ j →
        st'.mem.bytes j = B j) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 1048480, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 1048352, w5, w6, Value.i32 0], values := [] })) :
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
      { params := [Value.i64 n, Value.i32 1048480, Value.i32 32, Value.i32 cap],
        locals := [Value.i32 1048352, Value.i32 0, Value.i32 0, Value.i32 0],
        values := [] } env := by
  have a360 : (1048360 : UInt32).toNat = 1048360 := rfl
  have a364 : (1048364 : UInt32).toNat = 1048364 := rfl
  have a376 : (1048376 : UInt32).toNat = 1048376 := rfl
  have a388 : (1048388 : UInt32).toNat = 1048388 := rfl
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals = st2.globals ∧
      (∃ i : Nat, i ≤ c ∧
        st'.mem.read32 1048388 = UInt32.ofNat i ∧
        st'.mem.read64 1048376 = UInt64.ofNat (n.toNat / 10 ^ (c - i)) ∧
        st'.mem.read32 1048364 = UInt32.ofNat c ∧
        (∀ p : Nat, i ≤ p → p < c → st'.mem.bytes (1048480 + p) =
            UInt8.ofNat (48 + n.toNat / 10 ^ (c - 1 - p) % 10)) ∧
        (∀ j : Nat, j < 1048352 ∨ (1048416 ≤ j ∧ j < 1048480) ∨ 1048512 ≤ j →
            st'.mem.bytes j = B j)) ∧
      (∃ w5 w6 : Value,
        s' = { params := [Value.i64 n, Value.i32 1048480, Value.i32 32, Value.i32 cap],
               locals := [Value.i32 1048352, w5, w6, Value.i32 0], values := [] }))
    (μ := fun st' _ => (st'.mem.read32 1048388).toNat)
  · -- entry invariant: `i = c`, value slot holds `n`
    refine ⟨hpg2, rfl, ⟨c, le_rfl, hidx, ?_, hcnt,
      fun p hp1 hp2 => absurd hp1 (by omega), hpres⟩, Value.i32 0, Value.i32 0, rfl⟩
    rw [Nat.sub_self, pow_zero, Nat.div_one, UInt64.ofNat_toNat]
    exact hval
  · -- step
    rintro st3 s3 ⟨hpg3, hgl3, ⟨i, hiC, hidx3, hval3, hcnt3, hdig3, hpres3⟩, w5, w6, rfl⟩
    apply wp_block_cons
    wp_run
    simp [hpg3, hidx3, hval3, hcnt3]
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
      have haddr : (UInt32.ofNat (i - 1) + 1048480).toNat = 1048480 + (i - 1) := by
        rw [UInt32.toNat_add, hofim1]
        simp; omega
      have hnb : ¬ (1114112 ≤ 1048480 + (i - 1)) := by omega
      have hd64 : n.toNat / 10 ^ (c - i) < 18446744073709551616 := by
        have h1 : n.toNat / 10 ^ (c - i) ≤ n.toNat := Nat.div_le_self _ _
        have h2 := UInt64.toNat_lt_size n
        simp [UInt64.size] at h2
        omega
      have hd : n.toNat / 10 ^ (c - i) % 18446744073709551616 % 10 % 4294967296 =
          n.toNat / 10 ^ (c - i) % 10 := by
        rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt (by omega)]
      simp [him1, hguard, hd, haddr, hpg3, hnb]
      -- `hd`'s nested-mod shape makes every later `omega` pathologically
      -- slow (minutes each); drop it now that the simp consumed it.
      clear hd
      refine ⟨⟨hgl3, ⟨i - 1, by omega, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
      · rw [read32_write8_disjoint _ _ _ _ (by omega), read32_write32_same']
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
      · rw [read32_write8_disjoint _ _ _ _ (by omega),
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
        exact hpres3 j hj
      · rw [read32_write8_disjoint _ _ _ _ (by omega), read32_write32_same', hofim1,
          Nat.mod_eq_of_lt (by omega)]
        omega

/-! ## The count loop, standalone

Counts the decimal digits of `n`: slot `1048364` walks `1, 2, …` while
slot `1048368` peels `n/10, n/100, …`. Exits with `.Break 0` (success:
`numDigits n.toNat ≤ cap`, via `br 2`) or `.Break 1` (capacity
exceeded, via `br_if 3`) at the loop-instruction level. -/

set_option maxHeartbeats 1600000 in
private theorem func6_count_loop (env : HostEnv Unit) (n : UInt64) (cap : UInt32)
    (B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st1 : Store Unit)
    (hcap : cap.toNat ≤ 32)
    (hpg : st1.mem.pages = 17)
    (hslot12 : st1.mem.read32 1048364 = 1)
    (hslot16 : st1.mem.read64 1048368 = UInt64.ofNat (n.toNat / 10))
    (hpres : ∀ i : Nat, i < 1048352 ∨ 1048416 ≤ i → st1.mem.bytes i = B i)
    (hsucc : ∀ st' : Store Unit,
      st'.mem.pages = 17 →
      st'.globals = st1.globals →
      numDigits n.toNat ≤ cap.toNat →
      st'.mem.read32 1048364 = UInt32.ofNat (numDigits n.toNat) →
      (∀ i : Nat, i < 1048352 ∨ 1048416 ≤ i → st'.mem.bytes i = B i) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 1048480, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 1048352, Value.i32 0, Value.i32 0, Value.i32 0],
          values := [] }))
    (hfail : ∀ st' : Store Unit,
      st'.mem.pages = 17 →
      st'.globals = st1.globals →
      cap.toNat < numDigits n.toNat →
      (∀ i : Nat, i < 1048352 ∨ 1048416 ≤ i → st'.mem.bytes i = B i) →
      Q (.Break 1 st'
        { params := [Value.i64 n, Value.i32 1048480, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 1048352, Value.i32 0, Value.i32 0, Value.i32 0],
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
      { params := [Value.i64 n, Value.i32 1048480, Value.i32 32, Value.i32 cap],
        locals := [Value.i32 1048352, Value.i32 0, Value.i32 0, Value.i32 0],
        values := [] } env := by
  have a364 : (1048364 : UInt32).toNat = 1048364 := rfl
  have a368 : (1048368 : UInt32).toNat = 1048368 := rfl
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals = st1.globals ∧
      (∃ c : Nat, 1 ≤ c ∧ c ≤ numDigits n.toNat ∧
        st'.mem.read32 1048364 = UInt32.ofNat c ∧
        st'.mem.read64 1048368 = UInt64.ofNat (n.toNat / 10 ^ c)) ∧
      (∀ i : Nat, i < 1048352 ∨ 1048416 ≤ i → st'.mem.bytes i = B i) ∧
      s' = { params := [Value.i64 n, Value.i32 1048480, Value.i32 32, Value.i32 cap],
             locals := [Value.i32 1048352, Value.i32 0, Value.i32 0, Value.i32 0],
             values := [] })
    (μ := fun st' _ => (st'.mem.read64 1048368).toNat)
  · -- entry invariant: `c = 1`
    refine ⟨hpg, rfl, ⟨1, le_rfl, numDigits_pos n.toNat, by simpa using hslot12, ?_⟩,
      hpres, rfl⟩
    rw [pow_one]
    exact hslot16
  · -- step
    rintro st' s' ⟨hpg', hgl', ⟨c, hc1, hcL, hslot12', hslot16'⟩, hpres', rfl⟩
    apply wp_block_cons
    wp_run
    simp [hpg', hslot12', hslot16']
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
      · apply UInt32.toNat.inj
        rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt', UInt32.toNat_ofNat_of_lt']
        · simp
          have := numDigits_toNat_le n
          omega
        · have := numDigits_toNat_le n
          simp [UInt32.size]; omega
        · have := numDigits_toNat_le n
          simp [UInt32.size]; omega
      · apply UInt64.toNat.inj
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
      · rw [Nat.mod_eq_of_lt hvsz]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hv) (by norm_num)

/-! ## `func6_spec`: prologue → count loop → success tail → write loop → epilogue -/

set_option maxHeartbeats 1600000 in
theorem func6_spec (env : HostEnv Unit) (st0 : Store Unit) (n : UInt64) (cap : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 1048416))
    (hcap : cap.toNat ≤ 32) :
    TerminatesWith env «module» 6 st0 [.i32 cap, .i32 32, .i32 1048480, .i64 n]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 1048416) ∧
        rs = [.i32 (if numDigits n.toNat ≤ cap.toNat
                    then UInt32.ofNat (numDigits n.toNat) else 4294967295)] ∧
        (numDigits n.toNat ≤ cap.toNat → HasDigitsAt st'.mem 1048480 n.toNat) ∧
        (∀ i : Nat, i < 1048352 ∨ (1048416 ≤ i ∧ i < 1048480) ∨ 1048512 ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have a352 : (1048352 : UInt32).toNat = 1048352 := rfl
  have a360 : (1048360 : UInt32).toNat = 1048360 := rfl
  have a364 : (1048364 : UInt32).toNat = 1048364 := rfl
  have a368 : (1048368 : UInt32).toNat = 1048368 := rfl
  have a376 : (1048376 : UInt32).toNat = 1048376 := rfl
  have a388 : (1048388 : UInt32).toNat = 1048388 := rfl
  have a392 : (1048392 : UInt32).toNat = 1048392 := rfl
  have a404 : (1048404 : UInt32).toNat = 1048404 := rfl
  have a408 : (1048408 : UInt32).toNat = 1048408 := rfl
  have a412 : (1048412 : UInt32).toNat = 1048412 := rfl
  have a480 : (1048480 : UInt32).toNat = 1048480 := rfl
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i32, .i32, .i32], func6, [.i32]⟩) rfl
  unfold func6
  wp_run
  simp [hg, hpg]
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  apply func6_count_loop env n cap st0.mem.bytes _ hcap
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
    simp [hpg', hslot12']
    apply func6_write_loop env n cap (numDigits n.toNat) st0.mem.bytes _ hcap hfits
      (numDigits_toNat_le n)
    · simp [hpg']
    · -- index slot = c
      rw [read32_write32_same']
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
      simp [hpg2, hres, hgl2, hgl', List.getElem?_set_self (by simpa using hglen)]
      refine ⟨fun h => absurd h (by omega), fun _ j hj => hdig j hj, ?_⟩
      intro i hi
      exact hpres2 i (by omega)
  · -- failure: store `-1`, epilogue
    intro st' hpg' hgl' hover hpres'
    simp only []
    wp_run
    simp [hpg', hgl', List.getElem?_set_self (by simpa using hglen)]
    refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), ?_⟩
    intro i hi
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hpres' i (by omega)

end Project.Itoa.Proofs
