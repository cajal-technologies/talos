import Project.Itoa.Spec

/-!
# Proof of `CheckI64Spec` / `CheckU64Spec`

The exported `check_*(n, cap)` runs the `itoa`-crate formatter and a
naive `% 10` oracle into two on-stack buffers and traps via `unreachable`
iff they disagree. No-trap is therefore the equivalence of the two
formatters; both compute the decimal representation of `n`.

This file is built bottom-up:

1. `wp_call_of_terminates` — step a `.call id` from a `TerminatesWith`
   proof of the callee *at the concrete current store*. (`FuncSpec`
   quantifies over all stores and so is unusable for callees that can
   trap on a small/garbage memory; the harness only ever runs from
   `«module».initialStore`.)
2. `decimalDigits` — the shared decimal-string reference both formatters
   are proven to produce.
3. naive-formatter correctness (`func0` / `func1`).
4. itoa-core correctness (`func13`, via the `DIGIT_TABLE`).
5. harness composition (`func2` / `func4`) ⇒ no-trap.
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

theorem read8_write8_same (m : Mem) (a : UInt32) (v : UInt8) :
    (m.write8 a v).bytes a.toNat = v := by simp

theorem read8_write8_disjoint (m : Mem) (a : UInt32) (v : UInt8) (i : Nat)
    (h : i ≠ a.toNat) : (m.write8 a v).bytes i = m.bytes i := by simp [h]

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

/-- `m` holds the decimal string of `n` in the bytes `[b, b + numDigits n)`. -/
def HasDigitsAt (m : Mem) (b n : Nat) : Prop :=
  ∀ j, j < numDigits n →
    m.bytes (b + j) = UInt8.ofNat (48 + n / 10 ^ (numDigits n - 1 - j) % 10)

set_option maxRecDepth 8000 in
/-- The shared right-to-left digit write loop (used by `func1`/`func0`).
Starting with `local4 = L`, `local6 = local3 = L-1`, `local0 = n`, it writes
`decimalDigits n` into `[outPtr, outPtr+L)` and exits with `local6 = -1`. -/
private theorem write_loop_correct (st : Store Unit) (env : HostEnv Unit)
    (n : UInt64) (outPtr outLen : UInt32) (L : Nat) (v5 : UInt64) (Q : Assertion Unit)
    (hLpos : 1 ≤ L) (hLn : L = numDigits n.toNat)
    (hLout : L ≤ outLen.toNat)
    (hbnd : outPtr.toNat + L ≤ st.mem.pages * 65536)
    (hwrap : outPtr.toNat + L ≤ 4294967296)
    (hexit : ∀ (mem' : Mem) (m5 : UInt64),
        mem'.pages = st.mem.pages →
        (∀ j, j < L → mem'.bytes (outPtr.toNat + j)
            = UInt8.ofNat (48 + n.toNat / 10 ^ (L - 1 - j) % 10)) →
        (∀ a, (a < outPtr.toNat ∨ outPtr.toNat + L ≤ a) → mem'.bytes a = st.mem.bytes a) →
        Q (.Fallthrough { st with mem := mem' }
            ⟨[.i64 0, .i32 outPtr, .i32 outLen, .i32 (UInt32.ofNat (L - 1))],
             [.i32 (UInt32.ofNat L), .i64 m5, .i32 4294967295], []⟩)) :
    wp «module»
      [.loop 0 0 [.localGet 3, .localGet 2, .geU, .br_if 2, .localGet 1, .localGet 6, .add,
        .localGet 0, .localGet 0, .constI64 10, .divUI64, .localSet 5, .localGet 5, .constI64 10,
        .mulI64, .subI64, .wrapI64, .const 48, .or, .store8 0, .localGet 5, .localSet 0,
        .localGet 6, .const 4294967295, .add, .localSet 6, .localGet 6, .const 4294967295, .ne,
        .br_if 0]] Q st
      ⟨[.i64 n, .i32 outPtr, .i32 outLen, .i32 (UInt32.ofNat (L - 1))],
       [.i32 (UInt32.ofNat L), .i64 v5, .i32 (UInt32.ofNat (L - 1))], []⟩ env := by
  have hLsmall : L ≤ 20 := hLn ▸ numDigits_toNat_le n
  apply wp_loop_cons
    (Inv := fun st' s' => ∃ k v5', k < L ∧ st'.mem.pages = st.mem.pages ∧
      st' = { st with mem := st'.mem } ∧
      s'.params = [.i64 (UInt64.ofNat (n.toNat / 10 ^ k)), .i32 outPtr, .i32 outLen,
        .i32 (UInt32.ofNat (L - 1))] ∧
      s'.locals = [.i32 (UInt32.ofNat L), .i64 v5', .i32 (UInt32.ofNat (L - 1 - k))] ∧
      s'.values = [] ∧
      (∀ j, L - k ≤ j → j < L → st'.mem.bytes (outPtr.toNat + j)
          = UInt8.ofNat (48 + n.toNat / 10 ^ (L - 1 - j) % 10)) ∧
      (∀ a, (a < outPtr.toNat ∨ outPtr.toNat + L ≤ a) → st'.mem.bytes a = st.mem.bytes a))
    (μ := fun _ s' => match s'.locals with | [_, _, .i32 m6] => m6.toNat | _ => 0)
  · -- hInit (k = 0)
    refine ⟨0, v5, hLpos, rfl, rfl, ?_, ?_, rfl, ?_, fun a _ => rfl⟩
    · simp [pow_zero, Nat.div_one, UInt64.ofNat_toNat]
    · simp
    · intro j h1 h2; omega
  · -- hStep
    rintro st' s' ⟨k, v5', hk, hpages, hshape, hparams, hlocals, hvals, hdig, hframe⟩
    obtain ⟨p, l, vstk⟩ := s'
    simp only at hparams hlocals hvals
    subst hparams; subst hlocals; subst hvals
    -- toNat facts for the small offsets
    have hsz : UInt32.size = 4294967296 := rfl
    have htoNat_L1 : (UInt32.ofNat (L - 1)).toNat = L - 1 :=
      UInt32.toNat_ofNat_of_lt' (by omega)
    have htoNat_L1k : (UInt32.ofNat (L - 1 - k)).toNat = L - 1 - k :=
      UInt32.toNat_ofNat_of_lt' (by omega)
    -- (1) `geU` bounds-check does not trap: L-1 < outLen
    have htt : ¬ outLen ≤ UInt32.ofNat (L - 1) := by
      intro hle; have := UInt32.le_iff_toNat_le.mp hle
      rw [htoNat_L1] at this; omega
    -- (2) `store8` address in range, no wrap
    have haddr : (L - 1 - k + outPtr.toNat) % 4294967296 = L - 1 - k + outPtr.toNat :=
      Nat.mod_eq_of_lt (by omega)
    have hstore : ¬ st'.mem.pages * 65536 ≤ L - 1 - k + outPtr.toNat := by
      rw [hpages]; omega
    -- digit value written = '0' + (n / 10^k) % 10
    have hMtoNat : (UInt64.ofNat (n.toNat / 10 ^ k)).toNat = n.toNat / 10 ^ k :=
      UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (UInt64.toNat_lt n))
    have hdigval : (UInt8.ofNat ((UInt64.ofNat (n.toNat / 10 ^ k)
          - UInt64.ofNat (n.toNat / 10 ^ k) / 10 * 10).toNat % 4294967296) ||| 48)
        = UInt8.ofNat (48 + n.toNat / 10 ^ k % 10) := by
      rw [show UInt64.ofNat (n.toNat / 10 ^ k) - UInt64.ofNat (n.toNat / 10 ^ k) / 10 * 10
            = UInt64.ofNat (n.toNat / 10 ^ k) % 10 from by bv_decide,
        UInt64.toNat_mod, hMtoNat, show (10 : UInt64).toNat = 10 from rfl,
        Nat.mod_eq_of_lt (show n.toNat / 10 ^ k % 10 < 4294967296 from by
          have := Nat.mod_lt (n.toNat / 10 ^ k) (show 0 < 10 by norm_num); omega)]
      exact digit_byte8 _ (Nat.mod_lt _ (by norm_num))
    simp [wp_simp, htt, hstore, haddr, hdigval]
    -- exit (k = L-1) vs continue (k < L-1)
    have reconcile : ∀ d, d < 10 → (48 : UInt8) + UInt8.ofNat d = UInt8.ofNat (48 + d) := by
      intro d hd; interval_cases d <;> decide
    split
    · -- exit (k = L - 1)
      rename_i x vs heq
      have hz : UInt32.ofNat (L - 1 - k) = 0 := by
        by_contra hne; rw [if_neg hne] at heq; simp at heq
      have hLk0 : L - 1 - k = 0 := by
        have h := congrArg UInt32.toNat hz; rw [htoNat_L1k] at h; simpa using h
      have hk1 : k + 1 = L := by omega
      have hM10nat : n.toNat / 10 ^ k / 10 = 0 := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ, hk1]
        exact Nat.div_eq_of_lt (hLn ▸ lt_ten_pow_numDigits n.toNat)
      have hM10 : UInt64.ofNat (n.toNat / 10 ^ k) / 10 = 0 := by
        apply UInt64.toNat.inj
        rw [UInt64.toNat_div, hMtoNat, show (10 : UInt64).toNat = 10 from rfl, hM10nat]; rfl
      have hg : st'.globals = st.globals := by rw [hshape]
      have hds : st'.dataSegments = st.dataSegments := by rw [hshape]
      have htb : st'.tables = st.tables := by rw [hshape]
      have hes : st'.elementSegments = st.elementSegments := by rw [hshape]
      have hh : st'.host = st.host := by rw [hshape]
      have haddrE : UInt32.ofNat (L - 1 - k) + outPtr = outPtr := by rw [hLk0]; simp
      have hl6 : (4294967295 : UInt32) + UInt32.ofNat (L - 1 - k) = 4294967295 := by
        rw [hLk0]; simp
      rw [hg, hds, htb, hes, hh, hM10, haddrE, hl6]
      apply hexit
      · simp [hpages]
      · intro j hj
        rw [read8_write8_bytes]
        by_cases hj0 : outPtr.toNat + j = outPtr.toNat
        · have hje : j = 0 := by omega
          subst hje
          rw [if_pos hj0]
          simp only [Nat.sub_zero]
          rw [show L - 1 = k from by omega]
          exact reconcile _ (Nat.mod_lt _ (by norm_num))
        · rw [if_neg hj0]
          exact hdig j (by omega) hj
      · intro a ha
        rw [read8_write8_bytes, if_neg (by omega)]
        exact hframe a ha
    · -- continue (k < L - 1)
      rename_i x1 nv vs hnv heq
      have hkLt : k + 1 < L := by
        rcases Nat.lt_or_ge (k + 1) L with h | h
        · exact h
        · exfalso; have hk0 : L - 1 - k = 0 := by omega
          rw [hk0] at heq; simp at heq; exact hnv heq.left.symm
      refine ⟨⟨k + 1, hkLt, hpages,
        ⟨by rw [hshape], by rw [hshape], by rw [hshape], by rw [hshape]⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
      · -- remaining value: M / 10 = ofNat (n / 10^(k+1))
        have hMtoNat1 : (UInt64.ofNat (n.toNat / 10 ^ (k + 1))).toNat = n.toNat / 10 ^ (k + 1) :=
          UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (UInt64.toNat_lt n))
        apply UInt64.toNat.inj
        rw [UInt64.toNat_div, hMtoNat, show (10 : UInt64).toNat = 10 from rfl, hMtoNat1,
          Nat.div_div_eq_div_mul, ← pow_succ]
      · -- next position: 4294967295 + ofNat(L-1-k) = ofNat(L-1-(k+1))
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, htoNat_L1k, show (4294967295 : UInt32).toNat = 4294967295 from rfl,
          UInt32.toNat_ofNat_of_lt' (by omega)]
        omega
      · -- digits
        intro j hj1 hj2
        by_cases hje : outPtr.toNat + j = L - 1 - k + outPtr.toNat
        · rw [if_pos hje]
          have hjk : j = L - 1 - k := by omega
          subst hjk
          rw [show L - 1 - (L - 1 - k) = k from by omega]
        · rw [if_neg hje, hdig j (by omega) hj2]
          exact (reconcile _ (Nat.mod_lt _ (by norm_num))).symm
      · -- framing
        intro a ha
        by_cases hae : a = L - 1 - k + outPtr.toNat
        · exfalso; omega
        · rw [if_neg hae]; exact hframe a ha
      · -- measure decreases
        omega
    · -- unreachable catch-all
      rename_i x vs heq; exact absurd heq (by simp)

theorem func1_spec (env : HostEnv Unit) (st : Store Unit)
    (n : UInt64) (outPtr outLen cap : UInt32)
    (hcap : cap.toNat ≤ 32) (houtLen : cap.toNat ≤ outLen.toNat)
    (hbound : outPtr.toNat + 32 ≤ st.mem.pages * 65536)
    (hwrap : outPtr.toNat + 32 ≤ 4294967296) :
    TerminatesWith env «module» 1 st [.i32 cap, .i32 outLen, .i32 outPtr, .i64 n]
      (fun st' rs =>
        if numDigits n.toNat ≤ cap.toNat then
          rs = [.i32 (UInt32.ofNat (numDigits n.toNat))] ∧
          st'.mem.pages = st.mem.pages ∧
          HasDigitsAt st'.mem outPtr.toNat n.toNat ∧
          (∀ a, ¬(outPtr.toNat ≤ a ∧ a < outPtr.toNat + numDigits n.toNat) →
            st'.mem.bytes a = st.mem.bytes a)
        else
          rs = [.i32 4294967295] ∧ st' = st) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i64, .i32], func1, [.i32]⟩) rfl
  unfold func1
  apply wp_block_cons; apply wp_block_cons; apply wp_block_cons
  apply wp_block_cons; apply wp_block_cons; apply wp_block_cons
  simp only [Function.toLocals, Function.numParams, List.length_cons, List.length_nil,
    List.take, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.map, ValueType.zero]
  simp [wp_simp]
  have hcapsmall : cap.toNat < 2147483648 := by omega
  by_cases h10 : n < 10
  · -- n < 10: single digit, no count loop
    have hn10 : n.toNat < 10 := by
      have := (UInt64.lt_iff_toNat_lt).mp h10; simpa using this
    have hnd : numDigits n.toNat = 1 := numDigits_lt_ten hn10
    simp [wp_simp, h10]
    by_cases hc : cap.toInt32 < 1
    · -- cap < 1 ⇒ cap.toNat = 0 ⇒ branch returns -1, premise `1 ≤ 0` false
      have hc0 : cap.toNat = 0 := by
        have h1 : cap.toInt32.toInt < (1 : Int32).toInt := Int32.lt_iff_toInt_lt.mp hc
        rw [toInt32_toInt_small cap hcapsmall] at h1
        simp only [show (1 : Int32).toInt = 1 from by decide] at h1
        omega
      simp [wp_simp, hc, hnd, hc0]
    · simp [wp_simp, hc]
      have hcap1 : 1 ≤ cap.toNat := by
        by_contra h; push Not at h; apply hc
        have hlt : cap.toInt32.toInt < (1 : Int32).toInt := by
          rw [toInt32_toInt_small cap hcapsmall, show (1 : Int32).toInt = 1 from by decide]
          omega
        exact Int32.lt_iff_toInt_lt.mpr hlt
      apply write_loop_correct (L := 1) (v5 := 0)
      · exact le_refl 1
      · exact hnd.symm
      · omega
      · omega
      · have := UInt32.toNat_lt outPtr; omega
      · intro mem' m5 hp hd hf
        simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
          List.getElem?_cons_succ, List.getElem?_nil, Nat.reduceLT, Nat.reduceAdd,
          Nat.reduceSub, reduceIte]
        rw [hnd, if_pos hcap1]
        refine ⟨rfl, hp, ?_, ?_⟩
        · intro j hj
          rw [hnd] at hj
          have hj0 : j = 0 := by omega
          subst hj0
          rw [hnd]; exact hd 0 (by omega)
        · intro a ha
          apply hf a
          by_cases h : outPtr.toNat ≤ a
          · right; have := ha h; omega
          · left; omega
  · -- n ≥ 10: count digits then write
    simp [wp_simp, h10]
    have hn10 : 10 ≤ n.toNat := by
      by_contra h; push Not at h
      exact h10 (UInt64.lt_iff_toNat_lt.mpr (by simpa using h))
    apply wp_loop_cons
      (Inv := fun st' s' => st' = st ∧ s'.values = [] ∧
        s'.params = [.i64 n, .i32 outPtr, .i32 outLen, .i32 cap] ∧
        ∃ (l4 : UInt32) (l5 : UInt64) (l6 : UInt32), s'.locals = [.i32 l4, .i64 l5, .i32 l6] ∧
          1 ≤ l4.toNat ∧ 10 ≤ l5.toNat ∧
          numDigits n.toNat = (l4.toNat - 1) + numDigits l5.toNat)
      (μ := fun _ s' => match s'.locals with | [_, .i64 l5, _] => l5.toNat | _ => 0)
    · -- hInit
      exact ⟨rfl, rfl, rfl, 1, n, 0, rfl, by simp, hn10, by simp⟩
    · -- hStep
      rintro st' s' ⟨rfl, hvals, hparams, l4, l5, l6, hlocals, hl4, hl5, hrel⟩
      obtain ⟨p, ll, vstk⟩ := s'
      simp only at hparams hlocals hvals
      subst hparams; subst hlocals; subst hvals
      have hnd20 : numDigits n.toNat ≤ 20 := numDigits_toNat_le n
      have hl5pos : 1 ≤ numDigits l5.toNat := numDigits_pos _
      simp [wp_simp]
      split
      · -- exit (l5 < 100): local4 has reached numDigits n
        rename_i x1 vs heq
        have hlt100 : ¬ (100 ≤ l5) := by intro h; rw [if_pos h] at heq; simp at heq
        have hl5lt : l5.toNat < 100 := by
          by_contra h; push Not at h
          exact hlt100 (UInt64.le_iff_toNat_le.mpr (by simpa using h))
        have hnd2 : numDigits l5.toNat = 2 := by
          rw [numDigits_ge_ten (by omega), numDigits_lt_ten (by omega)]
        have hloc4 : 1 + l4.toNat = numDigits n.toNat := by omega
        have hnumpos : 1 ≤ numDigits n.toNat := numDigits_pos _
        have hsz : UInt32.size = 4294967296 := rfl
        have hbnat : (1 + l4 : UInt32).toNat = numDigits n.toNat := by
          rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]; omega
        have hbridge : (1 + l4.toInt32 ≤ cap.toInt32) ↔ (numDigits n.toNat ≤ cap.toNat) := by
          have hadd : (1 : Int32) + l4.toInt32 = (1 + l4).toInt32 := by bv_decide
          rw [hadd, leS_small (1 + l4) cap (by omega) (by omega), hbnat]
        have hl4ne : (1 + l4 : UInt32) ≠ 0 := by
          intro h; have := congrArg UInt32.toNat h
          rw [UInt32.toNat_add] at this
          simp only [show (1 : UInt32).toNat = 1 from rfl, show (0 : UInt32).toNat = 0 from rfl] at this
          omega
        have hl4eq : (1 + l4 : UInt32) = UInt32.ofNat (numDigits n.toNat) := by
          apply UInt32.toNat.inj
          rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl,
            UInt32.toNat_ofNat_of_lt' (by omega)]
          omega
        have hl3eq : (4294967295 : UInt32) + (1 + l4) = UInt32.ofNat (numDigits n.toNat - 1) := by
          apply UInt32.toNat.inj
          rw [UInt32.toNat_add, hl4eq, UInt32.toNat_ofNat_of_lt' (by omega),
            show (4294967295 : UInt32).toNat = 4294967295 from rfl,
            UInt32.toNat_ofNat_of_lt' (by omega)]
          omega
        have hne2 : UInt32.ofNat (numDigits n.toNat) ≠ 0 := hl4eq ▸ hl4ne
        split
        · -- leS false: numDigits > cap, returned -1, premise is vacuous
          rename_i x1 vs heq
          intro hle
          exfalso
          have hnotC : ¬ (1 + l4.toInt32 ≤ cap.toInt32) := by
            intro hC; rw [if_pos hC] at heq; simp at heq
          exact hnotC (hbridge.mpr hle)
        · -- leS true: write the digits via the shared loop
          rename_i x1 nv vs hnv heq
          have hC : 1 + l4.toInt32 ≤ cap.toInt32 := by
            by_contra h; rw [if_neg h] at heq; simp at heq; exact hnv heq.left.symm
          have hfit := hbridge.mp hC
          split
          · -- inner: 1 + l4 = 0 impossible
            rename_i y1 vs2 heq2
            simp only [List.cons.injEq, Value.i32.injEq] at heq2
            exact absurd heq2.1 hl4ne
          · -- inner: write loop
            rename_i y1 ny vs2 hny heq2
            rw [hl3eq, hl4eq]
            apply write_loop_correct (L := numDigits n.toNat) (v5 := l5 / 10)
            · exact hnumpos
            · rfl
            · omega
            · omega
            · omega
            · intro mem' m5 hp hd hf
              simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
                List.getElem?_cons_succ, List.getElem?_nil, Nat.reduceLT, Nat.reduceAdd,
                Nat.reduceSub, reduceIte]
              rw [if_pos hfit]
              refine ⟨trivial, hp, hd, ?_⟩
              intro a ha
              apply hf a
              by_cases h : outPtr.toNat ≤ a
              · right; exact ha h
              · left; omega
          · rename_i heq2; exact absurd heq2 (by simp)
        · -- outer catch-all
          rename_i heq; exact absurd heq (by simp)
      · -- continue (100 ≤ l5)
        rename_i x1 nv vs hnv heq
        have h100 : 100 ≤ l5 := by
          by_contra h; rw [if_neg h] at heq; simp at heq; exact hnv heq.left.symm
        have hl5100 : 100 ≤ l5.toNat := by
          have := UInt64.le_iff_toNat_le.mp h100; simpa using this
        have hl4b : 1 + l4.toNat < 4294967296 := by omega
        have hmod : (1 + l4.toNat) % 4294967296 = 1 + l4.toNat := Nat.mod_eq_of_lt hl4b
        have hdg : numDigits l5.toNat = numDigits (l5.toNat / 10) + 1 := numDigits_ge_ten (by omega)
        rw [hmod]
        exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
      · -- unreachable catch-all
        rename_i heq; exact absurd heq (by simp)

set_option maxRecDepth 8000 in
/-- The magnitude write loop for `func0`'s negative branch: writes the `L`
decimal digits of `mag` into `[outPtr+1, outPtr+1+L)` (offset 0 holds `'-'`),
exiting via `Break 4` (→ `Q (.Break 3)`) once `local6` reaches 1. -/
private theorem neg_write_loop_correct (st : Store Unit) (env : HostEnv Unit)
    (mag : UInt64) (outPtr outLen : UInt32) (L : Nat)
    (l0i : UInt64) (l3i l4v : UInt32) (Q : Assertion Unit)
    (hLpos : 1 ≤ L) (hLn : L = numDigits mag.toNat)
    (hLout : L + 1 ≤ outLen.toNat)
    (hbnd : outPtr.toNat + 1 + L ≤ st.mem.pages * 65536)
    (hwrap : outPtr.toNat + 1 + L ≤ 4294967296)
    (hexit : ∀ (mem' : Mem) (m5 m0 : UInt64) (l3 : UInt32),
        mem'.pages = st.mem.pages →
        (∀ j, j < L → mem'.bytes (outPtr.toNat + 1 + j)
            = UInt8.ofNat (48 + mag.toNat / 10 ^ (L - 1 - j) % 10)) →
        (∀ a, (a < outPtr.toNat + 1 ∨ outPtr.toNat + 1 + L ≤ a) → mem'.bytes a = st.mem.bytes a) →
        Q (.Break 3 { st with mem := mem' }
            ⟨[.i64 m0, .i32 outPtr, .i32 outLen, .i32 l3],
             [.i32 l4v, .i64 m5, .i32 0], []⟩)) :
    wp «module»
      [.loop 0 0 [.localGet 6, .localGet 2, .geU, .br_if 3, .localGet 1, .localGet 6, .add,
        .localGet 5, .localGet 5, .constI64 10, .divUI64, .localSet 0, .localGet 0, .constI64 10,
        .mulI64, .subI64, .wrapI64, .const 48, .or, .store8 0, .localGet 6, .const 1, .gtU,
        .localSet 3, .localGet 6, .const 4294967295, .add, .localSet 6, .localGet 0, .localSet 5,
        .localGet 3, .eqz, .br_if 4, .br 0]] Q st
      ⟨[.i64 l0i, .i32 outPtr, .i32 outLen, .i32 l3i],
       [.i32 l4v, .i64 mag, .i32 (UInt32.ofNat L)], []⟩ env := by
  have hLsmall : L ≤ 20 := hLn ▸ numDigits_toNat_le mag
  apply wp_loop_cons
    (Inv := fun st' s' => ∃ k l0' l3', k < L ∧ st'.mem.pages = st.mem.pages ∧
      st' = { st with mem := st'.mem } ∧
      s'.params = [.i64 l0', .i32 outPtr, .i32 outLen, .i32 l3'] ∧
      s'.locals = [.i32 l4v, .i64 (UInt64.ofNat (mag.toNat / 10 ^ k)),
        .i32 (UInt32.ofNat (L - k))] ∧
      s'.values = [] ∧
      (∀ i, L - k ≤ i → i < L → st'.mem.bytes (outPtr.toNat + 1 + i)
          = UInt8.ofNat (48 + mag.toNat / 10 ^ (L - 1 - i) % 10)) ∧
      (∀ a, (a < outPtr.toNat + 1 ∨ outPtr.toNat + 1 + L ≤ a) → st'.mem.bytes a = st.mem.bytes a))
    (μ := fun _ s' => match s'.locals with | [_, _, .i32 m6] => m6.toNat | _ => 0)
  · -- hInit (k = 0)
    refine ⟨0, l0i, l3i, hLpos, rfl, rfl, rfl, ?_, rfl, ?_, fun a _ => rfl⟩
    · simp [pow_zero, Nat.div_one, UInt64.ofNat_toNat]
    · intro i h1 h2; omega
  · -- hStep
    rintro st' s' ⟨k, l0', l3', hk, hpages, hshape, hparams, hlocals, hvals, hdig, hframe⟩
    obtain ⟨p, l, vstk⟩ := s'
    simp only at hparams hlocals hvals
    subst hparams; subst hlocals; subst hvals
    have hsz : UInt32.size = 4294967296 := rfl
    have htoNatLk : (UInt32.ofNat (L - k)).toNat = L - k := UInt32.toNat_ofNat_of_lt' (by omega)
    have htt : ¬ outLen ≤ UInt32.ofNat (L - k) := by
      intro hle; have := UInt32.le_iff_toNat_le.mp hle; rw [htoNatLk] at this; omega
    have haddr : (L - k + outPtr.toNat) % 4294967296 = L - k + outPtr.toNat :=
      Nat.mod_eq_of_lt (by omega)
    have hstore : ¬ st'.mem.pages * 65536 ≤ L - k + outPtr.toNat := by rw [hpages]; omega
    have hMtoNat : (UInt64.ofNat (mag.toNat / 10 ^ k)).toNat = mag.toNat / 10 ^ k :=
      UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (UInt64.toNat_lt mag))
    have hdigval : (UInt8.ofNat ((UInt64.ofNat (mag.toNat / 10 ^ k)
          - UInt64.ofNat (mag.toNat / 10 ^ k) / 10 * 10).toNat % 4294967296) ||| 48)
        = UInt8.ofNat (48 + mag.toNat / 10 ^ k % 10) := by
      rw [show UInt64.ofNat (mag.toNat / 10 ^ k) - UInt64.ofNat (mag.toNat / 10 ^ k) / 10 * 10
            = UInt64.ofNat (mag.toNat / 10 ^ k) % 10 from by bv_decide,
        UInt64.toNat_mod, hMtoNat, show (10 : UInt64).toNat = 10 from rfl,
        Nat.mod_eq_of_lt (show mag.toNat / 10 ^ k % 10 < 4294967296 from by
          have := Nat.mod_lt (mag.toNat / 10 ^ k) (show 0 < 10 by norm_num); omega)]
      exact digit_byte8 _ (Nat.mod_lt _ (by norm_num))
    have reconcile : ∀ d, d < 10 → (48 : UInt8) + UInt8.ofNat d = UInt8.ofNat (48 + d) := by
      intro d hd; interval_cases d <;> decide
    simp [wp_simp, htt, hstore, haddr, hdigval]
    split
    · -- continue (L - k > 1)
      rename_i x1 vs heq
      have hLk1 : 1 < L - k := by
        by_contra h; push Not at h
        rw [if_pos (UInt32.le_iff_toNat_le.mpr
          (by rw [htoNatLk, show (1 : UInt32).toNat = 1 from rfl]; omega))] at heq
        simp at heq
      have hkLt : k + 1 < L := by omega
      have hM1 : (UInt64.ofNat (mag.toNat / 10 ^ (k + 1))).toNat = mag.toNat / 10 ^ (k + 1) :=
        UInt64.toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (UInt64.toNat_lt mag))
      have he5 : UInt64.ofNat (mag.toNat / 10 ^ k) / 10 = UInt64.ofNat (mag.toNat / 10 ^ (k + 1)) := by
        apply UInt64.toNat.inj
        rw [UInt64.toNat_div, hMtoNat, show (10 : UInt64).toNat = 10 from rfl, hM1,
          Nat.div_div_eq_div_mul, ← pow_succ]
      have he6 : (4294967295 : UInt32) + UInt32.ofNat (L - k) = UInt32.ofNat (L - (k + 1)) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, htoNatLk, show (4294967295 : UInt32).toNat = 4294967295 from rfl,
          UInt32.toNat_ofNat_of_lt' (by omega)]
        omega
      refine ⟨⟨k + 1, hkLt, hpages,
        ⟨by rw [hshape], by rw [hshape], by rw [hshape], by rw [hshape]⟩, ⟨he5, he6⟩, ?_, ?_⟩, ?_⟩
      · -- digits
        intro i hi1 hi2
        by_cases hie : outPtr.toNat + 1 + i = L - k + outPtr.toNat
        · rw [if_pos hie]
          have hik : i = L - k - 1 := by omega
          subst hik
          rw [show L - 1 - (L - k - 1) = k from by omega]
        · rw [if_neg hie, hdig i (by omega) hi2]
          exact (reconcile _ (Nat.mod_lt _ (by norm_num))).symm
      · -- framing
        intro a ha
        by_cases hae : a = L - k + outPtr.toNat
        · exfalso; omega
        · rw [if_neg hae]; exact hframe a (by omega)
      · -- measure
        omega
    · -- exit (L - k = 1, i.e. k = L - 1)
      rename_i x1 nv vs hnv heq
      have hLk1 : L - k = 1 := by
        by_contra h
        rw [if_neg (show ¬ UInt32.ofNat (L - k) ≤ 1 by
          intro hle; have := UInt32.le_iff_toNat_le.mp hle
          rw [htoNatLk, show (1 : UInt32).toNat = 1 from rfl] at this; omega)] at heq
        simp at heq; exact hnv heq.left.symm
      have hvs : vs = [] := by rw [hLk1] at heq; simp at heq; exact heq.2
      subst hvs
      have hk1 : k + 1 = L := by omega
      have ho1 : (outPtr + 1).toNat = outPtr.toNat + 1 := by
        rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hM10nat : mag.toNat / 10 ^ k / 10 = 0 := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ, hk1]
        exact Nat.div_eq_of_lt (hLn ▸ lt_ten_pow_numDigits mag.toNat)
      have hM10 : UInt64.ofNat (mag.toNat / 10 ^ k) / 10 = 0 := by
        apply UInt64.toNat.inj
        rw [UInt64.toNat_div, hMtoNat, show (10 : UInt64).toNat = 10 from rfl, hM10nat]; rfl
      have hg : st'.globals = st.globals := by rw [hshape]
      have hds : st'.dataSegments = st.dataSegments := by rw [hshape]
      have htb : st'.tables = st.tables := by rw [hshape]
      have hes : st'.elementSegments = st.elementSegments := by rw [hshape]
      have hh : st'.host = st.host := by rw [hshape]
      have hl3 : (if 1 < UInt32.ofNat (L - k) then (1 : UInt32) else 0) = 0 := by
        rw [if_neg]; intro hlt; have := UInt32.lt_iff_toNat_lt.mp hlt
        rw [htoNatLk, show (1 : UInt32).toNat = 1 from rfl] at this; omega
      have hl6 : (4294967295 : UInt32) + UInt32.ofNat (L - k) = 0 := by rw [hLk1]; decide
      have haddrE : UInt32.ofNat (L - k) + outPtr = outPtr + 1 := by
        rw [hLk1, show UInt32.ofNat 1 = 1 from rfl]
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
        omega
      rw [hg, hds, htb, hes, hh, hM10, hl3, hl6, haddrE]
      apply hexit
      · simp [hpages]
      · intro j hj
        rw [read8_write8_bytes, ho1]
        by_cases hj0 : outPtr.toNat + 1 + j = outPtr.toNat + 1
        · have hje : j = 0 := by omega
          subst hje
          rw [if_pos hj0]
          simp only [Nat.sub_zero]
          rw [show L - 1 = k from by omega]
          exact reconcile _ (Nat.mod_lt _ (by norm_num))
        · rw [if_neg hj0]
          exact hdig j (by omega) hj
      · intro a ha
        rw [read8_write8_bytes, ho1, if_neg (by omega)]
        exact hframe a ha
    · -- unreachable catch-all
      rename_i heq; exact absurd heq (by simp)

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

theorem func0_spec (env : HostEnv Unit) (st : Store Unit)
    (n : UInt64) (outPtr outLen cap : UInt32)
    (hcap : cap.toNat ≤ 32) (houtLen : cap.toNat ≤ outLen.toNat)
    (hbound : outPtr.toNat + 32 ≤ st.mem.pages * 65536)
    (hwrap : outPtr.toNat + 32 ≤ 4294967296) :
    TerminatesWith env «module» 0 st [.i32 cap, .i32 outLen, .i32 outPtr, .i64 n]
      (fun st' rs =>
        if i64len n ≤ cap.toNat then
          rs = [.i32 (UInt32.ofNat (i64len n))] ∧
          st'.mem.pages = st.mem.pages ∧
          HasDigitsI64 st'.mem outPtr.toNat n ∧
          (∀ a, ¬(outPtr.toNat ≤ a ∧ a < outPtr.toNat + i64len n) →
            st'.mem.bytes a = st.mem.bytes a)
        else
          rs = [.i32 4294967295] ∧ st' = st) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i64, .i32], func0, [.i32]⟩) rfl
  unfold func0
  apply wp_block_cons; apply wp_block_cons; apply wp_block_cons; apply wp_block_cons
  simp only [Function.toLocals, Function.numParams, List.length_cons, List.length_nil,
    List.take, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.map, ValueType.zero]
  simp [wp_simp]
  by_cases hsign : 18446744073709551615 < n.toInt64
  · -- n ≥ 0: delegate to func1
    simp [wp_simp, hsign]
    have hnn : ¬ (9223372036854775808 ≤ n.toNat) := by
      have := (i64_sign_bridge n).mp hsign; omega
    refine wp_call_of_terminates
      (func1_spec env st n outPtr outLen cap hcap houtLen hbound hwrap) ?_
    rintro st' vs hP
    by_cases hfit : numDigits n.toNat ≤ cap.toNat
    · rw [if_pos hfit] at hP
      obtain ⟨hrs, hpg, hdg, hfr⟩ := hP
      subst hrs
      simp [wp_simp, i64len, i64mag, HasDigitsI64, hnn, hfit]
      exact ⟨hpg, hdg, fun a ha => hfr a (fun h => by have := ha h.1; omega)⟩
    · rw [if_neg hfit] at hP
      obtain ⟨hrs, hst⟩ := hP
      subst hrs
      simp [wp_simp, i64len, i64mag, hnn, hfit]
      exact hst
  · -- n < 0: emit '-' then format the magnitude
    have hneg : 9223372036854775808 ≤ n.toNat := by
      by_contra h; push Not at h; exact hsign ((i64_sign_bridge n).mpr h)
    simp [wp_simp, hsign]
    apply wp_block_cons
    simp [wp_simp]
    have hmn : i64mag n = (-n).toNat := by
      have : (9223372036854775808 : ℕ) ≤ n.toNat := hneg
      simp [i64mag, this, zero_sub]
    by_cases hmag : -n < (10 : UInt64)
    · -- magnitude < 10: single digit (i64len n = 2)
      have hmag10 : (-n).toNat < 10 := by have := UInt64.lt_iff_toNat_lt.mp hmag; simpa using this
      have hL1 : numDigits (i64mag n) = 1 := by rw [hmn, numDigits_lt_ten hmag10]
      have hlen : i64len n = 2 := by
        have : (9223372036854775808 : ℕ) ≤ n.toNat := hneg
        simp [i64len, this, hL1]
      simp [wp_simp, hmag]
      have hcapcmp : (cap.toInt32 < 2) ↔ cap.toNat < 2 := by
        rw [Int32.lt_iff_toInt_lt, toInt32_toInt_small cap (by omega),
          show (2 : Int32).toInt = 2 from by decide]
        omega
      split
      · -- cap ≥ 2: store '-' and write the magnitude digit
        rename_i x1 vs heq
        have hcap2 : 2 ≤ cap.toNat := by
          by_contra h; push Not at h
          rw [if_pos (hcapcmp.mpr h)] at heq; simp at heq
        apply wp_block_cons
        apply wp_block_cons
        simp [wp_simp]
        have houtNe : ¬ outLen = 0 := by
          intro h; rw [h] at houtLen; simp at houtLen; omega
        simp [wp_simp, houtNe]
        refine ⟨by omega, ?_⟩
        convert neg_write_loop_correct (mag := -n) (L := 1) (l4v := 2) (env := env) (Q := _)
          (st := { st with mem := st.mem.write8 outPtr 45 })
          (outPtr := outPtr) (outLen := outLen) (l0i := n) (l3i := cap)
          (le_refl 1) (by rw [← hmn, hL1]) (by omega)
          (by simp only [write8_pages]; omega) (by omega) ?_ using 2
        · exact ((List.cons.injEq _ _ _ _).mp heq).2.symm
        · intro mem' m5 m0 l3 hp hd hf
          simp only [wp_simp, hlen]
          simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
            List.getElem?_cons_succ, show ¬ (4 < 4) from by decide, show 4 < 4 + 3 from by decide,
            if_false, if_true, Option.some.injEq, show 4 - (0 + 1 + 1 + 1 + 1) = 0 from rfl]
          rw [if_pos hcap2]
          refine ⟨by decide, hp.trans rfl, ?_, ?_⟩
          · -- HasDigitsI64: '-' at outPtr, magnitude digit at outPtr+1
            rw [HasDigitsI64, if_pos hneg]
            refine ⟨?_, ?_⟩
            · rw [hf outPtr.toNat (Or.inl (by omega))]
              exact read8_write8_same st.mem outPtr 45
            · intro j hj
              rw [hL1] at hj
              rw [hL1, hmn]
              exact hd j hj
          · -- framing outside [outPtr, outPtr+2)
            intro a ha
            rw [hf a (by omega)]
            simp only [read8_write8_bytes]
            rw [if_neg (by omega)]
      · -- cap < 2: i64len > cap, returns -1
        rename_i x1 nv vs hnv heq
        intro hfit
        rw [hlen] at hfit
        exfalso
        have hcaplt : cap.toInt32 < 2 := by
          by_contra h; rw [if_neg h] at heq; simp at heq; exact hnv heq.left.symm
        have := hcapcmp.mp hcaplt
        omega
      · rename_i heq; exact absurd heq (by simp)
    · -- mag ≥ 10: count digits then emit '-' and format the magnitude
      have hmag10' : 10 ≤ (-n).toNat := by
        by_contra h; push Not at h
        exact hmag (UInt64.lt_iff_toNat_lt.mpr (by simpa using h))
      have hilen : i64len n = 1 + numDigits (-n).toNat := by
        simp only [i64len, if_pos hneg]; rw [hmn]; omega
      simp [wp_simp, hmag]
      apply wp_loop_cons
        (Inv := fun st' s' => st' = st ∧ s'.values = [] ∧
          (∃ (l0 : UInt64) (l4 l6 : UInt32),
            s'.params = [.i64 l0, .i32 outPtr, .i32 outLen, .i32 cap] ∧
            s'.locals = [.i32 l4, .i64 (-n), .i32 l6] ∧
            2 ≤ l4.toNat ∧ 10 ≤ l0.toNat ∧
            i64len n = (l4.toNat - 1) + numDigits l0.toNat))
        (μ := fun _ s' => match s'.params with | [.i64 l0, _, _, _] => l0.toNat | _ => 0)
      · -- hInit
        exact ⟨rfl, rfl, -n, 2, 0, rfl, rfl, by simp, hmag10', by rw [hilen]; simp⟩
      · -- hStep
        rintro st' s' ⟨rfl, hvals, l0, l4, l6, hparams, hlocals, hl4, hl0, hrel⟩
        obtain ⟨p, ll, vstk⟩ := s'
        simp only at hparams hlocals hvals
        subst hparams; subst hlocals; subst hvals
        have hnd20 : numDigits (-n).toNat ≤ 20 := numDigits_toNat_le _
        have hl0pos : 1 ≤ numDigits l0.toNat := numDigits_pos _
        simp [wp_simp]
        split
        · -- exit (l0 < 100): l4 + 1 = i64len n; do the cap-check + sign + write
          rename_i x1 vs heq
          have hl0lt100 : l0.toNat < 100 := by
            by_contra h; push Not at h
            rw [if_pos (UInt64.le_iff_toNat_le.mpr (by simpa using h))] at heq; simp at heq
          have hnd2 : numDigits l0.toNat = 2 := by
            rw [numDigits_ge_ten (by omega), numDigits_lt_ten (by omega)]
          have hsz : UInt32.size = 4294967296 := rfl
          have htot : 1 + l4.toNat = i64len n := by omega
          have hilen20 : i64len n ≤ 21 := by rw [hilen]; omega
          have hLpos : 1 ≤ numDigits (-n).toNat := numDigits_pos _
          have hl4tot : (1 + l4 : UInt32).toNat = i64len n := by
            rw [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]; omega
          have hcapcmp : (cap.toInt32 < 1 + l4.toInt32) ↔ cap.toNat < i64len n := by
            rw [show (1 : Int32) + l4.toInt32 = (1 + l4).toInt32 from by bv_decide,
              Int32.lt_iff_toInt_lt, toInt32_toInt_small cap (by omega),
              toInt32_toInt_small (1 + l4) (by rw [hl4tot]; omega), hl4tot]
            omega
          split
          · -- cap ≥ i64len n: store '-' and write the magnitude digits
            rename_i x2 vs2 heq2
            have hfit : i64len n ≤ cap.toNat := by
              by_contra h; push Not at h
              rw [if_pos (hcapcmp.mpr h)] at heq2; simp at heq2
            apply wp_block_cons
            apply wp_block_cons
            simp [wp_simp]
            have houtNe : ¬ outLen = 0 := by
              intro hh; rw [hh] at houtLen; simp at houtLen; omega
            have h2le : (2 : UInt32) ≤ 1 + l4 := by
              rw [UInt32.le_iff_toNat_le, hl4tot, show (2 : UInt32).toNat = 2 from rfl]; omega
            simp [wp_simp, houtNe, h2le]
            refine ⟨by omega, ?_⟩
            convert neg_write_loop_correct (mag := -n) (L := numDigits (-n).toNat) (l4v := 1 + l4)
              (env := env) (Q := _) (st := { st' with mem := st'.mem.write8 outPtr 45 })
              (outPtr := outPtr) (outLen := outLen) (l0i := l0 / 10) (l3i := cap)
              hLpos rfl (by omega) (by simp only [write8_pages]; omega) (by omega) ?_ using 2
            case convert_2 =>
              intro mem' m5 m0 l3 hp hd hf
              simp only [wp_simp]
              simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
                List.getElem?_cons_succ, show ¬ (4 < 4) from by decide, show 4 < 4 + 3 from by decide,
                if_false, if_true, Option.some.injEq, show 4 - (0 + 1 + 1 + 1 + 1) = 0 from rfl]
              rw [if_pos hfit]
              refine ⟨?_, hp.trans rfl, ?_, ?_⟩
              · simp only [Value.i32.injEq]
                apply UInt32.toNat.inj
                rw [hl4tot, UInt32.toNat_ofNat_of_lt' (by omega)]
              · rw [HasDigitsI64, if_pos hneg]
                refine ⟨?_, ?_⟩
                · rw [hf outPtr.toNat (Or.inl (by omega))]
                  exact read8_write8_same st'.mem outPtr 45
                · intro j hj
                  rw [hmn] at hj ⊢
                  exact hd j hj
              · intro a ha
                rw [hf a (by omega)]
                simp only [read8_write8_bytes]
                rw [if_neg (by omega)]
            all_goals first
              | exact ((List.cons.injEq _ _ _ _).mp heq2).2.symm
              | (simp only [List.cons.injEq, Value.i32.injEq, and_true, true_and]
                 apply UInt32.toNat.inj
                 rw [UInt32.toNat_add, UInt32.toNat_add,
                   show (4294967295 : UInt32).toNat = 4294967295 from rfl,
                   show (1 : UInt32).toNat = 1 from rfl, UInt32.toNat_ofNat_of_lt' (by omega)]
                 omega)
          · -- cap < i64len n: returns -1, vacuous
            rename_i x2 nv2 vs2 hnv2 heq2
            intro hfit
            exfalso
            have hclt : cap.toInt32 < 1 + l4.toInt32 := by
              by_contra h; rw [if_neg h] at heq2; simp at heq2; exact hnv2 heq2.left.symm
            have := hcapcmp.mp hclt
            omega
          · rename_i heq2; exact absurd heq2 (by simp)
        · -- continue (100 ≤ l0)
          rename_i x1 nv vs hnv heq
          have h100 : 100 ≤ l0 := by
            by_contra h; rw [if_neg h] at heq; simp at heq; exact hnv heq.left.symm
          have hl0100 : 100 ≤ l0.toNat := by
            have := UInt64.le_iff_toNat_le.mp h100; simpa using this
          have hl4b : 1 + l4.toNat < 4294967296 := by omega
          have hmod : (1 + l4.toNat) % 4294967296 = 1 + l4.toNat := Nat.mod_eq_of_lt hl4b
          have hdg : numDigits l0.toNat = numDigits (l0.toNat / 10) + 1 := numDigits_ge_ten (by omega)
          rw [hmod]
          exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
        · -- unreachable catch-all
          rename_i heq; exact absurd heq (by simp)

end Project.Itoa.Proofs
