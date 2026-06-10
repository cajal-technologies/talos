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
memory-routed code with new indices. The whole naive side is re-proven
below, parametric in the shadow-stack pointer `g` as `HarnessSpec`'s
∀-`g` quantification requires: the u64 core `func6` (`func6_spec`, its
two memory-routed loops factored into standalone `wp` lemmas over an
abstract continuation so the per-iteration proofs stay small), its
wrapper `func5`, the i64 core `func4` (delegating to `func6` for
non-negative inputs, with its own loop lemmas for the negative path),
its wrapper `func3`, the capacity clamp `func7`, and the harness
byte-compare loop (`harness_compare_loop`, shared by `func21` and
`func23`). Re-proving the fast-formatter core (`func40` and its
helpers, behind `func22`/`func24`) — and then discharging the
`HarnessSpec` hypotheses — is the remaining open work.
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

/-- `run` on an operand stack `args ++ rem` (exact-arity `args`, non-import
callee) is `run` on `args` alone with `rem` passed through unchanged. -/
private theorem run_append {α : Type} {env : HostEnv α} {m : Module} {id : Nat}
    {st : Store α} (fuel : Nat) (args rem : List Value) (f : Function)
    (himp : m.imports[id]? = none)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hlen : f.numParams = args.length) :
    run fuel m id st (args ++ rem) env =
      match run fuel m id st args env with
      | .Success vs st' => .Success (vs ++ rem) st'
      | r => r := by
  simp only [run, himp, hf, hlen, List.take_left, List.drop_left, List.take_length,
    List.drop_length]
  cases exec fuel m st (f.toLocals args.reverse) f.body env with
  | Fallthrough st' s' => simp
  | Return st' vs => simp
  | Break k st' s' => cases k <;> simp
  | Invalid msg => simp
  | OutOfFuel => simp
  | Trap st' msg => simp

/-- `wp_call_of_terminates` with a caller-remainder: the operand stack is
`args ++ rem`; the callee consumes exactly `args` and `rem` survives. -/
theorem wp_call_of_terminates_frame {α : Type} {env : HostEnv α} {m : Module}
    {st : Store α} {s : Locals} {Q : Assertion α} {id : Nat} {rest : Program}
    {args rem : List Value} {f : Function}
    {P : Store α → List Value → Prop}
    (hs : s.values = args ++ rem)
    (himp : m.imports[id]? = none)
    (hf : m.funcs[id - m.imports.length]? = some f)
    (hlen : f.numParams = args.length)
    (hterm : TerminatesWith env m id st args P)
    (hPost : ∀ st' vs, P st' vs →
      wp m rest Q st' { s with values := vs ++ rem } env) :
    wp m (.call id :: rest) Q st s env := by
  unfold wp
  unfold TerminatesWith at hterm
  obtain ⟨Ns, hNs⟩ := hterm
  obtain ⟨vs, st', hRun, hPost_vs⟩ := hNs Ns le_rfl
  have hRun_ne : run Ns m id st args env ≠ .OutOfFuel := by
    rw [hRun]; intro h; cases h
  have hwp_rest := hPost st' vs hPost_vs
  unfold wp at hwp_rest
  obtain ⟨Nr, hNr⟩ := hwp_rest
  refine ⟨max (Ns + 1) (Nr + 1), fun fuel hfuel => ?_⟩
  obtain ⟨fl, rfl⟩ : ∃ fl, fuel = fl + 1 := ⟨fuel - 1, by omega⟩
  have hRun_f : run fl m id st args env = .Success vs st' := by
    rw [run_fuel_mono (by omega : fl ≥ Ns) hRun_ne]; exact hRun
  rw [exec_call_cons, hs, run_append fl args rem f himp hf hlen, hRun_f]
  exact hNr (fl + 1) (by omega)

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
private theorem toNat_add_of_lt (a b : UInt32) (h : a.toNat + b.toNat < 4294967296) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]
  exact Nat.mod_eq_of_lt h

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

/-! ## Naive i64 core (`func4`): negative-path loops, standalone

For negative inputs `func4` runs its own count/write loops over the
magnitude `m = 0 - n` (frame `[fp, fp+80)`, count slot `fp+4`, peel
slot `fp+8`, write-value slot `fp+16`, write-index slot `fp+28`). The
total length `L = numDigits m + 1` includes the leading `'-'` written
separately at `out`; the write loop fills positions `[1, L)`. -/

set_option maxHeartbeats 1600000 in
private theorem func4_count_loop (env : HostEnv Unit) (n m : UInt64) (cap : UInt32)
    (B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st1 : Store Unit) (fp out : UInt32)
    (hfp_hi : fp.toNat + 80 ≤ 1048576)
    (hcap : cap.toNat ≤ 32)
    (hpg : st1.mem.pages = 17)
    (hslot4 : st1.mem.read32 (fp + 4) = 1)
    (hslot8 : st1.mem.read64 (fp + 8) = UInt64.ofNat (m.toNat / 10))
    (hpres : ∀ i : Nat, i < fp.toNat ∨ fp.toNat + 80 ≤ i → st1.mem.bytes i = B i)
    (hsucc : ∀ st' : Store Unit,
      st'.mem.pages = 17 →
      st'.globals = st1.globals →
      numDigits m.toNat + 1 ≤ cap.toNat →
      (∀ i : Nat, i < fp.toNat ∨ fp.toNat + 80 ≤ i → st'.mem.bytes i = B i) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 fp, Value.i64 m,
            Value.i32 (UInt32.ofNat (numDigits m.toNat + 1)),
            Value.i32 0, Value.i32 0, Value.i32 0],
          values := [] }))
    (hfail : ∀ st' : Store Unit,
      st'.mem.pages = 17 →
      st'.globals = st1.globals →
      cap.toNat < numDigits m.toNat + 1 →
      (∀ i : Nat, i < fp.toNat ∨ fp.toNat + 80 ≤ i → st'.mem.bytes i = B i) →
      Q (.Break 1 st'
        { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 fp, Value.i64 m,
            Value.i32 (UInt32.ofNat (numDigits m.toNat + 1)),
            Value.i32 0, Value.i32 0, Value.i32 0],
          values := [] })) :
    wp «module»
      (.loop 0 0 [
        .block 0 0 [
          .localGet 4, .load64 (8 : UInt32), .constI64 (0 : UInt64), .gtUI64,
          .const (1 : UInt32), .and, .br_if 0,
          .localGet 4, .load32 (4 : UInt32), .const (1 : UInt32), .add, .localSet 6,
          .localGet 4, .localGet 6, .store32 (68 : UInt32),
          .localGet 6, .localGet 3, .gtS, .const (1 : UInt32), .and, .br_if 3,
          .br 2 ],
        .localGet 4, .localGet 4, .load32 (4 : UInt32), .const (1 : UInt32), .add,
        .store32 (4 : UInt32),
        .localGet 4, .localGet 4, .load64 (8 : UInt32), .constI64 (10 : UInt64),
        .divUI64, .store64 (8 : UInt32),
        .br 0 ] :: rest) Q st1
      { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
        locals := [Value.i32 fp, Value.i64 m, Value.i32 0, Value.i32 0,
          Value.i32 0, Value.i32 0],
        values := [] } env := by
  have t4 : (fp + 4).toNat = fp.toNat + 4 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have t8 : (fp + 8).toNat = fp.toNat + 8 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have t68 : (fp + 68).toNat = fp.toNat + 68 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals = st1.globals ∧
      (∃ c : Nat, 1 ≤ c ∧ c ≤ numDigits m.toNat ∧
        st'.mem.read32 (fp + 4) = UInt32.ofNat c ∧
        st'.mem.read64 (fp + 8) = UInt64.ofNat (m.toNat / 10 ^ c)) ∧
      (∀ i : Nat, i < fp.toNat ∨ fp.toNat + 80 ≤ i → st'.mem.bytes i = B i) ∧
      s' = { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
             locals := [Value.i32 fp, Value.i64 m, Value.i32 0, Value.i32 0,
               Value.i32 0, Value.i32 0],
             values := [] })
    (μ := fun st' _ => (st'.mem.read64 (fp + 8)).toNat)
  · -- entry invariant: `c = 1`
    refine ⟨hpg, rfl, ⟨1, le_rfl, numDigits_pos m.toNat, by simpa using hslot4, ?_⟩,
      hpres, rfl⟩
    rw [pow_one]
    exact hslot8
  · -- step
    rintro st' s' ⟨hpg', hgl', ⟨c, hc1, hcL, hslot4', hslot8'⟩, hpres', rfl⟩
    have g4 : ¬ (1114112 < fp.toNat + 4 + 4) := by omega
    have g8 : ¬ (1114112 < fp.toNat + 8 + 8) := by omega
    have g68 : ¬ (1114112 < fp.toNat + 68 + 4) := by omega
    have q4 : fp.toNat ≤ 1114104 := by omega
    have q8 : fp.toNat ≤ 1114096 := by omega
    have q68 : fp.toNat ≤ 1114040 := by omega
    apply wp_block_cons
    wp_run
    simp [hpg', hslot4', hslot8', g4, g8, g68]
    have hvsz : m.toNat / 10 ^ c < 18446744073709551616 := by
      have h1 : m.toNat / 10 ^ c ≤ m.toNat := Nat.div_le_self _ _
      have h2 := UInt64.toNat_lt_size m
      simp [UInt64.size] at h2
      omega
    have hofv : (UInt64.ofNat (m.toNat / 10 ^ c)).toNat = m.toNat / 10 ^ c :=
      UInt64.toNat_ofNat_of_lt' hvsz
    by_cases hv : m.toNat / 10 ^ c = 0
    · -- count loop exits: `v = 0`, so `c` is exactly the digit count
      have hvz : UInt64.ofNat (m.toNat / 10 ^ c) = 0 := by
        apply UInt64.toNat.inj; rw [hofv, hv]; rfl
      simp [hvz]
      have hL : c = numDigits m.toNat := by
        have h10 : m.toNat < 10 ^ c := by
          by_contra hge
          have hb : 0 < 10 ^ c := Nat.pow_pos (by norm_num)
          have : 0 < m.toNat / 10 ^ c := Nat.div_pos (by omega) hb
          omega
        rcases Nat.eq_zero_or_pos m.toNat with h0 | h1
        · have : numDigits m.toNat = 1 := by rw [h0]; exact numDigits_lt_ten (by norm_num)
          omega
        · have hlow := ten_pow_numDigits_le m.toNat h1
          have hlt : 10 ^ (numDigits m.toNat - 1) < 10 ^ c := lt_of_le_of_lt hlow h10
          have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hlt
          omega
      have hc20 : c ≤ 20 := hL ▸ numDigits_toNat_le m
      have hadd1 : (1 : UInt32) + UInt32.ofNat c = UInt32.ofNat (c + 1) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega),
          UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp
        omega
      have hofc1 : (UInt32.ofNat (c + 1)).toNat = c + 1 := by
        rw [UInt32.toNat_ofNat_of_lt']
        simp [UInt32.size]; omega
      have hcmpI : (cap.toInt32 < 1 + Int32.ofNat c) ↔ cap.toNat < c + 1 := by
        rw [show (1 : Int32) + Int32.ofNat c = (UInt32.ofNat (c + 1)).toInt32 from by
              rw [← hadd1]; rfl,
            ltS_small cap (UInt32.ofNat (c + 1)) (by omega) (by rw [hofc1]; omega), hofc1]
      by_cases hgt : cap.toNat < c + 1
      · -- total length exceeds `cap`: `br_if 3` fires
        simp [hcmpI, hgt]
        rw [hadd1, hL]
        apply hfail _ (by simp [hpg']) (by simpa using hgl') (by omega)
        intro i hi
        rw [write32_bytes_of_disjoint _ _ _ _ (by omega)]
        exact hpres' i hi
      · -- fits: `br 2`
        simp [hcmpI, hgt]
        rw [hadd1, hL]
        apply hsucc _ (by simp [hpg']) (by simpa using hgl') (by omega)
        intro i hi
        rw [write32_bytes_of_disjoint _ _ _ _ (by omega)]
        exact hpres' i hi
    · -- count loop continues
      have hpos : (0 : UInt64) < UInt64.ofNat (m.toNat / 10 ^ c) := by
        rw [UInt64.lt_iff_toNat_lt, hofv]
        exact Nat.pos_of_ne_zero hv
      simp [hpos]
      have h10c : 10 ^ c ≤ m.toNat := by
        by_contra hlt
        exact hv (Nat.div_eq_of_lt (by omega))
      have hclt : c < numDigits m.toNat := by
        have hup := lt_ten_pow_numDigits m.toNat
        have : 10 ^ c < 10 ^ numDigits m.toNat := by omega
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp this
      refine ⟨⟨hgl', ⟨c + 1, by omega, by omega, ?_, ?_⟩, ?_⟩, ?_⟩
      · rw [read32_write64_disjoint _ _ _ _ (by omega), read32_write32_same']
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt', UInt32.toNat_ofNat_of_lt']
        · simp
          have := numDigits_toNat_le m
          omega
        · have := numDigits_toNat_le m
          simp [UInt32.size]; omega
        · have := numDigits_toNat_le m
          simp [UInt32.size]; omega
      · rw [read64_write32_disjoint _ _ _ _ (by omega), hslot8']
        apply UInt64.toNat.inj
        rw [UInt64.toNat_div, hofv, UInt64.toNat_ofNat_of_lt' (by
          have h1 : m.toNat / 10 ^ (c + 1) ≤ m.toNat / 10 ^ c := by
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
      · rw [read64_write32_disjoint _ _ _ _ (by omega), hslot8', hofv,
          Nat.mod_eq_of_lt hvsz]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hv) (by norm_num)

set_option maxHeartbeats 1600000 in
private theorem func4_write_loop (env : HostEnv Unit) (n m : UInt64) (cap : UInt32)
    (L : Nat) (B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st2 : Store Unit) (fp out : UInt32)
    (hfp_hi : fp.toNat + 80 ≤ out.toNat)
    (hout_hi : out.toNat + 32 ≤ 1048576)
    (_hcap : cap.toNat ≤ 32) (_hcle : L ≤ cap.toNat) (hL1 : 1 ≤ L) (hL21 : L ≤ 21)
    (hpg2 : st2.mem.pages = 17)
    (hidx : st2.mem.read32 (fp + 28) = UInt32.ofNat L)
    (hval : st2.mem.read64 (fp + 16) = m)
    (hpres : ∀ j : Nat, j < fp.toNat ∨ (fp.toNat + 80 ≤ j ∧ j < out.toNat + 1) ∨
        out.toNat + 32 ≤ j →
      st2.mem.bytes j = B j)
    (hexit : ∀ (st' : Store Unit) (w7 w8 : Value),
      st'.mem.pages = 17 →
      st'.globals = st2.globals →
      st'.mem.read32 fp = UInt32.ofNat L →
      (∀ p : Nat, 1 ≤ p → p < L →
        st'.mem.bytes (out.toNat + p) = UInt8.ofNat (48 + m.toNat / 10 ^ (L - 1 - p) % 10)) →
      (∀ j : Nat, j < fp.toNat ∨ (fp.toNat + 80 ≤ j ∧ j < out.toNat + 1) ∨
          out.toNat + 32 ≤ j →
        st'.mem.bytes j = B j) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 fp, Value.i64 m, Value.i32 (UInt32.ofNat L), w7, w8,
            Value.i32 0],
          values := [] })) :
    wp «module»
      (.loop 0 0 [
        .block 0 0 [
          .localGet 4, .load32 (28 : UInt32), .const (1 : UInt32), .gtU,
          .const (1 : UInt32), .and, .br_if 0,
          .localGet 4, .localGet 6, .store32 (0 : UInt32),
          .br 2 ],
        .localGet 4, .localGet 4, .load32 (28 : UInt32), .const (1 : UInt32), .sub,
        .store32 (28 : UInt32),
        .localGet 4, .load64 (16 : UInt32), .constI64 (10 : UInt64), .remUI64, .wrapI64,
        .localSet 7,
        .localGet 4, .load32 (28 : UInt32), .localSet 8,
        .block 0 0 [
          .localGet 8, .localGet 2, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
          .localGet 1, .localGet 8, .add, .localGet 7, .const (48 : UInt32), .add,
          .store8 (0 : UInt32),
          .localGet 4, .localGet 4, .load64 (16 : UInt32), .constI64 (10 : UInt64),
          .divUI64, .store64 (16 : UInt32),
          .br 1 ]
      ] :: rest) Q st2
      { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
        locals := [Value.i32 fp, Value.i64 m, Value.i32 (UInt32.ofNat L), Value.i32 0,
          Value.i32 0, Value.i32 0],
        values := [] } env := by
  have t16 : (fp + 16).toNat = fp.toNat + 16 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have t28 : (fp + 28).toNat = fp.toNat + 28 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals = st2.globals ∧
      (∃ i : Nat, 1 ≤ i ∧ i ≤ L ∧
        st'.mem.read32 (fp + 28) = UInt32.ofNat i ∧
        st'.mem.read64 (fp + 16) = UInt64.ofNat (m.toNat / 10 ^ (L - i)) ∧
        (∀ p : Nat, i ≤ p → p < L → st'.mem.bytes (out.toNat + p) =
            UInt8.ofNat (48 + m.toNat / 10 ^ (L - 1 - p) % 10)) ∧
        (∀ j : Nat, j < fp.toNat ∨ (fp.toNat + 80 ≤ j ∧ j < out.toNat + 1) ∨
            out.toNat + 32 ≤ j →
            st'.mem.bytes j = B j)) ∧
      (∃ w7 w8 : Value,
        s' = { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
               locals := [Value.i32 fp, Value.i64 m, Value.i32 (UInt32.ofNat L), w7, w8,
                 Value.i32 0],
               values := [] }))
    (μ := fun st' _ => (st'.mem.read32 (fp + 28)).toNat)
  · -- entry invariant: `i = L`, value slot holds `m`
    refine ⟨hpg2, rfl, ⟨L, hL1, le_rfl, hidx, ?_, fun p hp1 hp2 => absurd hp1 (by omega),
      hpres⟩, Value.i32 0, Value.i32 0, rfl⟩
    rw [Nat.sub_self, pow_zero, Nat.div_one, UInt64.ofNat_toNat]
    exact hval
  · -- step
    rintro st3 s3 ⟨hpg3, hgl3, ⟨i, hi1, hiL, hidx3, hval3, hdig3, hpres3⟩, w7, w8, rfl⟩
    have g0 : ¬ (1114112 < fp.toNat + 4) := by omega
    have g16 : ¬ (1114112 < fp.toNat + 16 + 8) := by omega
    have g28 : ¬ (1114112 < fp.toNat + 28 + 4) := by omega
    have q0 : fp.toNat ≤ 1114108 := by omega
    have q16 : fp.toNat ≤ 1114088 := by omega
    have q28 : fp.toNat ≤ 1114080 := by omega
    apply wp_block_cons
    wp_run
    simp [hpg3, hidx3, g0, g16, g28]
    have hofi : (UInt32.ofNat i).toNat = i := by
      rw [UInt32.toNat_ofNat_of_lt']
      simp [UInt32.size]; omega
    by_cases hi0 : i = 1
    · -- exit: store the total length into the result slot, `br 2`
      have hz : UInt32.ofNat i = 1 := by rw [hi0]; rfl
      simp [hz]
      apply hexit
      · simp [hpg3]
      · simpa using hgl3
      · rw [read32_write32_same']
      · intro p hp1 hp
        rw [read32_write32_bytes, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
        exact hdig3 p (by omega) hp
      · intro j hj
        rw [read32_write32_bytes, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
        exact hpres3 j hj
    · -- one more digit to write
      have hpos2 : (1 : UInt32) < UInt32.ofNat i := by
        rw [UInt32.lt_iff_toNat_lt, hofi]
        simp; omega
      simp [hpos2]
      apply wp_block_cons
      wp_run
      have him1 : UInt32.ofNat i - 1 = UInt32.ofNat (i - 1) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_sub_of_le _ _ (by
          rw [UInt32.le_iff_toNat_le]
          simpa [hofi] using (by omega : 1 ≤ i)), hofi]
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
      have hd64 : m.toNat / 10 ^ (L - i) < 18446744073709551616 := by
        have h1 : m.toNat / 10 ^ (L - i) ≤ m.toNat := Nat.div_le_self _ _
        have h2 := UInt64.toNat_lt_size m
        simp [UInt64.size] at h2
        omega
      have hd : m.toNat / 10 ^ (L - i) % 18446744073709551616 % 10 % 4294967296 =
          m.toNat / 10 ^ (L - i) % 10 := by
        rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt (by omega)]
      have hrv : (st3.mem.write32 (fp + 28) (UInt32.ofNat (i - 1))).read64 (fp + 16) =
          UInt64.ofNat (m.toNat / 10 ^ (L - i)) := by
        rw [read64_write32_disjoint _ _ _ _ (by omega)]
        exact hval3
      simp [him1, hguard, hrv, hd, haddr, hpg3, hnb, g16]
      -- `hd`'s nested-mod shape makes every later `omega` pathologically
      -- slow (minutes each); drop it now that the simp consumed it.
      clear hd
      refine ⟨⟨hgl3, ⟨i - 1, by omega, by omega, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
      · rw [read32_write64_disjoint _ _ _ _ (by omega),
          read32_write8_disjoint _ _ _ _ (by omega), read32_write32_same']
      · rw [read64_write8_disjoint _ _ _ _ (by omega),
          read64_write32_disjoint _ _ _ _ (by omega), hval3]
        apply UInt64.toNat.inj
        have hsz : UInt64.size = 18446744073709551616 := rfl
        rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' (by omega),
          UInt64.toNat_ofNat_of_lt' (by
            have h1 : m.toNat / 10 ^ (L - (i - 1)) ≤ m.toNat / 10 ^ (L - i) := by
              rw [show L - (i - 1) = (L - i) + 1 from by omega, pow_succ,
                ← Nat.div_div_eq_div_mul]
              exact Nat.div_le_self _ _
            omega)]
        rw [show L - (i - 1) = (L - i) + 1 from by omega, pow_succ,
          ← Nat.div_div_eq_div_mul]
        rfl
      · intro p hp1 hp2
        rw [write64_bytes_of_disjoint _ _ _ _ (by omega)]
        by_cases hpe : p = i - 1
        · subst hpe
          rw [read8_write8_bytes, if_pos (by omega),
            show L - 1 - (i - 1) = L - i from by omega]
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

set_option maxRecDepth 10000 in
/-- `n` (as i64) is non-negative iff its `toNat` is below `2^63` (`≤`-form). -/
private theorem i64_nonneg_bridge (n : UInt64) :
    ((0 : Int64) ≤ n.toInt64) ↔ (n.toNat < 9223372036854775808) := by
  rw [Int64.le_iff_toInt_le, show ((0 : Int64)).toInt = 0 from by decide,
    show n.toInt64.toInt = n.toInt64.toBitVec.toInt from rfl, BitVec.toInt_eq_toNat_bmod,
    show n.toInt64.toBitVec.toNat = n.toNat from rfl, Int.bmod]
  have hb : n.toNat < 18446744073709551616 := by
    have := UInt64.toNat_lt n; simpa [UInt64.size] using this
  norm_num; omega

set_option maxHeartbeats 16000000 in
/-- `func4`: the naive i64 formatter core. For non-negative `n` it delegates
to `func6`; for negative `n` it writes `'-'` and formats the magnitude with
its own loops. -/
theorem func4_spec (env : HostEnv Unit) (st0 : Store Unit) (g out : UInt32)
    (n : UInt64) (cap : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg144 : 144 ≤ g.toNat) (hgout : g.toNat ≤ out.toNat)
    (hout : out.toNat + 32 ≤ 1048576)
    (hcap : cap.toNat ≤ 32) :
    TerminatesWith env «module» 4 st0 [.i32 cap, .i32 32, .i32 out, .i64 n]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 (if i64len n ≤ cap.toNat
                    then UInt32.ofNat (i64len n) else 4294967295)] ∧
        (i64len n ≤ cap.toNat → HasDigitsI64 st'.mem out.toNat n) ∧
        (∀ i : Nat, i < g.toNat - 144 ∨ (g.toNat ≤ i ∧ i < out.toNat) ∨
            out.toNat + 32 ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hfp : (g - 80).toNat = g.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le g 80 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t4 : (g - 80 + 4).toNat = g.toNat - 80 + 4 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t8 : (g - 80 + 8).toNat = g.toNat - 80 + 8 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t16 : (g - 80 + 16).toNat = g.toNat - 80 + 16 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t28 : (g - 80 + 28).toNat = g.toNat - 80 + 28 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t32 : (g - 80 + 32).toNat = g.toNat - 80 + 32 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t44 : (g - 80 + 44).toNat = g.toNat - 80 + 44 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t48 : (g - 80 + 48).toNat = g.toNat - 80 + 48 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t52 : (g - 80 + 52).toNat = g.toNat - 80 + 52 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t56 : (g - 80 + 56).toNat = g.toNat - 80 + 56 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t68 : (g - 80 + 68).toNat = g.toNat - 80 + 68 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t72 : (g - 80 + 72).toNat = g.toNat - 80 + 72 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have hback : 80 + (g - 80) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hfp]; simp; omega
  have p0 : ¬ (1114112 < g.toNat - 80 + 4) := by omega
  have p4 : ¬ (1114112 < g.toNat - 80 + 4 + 4) := by omega
  have p8 : ¬ (1114112 < g.toNat - 80 + 8 + 8) := by omega
  have p16 : ¬ (1114112 < g.toNat - 80 + 16 + 8) := by omega
  have p28 : ¬ (1114112 < g.toNat - 80 + 28 + 4) := by omega
  have p32 : ¬ (1114112 < g.toNat - 80 + 32 + 8) := by omega
  have p44 : ¬ (1114112 < g.toNat - 80 + 44 + 4) := by omega
  have p48 : ¬ (1114112 < g.toNat - 80 + 48 + 4) := by omega
  have p52 : ¬ (1114112 < g.toNat - 80 + 52 + 4) := by omega
  have p56 : ¬ (1114112 < g.toNat - 80 + 56 + 8) := by omega
  have p72 : ¬ (1114112 < g.toNat - 80 + 72 + 8) := by omega
  have q0 : g.toNat - 80 ≤ 1114108 := by omega
  have q4 : g.toNat - 80 ≤ 1114104 := by omega
  have q8 : g.toNat - 80 ≤ 1114096 := by omega
  have q16 : g.toNat - 80 ≤ 1114088 := by omega
  have q28 : g.toNat - 80 ≤ 1114080 := by omega
  have q32 : g.toNat - 80 ≤ 1114072 := by omega
  have q44 : g.toNat - 80 ≤ 1114064 := by omega
  have q48 : g.toNat - 80 ≤ 1114060 := by omega
  have q52 : g.toNat - 80 ≤ 1114056 := by omega
  have q56 : g.toNat - 80 ≤ 1114048 := by omega
  have q72 : g.toNat - 80 ≤ 1114032 := by omega
  have hob : ¬ (1114112 ≤ out.toNat) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i64, .i32, .i32, .i32, .i32], func4,
      [.i32]⟩) rfl
  unfold func4
  wp_run
  simp [hg, hpg, hfp, p32, p44, p48, p52]
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  by_cases hsgn : (0 : Int64) ≤ n.toInt64
  · -- non-negative: delegate to `func6`
    have hneg : n.toNat < 9223372036854775808 := (i64_nonneg_bridge n).mp hsgn
    simp [hsgn]
    have hmag : i64mag n = n.toNat := by
      unfold i64mag; rw [if_neg (by omega)]
    have hlen : i64len n = numDigits n.toNat := by
      unfold i64len; rw [hmag, if_neg (by omega)]; omega
    apply wp_call_of_terminates_frame
      (args := [.i32 cap, .i32 32, .i32 out, .i64 n]) (rem := [.i32 (g - 80)])
      (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i32, .i32, .i32], func6, [.i32]⟩)
      rfl rfl rfl rfl
      (func6_spec env _ (g - 80) out n cap
        (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
        (by omega) (by omega) hout hcap)
    rintro st' vs ⟨hpg', hg', hrs, hdig, hpres⟩
    obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
    subst hrs
    wp_run
    simp [hpg', hg', hback, hfp, p0, q0, List.getElem?_set_self hglen']
    refine ⟨?_, ?_, ?_⟩
    · rw [hlen]
    · rw [hlen]
      intro hfits
      rw [HasDigitsI64, if_neg (by omega), hmag]
      intro j hj
      rw [write32_bytes_of_disjoint _ _ _ _ (by omega)]
      exact hdig hfits j hj
    · intro i hi
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hstep := hpres i (by omega)
      rw [hstep]
      rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega)]
  · -- negative: write `'-'` then format the magnitude
    have hneg : ¬ n.toNat < 9223372036854775808 :=
      fun h => hsgn ((i64_nonneg_bridge n).mpr h)
    simp [hsgn, p4, p8, p56, p72, hpg, hfp]
    have hmag : i64mag n = (0 - n).toNat := by
      unfold i64mag; rw [if_pos (by omega)]
    have hlen : i64len n = numDigits (0 - n).toNat + 1 := by
      unfold i64len; rw [hmag, if_pos (by omega)]
    apply wp_block_cons
    apply wp_block_cons
    apply wp_block_cons
    apply wp_block_cons
    apply wp_block_cons
    apply func4_count_loop env n (0 - n) cap st0.mem.bytes _ (g - 80) out
      (by omega) hcap
    · -- pages after prologue + negative setup
      simp [hpg]
    · -- count slot = 1
      rw [read32_write64_disjoint _ _ _ _ (by omega), read32_write32_same']
    · -- peel slot = m / 10
      rw [read64_write64_same]
      apply UInt64.toNat.inj
      rw [UInt64.toNat_ofNat_of_lt']
      · exact UInt64.toNat_div (0 - n) 10
      · have := UInt64.toNat_lt_size (0 - n)
        have : (0 - n).toNat / 10 ≤ (0 - n).toNat := Nat.div_le_self _ _
        omega
    · -- bytes outside the frame untouched by prologue + setup
      intro i hi
      rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega)]
    · -- fits: `'-'`, slots for the write loop, the write loop, epilogue
      intro st' hpg' hgl' hfits hpres'
      simp only []
      wp_run
      simp [hpg', hob, hfp, p16, p28]
      have hmod : (UInt64.size - n.toNat) % UInt64.size = (0 - n).toNat := by simp
      have hsplit : UInt32.ofNat (numDigits (0 - n).toNat) + 1 =
          UInt32.ofNat (numDigits (0 - n).toNat + 1) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add,
          UInt32.toNat_ofNat_of_lt' (by
            have := numDigits_toNat_le (0 - n)
            rw [show UInt32.size = 4294967296 from rfl]; omega),
          UInt32.toNat_ofNat_of_lt' (by
            have := numDigits_toNat_le (0 - n)
            rw [show UInt32.size = 4294967296 from rfl]; omega),
          show (1 : UInt32).toNat = 1 from rfl]
        rw [Nat.mod_eq_of_lt (by
          have := numDigits_toNat_le (0 - n)
          omega)]
      rw [show (-n : UInt64) = 0 - n from by bv_decide, hmod, hsplit]
      apply func4_write_loop env n (0 - n) cap (numDigits (0 - n).toNat + 1)
        (fun j => if j = out.toNat then 45 else st0.mem.bytes j) _ (g - 80) out
        (by omega) hout hcap hfits (by omega)
        (by have := numDigits_toNat_le (0 - n); omega)
      · simp [hpg']
      · -- index slot = L
        rw [read32_write32_same']
      · -- value slot = m
        rw [read64_write32_disjoint _ _ _ _ (by omega), read64_write64_same]
      · -- preservation through `'-'` and the two slot stores
        intro j hj
        rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
            write64_bytes_of_disjoint _ _ _ _ (by omega)]
        by_cases hje : j = out.toNat
        · subst hje
          rw [read8_write8_bytes, if_pos (by omega), if_pos rfl]
        · rw [read8_write8_bytes, if_neg (by omega), if_neg hje]
          exact hpres' j (by omega)
      · -- write-loop exit: epilogue
        intro st2 w7 w8 hpg2 hgl2 hres hdig hpres2
        simp only []
        wp_run
        simp [hpg2, hres, hgl2, hgl', hback, hfp, q0,
          List.getElem?_set_self (by simpa using hglen)]
        refine ⟨?_, ?_, ?_⟩
        · rw [hlen, hmod, hsplit, if_pos (by omega)]
        · rw [hlen]
          intro _
          rw [HasDigitsI64, if_pos (by omega), hmag]
          constructor
          · have h45 := hpres2 out.toNat (by omega)
            rw [if_pos rfl] at h45
            exact h45
          · intro j hjd
            have := hdig (j + 1) (by omega) (by omega)
            rw [show numDigits (0 - n).toNat + 1 - 1 - (j + 1) =
              numDigits (0 - n).toNat - 1 - j from by omega] at this
            rw [show out.toNat + 1 + j = out.toNat + (j + 1) from by omega]
            exact this
        · intro i hi
          have hstep := hpres2 i (by omega)
          rw [hstep, if_neg (by omega)]
    · -- capacity exceeded: store `-1`, epilogue
      intro st' hpg' hgl' hover hpres'
      simp only []
      wp_run
      simp [hpg', hgl', hback, hfp, p0, q0,
        List.getElem?_set_self (by simpa using hglen)]
      refine ⟨fun h => absurd h (by rw [hlen] at h; omega),
        fun h => absurd h (by rw [hlen] at h; omega), ?_⟩
      intro i hi
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hpres' i (by omega)

/-! ## `func3_spec`: the naive i64 wrapper

A 32-byte shadow-stack wrapper: spill `(n, out, outLen, cap)` into a
fresh frame, forward to `func4`, restore the stack pointer. -/

set_option maxHeartbeats 1600000 in
theorem func3_spec (env : HostEnv Unit) (st0 : Store Unit) (g out : UInt32)
    (n : UInt64) (cap : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg176 : 176 ≤ g.toNat) (hgout : g.toNat ≤ out.toNat)
    (hout : out.toNat + 32 ≤ 1048576)
    (hcap : cap.toNat ≤ 32) :
    TerminatesWith env «module» 3 st0 [.i32 cap, .i32 32, .i32 out, .i64 n]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 (if i64len n ≤ cap.toNat
                    then UInt32.ofNat (i64len n) else 4294967295)] ∧
        (i64len n ≤ cap.toNat → HasDigitsI64 st'.mem out.toNat n) ∧
        (∀ i : Nat, i < g.toNat - 176 ∨ (g.toNat ≤ i ∧ i < out.toNat) ∨
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
    (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i32], func3, [.i32]⟩) rfl
  unfold func3
  wp_run
  simp [hg, hpg, hsub, p8, p20, p24, p28]
  apply wp_call_of_terminates (func4_spec env _ (g - 32) out n cap
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

/-! ## The harness byte-compare loop, standalone

The tail of `func21`/`func23` (textually identical in both): walk the
index slot `fp+68` over `[0, len)`, comparing the fast buffer at
`[fp, fp+32)` against the naive buffer at `[fp+32, fp+64)` byte by
byte, trapping (`call 17`) on any disagreement. Under the hypothesis
that both buffers hold the same bytes `D` on `[0, len)`, the loop
always exits cleanly via `br_if 1` (`.Break 0` at the loop level),
touching only the index slot. -/

set_option maxHeartbeats 1600000 in
theorem harness_compare_loop (env : HostEnv Unit) (n : UInt64) (cap : UInt32)
    (lenv : UInt32) (D B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st1 : Store Unit) (fp : UInt32)
    (w3 w4 w5 w7 w8 w9 w10 w11 : Value)
    (hfp_hi : fp.toNat + 96 ≤ 1048576)
    (hL : lenv.toNat ≤ 32)
    (hpg : st1.mem.pages = 17)
    (hidx : st1.mem.read32 (fp + 68) = 0)
    (hpres : ∀ j : Nat, j < fp.toNat + 68 ∨ fp.toNat + 72 ≤ j →
      st1.mem.bytes j = B j)
    (hfast : ∀ j : Nat, j < lenv.toNat → B (fp.toNat + j) = D j)
    (hnaive : ∀ j : Nat, j < lenv.toNat → B (fp.toNat + 32 + j) = D j)
    (hexit : ∀ (st' : Store Unit) (w8' w9' w10' w11' : Value),
      st'.mem.pages = 17 →
      st'.globals = st1.globals →
      (∀ j : Nat, j < fp.toNat + 68 ∨ fp.toNat + 72 ≤ j →
        st'.mem.bytes j = B j) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 cap],
          locals := [Value.i32 fp, w3, w4, w5, Value.i32 lenv, w7,
            w8', w9', w10', w11'],
          values := [] })) :
    wp «module»
      (.loop 0 0 [
        .localGet 2, .load32 (68 : UInt32), .localGet 6, .ltU,
        .const (1 : UInt32), .and, .eqz, .br_if 1,
        .localGet 2, .load32 (68 : UInt32), .localSet 8,
        .block 0 0 [
          .block 0 0 [
            .block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .localGet 8, .const (32 : UInt32), .ltU, .const (1 : UInt32),
                  .and, .eqz, .br_if 0,
                  .localGet 2, .localGet 8, .add, .load8U (0 : UInt32), .localSet 9,
                  .localGet 2, .load32 (68 : UInt32), .localSet 10,
                  .localGet 10, .const (32 : UInt32), .ltU, .const (1 : UInt32),
                  .and, .br_if 1,
                  .br 2 ],
                .localGet 8, .const (32 : UInt32), .const (1049048 : UInt32),
                .call 102, .unreachable ],
              .localGet 2, .const (32 : UInt32), .add, .localGet 10, .add,
              .load8U (0 : UInt32), .localSet 11,
              .localGet 9, .const (255 : UInt32), .and, .localGet 11,
              .const (255 : UInt32), .and, .ne, .const (1 : UInt32), .and,
              .br_if 2, .br 1 ],
            .localGet 10, .const (32 : UInt32), .const (1049064 : UInt32),
            .call 102, .unreachable ],
          .localGet 2, .localGet 2, .load32 (68 : UInt32), .const (1 : UInt32),
          .add, .store32 (68 : UInt32), .br 1 ]
      ] :: rest) Q st1
      { params := [Value.i64 n, Value.i32 cap],
        locals := [Value.i32 fp, w3, w4, w5, Value.i32 lenv, w7, w8, w9, w10, w11],
        values := [] } env := by
  have t68 : (fp + 68).toNat = fp.toNat + 68 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals = st1.globals ∧
      (∃ k : Nat, k ≤ lenv.toNat ∧
        st'.mem.read32 (fp + 68) = UInt32.ofNat k ∧
        (∀ j : Nat, j < fp.toNat + 68 ∨ fp.toNat + 72 ≤ j →
          st'.mem.bytes j = B j)) ∧
      (∃ v8 v9 v10 v11 : Value,
        s' = { params := [Value.i64 n, Value.i32 cap],
               locals := [Value.i32 fp, w3, w4, w5, Value.i32 lenv, w7,
                 v8, v9, v10, v11],
               values := [] }))
    (μ := fun st' _ => lenv.toNat - (st'.mem.read32 (fp + 68)).toNat)
  · -- entry invariant: `k = 0`
    exact ⟨hpg, rfl, ⟨0, by omega, by simpa using hidx, hpres⟩,
      w8, w9, w10, w11, rfl⟩
  · -- step
    rintro st3 s3 ⟨hpg3, hgl3, ⟨k, hkL, hidx3, hpres3⟩, v8, v9, v10, v11, rfl⟩
    have g68 : ¬ (1114112 < fp.toNat + 68 + 4) := by omega
    have q68 : fp.toNat ≤ 1114040 := by omega
    have hofk : (UInt32.ofNat k).toNat = k := by
      rw [UInt32.toNat_ofNat_of_lt']
      simp [UInt32.size]; omega
    wp_run
    simp [hpg3, hidx3, g68]
    by_cases hk : k < lenv.toNat
    · -- one more byte to compare
      have hklt : UInt32.ofNat k < lenv := by
        rw [UInt32.lt_iff_toNat_lt, hofk]; exact hk
      have hk32 : UInt32.ofNat k < 32 := by
        rw [UInt32.lt_iff_toNat_lt, hofk]
        simp; omega
      simp [hklt]
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      wp_run
      have haddr1 : (UInt32.ofNat k + fp).toNat = fp.toNat + k := by
        rw [UInt32.toNat_add, hofk]
        have : k + fp.toNat < UInt32.size := by simp [UInt32.size]; omega
        rw [Nat.mod_eq_of_lt this]
        omega
      have haddr2 : (UInt32.ofNat k + (32 + fp)).toNat = fp.toNat + 32 + k := by
        rw [UInt32.toNat_add, hofk, toNat_add_of_lt _ _ (by simp; omega)]
        simp only [show (32 : UInt32).toNat = 32 from rfl]
        have : k + (32 + fp.toNat) < UInt32.size := by simp [UInt32.size]; omega
        rw [Nat.mod_eq_of_lt this]
        omega
      have hnb1 : ¬ (1114112 ≤ fp.toNat + k) := by omega
      have hnb2 : ¬ (1114112 ≤ fp.toNat + 32 + k) := by omega
      have hb1 : st3.mem.read8 (UInt32.ofNat k + fp) = D k := by
        show st3.mem.bytes (UInt32.ofNat k + fp).toNat = D k
        rw [haddr1, hpres3 _ (by omega)]
        exact hfast k hk
      have hb2 : st3.mem.read8 (UInt32.ofNat k + (32 + fp)) = D k := by
        show st3.mem.bytes (UInt32.ofNat k + (32 + fp)).toNat = D k
        rw [haddr2, hpres3 _ (by omega)]
        exact hnaive k hk
      have hadd1 : (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, hofk,
          UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp
        omega
      simp [hk32, haddr1, haddr2, hnb1, hnb2, hb1, hb2, hpg3, hidx3, g68]
      refine ⟨⟨hgl3, ⟨k + 1, by omega, hadd1, ?_⟩⟩, ?_⟩
      · intro j hj
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        exact hpres3 j hj
      · omega
    · -- all bytes agree: `br_if 1` exits the loop
      have hnk : ¬ (UInt32.ofNat k < lenv) := by
        rw [UInt32.lt_iff_toNat_lt, hofk]; omega
      simp [hnk]
      exact hexit st3 v8 v9 v10 v11 hpg3 hgl3 hpres3

/-! ## Fast-formatter helpers (`func40`'s callee closure)

Frame-pointer-parametric specs for every function the `itoa` u64 core
`func40` calls — `func41`/`func42` (checked `Result` wrap/unwrap, per
chunk iteration), `func38` (the `/100` magic-division splitter),
`func39` → `func46` (the `DIGIT_TABLE` address computation), plus the
slice packaging chain `func49` → `func47` → `func37`/`func45` and the
wrapper glue `func10` (identity 2nd-arg) and `func25` (the 40-byte
red-zone copy used by `func22`/`func24`). All are stated over an
abstract shadow-stack pointer `g` (`g.toNat ≤ 1048576`, frame-size
lower bound per function) with byte-level framing postconditions in
`toNat` form, matching the naive-side corpus idiom. Leaves that never
move the stack pointer (`func10`/`func37`/`func38`/`func45`/`func46`/
`func48`/`func25`) spill into the red zone *below* the current `g`, so
their framing windows extend 16/32 bytes beneath it; wrappers compose
callees via `wp_call_of_terminates`.

Signedness/conversion bridges: `extendS_toUInt64_small` (sign-extension
of a known-nonnegative i32 is zero-extension); `func48`/`func41` take
`x.toNat < 2^31` (all of `func40`'s call sites pass constants 999 /
10000), `func42` takes an even discriminant (its call sites pass the
`Ok`-tag 0 written by `func41`). -/

set_option maxHeartbeats 1600000 in
theorem func10_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (a b : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg16 : 16 ≤ g.toNat) (hghi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 10 st0 [.i32 b, .i32 a]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 b] ∧
        (∀ i : Nat, i < g.toNat - 16 ∨ g.toNat ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 16 + 8).toNat = g.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 16 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  have q8 : g.toNat - 16 ≤ 1114100 := by omega
  have q12 : g.toNat - 16 ≤ 1114096 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32], func10, [.i32]⟩) rfl
  unfold func10
  wp_run
  simp [hg, hpg, hsub, p8, p12]
  intro i hi
  repeat rw [if_neg (by omega)]

set_option maxHeartbeats 1600000 in
theorem func46_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (a0 a1 a2 a3 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg16 : 16 ≤ g.toNat) (hghi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 46 st0 [.i32 a3, .i32 a2, .i32 a1, .i32 a0]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 (a0 + a1)] ∧
        (∀ i : Nat, i < g.toNat - 16 ∨ g.toNat ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t4 : (g - 16 + 4).toNat = g.toNat - 16 + 4 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t8 : (g - 16 + 8).toNat = g.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p4 : ¬ (1114112 < g.toNat - 16 + 4 + 4) := by omega
  have p8 : ¬ (1114112 < g.toNat - 16 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32], func46, [.i32]⟩) rfl
  unfold func46
  wp_run
  simp [hg, hpg, hsub, p4, p8, p12]
  intro i hi
  repeat rw [if_neg (by omega)]

set_option maxHeartbeats 1600000 in
theorem func45_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret a b : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg16 : 16 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 8 ≤ 1114112) :
    TerminatesWith env «module» 45 st0 [.i32 b, .i32 a, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read32 ret = a ∧
        st'.mem.read32 (ret + 4) = b ∧
        (∀ i : Nat, (i < g.toNat - 16 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 8 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 16 + 8).toNat = g.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr4 : (ret + 4).toNat = ret.toNat + 4 := by
    rw [UInt32.toNat_add]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 16 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 4) := by omega
  have pr4 : ¬ (1114112 < ret.toNat + 4 + 4) := by omega
  have qr0 : ret.toNat ≤ 1114108 := by omega
  have qr4 : ret.toNat ≤ 1114104 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32], [.i32], func45, []⟩) rfl
  unfold func45
  wp_run
  simp [hg, hpg, hsub, p8, p12, pr0, pr4]
  refine ⟨?_, ?_⟩
  · rw [read32_write32_disjoint' _ _ _ _ (by omega), read32_write32_same']
  · intro i hi hir
    repeat rw [if_neg (by omega)]

set_option maxHeartbeats 1600000 in
theorem func37_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret p1 p2 p3 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg32 : 32 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 8 ≤ 1114112) :
    TerminatesWith env «module» 37 st0 [.i32 p3, .i32 p2, .i32 p1, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read32 ret = p1 + p2 ∧
        st'.mem.read32 (ret + 4) = p3 - p1 ∧
        (∀ i : Nat, (i < g.toNat - 32 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 8 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 32 + 8).toNat = g.toNat - 32 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 32 + 12).toNat = g.toNat - 32 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t16 : (g - 32 + 16).toNat = g.toNat - 32 + 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t20 : (g - 32 + 20).toNat = g.toNat - 32 + 20 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t24 : (g - 32 + 24).toNat = g.toNat - 32 + 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t28 : (g - 32 + 28).toNat = g.toNat - 32 + 28 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr4 : (ret + 4).toNat = ret.toNat + 4 := by
    rw [UInt32.toNat_add]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 32 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 32 + 12 + 4) := by omega
  have p16 : ¬ (1114112 < g.toNat - 32 + 16 + 4) := by omega
  have p20 : ¬ (1114112 < g.toNat - 32 + 20 + 4) := by omega
  have p24 : ¬ (1114112 < g.toNat - 32 + 24 + 4) := by omega
  have p28 : ¬ (1114112 < g.toNat - 32 + 28 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 4) := by omega
  have pr4 : ¬ (1114112 < ret.toNat + 4 + 4) := by omega
  have qr0 : ret.toNat ≤ 1114108 := by omega
  have qr4 : ret.toNat ≤ 1114104 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32, .i32], func37, []⟩) rfl
  unfold func37
  wp_run
  simp [hg, hpg, hsub, p8, p12, p16, p20, p24, p28, pr0, pr4]
  refine ⟨?_, ?_⟩
  · rw [read32_write32_disjoint' _ _ _ _ (by omega), read32_write32_same']
  · intro i hi hir
    repeat rw [if_neg (by omega)]

set_option maxHeartbeats 1600000 in
theorem func38_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret x : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg16 : 16 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 8 ≤ 1114112) :
    TerminatesWith env «module» 38 st0 [.i32 x, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read32 ret = (5243 * x) >>> 19 ∧
        st'.mem.read32 (ret + 4) = x - (100 : UInt32) * ((5243 * x) >>> 19) ∧
        (∀ i : Nat, (i < g.toNat - 16 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 8 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 16 + 8).toNat = g.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr4 : (ret + 4).toNat = ret.toNat + 4 := by
    rw [UInt32.toNat_add]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 16 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 4) := by omega
  have pr4 : ¬ (1114112 < ret.toNat + 4 + 4) := by omega
  have qr0 : ret.toNat ≤ 1114108 := by omega
  have qr4 : ret.toNat ≤ 1114104 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32], func38, []⟩) rfl
  unfold func38
  wp_run
  simp [hg, hpg, hsub, p8, p12, pr0, pr4]
  refine ⟨?_, ?_⟩
  · rw [read32_write32_disjoint' _ _ _ _ (by omega), read32_write32_same']
  · intro i hi hir
    repeat rw [if_neg (by omega)]

private theorem extendS_toUInt64_small (x : UInt32) (hx : x.toNat < 2147483648) :
    x.toInt32.toInt64.toUInt64 = x.toUInt64 := by
  have hx' : x < 2147483648 := by rw [UInt32.lt_iff_toNat_lt]; simpa using hx
  bv_decide

set_option maxHeartbeats 1600000 in
theorem func48_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret x : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg16 : 16 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 16 ≤ 1114112)
    (hx : x.toNat < 2147483648) :
    TerminatesWith env «module» 48 st0 [.i32 x, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read64 ret = 0 ∧
        st'.mem.read64 (ret + 8) = UInt64.ofNat x.toNat ∧
        (∀ i : Nat, (i < g.toNat - 16 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 16 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr8 : (ret + 8).toNat = ret.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 8) := by omega
  have pr8 : ¬ (1114112 < ret.toNat + 8 + 8) := by omega
  have qr0 : ret.toNat ≤ 1114104 := by omega
  have qr8 : ret.toNat ≤ 1114096 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i64, .i64], func48, []⟩) rfl
  unfold func48
  wp_run
  simp [hg, hpg, hsub, p12]
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  have hge : (0 : Int32) ≤ x.toInt32 := by
    have h := (leS_small 0 x (by decide) hx).mpr (Nat.zero_le _)
    simpa using h
  simp [hge, hg, hpg, pr0, pr8, extendS_toUInt64_small x hx]
  refine ⟨?_, ?_⟩
  · rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · intro i hi hir
    rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 1600000 in
theorem func42_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (v0 v1 : UInt64) (a2 a3 a4 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg48 : 48 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hv0 : v0.toNat % 2 = 0) :
    TerminatesWith env «module» 42 st0 [.i32 a4, .i32 a3, .i32 a2, .i64 v1, .i64 v0]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i64 v1] ∧
        (∀ i : Nat, i < g.toNat - 48 ∨ g.toNat ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 48).toNat = g.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le g 48 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 48 + 8).toNat = g.toNat - 48 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t16 : (g - 48 + 16).toNat = g.toNat - 48 + 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t32 : (g - 48 + 32).toNat = g.toNat - 48 + 32 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t36 : (g - 48 + 36).toNat = g.toNat - 48 + 36 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t40 : (g - 48 + 40).toNat = g.toNat - 48 + 40 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 48 + (g - 48) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 48 + 8 + 8) := by omega
  have p16 : ¬ (1114112 < g.toNat - 48 + 16 + 8) := by omega
  have p32 : ¬ (1114112 < g.toNat - 48 + 32 + 4) := by omega
  have p36 : ¬ (1114112 < g.toNat - 48 + 36 + 4) := by omega
  have p40 : ¬ (1114112 < g.toNat - 48 + 40 + 8) := by omega
  have q8 : g.toNat - 48 ≤ 1114096 := by omega
  have q16 : g.toNat - 48 ≤ 1114088 := by omega
  have q32 : g.toNat - 48 ≤ 1114076 := by omega
  have q36 : g.toNat - 48 ≤ 1114072 := by omega
  have q40 : g.toNat - 48 ≤ 1114064 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i64, .i32, .i32, .i32], [.i32, .i64], func42, [.i64]⟩) rfl
  unfold func42
  wp_run
  simp [hg, hpg, hsub, p8, p16, p32, p36]
  apply wp_block_cons
  wp_run
  have hb8 : ((((st0.mem.write64 (g - 48 + 8) v0).write64 (g - 48 + 16) v1).write32
      (g - 48 + 32) a2).write32 (g - 48 + 36) a3).read64 (g - 48 + 8) = v0 := by
    rw [read64_write32_disjoint _ _ _ _ (by omega),
        read64_write32_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_same]
  have hb16 : ((((st0.mem.write64 (g - 48 + 8) v0).write64 (g - 48 + 16) v1).write32
      (g - 48 + 32) a2).write32 (g - 48 + 36) a3).read64 (g - 48 + 16) = v1 := by
    rw [read64_write32_disjoint _ _ _ _ (by omega),
        read64_write32_disjoint _ _ _ _ (by omega),
        read64_write64_same]
  have hcond : (1 : UInt32) &&& UInt32.ofNat (v0.toNat % 4294967296) = 0 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_and,
      UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
    show (1 : Nat) &&& v0.toNat % 4294967296 = 0
    rw [Nat.and_comm, Nat.and_one_is_mod]
    omega
  simp [hb8, hb16, hcond, hpg, hsub, hback, p16, p40, q8,
    List.getElem?_set_self (by simpa using hglen)]
  intro i hi
  rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write64_bytes_of_disjoint _ _ _ _ (by omega),
      write64_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 1600000 in
theorem func39_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (a0 a1 a2 a3 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg32 : 32 ≤ g.toNat) (hghi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 39 st0 [.i32 a3, .i32 a2, .i32 a1, .i32 a0]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 (a2 + a0)] ∧
        (∀ i : Nat, i < g.toNat - 32 ∨ g.toNat ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t4 : (g - 16 + 4).toNat = g.toNat - 16 + 4 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t8 : (g - 16 + 8).toNat = g.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 16 + (g - 16) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p4 : ¬ (1114112 < g.toNat - 16 + 4 + 4) := by omega
  have p8 : ¬ (1114112 < g.toNat - 16 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32], func39, [.i32]⟩) rfl
  unfold func39
  wp_run
  simp [hg, hpg, hsub, p4, p8, p12]
  apply wp_call_of_terminates (func46_spec env _ (g - 16) a2 a0 a1 a3
    (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
    (by omega) (by omega))
  rintro st' vs ⟨hpg', hg', hrs, hpres⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  subst hrs
  wp_run
  simp [hg', hback, hpg', List.getElem?_set_self hglen']
  intro i hi
  have hstep := hpres i (by omega)
  rw [hstep,
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 1600000 in
theorem func41_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret x : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg32 : 32 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 16 ≤ 1114112)
    (hx : x.toNat < 2147483648) :
    TerminatesWith env «module» 41 st0 [.i32 x, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read64 ret = 0 ∧
        st'.mem.read64 (ret + 8) = x.toUInt64 ∧
        (∀ i : Nat, (i < g.toNat - 32 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 16 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 16 + (g - 16) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32], func41, []⟩) rfl
  unfold func41
  wp_run
  simp [hg, hpg, hsub, p12]
  apply wp_call_of_terminates (func48_spec env _ (g - 16) ret x
    (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
    (by omega) (by omega) hret hx)
  rintro st' vs ⟨hpg', hg', hrs, hr0, hr8, hpres⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  subst hrs
  wp_run
  simp [hg', hback, hpg', hr0, hr8, List.getElem?_set_self hglen']
  intro i hi hir
  have hstep := hpres i (by omega) (by omega)
  rw [hstep, write32_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 1600000 in
theorem func47_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret a1 a2 a3 a4 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg64 : 64 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 8 ≤ 1114112) :
    TerminatesWith env «module» 47 st0 [.i32 a4, .i32 a3, .i32 a2, .i32 a1, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read32 ret = a3 + a1 ∧
        st'.mem.read32 (ret + 4) = a2 - a3 ∧
        (∀ i : Nat, (i < g.toNat - 64 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 8 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 32 + 8).toNat = g.toNat - 32 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 32 + 12).toNat = g.toNat - 32 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t20 : (g - 32 + 20).toNat = g.toNat - 32 + 20 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t24 : (g - 32 + 24).toNat = g.toNat - 32 + 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t28 : (g - 32 + 28).toNat = g.toNat - 32 + 28 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr4 : (ret + 4).toNat = ret.toNat + 4 := by
    rw [UInt32.toNat_add]; simp; omega
  have hback : 32 + (g - 32) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p20 : ¬ (1114112 < g.toNat - 32 + 20 + 4) := by omega
  have p24 : ¬ (1114112 < g.toNat - 32 + 24 + 4) := by omega
  have p28 : ¬ (1114112 < g.toNat - 32 + 28 + 4) := by omega
  have p8 : ¬ (1114112 < g.toNat - 32 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 32 + 12 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 4) := by omega
  have pr4 : ¬ (1114112 < ret.toNat + 4 + 4) := by omega
  have qr0 : ret.toNat ≤ 1114108 := by omega
  have qr4 : ret.toNat ≤ 1114104 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32, .i32], [.i32, .i32], func47, []⟩) rfl
  unfold func47
  wp_run
  simp [hg, hpg, hsub, p20, p24, p28]
  have haddr8 : (8 : UInt32) + (g - 32) = g - 32 + 8 := by bv_decide
  have haddr12 : g - 32 + 8 + 4 = g - 32 + 12 := by
    bv_decide
  have t8' : ((8 : UInt32) + (g - 32)).toNat = g.toNat - 32 + 8 := by
    rw [haddr8]; exact t8
  apply wp_call_of_terminates (func37_spec env _ (g - 32) (8 + (g - 32)) a3 a1 a2
    (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
    (by omega) (by omega) (by omega))
  rintro st' vs ⟨hpg', hg', hrs, hr0, hr4, hpres⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  subst hrs
  rw [haddr8] at hr0
  rw [haddr8, haddr12] at hr4
  wp_run
  simp [hg', hback, hpg', hsub, hr0, hr4, p8, p12, pr0, pr4,
    List.getElem?_set_self hglen']
  refine ⟨?_, ?_⟩
  · rw [read32_write32_disjoint' _ _ _ _ (by omega), read32_write32_same']
  · intro i hi hir
    repeat rw [if_neg (by omega)]
    have hstep := hpres i (by omega) (by omega)
    rw [hstep,
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 8000000 in
theorem func49_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret a1 a2 a3 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg112 : 112 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 8 ≤ 1114112) :
    TerminatesWith env «module» 49 st0 [.i32 a3, .i32 a2, .i32 a1, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read32 ret = a3 + a1 ∧
        st'.mem.read32 (ret + 4) = a2 - a3 ∧
        (∀ i : Nat, (i < g.toNat - 112 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 8 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 48).toNat = g.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le g 48 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 48 + 8).toNat = g.toNat - 48 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 48 + 12).toNat = g.toNat - 48 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t16 : (g - 48 + 16).toNat = g.toNat - 48 + 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t20 : (g - 48 + 20).toNat = g.toNat - 48 + 20 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t28 : (g - 48 + 28).toNat = g.toNat - 48 + 28 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t32 : (g - 48 + 32).toNat = g.toNat - 48 + 32 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t36 : (g - 48 + 36).toNat = g.toNat - 48 + 36 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t40 : (g - 48 + 40).toNat = g.toNat - 48 + 40 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t44 : (g - 48 + 44).toNat = g.toNat - 48 + 44 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr4 : (ret + 4).toNat = ret.toNat + 4 := by
    rw [UInt32.toNat_add]; simp; omega
  have hback : 48 + (g - 48) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p28 : ¬ (1114112 < g.toNat - 48 + 28 + 4) := by omega
  have p32 : ¬ (1114112 < g.toNat - 48 + 32 + 4) := by omega
  have p36 : ¬ (1114112 < g.toNat - 48 + 36 + 4) := by omega
  have p16 : ¬ (1114112 < g.toNat - 48 + 16 + 4) := by omega
  have p20 : ¬ (1114112 < g.toNat - 48 + 20 + 4) := by omega
  have p8 : ¬ (1114112 < g.toNat - 48 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 48 + 12 + 4) := by omega
  have p40 : ¬ (1114112 < g.toNat - 48 + 40 + 4) := by omega
  have p44 : ¬ (1114112 < g.toNat - 48 + 44 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 4) := by omega
  have pr4 : ¬ (1114112 < ret.toNat + 4 + 4) := by omega
  have qr0 : ret.toNat ≤ 1114108 := by omega
  have qr4 : ret.toNat ≤ 1114104 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32, .i32, .i32, .i32], func49, []⟩) rfl
  unfold func49
  wp_run
  simp [hg, hpg, hsub, p28, p32, p36]
  have haddr16 : (16 : UInt32) + (g - 48) = g - 48 + 16 := by bv_decide
  have haddr20 : g - 48 + 16 + 4 = g - 48 + 20 := by
    bv_decide
  have haddr8 : (8 : UInt32) + (g - 48) = g - 48 + 8 := by bv_decide
  have haddr12 : g - 48 + 8 + 4 = g - 48 + 12 := by
    bv_decide
  have t16' : ((16 : UInt32) + (g - 48)).toNat = g.toNat - 48 + 16 := by
    rw [haddr16]; exact t16
  have t8' : ((8 : UInt32) + (g - 48)).toNat = g.toNat - 48 + 8 := by
    rw [haddr8]; exact t8
  apply wp_call_of_terminates (func47_spec env _ (g - 48) (16 + (g - 48)) a1 a2 a3 1049600
    (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
    (by omega) (by omega) (by omega))
  rintro st' vs ⟨hpg', hg', hrs, hr16, hr20, hpres⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  subst hrs
  rw [haddr16] at hr16
  rw [haddr16, haddr20] at hr20
  wp_run
  simp [hpg', hsub, hr16, hr20, p16, p20, p40, p44]
  apply wp_call_of_terminates (func45_spec env _ (g - 48) (8 + (g - 48)) (a3 + a1) (a2 - a3)
    (by simp [hpg']) (by simpa using hg')
    (by omega) (by omega) (by omega))
  rintro st2 vs2 ⟨hpg2, hg2, hrs2, hra, hrb, hpres2⟩
  obtain ⟨hglen2, -⟩ := List.getElem?_eq_some_iff.mp hg2
  subst hrs2
  rw [haddr8] at hra
  rw [haddr8, haddr12] at hrb
  wp_run
  simp [hg2, hback, hpg2, hsub, hra, hrb, p8, p12, pr0, pr4,
    List.getElem?_set_self hglen2]
  refine ⟨?_, ?_⟩
  · rw [read32_write32_disjoint' _ _ _ _ (by omega), read32_write32_same']
  · intro i hi hir
    repeat rw [if_neg (by omega)]
    have hstep2 := hpres2 i (by omega) (by omega)
    rw [hstep2,
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega)]
    have hstep := hpres i (by omega) (by omega)
    rw [hstep,
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 1600000 in
theorem func25_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (a0 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg48 : 48 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hdst : g.toNat ≤ a0.toNat) (hdhi : a0.toNat + 40 ≤ 1114112) :
    TerminatesWith env «module» 25 st0 [.i32 a0]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read64 a0 = st0.mem.read64 (g - 48 + 8) ∧
        st'.mem.read64 (a0 + 8) = st0.mem.read64 (g - 48 + 16) ∧
        st'.mem.read64 (a0 + 16) = st0.mem.read64 (g - 48 + 24) ∧
        st'.mem.read64 (a0 + 24) = st0.mem.read64 (g - 48 + 32) ∧
        st'.mem.read64 (a0 + 32) = st0.mem.read64 (g - 48 + 40) ∧
        (∀ i : Nat, i < a0.toNat ∨ a0.toNat + 40 ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 48).toNat = g.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le g 48 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 48 + 8).toNat = g.toNat - 48 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t16 : (g - 48 + 16).toNat = g.toNat - 48 + 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t24 : (g - 48 + 24).toNat = g.toNat - 48 + 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t32 : (g - 48 + 32).toNat = g.toNat - 48 + 32 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t40 : (g - 48 + 40).toNat = g.toNat - 48 + 40 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have ta8 : (a0 + 8).toNat = a0.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  have ta16 : (a0 + 16).toNat = a0.toNat + 16 := by
    rw [UInt32.toNat_add]; simp; omega
  have ta24 : (a0 + 24).toNat = a0.toNat + 24 := by
    rw [UInt32.toNat_add]; simp; omega
  have ta32 : (a0 + 32).toNat = a0.toNat + 32 := by
    rw [UInt32.toNat_add]; simp; omega
  have ps8 : ¬ (1114112 < g.toNat - 48 + 8 + 8) := by omega
  have ps16 : ¬ (1114112 < g.toNat - 48 + 16 + 8) := by omega
  have ps24 : ¬ (1114112 < g.toNat - 48 + 24 + 8) := by omega
  have ps32 : ¬ (1114112 < g.toNat - 48 + 32 + 8) := by omega
  have ps40 : ¬ (1114112 < g.toNat - 48 + 40 + 8) := by omega
  have pa0 : ¬ (1114112 < a0.toNat + 8) := by omega
  have pa8 : ¬ (1114112 < a0.toNat + 8 + 8) := by omega
  have pa16 : ¬ (1114112 < a0.toNat + 16 + 8) := by omega
  have pa24 : ¬ (1114112 < a0.toNat + 24 + 8) := by omega
  have pa32 : ¬ (1114112 < a0.toNat + 32 + 8) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32], [.i32], func25, []⟩) rfl
  unfold func25
  wp_run
  simp [hg, hpg, hsub, ps8, ps16, ps24, ps32, ps40, pa0, pa8, pa16, pa24, pa32]
  have e32 : (st0.mem.write64 (a0 + 32) (st0.mem.read64 (g - 48 + 40))).read64
      (g - 48 + 32) = st0.mem.read64 (g - 48 + 32) :=
    read64_write64_disjoint _ _ _ _ (by omega)
  simp only [e32]
  have e24 : ((st0.mem.write64 (a0 + 32) (st0.mem.read64 (g - 48 + 40))).write64
      (a0 + 24) (st0.mem.read64 (g - 48 + 32))).read64 (g - 48 + 24)
      = st0.mem.read64 (g - 48 + 24) := by
    rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega)]
  simp only [e24]
  have e16 : (((st0.mem.write64 (a0 + 32) (st0.mem.read64 (g - 48 + 40))).write64
      (a0 + 24) (st0.mem.read64 (g - 48 + 32))).write64
      (a0 + 16) (st0.mem.read64 (g - 48 + 24))).read64 (g - 48 + 16)
      = st0.mem.read64 (g - 48 + 16) := by
    rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega)]
  simp only [e16]
  have e8 : ((((st0.mem.write64 (a0 + 32) (st0.mem.read64 (g - 48 + 40))).write64
      (a0 + 24) (st0.mem.read64 (g - 48 + 32))).write64
      (a0 + 16) (st0.mem.read64 (g - 48 + 24))).write64
      (a0 + 8) (st0.mem.read64 (g - 48 + 16))).read64 (g - 48 + 8)
      = st0.mem.read64 (g - 48 + 8) := by
    rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega)]
  simp only [e8]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · intro i hi
    rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega)]

end Project.Itoa.Proofs
