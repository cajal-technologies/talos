import CodeLib.RustStd.HashMap.Table
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup

/-!
# The table model refines the association-list model

`CodeLib.RustStd.HashMap.Table` is the SwissTable of `hashbrown` 0.16.1 at
the level of control bytes and slots.  `CodeLib.RustStd.HashMap.Basic` is the
association list that the contracts in `Project.RustHashMap.Spec` speak
about.  This file proves that `Table.toList` carries each operation of the
first to the matching operation of the second.

The invariant `WF hash t` says what a table that the Rust code built looks
like: the bucket count is a power of two, the control bytes obey the mirror
rule of `set_ctrl`, a slot is full exactly where its control byte is full, a
full byte is the tag of the key in its slot, no key sits in two slots, and
every key is reachable: no window of its probe sequence before the window
that holds it has an `EMPTY` byte.  `Clean t` adds that the table has no
tombstone, which is the state of every table that an export of
`rust_hash_map` builds before it inserts.  The one path that a `Clean` table
never takes is `rehashInPlace`, so this file does not reason about it.

The arithmetic part is the cover lemma: in a table of `8 * 2 ^ k` buckets the
first `2 ^ k` windows of a probe sequence visit every bucket.  It rests on the
fact that the triangular numbers are a permutation modulo a power of two.

The results at the end are the shapes of the exports: `sortByKey_ofEntries`,
`insert_ofEntries`, `remove_ofEntries`, `get_ofEntries`,
`containsKey_ofEntries` and `len_ofEntries`.  Each one takes the entry list
of the wire and holds for every hash function.  The one bound is
`es.length <= 2 ^ 30`, which keeps the bucket count below `2 ^ 32`, the
range of `usize` on wasm32.  `WF.insert` is the general step: any `Clean`
table with fewer than `2 ^ 32` buckets, with the resize.
-/

namespace Wasm.RustStd.HashMap

variable {K V : Type}

namespace Table

/-! ## Bucket counts -/

/-- The bucket counts a table can have: one, or a power of two from four up.
`nextPow2` never returns more than `2 ^ 32`. -/
def Shape (b : Nat) : Prop := ∃ m, m ≤ 32 ∧ m ≠ 1 ∧ b = 2 ^ m

theorem Shape.pos {b : Nat} (h : Shape b) : 0 < b := by
  obtain ⟨m, -, -, rfl⟩ := h
  positivity

theorem Shape.dvd_pow32 {b : Nat} (h : Shape b) : b ∣ 2 ^ 32 := by
  obtain ⟨m, hm, -, rfl⟩ := h
  exact Nat.pow_dvd_pow 2 hm

theorem Shape.small {b : Nat} (h : Shape b) (hb : b < 8) : b = 1 ∨ b = 4 := by
  obtain ⟨m, -, hm1, rfl⟩ := h
  have hm : m < 3 := by
    by_contra hc
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hc)
    omega
  interval_cases m <;> simp_all

theorem Shape.dvd_eight {b : Nat} (h : Shape b) (hb : b < 8) : b ∣ 8 := by
  rcases h.small hb with rfl | rfl <;> norm_num

theorem Shape.eq_mul_pow {b : Nat} (h : Shape b) (hb : 8 ≤ b) :
    ∃ k, b = 8 * 2 ^ k := by
  obtain ⟨m, -, -, rfl⟩ := h
  have hm : 3 ≤ m := by
    by_contra hc
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact ⟨k, by simp [Nat.pow_add]⟩

theorem Shape.cap_lt {b : Nat} (h : Shape b) : bucketMaskToCapacity (b - 1) < b := by
  have := h.pos
  unfold bucketMaskToCapacity
  split <;> omega

/-! ## The mirror rule -/

/-- A byte between `buckets` and eight of a small table is padding. -/
def IsPad (b p : Nat) : Prop := b < 8 ∧ b ≤ p ∧ p < 8

instance (b p : Nat) : Decidable (IsPad b p) := by unfold IsPad; infer_instance

/-- The physical control bytes as `set_ctrl` keeps them: a pad byte is
`EMPTY`, and every other byte is the byte of its bucket. -/
def Mirror (t : Table K V) : Prop :=
  ∀ p, p < t.buckets + 8 →
    t.ctrlAt p = if IsPad t.buckets p then EMPTY else t.ctrlAt (p % t.buckets)

theorem wrapSub_eight_of_le {b i : Nat} (hb : b ∣ 2 ^ 32) (h8 : 8 ≤ b) :
    wrapSub i 8 b = (i + (b - 8)) % b := by
  have hle : b ≤ 2 ^ 32 := Nat.le_of_dvd (by norm_num) hb
  have h1 : (b - 8) ≡ (2 ^ 32 - 8) [MOD b] :=
    (Nat.modEq_iff_dvd' (by omega)).2 (by
      rw [show 2 ^ 32 - 8 - (b - 8) = 2 ^ 32 - b by omega]
      exact Nat.dvd_sub hb dvd_rfl)
  unfold wrapSub
  rw [show i + 2 ^ 32 - 8 = i + (2 ^ 32 - 8) by omega]
  exact (Nat.ModEq.add_left i h1).symm

theorem wrapSub_eight_of_dvd {b i : Nat} (hb : b ∣ 2 ^ 32) (h8 : b ∣ 8) :
    wrapSub i 8 b = i % b := by
  unfold wrapSub
  rw [show i + 2 ^ 32 - 8 = i + (2 ^ 32 - 8) by omega]
  have : (2 ^ 32 - 8) % b = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hb h8)
  rw [Nat.add_mod, this, Nat.add_zero, Nat.mod_mod]

theorem index2_eq_of_le {b i : Nat} (hb : b ∣ 2 ^ 32) (h8 : 8 ≤ b) (hi : i < b) :
    index2 b i = if i < 8 then i + b else i := by
  unfold index2
  rw [wrapSub_eight_of_le hb h8]
  split
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show i + (b - 8) = (i - 8) + b by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem index2_eq_of_dvd {b i : Nat} (hb : b ∣ 2 ^ 32) (h8 : b ∣ 8) (hi : i < b) :
    index2 b i = i + 8 := by
  unfold index2
  rw [wrapSub_eight_of_dvd hb h8, Nat.mod_eq_of_lt hi]

theorem index2_lt {b i : Nat} (hs : Shape b) (hi : i < b) : index2 b i < b + 8 := by
  rcases Nat.lt_or_ge b 8 with h | h
  · rw [index2_eq_of_dvd hs.dvd_pow32 (hs.dvd_eight h) hi]; omega
  · rw [index2_eq_of_le hs.dvd_pow32 h hi]; split <;> omega

/-- The two places `set_ctrl` writes are exactly the physical bytes of one
bucket that are not padding. -/
theorem index2_iff {b i p : Nat} (hs : Shape b) (hi : i < b) (hp : p < b + 8) :
    (p = i ∨ p = index2 b i) ↔ (¬ IsPad b p ∧ p % b = i) := by
  have hpos := hs.pos
  rcases Nat.lt_or_ge b 8 with h | h
  · rw [index2_eq_of_dvd hs.dvd_pow32 (hs.dvd_eight h) hi]
    have h8 : 8 % b = 0 := Nat.mod_eq_zero_of_dvd (hs.dvd_eight h)
    unfold IsPad
    constructor
    · rintro (rfl | rfl)
      · exact ⟨by omega, Nat.mod_eq_of_lt hi⟩
      · refine ⟨by omega, ?_⟩
        rw [Nat.add_mod, h8, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hi]
    · rintro ⟨hpad, hmod⟩
      rcases Nat.lt_or_ge p b with hpb | hpb
      · left; rw [Nat.mod_eq_of_lt hpb] at hmod; exact hmod
      · right
        have hp8 : 8 ≤ p := by omega
        rw [show p = (p - 8) + 8 by omega, Nat.add_mod, h8, Nat.add_zero, Nat.mod_mod,
          Nat.mod_eq_of_lt (by omega)] at hmod
        omega
  · rw [index2_eq_of_le hs.dvd_pow32 h hi]
    have hnopad : ¬ IsPad b p := by unfold IsPad; omega
    simp only [hnopad, not_false_eq_true, true_and]
    constructor
    · rintro (rfl | hp2)
      · exact Nat.mod_eq_of_lt hi
      · split at hp2
        · subst hp2; rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
        · subst hp2; exact Nat.mod_eq_of_lt hi
    · intro hmod
      rcases Nat.lt_or_ge p b with hpb | hpb
      · left; rw [Nat.mod_eq_of_lt hpb] at hmod; exact hmod
      · right
        rw [show p = (p - b) + b by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hmod
        split <;> omega

/-! ## Triangular numbers modulo a power of two -/

theorem tri_step (n d : Nat) :
    (n + d) * (n + d + 1) = n * (n + 1) + d * (2 * n + d + 1) := by ring

theorem pow_two_dvd_of_dvd_mul_odd {e d o : Nat} (ho : o % 2 = 1) (h : 2 ^ e ∣ d * o) :
    2 ^ e ∣ d := by
  have hc : Nat.Coprime (2 ^ e) o :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
  exact hc.dvd_of_dvd_mul_right h

/-- Two triangular numbers below `2 ^ k` that agree modulo `2 ^ (k + 1)` have
the same index: of `d` and `2 * n + d + 1` one is odd, so the power of two
divides the other, which is too small. -/
theorem tri_inj {k n m : Nat} (hn : n < 2 ^ k) (hm : m < 2 ^ k)
    (h : n * (n + 1) % 2 ^ (k + 1) = m * (m + 1) % 2 ^ (k + 1)) : n = m := by
  wlog hle : n ≤ m generalizing n m
  · exact (this hm hn h.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [tri_step] at h
  have hdvd : 2 ^ (k + 1) ∣ d * (2 * n + d + 1) := by
    have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [Nat.add_sub_cancel_left] at this
    exact Nat.dvd_of_mod_eq_zero this
  have hk : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  rcases Nat.even_or_odd d with hd | hd
  · obtain ⟨r, hr⟩ := hd
    have ho : (2 * n + d + 1) % 2 = 1 := by omega
    have hdd := pow_two_dvd_of_dvd_mul_odd ho hdvd
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · rfl
    · have := Nat.le_of_dvd hpos hdd
      omega
  · have ho : d % 2 = 1 := Nat.odd_iff.1 hd
    have hdd := pow_two_dvd_of_dvd_mul_odd ho (by rwa [Nat.mul_comm] at hdvd)
    have := Nat.le_of_dvd (by omega) hdd
    omega

/-- The triangular numbers below `2 ^ k` hit every residue modulo `2 ^ k`. -/
theorem tri_surj (k r : Nat) (hr : r < 2 ^ k) :
    ∃ n < 2 ^ k, n * (n + 1) / 2 % 2 ^ k = r := by
  have hpos : 0 < 2 ^ k := by positivity
  have hinj : Function.Injective
      (fun n : Fin (2 ^ k) => (⟨n.1 * (n.1 + 1) / 2 % 2 ^ k, Nat.mod_lt _ hpos⟩ : Fin (2 ^ k))) := by
    intro n m hnm
    have h : n.1 * (n.1 + 1) / 2 % 2 ^ k = m.1 * (m.1 + 1) / 2 % 2 ^ k := congrArg Fin.val hnm
    apply Fin.ext
    apply tri_inj n.2 m.2
    have h2 : 2 * (n.1 * (n.1 + 1) / 2 % 2 ^ k) = 2 * (m.1 * (m.1 + 1) / 2 % 2 ^ k) := by rw [h]
    rwa [← Nat.mul_mod_mul_left, ← Nat.mul_mod_mul_left,
      Nat.mul_div_cancel' (Nat.even_mul_succ_self n.1).two_dvd,
      Nat.mul_div_cancel' (Nat.even_mul_succ_self m.1).two_dvd, ← Nat.pow_succ'] at h2
  obtain ⟨n, hn⟩ := Finite.injective_iff_surjective.1 hinj ⟨r, hr⟩
  exact ⟨n.1, n.2, congrArg Fin.val hn⟩

/-- In a ring of `8 * 2 ^ k` positions, the windows that start at
`p0 + 4 * n * (n + 1)` for `n < 2 ^ k` cover every position. -/
theorem cover_aux (k p0 i : Nat) (hi : i < 8 * 2 ^ k) :
    ∃ n < 2 ^ k, ∃ j < 8, (p0 + 4 * n * (n + 1) + j) % (8 * 2 ^ k) = i := by
  have hpos : 0 < 8 * 2 ^ k := by positivity
  set b := 8 * 2 ^ k with hb
  set q := (i + b - p0 % b) % b with hq
  have hqb : q < b := Nat.mod_lt _ hpos
  have hq8 : q / 8 < 2 ^ k := by omega
  obtain ⟨n, hn, hT⟩ := tri_surj k (q / 8) hq8
  refine ⟨n, hn, q % 8, Nat.mod_lt _ (by norm_num), ?_⟩
  have h8T : 4 * n * (n + 1) = 8 * (n * (n + 1) / 2) := by
    obtain ⟨c, hc⟩ := (Nat.even_mul_succ_self n).two_dvd
    rw [Nat.mul_assoc, hc, Nat.mul_div_cancel_left c (by norm_num)]
    ring
  have hmod : 8 * (n * (n + 1) / 2) % b = 8 * (q / 8) := by
    rw [hb, Nat.mul_mod_mul_left, hT]
  have h1 : 8 * (n * (n + 1) / 2) ≡ 8 * (q / 8) [MOD b] := by
    unfold Nat.ModEq
    rw [hmod, Nat.mod_eq_of_lt (by omega)]
  have h2 := (h1.add_left p0).add_right (q % 8)
  have h3 : p0 + 8 * (q / 8) + q % 8 = p0 + q := by omega
  have hp0 : p0 % b < b := Nat.mod_lt _ hpos
  have hpq : (p0 + q) % b = i := by
    rw [Nat.add_mod, hq, Nat.mod_mod, Nat.add_mod_mod,
      show p0 % b + (i + b - p0 % b) = i + b by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  unfold Nat.ModEq at h2
  rw [h8T, h2, h3, hpq]

/-! ## Probe sequences in closed form -/

/-- The probe sequence, indexed by the window number. -/
def probeSeq (t : Table K V) (hash : UInt64) : Nat → ProbeSeq
  | 0 => probeStart t hash
  | n + 1 => (probeSeq t hash n).next t

/-- Window `n` starts at `h1 + 8 * (1 + 2 + ... + n)`, masked to the table. -/
theorem probeSeq_pos (t : Table K V) (hash : UInt64) (n : Nat) :
    (probeSeq t hash n).pos = (h1 hash + 4 * n * (n + 1)) % t.buckets := by
  suffices h : (probeSeq t hash n).pos = (h1 hash + 4 * n * (n + 1)) % t.buckets ∧
      (probeSeq t hash n).stride = 8 * n from h.1
  induction n with
  | zero => simp [probeSeq, probeStart]
  | succ n ih =>
    obtain ⟨hp, hs⟩ := ih
    simp only [probeSeq, ProbeSeq.next, hp, hs]
    refine ⟨?_, by ring⟩
    rw [Nat.mod_add_mod]
    congr 1
    ring

/-- The window of probe step `n`. -/
def window (t : Table K V) (hash : UInt64) (n : Nat) : List UInt8 :=
  groupAt t (probeSeq t hash n).pos

/-- The bucket that offset `j` of window `n` names. -/
def probeIdx (t : Table K V) (hash : UInt64) (n j : Nat) : Nat :=
  ((probeSeq t hash n).pos + j) % t.buckets

/-- Window `n` names bucket `i` through a byte that is not padding. -/
def InWindow (t : Table K V) (hash : UInt64) (n i : Nat) : Prop :=
  ∃ j < 8, ¬ IsPad t.buckets ((probeSeq t hash n).pos + j) ∧ probeIdx t hash n j = i

/-! ## Groups -/

theorem groupAt_length (t : Table K V) (p : Nat) : (groupAt t p).length = 8 := by
  simp [groupAt]

theorem groupAt_getD (t : Table K V) (p j : Nat) (hj : j < 8) :
    (groupAt t p).getD j EMPTY = t.ctrlAt (p + j) := by
  simp [groupAt, List.getD_eq_getElem?_getD, hj]

theorem mem_groupAt {t : Table K V} {p : Nat} {c : UInt8} :
    c ∈ groupAt t p ↔ ∃ j < 8, t.ctrlAt (p + j) = c := by
  simp [groupAt, List.mem_range]

theorem matchEmpty_iff {t : Table K V} {p : Nat} :
    matchEmpty (groupAt t p) = true ↔ ∃ j < 8, t.ctrlAt (p + j) = EMPTY := by
  simp [matchEmpty, List.any_eq_true, mem_groupAt, isEmpty]

theorem isSpecial_iff {c : UInt8} : isSpecial c = true ↔ ¬ isFull c = true := by
  simp [isSpecial, isFull, UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt]

theorem isSpecial_EMPTY : isSpecial EMPTY = true := by decide

theorem isSpecial_DELETED : isSpecial DELETED = true := by decide

theorem isFull_EMPTY : isFull EMPTY = false := by decide

/-! ## The invariant -/

/-- The part of the invariant that does not mention the two counters. -/
structure Layout (hash : K → UInt64) (t : Table K V) : Prop where
  shape : Shape t.buckets
  ctrl_len : t.ctrl.length = t.buckets + 8
  slots_len : t.slots.length = t.buckets
  mirror : Mirror t
  full_iff : ∀ i, i < t.buckets → (isFull (t.ctrlAt i) = true ↔ (t.slotAt i).isSome = true)
  tag : ∀ i, i < t.buckets → ∀ k v, t.slotAt i = some (k, v) → t.ctrlAt i = h2 (hash k)
  uniq : ∀ i j, i < t.buckets → j < t.buckets → ∀ k v v',
    t.slotAt i = some (k, v) → t.slotAt j = some (k, v') → i = j
  reach : ∀ i, i < t.buckets → ∀ k v, t.slotAt i = some (k, v) →
    ∃ n, InWindow t (hash k) n i ∧ ∀ m, m < n → matchEmpty (window t (hash k) m) = false

/-- A table the Rust code built. -/
structure WF (hash : K → UInt64) (t : Table K V) : Prop extends Layout hash t where
  items_eq : t.items = (toList t).length

/-- No tombstone, and `growth_left` accounts for every item. -/
def Clean (t : Table K V) : Prop :=
  (∀ i, i < t.buckets → isSpecial (t.ctrlAt i) = true → t.ctrlAt i = EMPTY) ∧
  t.growthLeft + t.items = bucketMaskToCapacity (t.buckets - 1)

variable {hash : K → UInt64} {t : Table K V}

theorem Layout.pos (hw : Layout hash t) : 0 < t.buckets := hw.shape.pos

theorem Layout.probe_lt (hw : Layout hash t) (h : UInt64) (n : Nat) :
    (probeSeq t h n).pos < t.buckets := by
  rw [probeSeq_pos]; exact Nat.mod_lt _ hw.pos

theorem Layout.probeIdx_lt (hw : Layout hash t) (h : UInt64) (n j : Nat) :
    probeIdx t h n j < t.buckets := Nat.mod_lt _ hw.pos

theorem Layout.window_getD (hw : Layout hash t) (h : UInt64) (n j : Nat) (hj : j < 8) :
    (window t h n).getD j EMPTY =
      if IsPad t.buckets ((probeSeq t h n).pos + j) then EMPTY
      else t.ctrlAt (probeIdx t h n j) := by
  unfold window probeIdx
  rw [groupAt_getD _ _ _ hj]
  exact hw.mirror _ (by have := hw.probe_lt h n; omega)

theorem matchEmpty_window (t : Table K V) (h : UInt64) (n : Nat) :
    matchEmpty (window t h n) = true ↔
      ∃ j < 8, t.ctrlAt ((probeSeq t h n).pos + j) = EMPTY :=
  matchEmpty_iff

theorem slotAt_none_of_ge {t : Table K V} {i : Nat} (hlen : t.slots.length = t.buckets)
    (hi : t.buckets ≤ i) : t.slotAt i = none := by
  have : t.slots[i]? = none := List.getElem?_eq_none_iff.2 (by omega)
  simp [slotAt, List.getD_eq_getElem?_getD, this]

/-- In a table with fewer than eight buckets every window names every bucket. -/
theorem Layout.inWindow_of_small (hw : Layout hash t) (hb : t.buckets < 8) (h : UInt64)
    (n : Nat) {i : Nat} (hi : i < t.buckets) : InWindow t h n i := by
  have hp := hw.probe_lt h n
  have h8 : 8 % t.buckets = 0 := Nat.mod_eq_zero_of_dvd (hw.shape.dvd_eight hb)
  obtain ⟨p, hpe⟩ : ∃ p, (probeSeq t h n).pos = p := ⟨_, rfl⟩
  rw [hpe] at hp
  unfold InWindow probeIdx
  rw [hpe]
  rcases Nat.lt_or_ge i p with hlt | hge
  · refine ⟨i + 8 - p, by omega, by unfold IsPad; omega, ?_⟩
    rw [show p + (i + 8 - p) = i + 8 by omega, Nat.add_mod, h8, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt hi]
  · refine ⟨i - p, by omega, by unfold IsPad; omega, ?_⟩
    rw [show p + (i - p) = i by omega, Nat.mod_eq_of_lt hi]

/-- In a table with fewer than eight buckets every window has a pad byte. -/
theorem Layout.matchEmpty_of_small (hw : Layout hash t) (hb : t.buckets < 8) (h : UInt64)
    (n : Nat) : matchEmpty (window t h n) = true := by
  have hp := hw.probe_lt h n
  rw [matchEmpty_window t]
  refine ⟨t.buckets - (probeSeq t h n).pos, by omega, ?_⟩
  rw [hw.mirror _ (by omega), if_pos (by unfold IsPad; omega)]

/-- In a table with at least eight buckets the first `buckets / 8` windows
name every bucket. -/
theorem Layout.inWindow_cover (hw : Layout hash t) (hb : 8 ≤ t.buckets) (h : UInt64)
    {i : Nat} (hi : i < t.buckets) : ∃ n < t.buckets / 8, InWindow t h n i := by
  obtain ⟨k, hk⟩ := hw.shape.eq_mul_pow hb
  obtain ⟨n, hn, j, hj, hnj⟩ := cover_aux k (h1 h) i (by omega)
  refine ⟨n, by omega, j, hj, by unfold IsPad; omega, ?_⟩
  unfold probeIdx
  rw [probeSeq_pos, Nat.mod_add_mod, hk]
  exact hnj

/-- A reachable key has a witness window inside the probe fuel. -/
theorem Layout.reach_lt (hw : Layout hash t) {i : Nat} (hi : i < t.buckets) {k : K} {v : V}
    (hs : t.slotAt i = some (k, v)) :
    ∃ n < probeFuel t, InWindow t (hash k) n i ∧
      ∀ m, m < n → matchEmpty (window t (hash k) m) = false := by
  obtain ⟨n, hin, hemp⟩ := hw.reach i hi k v hs
  unfold probeFuel
  rcases Nat.lt_or_ge n (t.buckets / 8 + 1) with hlt | hge
  · exact ⟨n, hlt, hin, hemp⟩
  · rcases Nat.lt_or_ge t.buckets 8 with hb | hb
    · exact ⟨0, by omega, hw.inWindow_of_small hb _ 0 hi, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
    · obtain ⟨n', hn', hin'⟩ := hw.inWindow_cover hb (hash k) hi
      exact ⟨n', by omega, hin', fun m hm => hemp m (by omega)⟩

/-! ## The entry list -/

theorem mem_toList {t : Table K V} {x : K × V} :
    x ∈ toList t ↔ ∃ i < t.buckets, t.slotAt i = some x := by
  simp [toList, List.mem_filterMap, List.mem_range]

/-- The entries of the buckets before `i`. -/
def pre (t : Table K V) (i : Nat) : List (K × V) := (List.range' 0 i).filterMap t.slotAt

/-- The entries of the buckets after `i`. -/
def post (t : Table K V) (i : Nat) : List (K × V) :=
  (List.range' (i + 1) (t.buckets - (i + 1))).filterMap t.slotAt

theorem toList_split (t : Table K V) {i : Nat} (hi : i < t.buckets) :
    toList t = pre t i ++ (t.slotAt i).toList ++ post t i := by
  have h1 : List.range' 0 t.buckets = List.range' 0 i ++ List.range' i (t.buckets - i) := by
    have := @List.range'_append 0 i (t.buckets - i) 1
    simp only [Nat.zero_add, Nat.one_mul] at this
    rw [Nat.add_sub_cancel' hi.le] at this
    exact this.symm
  have h2 : List.range' i (t.buckets - i) = i :: List.range' (i + 1) (t.buckets - (i + 1)) := by
    rw [show t.buckets - i = (t.buckets - (i + 1)) + 1 by omega, List.range'_succ]
  unfold toList pre post
  rw [List.range_eq_range', h1, h2, List.filterMap_append]
  rcases hs : t.slotAt i with _ | x <;> simp [hs]

theorem pre_congr {t t' : Table K V} {i : Nat}
    (h : ∀ j, j < i → t'.slotAt j = t.slotAt j) : pre t' i = pre t i := by
  unfold pre
  apply List.filterMap_congr
  intro j hj
  rw [List.mem_range'] at hj
  obtain ⟨x, hx, rfl⟩ := hj
  exact h _ (by omega)

theorem post_congr {t t' : Table K V} {i : Nat} (hb : t'.buckets = t.buckets)
    (h : ∀ j, i < j → j < t.buckets → t'.slotAt j = t.slotAt j) : post t' i = post t i := by
  unfold post
  rw [hb]
  apply List.filterMap_congr
  intro j hj
  rw [List.mem_range'] at hj
  obtain ⟨x, hx, rfl⟩ := hj
  exact h _ (by omega) (by omega)

theorem slotAt_set_self {t : Table K V} {i : Nat} (hi : i < t.slots.length)
    (o : Option (K × V)) : ({ t with slots := t.slots.set i o } : Table K V).slotAt i = o := by
  simp [slotAt, List.getD_eq_getElem?_getD, List.getElem?_set_self hi]

theorem slotAt_set_ne {t : Table K V} {i j : Nat} (h : j ≠ i) (o : Option (K × V)) :
    ({ t with slots := t.slots.set i o } : Table K V).slotAt j = t.slotAt j := by
  simp [slotAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem ctrlAt_setCtrl (hs : Shape t.buckets) (hlen : t.ctrl.length = t.buckets + 8)
    {i : Nat} (hi : i < t.buckets) (c : UInt8) (p : Nat) :
    (t.setCtrl i c).ctrlAt p = if p = i ∨ p = index2 t.buckets i then c else t.ctrlAt p := by
  have h2 := index2_lt hs hi
  unfold setCtrl ctrlAt
  simp only [List.getD_eq_getElem?_getD]
  by_cases hp2 : p = index2 t.buckets i
  · subst hp2
    rw [List.getElem?_set_self (by rw [List.length_set]; omega)]
    simp
  · rw [List.getElem?_set_ne (Ne.symm hp2)]
    by_cases hp1 : p = i
    · subst hp1
      rw [List.getElem?_set_self (by omega)]
      simp
    · rw [List.getElem?_set_ne (Ne.symm hp1)]
      simp [hp1, hp2]

theorem mirror_setCtrl (hs : Shape t.buckets) (hlen : t.ctrl.length = t.buckets + 8)
    (hm : Mirror t) {i : Nat} (hi : i < t.buckets) (c : UInt8) : Mirror (t.setCtrl i c) := by
  intro p hp
  have hb : (t.setCtrl i c).buckets = t.buckets := rfl
  rw [hb] at hp ⊢
  have hpb : p % t.buckets < t.buckets := Nat.mod_lt _ hs.pos
  rw [ctrlAt_setCtrl hs hlen hi, ctrlAt_setCtrl hs hlen hi]
  have hnp : ¬ IsPad t.buckets (p % t.buckets) := by unfold IsPad; omega
  have e1 := index2_iff hs hi hp
  have e2 := index2_iff hs hi (by omega : p % t.buckets < t.buckets + 8)
  rw [Nat.mod_mod] at e2
  by_cases hpad : IsPad t.buckets p
  · have h1 : ¬ (p = i ∨ p = index2 t.buckets i) := fun h => (e1.1 h).1 hpad
    rw [if_neg h1, if_pos hpad, hm p hp, if_pos hpad]
  · rw [if_neg hpad]
    by_cases hq : p % t.buckets = i
    · have h1 : p = i ∨ p = index2 t.buckets i := e1.2 ⟨hpad, hq⟩
      have h2 : p % t.buckets = i ∨ p % t.buckets = index2 t.buckets i := e2.2 ⟨hnp, hq⟩
      rw [if_pos h1, if_pos h2]
    · have h1 : ¬ (p = i ∨ p = index2 t.buckets i) := fun h => hq (e1.1 h).2
      have h2 : ¬ (p % t.buckets = i ∨ p % t.buckets = index2 t.buckets i) :=
        fun h => hq (e2.1 h).2
      rw [if_neg h1, if_neg h2, hm p hp, if_neg hpad]

/-- Distinct slots hold distinct keys, so the entry list has distinct keys. -/
theorem Layout.nodupKeys_toList (hw : Layout hash t) : NodupKeys (toList t) := by
  unfold NodupKeys
  apply List.Nodup.map_on
  · intro x hx y hy hxy
    obtain ⟨i, hi, hxi⟩ := mem_toList.1 hx
    obtain ⟨j, hj, hyj⟩ := mem_toList.1 hy
    obtain ⟨kx, vx⟩ := x
    obtain ⟨ky, vy⟩ := y
    simp only at hxy
    subst hxy
    have := hw.uniq i j hi hj kx vx vy hxi hyj
    subst this
    rw [hxi] at hyj
    exact Option.some.inj hyj
  · unfold toList
    apply List.Nodup.filterMap _ List.nodup_range
    intro a a' b hb hb'
    rw [Option.mem_def] at hb hb'
    by_cases ha : a < t.buckets
    · by_cases ha' : a' < t.buckets
      · exact hw.uniq a a' ha ha' b.1 b.2 b.2 hb hb'
      · rw [slotAt_none_of_ge hw.slots_len (by omega)] at hb'; cases hb'
    · rw [slotAt_none_of_ge hw.slots_len (by omega)] at hb; cases hb

/-! ## The lookup loops -/

theorem lowestSpecial_groupAt_some {t : Table K V} {p j : Nat}
    (h : lowestSpecial (groupAt t p) = some j) :
    j < 8 ∧ isSpecial (t.ctrlAt (p + j)) = true ∧
      ∀ j', j' < j → isSpecial (t.ctrlAt (p + j')) = false := by
  unfold lowestSpecial at h
  rw [List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hj, hs, hmin⟩ := h
  rw [groupAt_length] at hj
  simp only [groupAt, List.getElem_map, List.getElem_range] at hs hmin
  exact ⟨hj, hs, fun j' hj' => by simpa using hmin j' hj'⟩

theorem matchEmpty_eq_false_of_lowestSpecial_none {g : List UInt8}
    (h : lowestSpecial g = none) : matchEmpty g = false := by
  unfold lowestSpecial at h
  rw [List.findIdx?_eq_none_iff] at h
  rcases hme : matchEmpty g with _ | _
  · rfl
  · exfalso
    unfold matchEmpty at hme
    rw [List.any_eq_true] at hme
    obtain ⟨x, hx, hxe⟩ := hme
    have := h x hx
    rw [isEmpty, beq_iff_eq] at hxe
    subst hxe
    exact absurd this (by decide)

theorem lowestSpecial_ne_none_of_mem {g : List UInt8} {c : UInt8} (hc : c ∈ g)
    (hs : isSpecial c = true) : lowestSpecial g ≠ none := by
  intro h
  unfold lowestSpecial at h
  rw [List.findIdx?_eq_none_iff] at h
  have := h c hc
  rw [hs] at this
  cases this

/-- The first window at or after `s`, within `f` windows, that has a special
byte, with the offset of its lowest special byte. -/
def firstSpecial (t : Table K V) (hash : UInt64) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | f + 1, s =>
    match lowestSpecial (window t hash s) with
    | some j => some (s, j)
    | none => firstSpecial t hash f (s + 1)

theorem firstSpecial_some (t : Table K V) (h : UInt64) :
    ∀ (f s n j : Nat), firstSpecial t h f s = some (n, j) →
      s ≤ n ∧ n < s + f ∧ lowestSpecial (window t h n) = some j ∧
        ∀ m, s ≤ m → m < n → lowestSpecial (window t h m) = none := by
  intro f
  induction f with
  | zero => intro s n j hf; simp [firstSpecial] at hf
  | succ f ih =>
    intro s n j hf
    rcases hls : lowestSpecial (window t h s) with _ | j'
    · simp only [firstSpecial, hls] at hf
      obtain ⟨h1, h2, h3, h4⟩ := ih (s + 1) n j hf
      refine ⟨by omega, by omega, h3, fun m hm hmn => ?_⟩
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact hls
      · exact h4 m hlt hmn
    · simp only [firstSpecial, hls, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨le_rfl, by omega, hls, fun m hm hmn => by omega⟩

theorem firstSpecial_ne_none (t : Table K V) (h : UInt64) :
    ∀ (f s : Nat), (∃ m, m < f ∧ lowestSpecial (window t h (s + m)) ≠ none) →
      firstSpecial t h f s ≠ none := by
  intro f
  induction f with
  | zero => intro s hm; obtain ⟨m, hm, -⟩ := hm; omega
  | succ f ih =>
    intro s hm hf
    rcases hls : lowestSpecial (window t h s) with _ | j'
    · simp only [firstSpecial, hls] at hf
      obtain ⟨m, hmf, hm⟩ := hm
      rcases m with _ | m
      · rw [Nat.add_zero] at hm; exact hm hls
      · exact ih (s + 1) ⟨m, by omega, by rw [Nat.add_assoc, Nat.add_comm 1 m]; exact hm⟩ hf
    · simp [firstSpecial, hls] at hf

theorem findInsertIndexLoop_eq (t : Table K V) (hash : UInt64) :
    ∀ (f s : Nat), findInsertIndexLoop t f (probeSeq t hash s) =
      (firstSpecial t hash f s).map fun nj => fixInsertIndex t (probeIdx t hash nj.1 nj.2) := by
  intro f
  induction f with
  | zero => intro s; rfl
  | succ f ih =>
    intro s
    rcases hls : lowestSpecial (window t hash s) with _ | j
    · unfold window at hls
      simp only [findInsertIndexLoop, firstSpecial, window, hls]
      exact ih (s + 1)
    · unfold window at hls
      simp only [findInsertIndexLoop, firstSpecial, window, hls, Option.map_some]
      rfl

/-- The byte at a non-pad offset of a window is the byte of the bucket it names. -/
theorem Layout.ctrlAt_probe (hw : Layout hash t) (h : UInt64) {n j : Nat} (hj : j < 8)
    (hpad : ¬ IsPad t.buckets ((probeSeq t h n).pos + j)) :
    t.ctrlAt ((probeSeq t h n).pos + j) = t.ctrlAt (probeIdx t h n j) := by
  rw [hw.mirror _ (by have := hw.probe_lt h n; omega), if_neg hpad]
  rfl

/-- With an `EMPTY` bucket somewhere, some window inside the fuel has a
special byte. -/
theorem Layout.firstSpecial_probe (hw : Layout hash t) (h : UInt64) {e : Nat}
    (he : e < t.buckets) (hemp : t.ctrlAt e = EMPTY) :
    firstSpecial t h (probeFuel t) 0 ≠ none := by
  apply firstSpecial_ne_none
  rcases Nat.lt_or_ge t.buckets 8 with hb | hb
  · refine ⟨0, by unfold probeFuel; omega, fun hn => ?_⟩
    have := matchEmpty_eq_false_of_lowestSpecial_none hn
    rw [hw.matchEmpty_of_small hb h 0] at this
    cases this
  · obtain ⟨n, hn, j, hj, hpad, hidx⟩ := hw.inWindow_cover hb h he
    refine ⟨n, by unfold probeFuel; omega, fun hnone => ?_⟩
    have := matchEmpty_eq_false_of_lowestSpecial_none hnone
    rw [Nat.zero_add] at this
    have hme : matchEmpty (window t h n) = true := by
      rw [matchEmpty_window]
      refine ⟨j, hj, ?_⟩
      rw [hw.ctrlAt_probe h hj hpad, hidx, hemp]
    rw [hme] at this
    cases this

/-- The insert index is a special bucket, and the new key is reachable there. -/
theorem Layout.insertIndex_spec (hw : Layout hash t) (h : UInt64) {n j : Nat}
    (hfs : firstSpecial t h (probeFuel t) 0 = some (n, j)) {e : Nat} (he : e < t.buckets)
    (hemp : t.ctrlAt e = EMPTY) :
    fixInsertIndex t (probeIdx t h n j) < t.buckets ∧
      isSpecial (t.ctrlAt (fixInsertIndex t (probeIdx t h n j))) = true ∧
      InWindow t h n (fixInsertIndex t (probeIdx t h n j)) ∧
      ∀ m, m < n → matchEmpty (window t h m) = false := by
  obtain ⟨-, -, hls, hmin⟩ := firstSpecial_some t h _ _ _ _ hfs
  have hnoemp : ∀ m, m < n → matchEmpty (window t h m) = false := fun m hm =>
    matchEmpty_eq_false_of_lowestSpecial_none (hmin m (Nat.zero_le m) hm)
  unfold window at hls
  obtain ⟨hj, hsp, -⟩ := lowestSpecial_groupAt_some hls
  rcases Nat.lt_or_ge t.buckets 8 with hb | hb
  · have hn0 : n = 0 := by
      by_contra hne
      have := matchEmpty_eq_false_of_lowestSpecial_none (hmin 0 (Nat.zero_le 0) (by omega))
      rw [hw.matchEmpty_of_small hb h 0] at this
      cases this
    subst hn0
    unfold fixInsertIndex
    split
    · have hex : lowestSpecial (groupAt t 0) ≠ none :=
        lowestSpecial_ne_none_of_mem (mem_groupAt.2 ⟨e, by omega, rfl⟩)
          (by rw [Nat.zero_add, hemp]; decide)
      rcases hls0 : lowestSpecial (groupAt t 0) with _ | x
      · exact absurd hls0 hex
      · obtain ⟨hx, hsx, hminx⟩ := lowestSpecial_groupAt_some hls0
        have hxe : x ≤ e := by
          by_contra hlt
          have := hminx e (by omega)
          rw [Nat.zero_add, hemp] at this
          cases this
        rw [Nat.zero_add] at hsx
        simp only [Option.getD_some]
        exact ⟨by omega, hsx, hw.inWindow_of_small hb h 0 (by omega), hnoemp⟩
    · rename_i hnfull
      exact ⟨hw.probeIdx_lt h 0 j, isSpecial_iff.2 hnfull,
        hw.inWindow_of_small hb h 0 (hw.probeIdx_lt h 0 j), hnoemp⟩
  · have hpad : ¬ IsPad t.buckets ((probeSeq t h n).pos + j) := by unfold IsPad; omega
    rw [hw.ctrlAt_probe h hj hpad] at hsp
    have hnf : isFull (t.ctrlAt (probeIdx t h n j)) = false := by
      rcases hf : isFull (t.ctrlAt (probeIdx t h n j)) with _ | _
      · rfl
      · exact absurd hf (isSpecial_iff.1 hsp)
    unfold fixInsertIndex
    rw [hnf]
    simp only [Bool.false_eq_true, if_false]
    exact ⟨hw.probeIdx_lt h n j, hsp, ⟨j, hj, hpad, rfl⟩, hnoemp⟩

section Loops
variable [BEq K] [LawfulBEq K]

theorem keyIs_iff (t : Table K V) (i : Nat) (k : K) :
    t.keyIs i k = true ↔ ∃ v, t.slotAt i = some (k, v) := by
  unfold keyIs
  rcases h : t.slotAt i with _ | ⟨k', v⟩
  · simp
  · simp [beq_iff_eq]

omit [LawfulBEq K] in
theorem tagFind_some {t : Table K V} {tag : UInt8} {k : K} {p j : Nat}
    (h : (matchTag tag (groupAt t p)).find? (fun j => t.keyIs ((p + j) % t.buckets) k)
      = some j) :
    j < 8 ∧ t.ctrlAt (p + j) = tag ∧ t.keyIs ((p + j) % t.buckets) k = true := by
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  unfold matchTag at hmem
  rw [List.mem_filter, List.mem_range, groupAt_length] at hmem
  obtain ⟨hj, htag⟩ := hmem
  rw [groupAt_getD _ _ _ hj, beq_iff_eq] at htag
  exact ⟨hj, htag, hp⟩

omit [LawfulBEq K] in
theorem tagFind_none {t : Table K V} {tag : UInt8} {k : K} {p : Nat}
    (h : (matchTag tag (groupAt t p)).find? (fun j => t.keyIs ((p + j) % t.buckets) k)
      = none) :
    ∀ j, j < 8 → t.ctrlAt (p + j) = tag → t.keyIs ((p + j) % t.buckets) k = false := by
  intro j hj htag
  rw [List.find?_eq_none] at h
  have hmem : j ∈ matchTag tag (groupAt t p) := by
    unfold matchTag
    rw [List.mem_filter, List.mem_range, groupAt_length, groupAt_getD _ _ _ hj, htag]
    exact ⟨hj, beq_self_eq_true tag⟩
  simpa using h j hmem

omit [LawfulBEq K] in
theorem findLoop_some (t : Table K V) (hb : 0 < t.buckets) (tag : UInt8) (k : K) :
    ∀ (f : Nat) (p : ProbeSeq) (i : Nat), findLoop t tag k f p = some i →
      i < t.buckets ∧ t.keyIs i k = true := by
  intro f
  induction f with
  | zero => intro p i h; simp [findLoop] at h
  | succ f ih =>
    intro p i h
    simp only [findLoop] at h
    split at h
    · rename_i j hfind
      obtain ⟨-, -, hkey⟩ := tagFind_some hfind
      cases h
      exact ⟨Nat.mod_lt _ hb, hkey⟩
    · split at h
      · cases h
      · exact ih _ _ h

theorem findLoop_none_of_absent (t : Table K V) (hb : 0 < t.buckets) (tag : UInt8) {k : K}
    (habs : ∀ i, i < t.buckets → ∀ v, t.slotAt i ≠ some (k, v)) :
    ∀ (f : Nat) (p : ProbeSeq), findLoop t tag k f p = none := by
  intro f
  induction f with
  | zero => intro p; rfl
  | succ f ih =>
    intro p
    simp only [findLoop]
    split
    · rename_i j hfind
      obtain ⟨-, -, hkey⟩ := tagFind_some hfind
      obtain ⟨v, hv⟩ := (keyIs_iff t _ k).1 hkey
      exact absurd hv (habs _ (Nat.mod_lt _ hb) v)
    · split
      · rfl
      · exact ih _

theorem Layout.findLoop_found (hw : Layout hash t) {k : K} {v : V} {i₀ : Nat}
    (hi₀ : i₀ < t.buckets) (hslot : t.slotAt i₀ = some (k, v)) :
    ∀ (f s m : Nat), m < f →
      (∀ m', m' < m → matchEmpty (window t (hash k) (s + m')) = false) →
      InWindow t (hash k) (s + m) i₀ →
      findLoop t (h2 (hash k)) k f (probeSeq t (hash k) s) = some i₀ := by
  intro f
  induction f with
  | zero => intro s m hm; omega
  | succ f ih =>
    intro s m hm hemp hin
    have hkey : t.keyIs i₀ k = true := (keyIs_iff t i₀ k).2 ⟨v, hslot⟩
    have htag : t.ctrlAt i₀ = h2 (hash k) := hw.tag i₀ hi₀ k v hslot
    simp only [findLoop]
    split
    · rename_i j hfind
      obtain ⟨hj, htagj, hkeyj⟩ := tagFind_some hfind
      obtain ⟨v', hv'⟩ := (keyIs_iff t _ k).1 hkeyj
      rw [hw.uniq _ i₀ (Nat.mod_lt _ hw.pos) hi₀ k v' v hv' hslot]
    · rename_i hfind
      rcases m with _ | m
      · exfalso
        obtain ⟨j₀, hj₀, hpad, hidx⟩ := hin
        rw [Nat.add_zero] at hidx hpad
        have hbyte : t.ctrlAt ((probeSeq t (hash k) s).pos + j₀) = h2 (hash k) := by
          rw [hw.ctrlAt_probe (hash k) hj₀ hpad, hidx, htag]
        have := tagFind_none hfind j₀ hj₀ hbyte
        unfold probeIdx at hidx
        rw [hidx, hkey] at this
        cases this
      · have hne : matchEmpty (window t (hash k) s) = false := by
          have := hemp 0 (by omega); rwa [Nat.add_zero] at this
        unfold window at hne
        rw [hne]
        simp only [Bool.false_eq_true, if_false]
        exact ih (s + 1) m (by omega)
          (fun m' hm' => by rw [Nat.add_assoc, Nat.add_comm 1 m']; exact hemp (m' + 1) (by omega))
          (by rw [Nat.add_assoc, Nat.add_comm 1 m]; exact hin)

theorem Layout.findOrFindInsertLoop_found (hw : Layout hash t) {k : K} {v : V} {i₀ : Nat}
    (hi₀ : i₀ < t.buckets) (hslot : t.slotAt i₀ = some (k, v)) :
    ∀ (f s m : Nat) (cand : Option Nat), m < f →
      (∀ m', m' < m → matchEmpty (window t (hash k) (s + m')) = false) →
      InWindow t (hash k) (s + m) i₀ →
      findOrFindInsertLoop t (h2 (hash k)) k f (probeSeq t (hash k) s) cand = .found i₀ := by
  intro f
  induction f with
  | zero => intro s m cand hm; omega
  | succ f ih =>
    intro s m cand hm hemp hin
    have hkey : t.keyIs i₀ k = true := (keyIs_iff t i₀ k).2 ⟨v, hslot⟩
    have htag : t.ctrlAt i₀ = h2 (hash k) := hw.tag i₀ hi₀ k v hslot
    simp only [findOrFindInsertLoop]
    split
    · rename_i j hfind
      obtain ⟨hj, htagj, hkeyj⟩ := tagFind_some hfind
      obtain ⟨v', hv'⟩ := (keyIs_iff t _ k).1 hkeyj
      rw [hw.uniq _ i₀ (Nat.mod_lt _ hw.pos) hi₀ k v' v hv' hslot]
    · rename_i hfind
      rcases m with _ | m
      · exfalso
        obtain ⟨j₀, hj₀, hpad, hidx⟩ := hin
        rw [Nat.add_zero] at hidx hpad
        have hbyte : t.ctrlAt ((probeSeq t (hash k) s).pos + j₀) = h2 (hash k) := by
          rw [hw.ctrlAt_probe (hash k) hj₀ hpad, hidx, htag]
        have := tagFind_none hfind j₀ hj₀ hbyte
        unfold probeIdx at hidx
        rw [hidx, hkey] at this
        cases this
      · have hne : matchEmpty (window t (hash k) s) = false := by
          have := hemp 0 (by omega); rwa [Nat.add_zero] at this
        unfold window at hne
        rw [hne]
        simp only [Bool.false_eq_true, if_false]
        exact ih (s + 1) m _ (by omega)
          (fun m' hm' => by rw [Nat.add_assoc, Nat.add_comm 1 m']; exact hemp (m' + 1) (by omega))
          (by rw [Nat.add_assoc, Nat.add_comm 1 m]; exact hin)

theorem findOrFindInsertLoop_absent (t : Table K V) (hb : 0 < t.buckets) (hash : UInt64)
    (tag : UInt8) {k : K} (habs : ∀ i, i < t.buckets → ∀ v, t.slotAt i ≠ some (k, v)) :
    ∀ (f s : Nat) (cand : Option Nat),
      findOrFindInsertLoop t tag k f (probeSeq t hash s) cand =
        .insertAt (fixInsertIndex t
          ((cand.or ((firstSpecial t hash f s).map fun nj => probeIdx t hash nj.1 nj.2)).getD 0)) := by
  intro f
  induction f with
  | zero => intro s cand; simp [findOrFindInsertLoop, firstSpecial]
  | succ f ih =>
    intro s cand
    have hfind : (matchTag tag (groupAt t (probeSeq t hash s).pos)).find?
        (fun j => t.keyIs (((probeSeq t hash s).pos + j) % t.buckets) k) = none := by
      rw [List.find?_eq_none]
      intro j _ hj
      obtain ⟨v, hv⟩ := (keyIs_iff t _ k).1 hj
      exact habs _ (Nat.mod_lt _ hb) v hv
    rcases hls : lowestSpecial (window t hash s) with _ | j
    · unfold window at hls
      have hne := matchEmpty_eq_false_of_lowestSpecial_none hls
      cases cand <;>
        simp only [findOrFindInsertLoop, firstSpecial, window, hls, hfind, hne, Option.map_none,
          Bool.false_eq_true, if_false] <;>
        exact ih (s + 1) _
    · unfold window at hls
      cases cand <;> simp only [findOrFindInsertLoop, firstSpecial, window, hls, hfind,
          Option.map_some, Option.none_or, Option.some_or]
      · split
        · rfl
        · rw [show ProbeSeq.next t (probeSeq t hash s) = probeSeq t hash (s + 1) from rfl,
            ih (s + 1) (some _)]
          simp only [Option.some_or]
          rfl
      · split
        · rfl
        · rw [show ProbeSeq.next t (probeSeq t hash s) = probeSeq t hash (s + 1) from rfl,
            ih (s + 1) (some _)]
          simp only [Option.some_or]

/-- A key in the table is found at its bucket. -/
theorem Layout.find_of_slot (hw : Layout hash t) {i : Nat} (hi : i < t.buckets) {k : K} {v : V}
    (hs : t.slotAt i = some (k, v)) : find t (hash k) k = some i := by
  obtain ⟨n, hn, hin, hemp⟩ := hw.reach_lt hi hs
  exact hw.findLoop_found hi hs (probeFuel t) 0 n hn
    (fun m' hm' => by simpa using hemp m' hm') (by simpa using hin)

/-- A found bucket holds the key. -/
theorem Layout.slot_of_find (hw : Layout hash t) {k : K} {i : Nat}
    (h : find t (hash k) k = some i) : i < t.buckets ∧ ∃ v, t.slotAt i = some (k, v) := by
  obtain ⟨hi, hkey⟩ := findLoop_some t hw.pos _ k _ _ _ h
  exact ⟨hi, (keyIs_iff t i k).1 hkey⟩

theorem Layout.find_eq_none_iff (hw : Layout hash t) (k : K) :
    find t (hash k) k = none ↔ ∀ i, i < t.buckets → ∀ v, t.slotAt i ≠ some (k, v) := by
  constructor
  · intro h i hi v hs
    rw [hw.find_of_slot hi hs] at h
    cases h
  · intro habs
    rcases h : find t (hash k) k with _ | i
    · rfl
    · obtain ⟨hi, v, hv⟩ := hw.slot_of_find h
      exact absurd hv (habs i hi v)

theorem Layout.findOrFindInsert_found (hw : Layout hash t) {i : Nat} (hi : i < t.buckets)
    {k : K} {v : V} (hs : t.slotAt i = some (k, v)) :
    findOrFindInsertIndex t (hash k) k = .found i := by
  obtain ⟨n, hn, hin, hemp⟩ := hw.reach_lt hi hs
  exact hw.findOrFindInsertLoop_found hi hs (probeFuel t) 0 n none hn
    (fun m' hm' => by simpa using hemp m' hm') (by simpa using hin)

/-- For an absent key the lookup returns the insert index of `findInsertIndex`. -/
theorem Layout.findOrFindInsert_absent (hw : Layout hash t) {k : K}
    (habs : ∀ i, i < t.buckets → ∀ v, t.slotAt i ≠ some (k, v)) {e : Nat} (he : e < t.buckets)
    (hemp : t.ctrlAt e = EMPTY) :
    ∃ n j, firstSpecial t (hash k) (probeFuel t) 0 = some (n, j) ∧
      findInsertIndex t (hash k) = fixInsertIndex t (probeIdx t (hash k) n j) ∧
      findOrFindInsertIndex t (hash k) k = .insertAt (findInsertIndex t (hash k)) := by
  rcases hfs : firstSpecial t (hash k) (probeFuel t) 0 with _ | ⟨n, j⟩
  · exact absurd hfs (hw.firstSpecial_probe (hash k) he hemp)
  · refine ⟨n, j, rfl, ?_, ?_⟩
    · unfold findInsertIndex
      rw [show probeStart t (hash k) = probeSeq t (hash k) 0 from rfl, findInsertIndexLoop_eq, hfs]
      rfl
    · unfold findOrFindInsertIndex findInsertIndex
      rw [show probeStart t (hash k) = probeSeq t (hash k) 0 from rfl,
        findOrFindInsertLoop_absent t hw.pos (hash k) _ habs, findInsertIndexLoop_eq, hfs]
      rfl

end Loops

/-! ## The list model under permutation

`CodeLib.RustStd.HashMap.Basic` keeps its lemmas to the shapes the codec
needs.  The table stores its entries in bucket order, so the refinement
compares lists up to permutation.  These lemmas stay here until a second
consumer moves them. -/

section ListModel
variable [BEq K] [LawfulBEq K]

omit [BEq K] [LawfulBEq K] in
theorem nodupKeys_eq_of_fst {l : List (K × V)} (h : NodupKeys l) {x y : K × V}
    (hx : x ∈ l) (hy : y ∈ l) (hk : x.1 = y.1) : x = y :=
  List.inj_on_of_nodup_map h hx hy hk

theorem find?_key_perm {l m : List (K × V)} (hp : l.Perm m) (hn : NodupKeys m) (k : K) :
    l.find? (fun e => e.1 == k) = m.find? (fun e => e.1 == k) := by
  rcases hl : l.find? (fun e => e.1 == k) with _ | x
  · rw [hl]
    symm
    rw [List.find?_eq_none] at hl ⊢
    intro y hy
    exact hl y (hp.mem_iff.2 hy)
  · have hx := List.mem_of_find?_eq_some hl
    have hpx := List.find?_some hl
    rcases hm : m.find? (fun e => e.1 == k) with _ | y
    · rw [List.find?_eq_none] at hm
      exact absurd hpx (hm x (hp.mem_iff.1 hx))
    · have hy := List.mem_of_find?_eq_some hm
      have hpy := List.find?_some hm
      rw [beq_iff_eq] at hpx hpy
      rw [hl, hm, nodupKeys_eq_of_fst hn (hp.mem_iff.1 hx) hy (hpx.trans hpy.symm)]

theorem get_perm {l m : List (K × V)} (hp : l.Perm m) (hn : NodupKeys m) (k : K) :
    HashMap.get l k = HashMap.get m k := by
  unfold HashMap.get
  rw [find?_key_perm hp hn]

theorem containsKey_perm {l m : List (K × V)} (hp : l.Perm m) (hn : NodupKeys m) (k : K) :
    HashMap.containsKey l k = HashMap.containsKey m k := by
  unfold HashMap.containsKey
  rw [find?_key_perm hp hn]

theorem insert_perm {l m : List (K × V)} (hp : l.Perm m) (hn : NodupKeys m) (k : K) (v : V) :
    (HashMap.insert l k v).1 = (HashMap.insert m k v).1 ∧
      ((HashMap.insert l k v).2).Perm (HashMap.insert m k v).2 := by
  unfold HashMap.insert
  rw [find?_key_perm hp hn]
  rcases hm : m.find? (fun e => e.1 == k) with _ | x
  · simp only [hm]
    exact ⟨trivial, hp.append_right _⟩
  · simp only [hm]
    exact ⟨trivial, hp.map _⟩

theorem remove_perm {l m : List (K × V)} (hp : l.Perm m) (hn : NodupKeys m) (k : K) :
    (HashMap.remove l k).1 = (HashMap.remove m k).1 ∧
      ((HashMap.remove l k).2).Perm (HashMap.remove m k).2 := by
  unfold HashMap.remove
  exact ⟨get_perm hp hn k, hp.filter _⟩

theorem find?_key_found {l₁ : List (K × V)} (l₂ : List (K × V)) {k : K} (v' : V)
    (h₁ : ∀ x ∈ l₁, x.1 ≠ k) :
    (l₁ ++ (k, v') :: l₂).find? (fun e => e.1 == k) = some (k, v') := by
  rw [List.find?_append, List.find?_eq_none.2 (fun x hx => by simpa using h₁ x hx),
    Option.none_or, List.find?_cons_of_pos (by simp)]

theorem find?_key_absent {l : List (K × V)} {k : K} (h : ∀ x ∈ l, x.1 ≠ k) :
    l.find? (fun e => e.1 == k) = none :=
  List.find?_eq_none.2 (fun x hx => by simpa using h x hx)

theorem get_list_found {l₁ : List (K × V)} (l₂ : List (K × V)) {k : K} (v' : V)
    (h₁ : ∀ x ∈ l₁, x.1 ≠ k) :
    HashMap.get (l₁ ++ (k, v') :: l₂) k = some v' := by
  unfold HashMap.get
  rw [find?_key_found l₂ v' h₁]
  rfl

theorem get_list_absent {l : List (K × V)} {k : K} (h : ∀ x ∈ l, x.1 ≠ k) :
    HashMap.get l k = none := by
  unfold HashMap.get
  rw [find?_key_absent h]
  rfl

theorem containsKey_list_found {l₁ : List (K × V)} (l₂ : List (K × V)) {k : K} (v' : V)
    (h₁ : ∀ x ∈ l₁, x.1 ≠ k) :
    HashMap.containsKey (l₁ ++ (k, v') :: l₂) k = true := by
  unfold HashMap.containsKey
  rw [find?_key_found l₂ v' h₁]
  rfl

theorem containsKey_list_absent {l : List (K × V)} {k : K} (h : ∀ x ∈ l, x.1 ≠ k) :
    HashMap.containsKey l k = false := by
  unfold HashMap.containsKey
  rw [find?_key_absent h]
  rfl

theorem insert_list_found {l₁ l₂ : List (K × V)} {k : K} (v' v : V)
    (h₁ : ∀ x ∈ l₁, x.1 ≠ k) (h₂ : ∀ x ∈ l₂, x.1 ≠ k) :
    HashMap.insert (l₁ ++ (k, v') :: l₂) k v = (some v', l₁ ++ (k, v) :: l₂) := by
  have e1 : l₁.map (fun e : K × V => if e.1 == k then (k, v) else e) = l₁ := by
    rw [List.map_congr_left (g := id) (fun x hx => by simp [h₁ x hx]), List.map_id]
  have e2 : l₂.map (fun e : K × V => if e.1 == k then (k, v) else e) = l₂ := by
    rw [List.map_congr_left (g := id) (fun x hx => by simp [h₂ x hx]), List.map_id]
  unfold HashMap.insert
  rw [find?_key_found l₂ v' h₁, List.map_append, List.map_cons, e1, e2]
  simp

theorem insert_list_absent {l : List (K × V)} {k : K} (h : ∀ x ∈ l, x.1 ≠ k) (v : V) :
    HashMap.insert l k v = (none, l ++ [(k, v)]) := by
  unfold HashMap.insert
  rw [find?_key_absent h]

theorem remove_list_found {l₁ l₂ : List (K × V)} {k : K} (v' : V)
    (h₁ : ∀ x ∈ l₁, x.1 ≠ k) (h₂ : ∀ x ∈ l₂, x.1 ≠ k) :
    HashMap.remove (l₁ ++ (k, v') :: l₂) k = (some v', l₁ ++ l₂) := by
  unfold HashMap.remove
  rw [get_list_found l₂ v' h₁, List.filter_append, List.filter_cons_of_neg (by simp),
    List.filter_eq_self.2 (fun x hx => by simp [h₁ x hx]),
    List.filter_eq_self.2 (fun x hx => by simp [h₂ x hx])]

theorem remove_list_absent {l : List (K × V)} {k : K} (h : ∀ x ∈ l, x.1 ≠ k) :
    HashMap.remove l k = (none, l) := by
  unfold HashMap.remove
  rw [get_list_absent h, List.filter_eq_self.2 (fun x hx => by simp [h x hx])]

end ListModel

/-! ## Tags -/

theorem isFull_h2 (h : UInt64) : isFull (h2 h) = true := by
  unfold isFull h2
  rw [decide_eq_true_eq, UInt8.lt_iff_toNat_lt, UInt64.toNat_toUInt8, UInt64.toNat_and]
  have hle : (h >>> 25).toNat &&& (0x7f : UInt64).toNat ≤ (0x7f : UInt64).toNat :=
    Nat.and_le_right
  have e1 : (0x7f : UInt64).toNat = 127 := rfl
  have e2 : (0x80 : UInt8).toNat = 128 := rfl
  rw [e1] at hle ⊢
  rw [e2]
  omega

theorem h2_ne_EMPTY (h : UInt64) : h2 h ≠ EMPTY := by
  intro he
  have := isFull_h2 h
  rw [he, isFull_EMPTY] at this
  cases this

theorem isSpecial_h2 (h : UInt64) : isSpecial (h2 h) = false := by
  rw [Bool.eq_false_iff]
  intro hs
  exact isSpecial_iff.1 hs (isFull_h2 h)

theorem isEmpty_iff {c : UInt8} : isEmpty c = true ↔ c = EMPTY := by
  unfold isEmpty
  exact beq_iff_eq

theorem isEmpty_h2 (h : UInt64) : isEmpty (h2 h) = false := by
  unfold isEmpty
  exact beq_eq_false_iff_ne.2 (h2_ne_EMPTY h)

/-! ## Congruences -/

theorem probeSeq_congr (t t' : Table K V) (hb : t'.buckets = t.buckets) (h : UInt64) :
    ∀ n, probeSeq t' h n = probeSeq t h n := by
  intro n
  induction n with
  | zero => simp [probeSeq, probeStart, hb]
  | succ n ih => simp [probeSeq, ProbeSeq.next, ih, hb]

theorem inWindow_congr (t t' : Table K V) (hb : t'.buckets = t.buckets) (h : UInt64)
    (n i : Nat) : InWindow t' h n i ↔ InWindow t h n i := by
  unfold InWindow probeIdx
  rw [probeSeq_congr t t' hb, hb]

theorem window_congr (t t' : Table K V) (hb : t'.buckets = t.buckets)
    (hc : ∀ p, t'.ctrlAt p = t.ctrlAt p) (h : UInt64) (n : Nat) :
    window t' h n = window t h n := by
  unfold window groupAt
  rw [probeSeq_congr t t' hb]
  exact List.map_congr_left (fun j _ => hc _)

/-- A table with new counters. -/
def withCounters (t : Table K V) (a g : Nat) : Table K V :=
  { t with items := a, growthLeft := g }

theorem Layout.counters (hw : Layout hash t) (a g : Nat) :
    Layout hash (withCounters t a g) := by
  set t' : Table K V := withCounters t a g with ht'
  have hb : t'.buckets = t.buckets := rfl
  refine ⟨hw.shape, hw.ctrl_len, hw.slots_len, hw.mirror, hw.full_iff, hw.tag, hw.uniq, ?_⟩
  intro i hi k v hs
  obtain ⟨n, hin, hemp⟩ := hw.reach i hi k v hs
  refine ⟨n, (inWindow_congr t t' hb _ _ _).2 hin, fun m hm => ?_⟩
  rw [window_congr t t' hb (fun _ => rfl)]
  exact hemp m hm

theorem toList_counters (t : Table K V) (a g : Nat) :
    toList (withCounters t a g) = toList t := rfl

theorem ctrlAt_setCtrl_self (hs : Shape t.buckets) (hlen : t.ctrl.length = t.buckets + 8)
    {i : Nat} (hi : i < t.buckets) (c : UInt8) : (t.setCtrl i c).ctrlAt i = c := by
  rw [ctrlAt_setCtrl hs hlen hi, if_pos (Or.inl rfl)]

theorem ctrlAt_setCtrl_ne (hs : Shape t.buckets) (hlen : t.ctrl.length = t.buckets + 8)
    {i : Nat} (hi : i < t.buckets) (c : UInt8) {p : Nat} (hp : p < t.buckets) (hne : p ≠ i) :
    (t.setCtrl i c).ctrlAt p = t.ctrlAt p := by
  rw [ctrlAt_setCtrl hs hlen hi, if_neg]
  intro hor
  have := (index2_iff hs hi (by omega)).1 hor
  rw [Nat.mod_eq_of_lt hp] at this
  exact hne this.2

theorem Layout.slotAt_eq_none (hw : Layout hash t) {i : Nat} (hi : i < t.buckets)
    (hsp : isSpecial (t.ctrlAt i) = true) : t.slotAt i = none := by
  rcases hs : t.slotAt i with _ | x
  · rfl
  · exact absurd ((hw.full_iff i hi).2 (by rw [hs]; rfl)) (isSpecial_iff.1 hsp)

/-! ## The entries around one bucket -/

theorem mem_pre {t : Table K V} {i : Nat} {x : K × V} :
    x ∈ pre t i ↔ ∃ j, j < i ∧ t.slotAt j = some x := by
  unfold pre
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, hjx⟩
    rw [List.mem_range'] at hj
    obtain ⟨m, hm, rfl⟩ := hj
    exact ⟨0 + 1 * m, by omega, hjx⟩
  · rintro ⟨j, hj, hjx⟩
    exact ⟨j, List.mem_range'.2 ⟨j, hj, by omega⟩, hjx⟩

theorem mem_post {t : Table K V} {i : Nat} {x : K × V} :
    x ∈ post t i ↔ ∃ j, i < j ∧ j < t.buckets ∧ t.slotAt j = some x := by
  unfold post
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, hjx⟩
    rw [List.mem_range'] at hj
    obtain ⟨m, hm, rfl⟩ := hj
    exact ⟨i + 1 + 1 * m, by omega, by omega, hjx⟩
  · rintro ⟨j, hj, hjb, hjx⟩
    exact ⟨j, List.mem_range'.2 ⟨j - (i + 1), by omega, by omega⟩, hjx⟩

theorem Layout.toList_eq_of_slot (hw : Layout hash t) {i : Nat} (hi : i < t.buckets) {k : K}
    {v : V} (hs : t.slotAt i = some (k, v)) :
    toList t = pre t i ++ (k, v) :: post t i ∧
      (∀ x ∈ pre t i, x.1 ≠ k) ∧ (∀ x ∈ post t i, x.1 ≠ k) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [toList_split t hi, hs, List.append_assoc]
    rfl
  · intro x hx hxk
    obtain ⟨j, hj, hjx⟩ := mem_pre.1 hx
    obtain ⟨kx, vx⟩ := x
    simp only at hxk
    subst hxk
    have := hw.uniq j i (by omega) hi kx vx v hjx hs
    omega
  · intro x hx hxk
    obtain ⟨j, hj, hjb, hjx⟩ := mem_post.1 hx
    obtain ⟨kx, vx⟩ := x
    simp only at hxk
    subst hxk
    have := hw.uniq j i hjb hi kx vx v hjx hs
    omega

theorem toList_absent {t : Table K V} {k : K}
    (habs : ∀ j, j < t.buckets → ∀ v', t.slotAt j ≠ some (k, v')) :
    ∀ x ∈ toList t, x.1 ≠ k := by
  intro x hx hxk
  obtain ⟨j, hj, hjx⟩ := mem_toList.1 hx
  obtain ⟨kx, vx⟩ := x
  simp only at hxk
  subst hxk
  exact habs j hj vx hjx

theorem length_filterMap_range' {α : Type} (f : Nat → Option α) :
    ∀ (n s : Nat), (∀ i, s ≤ i → i < s + n → (f i).isSome = true) →
      ((List.range' s n).filterMap f).length = n := by
  intro n
  induction n with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s hs
    rw [List.range'_succ, List.filterMap_cons]
    rcases hf : f s with _ | x
    · have := hs s le_rfl (by omega)
      rw [hf] at this
      cases this
    · simp only [List.length_cons]
      rw [ih (s + 1) (fun i h1 h2 => hs i (by omega) (by omega))]

/-- A table with room has an `EMPTY` byte. -/
theorem WF.exists_empty (hw : WF hash t) (hcl : Clean t) (hg : 1 ≤ t.growthLeft) :
    ∃ e, e < t.buckets ∧ t.ctrlAt e = EMPTY := by
  by_contra hno
  have hfull : ∀ i, i < t.buckets → (t.slotAt i).isSome = true := by
    intro i hi
    rw [← hw.full_iff i hi]
    rcases hf : isFull (t.ctrlAt i) with _ | _
    · exfalso
      have hsp : isSpecial (t.ctrlAt i) = true := isSpecial_iff.2 (by rw [hf]; decide)
      exact hno ⟨i, hi, hcl.1 i hi hsp⟩
    · rfl
  have hlen : (toList t).length = t.buckets := by
    unfold toList
    rw [List.range_eq_range']
    exact length_filterMap_range' t.slotAt t.buckets 0 (fun i _ hi => hfull i (by omega))
  have h1 := hw.shape.cap_lt
  have h2 := hw.items_eq
  have h3 := hcl.2
  omega

/-! ## Placing an entry -/

/-- The shared write of `insert_at_index` and of the `resize` step: the tag at
`i` and its mirror, and the entry in slot `i`. -/
def place (t : Table K V) (i : Nat) (tag : UInt8) (kv : K × V) : Table K V :=
  let t := t.setCtrl i tag
  { t with slots := t.slots.set i (some kv) }

theorem insertAt_eq (t : Table K V) (i : Nat) (tag : UInt8) (kv : K × V) :
    insertAt t i tag kv =
      withCounters (place t i tag kv) (t.items + 1)
        (t.growthLeft - (if isEmpty (t.ctrlAt i) then 1 else 0)) := rfl

theorem slotAt_place_self {t : Table K V} {i : Nat} (hi : i < t.slots.length) (tag : UInt8)
    (kv : K × V) : (place t i tag kv).slotAt i = some kv :=
  slotAt_set_self (t := t.setCtrl i tag) hi _

theorem slotAt_place_ne {t : Table K V} {i j : Nat} (h : j ≠ i) (tag : UInt8) (kv : K × V) :
    (place t i tag kv).slotAt j = t.slotAt j :=
  slotAt_set_ne (t := t.setCtrl i tag) h _

theorem toList_place (hw : Layout hash t) {i : Nat} (hi : i < t.buckets)
    (hnone : t.slotAt i = none) (tag : UInt8) (kv : K × V) :
    (toList (place t i tag kv)).Perm (kv :: toList t) := by
  have h1 : pre (place t i tag kv) i = pre t i :=
    pre_congr (fun j hj => slotAt_place_ne (by omega) _ _)
  have h2 : post (place t i tag kv) i = post t i :=
    post_congr rfl (fun j hj _ => slotAt_place_ne (by omega) _ _)
  have h3 : (place t i tag kv).slotAt i = some kv :=
    slotAt_place_self (by rw [hw.slots_len]; exact hi) _ _
  rw [toList_split (place t i tag kv) hi, toList_split t hi, h1, h2, hnone, h3]
  show (pre t i ++ [kv] ++ post t i).Perm (kv :: (pre t i ++ [] ++ post t i))
  rw [List.append_nil, List.append_assoc, List.singleton_append]
  exact List.perm_middle

/-- Placing a fresh key at a special bucket that its probe reaches keeps the
layout. -/
theorem Layout.place (hw : Layout hash t) {i : Nat} (hi : i < t.buckets) {k : K} (v : V)
    (habs : ∀ j, j < t.buckets → ∀ v', t.slotAt j ≠ some (k, v'))
    {n : Nat} (hin : InWindow t (hash k) n i)
    (hemp : ∀ m, m < n → matchEmpty (window t (hash k) m) = false) :
    Layout hash (Table.place t i (h2 (hash k)) (k, v)) := by
  have hb : (Table.place t i (h2 (hash k)) (k, v)).buckets = t.buckets := rfl
  have hctrl : ∀ p, (Table.place t i (h2 (hash k)) (k, v)).ctrlAt p =
      if p = i ∨ p = index2 t.buckets i then h2 (hash k) else t.ctrlAt p :=
    fun p => ctrlAt_setCtrl hw.shape hw.ctrl_len hi _ p
  have hctrl_ne : ∀ p, p < t.buckets → p ≠ i →
      (Table.place t i (h2 (hash k)) (k, v)).ctrlAt p = t.ctrlAt p :=
    fun p hp hne => ctrlAt_setCtrl_ne hw.shape hw.ctrl_len hi _ hp hne
  have hctrl_self : (Table.place t i (h2 (hash k)) (k, v)).ctrlAt i = h2 (hash k) :=
    ctrlAt_setCtrl_self hw.shape hw.ctrl_len hi _
  have hslot_self : (Table.place t i (h2 (hash k)) (k, v)).slotAt i = some (k, v) :=
    slotAt_place_self (by rw [hw.slots_len]; exact hi) _ _
  have hslot_ne : ∀ j, j ≠ i → (Table.place t i (h2 (hash k)) (k, v)).slotAt j = t.slotAt j :=
    fun j hj => slotAt_place_ne hj _ _
  have hwin : ∀ (h : UInt64) (m : Nat), matchEmpty (window t h m) = false →
      matchEmpty (window (Table.place t i (h2 (hash k)) (k, v)) h m) = false := by
    intro h m hm
    rw [Bool.eq_false_iff] at hm ⊢
    intro hme
    apply hm
    rw [matchEmpty_window] at hme ⊢
    obtain ⟨j, hj, hj'⟩ := hme
    rw [probeSeq_congr t _ hb, hctrl] at hj'
    split_ifs at hj' with hc
    · exact absurd hj' (h2_ne_EMPTY _)
    · exact ⟨j, hj, hj'⟩
  refine ⟨hw.shape, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((t.ctrl.set i _).set _ _).length = t.buckets + 8
    rw [List.length_set, List.length_set, hw.ctrl_len]
  · show (t.slots.set i _).length = t.buckets
    rw [List.length_set, hw.slots_len]
  · exact mirror_setCtrl hw.shape hw.ctrl_len hw.mirror hi _
  · intro p hp
    rw [hb] at hp
    by_cases hpi : p = i
    · rw [hpi, hctrl_self, hslot_self, isFull_h2]
      simp
    · rw [hctrl_ne p hp hpi, hslot_ne p hpi]
      exact hw.full_iff p hp
  · intro p hp k' v' hs
    rw [hb] at hp
    by_cases hpi : p = i
    · rw [hpi] at hs ⊢
      rw [hslot_self] at hs
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs)
      exact hctrl_self
    · rw [hslot_ne p hpi] at hs
      rw [hctrl_ne p hp hpi]
      exact hw.tag p hp k' v' hs
  · intro p q hp hq k' v₁ v₂ hs₁ hs₂
    rw [hb] at hp hq
    by_cases hpi : p = i
    · by_cases hqi : q = i
      · rw [hpi, hqi]
      · exfalso
        rw [hpi, hslot_self] at hs₁
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs₁)
        rw [hslot_ne q hqi] at hs₂
        exact habs q hq v₂ hs₂
    · by_cases hqi : q = i
      · exfalso
        rw [hqi, hslot_self] at hs₂
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs₂)
        rw [hslot_ne p hpi] at hs₁
        exact habs p hp v₁ hs₁
      · rw [hslot_ne p hpi] at hs₁
        rw [hslot_ne q hqi] at hs₂
        exact hw.uniq p q hp hq k' v₁ v₂ hs₁ hs₂
  · intro p hp k' v' hs
    rw [hb] at hp
    by_cases hpi : p = i
    · rw [hpi] at hs ⊢
      rw [hslot_self] at hs
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hs)
      exact ⟨n, (inWindow_congr t _ hb _ _ _).2 hin, fun m hm => hwin _ m (hemp m hm)⟩
    · rw [hslot_ne p hpi] at hs
      obtain ⟨n', hin', hemp'⟩ := hw.reach p hp k' v' hs
      exact ⟨n', (inWindow_congr t _ hb _ _ _).2 hin', fun m hm => hwin _ m (hemp' m hm)⟩

/-- `insert_at_index` of a fresh key keeps `WF` and adds the entry. -/
theorem WF.insertAt (hw : WF hash t) {i : Nat} (hi : i < t.buckets)
    (hsp : isSpecial (t.ctrlAt i) = true) {k : K} (v : V)
    (habs : ∀ j, j < t.buckets → ∀ v', t.slotAt j ≠ some (k, v'))
    {n : Nat} (hin : InWindow t (hash k) n i)
    (hemp : ∀ m, m < n → matchEmpty (window t (hash k) m) = false) :
    WF hash (insertAt t i (h2 (hash k)) (k, v)) ∧
      (toList (insertAt t i (h2 (hash k)) (k, v))).Perm ((k, v) :: toList t) := by
  have hl := hw.toLayout.place hi v habs hin hemp
  have hperm := toList_place hw.toLayout hi (hw.toLayout.slotAt_eq_none hi hsp) (h2 (hash k)) (k, v)
  rw [insertAt_eq, toList_counters]
  refine ⟨⟨hl.counters _ _, ?_⟩, hperm⟩
  show t.items + 1 = (toList (Table.place t i (h2 (hash k)) (k, v))).length
  rw [hw.items_eq, hperm.length_eq, List.length_cons]

/-- Replacing the value of a present key keeps the layout. -/
theorem Layout.replace (hw : Layout hash t) {i : Nat} (hi : i < t.buckets) {k : K} {v' : V}
    (hs : t.slotAt i = some (k, v')) (v : V) :
    Layout hash { t with slots := t.slots.set i (some (k, v)) } := by
  set t' : Table K V := { t with slots := t.slots.set i (some (k, v)) } with ht'
  have hb : t'.buckets = t.buckets := rfl
  have hslot_self : t'.slotAt i = some (k, v) :=
    slotAt_set_self (by rw [hw.slots_len]; exact hi) _
  have hslot_ne : ∀ j, j ≠ i → t'.slotAt j = t.slotAt j := fun j hj => slotAt_set_ne hj _
  have hctrl : ∀ p, t'.ctrlAt p = t.ctrlAt p := fun p => rfl
  have key : ∀ r, r < t.buckets → ∀ k' w, t'.slotAt r = some (k', w) →
      ∃ w', t.slotAt r = some (k', w') := by
    intro r hr k' w hw'
    by_cases hri : r = i
    · rw [hri] at hw' ⊢
      rw [hslot_self] at hw'
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hw')
      exact ⟨v', hs⟩
    · rw [hslot_ne r hri] at hw'
      exact ⟨w, hw'⟩
  refine ⟨hw.shape, hw.ctrl_len, ?_, hw.mirror, ?_, ?_, ?_, ?_⟩
  · show (t.slots.set i _).length = t.buckets
    rw [List.length_set, hw.slots_len]
  · intro p hp
    rw [hctrl]
    by_cases hpi : p = i
    · rw [hpi, hslot_self]
      have := (hw.full_iff i hi).2 (by rw [hs]; rfl)
      rw [this]
      simp
    · rw [hslot_ne p hpi]
      exact hw.full_iff p hp
  · intro p hp k' w hs₁
    rw [hctrl]
    obtain ⟨w', hw'⟩ := key p hp k' w hs₁
    exact hw.tag p hp k' w' hw'
  · intro p q hp hq k' v₁ v₂ hs₁ hs₂
    obtain ⟨w₁, hw₁⟩ := key p hp k' v₁ hs₁
    obtain ⟨w₂, hw₂⟩ := key q hq k' v₂ hs₂
    exact hw.uniq p q hp hq k' w₁ w₂ hw₁ hw₂
  · intro p hp k' w hs₁
    obtain ⟨w', hw'⟩ := key p hp k' w hs₁
    obtain ⟨n, hin, hemp⟩ := hw.reach p hp k' w' hw'
    refine ⟨n, (inWindow_congr t t' hb _ _ _).2 hin, fun m hm => ?_⟩
    rw [window_congr t t' hb hctrl]
    exact hemp m hm

/-! ## The map operations on a table with room -/

theorem reserve_eq_self (hash : K → UInt64) (t : Table K V) {a : Nat}
    (h : a ≤ t.growthLeft) : reserve hash t a = t := by
  unfold reserve
  rw [if_pos h]

section Ops
variable [BEq K] [LawfulBEq K]

theorem Layout.get_eq (hw : Layout hash t) (k : K) :
    Table.get hash t k = HashMap.get (toList t) k := by
  by_cases hpres : ∃ i, i < t.buckets ∧ ∃ v', t.slotAt i = some (k, v')
  · obtain ⟨i, hi, v', hs⟩ := hpres
    obtain ⟨hl, hpre, hpost⟩ := hw.toList_eq_of_slot hi hs
    rw [hl, get_list_found _ v' hpre]
    unfold Table.get
    rw [hw.find_of_slot hi hs]
    show (t.slotAt i).map Prod.snd = some v'
    rw [hs]
    rfl
  · have habs : ∀ j, j < t.buckets → ∀ v', t.slotAt j ≠ some (k, v') :=
      fun j hj v' hs => hpres ⟨j, hj, v', hs⟩
    rw [get_list_absent (toList_absent habs)]
    unfold Table.get
    rw [(hw.find_eq_none_iff k).2 habs]
    rfl

theorem Layout.containsKey_eq (hw : Layout hash t) (k : K) :
    Table.containsKey hash t k = HashMap.containsKey (toList t) k := by
  by_cases hpres : ∃ i, i < t.buckets ∧ ∃ v', t.slotAt i = some (k, v')
  · obtain ⟨i, hi, v', hs⟩ := hpres
    obtain ⟨hl, hpre, hpost⟩ := hw.toList_eq_of_slot hi hs
    rw [hl, containsKey_list_found _ v' hpre]
    unfold Table.containsKey
    rw [hw.find_of_slot hi hs]
    rfl
  · have habs : ∀ j, j < t.buckets → ∀ v', t.slotAt j ≠ some (k, v') :=
      fun j hj v' hs => hpres ⟨j, hj, v', hs⟩
    rw [containsKey_list_absent (toList_absent habs)]
    unfold Table.containsKey
    rw [(hw.find_eq_none_iff k).2 habs]
    rfl

omit [BEq K] [LawfulBEq K] in
theorem WF.len_eq (hw : WF hash t) : len t = HashMap.len (toList t) := hw.items_eq

/-- `insert` on a table with room: no resize, and the entry list changes as
the list model says. -/
theorem WF.insert_of_growth (hw : WF hash t) (hcl : Clean t) (hg : 1 ≤ t.growthLeft)
    (k : K) (v : V) :
    WF hash (Table.insert hash t k v).2 ∧ Clean (Table.insert hash t k v).2 ∧
      (Table.insert hash t k v).2.buckets = t.buckets ∧
      (Table.insert hash t k v).1 = HashMap.get (toList t) k ∧
      (toList (Table.insert hash t k v).2).Perm (HashMap.insert (toList t) k v).2 := by
  have hres : reserve hash t 1 = t := reserve_eq_self hash t hg
  by_cases hpres : ∃ i, i < t.buckets ∧ ∃ v', t.slotAt i = some (k, v')
  · obtain ⟨i, hi, v', hs⟩ := hpres
    have hfind := hw.toLayout.findOrFindInsert_found hi hs
    obtain ⟨hl, hpre, hpost⟩ := hw.toLayout.toList_eq_of_slot hi hs
    have heq : Table.insert hash t k v =
        (some v', { t with slots := t.slots.set i (some (k, v)) }) := by
      simp only [Table.insert, hres, hfind, hs]
    rw [heq, hl, get_list_found _ v' hpre, insert_list_found v' v hpre hpost]
    set t' : Table K V := { t with slots := t.slots.set i (some (k, v)) } with ht'
    have hself : t'.slotAt i = some (k, v) := slotAt_set_self (by rw [hw.slots_len]; exact hi) _
    have hpre' : pre t' i = pre t i := pre_congr (fun j hj => slotAt_set_ne (by omega) _)
    have hpost' : post t' i = post t i := post_congr rfl (fun j hj _ => slotAt_set_ne (by omega) _)
    have htl : toList t' = pre t i ++ (k, v) :: post t i := by
      rw [toList_split t' hi, hpre', hpost', hself, List.append_assoc]
      rfl
    have hl' : Layout hash t' := hw.toLayout.replace hi hs v
    refine ⟨⟨hl', ?_⟩, ⟨hcl.1, hcl.2⟩, rfl, rfl, by rw [htl]⟩
    show t.items = (toList t').length
    rw [htl, hw.items_eq, hl, List.length_append, List.length_append, List.length_cons,
      List.length_cons]
  · have habs : ∀ j, j < t.buckets → ∀ v', t.slotAt j ≠ some (k, v') :=
      fun j hj v' hs => hpres ⟨j, hj, v', hs⟩
    obtain ⟨e, he, hemp⟩ := hw.exists_empty hcl hg
    obtain ⟨n, j, hfs, hidx, hfind⟩ := hw.toLayout.findOrFindInsert_absent habs he hemp
    obtain ⟨hlt, hsp, hin, hnoemp⟩ := hw.toLayout.insertIndex_spec (hash k) hfs he hemp
    rw [← hidx] at hlt hsp hin
    have heq : Table.insert hash t k v =
        (none, Table.insertAt t (findInsertIndex t (hash k)) (h2 (hash k)) (k, v)) := by
      simp only [Table.insert, hres, hfind]
    obtain ⟨hw', hperm⟩ := hw.insertAt hlt hsp v habs hin hnoemp
    have hnk := toList_absent habs
    rw [heq, get_list_absent hnk, insert_list_absent hnk v]
    refine ⟨hw', ?_, rfl, rfl, hperm.trans (List.perm_append_singleton _ _).symm⟩
    have hbyte : t.ctrlAt (findInsertIndex t (hash k)) = EMPTY := hcl.1 _ hlt hsp
    rw [insertAt_eq]
    refine ⟨?_, ?_⟩
    · intro p hp hsp'
      have hp' : p < t.buckets := hp
      have hc : (withCounters (Table.place t (findInsertIndex t (hash k)) (h2 (hash k)) (k, v))
          (t.items + 1)
          (t.growthLeft - (if isEmpty (t.ctrlAt (findInsertIndex t (hash k)))
            then 1 else 0))).ctrlAt p =
          (t.setCtrl (findInsertIndex t (hash k)) (h2 (hash k))).ctrlAt p := rfl
      rw [hc] at hsp' ⊢
      by_cases hpi : p = findInsertIndex t (hash k)
      · rw [hpi, ctrlAt_setCtrl_self hw.shape hw.ctrl_len hlt, isSpecial_h2] at hsp'
        cases hsp'
      · rw [ctrlAt_setCtrl_ne hw.shape hw.ctrl_len hlt _ hp' hpi] at hsp' ⊢
        exact hcl.1 p hp' hsp'
    · show t.growthLeft - (if isEmpty (t.ctrlAt (findInsertIndex t (hash k))) then 1 else 0) +
        (t.items + 1) = bucketMaskToCapacity (t.buckets - 1)
      rw [isEmpty_iff.2 hbyte, if_pos rfl]
      have := hcl.2
      omega

end Ops

/-! ## Erasing an entry -/

theorem not_isEmpty_iff {c : UInt8} : (!isEmpty c) = true ↔ c ≠ EMPTY := by
  unfold isEmpty
  rw [Bool.not_eq_true', beq_eq_false_iff_ne]

theorem not_isEmpty_eq_false_iff {c : UInt8} : (!isEmpty c) = false ↔ c = EMPTY := by
  unfold isEmpty
  rw [Bool.not_eq_false', beq_iff_eq]

theorem takeWhile_length_spec {α : Type} (p : α → Bool) (d : α) : ∀ (g : List α),
    (g.takeWhile p).length ≤ g.length ∧
    (∀ j, j < (g.takeWhile p).length → p (g.getD j d) = true) ∧
    ((g.takeWhile p).length < g.length → p (g.getD (g.takeWhile p).length d) = false) := by
  intro g
  induction g with
  | nil => simp
  | cons a g ih =>
    rw [List.takeWhile_cons]
    split_ifs with ha
    · simp only [List.length_cons]
      refine ⟨by omega, ?_, ?_⟩
      · intro j hj
        rcases j with _ | j
        · simpa using ha
        · have := ih.2.1 j (by omega)
          simpa using this
      · intro hlt
        have := ih.2.2 (by omega)
        simpa using this
    · simp only [List.length_nil]
      refine ⟨by omega, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ => ?_⟩
      simpa using ha

theorem getD_reverse_of_lt {α : Type} {l : List α} {j : Nat} (hj : j < l.length) (d : α) :
    l.reverse.getD j d = l.getD (l.length - 1 - j) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse hj]

theorem trailNonEmpty_spec (t : Table K V) (p : Nat) :
    trailNonEmpty (groupAt t p) ≤ 8 ∧
    (∀ j, j < trailNonEmpty (groupAt t p) → t.ctrlAt (p + j) ≠ EMPTY) ∧
    (trailNonEmpty (groupAt t p) < 8 →
      t.ctrlAt (p + trailNonEmpty (groupAt t p)) = EMPTY) := by
  obtain ⟨h1, h2, h3⟩ := takeWhile_length_spec (fun c => !isEmpty c) EMPTY (groupAt t p)
  rw [groupAt_length] at h1 h3
  unfold trailNonEmpty
  refine ⟨h1, fun j hj => ?_, fun hlt => ?_⟩
  · have := h2 j hj
    rw [groupAt_getD _ _ _ (by omega)] at this
    exact not_isEmpty_iff.1 this
  · have := h3 hlt
    rw [groupAt_getD _ _ _ hlt] at this
    exact not_isEmpty_eq_false_iff.1 this

theorem leadNonEmpty_spec (t : Table K V) (p : Nat) :
    leadNonEmpty (groupAt t p) ≤ 8 ∧
    (∀ j, 8 - leadNonEmpty (groupAt t p) ≤ j → j < 8 → t.ctrlAt (p + j) ≠ EMPTY) ∧
    (leadNonEmpty (groupAt t p) < 8 →
      t.ctrlAt (p + (7 - leadNonEmpty (groupAt t p))) = EMPTY) := by
  obtain ⟨h1, h2, h3⟩ := takeWhile_length_spec (fun c => !isEmpty c) EMPTY (groupAt t p).reverse
  rw [List.length_reverse, groupAt_length] at h1 h3
  unfold leadNonEmpty
  refine ⟨h1, fun j hj8 hj => ?_, fun hlt => ?_⟩
  · have := h2 (7 - j) (by omega)
    rw [getD_reverse_of_lt (by rw [groupAt_length]; omega), groupAt_length,
      show 8 - 1 - (7 - j) = j by omega, groupAt_getD _ _ _ hj] at this
    exact not_isEmpty_iff.1 this
  · have := h3 hlt
    rw [getD_reverse_of_lt (by rw [groupAt_length]; omega), groupAt_length,
      show 8 - 1 - ((groupAt t p).reverse.takeWhile (fun c => !isEmpty c)).length =
        7 - ((groupAt t p).reverse.takeWhile (fun c => !isEmpty c)).length by omega,
      groupAt_getD _ _ _ (by omega)] at this
    exact not_isEmpty_eq_false_iff.1 this

/-- When the runs of full bytes around `i` are short, every window that names
`i` already has an `EMPTY` byte. -/
theorem Layout.window_empty_of_runs (hw : Layout hash t) (hb : 8 ≤ t.buckets) {i : Nat}
    (hi : i < t.buckets)
    (hrun : leadNonEmpty (groupAt t (wrapSub i 8 t.buckets)) + trailNonEmpty (groupAt t i) < 8)
    (h : UInt64) (n : Nat) (hin : InWindow t h n i) : matchEmpty (window t h n) = true := by
  set L := leadNonEmpty (groupAt t (wrapSub i 8 t.buckets)) with hL
  set T := trailNonEmpty (groupAt t i) with hT
  obtain ⟨j0, hj0, -, hidx⟩ := hin
  unfold probeIdx at hidx
  have hposb : (probeSeq t h n).pos < t.buckets := hw.probe_lt h n
  have ring : ∀ p, p < t.buckets + 8 → t.ctrlAt p = t.ctrlAt (p % t.buckets) := by
    intro p hp
    rw [hw.mirror p hp, if_neg (by unfold IsPad; omega)]
  have hwb : wrapSub i 8 t.buckets < t.buckets := Nat.mod_lt _ hw.pos
  have hbefore : wrapSub i 8 t.buckets = (i + (t.buckets - 8)) % t.buckets :=
    wrapSub_eight_of_le hw.shape.dvd_pow32 hb
  obtain ⟨hl1, -, hl3⟩ := leadNonEmpty_spec t (wrapSub i 8 t.buckets)
  obtain ⟨ht1, -, ht3⟩ := trailNonEmpty_spec t i
  rw [← hL] at hl1 hl3
  rw [← hT] at ht1 ht3
  rw [matchEmpty_window]
  rcases Nat.lt_or_ge L j0 with hlt | hge
  · refine ⟨j0 - (L + 1), by omega, ?_⟩
    have hE := hl3 (by omega)
    rw [ring _ (by omega), hbefore, Nat.mod_add_mod,
      show i + (t.buckets - 8) + (7 - L) = i + t.buckets - (L + 1) by omega] at hE
    rw [ring _ (by omega), ← hE]
    congr 1
    have h1 : (L + 1) + ((probeSeq t h n).pos + (j0 - (L + 1))) ≡
        (L + 1) + (i + t.buckets - (L + 1)) [MOD t.buckets] := by
      rw [show (L + 1) + ((probeSeq t h n).pos + (j0 - (L + 1))) = (probeSeq t h n).pos + j0 by
          omega,
        show (L + 1) + (i + t.buckets - (L + 1)) = i + t.buckets by omega]
      unfold Nat.ModEq
      rw [hidx, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    exact Nat.ModEq.add_left_cancel' _ h1
  · refine ⟨j0 + T, by omega, ?_⟩
    have hE := ht3 (by omega)
    rw [ring _ (by omega)] at hE
    rw [ring _ (by omega), ← hE]
    congr 1
    have h1 : (probeSeq t h n).pos + j0 + T ≡ i + T [MOD t.buckets] :=
      Nat.ModEq.add_right _ (by unfold Nat.ModEq; rw [hidx, Nat.mod_eq_of_lt hi])
    rw [← Nat.add_assoc]
    exact h1

theorem toList_erase (hw : Layout hash t) {i : Nat} (hi : i < t.buckets) :
    toList (erase t i) = pre t i ++ post t i := by
  have h1 : pre (erase t i) i = pre t i :=
    pre_congr (fun j hj => slotAt_set_ne (by omega) _)
  have h2 : post (erase t i) i = post t i :=
    post_congr rfl (fun j hj _ => slotAt_set_ne (by omega) _)
  have h3 : (erase t i).slotAt i = none :=
    slotAt_set_self (by show i < t.slots.length; rw [hw.slots_len]; exact hi) _
  rw [toList_split (erase t i) hi, h1, h2, h3]
  show pre t i ++ [] ++ post t i = _
  rw [List.append_nil]

/-- `erase` keeps `WF` and drops the entry. -/
theorem WF.erase (hw : WF hash t) {i : Nat} (hi : i < t.buckets) {k : K} {v : V}
    (hs : t.slotAt i = some (k, v)) :
    WF hash (Table.erase t i) ∧ (Table.erase t i).buckets = t.buckets ∧
      toList (Table.erase t i) = pre t i ++ post t i := by
  have htl := toList_erase hw.toLayout hi
  set c : UInt8 := if 8 ≤ leadNonEmpty (groupAt t (wrapSub i 8 t.buckets)) +
    trailNonEmpty (groupAt t i) then DELETED else EMPTY with hc
  have hb : (Table.erase t i).buckets = t.buckets := rfl
  have hctrl : ∀ p, (Table.erase t i).ctrlAt p = (t.setCtrl i c).ctrlAt p := fun p => rfl
  have hcs : isSpecial c = true := by
    rw [hc]; split_ifs <;> decide
  have hslot_self : (Table.erase t i).slotAt i = none :=
    slotAt_set_self (t := t.setCtrl i c) (by show i < t.slots.length; rw [hw.slots_len]; exact hi) _
  have hslot_ne : ∀ j, j ≠ i → (Table.erase t i).slotAt j = t.slotAt j :=
    fun j hj => slotAt_set_ne (t := t.setCtrl i c) hj _
  have hctrl_ne : ∀ p, p < t.buckets → p ≠ i → (Table.erase t i).ctrlAt p = t.ctrlAt p :=
    fun p hp hne => by rw [hctrl]; exact ctrlAt_setCtrl_ne hw.shape hw.ctrl_len hi _ hp hne
  have hctrl_self : (Table.erase t i).ctrlAt i = c := by
    rw [hctrl]; exact ctrlAt_setCtrl_self hw.shape hw.ctrl_len hi _
  have hwin : ∀ (h : UInt64) (m : Nat), matchEmpty (window t h m) = false →
      matchEmpty (window (Table.erase t i) h m) = false := by
    intro h m hm
    rw [Bool.eq_false_iff] at hm ⊢
    intro hme
    apply hm
    rw [matchEmpty_window] at hme
    obtain ⟨j, hj, hj'⟩ := hme
    rw [probeSeq_congr t _ hb, hctrl, ctrlAt_setCtrl hw.shape hw.ctrl_len hi] at hj'
    have hpj : (probeSeq t h m).pos + j < t.buckets + 8 := by
      have := hw.toLayout.probe_lt h m; omega
    split_ifs at hj' with hor
    · rcases Nat.lt_or_ge t.buckets 8 with hb8 | hb8
      · exact hw.toLayout.matchEmpty_of_small hb8 h m
      · have hrun : leadNonEmpty (groupAt t (wrapSub i 8 t.buckets)) +
            trailNonEmpty (groupAt t i) < 8 := by
          by_contra hge
          rw [hc, if_pos (Nat.le_of_not_lt hge)] at hj'
          exact absurd hj' (by decide)
        have hin : InWindow t h m i := by
          obtain ⟨hpad, hmod⟩ := (index2_iff hw.shape hi hpj).1 hor
          exact ⟨j, hj, hpad, hmod⟩
        exact hw.toLayout.window_empty_of_runs hb8 hi hrun h m hin
    · exact (matchEmpty_window t h m).2 ⟨j, hj, hj'⟩
  refine ⟨⟨⟨hw.shape, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, rfl, htl⟩
  · show ((t.ctrl.set i _).set _ _).length = t.buckets + 8
    rw [List.length_set, List.length_set, hw.ctrl_len]
  · show (t.slots.set i _).length = t.buckets
    rw [List.length_set, hw.slots_len]
  · exact mirror_setCtrl hw.shape hw.ctrl_len hw.mirror hi _
  · intro p hp
    rw [hb] at hp
    by_cases hpi : p = i
    · rw [hpi, hctrl_self, hslot_self]
      have : isFull c = false := by
        rcases hf : isFull c with _ | _
        · rfl
        · exact absurd hf (isSpecial_iff.1 hcs)
      rw [this]
      simp
    · rw [hctrl_ne p hp hpi, hslot_ne p hpi]
      exact hw.full_iff p hp
  · intro p hp k' v' hs'
    rw [hb] at hp
    by_cases hpi : p = i
    · rw [hpi, hslot_self] at hs'
      cases hs'
    · rw [hslot_ne p hpi] at hs'
      rw [hctrl_ne p hp hpi]
      exact hw.tag p hp k' v' hs'
  · intro p q hp hq k' v₁ v₂ hs₁ hs₂
    rw [hb] at hp hq
    by_cases hpi : p = i
    · rw [hpi, hslot_self] at hs₁
      cases hs₁
    · by_cases hqi : q = i
      · rw [hqi, hslot_self] at hs₂
        cases hs₂
      · rw [hslot_ne p hpi] at hs₁
        rw [hslot_ne q hqi] at hs₂
        exact hw.uniq p q hp hq k' v₁ v₂ hs₁ hs₂
  · intro p hp k' v' hs'
    rw [hb] at hp
    by_cases hpi : p = i
    · rw [hpi, hslot_self] at hs'
      cases hs'
    · rw [hslot_ne p hpi] at hs'
      obtain ⟨n, hin, hemp⟩ := hw.reach p hp k' v' hs'
      exact ⟨n, (inWindow_congr t _ hb _ _ _).2 hin, fun m hm => hwin _ m (hemp m hm)⟩
  · show t.items - 1 = (toList (Table.erase t i)).length
    rw [htl, hw.items_eq, (hw.toLayout.toList_eq_of_slot hi hs).1, List.length_append,
      List.length_append, List.length_cons]
    omega

section Remove
variable [BEq K] [LawfulBEq K]

/-- `remove` keeps `WF`, and the entry list changes as the list model says. -/
theorem WF.remove (hw : WF hash t) (k : K) :
    WF hash (Table.remove hash t k).2 ∧ (Table.remove hash t k).2.buckets = t.buckets ∧
      (Table.remove hash t k).1 = (HashMap.remove (toList t) k).1 ∧
      (toList (Table.remove hash t k).2).Perm (HashMap.remove (toList t) k).2 := by
  by_cases hpres : ∃ i, i < t.buckets ∧ ∃ v', t.slotAt i = some (k, v')
  · obtain ⟨i, hi, v', hs⟩ := hpres
    have hfind := hw.toLayout.find_of_slot hi hs
    obtain ⟨hl, hpre, hpost⟩ := hw.toLayout.toList_eq_of_slot hi hs
    have heq : Table.remove hash t k = (some v', Table.erase t i) := by
      simp only [Table.remove, hfind, hs, Option.map_some]
    obtain ⟨hw', hb, htl⟩ := hw.erase hi hs
    rw [heq, hl, remove_list_found v' hpre hpost]
    exact ⟨hw', hb, rfl, by rw [htl]⟩
  · have habs : ∀ j, j < t.buckets → ∀ v', t.slotAt j ≠ some (k, v') :=
      fun j hj v' hs => hpres ⟨j, hj, v', hs⟩
    have hfind := (hw.toLayout.find_eq_none_iff k).2 habs
    have heq : Table.remove hash t k = (none, t) := by
      simp only [Table.remove, hfind]
    rw [heq, remove_list_absent (toList_absent habs)]
    exact ⟨hw, rfl, rfl, List.Perm.refl _⟩

end Remove

/-! ## Checkpoint F: fresh tables, sizing, `resize`, `reserve`

`rehashInPlace` is unreachable from a `Clean` table. `reserve` takes that
branch only when `items + additional <= fullCap / 2`, and a `Clean` table
with `growthLeft < additional` has `items + additional > fullCap`. The lemmas
below cover the `resize` branch, and `reserve_eq_resize` records the
decision. -/

/-! ### Fresh tables -/

theorem ctrlAt_newEmpty (b p : Nat) : (newEmpty b : Table K V).ctrlAt p = EMPTY := by
  unfold ctrlAt newEmpty
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem slotAt_newEmpty (b p : Nat) : (newEmpty b : Table K V).slotAt p = none := by
  unfold slotAt newEmpty
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem toList_newEmpty (b : Nat) : toList (newEmpty b : Table K V) = [] := by
  unfold toList
  rw [List.filterMap_eq_nil_iff]
  intro i _
  exact slotAt_newEmpty b i

theorem empty_eq_newEmpty : (empty : Table K V) = newEmpty 1 := rfl

theorem layout_newEmpty {b : Nat} (hs : Shape b) (hash : K → UInt64) :
    Layout hash (newEmpty b : Table K V) := by
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (List.replicate (b + 8) EMPTY).length = b + 8
    rw [List.length_replicate]
  · show (List.replicate b (none : Option (K × V))).length = b
    rw [List.length_replicate]
  · intro p _
    rw [ctrlAt_newEmpty, ctrlAt_newEmpty]
    split <;> rfl
  · intro i _
    rw [ctrlAt_newEmpty, slotAt_newEmpty, isFull_EMPTY]
    simp
  · intro i _ k v hs
    rw [slotAt_newEmpty] at hs
    cases hs
  · intro i j _ _ k v v' hs
    rw [slotAt_newEmpty] at hs
    cases hs
  · intro i _ k v hs
    rw [slotAt_newEmpty] at hs
    cases hs

theorem wf_newEmpty {b : Nat} (hs : Shape b) (hash : K → UInt64) :
    WF hash (newEmpty b : Table K V) :=
  ⟨layout_newEmpty hs hash, by rw [toList_newEmpty]; rfl⟩

theorem clean_newEmpty (b : Nat) : Clean (newEmpty b : Table K V) :=
  ⟨fun i _ _ => ctrlAt_newEmpty b i, Nat.add_zero _⟩

/-- The bucket count of `withCapacity cap`. -/
def capBuckets (cap : Nat) : Nat := if cap = 0 then 1 else capacityToBuckets cap

theorem withCapacity_eq (cap : Nat) :
    (withCapacity cap : Table K V) = newEmpty (capBuckets cap) := by
  unfold withCapacity capBuckets
  by_cases h : cap = 0
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]

/-! ### Sizing -/

/-- The loop of `nextPow2` from `2 ^ j`: the result is the least power of two
that is at least `n`, as long as the fuel reaches it. -/
theorem nextPow2_go_spec (n : Nat) : ∀ (f j : Nat), n ≤ 2 ^ (f + j) →
    ∃ m, j ≤ m ∧ m ≤ f + j ∧ nextPow2.go n f (2 ^ j) = 2 ^ m ∧ n ≤ 2 ^ m ∧
      (m = j ∨ 2 ^ (m - 1) < n) := by
  intro f
  induction f with
  | zero =>
    intro j hj
    rw [Nat.zero_add] at hj
    exact ⟨j, le_rfl, by omega, rfl, hj, Or.inl rfl⟩
  | succ f ih =>
    intro j hj
    rw [show nextPow2.go n (f + 1) (2 ^ j) =
      if n ≤ 2 ^ j then 2 ^ j else nextPow2.go n f (2 ^ j * 2) from rfl]
    by_cases hle : n ≤ 2 ^ j
    · rw [if_pos hle]
      exact ⟨j, le_rfl, by omega, rfl, hle, Or.inl rfl⟩
    · rw [if_neg hle, ← Nat.pow_succ]
      obtain ⟨m, hm1, hm2, hgo, hnm, hor⟩ :=
        ih (j + 1) (by rw [show f + (j + 1) = f + 1 + j by omega]; exact hj)
      refine ⟨m, by omega, by omega, hgo, hnm, Or.inr ?_⟩
      rcases hor with rfl | hlt
      · rw [Nat.add_sub_cancel]
        exact Nat.lt_of_not_le hle
      · exact hlt

theorem nextPow2_spec {n : Nat} (hn : n ≤ 2 ^ 32) :
    ∃ m, m ≤ 32 ∧ nextPow2 n = 2 ^ m ∧ n ≤ 2 ^ m ∧ (m = 0 ∨ 2 ^ (m - 1) < n) := by
  obtain ⟨m, -, hm2, hgo, hnm, hor⟩ :=
    nextPow2_go_spec n 32 0 (by rw [Nat.add_zero]; exact hn)
  exact ⟨m, by omega, hgo, hnm, hor⟩

/-- `capacity_to_buckets` gives a table shape with room for `cap` items. -/
theorem capacityToBuckets_spec {cap : Nat} (hc : cap * 8 / 7 ≤ 2 ^ 32) :
    Shape (capacityToBuckets cap) ∧
      cap ≤ bucketMaskToCapacity (capacityToBuckets cap - 1) := by
  unfold capacityToBuckets
  by_cases h15 : cap < 15
  · rw [if_pos h15]
    show Shape (if max 3 cap < 4 then 4 else if max 3 cap < 8 then 8 else 16) ∧
      cap ≤ bucketMaskToCapacity ((if max 3 cap < 4 then 4 else if max 3 cap < 8 then 8 else 16) - 1)
    by_cases h4 : max 3 cap < 4
    · rw [if_pos h4]
      exact ⟨⟨2, by omega, by omega, rfl⟩, by show cap ≤ 3; omega⟩
    · rw [if_neg h4]
      by_cases h8 : max 3 cap < 8
      · rw [if_pos h8]
        exact ⟨⟨3, by omega, by omega, rfl⟩, by show cap ≤ 7; omega⟩
      · rw [if_neg h8]
        exact ⟨⟨4, by omega, by omega, rfl⟩, by show cap ≤ 14; omega⟩
  · rw [if_neg h15]
    obtain ⟨m, hm, hp, hnm, -⟩ := nextPow2_spec hc
    rw [hp]
    have hm5 : 5 ≤ m := by
      by_contra hlt
      have : 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    refine ⟨⟨m, hm, by omega, rfl⟩, ?_⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm5
    rw [hk, Nat.pow_add] at hnm ⊢
    generalize 2 ^ k = q at hnm ⊢
    unfold bucketMaskToCapacity
    rw [if_neg (by omega)]
    omega

theorem capacityToBuckets_lt {cap : Nat} (hc : cap * 8 / 7 ≤ 2 ^ 31) :
    capacityToBuckets cap < 2 ^ 32 := by
  unfold capacityToBuckets
  by_cases h15 : cap < 15
  · rw [if_pos h15]
    show (if max 3 cap < 4 then 4 else if max 3 cap < 8 then 8 else 16) < 2 ^ 32
    split_ifs <;> omega
  · rw [if_neg h15]
    obtain ⟨m, -, hp, -, hor⟩ := nextPow2_spec (n := cap * 8 / 7) (by omega)
    rw [hp]
    rcases hor with rfl | hlt
    · omega
    · have h1 : 2 ^ (m - 1) < 2 ^ 31 := by omega
      rw [Nat.pow_lt_pow_iff_right (by omega)] at h1
      exact Nat.pow_lt_pow_right (by omega) (by omega)

theorem capBuckets_spec {cap : Nat} (hc : cap * 8 / 7 ≤ 2 ^ 32) :
    Shape (capBuckets cap) ∧ cap ≤ bucketMaskToCapacity (capBuckets cap - 1) := by
  unfold capBuckets
  by_cases h : cap = 0
  · rw [if_pos h, h]
    exact ⟨⟨0, by omega, by omega, rfl⟩, Nat.zero_le _⟩
  · rw [if_neg h]
    exact capacityToBuckets_spec hc

theorem capBuckets_lt {cap : Nat} (hc : cap * 8 / 7 ≤ 2 ^ 31) : capBuckets cap < 2 ^ 32 := by
  unfold capBuckets
  by_cases h : cap = 0
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    exact capacityToBuckets_lt hc

/-- One more item than the full capacity still fits the sizing bound when the
table has fewer than `2 ^ 32` buckets. -/
theorem Shape.grow_bound {b : Nat} (hs : Shape b) (hb : b < 2 ^ 32) :
    (bucketMaskToCapacity (b - 1) + 1) * 8 / 7 ≤ 2 ^ 32 := by
  rcases Nat.lt_or_ge b 8 with h8 | h8
  · rcases hs.small h8 with rfl | rfl <;> decide
  · obtain ⟨k, hk⟩ := hs.eq_mul_pow h8
    unfold bucketMaskToCapacity
    by_cases h8' : b - 1 < 8
    · rw [if_pos h8']
      omega
    · rw [if_neg h8']
      generalize 2 ^ k = q at hk
      omega

/-! ### The insert index of a table with room -/

/-- `findInsertIndex` on a table with an `EMPTY` byte: a special bucket that
the probe of `h` reaches, with no earlier window that has an `EMPTY` byte. -/
theorem Layout.findInsertIndex_spec (hw : Layout hash t) (h : UInt64) {e : Nat}
    (he : e < t.buckets) (hemp : t.ctrlAt e = EMPTY) :
    findInsertIndex t h < t.buckets ∧ isSpecial (t.ctrlAt (findInsertIndex t h)) = true ∧
      ∃ n, InWindow t h n (findInsertIndex t h) ∧
        ∀ m, m < n → matchEmpty (window t h m) = false := by
  rcases hfs : firstSpecial t h (probeFuel t) 0 with _ | ⟨n, j⟩
  · exact absurd hfs (hw.firstSpecial_probe h he hemp)
  · have hidx : findInsertIndex t h = fixInsertIndex t (probeIdx t h n j) := by
      unfold findInsertIndex
      rw [show probeStart t h = probeSeq t h 0 from rfl, findInsertIndexLoop_eq, hfs]
      rfl
    obtain ⟨hlt, hsp, hin, hnoemp⟩ := hw.insertIndex_spec h hfs he hemp
    rw [← hidx] at hlt hsp hin
    exact ⟨hlt, hsp, n, hin, hnoemp⟩

/-- A layout with no tombstone and fewer entries than buckets has an `EMPTY`
byte. -/
theorem Layout.exists_empty_of_lt (hw : Layout hash t)
    (hsp : ∀ i, i < t.buckets → isSpecial (t.ctrlAt i) = true → t.ctrlAt i = EMPTY)
    (hlen : (toList t).length < t.buckets) : ∃ e, e < t.buckets ∧ t.ctrlAt e = EMPTY := by
  by_contra hno
  have hfull : ∀ i, i < t.buckets → (t.slotAt i).isSome = true := by
    intro i hi
    rw [← hw.full_iff i hi]
    rcases hf : isFull (t.ctrlAt i) with _ | _
    · exfalso
      have hs : isSpecial (t.ctrlAt i) = true := isSpecial_iff.2 (by rw [hf]; decide)
      exact hno ⟨i, hi, hsp i hi hs⟩
    · rfl
  have : (toList t).length = t.buckets := by
    unfold toList
    rw [List.range_eq_range']
    exact length_filterMap_range' t.slotAt t.buckets 0 (fun i _ hi => hfull i (by omega))
  omega

/-! ### The `resize` fold -/

theorem length_filterMap_of_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome = true) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons]
    rcases hf : f x with _ | y
    · have := h x List.mem_cons_self
      rw [hf] at this
      cases this
    · show (y :: List.filterMap f l).length = (x :: l).length
      rw [List.length_cons, List.length_cons,
        length_filterMap_of_isSome f l (fun z hz => h z (List.mem_cons_of_mem x hz))]

theorem filterMap_filter_of_none {α β : Type} (p : α → Bool) (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, p x = false → f x = none) →
      (l.filter p).filterMap f = l.filterMap f
  | [], _ => rfl
  | x :: l, h => by
    have ih := filterMap_filter_of_none p f l (fun y hy => h y (List.mem_cons_of_mem x hy))
    rcases hp : p x with _ | _
    · rw [List.filter_cons_of_neg (by rw [hp]; decide), ih, List.filterMap_cons,
        h x List.mem_cons_self hp]
    · rw [List.filter_cons_of_pos hp, List.filterMap_cons, List.filterMap_cons, ih]

theorem mem_fullIndices {t : Table K V} {i : Nat} :
    i ∈ fullIndices t ↔ i < t.buckets ∧ isFull (t.ctrlAt i) = true := by
  unfold fullIndices
  rw [List.mem_filter, List.mem_range]

theorem nodup_fullIndices (t : Table K V) : (fullIndices t).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem filterMap_fullIndices (hw : Layout hash t) :
    (fullIndices t).filterMap t.slotAt = toList t := by
  unfold fullIndices toList
  apply filterMap_filter_of_none
  intro i hi hnf
  rw [List.mem_range] at hi
  rcases hs : t.slotAt i with _ | x
  · rfl
  · have := (hw.full_iff i hi).2 (by rw [hs]; rfl)
    rw [hnf] at this
    cases this

theorem length_fullIndices (hw : Layout hash t) : (fullIndices t).length = (toList t).length := by
  rw [← filterMap_fullIndices hw]
  exact (length_filterMap_of_isSome _ _ (fun j hj =>
    (hw.full_iff j (mem_fullIndices.1 hj).1).1 (mem_fullIndices.1 hj).2)).symm

/-- One step of the `resize` fold: the entry of bucket `i` of `t` moves into
`n` at its insert index. -/
def moveStep (hash : K → UInt64) (t n : Table K V) (i : Nat) : Table K V :=
  match t.slotAt i with
  | some (k, v) => place n (findInsertIndex n (hash k)) (h2 (hash k)) (k, v)
  | none => n

theorem resize_eq (hash : K → UInt64) (t : Table K V) (cap : Nat) :
    resize hash t cap =
      withCounters ((fullIndices t).foldl (moveStep hash t) (withCapacity cap)) t.items
        (((fullIndices t).foldl (moveStep hash t) (withCapacity cap)).growthLeft - t.items) := by
  unfold resize withCounters moveStep place
  rfl

theorem moveStep_growthLeft (hash : K → UInt64) (t n : Table K V) (i : Nat) :
    (moveStep hash t n i).growthLeft = n.growthLeft := by
  unfold moveStep
  split <;> rfl

theorem foldl_moveStep_growthLeft (hash : K → UInt64) (t : Table K V) :
    ∀ (l : List Nat) (n : Table K V), (l.foldl (moveStep hash t) n).growthLeft = n.growthLeft
  | [], _ => rfl
  | i :: l, n => by
    rw [List.foldl_cons, foldl_moveStep_growthLeft hash t l, moveStep_growthLeft]

/-- The state of the `resize` fold after the buckets in `l₁` moved. -/
def MoveInv (hash : K → UInt64) (t : Table K V) (b₀ : Nat) (l₁ : List Nat)
    (n : Table K V) : Prop :=
  Layout hash n ∧ n.buckets = b₀ ∧
    (∀ i, i < n.buckets → isSpecial (n.ctrlAt i) = true → n.ctrlAt i = EMPTY) ∧
    (toList n).Perm (l₁.filterMap t.slotAt)

theorem moveStep_inv (hw : Layout hash t) {b₀ : Nat}
    (hcap : (toList t).length ≤ bucketMaskToCapacity (b₀ - 1))
    {l₁ l₂ : List Nat} {i : Nat} (hlist : l₁ ++ i :: l₂ = fullIndices t) {n : Table K V}
    (hinv : MoveInv hash t b₀ l₁ n) : MoveInv hash t b₀ (l₁ ++ [i]) (moveStep hash t n i) := by
  obtain ⟨hln, hb, hsp, hperm⟩ := hinv
  have hi : i ∈ fullIndices t := by
    rw [← hlist]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨hib, hif⟩ := mem_fullIndices.1 hi
  obtain ⟨⟨k, v⟩, hs⟩ := Option.isSome_iff_exists.1 ((hw.full_iff i hib).1 hif)
  have hstep : moveStep hash t n i = place n (findInsertIndex n (hash k)) (h2 (hash k)) (k, v) := by
    simp only [moveStep, hs]
  have hnd : (l₁ ++ i :: l₂).Nodup := by
    rw [hlist]
    exact nodup_fullIndices t
  have hnotin : i ∉ l₁ := fun h =>
    (List.nodup_cons.1 (List.nodup_middle.1 hnd)).1 (List.mem_append_left _ h)
  have hl₁ : ∀ j ∈ l₁, j < t.buckets := fun j hj =>
    (mem_fullIndices.1 (by rw [← hlist]; exact List.mem_append_left _ hj)).1
  have habs : ∀ j, j < n.buckets → ∀ v', n.slotAt j ≠ some (k, v') := by
    intro j hj v' hsj
    have hmem : (k, v') ∈ l₁.filterMap t.slotAt := hperm.subset (mem_toList.2 ⟨j, hj, hsj⟩)
    obtain ⟨j', hj'l, hsj'⟩ := List.mem_filterMap.1 hmem
    have := hw.uniq j' i (hl₁ j' hj'l) hib k v' v hsj' hs
    exact hnotin (this ▸ hj'l)
  have hlen : (toList n).length < n.buckets := by
    have e1 : (toList n).length = (l₁.filterMap t.slotAt).length := hperm.length_eq
    have e2 : (l₁.filterMap t.slotAt).length ≤ l₁.length := List.length_filterMap_le _ _
    have e3 := length_fullIndices hw
    have e4 : (l₁ ++ i :: l₂).length = (fullIndices t).length := by rw [hlist]
    rw [List.length_append, List.length_cons] at e4
    have e5 := hln.shape.cap_lt
    rw [hb] at e5 ⊢
    omega
  obtain ⟨e, he, hemp⟩ := hln.exists_empty_of_lt hsp hlen
  obtain ⟨hlt, hsp', m, hin, hnoemp⟩ := hln.findInsertIndex_spec (hash k) he hemp
  rw [hstep]
  refine ⟨hln.place hlt v habs hin hnoemp, hb, ?_, ?_⟩
  · intro p hp hsp''
    have hc : ∀ q, (place n (findInsertIndex n (hash k)) (h2 (hash k)) (k, v)).ctrlAt q =
        (n.setCtrl (findInsertIndex n (hash k)) (h2 (hash k))).ctrlAt q := fun q => rfl
    have hp' : p < n.buckets := hp
    rw [hc] at hsp'' ⊢
    by_cases hpi : p = findInsertIndex n (hash k)
    · rw [hpi, ctrlAt_setCtrl_self hln.shape hln.ctrl_len hlt, isSpecial_h2] at hsp''
      cases hsp''
    · rw [ctrlAt_setCtrl_ne hln.shape hln.ctrl_len hlt _ hp' hpi] at hsp'' ⊢
      exact hsp p hp' hsp''
  · have hnone : n.slotAt (findInsertIndex n (hash k)) = none := hln.slotAt_eq_none hlt hsp'
    have hp1 := toList_place hln hlt hnone (h2 (hash k)) (k, v)
    rw [List.filterMap_append, List.filterMap_cons, hs]
    show (toList (place n (findInsertIndex n (hash k)) (h2 (hash k)) (k, v))).Perm
      (l₁.filterMap t.slotAt ++ [(k, v)])
    exact hp1.trans ((hperm.cons _).trans (List.perm_append_singleton _ _).symm)

theorem foldl_moveStep_inv (hw : Layout hash t) {b₀ : Nat}
    (hcap : (toList t).length ≤ bucketMaskToCapacity (b₀ - 1)) :
    ∀ (l₂ l₁ : List Nat) (n : Table K V), l₁ ++ l₂ = fullIndices t →
      MoveInv hash t b₀ l₁ n → MoveInv hash t b₀ (l₁ ++ l₂) (l₂.foldl (moveStep hash t) n)
  | [], l₁, n, _, hinv => by
    rw [List.append_nil]
    exact hinv
  | i :: l₂, l₁, n, hlist, hinv => by
    rw [List.foldl_cons]
    have := foldl_moveStep_inv hw hcap l₂ (l₁ ++ [i]) (moveStep hash t n i)
      (by rw [List.append_assoc, List.singleton_append]; exact hlist)
      (moveStep_inv hw hcap hlist hinv)
    rw [List.append_assoc, List.singleton_append] at this
    exact this

/-- `resize` keeps the entries and clears every tombstone. -/
theorem WF.resize (hw : WF hash t) {cap : Nat} (hs : Shape (capBuckets cap))
    (hcap : t.items ≤ bucketMaskToCapacity (capBuckets cap - 1)) :
    WF hash (Table.resize hash t cap) ∧ Clean (Table.resize hash t cap) ∧
      (Table.resize hash t cap).buckets = capBuckets cap ∧
      (Table.resize hash t cap).items = t.items ∧
      (toList (Table.resize hash t cap)).Perm (toList t) := by
  have hcap' : (toList t).length ≤ bucketMaskToCapacity (capBuckets cap - 1) := by
    rw [← hw.items_eq]
    exact hcap
  have hinv0 : MoveInv hash t (capBuckets cap) [] (withCapacity cap) := by
    rw [withCapacity_eq]
    refine ⟨layout_newEmpty hs hash, rfl, fun i _ _ => ctrlAt_newEmpty _ i, ?_⟩
    rw [toList_newEmpty]
    exact List.Perm.refl _
  obtain ⟨hl, hb, hsp, hperm⟩ :=
    foldl_moveStep_inv hw.toLayout hcap' (fullIndices t) [] (withCapacity cap) rfl hinv0
  rw [List.nil_append, filterMap_fullIndices hw.toLayout] at hperm
  rw [resize_eq]
  set moved := (fullIndices t).foldl (moveStep hash t) (withCapacity cap) with hmoved
  have hg : moved.growthLeft = bucketMaskToCapacity (capBuckets cap - 1) := by
    rw [hmoved, foldl_moveStep_growthLeft, withCapacity_eq]
    rfl
  refine ⟨⟨hl.counters _ _, ?_⟩, ⟨?_, ?_⟩, hb, rfl, ?_⟩
  · show t.items = (toList moved).length
    rw [hperm.length_eq, hw.items_eq]
  · intro p hp hsp'
    exact hsp p hp hsp'
  · show moved.growthLeft - t.items + t.items = bucketMaskToCapacity (moved.buckets - 1)
    rw [hg, hb]
    omega
  · rw [toList_counters]
    exact hperm

/-! ### `reserve` on a table without tombstones -/

theorem reserve_eq_resize (hcl : Clean t) {a : Nat} (hlt : t.growthLeft < a) :
    reserve hash t a =
      resize hash t (max (t.items + a) (bucketMaskToCapacity (t.buckets - 1) + 1)) := by
  unfold reserve
  rw [if_neg (by omega)]
  show (if t.items + a ≤ bucketMaskToCapacity (t.buckets - 1) / 2 then rehashInPlace hash t
    else resize hash t (max (t.items + a) (bucketMaskToCapacity (t.buckets - 1) + 1))) = _
  rw [if_neg (by have := hcl.2; omega)]

/-- `reserve` on a `Clean` table: the entries stay, the table stays `Clean`,
and the room is there. The bucket count either stays or is the one of the
new capacity. -/
theorem WF.reserve (hw : WF hash t) (hcl : Clean t) {a : Nat}
    (hc : max (t.items + a) (bucketMaskToCapacity (t.buckets - 1) + 1) * 8 / 7 ≤ 2 ^ 32) :
    WF hash (Table.reserve hash t a) ∧ Clean (Table.reserve hash t a) ∧
      (toList (Table.reserve hash t a)).Perm (toList t) ∧
      a ≤ (Table.reserve hash t a).growthLeft ∧
      ((Table.reserve hash t a).buckets = t.buckets ∨
        (Table.reserve hash t a).buckets =
          capBuckets (max (t.items + a) (bucketMaskToCapacity (t.buckets - 1) + 1))) := by
  by_cases hle : a ≤ t.growthLeft
  · rw [reserve_eq_self hash t hle]
    exact ⟨hw, hcl, List.Perm.refl _, hle, Or.inl rfl⟩
  · rw [reserve_eq_resize hcl (Nat.lt_of_not_le hle)]
    set cap := max (t.items + a) (bucketMaskToCapacity (t.buckets - 1) + 1) with hcapdef
    obtain ⟨hs, hle'⟩ := capBuckets_spec hc
    obtain ⟨hw', hcl', hb, hitems, hperm⟩ := hw.resize hs (by omega)
    refine ⟨hw', hcl', hperm, ?_, Or.inr hb⟩
    have := hcl'.2
    rw [hitems, hb] at this
    omega

theorem Clean.grow_bound (hcl : Clean t) (hs : Shape t.buckets) (hb : t.buckets < 2 ^ 32) :
    max (t.items + 1) (bucketMaskToCapacity (t.buckets - 1) + 1) * 8 / 7 ≤ 2 ^ 32 := by
  have h1 := hs.grow_bound hb
  have h2 := hcl.2
  rw [Nat.max_eq_right (by omega)]
  exact h1

section Resize
variable [BEq K] [LawfulBEq K]

omit [LawfulBEq K] in
theorem insert_eq_of_reserve (k : K) (v : V) (h : 1 ≤ (reserve hash t 1).growthLeft) :
    Table.insert hash t k v = Table.insert hash (reserve hash t 1) k v := by
  conv_rhs => unfold Table.insert
  rw [reserve_eq_self hash (reserve hash t 1) h]
  rfl

/-- `HashMap::insert` on any `Clean` table with fewer than `2 ^ 32` buckets. -/
theorem WF.insert (hw : WF hash t) (hcl : Clean t) (hb : t.buckets < 2 ^ 32) (k : K) (v : V) :
    WF hash (Table.insert hash t k v).2 ∧ Clean (Table.insert hash t k v).2 ∧
      (Table.insert hash t k v).1 = HashMap.get (toList t) k ∧
      (toList (Table.insert hash t k v).2).Perm (HashMap.insert (toList t) k v).2 := by
  obtain ⟨hw', hcl', hperm, hg, -⟩ := hw.reserve hcl (hcl.grow_bound hw.shape hb)
  rw [insert_eq_of_reserve k v hg]
  obtain ⟨h1, h2, -, h3, h4⟩ := hw'.insert_of_growth hcl' hg k v
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h3]
    exact get_perm hperm hw.toLayout.nodupKeys_toList k
  · exact h4.trans (insert_perm hperm hw.toLayout.nodupKeys_toList k v).2

end Resize

/-! ## Checkpoint G: `ofEntries` and the sorted entry list -/

/-- The insert fold of `extend`. -/
def insertAll [BEq K] (hash : K → UInt64) (t : Table K V) (es : List (K × V)) : Table K V :=
  es.foldl (fun t kv => (Table.insert hash t kv.1 kv.2).2) t

theorem insertAll_cons [BEq K] (hash : K → UInt64) (t : Table K V) (kv : K × V)
    (es : List (K × V)) :
    insertAll hash t (kv :: es) = insertAll hash (Table.insert hash t kv.1 kv.2).2 es := rfl

/-- `from_iter` reserves the exact length, then inserts each entry. -/
theorem ofEntries_eq [BEq K] (hash : K → UInt64) (es : List (K × V)) :
    ofEntries hash es = insertAll hash (reserve hash (empty : Table K V) es.length) es := by
  unfold ofEntries extend insertAll
  show es.foldl _ (reserve hash empty
    (if (empty : Table K V).items = 0 then es.length else (es.length + 1) / 2)) = _
  rw [if_pos (show (empty : Table K V).items = 0 from rfl)]

theorem ofEntries_append_singleton [BEq K] (es : List (K × V)) (kv : K × V) :
    HashMap.ofEntries (es ++ [kv]) = (HashMap.insert (HashMap.ofEntries es) kv.1 kv.2).2 := by
  unfold HashMap.ofEntries
  rw [List.foldl_append]
  rfl

section OfEntries
variable [BEq K] [LawfulBEq K]

/-- The insert fold on a table with room for every entry never resizes. -/
theorem insertAll_inv :
    ∀ (es₂ es₁ : List (K × V)) (t : Table K V), WF hash t → Clean t →
      (toList t).Perm (HashMap.ofEntries es₁) → es₂.length ≤ t.growthLeft →
      WF hash (insertAll hash t es₂) ∧ Clean (insertAll hash t es₂) ∧
        (insertAll hash t es₂).buckets = t.buckets ∧
        (toList (insertAll hash t es₂)).Perm (HashMap.ofEntries (es₁ ++ es₂))
  | [], es₁, t, hw, hcl, hperm, _ => by
    rw [List.append_nil]
    exact ⟨hw, hcl, rfl, hperm⟩
  | kv :: es₂, es₁, t, hw, hcl, hperm, hg => by
    rw [insertAll_cons]
    rw [List.length_cons] at hg
    have hg1 : 1 ≤ t.growthLeft := by omega
    obtain ⟨hw', hcl', hb', -, hperm'⟩ := hw.insert_of_growth hcl hg1 kv.1 kv.2
    set t' := (Table.insert hash t kv.1 kv.2).2 with ht'
    have hperm'' : (toList t').Perm (HashMap.ofEntries (es₁ ++ [kv])) := by
      rw [ofEntries_append_singleton]
      exact hperm'.trans (insert_perm hperm (nodupKeys_ofEntries es₁) kv.1 kv.2).2
    have hg' : es₂.length ≤ t'.growthLeft := by
      have c1 := hcl.2
      have c2 := hcl'.2
      have c3 := hw.items_eq
      have c4 := hw'.items_eq
      have c5 := hperm'.length_eq
      have c6 := length_insert_le (toList t) kv.1 kv.2
      rw [hb'] at c2
      omega
    have := insertAll_inv es₂ (es₁ ++ [kv]) t' hw' hcl' hperm'' hg'
    rw [List.append_assoc, List.singleton_append] at this
    obtain ⟨w1, w2, w3, w4⟩ := this
    exact ⟨w1, w2, by rw [w3, hb'], w4⟩

/-- `FromIterator::from_iter`: the table holds the entries of the list model,
has no tombstone, and has fewer than `2 ^ 32` buckets. -/
theorem wf_ofEntries (hash : K → UInt64) (es : List (K × V)) (hn : es.length ≤ 2 ^ 30) :
    WF hash (ofEntries hash es) ∧ Clean (ofEntries hash es) ∧
      (ofEntries hash es).buckets < 2 ^ 32 ∧
      (toList (ofEntries hash es)).Perm (HashMap.ofEntries es) := by
  rw [ofEntries_eq]
  have hw0 : WF hash (empty : Table K V) := wf_newEmpty ⟨0, by omega, by omega, rfl⟩ hash
  have hcl0 : Clean (empty : Table K V) := clean_newEmpty 1
  have hc : max ((empty : Table K V).items + es.length)
      (bucketMaskToCapacity ((empty : Table K V).buckets - 1) + 1) * 8 / 7 ≤ 2 ^ 32 := by
    show max (0 + es.length) (0 + 1) * 8 / 7 ≤ 2 ^ 32
    omega
  obtain ⟨hw1, hcl1, hperm1, hg1, hb1⟩ := hw0.reserve hcl0 hc
  have htl : toList (empty : Table K V) = [] := toList_newEmpty 1
  rw [htl] at hperm1
  obtain ⟨w1, w2, w3, w4⟩ :=
    insertAll_inv es [] (reserve hash empty es.length) hw1 hcl1 hperm1 hg1
  rw [List.nil_append] at w4
  refine ⟨w1, w2, ?_, w4⟩
  rw [w3]
  rcases hb1 with hb1 | hb1
  · rw [hb1]
    show 1 < 2 ^ 32
    omega
  · rw [hb1]
    apply capBuckets_lt
    show max (0 + es.length) (0 + 1) * 8 / 7 ≤ 2 ^ 31
    omega

omit [BEq K] [LawfulBEq K] in
/-- Two key-sorted lists with the same entries and distinct keys are equal. -/
theorem eq_of_perm_of_pairwise [LE K] (hanti : ∀ a b : K, a ≤ b → b ≤ a → a = b) :
    ∀ (l₁ l₂ : List (K × V)), l₁.Pairwise (fun a b => a.1 ≤ b.1) →
      l₂.Pairwise (fun a b => a.1 ≤ b.1) → NodupKeys l₁ → l₁.Perm l₂ → l₁ = l₂
  | [], _, _, _, _, hp => hp.nil_eq
  | x :: l₁, l₂, h1, h2, hn, hp => by
    obtain ⟨s, r, rfl⟩ := List.append_of_mem (hp.subset List.mem_cons_self)
    have hp' : l₁.Perm (s ++ r) := (hp.trans List.perm_middle).cons_inv
    rcases s with _ | ⟨y, s'⟩
    · rw [List.nil_append] at hp' ⊢
      rw [eq_of_perm_of_pairwise hanti l₁ r h1.of_cons h2.of_cons
        (List.nodup_cons.1 hn).2 hp']
    · exfalso
      have hy : y ∈ l₁ := hp'.symm.subset (List.mem_append_left _ List.mem_cons_self)
      have hxy : x.1 ≤ y.1 := (List.pairwise_cons.1 h1).1 y hy
      rw [List.cons_append] at h2
      have hyx : y.1 ≤ x.1 :=
        (List.pairwise_cons.1 h2).1 x (List.mem_append_right _ List.mem_cons_self)
      have heq : y.1 = x.1 := hanti _ _ hyx hxy
      exact (List.nodup_cons.1 hn).1 (List.mem_map.2 ⟨y, hy, heq⟩)

omit [BEq K] [LawfulBEq K] in
/-- The sort of a list with distinct keys is the sort of each permutation. -/
theorem sortByKey_eq_of_perm [LE K] [DecidableRel (α := K) (· ≤ ·)]
    (htrans : ∀ a b c : K, a ≤ b → b ≤ c → a ≤ c) (htotal : ∀ a b : K, a ≤ b ∨ b ≤ a)
    (hanti : ∀ a b : K, a ≤ b → b ≤ a → a = b) {l m : List (K × V)} (hn : NodupKeys l)
    (hp : l.Perm m) : sortByKey l = sortByKey m :=
  eq_of_perm_of_pairwise hanti _ _ (pairwise_sortByKey htrans htotal l)
    (pairwise_sortByKey htrans htotal m) (nodupKeys_sortByKey hn)
    ((sortByKey_perm l).trans (hp.trans (sortByKey_perm m).symm))

/-! ### The export shapes

Each export of the crate builds the map with `from_iter`, does one
operation, and writes the map back sorted by key. These are the statements
that `Project.RustHashMap.Spec` names, on the table instead of the list. -/

theorem get_ofEntries (hash : K → UInt64) (es : List (K × V)) (hn : es.length ≤ 2 ^ 30)
    (k : K) : Table.get hash (ofEntries hash es) k = HashMap.get (HashMap.ofEntries es) k := by
  obtain ⟨hw, -, -, hperm⟩ := wf_ofEntries hash es hn
  rw [hw.toLayout.get_eq]
  exact get_perm hperm (nodupKeys_ofEntries es) k

theorem containsKey_ofEntries (hash : K → UInt64) (es : List (K × V)) (hn : es.length ≤ 2 ^ 30)
    (k : K) :
    Table.containsKey hash (ofEntries hash es) k = HashMap.containsKey (HashMap.ofEntries es) k := by
  obtain ⟨hw, -, -, hperm⟩ := wf_ofEntries hash es hn
  rw [hw.toLayout.containsKey_eq]
  exact containsKey_perm hperm (nodupKeys_ofEntries es) k

theorem len_ofEntries (hash : K → UInt64) (es : List (K × V)) (hn : es.length ≤ 2 ^ 30) :
    len (ofEntries hash es) = HashMap.len (HashMap.ofEntries es) := by
  obtain ⟨hw, -, -, hperm⟩ := wf_ofEntries hash es hn
  rw [hw.len_eq]
  exact hperm.length_eq

theorem sortByKey_ofEntries [LE K] [DecidableRel (α := K) (· ≤ ·)]
    (htrans : ∀ a b c : K, a ≤ b → b ≤ c → a ≤ c) (htotal : ∀ a b : K, a ≤ b ∨ b ≤ a)
    (hanti : ∀ a b : K, a ≤ b → b ≤ a → a = b)
    (hash : K → UInt64) (es : List (K × V)) (hn : es.length ≤ 2 ^ 30) :
    sortByKey (toList (ofEntries hash es)) = sortByKey (HashMap.ofEntries es) := by
  obtain ⟨hw, -, -, hperm⟩ := wf_ofEntries hash es hn
  exact sortByKey_eq_of_perm htrans htotal hanti hw.toLayout.nodupKeys_toList hperm

theorem insert_ofEntries [LE K] [DecidableRel (α := K) (· ≤ ·)]
    (htrans : ∀ a b c : K, a ≤ b → b ≤ c → a ≤ c) (htotal : ∀ a b : K, a ≤ b ∨ b ≤ a)
    (hanti : ∀ a b : K, a ≤ b → b ≤ a → a = b)
    (hash : K → UInt64) (es : List (K × V)) (hn : es.length ≤ 2 ^ 30) (k : K) (v : V) :
    (Table.insert hash (ofEntries hash es) k v).1 = HashMap.get (HashMap.ofEntries es) k ∧
      sortByKey (toList (Table.insert hash (ofEntries hash es) k v).2) =
        sortByKey (HashMap.insert (HashMap.ofEntries es) k v).2 := by
  obtain ⟨hw, hcl, hb, hperm⟩ := wf_ofEntries hash es hn
  obtain ⟨hw', -, h1, h2⟩ := hw.insert hcl hb k v
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact get_perm hperm (nodupKeys_ofEntries es) k
  · exact sortByKey_eq_of_perm htrans htotal hanti hw'.toLayout.nodupKeys_toList
      (h2.trans (insert_perm hperm (nodupKeys_ofEntries es) k v).2)

theorem remove_ofEntries [LE K] [DecidableRel (α := K) (· ≤ ·)]
    (htrans : ∀ a b c : K, a ≤ b → b ≤ c → a ≤ c) (htotal : ∀ a b : K, a ≤ b ∨ b ≤ a)
    (hanti : ∀ a b : K, a ≤ b → b ≤ a → a = b)
    (hash : K → UInt64) (es : List (K × V)) (hn : es.length ≤ 2 ^ 30) (k : K) :
    (Table.remove hash (ofEntries hash es) k).1 = (HashMap.remove (HashMap.ofEntries es) k).1 ∧
      sortByKey (toList (Table.remove hash (ofEntries hash es) k).2) =
        sortByKey (HashMap.remove (HashMap.ofEntries es) k).2 := by
  obtain ⟨hw, -, -, hperm⟩ := wf_ofEntries hash es hn
  obtain ⟨hw', -, h1, h2⟩ := hw.remove k
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact (remove_perm hperm (nodupKeys_ofEntries es) k).1
  · exact sortByKey_eq_of_perm htrans htotal hanti hw'.toLayout.nodupKeys_toList
      (h2.trans (remove_perm hperm (nodupKeys_ofEntries es) k).2)

end OfEntries

end Table

end Wasm.RustStd.HashMap
