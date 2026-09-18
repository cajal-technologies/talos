import CodeLib.RustStd.HashMap.TableRefinement
import CodeLib.RustStd.HashMap.Swar
import CodeLib.RustStd.HashMap.ProbeWasm

/-!
# Where the compiled probe loop stops

The probe loop of absolute `func 18`, WAT lines 4339 to 4545, carries no
fuel.  It stops at the first window that holds the key, and otherwise at the
first window with an `EMPTY` byte.  A total weakest precondition needs a
measure, so this module names the window that bounds the walk.

`Table.WF.exists_empty` gives one `EMPTY` bucket from `Table.Clean` and
`1 ≤ growthLeft`, and `Table.Layout.firstSpecial_probe` turns that bucket
into a window inside `Table.probeFuel`.  `exists_first_empty_window` takes
the least such window.  The measure of the loop is that window minus the
current one.

`Table.Layout` alone is not enough, which is why `Func15Spec` takes
`Table.WF` and `Table.Clean`.  `Layout` relates the control bytes to the
slots and says nothing about `growthLeft`, so it admits a table whose every
byte is full, and the compiled loop does not stop on such a table.

The `SWAR` bridges below give the same masks in the operand order that the
compiled code builds them, and `fixInsertIndex_spec` says where
`fix_insert_index` lands.

Move all of these beside the probe lemmas of
`CodeLib.RustStd.HashMap.TableRefinement` when `codelib` is edited for
another reason.
-/

namespace Project.RustHashMap.ProbeStop

open Wasm.RustStd.HashMap
open Wasm.RustStd.HashMap.Table

variable {K V : Type} {hash : K → UInt64} {t : Table K V}

/-- The stride of window `n` is eight groups times `n`.  `probeSeq_pos`
proves this on the way and keeps it private. -/
theorem probeSeq_stride (t : Table K V) (h : UInt64) (n : Nat) :
    (probeSeq t h n).stride = 8 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [probeSeq, ProbeSeq.next, ih]; omega

/-- A `Clean` table with room has a window with an `EMPTY` byte, inside the
probe fuel. -/
theorem exists_empty_window (hw : WF hash t) (hcl : Clean t) (hg : 1 ≤ t.growthLeft)
    (h : UInt64) : ∃ n, n < probeFuel t ∧ matchEmpty (window t h n) = true := by
  obtain ⟨e, he, hemp⟩ := hw.exists_empty hcl hg
  have hne := hw.toLayout.firstSpecial_probe h he hemp
  rcases hf : firstSpecial t h (probeFuel t) 0 with _ | ⟨n, j⟩
  · exact absurd hf hne
  obtain ⟨-, hlt, hls, -⟩ := firstSpecial_some t h _ _ _ _ hf
  unfold window at hls
  obtain ⟨hj, hsp, -⟩ := lowestSpecial_groupAt_some hls
  refine ⟨n, by omega, ?_⟩
  rw [matchEmpty_window]
  refine ⟨j, hj, ?_⟩
  have hp := hw.toLayout.probe_lt h n
  have hmir := hw.toLayout.mirror ((probeSeq t h n).pos + j) (by omega)
  by_cases hpad : IsPad t.buckets ((probeSeq t h n).pos + j)
  · rw [hmir, if_pos hpad]
  · rw [hmir, if_neg hpad]
    rw [hmir, if_neg hpad] at hsp
    exact hcl.1 _ (Nat.mod_lt _ hw.toLayout.pos) hsp

/-- The first window with an `EMPTY` byte.  The compiled loop stops at or
before it, so `N - n` is the measure of the walk. -/
theorem exists_first_empty_window (hw : WF hash t) (hcl : Clean t)
    (hg : 1 ≤ t.growthLeft) (h : UInt64) :
    ∃ N, N < probeFuel t ∧ matchEmpty (window t h N) = true ∧
      ∀ m, m < N → matchEmpty (window t h m) = false := by
  have hex : ∃ n, matchEmpty (window t h n) = true := by
    obtain ⟨n, -, hn⟩ := exists_empty_window hw hcl hg h
    exact ⟨n, hn⟩
  obtain ⟨n, hn, hmatch⟩ := exists_empty_window hw hcl hg h
  refine ⟨Nat.find hex, Nat.lt_of_le_of_lt (Nat.find_le hmatch) hn, Nat.find_spec hex, ?_⟩
  intro m hm
  exact Bool.eq_false_iff.mpr (Nat.find_min hex hm)

/-! ## The `SWAR` formulas in the order the compiled code writes them -/

/-- `Group::match_tag`, with the `not` on the left and the tag lanes as
`repeatByte`.  `swarMatchTag_of_wasm` states the same word with the two
operands of the `i64.and` the other way round and the lanes as a product. -/
theorem swarMatchTag_wasm (tag : UInt8) (x : UInt64) :
    ((x ^^^ repeatByte tag) ^^^ 18446744073709551615) &&&
        ((x ^^^ repeatByte tag) + 18374403900871474943) &&& 9259542123273814144 =
      swarMatchTag tag x := by
  rw [show (9259542123273814144 : UInt64) = REP80 from rfl,
    UInt64.and_comm ((x ^^^ repeatByte tag) ^^^ 18446744073709551615),
    ← repeatByte_eq_mul_REP01]
  exact swarMatchTag_of_wasm tag x

/-- The tag of a hash is a `FULL` control byte. -/
theorem isFull_h2 (h : UInt64) : isFull (h2 h) = true := by
  have hb : ((h >>> 25) &&& 127).toNat < 128 := by
    rw [UInt64.toNat_and, show (127 : UInt64).toNat = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hlt : (h2 h).toNat < 128 := by
    rw [← UInt8.toNat_toUInt64, h2_toUInt64]
    exact hb
  unfold isFull
  rw [decide_eq_true_iff, UInt8.lt_iff_toNat_lt]
  exact hlt

/-- A byte that the compiled `match_tag` flags names a full bucket, so the
slot of that bucket holds a pair.  The compiled walk loads the key of every
flagged byte, so a proof of that walk needs this. -/
theorem slotAt_isSome_of_mem_matchBytes (hw : Layout hash t) (h : UInt64) (n : Nat)
    {j : Nat}
    (hj : j ∈ setBytes (swarMatchTag (h2 h) (groupWord (window t h n)))) :
    (t.slotAt (probeIdx t h n j)).isSome = true := by
  have hg : (window t h n).length = 8 := groupAt_length _ _
  simp only [setBytes, List.mem_filter, List.mem_range] at hj
  obtain ⟨hj8, hb⟩ := hj
  have hfullb : isFull ((window t h n).getD j EMPTY) = true :=
    isFull_of_hasBit_swarMatchTag hg hj8 (isFull_h2 h) hb
  rw [hw.window_getD h n j hj8] at hfullb
  by_cases hpad : IsPad t.buckets ((probeSeq t h n).pos + j)
  · rw [if_pos hpad] at hfullb
    exact absurd hfullb (by decide)
  · rw [if_neg hpad] at hfullb
    exact (hw.full_iff _ (hw.probeIdx_lt h n j)).mp hfullb

/-- `slotAt_isSome_of_mem_matchBytes` with `window` and `probeIdx` unfolded,
which is the shape a body proof reads off the compiled probe. -/
theorem slotAt_isSome_of_mem_matchTag (hw : Layout hash t) (h : UInt64) (n : Nat)
    {j : Nat}
    (hj : j ∈ setBytes
      (swarMatchTag (h2 h) (groupWord (groupAt t (probeSeq t h n).pos)))) :
    (t.slotAt (((probeSeq t h n).pos + j) % t.buckets)).isSome = true :=
  slotAt_isSome_of_mem_matchBytes hw h n hj

/-- Every `match_tag` mask carries high bits only. -/
theorem swarMatchTag_and_REP80 (tag : UInt8) (x : UInt64) :
    swarMatchTag tag x &&& REP80 = swarMatchTag tag x := by
  unfold swarMatchTag
  rw [UInt64.and_assoc, UInt64.and_self]

/-- `Group::match_empty_or_deleted` as the compiled code writes it. -/
theorem swarMatchEmptyOrDeleted_wasm (x : UInt64) :
    x &&& (9259542123273814144 : UInt64) = swarMatchEmptyOrDeleted x := rfl

/-- `Group::match_empty`, from the word that `match_empty_or_deleted` left
in local 5 and the group word in local 7. -/
theorem swarMatchEmpty_wasm (x : UInt64) :
    (x &&& (9259542123273814144 : UInt64)) &&& (x <<< 1) = swarMatchEmpty x := by
  unfold swarMatchEmpty
  rw [show (9259542123273814144 : UInt64) = REP80 from rfl, UInt64.and_assoc,
    UInt64.and_comm REP80, ← UInt64.and_assoc]

/-- The mask of `match_empty_or_deleted` is zero exactly when the group has
no special byte, which is the guard of WAT line 4405. -/
theorem swarMatchEmptyOrDeleted_eq_zero_iff {g : List UInt8} (hg : g.length = 8) :
    swarMatchEmptyOrDeleted (groupWord g) = 0 ↔ lowestSpecial g = none := by
  rw [← lowestSetByte_swarMatchEmptyOrDeleted hg]
  unfold lowestSetByte swarMatchEmptyOrDeleted
  rw [eq_zero_iff_hasBit]
  constructor
  · intro h
    rw [List.find?_eq_none]
    intro j hj
    rw [h j (List.mem_range.mp hj)]
    exact Bool.false_ne_true
  · intro h j hj
    rw [List.find?_eq_none] at h
    exact Bool.eq_false_iff.mpr (h j (List.mem_range.mpr hj))

/-! ## The insert index -/

/-- `i64.ctz` of a match mask, wrapped and shifted by three, is the lowest
flagged byte.  `matchIndex_of_wasm` states the same step with the group
position added and the bucket mask applied; `fix_insert_index` reads the
group at zero, where neither is needed. -/
theorem ctzByte_of_wasm {msk : UInt64} (hmask : msk &&& REP80 = msk) {j0 : Nat}
    (hlow : lowestSetByte msk = some j0) :
    (UInt64.ofNat (Wasm.ctz64 64 msk)).toUInt32 >>> 3 = UInt32.ofNat j0 := by
  have hj8 : j0 < 8 := List.mem_range.mp (List.mem_of_find?_eq_some hlow)
  obtain ⟨hbit, hmin⟩ := lowest_bit_of_lowestSetByte hmask hlow
  have hctz : Wasm.ctz64 64 msk = 8 * j0 + 7 := by
    have := ctz64_eq 64 (Nat.le_refl 64) msk (8 * j0 + 7) (by omega) hbit hmin
    omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight, UInt64.toNat_toUInt32, UInt64.toNat_ofNat', hctz,
    show (3 : UInt32).toNat % 32 = 3 from rfl, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : 8 * j0 + 7 < 2 ^ 64),
    UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega : j0 < UInt32.size)]
  omega

/-- `(i - 8) & bucket_mask`, the mirror position that the compiled
`set_ctrl` computes at WAT lines 4467 to 4472, is the first half of
`Table.index2`. -/
theorem index2_of_wasm (t : Table K V) {m : Nat} (hm : m ≤ 32)
    (hb : t.buckets = 2 ^ m) {i : Nat} (hi : i < 2 ^ 32) :
    ((UInt32.ofNat i - 8) &&& UInt32.ofNat (t.buckets - 1)).toNat
      = wrapSub i 8 t.buckets := by
  have hdvd : 2 ^ m ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hm
  have hstep : (UInt32.ofNat i - 8).toNat = (i + 2 ^ 32 - 8) % 2 ^ 32 := by
    simp only [UInt32.toNat_sub, UInt32.toNat_ofNat', UInt32.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega : i < 4294967296)]
    congr 1
    omega
  rw [hb, and_mask_toNat _ hm, hstep, wrapSub, Nat.mod_mod_of_dvd _ hdvd]

/-- With room to insert and at most eight buckets, the first group holds a
special byte, and the lowest one names an `EMPTY` bucket.  `fix_insert_index`
reads that group at WAT lines 4443 to 4453. -/
theorem lowestSpecial_groupAt_zero (hwf : WF hash t) (hcl : Clean t)
    (hg : 1 ≤ t.growthLeft) (hb8 : t.buckets ≤ 8) :
    ∃ j0, lowestSpecial (groupAt t 0) = some j0 ∧ j0 < t.buckets ∧
      t.ctrlAt j0 = EMPTY := by
  obtain ⟨e, he, hemp⟩ := hwf.exists_empty hcl hg
  have hex : lowestSpecial (groupAt t 0) ≠ none :=
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
    exact ⟨x, rfl, by omega, hcl.1 _ (by omega) hsx⟩

/-- The candidate that the compiled probe records always fixes up to an
`EMPTY` bucket.  In a table with more than eight buckets the candidate is
already special, because no byte of a window is padding; with eight or
fewer, `fix_insert_index` reads the first group instead, and the room that
`growth_left` gives puts an `EMPTY` byte in it. -/
theorem fixInsertIndex_spec (hwf : WF hash t) (hcl : Clean t)
    (hg : 1 ≤ t.growthLeft) {c : Nat} (hc : c < t.buckets)
    (hspecial : isSpecial (t.ctrlAt c) = true ∨ t.buckets ≤ 8) :
    fixInsertIndex t c < t.buckets ∧ t.ctrlAt (fixInsertIndex t c) = EMPTY := by
  unfold fixInsertIndex
  by_cases hfull : isFull (t.ctrlAt c) = true
  · rw [if_pos hfull]
    have hb8 : t.buckets ≤ 8 := by
      rcases hspecial with hs | hs
      · exact absurd hfull (isSpecial_iff.mp hs)
      · exact hs
    obtain ⟨x, hls0, hxb, hxe⟩ := lowestSpecial_groupAt_zero hwf hcl hg hb8
    rw [hls0]
    exact ⟨hxb, hxe⟩
  · rw [if_neg hfull]
    exact ⟨hc, hcl.1 c hc (isSpecial_iff.mpr hfull)⟩

/-! ## The two byte bridges of the insert tail -/

/-- `i32.load8_s` of a control byte, compared against zero with `i32.lt_s`,
is `Table.isSpecial`.  That is the test of WAT lines 4435 to 4441. -/
theorem ltS_signByte (b : UInt8) :
    ((Int32.ofInt (Wasm.signExtend b.toNat 8)).toUInt32.toInt32 <
        (0 : UInt32).toInt32) ↔ isSpecial b = true := by
  have hb : b.toNat < 256 := by
    have := UInt8.toNat_lt_size b
    simpa using this
  have hzero : ((0 : UInt32).toInt32).toInt = 0 := rfl
  rw [Int32.toInt32_toUInt32, Int32.lt_iff_toInt_lt, hzero,
    Int32.toInt_ofInt_of_le
      (by unfold Wasm.signExtend; dsimp only; split <;> omega)
      (by unfold Wasm.signExtend; dsimp only; split <;> omega)]
  unfold Wasm.signExtend
  dsimp only
  simp only [isSpecial, decide_eq_true_eq]
  rw [show ((0x80 : UInt8) ≤ b) ↔ (128 ≤ b.toNat) from by
    rw [UInt8.le_iff_toNat_le]; rfl]
  split <;> omega

/-- The byte that `set_ctrl` stores at WAT lines 4455 to 4462: the hash,
shifted by 25, wrapped to 32 bits and masked to seven bits, is the tag. -/
theorem tagByte_of_wasm (y : UInt64) :
    ((y >>> 25).toUInt32 &&& 127).toUInt8 = h2 y := by
  unfold h2
  apply UInt8.toNat_inj.mp
  simp [UInt64.toNat_toUInt8]

end Project.RustHashMap.ProbeStop
