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

Move these three beside the probe lemmas of
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

/-- `Group::match_empty`, from the word that `match_empty_or_deleted` left
in local 5. -/
theorem swarMatchEmpty_wasm (x : UInt64) :
    (x <<< 1) &&& (9259542123273814144 &&& x) = swarMatchEmpty x := by
  unfold swarMatchEmpty
  rw [show (9259542123273814144 : UInt64) = REP80 from rfl,
    UInt64.and_comm (x <<< 1), UInt64.and_assoc, UInt64.and_comm REP80]

end Project.RustHashMap.ProbeStop
