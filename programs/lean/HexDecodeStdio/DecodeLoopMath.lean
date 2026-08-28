import Mathlib
import HexDecodeStdio.DecodeLoopReserveOperational

namespace Submission.HexDecodeStdio

open Project.HexStdio.Spec

theorem decode_append_even (left right : List UInt8)
    (heven : left.length % 2 = 0) :
    decode (left ++ right) =
      Option.bind (decode left) (fun pref =>
        Option.map (fun suffix => pref ++ suffix) (decode right)) := by
  induction left using List.twoStepInduction generalizing right with
  | nil => simp [decode]
  | singleton hi => simp at heven
  | cons_cons hi lo rest ih _ =>
      have hrest : rest.length % 2 = 0 := by
        have hlen : (hi :: lo :: rest).length = rest.length + 2 := by
          simp
        rw [hlen, Nat.add_mod] at heven
        norm_num [Nat.mod_mod] at heven
        exact heven
      simp only [List.cons_append, decode]
      rw [ih right hrest]
      cases hhi : hexValue hi <;> simp [hhi]
      cases hlo : hexValue lo <;> simp [hlo]
      cases hp : decode rest <;> simp [hp]
      cases hr : decode right <;> simp [hr, List.append_assoc]

theorem byte_from_div_mod (byte : UInt8) :
    16 * UInt8.ofNat (byte.toNat / 16) + UInt8.ofNat (byte.toNat % 16) =
      byte := by
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_add, UInt8.toNat_mul, UInt8.toNat_ofNat]
  have hb := byte.toNat_lt
  norm_num at hb ⊢
  omega

theorem decode_append_valid_pair (pref rest decoded : List UInt8)
    (hi lo byte : UInt8)
    (heven : pref.length % 2 = 0)
    (hprefix : decode pref = some decoded)
    (hhi : hexValue hi = some (byte.toNat / 16))
    (hlo : hexValue lo = some (byte.toNat % 16)) :
    decode (pref ++ hi :: lo :: rest) =
      (decode rest).map (fun suffix => decoded ++ byte :: suffix) := by
  rw [decode_append_even pref (hi :: lo :: rest) heven, hprefix]
  simp only [decode, hhi, hlo, Option.bind_some, Option.map_eq_map]
  cases hrest : decode rest <;> simp [hrest]
  exact byte_from_div_mod byte

theorem decode_append_invalid_high (pref rest decoded : List UInt8)
    (hi lo : UInt8) (heven : pref.length % 2 = 0)
    (hprefix : decode pref = some decoded)
    (hhi : hexValue hi = none) :
    decode (pref ++ hi :: lo :: rest) = none := by
  rw [decode_append_even pref (hi :: lo :: rest) heven, hprefix]
  simp [decode, hhi]

theorem decode_append_invalid_low (pref rest decoded : List UInt8)
    (hi lo : UInt8) (hiNibble : Nat)
    (heven : pref.length % 2 = 0)
    (hprefix : decode pref = some decoded)
    (hhi : hexValue hi = some hiNibble)
    (hlo : hexValue lo = none) :
    decode (pref ++ hi :: lo :: rest) = none := by
  rw [decode_append_even pref (hi :: lo :: rest) heven, hprefix]
  simp [decode, hhi, hlo]

theorem decode_append_empty (pref decoded : List UInt8)
    (heven : pref.length % 2 = 0)
    (hprefix : decode pref = some decoded) :
    decode pref = some decoded := hprefix

theorem even_tail_of_append_even (pref remaining : List UInt8)
    (hp : pref.length % 2 = 0)
    (hall : (pref ++ remaining).length % 2 = 0) :
    remaining.length % 2 = 0 := by
  simpa [List.length_append, Nat.add_mod, hp, Nat.mod_mod] using hall

theorem decode_some_length (input output : List UInt8)
    (h : decode input = some output) : input.length = 2 * output.length := by
  induction input using List.twoStepInduction generalizing output with
  | nil =>
      simp [decode] at h
      subst output
      simp
  | singleton byte => simp [decode] at h
  | cons_cons hi lo rest ih =>
      simp only [decode] at h
      cases hhi : hexValue hi with
      | none => simp [hhi] at h
      | some hiNibble =>
          cases hlo : hexValue lo with
          | none => simp [hhi, hlo] at h
          | some loNibble =>
              cases hrest : decode rest with
              | none => simp [hhi, hlo, hrest] at h
              | some tail =>
                  simp [hhi, hlo, hrest] at h
                  subst output
                  have hlen := ih tail hrest
                  simp
                  omega

end Submission.HexDecodeStdio
