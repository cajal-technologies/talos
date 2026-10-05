import HexDecodeStdio.DecodeSpec
import HexDecodeStdio.DecodeIterator

namespace Project.HexDecodeStdio

open Project.HexStdio.Spec

theorem decimal_route (c : UInt8)
    (h : 48 ≤ c.toNat ∧ c.toNat ≤ 57) : HexRoute.decimal.valid c := by
  have hc : c = UInt8.ofNat c.toNat := UInt8.ofNat_toNat.symm
  have hn := c.toNat_lt
  generalize c.toNat = n at hc hn
  subst c
  interval_cases n <;> revert h <;> simp only [HexRoute.valid] <;> decide +kernel

theorem lower_route (c : UInt8)
    (h : 97 ≤ c.toNat ∧ c.toNat ≤ 102) : HexRoute.lower.valid c := by
  have hc : c = UInt8.ofNat c.toNat := UInt8.ofNat_toNat.symm
  have hn := c.toNat_lt
  generalize c.toNat = n at hc hn
  subst c
  interval_cases n <;> revert h <;> simp only [HexRoute.valid] <;> decide +kernel

theorem upper_route (c : UInt8)
    (h : 65 ≤ c.toNat ∧ c.toNat ≤ 70) : HexRoute.upper.valid c := by
  have hc : c = UInt8.ofNat c.toNat := UInt8.ofNat_toNat.symm
  have hn := c.toNat_lt
  generalize c.toNat = n at hc hn
  subst c
  interval_cases n <;> revert h <;> simp only [HexRoute.valid] <;> decide +kernel

theorem decimal_nibble (c : UInt8)
    (h : 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    (HexRoute.decimal.nibble c).toNat = c.toNat - 48 := by
  have hc : c = UInt8.ofNat c.toNat := UInt8.ofNat_toNat.symm
  have hn := c.toNat_lt
  generalize c.toNat = n at hc hn
  subst c
  interval_cases n <;> revert h <;> simp only [HexRoute.nibble] <;> decide +kernel

theorem lower_nibble (c : UInt8)
    (h : 97 ≤ c.toNat ∧ c.toNat ≤ 102) :
    (HexRoute.lower.nibble c).toNat = c.toNat - 97 + 10 := by
  have hc : c = UInt8.ofNat c.toNat := UInt8.ofNat_toNat.symm
  have hn := c.toNat_lt
  generalize c.toNat = n at hc hn
  subst c
  interval_cases n <;> revert h <;> simp only [HexRoute.nibble] <;> decide +kernel

theorem upper_nibble (c : UInt8)
    (h : 65 ≤ c.toNat ∧ c.toNat ≤ 70) :
    (HexRoute.upper.nibble c).toNat = c.toNat - 65 + 10 := by
  have hc : c = UInt8.ofNat c.toNat := UInt8.ofNat_toNat.symm
  have hn := c.toNat_lt
  generalize c.toNat = n at hc hn
  subst c
  interval_cases n <;> revert h <;> simp only [HexRoute.nibble] <;> decide +kernel

theorem hexValue_some_route (c : UInt8) (n : Nat)
    (h : hexValue c = some n) :
    ∃ route : HexRoute, route.valid c ∧ (route.nibble c).toNat = n := by
  simp only [hexValue] at h
  split at h <;> rename_i hdigit
  · simp only [Option.some.injEq] at h
    subst n
    exact ⟨.decimal, decimal_route c hdigit, decimal_nibble c hdigit⟩
  · split at h <;> rename_i hlower
    · simp only [Option.some.injEq] at h
      subst n
      exact ⟨.lower, lower_route c hlower, lower_nibble c hlower⟩
    · split at h <;> rename_i hupper
      · simp only [Option.some.injEq] at h
        subst n
        exact ⟨.upper, upper_route c hupper, upper_nibble c hupper⟩
      · contradiction

set_option maxHeartbeats 2000000 in
theorem hexValue_of_route_valid (route : HexRoute) (c : UInt8)
    (h : route.valid c) :
    hexValue c = some (route.nibble c).toNat := by
  have hc : c = UInt8.ofNat c.toNat := UInt8.ofNat_toNat.symm
  have hn := c.toNat_lt
  generalize c.toNat = n at hc hn
  subst c
  cases route <;> interval_cases n <;> revert h <;>
    simp only [HexRoute.valid, HexRoute.nibble, hexValue] <;> decide +kernel

theorem hexValue_none_tests (c : UInt8) (h : hexValue c = none) :
    ¬ (((4294967231 + c.toUInt32) &&& 255) < 6) ∧
    ¬ (((4294967199 + c.toUInt32) &&& 255) < 6) ∧
    ¬ (((4294967248 + c.toUInt32) &&& 255) < 10) := by
  have hc : c = UInt8.ofNat c.toNat := UInt8.ofNat_toNat.symm
  have hn := c.toNat_lt
  generalize c.toNat = n at hc hn
  subst c
  interval_cases n <;> revert h <;> simp only [hexValue] <;> decide +kernel

/-- Combining two four-bit route values is exactly the byte construction in
the mathematical decoder. -/
theorem nibble_or_eq_ofNat (lo hi : UInt32)
    (hlo : lo.toNat < 16) (hhi : hi.toNat < 16) :
    (lo ||| (hi <<< (4 : UInt32))).toUInt8 =
      UInt8.ofNat (16 * hi.toNat + lo.toNat) := by
  have elo : lo = UInt32.ofNat lo.toNat := by
    apply UInt32.toNat_inj.mp
    simp
  have ehi : hi = UInt32.ofNat hi.toNat := by
    apply UInt32.toNat_inj.mp
    simp
  generalize hloNat : lo.toNat = loNat at hlo elo ⊢
  generalize hhiNat : hi.toNat = hiNat at hhi ehi ⊢
  interval_cases loNat <;> interval_cases hiNat <;> simp_all <;> decide

theorem hexValue_some_lt (c : UInt8) (n : Nat)
    (h : hexValue c = some n) : n < 16 := by
  simp only [hexValue] at h
  split at h <;> rename_i hdigit
  · simp only [Option.some.injEq] at h
    omega
  · split at h <;> rename_i hlower
    · simp only [Option.some.injEq] at h
      omega
    · split at h <;> rename_i hupper
      · simp only [Option.some.injEq] at h
        omega
      · contradiction

theorem route_pair_byte (hi lo : UInt8) (hiNibble loNibble : Nat)
    (hiRoute loRoute : HexRoute)
    (hhi : (hiRoute.nibble hi).toNat = hiNibble)
    (hlo : (loRoute.nibble lo).toNat = loNibble)
    (hhiLt : hiNibble < 16) (hloLt : loNibble < 16) :
    (loRoute.nibble lo |||
        (hiRoute.nibble hi <<< (4 : UInt32))).toUInt8 =
      UInt8.ofNat (16 * hiNibble + loNibble) := by
  calc
    _ = UInt8.ofNat
        (16 * (hiRoute.nibble hi).toNat + (loRoute.nibble lo).toNat) :=
      nibble_or_eq_ofNat _ _ (hlo.symm ▸ hloLt) (hhi.symm ▸ hhiLt)
    _ = _ := by rw [hhi, hlo]

end Project.HexDecodeStdio
