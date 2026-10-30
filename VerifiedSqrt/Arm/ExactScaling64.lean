module

public import VerifiedSqrt.Arm.Classification64
public import VerifiedSqrt.Float.Rounding

@[expose] public section

namespace VerifiedSqrt.Arm

def normalizedCoefficient64 (n : Nat) : Nat := n * 2 ^ (52 - n.log2)

theorem normalizedCoefficient64_bounds (n : Nat) (lo : 0 < n) (hi : n < 2 ^ 53) :
    2 ^ 52 ≤ normalizedCoefficient64 n ∧ normalizedCoefficient64 n < 2 ^ 53 := by
  have hl : n.log2 ≤ 52 := by
    have h := (Nat.log2_lt (by omega : n ≠ 0)).mpr hi
    omega
  have hp : 0 < 2 ^ (52 - n.log2) := by positivity
  have hb := Nat.mul_le_mul_right (2 ^ (52 - n.log2)) (Nat.log2_self_le (by omega : n ≠ 0))
  have ht := Nat.mul_lt_mul_of_pos_right (Nat.lt_log2_self (n := n)) hp
  rw [← pow_add, show n.log2 + (52 - n.log2) = 52 by omega] at hb
  rw [← pow_add, show n.log2 + 1 + (52 - n.log2) = 53 by omega] at ht
  exact ⟨hb, ht⟩

theorem round64_exact (n : Nat) (source : Int) (lo : 0 < n) (hi : n < 2 ^ 53)
    (emin : -1022 ≤ (n.log2 : Int) + source) (emax : (n.log2 : Int) + source ≤ 1023) :
    round64 ⟨n, source⟩ =
      ⟨encode64 ((n.log2 : Int) + source + 1023).toNat
        (normalizedCoefficient64 n - 2 ^ 52), 0⟩ := by
  have hl : n.log2 ≤ 52 := by
    have h := (Nat.log2_lt (by omega : n ≠ 0)).mpr hi
    omega
  have hb := normalizedCoefficient64_bounds n lo hi
  have hmax : max ((n.log2 : Int) + source - 52) (-1074) =
      (n.log2 : Int) + source - 52 := max_eq_left (by omega)
  have hshift : (source - ((n.log2 : Int) + source - 52)).toNat = 52 - n.log2 := by omega
  have hbiased : ((n.log2 : Int) + source - 52 + 1075).toNat =
      ((n.log2 : Int) + source + 1023).toNat := by omega
  have hehi : ((n.log2 : Int) + source + 1023).toNat < 2047 := by omega
  have hmod : normalizedCoefficient64 n % 2 ^ 52 = normalizedCoefficient64 n - 2 ^ 52 := by omega
  norm_num at hb hmod
  have hcoeff : n * 2 ^ (52 - n.log2) = normalizedCoefficient64 n := rfl
  simp [round64, show ¬(n : Int) < 0 by omega, Nat.ne_of_gt lo, hmax,
    show ¬(n.log2 : Int) + source - 52 > source by omega, hshift, hbiased,
    hcoeff, show ¬normalizedCoefficient64 n < 4503599627370496 by omega,
    show ¬normalizedCoefficient64 n ≥ 9007199254740992 by omega,
    show ¬((n.log2 : Int) + source + 1023).toNat ≥ 2047 by omega,
    signed64, hmod, encode64]

theorem normalizedCoefficient64_mul (n : Nat) (lo : 0 < n) (hi : n < 2 ^ 53) :
    normalizedCoefficient64 n * 2 ^ n.log2 = n * 2 ^ 52 := by
  have hl : n.log2 ≤ 52 := by
    have h := (Nat.log2_lt (by omega : n ≠ 0)).mpr hi
    omega
  rw [normalizedCoefficient64, mul_assoc, ← pow_add,
    show 52 - n.log2 + n.log2 = 52 by omega]

theorem round64_exact_components (n : Nat) (source e : Int) (q : Nat)
    (hn : 0 < n)
    (he : max ((n.log2 : Int) + source - 52) (-1074) = e)
    (hr : (if e > source then roundShiftEven n (e - source).toNat
      else (n * 2 ^ (source - e).toNat, false)) = (q, false))
    (qlo : 2 ^ 52 ≤ q) (qhi : q < 2 ^ 53) (ehi : (e + 1075).toNat < 2047) :
    round64 ⟨n, source⟩ = ⟨encode64 (e + 1075).toNat (q - 2 ^ 52), 0⟩ := by
  have hmod : q % 4503599627370496 = q - 4503599627370496 := by omega
  simp only [round64, Int.natAbs_natCast, beq_iff_eq, Nat.ne_of_gt hn, ite_false, he, hr]
  simp [show ¬(n : Int) < 0 by omega, show ¬q < 4503599627370496 by omega,
    show ¬q ≥ 9007199254740992 by omega, show ¬(e + 1075).toNat ≥ 2047 by omega,
    signed64, hmod, encode64]

theorem round64_subnormal_product (n : Nat) (lo : 0 < n) (hi : n < 2 ^ 52) :
    round64 ⟨(n * 2 ^ 52 : Nat), -1020⟩ =
      ⟨encode64 (n.log2 + 55) (normalizedCoefficient64 n - 2 ^ 52), 0⟩ := by
  have hl : n.log2 ≤ 51 := by
    have h := (Nat.log2_lt (by omega : n ≠ 0)).mpr hi
    omega
  have hb := normalizedCoefficient64_bounds n lo (by omega)
  have hm := normalizedCoefficient64_mul n lo (by omega)
  have hlog := log2_mul_two_pow n 52 lo
  have hmax : max (((n * 2 ^ 52).log2 : Int) + -1020 - 52) (-1074) =
      (n.log2 : Int) - 1020 := by rw [hlog]; omega
  have hr : (if (n.log2 : Int) - 1020 > -1020 then
      roundShiftEven (n * 2 ^ 52) ((n.log2 : Int) - 1020 - -1020).toNat
      else (n * 2 ^ 52 * 2 ^ (-1020 - ((n.log2 : Int) - 1020)).toNat, false)) =
      (normalizedCoefficient64 n, false) := by
    split
    · rw [show ((n.log2 : Int) - 1020 - -1020).toNat = n.log2 by omega, ← hm]
      exact roundShiftEven_exact_multiple _ _
    · rename_i h
      have hz : n.log2 = 0 := by omega
      simp [hz, normalizedCoefficient64]
  have hbiased : ((n.log2 : Int) - 1020 + 1075).toNat = n.log2 + 55 := by omega
  have hn : 0 < n * 2 ^ 52 := by positivity
  have h := round64_exact_components (n * 2 ^ 52) (-1020) ((n.log2 : Int) - 1020)
    (normalizedCoefficient64 n) hn hmax hr hb.1 hb.2 (by omega)
  simpa only [hbiased] using h

end VerifiedSqrt.Arm
