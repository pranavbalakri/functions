module

public import VerifiedSqrt.Arm.Classification32
public import VerifiedSqrt.Float.Rounding

@[expose] public section

namespace VerifiedSqrt.Arm

def normalizedCoefficient32 (n : Nat) : Nat := n * 2 ^ (23 - n.log2)

theorem normalizedCoefficient32_bounds (n : Nat) (lo : 0 < n) (hi : n < 2 ^ 24) :
    2 ^ 23 ≤ normalizedCoefficient32 n ∧ normalizedCoefficient32 n < 2 ^ 24 := by
  have hl : n.log2 ≤ 23 := by
    have h := (Nat.log2_lt (by omega : n ≠ 0)).mpr hi
    omega
  have hp : 0 < 2 ^ (23 - n.log2) := by positivity
  have hb := Nat.mul_le_mul_right (2 ^ (23 - n.log2)) (Nat.log2_self_le (by omega : n ≠ 0))
  have ht := Nat.mul_lt_mul_of_pos_right (Nat.lt_log2_self (n := n)) hp
  rw [← pow_add, show n.log2 + (23 - n.log2) = 23 by omega] at hb
  rw [← pow_add, show n.log2 + 1 + (23 - n.log2) = 24 by omega] at ht
  exact ⟨hb, ht⟩

theorem round32_exact (n : Nat) (source : Int) (lo : 0 < n) (hi : n < 2 ^ 24)
    (emin : -126 ≤ (n.log2 : Int) + source) (emax : (n.log2 : Int) + source ≤ 127) :
    round32 ⟨n, source⟩ =
      ⟨encode32 ((n.log2 : Int) + source + 127).toNat
        (normalizedCoefficient32 n - 2 ^ 23), 0⟩ := by
  have hl : n.log2 ≤ 23 := by
    have h := (Nat.log2_lt (by omega : n ≠ 0)).mpr hi
    omega
  have hb := normalizedCoefficient32_bounds n lo hi
  have hmax : max ((n.log2 : Int) + source - 23) (-149) =
      (n.log2 : Int) + source - 23 := max_eq_left (by omega)
  have hshift : (source - ((n.log2 : Int) + source - 23)).toNat = 23 - n.log2 := by omega
  have hbiased : ((n.log2 : Int) + source - 23 + 150).toNat =
      ((n.log2 : Int) + source + 127).toNat := by omega
  have hehi : ((n.log2 : Int) + source + 127).toNat < 255 := by omega
  have hmod : normalizedCoefficient32 n % 2 ^ 23 = normalizedCoefficient32 n - 2 ^ 23 := by omega
  norm_num at hb hmod
  have hcoeff : n * 2 ^ (23 - n.log2) = normalizedCoefficient32 n := rfl
  simp [round32, show ¬(n : Int) < 0 by omega, Nat.ne_of_gt lo, hmax,
    show ¬(n.log2 : Int) + source - 23 > source by omega, hshift, hbiased,
    hcoeff, show ¬normalizedCoefficient32 n < 8388608 by omega,
    show ¬normalizedCoefficient32 n ≥ 16777216 by omega,
    show ¬((n.log2 : Int) + source + 127).toNat ≥ 255 by omega,
    signed32, hmod, encode32]

theorem normalizedCoefficient32_mul (n : Nat) (lo : 0 < n) (hi : n < 2 ^ 24) :
    normalizedCoefficient32 n * 2 ^ n.log2 = n * 2 ^ 23 := by
  have hl : n.log2 ≤ 23 := by
    have h := (Nat.log2_lt (by omega : n ≠ 0)).mpr hi
    omega
  rw [normalizedCoefficient32, mul_assoc, ← pow_add,
    show 23 - n.log2 + n.log2 = 23 by omega]

theorem round32_exact_components (n : Nat) (source e : Int) (q : Nat)
    (hn : 0 < n)
    (he : max ((n.log2 : Int) + source - 23) (-149) = e)
    (hr : (if e > source then roundShiftEven n (e - source).toNat
      else (n * 2 ^ (source - e).toNat, false)) = (q, false))
    (qlo : 2 ^ 23 ≤ q) (qhi : q < 2 ^ 24) (ehi : (e + 150).toNat < 255) :
    round32 ⟨n, source⟩ = ⟨encode32 (e + 150).toNat (q - 2 ^ 23), 0⟩ := by
  have hmod : q % 8388608 = q - 8388608 := by omega
  simp only [round32, Int.natAbs_natCast, beq_iff_eq, Nat.ne_of_gt hn, ite_false, he, hr]
  simp [show ¬(n : Int) < 0 by omega, show ¬q < 8388608 by omega,
    show ¬q ≥ 16777216 by omega, show ¬(e + 150).toNat ≥ 255 by omega,
    signed32, hmod, encode32]

theorem round32_subnormal_product (n : Nat) (lo : 0 < n) (hi : n < 2 ^ 23) :
    round32 ⟨(n * 2 ^ 23 : Nat), -124⟩ =
      ⟨encode32 (n.log2 + 26) (normalizedCoefficient32 n - 2 ^ 23), 0⟩ := by
  have hl : n.log2 ≤ 22 := by
    have h := (Nat.log2_lt (by omega : n ≠ 0)).mpr hi
    omega
  have hb := normalizedCoefficient32_bounds n lo (by omega)
  have hm := normalizedCoefficient32_mul n lo (by omega)
  have hlog := log2_mul_two_pow n 23 lo
  have hmax : max (((n * 2 ^ 23).log2 : Int) + -124 - 23) (-149) =
      (n.log2 : Int) - 124 := by rw [hlog]; omega
  have hr : (if (n.log2 : Int) - 124 > -124 then
      roundShiftEven (n * 2 ^ 23) ((n.log2 : Int) - 124 - -124).toNat
      else (n * 2 ^ 23 * 2 ^ (-124 - ((n.log2 : Int) - 124)).toNat, false)) =
      (normalizedCoefficient32 n, false) := by
    split
    · rw [show ((n.log2 : Int) - 124 - -124).toNat = n.log2 by omega, ← hm]
      exact roundShiftEven_exact_multiple _ _
    · rename_i h
      have hz : n.log2 = 0 := by omega
      simp [hz, normalizedCoefficient32]
  have hbiased : ((n.log2 : Int) - 124 + 150).toNat = n.log2 + 26 := by omega
  have hn : 0 < n * 2 ^ 23 := by positivity
  have h := round32_exact_components (n * 2 ^ 23) (-124) ((n.log2 : Int) - 124)
    (normalizedCoefficient32 n) hn hmax hr hb.1 hb.2 (by omega)
  simpa only [hbiased] using h

end VerifiedSqrt.Arm
