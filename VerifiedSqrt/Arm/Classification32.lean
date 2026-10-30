module

public import VerifiedSqrt.Arm.Encoding32

@[expose] public section

namespace VerifiedSqrt.Arm

theorem magnitude32_bits (x : UInt32) :
    (x &&& 0x7fffffff).toNat = x.toNat % 2 ^ 31 := by
  rw [UInt32.toNat_and]
  change x.toNat &&& (2 ^ 31 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem isZero32_iff (x : UInt32) : isZero32 x = true ↔ x.toNat % 2 ^ 31 = 0 := by
  simp only [isZero32, beq_iff_eq, ← UInt32.toNat_inj, magnitude32_bits]
  rfl

theorem isInf32_iff (x : UInt32) :
    isInf32 x = true ↔ x.toNat % 2 ^ 31 = 0x7f800000 := by
  simp only [isInf32, beq_iff_eq, ← UInt32.toNat_inj, magnitude32_bits]
  rfl

theorem positive_finite32_classify (x : UInt32) (lo : 0 < x.toNat)
    (hi : x.toNat < 0x7f800000) :
    sign32 x = false ∧ isZero32 x = false ∧ isNaN32 x = false ∧
      isInf32 x = false ∧ x ≠ 0x7f800000 ∧ exponent32 x < 255 := by
  have hs := sign32_false_of_lt x (by omega)
  have he : exponent32 x < 255 := by rw [exponent32_eq_div]; omega
  have hm : x.toNat % 2 ^ 31 = x.toNat := Nat.mod_eq_of_lt (by omega)
  refine ⟨hs, ?_, ?_, ?_, ?_, he⟩
  · apply Bool.eq_false_iff.mpr
    intro h
    have hz := (isZero32_iff x).mp h
    omega
  · simp [isNaN32, Nat.ne_of_lt he]
  · apply Bool.eq_false_iff.mpr
    intro h
    have hz := (isInf32_iff x).mp h
    omega
  · intro h
    subst x
    contradiction

end VerifiedSqrt.Arm
