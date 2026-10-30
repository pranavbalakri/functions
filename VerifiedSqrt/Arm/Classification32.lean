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

theorem isNaN32_iff (x : UInt32) :
    isNaN32 x = true ↔ 0x7f800000 < x.toNat % 2 ^ 31 := by
  simp only [isNaN32, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    exponent32_eq_div, fraction32_eq_mod]
  have hb := x.toNat_lt
  omega

theorem sign32_false_iff (x : UInt32) : sign32 x = false ↔ x.toNat < 2 ^ 31 := by
  constructor
  · intro h
    by_contra hn
    have ht := sign32_true_of_ge x (by omega)
    simp [h] at ht
  · exact sign32_false_of_lt x

theorem nan32_nonzero (x : UInt32) (hn : isNaN32 x = true) : isZero32 x = false := by
  apply Bool.eq_false_iff.mpr
  intro hz
  have hn := (isNaN32_iff x).mp hn
  have hz := (isZero32_iff x).mp hz
  omega

theorem positive_finite32_of_classification (x : UInt32)
    (hs : sign32 x = false) (hz : isZero32 x = false)
    (hn : isNaN32 x = false) (hi : isInf32 x = false) :
    0 < x.toNat ∧ x.toNat < 0x7f800000 := by
  have hb := (sign32_false_iff x).mp hs
  have hm : x.toNat % 2 ^ 31 = x.toNat := Nat.mod_eq_of_lt hb
  have hzero : x.toNat % 2 ^ 31 ≠ 0 := by
    intro h
    have h := (isZero32_iff x).mpr h
    simp [hz] at h
  have hnan : ¬0x7f800000 < x.toNat % 2 ^ 31 := by
    intro h
    have h := (isNaN32_iff x).mpr h
    simp [hn] at h
  have hinf : x.toNat % 2 ^ 31 ≠ 0x7f800000 := by
    intro h
    have h := (isInf32_iff x).mpr h
    simp [hi] at h
  omega

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
