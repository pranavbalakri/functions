module

public import VerifiedSqrt.Arm.Encoding64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem magnitude64_bits (x : UInt64) :
    (x &&& 0x7fffffffffffffff).toNat = x.toNat % 2 ^ 63 := by
  rw [UInt64.toNat_and]
  change x.toNat &&& (2 ^ 63 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem isZero64_iff (x : UInt64) : isZero64 x = true ↔ x.toNat % 2 ^ 63 = 0 := by
  simp only [isZero64, beq_iff_eq, ← UInt64.toNat_inj, magnitude64_bits]
  rfl

theorem isInf64_iff (x : UInt64) :
    isInf64 x = true ↔ x.toNat % 2 ^ 63 = 0x7ff0000000000000 := by
  simp only [isInf64, beq_iff_eq, ← UInt64.toNat_inj, magnitude64_bits]
  rfl

theorem isNaN64_iff (x : UInt64) :
    isNaN64 x = true ↔ 0x7ff0000000000000 < x.toNat % 2 ^ 63 := by
  simp only [isNaN64, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    exponent64_eq_div, fraction64_eq_mod]
  have hb := x.toNat_lt
  omega

theorem sign64_false_iff (x : UInt64) : sign64 x = false ↔ x.toNat < 2 ^ 63 := by
  constructor
  · intro h
    by_contra hn
    have ht := sign64_true_of_ge x (by omega)
    simp [h] at ht
  · exact sign64_false_of_lt x

theorem nan64_nonzero (x : UInt64) (hn : isNaN64 x = true) : isZero64 x = false := by
  apply Bool.eq_false_iff.mpr
  intro hz
  have hn := (isNaN64_iff x).mp hn
  have hz := (isZero64_iff x).mp hz
  omega

theorem positive_finite64_of_classification (x : UInt64)
    (hs : sign64 x = false) (hz : isZero64 x = false)
    (hn : isNaN64 x = false) (hi : isInf64 x = false) :
    0 < x.toNat ∧ x.toNat < 0x7ff0000000000000 := by
  have hb := (sign64_false_iff x).mp hs
  have hm : x.toNat % 2 ^ 63 = x.toNat := Nat.mod_eq_of_lt hb
  have hzero : x.toNat % 2 ^ 63 ≠ 0 := by
    intro h
    have h := (isZero64_iff x).mpr h
    simp [hz] at h
  have hnan : ¬0x7ff0000000000000 < x.toNat % 2 ^ 63 := by
    intro h
    have h := (isNaN64_iff x).mpr h
    simp [hn] at h
  have hinf : x.toNat % 2 ^ 63 ≠ 0x7ff0000000000000 := by
    intro h
    have h := (isInf64_iff x).mpr h
    simp [hi] at h
  omega

theorem positive_finite64_classify (x : UInt64) (lo : 0 < x.toNat)
    (hi : x.toNat < 0x7ff0000000000000) :
    sign64 x = false ∧ isZero64 x = false ∧ isNaN64 x = false ∧
      isInf64 x = false ∧ x ≠ 0x7ff0000000000000 ∧ exponent64 x < 2047 := by
  have hs := sign64_false_of_lt x (by omega)
  have he : exponent64 x < 2047 := by rw [exponent64_eq_div]; omega
  have hm : x.toNat % 2 ^ 63 = x.toNat := Nat.mod_eq_of_lt (by omega)
  refine ⟨hs, ?_, ?_, ?_, ?_, he⟩
  · apply Bool.eq_false_iff.mpr
    intro h
    have hz := (isZero64_iff x).mp h
    omega
  · simp [isNaN64, Nat.ne_of_lt he]
  · apply Bool.eq_false_iff.mpr
    intro h
    have hz := (isInf64_iff x).mp h
    omega
  · intro h
    subst x
    contradiction

end VerifiedSqrt.Arm
