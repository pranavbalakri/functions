module

public import VerifiedSqrt.Arm.Classification64
public import VerifiedSqrt.Arm.Rounding64
public import VerifiedSqrt.Sqrt.Normalization64
public import VerifiedSqrt.Sqrt.Subnormal64
public import VerifiedSqrt.Sqrt.Special64
public import VerifiedSqrt.Sqrt.Specification64

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

theorem scaledCore64_strict_nearest (x : UInt64) (k : Int)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000)
    (klo : -1021 ≤ k) (khi : k ≤ 1022) (y : UInt64)
    (hne : (unpack64 (rescale64 (core64 x) k)).toReal ≠ (unpack64 y).toReal) :
    |(unpack64 (rescale64 (core64 x) k)).toReal -
        Real.sqrt (unpack64 x).toReal * (2 : ℝ) ^ k| <
      |(unpack64 y).toReal - Real.sqrt (unpack64 x).toReal * (2 : ℝ) ^ k| := by
  have hb := correctedCore64_bounds x lo hi
  have hq := normalizedSignificand64_bounds (core64 x)
  have hr := normalized64_root_bounds x lo hi
  rw [normalized64_root x lo hi] at hr
  have hrlo : (2 : ℝ) ^ 52 ≤ Real.sqrt (normalizedRadicand64 x) := by
    norm_num at hr ⊢
    linarith [hr.1]
  have hrhi : Real.sqrt (normalizedRadicand64 x) ≤ (2 : ℝ) ^ 53 := by
    norm_num at hr ⊢
    linarith [hr.2]
  have he : ((k + 1023).toNat : Int) - 1075 = k - 52 := by omega
  have hp : Real.sqrt (unpack64 x).toReal * (2 : ℝ) ^ k =
      Real.sqrt (normalizedRadicand64 x) * (2 : ℝ) ^ (((k + 1023).toNat : Int) - 1075) := by
    rw [normalized64_root x lo hi, he, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num only [zpow_natCast]
    ring
  rw [hp, rescale64_encode _ k hb.1 hb.2 klo khi]
  apply encodeSignificand64_strict_nearest _ _ _ (by omega) (by omega) hq.1 hq.2 hrlo hrhi
    (certificate64_sound x (core64_certificate x lo hi)) y
  simpa only [rescale64_encode _ k hb.1 hb.2 klo khi] using hne

theorem algorithm64_normal (dn : Bool) (x : UInt64)
    (lo : 0 < x.toNat) (hi : x.toNat < 0x7ff0000000000000) (he : 0 < exponent64 x) :
    algorithm64 dn x = rescale64 (core64 (normalizedInput64 x)) (rootExponent64 x) := by
  obtain ⟨hs, hz, hn, _, hne, _⟩ := positive_finite64_classify x lo hi
  simp [algorithm64, hz, hne, hs, hn, Nat.ne_of_gt he,
    rescale64, normalizedInput64, rootExponent64]

theorem algorithm64_normal_strict_nearest (dn : Bool) (x : UInt64)
    (lo : 0 < x.toNat) (hi : x.toNat < 0x7ff0000000000000) (he : 0 < exponent64 x)
    (y : UInt64) (hne : (unpack64 (algorithm64 dn x)).toReal ≠ (unpack64 y).toReal) :
    |(unpack64 (algorithm64 dn x)).toReal - Real.sqrt (unpack64 x).toReal| <
      |(unpack64 y).toReal - Real.sqrt (unpack64 x).toReal| := by
  have hc := positive_finite64_classify x lo hi
  have hk := rootExponent64_bounds x he hc.2.2.2.2.2
  have hz := normalizedInput64_bounds x
  rw [algorithm64_normal dn x lo hi he] at hne ⊢
  rw [normalizedInput64_root x hc.1 he]
  exact scaledCore64_strict_nearest _ _ hz.1 hz.2 (by omega) (by omega) y hne

theorem algorithm64_subnormal (dn : Bool) (x : UInt64)
    (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 52) :
    algorithm64 dn x = rescale64 (core64 (normalizedInput64 (scaleSubnormal64 x)))
      (rootExponent64 (scaleSubnormal64 x) - 53) := by
  obtain ⟨hs, hz, hn, _, hne, _⟩ := positive_finite64_classify x lo (by omega)
  have he : exponent64 x = 0 := by rw [exponent64_eq_div]; omega
  simp [algorithm64, hz, hne, hs, hn, he,
    rescale64, normalizedInput64, rootExponent64, scaleSubnormal64]

theorem algorithm64_subnormal_strict_nearest (dn : Bool) (x : UInt64)
    (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 52)
    (y : UInt64) (hne : (unpack64 (algorithm64 dn x)).toReal ≠ (unpack64 y).toReal) :
    |(unpack64 (algorithm64 dn x)).toReal - Real.sqrt (unpack64 x).toReal| <
      |(unpack64 y).toReal - Real.sqrt (unpack64 x).toReal| := by
  have hp := scaleSubnormal64_properties x lo hi
  have hk : -537 ≤ rootExponent64 (scaleSubnormal64 x) - 53 ∧
      rootExponent64 (scaleSubnormal64 x) - 53 ≤ -512 := by
    dsimp [rootExponent64]
    omega
  have hz := normalizedInput64_bounds (scaleSubnormal64 x)
  rw [algorithm64_subnormal dn x lo hi] at hne ⊢
  rw [subnormal_normalized_root64 x lo hi]
  exact scaledCore64_strict_nearest _ _ hz.1 hz.2 (by omega) (by omega) y hne

theorem algorithm64_positive_strict_nearest (dn : Bool) (x : UInt64)
    (lo : 0 < x.toNat) (hi : x.toNat < 0x7ff0000000000000)
    (y : UInt64) (hne : (unpack64 (algorithm64 dn x)).toReal ≠ (unpack64 y).toReal) :
    |(unpack64 (algorithm64 dn x)).toReal - Real.sqrt (unpack64 x).toReal| <
      |(unpack64 y).toReal - Real.sqrt (unpack64 x).toReal| := by
  by_cases he : exponent64 x = 0
  · have hb : x.toNat < 2 ^ 52 := by rw [exponent64_eq_div] at he; omega
    exact algorithm64_subnormal_strict_nearest dn x lo hb y hne
  · exact algorithm64_normal_strict_nearest dn x lo hi (by omega) y hne

theorem algorithm64_positive_bounds (dn : Bool) (x : UInt64)
    (lo : 0 < x.toNat) (hi : x.toNat < 0x7ff0000000000000) :
    0 < (algorithm64 dn x).toNat ∧ (algorithm64 dn x).toNat < 0x7ff0000000000000 := by
  by_cases he : exponent64 x = 0
  · have hb : x.toNat < 2 ^ 52 := by rw [exponent64_eq_div] at he; omega
    have hp := scaleSubnormal64_properties x lo hb
    have hk : -537 ≤ rootExponent64 (scaleSubnormal64 x) - 53 ∧
        rootExponent64 (scaleSubnormal64 x) - 53 ≤ -512 := by
      dsimp [rootExponent64]
      omega
    have hz := normalizedInput64_bounds (scaleSubnormal64 x)
    have hq := correctedCore64_bounds _ hz.1 hz.2
    rw [algorithm64_subnormal dn x lo hb]
    exact rescale64_bounds _ _ hq.1 hq.2 (by omega) (by omega)
  · have hc := positive_finite64_classify x lo hi
    have hk := rootExponent64_bounds x (by omega) hc.2.2.2.2.2
    have hz := normalizedInput64_bounds x
    have hq := correctedCore64_bounds _ hz.1 hz.2
    rw [algorithm64_normal dn x lo hi (by omega)]
    exact rescale64_bounds _ _ hq.1 hq.2 (by omega) (by omega)

theorem algorithm64_positive_rounds (dn : Bool) (x : UInt64)
    (lo : 0 < x.toNat) (hi : x.toNat < 0x7ff0000000000000) :
    RoundsToNearestEven64 (Real.sqrt (unpack64 x).toReal) (algorithm64 dn x) := by
  have hb := algorithm64_positive_bounds dn x lo hi
  have hc := positive_finite64_classify _ hb.1 hb.2
  exact roundsToNearestEven64_of_strict _ _ hc.2.2.2.2.2
    (algorithm64_positive_strict_nearest dn x lo hi)

theorem algorithm64_correct (dn : Bool) (x : UInt64) :
    SqrtSpec64 dn x (algorithm64 dn x) := by
  by_cases hn : isNaN64 x = true
  · simpa only [SqrtSpec64, hn, ite_true] using algorithm64_nan dn x hn
  have hn : isNaN64 x = false := Bool.eq_false_iff.mpr hn
  by_cases hz : isZero64 x = true
  · simpa only [SqrtSpec64, hn, Bool.false_eq_true, ite_false, hz, ite_true]
      using algorithm64_zero dn x hz
  have hz : isZero64 x = false := Bool.eq_false_iff.mpr hz
  by_cases hs : sign64 x = true
  · simpa only [SqrtSpec64, hn, hz, Bool.false_eq_true, ite_false, hs, ite_true]
      using algorithm64_negative dn x hs hz hn
  have hs : sign64 x = false := Bool.eq_false_iff.mpr hs
  by_cases hi : isInf64 x = true
  · have hb := (sign64_false_iff x).mp hs
    have hm := (isInf64_iff x).mp hi
    rw [Nat.mod_eq_of_lt hb] at hm
    have hx : x = 0x7ff0000000000000 := UInt64.toNat_inj.mp hm
    simp only [SqrtSpec64, hn, hz, hs, Bool.false_eq_true, ite_false, hi, ite_true]
    subst x
    exact algorithm64_infinity dn
  have hi : isInf64 x = false := Bool.eq_false_iff.mpr hi
  have hb := positive_finite64_of_classification x hs hz hn hi
  have hy := algorithm64_positive_bounds dn x hb.1 hb.2
  have hc := positive_finite64_classify _ hy.1 hy.2
  simp only [SqrtSpec64, hn, hz, hs, hi, Bool.false_eq_true, ite_false]
  refine ⟨hc.1, ?_, algorithm64_positive_rounds dn x hb.1 hb.2⟩
  simp only [unpack64, Dyadic.toReal, hc.1, Bool.false_eq_true, ite_false, Int.cast_natCast]
  apply mul_pos _ (by positivity)
  by_cases he : exponent64 (algorithm64 dn x) = 0
  · have hf : 0 < fraction64 (algorithm64 dn x) := by
      rw [exponent64_eq_div] at he
      rw [fraction64_eq_mod]
      omega
    simp only [he, beq_self_eq_true, ite_true, Nat.add_zero]
    exact_mod_cast hf
  · simp only [beq_iff_eq, he, ite_false]
    positivity

end VerifiedSqrt.Sqrt
