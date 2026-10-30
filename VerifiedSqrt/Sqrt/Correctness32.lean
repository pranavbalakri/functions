module

public import VerifiedSqrt.Arm.Classification32
public import VerifiedSqrt.Arm.Rounding32
public import VerifiedSqrt.Sqrt.Normalization32
public import VerifiedSqrt.Sqrt.Subnormal32
public import VerifiedSqrt.Sqrt.Special32
public import VerifiedSqrt.Sqrt.Specification32

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

theorem scaledCore32_strict_nearest (x : UInt32) (k : Int)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000)
    (klo : -125 ≤ k) (khi : k ≤ 126) (y : UInt32)
    (hne : (unpack32 (rescale32 (core32 x) k)).toReal ≠ (unpack32 y).toReal) :
    |(unpack32 (rescale32 (core32 x) k)).toReal -
        Real.sqrt (unpack32 x).toReal * (2 : ℝ) ^ k| <
      |(unpack32 y).toReal - Real.sqrt (unpack32 x).toReal * (2 : ℝ) ^ k| := by
  have hb := correctedCore32_bounds x lo hi
  have hq := normalizedSignificand32_bounds (core32 x)
  have hr := normalized32_root_bounds x lo hi
  rw [normalized32_root x lo hi] at hr
  have hrlo : (2 : ℝ) ^ 23 ≤ Real.sqrt (normalizedRadicand32 x) := by
    norm_num at hr ⊢
    linarith [hr.1]
  have hrhi : Real.sqrt (normalizedRadicand32 x) ≤ (2 : ℝ) ^ 24 := by
    norm_num at hr ⊢
    linarith [hr.2]
  have he : ((k + 127).toNat : Int) - 150 = k - 23 := by omega
  have hp : Real.sqrt (unpack32 x).toReal * (2 : ℝ) ^ k =
      Real.sqrt (normalizedRadicand32 x) * (2 : ℝ) ^ (((k + 127).toNat : Int) - 150) := by
    rw [normalized32_root x lo hi, he, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num only [zpow_natCast]
    ring
  rw [hp, rescale32_encode _ k hb.1 hb.2 klo khi]
  apply encodeSignificand32_strict_nearest _ _ _ (by omega) (by omega) hq.1 hq.2 hrlo hrhi
    (certificate32_sound x (core32_certificate x lo hi)) y
  simpa only [rescale32_encode _ k hb.1 hb.2 klo khi] using hne

theorem algorithm32_normal (dn : Bool) (x : UInt32)
    (lo : 0 < x.toNat) (hi : x.toNat < 0x7f800000) (he : 0 < exponent32 x) :
    algorithm32 dn x = rescale32 (core32 (normalizedInput32 x)) (rootExponent32 x) := by
  obtain ⟨hs, hz, hn, _, hne, _⟩ := positive_finite32_classify x lo hi
  simp [algorithm32, hz, hne, hs, hn, Nat.ne_of_gt he,
    rescale32, normalizedInput32, rootExponent32]

theorem algorithm32_normal_strict_nearest (dn : Bool) (x : UInt32)
    (lo : 0 < x.toNat) (hi : x.toNat < 0x7f800000) (he : 0 < exponent32 x)
    (y : UInt32) (hne : (unpack32 (algorithm32 dn x)).toReal ≠ (unpack32 y).toReal) :
    |(unpack32 (algorithm32 dn x)).toReal - Real.sqrt (unpack32 x).toReal| <
      |(unpack32 y).toReal - Real.sqrt (unpack32 x).toReal| := by
  have hc := positive_finite32_classify x lo hi
  have hk := rootExponent32_bounds x he hc.2.2.2.2.2
  have hz := normalizedInput32_bounds x
  rw [algorithm32_normal dn x lo hi he] at hne ⊢
  rw [normalizedInput32_root x hc.1 he]
  exact scaledCore32_strict_nearest _ _ hz.1 hz.2 (by omega) (by omega) y hne

theorem algorithm32_subnormal (dn : Bool) (x : UInt32)
    (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 23) :
    algorithm32 dn x = rescale32 (core32 (normalizedInput32 (scaleSubnormal32 x)))
      (rootExponent32 (scaleSubnormal32 x) - 24) := by
  obtain ⟨hs, hz, hn, _, hne, _⟩ := positive_finite32_classify x lo (by omega)
  have he : exponent32 x = 0 := by rw [exponent32_eq_div]; omega
  simp [algorithm32, hz, hne, hs, hn, he,
    rescale32, normalizedInput32, rootExponent32, scaleSubnormal32]

theorem algorithm32_subnormal_strict_nearest (dn : Bool) (x : UInt32)
    (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 23)
    (y : UInt32) (hne : (unpack32 (algorithm32 dn x)).toReal ≠ (unpack32 y).toReal) :
    |(unpack32 (algorithm32 dn x)).toReal - Real.sqrt (unpack32 x).toReal| <
      |(unpack32 y).toReal - Real.sqrt (unpack32 x).toReal| := by
  have hp := scaleSubnormal32_properties x lo hi
  have hk : -75 ≤ rootExponent32 (scaleSubnormal32 x) - 24 ∧
      rootExponent32 (scaleSubnormal32 x) - 24 ≤ -64 := by
    dsimp [rootExponent32]
    omega
  have hz := normalizedInput32_bounds (scaleSubnormal32 x)
  rw [algorithm32_subnormal dn x lo hi] at hne ⊢
  rw [subnormal_normalized_root x lo hi]
  exact scaledCore32_strict_nearest _ _ hz.1 hz.2 (by omega) (by omega) y hne

theorem algorithm32_positive_strict_nearest (dn : Bool) (x : UInt32)
    (lo : 0 < x.toNat) (hi : x.toNat < 0x7f800000)
    (y : UInt32) (hne : (unpack32 (algorithm32 dn x)).toReal ≠ (unpack32 y).toReal) :
    |(unpack32 (algorithm32 dn x)).toReal - Real.sqrt (unpack32 x).toReal| <
      |(unpack32 y).toReal - Real.sqrt (unpack32 x).toReal| := by
  by_cases he : exponent32 x = 0
  · have hb : x.toNat < 2 ^ 23 := by rw [exponent32_eq_div] at he; omega
    exact algorithm32_subnormal_strict_nearest dn x lo hb y hne
  · exact algorithm32_normal_strict_nearest dn x lo hi (by omega) y hne

theorem algorithm32_positive_bounds (dn : Bool) (x : UInt32)
    (lo : 0 < x.toNat) (hi : x.toNat < 0x7f800000) :
    0 < (algorithm32 dn x).toNat ∧ (algorithm32 dn x).toNat < 0x7f800000 := by
  by_cases he : exponent32 x = 0
  · have hb : x.toNat < 2 ^ 23 := by rw [exponent32_eq_div] at he; omega
    have hp := scaleSubnormal32_properties x lo hb
    have hk : -75 ≤ rootExponent32 (scaleSubnormal32 x) - 24 ∧
        rootExponent32 (scaleSubnormal32 x) - 24 ≤ -64 := by
      dsimp [rootExponent32]
      omega
    have hz := normalizedInput32_bounds (scaleSubnormal32 x)
    have hq := correctedCore32_bounds _ hz.1 hz.2
    rw [algorithm32_subnormal dn x lo hb]
    exact rescale32_bounds _ _ hq.1 hq.2 (by omega) (by omega)
  · have hc := positive_finite32_classify x lo hi
    have hk := rootExponent32_bounds x (by omega) hc.2.2.2.2.2
    have hz := normalizedInput32_bounds x
    have hq := correctedCore32_bounds _ hz.1 hz.2
    rw [algorithm32_normal dn x lo hi (by omega)]
    exact rescale32_bounds _ _ hq.1 hq.2 (by omega) (by omega)

theorem algorithm32_positive_rounds (dn : Bool) (x : UInt32)
    (lo : 0 < x.toNat) (hi : x.toNat < 0x7f800000) :
    RoundsToNearestEven32 (Real.sqrt (unpack32 x).toReal) (algorithm32 dn x) := by
  have hb := algorithm32_positive_bounds dn x lo hi
  have hc := positive_finite32_classify _ hb.1 hb.2
  exact roundsToNearestEven32_of_strict _ _ hc.2.2.2.2.2
    (algorithm32_positive_strict_nearest dn x lo hi)

theorem algorithm32_correct (dn : Bool) (x : UInt32) :
    SqrtSpec32 dn x (algorithm32 dn x) := by
  by_cases hn : isNaN32 x = true
  · simpa only [SqrtSpec32, hn, ite_true] using algorithm32_nan dn x hn
  have hn : isNaN32 x = false := Bool.eq_false_iff.mpr hn
  by_cases hz : isZero32 x = true
  · simpa only [SqrtSpec32, hn, Bool.false_eq_true, ite_false, hz, ite_true]
      using algorithm32_zero dn x hz
  have hz : isZero32 x = false := Bool.eq_false_iff.mpr hz
  by_cases hs : sign32 x = true
  · simpa only [SqrtSpec32, hn, hz, Bool.false_eq_true, ite_false, hs, ite_true]
      using algorithm32_negative dn x hs hz hn
  have hs : sign32 x = false := Bool.eq_false_iff.mpr hs
  by_cases hi : isInf32 x = true
  · have hb := (sign32_false_iff x).mp hs
    have hm := (isInf32_iff x).mp hi
    rw [Nat.mod_eq_of_lt hb] at hm
    have hx : x = 0x7f800000 := UInt32.toNat_inj.mp hm
    simp only [SqrtSpec32, hn, hz, hs, Bool.false_eq_true, ite_false, hi, ite_true]
    subst x
    exact algorithm32_infinity dn
  have hi : isInf32 x = false := Bool.eq_false_iff.mpr hi
  have hb := positive_finite32_of_classification x hs hz hn hi
  have hy := algorithm32_positive_bounds dn x hb.1 hb.2
  have hc := positive_finite32_classify _ hy.1 hy.2
  simp only [SqrtSpec32, hn, hz, hs, hi, Bool.false_eq_true, ite_false]
  refine ⟨hc.1, ?_, algorithm32_positive_rounds dn x hb.1 hb.2⟩
  simp only [unpack32, Dyadic.toReal, hc.1, Bool.false_eq_true, ite_false, Int.cast_natCast]
  apply mul_pos _ (by positivity)
  by_cases he : exponent32 (algorithm32 dn x) = 0
  · have hf : 0 < fraction32 (algorithm32 dn x) := by
      rw [exponent32_eq_div] at he
      rw [fraction32_eq_mod]
      omega
    simp only [he, beq_self_eq_true, ite_true, Nat.add_zero]
    exact_mod_cast hf
  · simp only [beq_iff_eq, he, ite_false]
    positivity

end VerifiedSqrt.Sqrt
