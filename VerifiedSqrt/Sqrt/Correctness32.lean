module

public import VerifiedSqrt.Arm.Classification32
public import VerifiedSqrt.Arm.Rounding32
public import VerifiedSqrt.Sqrt.Normalization32

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

end VerifiedSqrt.Sqrt
