module

public import VerifiedSqrt.Arm.Spacing64
public import VerifiedSqrt.Float.Distance

@[expose] public section

namespace VerifiedSqrt.Arm

def RoundsToNearestEven64 (r : ℝ) (y : UInt64) : Prop :=
  exponent64 y < 2047 ∧
    ∀ z : UInt64, exponent64 z < 2047 →
      |(unpack64 y).toReal - r| ≤ |(unpack64 z).toReal - r| ∧
        ((unpack64 y).toReal ≠ (unpack64 z).toReal →
          |(unpack64 y).toReal - r| = |(unpack64 z).toReal - r| → fraction64 y % 2 = 0)

theorem roundsToNearestEven64_of_strict (r : ℝ) (y : UInt64)
    (hy : exponent64 y < 2047)
    (h : ∀ z : UInt64, (unpack64 y).toReal ≠ (unpack64 z).toReal →
      |(unpack64 y).toReal - r| < |(unpack64 z).toReal - r|) :
    RoundsToNearestEven64 r y := by
  refine ⟨hy, fun z _ => ?_⟩
  constructor
  · by_cases hz : (unpack64 y).toReal = (unpack64 z).toReal
    · rw [hz]
    · exact (h z hz).le
  · intro hz he
    exact False.elim ((ne_of_lt (h z hz)) he)

theorem encodeSignificand64_strict_nearest (e q : Nat) (r : ℝ)
    (elo : 2 ≤ e) (ehi : e ≤ 2045) (qlo : 2 ^ 52 ≤ q) (qhi : q ≤ 2 ^ 53)
    (rlo : (2 : ℝ) ^ 52 ≤ r) (rhi : r ≤ (2 : ℝ) ^ 53)
    (herr : |(q : ℝ) - r| < 1 / 2) (y : UInt64)
    (hne : (unpack64 (encodeSignificand64 e q)).toReal ≠ (unpack64 y).toReal) :
    |(unpack64 (encodeSignificand64 e q)).toReal - r * (2 : ℝ) ^ ((e : Int) - 1075)| <
      |(unpack64 y).toReal - r * (2 : ℝ) ^ ((e : Int) - 1075)| := by
  let c : ℝ := (2 : ℝ) ^ ((e : Int) - 1075)
  have hc : 0 < c := by dsimp [c]; positivity
  have hv := encodeSignificand64_value e q (by omega) ehi qlo qhi
  change (unpack64 (encodeSignificand64 e q)).toReal = (q : ℝ) * c at hv
  change |(unpack64 (encodeSignificand64 e q)).toReal - r * c| <
    |(unpack64 y).toReal - r * c|
  have hg (z : Int) : |(q : ℝ) * c - r * c| ≤ |(z : ℝ) * c - r * c| := by
    rw [scaled_distance _ _ _ hc.le, scaled_distance _ _ _ hc.le]
    apply mul_le_mul_of_nonneg_right _ hc.le
    exact nearestInteger_of_half r (q : Int) (by simpa using herr.le) z
  have hl : (2 : ℝ) ^ 52 * c ≤ r * c := mul_le_mul_of_nonneg_right rlo hc.le
  have hh : r * c ≤ (2 : ℝ) ^ 53 * c := mul_le_mul_of_nonneg_right rhi hc.le
  by_cases hylo : (unpack64 y).toReal < (2 : ℝ) ^ 52 * c
  · rw [hv]
    have hb := hg (2 ^ 52)
    simp only [Int.cast_pow, Int.cast_ofNat] at hb
    apply hb.trans_lt
    rw [abs_of_nonpos (by linarith : (2 : ℝ) ^ 52 * c - r * c ≤ 0),
      abs_of_nonpos (by linarith : (unpack64 y).toReal - r * c ≤ 0)]
    linarith
  by_cases hyhi : (2 : ℝ) ^ 53 * c < (unpack64 y).toReal
  · rw [hv]
    have hb := hg (2 ^ 53)
    simp only [Int.cast_pow, Int.cast_ofNat] at hb
    apply hb.trans_lt
    rw [abs_of_nonneg (by linarith : 0 ≤ (2 : ℝ) ^ 53 * c - r * c),
      abs_of_nonneg (by linarith : 0 ≤ (unpack64 y).toReal - r * c)]
    linarith
  have hl' : (2 : ℝ) ^ ((e : Int) - 1023) ≤ (unpack64 y).toReal := by
    rw [← binade64_lower e]
    exact le_of_not_gt hylo
  have hh' : (unpack64 y).toReal ≤ (2 : ℝ) ^ ((e : Int) - 1022) := by
    rw [← binade64_upper e]
    exact le_of_not_gt hyhi
  obtain ⟨z, hz⟩ := grid64_between y e elo ehi hl' hh'
  change (unpack64 y).toReal = (z : ℝ) * c at hz
  have hqz : (q : Int) ≠ z := by
    intro h
    apply hne
    rw [hv, hz, ← h, Int.cast_natCast]
  rw [hv, hz, scaled_distance _ _ _ hc.le, scaled_distance _ _ _ hc.le]
  apply mul_lt_mul_of_pos_right _ hc
  exact nearestInteger_strict_of_lt (by simpa using herr) hqz

end VerifiedSqrt.Arm
