module

public import VerifiedSqrt.Arm.Spacing32
public import VerifiedSqrt.Float.Distance

@[expose] public section

namespace VerifiedSqrt.Arm

def RoundsToNearestEven32 (r : ℝ) (y : UInt32) : Prop :=
  exponent32 y < 255 ∧
    ∀ z : UInt32, exponent32 z < 255 →
      |(unpack32 y).toReal - r| ≤ |(unpack32 z).toReal - r| ∧
        ((unpack32 y).toReal ≠ (unpack32 z).toReal →
          |(unpack32 y).toReal - r| = |(unpack32 z).toReal - r| → fraction32 y % 2 = 0)

theorem roundsToNearestEven32_of_strict (r : ℝ) (y : UInt32)
    (hy : exponent32 y < 255)
    (h : ∀ z : UInt32, (unpack32 y).toReal ≠ (unpack32 z).toReal →
      |(unpack32 y).toReal - r| < |(unpack32 z).toReal - r|) :
    RoundsToNearestEven32 r y := by
  refine ⟨hy, fun z _ => ?_⟩
  constructor
  · by_cases hz : (unpack32 y).toReal = (unpack32 z).toReal
    · rw [hz]
    · exact (h z hz).le
  · intro hz he
    exact False.elim ((ne_of_lt (h z hz)) he)

theorem encodeSignificand32_strict_nearest (e q : Nat) (r : ℝ)
    (elo : 2 ≤ e) (ehi : e ≤ 253) (qlo : 2 ^ 23 ≤ q) (qhi : q ≤ 2 ^ 24)
    (rlo : (2 : ℝ) ^ 23 ≤ r) (rhi : r ≤ (2 : ℝ) ^ 24)
    (herr : |(q : ℝ) - r| < 1 / 2) (y : UInt32)
    (hne : (unpack32 (encodeSignificand32 e q)).toReal ≠ (unpack32 y).toReal) :
    |(unpack32 (encodeSignificand32 e q)).toReal - r * (2 : ℝ) ^ ((e : Int) - 150)| <
      |(unpack32 y).toReal - r * (2 : ℝ) ^ ((e : Int) - 150)| := by
  let c : ℝ := (2 : ℝ) ^ ((e : Int) - 150)
  have hc : 0 < c := by dsimp [c]; positivity
  have hv := encodeSignificand32_value e q (by omega) ehi qlo qhi
  change (unpack32 (encodeSignificand32 e q)).toReal = (q : ℝ) * c at hv
  change |(unpack32 (encodeSignificand32 e q)).toReal - r * c| <
    |(unpack32 y).toReal - r * c|
  have hg (z : Int) : |(q : ℝ) * c - r * c| ≤ |(z : ℝ) * c - r * c| := by
    rw [scaled_distance _ _ _ hc.le, scaled_distance _ _ _ hc.le]
    apply mul_le_mul_of_nonneg_right _ hc.le
    exact nearestInteger_of_half r (q : Int) (by simpa using herr.le) z
  have hl : (2 : ℝ) ^ 23 * c ≤ r * c := mul_le_mul_of_nonneg_right rlo hc.le
  have hh : r * c ≤ (2 : ℝ) ^ 24 * c := mul_le_mul_of_nonneg_right rhi hc.le
  by_cases hylo : (unpack32 y).toReal < (2 : ℝ) ^ 23 * c
  · rw [hv]
    have hb := hg (2 ^ 23)
    simp only [Int.cast_pow, Int.cast_ofNat] at hb
    apply hb.trans_lt
    rw [abs_of_nonpos (by linarith : (2 : ℝ) ^ 23 * c - r * c ≤ 0),
      abs_of_nonpos (by linarith : (unpack32 y).toReal - r * c ≤ 0)]
    linarith
  by_cases hyhi : (2 : ℝ) ^ 24 * c < (unpack32 y).toReal
  · rw [hv]
    have hb := hg (2 ^ 24)
    simp only [Int.cast_pow, Int.cast_ofNat] at hb
    apply hb.trans_lt
    rw [abs_of_nonneg (by linarith : 0 ≤ (2 : ℝ) ^ 24 * c - r * c),
      abs_of_nonneg (by linarith : 0 ≤ (unpack32 y).toReal - r * c)]
    linarith
  have hl' : (2 : ℝ) ^ ((e : Int) - 127) ≤ (unpack32 y).toReal := by
    rw [← binade32_lower e]
    exact le_of_not_gt hylo
  have hh' : (unpack32 y).toReal ≤ (2 : ℝ) ^ ((e : Int) - 126) := by
    rw [← binade32_upper e]
    exact le_of_not_gt hyhi
  obtain ⟨z, hz⟩ := grid32_between y e elo ehi hl' hh'
  change (unpack32 y).toReal = (z : ℝ) * c at hz
  have hqz : (q : Int) ≠ z := by
    intro h
    apply hne
    rw [hv, hz, ← h, Int.cast_natCast]
  rw [hv, hz, scaled_distance _ _ _ hc.le, scaled_distance _ _ _ hc.le]
  apply mul_lt_mul_of_pos_right _ hc
  exact nearestInteger_strict_of_lt (by simpa using herr) hqz

end VerifiedSqrt.Arm
