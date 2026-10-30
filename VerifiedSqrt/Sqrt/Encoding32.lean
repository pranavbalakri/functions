module

public import VerifiedSqrt.Arm.Scalar32Real
public import VerifiedSqrt.Sqrt.Certificate32

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

theorem normalized32_exponent (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) :
    exponent32 x = 127 ∨ exponent32 x = 128 := by
  rw [exponent32_eq_div]
  norm_num
  omega

theorem normalized32_value (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) :
    (unpack32 x).toReal = (normalizedRadicand32 x : ℝ) / (2 : ℝ) ^ 46 := by
  have hs := sign32_false_of_lt x (by omega)
  rcases normalized32_exponent x lo hi with he | he <;>
    rw [unpack32_positive_normal x hs (by omega)] <;>
    simp [normalizedRadicand32, he] <;> ring

theorem normalized32_result_value (y : UInt32)
    (lo : 0x3f800000 ≤ y.toNat) (hi : y.toNat ≤ 0x40000000) :
    (unpack32 y).toReal = (normalizedSignificand32 y : ℝ) / (2 : ℝ) ^ 23 := by
  by_cases hy : y = 0x40000000
  · subst y
    rw [unpack32_positive_normal _ (sign32_false_of_lt _ (by decide)) (by decide)]
    norm_num [normalizedSignificand32, exponent32_eq_div, fraction32_eq_mod]
  · have he : exponent32 y = 127 := by
      rw [exponent32_eq_div]
      have hne : y.toNat ≠ 0x40000000 := by
        intro h
        apply hy
        exact UInt32.toNat_inj.mp h
      norm_num
      omega
    rw [unpack32_positive_normal y (sign32_false_of_lt y (by omega)) (by omega)]
    simp [normalizedSignificand32, hy, he]
    ring

theorem normalized32_root (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) :
    Real.sqrt (unpack32 x).toReal =
      Real.sqrt (normalizedRadicand32 x) / (2 : ℝ) ^ 23 := by
  rw [normalized32_value x lo hi, Real.sqrt_div (by positivity)]
  rw [show (2 : ℝ) ^ 46 = ((2 : ℝ) ^ 23) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

theorem normalized32_root_bounds (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) :
    1 ≤ Real.sqrt (unpack32 x).toReal ∧ Real.sqrt (unpack32 x).toReal ≤ 2 := by
  have hf : (fraction32 x : ℝ) < 2 ^ 23 := by exact_mod_cast fraction32_lt x
  have hf0 : (0 : ℝ) ≤ fraction32 x := by positivity
  have hv : 1 ≤ (unpack32 x).toReal ∧ (unpack32 x).toReal ≤ 4 := by
    have hs := sign32_false_of_lt x (by omega)
    rcases normalized32_exponent x lo hi with he | he <;>
      rw [unpack32_positive_normal x hs (by omega)] <;>
      norm_num [he] <;> constructor <;> linarith
  constructor
  · simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hv.1
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; exact hv.2⟩

theorem certificate32_result_error (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000)
    (h : coreCertificate32 x = true) :
    |(unpack32 (core32 x)).toReal - Real.sqrt (unpack32 x).toReal| <
      1 / (2 : ℝ) ^ 24 := by
  have hb := h
  simp only [coreCertificate32, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hlo : 0x3f800000 ≤ (core32 x).toNat := hb.1.1.1
  have hhi : (core32 x).toNat ≤ 0x40000000 := hb.1.1.2
  rw [normalized32_result_value _ hlo hhi, normalized32_root x lo hi, ← sub_div,
    abs_div]
  have he := certificate32_sound x h
  norm_num at *
  linarith

theorem certificate32_result_nearest_grid (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000)
    (h : coreCertificate32 x = true) (z : Int) :
    |(unpack32 (core32 x)).toReal - Real.sqrt (unpack32 x).toReal| ≤
      |(z : ℝ) / (2 : ℝ) ^ 23 - Real.sqrt (unpack32 x).toReal| := by
  have hb := h
  simp only [coreCertificate32, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hlo : 0x3f800000 ≤ (core32 x).toNat := hb.1.1.1
  have hhi : (core32 x).toNat ≤ 0x40000000 := hb.1.1.2
  rw [normalized32_result_value _ hlo hhi, normalized32_root x lo hi,
    ← sub_div, ← sub_div, abs_div, abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  simpa only [Int.cast_natCast] using (certificate32_nearest x h).1 z

theorem certificate32_result_strict_grid (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000)
    (h : coreCertificate32 x = true) (z : Int)
    (hne : (unpack32 (core32 x)).toReal ≠ (z : ℝ) / (2 : ℝ) ^ 23) :
    |(unpack32 (core32 x)).toReal - Real.sqrt (unpack32 x).toReal| <
      |(z : ℝ) / (2 : ℝ) ^ 23 - Real.sqrt (unpack32 x).toReal| := by
  have hb := h
  simp only [coreCertificate32, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hlo : 0x3f800000 ≤ (core32 x).toNat := hb.1.1.1
  have hhi : (core32 x).toNat ≤ 0x40000000 := hb.1.1.2
  have hn : (normalizedSignificand32 (core32 x) : Int) ≠ z := by
    intro he
    apply hne
    rw [normalized32_result_value _ hlo hhi, ← he, Int.cast_natCast]
  rw [normalized32_result_value _ hlo hhi, normalized32_root x lo hi,
    ← sub_div, ← sub_div, abs_div, abs_div]
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < |2 ^ 23|)).mpr
  apply nearestInteger_strict_of_lt (q := (normalizedSignificand32 (core32 x) : Int))
    (z := z) (by simpa only [Int.cast_natCast] using certificate32_sound x h) hn

theorem result32_grid_between (y : UInt32)
    (lo : 1 ≤ (unpack32 y).toReal) (hi : (unpack32 y).toReal ≤ 2) :
    ∃ z : Int, (unpack32 y).toReal = (z : ℝ) / (2 : ℝ) ^ 23 := by
  by_cases hl : (unpack32 y).toReal ≤ 1
  · exact ⟨8388608, by norm_num; linarith⟩
  by_cases hh : 2 ≤ (unpack32 y).toReal
  · exact ⟨16777216, by norm_num; linarith⟩
  have hsign : y.toNat < 2 ^ 31 := by
    by_contra hn
    have hv := unpack32_nonpos_of_sign y (sign32_true_of_ge y (by omega))
    linarith
  have hylo : 0x3f800000 ≤ y.toNat := by
    by_contra hn
    exact hl (unpack32_le_one y (by omega))
  have hyhi : y.toNat ≤ 0x40000000 := by
    by_contra hn
    exact hh (unpack32_ge_two y (by omega) hsign)
  exact ⟨normalizedSignificand32 y, by
    simpa only [Int.cast_natCast] using normalized32_result_value y hylo hyhi⟩

theorem certificate32_result_nearest_float (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000)
    (h : coreCertificate32 x = true) (y : UInt32) :
    |(unpack32 (core32 x)).toReal - Real.sqrt (unpack32 x).toReal| ≤
      |(unpack32 y).toReal - Real.sqrt (unpack32 x).toReal| := by
  have hr := normalized32_root_bounds x lo hi
  by_cases hl : (unpack32 y).toReal ≤ 1
  · have hb := certificate32_result_nearest_grid x lo hi h 8388608
    norm_num at hb
    apply hb.trans
    rw [abs_of_nonpos (by linarith : 1 - Real.sqrt (unpack32 x).toReal ≤ 0),
      abs_of_nonpos (by linarith : (unpack32 y).toReal - Real.sqrt (unpack32 x).toReal ≤ 0)]
    linarith
  by_cases hh : 2 ≤ (unpack32 y).toReal
  · have hb := certificate32_result_nearest_grid x lo hi h 16777216
    norm_num at hb
    apply hb.trans
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 - Real.sqrt (unpack32 x).toReal),
      abs_of_nonneg (by linarith : 0 ≤ (unpack32 y).toReal - Real.sqrt (unpack32 x).toReal)]
    linarith
  have hsign : y.toNat < 2 ^ 31 := by
    by_contra hn
    have hv := unpack32_nonpos_of_sign y (sign32_true_of_ge y (by omega))
    linarith
  have hylo : 0x3f800000 ≤ y.toNat := by
    by_contra hn
    exact hl (unpack32_le_one y (by omega))
  have hyhi : y.toNat ≤ 0x40000000 := by
    by_contra hn
    exact hh (unpack32_ge_two y (by omega) hsign)
  rw [normalized32_result_value y hylo hyhi]
  simpa only [Int.cast_natCast] using
    certificate32_result_nearest_grid x lo hi h (normalizedSignificand32 y)

theorem certificate32_result_unique_float (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000)
    (h : coreCertificate32 x = true) (y : UInt32)
    (hne : (unpack32 (core32 x)).toReal ≠ (unpack32 y).toReal) :
    |(unpack32 (core32 x)).toReal - Real.sqrt (unpack32 x).toReal| <
      |(unpack32 y).toReal - Real.sqrt (unpack32 x).toReal| := by
  have hr := normalized32_root_bounds x lo hi
  by_cases hl : (unpack32 y).toReal < 1
  · have hb := certificate32_result_nearest_grid x lo hi h 8388608
    norm_num at hb
    apply hb.trans_lt
    rw [abs_of_nonpos (by linarith : 1 - Real.sqrt (unpack32 x).toReal ≤ 0),
      abs_of_nonpos (by linarith : (unpack32 y).toReal - Real.sqrt (unpack32 x).toReal ≤ 0)]
    linarith
  by_cases hh : 2 < (unpack32 y).toReal
  · have hb := certificate32_result_nearest_grid x lo hi h 16777216
    norm_num at hb
    apply hb.trans_lt
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 - Real.sqrt (unpack32 x).toReal),
      abs_of_nonneg (by linarith : 0 ≤ (unpack32 y).toReal - Real.sqrt (unpack32 x).toReal)]
    linarith
  obtain ⟨z, hz⟩ := result32_grid_between y (by linarith) (by linarith)
  rw [hz] at hne ⊢
  exact certificate32_result_strict_grid x lo hi h z hne

end VerifiedSqrt.Sqrt
