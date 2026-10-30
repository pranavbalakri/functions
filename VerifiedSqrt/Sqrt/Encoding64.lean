module

public import VerifiedSqrt.Arm.Scalar64Real
public import VerifiedSqrt.Sqrt.Certificate64

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

theorem normalized64_exponent (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) :
    exponent64 x = 1023 ∨ exponent64 x = 1024 := by
  rw [exponent64_eq_div]
  norm_num
  omega

theorem normalized64_value (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) :
    (unpack64 x).toReal = (normalizedRadicand64 x : ℝ) / (2 : ℝ) ^ 104 := by
  have hs := sign64_false_of_lt x (by omega)
  rcases normalized64_exponent x lo hi with he | he <;>
    rw [unpack64_positive_normal x hs (by omega)] <;>
    simp [normalizedRadicand64, he] <;> ring

theorem normalized64_result_value (y : UInt64)
    (lo : 0x3ff0000000000000 ≤ y.toNat) (hi : y.toNat ≤ 0x4000000000000000) :
    (unpack64 y).toReal = (normalizedSignificand64 y : ℝ) / (2 : ℝ) ^ 52 := by
  by_cases hy : y = 0x4000000000000000
  · subst y
    rw [unpack64_positive_normal _ (sign64_false_of_lt _ (by decide)) (by decide)]
    norm_num [normalizedSignificand64, exponent64_eq_div, fraction64_eq_mod]
  · have he : exponent64 y = 1023 := by
      rw [exponent64_eq_div]
      have hne : y.toNat ≠ 0x4000000000000000 := by
        intro h
        apply hy
        exact UInt64.toNat_inj.mp h
      norm_num
      omega
    rw [unpack64_positive_normal y (sign64_false_of_lt y (by omega)) (by omega)]
    simp [normalizedSignificand64, hy, he]
    ring

theorem normalized64_root (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) :
    Real.sqrt (unpack64 x).toReal =
      Real.sqrt (normalizedRadicand64 x) / (2 : ℝ) ^ 52 := by
  rw [normalized64_value x lo hi, Real.sqrt_div (by positivity)]
  rw [show (2 : ℝ) ^ 104 = ((2 : ℝ) ^ 52) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

theorem normalized64_root_bounds (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) :
    1 ≤ Real.sqrt (unpack64 x).toReal ∧ Real.sqrt (unpack64 x).toReal ≤ 2 := by
  have hf : (fraction64 x : ℝ) < 2 ^ 52 := by exact_mod_cast fraction64_lt x
  have hf0 : (0 : ℝ) ≤ fraction64 x := by positivity
  have hv : 1 ≤ (unpack64 x).toReal ∧ (unpack64 x).toReal ≤ 4 := by
    have hs := sign64_false_of_lt x (by omega)
    rcases normalized64_exponent x lo hi with he | he <;>
      rw [unpack64_positive_normal x hs (by omega)] <;>
      norm_num [he] <;> constructor <;> linarith
  constructor
  · simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hv.1
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; exact hv.2⟩

theorem certificate64_result_error (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000)
    (h : coreCertificate64 x = true) :
    |(unpack64 (core64 x)).toReal - Real.sqrt (unpack64 x).toReal| <
      1 / (2 : ℝ) ^ 53 := by
  have hb := h
  simp only [coreCertificate64, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hlo : 0x3ff0000000000000 ≤ (core64 x).toNat := hb.1.1.1
  have hhi : (core64 x).toNat ≤ 0x4000000000000000 := hb.1.1.2
  rw [normalized64_result_value _ hlo hhi, normalized64_root x lo hi, ← sub_div,
    abs_div]
  have he := certificate64_sound x h
  norm_num at *
  linarith

theorem certificate64_result_nearest_grid (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000)
    (h : coreCertificate64 x = true) (z : Int) :
    |(unpack64 (core64 x)).toReal - Real.sqrt (unpack64 x).toReal| ≤
      |(z : ℝ) / (2 : ℝ) ^ 52 - Real.sqrt (unpack64 x).toReal| := by
  have hb := h
  simp only [coreCertificate64, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hlo : 0x3ff0000000000000 ≤ (core64 x).toNat := hb.1.1.1
  have hhi : (core64 x).toNat ≤ 0x4000000000000000 := hb.1.1.2
  rw [normalized64_result_value _ hlo hhi, normalized64_root x lo hi,
    ← sub_div, ← sub_div, abs_div, abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  simpa only [Int.cast_natCast] using (certificate64_nearest x h).1 z

theorem certificate64_result_strict_grid (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000)
    (h : coreCertificate64 x = true) (z : Int)
    (hne : (unpack64 (core64 x)).toReal ≠ (z : ℝ) / (2 : ℝ) ^ 52) :
    |(unpack64 (core64 x)).toReal - Real.sqrt (unpack64 x).toReal| <
      |(z : ℝ) / (2 : ℝ) ^ 52 - Real.sqrt (unpack64 x).toReal| := by
  have hb := h
  simp only [coreCertificate64, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hlo : 0x3ff0000000000000 ≤ (core64 x).toNat := hb.1.1.1
  have hhi : (core64 x).toNat ≤ 0x4000000000000000 := hb.1.1.2
  have hn : (normalizedSignificand64 (core64 x) : Int) ≠ z := by
    intro he
    apply hne
    rw [normalized64_result_value _ hlo hhi, ← he, Int.cast_natCast]
  rw [normalized64_result_value _ hlo hhi, normalized64_root x lo hi,
    ← sub_div, ← sub_div, abs_div, abs_div]
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < |2 ^ 52|)).mpr
  apply nearestInteger_strict_of_lt (q := (normalizedSignificand64 (core64 x) : Int))
    (z := z) (by simpa only [Int.cast_natCast] using certificate64_sound x h) hn

theorem result64_grid_between (y : UInt64)
    (lo : 1 ≤ (unpack64 y).toReal) (hi : (unpack64 y).toReal ≤ 2) :
    ∃ z : Int, (unpack64 y).toReal = (z : ℝ) / (2 : ℝ) ^ 52 := by
  by_cases hl : (unpack64 y).toReal ≤ 1
  · exact ⟨4503599627370496, by norm_num; linarith⟩
  by_cases hh : 2 ≤ (unpack64 y).toReal
  · exact ⟨9007199254740992, by norm_num; linarith⟩
  have hsign : y.toNat < 2 ^ 63 := by
    by_contra hn
    have hv := unpack64_nonpos_of_sign y (sign64_true_of_ge y (by omega))
    linarith
  have hylo : 0x3ff0000000000000 ≤ y.toNat := by
    by_contra hn
    exact hl (unpack64_le_one y (by omega))
  have hyhi : y.toNat ≤ 0x4000000000000000 := by
    by_contra hn
    exact hh (unpack64_ge_two y (by omega) hsign)
  exact ⟨normalizedSignificand64 y, by
    simpa only [Int.cast_natCast] using normalized64_result_value y hylo hyhi⟩

theorem certificate64_result_nearest_float (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000)
    (h : coreCertificate64 x = true) (y : UInt64) :
    |(unpack64 (core64 x)).toReal - Real.sqrt (unpack64 x).toReal| ≤
      |(unpack64 y).toReal - Real.sqrt (unpack64 x).toReal| := by
  have hr := normalized64_root_bounds x lo hi
  by_cases hl : (unpack64 y).toReal ≤ 1
  · have hb := certificate64_result_nearest_grid x lo hi h 4503599627370496
    norm_num at hb
    apply hb.trans
    rw [abs_of_nonpos (by linarith : 1 - Real.sqrt (unpack64 x).toReal ≤ 0),
      abs_of_nonpos (by linarith : (unpack64 y).toReal - Real.sqrt (unpack64 x).toReal ≤ 0)]
    linarith
  by_cases hh : 2 ≤ (unpack64 y).toReal
  · have hb := certificate64_result_nearest_grid x lo hi h 9007199254740992
    norm_num at hb
    apply hb.trans
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 - Real.sqrt (unpack64 x).toReal),
      abs_of_nonneg (by linarith : 0 ≤ (unpack64 y).toReal - Real.sqrt (unpack64 x).toReal)]
    linarith
  have hsign : y.toNat < 2 ^ 63 := by
    by_contra hn
    have hv := unpack64_nonpos_of_sign y (sign64_true_of_ge y (by omega))
    linarith
  have hylo : 0x3ff0000000000000 ≤ y.toNat := by
    by_contra hn
    exact hl (unpack64_le_one y (by omega))
  have hyhi : y.toNat ≤ 0x4000000000000000 := by
    by_contra hn
    exact hh (unpack64_ge_two y (by omega) hsign)
  rw [normalized64_result_value y hylo hyhi]
  simpa only [Int.cast_natCast] using
    certificate64_result_nearest_grid x lo hi h (normalizedSignificand64 y)

theorem certificate64_result_unique_float (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000)
    (h : coreCertificate64 x = true) (y : UInt64)
    (hne : (unpack64 (core64 x)).toReal ≠ (unpack64 y).toReal) :
    |(unpack64 (core64 x)).toReal - Real.sqrt (unpack64 x).toReal| <
      |(unpack64 y).toReal - Real.sqrt (unpack64 x).toReal| := by
  have hr := normalized64_root_bounds x lo hi
  by_cases hl : (unpack64 y).toReal < 1
  · have hb := certificate64_result_nearest_grid x lo hi h 4503599627370496
    norm_num at hb
    apply hb.trans_lt
    rw [abs_of_nonpos (by linarith : 1 - Real.sqrt (unpack64 x).toReal ≤ 0),
      abs_of_nonpos (by linarith : (unpack64 y).toReal - Real.sqrt (unpack64 x).toReal ≤ 0)]
    linarith
  by_cases hh : 2 < (unpack64 y).toReal
  · have hb := certificate64_result_nearest_grid x lo hi h 9007199254740992
    norm_num at hb
    apply hb.trans_lt
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 - Real.sqrt (unpack64 x).toReal),
      abs_of_nonneg (by linarith : 0 ≤ (unpack64 y).toReal - Real.sqrt (unpack64 x).toReal)]
    linarith
  obtain ⟨z, hz⟩ := result64_grid_between y (by linarith) (by linarith)
  rw [hz] at hne ⊢
  exact certificate64_result_strict_grid x lo hi h z hne

end VerifiedSqrt.Sqrt
