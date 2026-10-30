module

public import VerifiedSqrt.Sqrt.Algorithm32
public import VerifiedSqrt.Float.Real

namespace VerifiedSqrt.Sqrt

public def CoreCorrect32 : Prop :=
  ∀ i : Fin (2 ^ 24), coreCertificate32 (UInt32.ofNat (0x3f800000 + i.val)) = true

public theorem significand32_positive (y : UInt32) : 1 ≤ normalizedSignificand32 y := by
  simp only [normalizedSignificand32]
  split <;> omega

public theorem certificate32_sound (x : UInt32) (h : coreCertificate32 x = true) :
    |(normalizedSignificand32 (core32 x) : ℝ) - Real.sqrt (normalizedRadicand32 x)| < 1 / 2 := by
  let q := normalizedSignificand32 (core32 x)
  let n := normalizedRadicand32 x
  have hq : 1 ≤ q := significand32_positive _
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsub : 1 ≤ 2 * q := by omega
  simp only [coreCertificate32, Bool.and_eq_true, decide_eq_true_eq] at h
  have hlo := h.1.2
  have hhi := h.2
  change (2 * q - 1) ^ 2 < 4 * n at hlo
  change 4 * n < (2 * q + 1) ^ 2 at hhi
  have hloR : ((2 * q - 1) ^ 2 : Nat) < (4 * n : ℝ) := by exact_mod_cast hlo
  have hhiR : (4 * n : ℝ) < (2 * q + 1) ^ 2 := by exact_mod_cast hhi
  push_cast [Nat.cast_sub hsub] at hloR
  have bounds := midpoint_certificate (n : ℝ) (q : ℝ) (by positivity) hqR hloR hhiR
  change |(q : ℝ) - Real.sqrt n| < 1 / 2
  exact abs_lt.mpr ⟨by linarith [bounds.2], by linarith [bounds.1]⟩

#print axioms certificate32_sound

end VerifiedSqrt.Sqrt
