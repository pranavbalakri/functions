module

public import VerifiedSqrt.Sqrt.Algorithm64
public import VerifiedSqrt.Float.Real
public import VerifiedSqrt.Float.Rounding

namespace VerifiedSqrt.Sqrt

@[expose] public def CoreCorrect64 : Prop :=
  ∀ i : Fin (2 ^ 53), coreCertificate64 (UInt64.ofNat (0x3ff0000000000000 + i.val)) = true

public theorem significand64_positive (y : UInt64) : 1 ≤ normalizedSignificand64 y := by
  simp only [normalizedSignificand64]
  split <;> omega

public theorem certificate64_sound (x : UInt64) (h : coreCertificate64 x = true) :
    |(normalizedSignificand64 (core64 x) : ℝ) - Real.sqrt (normalizedRadicand64 x)| < 1 / 2 := by
  let q := normalizedSignificand64 (core64 x)
  let n := normalizedRadicand64 x
  have hq : 1 ≤ q := significand64_positive _
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsub : 1 ≤ 2 * q := by omega
  simp only [coreCertificate64, Bool.and_eq_true, decide_eq_true_eq] at h
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

public theorem certificate64_nearest (x : UInt64) (h : coreCertificate64 x = true) :
    NearestEvenInteger (Real.sqrt (normalizedRadicand64 x))
      (normalizedSignificand64 (core64 x)) := by
  apply nearestEvenInteger_of_lt
  simpa only [Int.cast_natCast] using certificate64_sound x h

public theorem certificate64_unique (x : UInt64) (h : coreCertificate64 x = true)
    (q : Int) (hq : NearestEvenInteger (Real.sqrt (normalizedRadicand64 x)) q) :
    q = normalizedSignificand64 (core64 x) :=
  nearestEvenInteger_unique hq (certificate64_nearest x h)

#print axioms certificate64_sound

end VerifiedSqrt.Sqrt
