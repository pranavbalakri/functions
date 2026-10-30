module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import VerifiedSqrt.Float.Dyadic

namespace VerifiedSqrt

public noncomputable def Dyadic.toReal (x : Dyadic) : ℝ :=
  (x.coefficient : ℝ) * (2 : ℝ) ^ x.exponent

public theorem midpoint_certificate (n q : ℝ) (hn : 0 ≤ n) (hq : 1 ≤ q)
    (lo : (2 * q - 1) ^ 2 < 4 * n) (hi : 4 * n < (2 * q + 1) ^ 2) :
    q - 1 / 2 < Real.sqrt n ∧ Real.sqrt n < q + 1 / 2 := by
  have hs := Real.sq_sqrt hn
  have hp := Real.sqrt_nonneg n
  constructor
  · by_contra h
    have hle : Real.sqrt n ≤ q - 1 / 2 := le_of_not_gt h
    nlinarith [sq_nonneg (q - 1 / 2 - Real.sqrt n)]
  · by_contra h
    have hle : q + 1 / 2 ≤ Real.sqrt n := le_of_not_gt h
    nlinarith [sq_nonneg (Real.sqrt n - (q + 1 / 2))]

public theorem correction_error_identity (x s h t : ℝ) (ht : t ^ 2 = x) :
    s + (x - s * s) * h - t = (s - t) * (1 - (s + t) * h) := by
  rw [← ht]
  ring

public theorem square_root_not_half_integer (n q : Nat) :
    Real.sqrt (n : ℝ) ≠ (q : ℝ) + 1 / 2 := by
  intro h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have he : (((2 * q + 1) ^ 2 : Nat) : ℝ) = (4 * n : ℝ) := by
    push_cast
    nlinarith
  have hi : (2 * q + 1) ^ 2 = 4 * n := by exact_mod_cast he
  have hid : (2 * q + 1) ^ 2 = 4 * (q * q + q) + 1 := by ring
  omega

#print axioms midpoint_certificate
#print axioms correction_error_identity
#print axioms square_root_not_half_integer

end VerifiedSqrt
