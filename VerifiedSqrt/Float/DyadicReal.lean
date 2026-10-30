module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Tactic.Ring
public import VerifiedSqrt.Float.Dyadic

@[expose] public section

namespace VerifiedSqrt

noncomputable def Dyadic.toReal (x : Dyadic) : ℝ :=
  (x.coefficient : ℝ) * (2 : ℝ) ^ x.exponent

theorem dyadic_align (e b : ℤ) (h : b ≤ e) :
    ((2 ^ (e - b).toNat : ℕ) : ℝ) * (2 : ℝ) ^ b = (2 : ℝ) ^ e := by
  push_cast
  rw [← zpow_natCast, Int.toNat_of_nonneg (by omega),
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

theorem Dyadic.toReal_add (a b : Dyadic) :
    (a.add b).toReal = a.toReal + b.toReal := by
  simp only [Dyadic.toReal, Dyadic.add, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [add_mul, mul_assoc, mul_assoc,
    dyadic_align _ _ (min_le_left _ _), dyadic_align _ _ (min_le_right _ _)]

theorem Dyadic.toReal_mul (a b : Dyadic) :
    (a.mul b).toReal = a.toReal * b.toReal := by
  simp only [Dyadic.toReal, Dyadic.mul, Int.cast_mul,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem Dyadic.toReal_half (a : Dyadic) :
    a.half.toReal = a.toReal / 2 := by
  simp [Dyadic.toReal, Dyadic.half,
    zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), mul_div_assoc]

end VerifiedSqrt
