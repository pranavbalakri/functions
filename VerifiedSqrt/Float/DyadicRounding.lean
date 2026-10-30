module

public import VerifiedSqrt.Float.DyadicReal
public import VerifiedSqrt.Float.Rounding

@[expose] public section

namespace VerifiedSqrt

def roundMagnitude (n : Nat) (source target : Int) : Nat × Bool :=
  if target > source then roundShiftEven n (target - source).toNat
  else (n * 2 ^ (source - target).toNat, false)

theorem roundMagnitude_nearest (n : Nat) (source target : Int) :
    NearestEvenInteger (((n : ℝ) * (2 : ℝ) ^ source) / (2 : ℝ) ^ target)
      (roundMagnitude n source target).1 := by
  by_cases h : target > source
  · have he : source - target = -((target - source).toNat : Int) := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    rw [roundMagnitude, ite_eq_left h, mul_div_assoc,
      ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), he, zpow_neg, zpow_natCast,
      ← div_eq_mul_inv]
    exact roundShiftEven_nearest _ _
  · have he : source - target = ((source - target).toNat : Int) := by
      rw [Int.toNat_of_nonneg (by omega)]
    rw [roundMagnitude, ite_eq_right h, mul_div_assoc,
      ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), he, zpow_natCast]
    convert nearestEvenInteger_self ((n * 2 ^ (source - target).toNat : Nat) : Int) using 1 <;>
      push_cast <;> rfl

theorem Dyadic.round_nearest (v : Dyadic) (e : Int) :
    let q := (roundMagnitude v.coefficient.natAbs v.exponent e).1
    NearestEvenInteger (v.toReal / (2 : ℝ) ^ e)
      (if v.coefficient < 0 then -(q : Int) else q) := by
  dsimp
  have h := roundMagnitude_nearest v.coefficient.natAbs v.exponent e
  have ha : (v.coefficient.natAbs : ℝ) = |(v.coefficient : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : Int => (z : ℝ)) (Int.natCast_natAbs v.coefficient)
  by_cases hs : v.coefficient < 0
  · rw [ite_eq_left hs]
    have hsR : (v.coefficient : ℝ) < 0 := by exact_mod_cast hs
    have hn := nearestEvenInteger_neg h
    rw [abs_of_neg hsR] at ha
    simpa only [Dyadic.toReal, ha, neg_mul, neg_div, neg_neg] using hn
  · rw [ite_eq_right hs]
    have hsR : (0 : ℝ) ≤ v.coefficient := by exact_mod_cast (le_of_not_gt hs)
    rw [abs_of_nonneg hsR] at ha
    simpa only [Dyadic.toReal, ha] using h

end VerifiedSqrt
