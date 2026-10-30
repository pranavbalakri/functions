module

public import VerifiedSqrt.Float.Rounding

public section

namespace VerifiedSqrt

theorem scaled_distance (a b c : ℝ) (hc : 0 ≤ c) :
    |a * c - b * c| = |a - b| * c := by
  rw [← sub_mul, abs_mul, abs_of_nonneg hc]

end VerifiedSqrt
