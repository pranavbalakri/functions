module

public import Mathlib.Analysis.Real.Sqrt

namespace VerifiedSqrt

public theorem real_sqrt_square (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x) ^ 2 = x :=
  Real.sq_sqrt hx

#print axioms real_sqrt_square

end VerifiedSqrt
