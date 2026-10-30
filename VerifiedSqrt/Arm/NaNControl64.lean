module

public import VerifiedSqrt.Arm.Scalar64

public section

namespace VerifiedSqrt.Arm

theorem mul64_dn_independent (dn : Bool) (a b : UInt64)
    (ha : isNaN64 a = false) (hb : isNaN64 b = false) :
    mul64 dn a b = mul64 false a b := by
  have hsa : isSNaN64 a = false := by simp [isSNaN64, ha]
  have hsb : isSNaN64 b = false := by simp [isSNaN64, hb]
  simp [mul64, processNaNs64, List.find?, ha, hb, hsa, hsb]

end VerifiedSqrt.Arm
