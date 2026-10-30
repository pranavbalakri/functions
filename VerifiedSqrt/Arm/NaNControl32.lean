module

public import VerifiedSqrt.Arm.Scalar32

public section

namespace VerifiedSqrt.Arm

theorem mul32_dn_independent (dn : Bool) (a b : UInt32)
    (ha : isNaN32 a = false) (hb : isNaN32 b = false) :
    mul32 dn a b = mul32 false a b := by
  have hsa : isSNaN32 a = false := by simp [isSNaN32, ha]
  have hsb : isSNaN32 b = false := by simp [isSNaN32, hb]
  simp [mul32, processNaNs32, List.find?, ha, hb, hsa, hsb]

end VerifiedSqrt.Arm
