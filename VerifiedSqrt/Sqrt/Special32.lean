module

public import VerifiedSqrt.Arm.Classification32
public import VerifiedSqrt.Sqrt.Algorithm32

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

theorem algorithm32_zero (dn : Bool) (x : UInt32) (hz : isZero32 x = true) :
    algorithm32 dn x = x := by
  simp [algorithm32, hz]

theorem algorithm32_infinity (dn : Bool) :
    algorithm32 dn 0x7f800000 = 0x7f800000 := by
  simp [algorithm32]

theorem algorithm32_nan (dn : Bool) (x : UInt32) (hn : isNaN32 x = true) :
    algorithm32 dn x = if dn then 0x7fc00000 else x ||| 0x400000 := by
  have hz := nan32_nonzero x hn
  have hne : x ≠ 0x7f800000 := by
    intro h
    subst x
    have hc : isNaN32 0x7f800000 = false := by decide +kernel
    simp [hc] at hn
  simp [algorithm32, hz, hne, hn, rsqrtEstimate32, processNaN32]

theorem algorithm32_negative (dn : Bool) (x : UInt32) (hs : sign32 x = true)
    (hz : isZero32 x = false) (hn : isNaN32 x = false) :
    algorithm32 dn x = 0x7fc00000 := by
  have hne : x ≠ 0x7f800000 := by
    intro h
    subst x
    have hc : sign32 0x7f800000 = false := by decide +kernel
    simp [hc] at hs
  simp [algorithm32, hz, hne, hs, hn, rsqrtEstimate32]

end VerifiedSqrt.Sqrt
