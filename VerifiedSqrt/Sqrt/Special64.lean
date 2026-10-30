module

public import VerifiedSqrt.Arm.Classification64
public import VerifiedSqrt.Sqrt.Algorithm64

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

theorem algorithm64_zero (dn : Bool) (x : UInt64) (hz : isZero64 x = true) :
    algorithm64 dn x = x := by
  simp [algorithm64, hz]

theorem algorithm64_infinity (dn : Bool) :
    algorithm64 dn 0x7ff0000000000000 = 0x7ff0000000000000 := by
  simp [algorithm64]

theorem algorithm64_nan (dn : Bool) (x : UInt64) (hn : isNaN64 x = true) :
    algorithm64 dn x = if dn then 0x7ff8000000000000 else x ||| 0x0008000000000000 := by
  have hz := nan64_nonzero x hn
  have hne : x ≠ 0x7ff0000000000000 := by
    intro h
    subst x
    have hc : isNaN64 0x7ff0000000000000 = false := by decide +kernel
    simp [hc] at hn
  simp [algorithm64, hz, hne, hn, rsqrtEstimate64, processNaN64]

theorem algorithm64_negative (dn : Bool) (x : UInt64) (hs : sign64 x = true)
    (hz : isZero64 x = false) (hn : isNaN64 x = false) :
    algorithm64 dn x = 0x7ff8000000000000 := by
  have hne : x ≠ 0x7ff0000000000000 := by
    intro h
    subst x
    have hc : sign64 0x7ff0000000000000 = false := by decide +kernel
    simp [hc] at hs
  simp [algorithm64, hz, hne, hs, hn, rsqrtEstimate64]

end VerifiedSqrt.Sqrt
