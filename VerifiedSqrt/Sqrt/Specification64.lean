module

public import VerifiedSqrt.Arm.Rounding64
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

def SqrtSpec64 (dn : Bool) (x y : UInt64) : Prop :=
  if isNaN64 x then y = (if dn then 0x7ff8000000000000 else x ||| 0x0008000000000000)
  else if isZero64 x then y = x
  else if sign64 x then y = 0x7ff8000000000000
  else if isInf64 x then y = x
  else sign64 y = false ∧ 0 < (unpack64 y).toReal ∧
    RoundsToNearestEven64 (Real.sqrt (unpack64 x).toReal) y

end VerifiedSqrt.Sqrt
