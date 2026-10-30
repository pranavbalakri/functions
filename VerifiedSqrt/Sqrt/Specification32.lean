module

public import VerifiedSqrt.Arm.Rounding32
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

def SqrtSpec32 (dn : Bool) (x y : UInt32) : Prop :=
  if isNaN32 x then y = (if dn then 0x7fc00000 else x ||| 0x400000)
  else if isZero32 x then y = x
  else if sign32 x then y = 0x7fc00000
  else if isInf32 x then y = x
  else sign32 y = false ∧ 0 < (unpack32 y).toReal ∧
    RoundsToNearestEven32 (Real.sqrt (unpack32 x).toReal) y

end VerifiedSqrt.Sqrt
