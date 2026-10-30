module

public import Std

@[expose] public section

namespace VerifiedSqrt.Sqrt

def correctIntegerRoot (n : Nat) : Nat → Nat → Nat
  | 0, q => q
  | fuel + 1, q =>
    if 4 * n < (2 * q - 1) ^ 2 then correctIntegerRoot n fuel (q - 1)
    else if (2 * q + 1) ^ 2 < 4 * n then correctIntegerRoot n fuel (q + 1)
    else q

end VerifiedSqrt.Sqrt
