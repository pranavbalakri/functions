module

public import Std

@[expose] public section

namespace VerifiedSqrt

public structure Dyadic where
  coefficient : Int
  exponent : Int
deriving Repr, DecidableEq

public def Dyadic.add (a b : Dyadic) : Dyadic :=
  let e := min a.exponent b.exponent
  ⟨a.coefficient * (2 ^ (a.exponent - e).toNat : Nat) +
    b.coefficient * (2 ^ (b.exponent - e).toNat : Nat), e⟩

public def Dyadic.mul (a b : Dyadic) : Dyadic :=
  ⟨a.coefficient * b.coefficient, a.exponent + b.exponent⟩

public def Dyadic.half (a : Dyadic) : Dyadic :=
  ⟨a.coefficient, a.exponent - 1⟩

public def roundShiftEven (n k : Nat) : Nat × Bool :=
  if k = 0 then (n, false) else
  let d := 2 ^ k
  let q := n / d
  let r := n % d
  (q + if 2 * r > d || (2 * r == d && q % 2 == 1) then 1 else 0, r != 0)

end VerifiedSqrt
