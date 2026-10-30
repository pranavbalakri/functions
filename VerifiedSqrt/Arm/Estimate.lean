module

public import Std

@[expose] public section

namespace VerifiedSqrt.Arm

public def estimateLoop (a : Nat) : Nat → Nat → Nat
  | 0, b => (b + 1) / 2
  | fuel + 1, b =>
    if a * (b + 1) * (b + 1) ≥ 2 ^ 28 then (b + 1) / 2
    else estimateLoop a fuel (b + 1)

public def recipSqrtEstimate (a : Nat) : Nat :=
  let a := if a < 256 then 2 * a + 1 else 2 * (2 * (a / 2) + 1)
  estimateLoop a 512 512

public def recipSqrtTable : Array Nat :=
  (List.range 384).toArray.map fun i => recipSqrtEstimate (128 + i)

end VerifiedSqrt.Arm
