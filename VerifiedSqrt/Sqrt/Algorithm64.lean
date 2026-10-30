module

public import VerifiedSqrt.Arm.Scalar64
public import VerifiedSqrt.Sqrt.IntegerCorrection

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

public def estimateCore64 (x : UInt64) : UInt64 :=
  let y₀ := (rsqrtEstimate64 false x).bits
  let y₁ := (mul64 false y₀ (rsqrtStep64 false (mul64 false x y₀).bits y₀).bits).bits
  let y₂ := (mul64 false y₁ (rsqrtStep64 false (mul64 false x y₁).bits y₁).bits).bits
  let y₃ := (mul64 false y₂ (rsqrtStep64 false (mul64 false x y₂).bits y₂).bits).bits
  let s := (mul64 false x y₃).bits
  let h := (mul64 false y₃ 0x3fe0000000000000).bits
  let r := (mulAdd64 false (s ^^^ 0x8000000000000000) s x).bits
  (mulAdd64 false r h s).bits

public def normalizedRadicand64 (x : UInt64) : Nat :=
  (2 ^ 52 + fraction64 x) * 2 ^ (52 + exponent64 x - 1023)

public def normalizedSignificand64 (y : UInt64) : Nat :=
  if y == 0x4000000000000000 then 2 ^ 53 else 2 ^ 52 + fraction64 y

public def correctedSignificand64 (x : UInt64) : Nat :=
  correctIntegerRoot (normalizedRadicand64 x) (2 ^ 52)
    (2 ^ 52 + fraction64 (estimateCore64 x))

public def core64 (x : UInt64) : UInt64 :=
  UInt64.ofNat (0x3fe0000000000000 + correctedSignificand64 x)

public def algorithm64 (dn : Bool) (x : UInt64) : UInt64 := Id.run do
  if isZero64 x || x == 0x7ff0000000000000 then return x
  if sign64 x || isNaN64 x then return (rsqrtEstimate64 dn x).bits
  let subnormal := exponent64 x == 0
  let x := if subnormal then (mul64 false x 0x4690000000000000).bits else x
  let e := (exponent64 x : Int) - 1023
  let k := e / 2 - if subnormal then 53 else 0
  let z := UInt64.ofNat (fraction64 x + (1023 + (e % 2).toNat) * 2 ^ 52)
  let q := core64 z
  return UInt64.ofNat ((q.toNat : Int) + k * 2 ^ 52).toNat

public def coreCertificate64 (x : UInt64) : Bool :=
  let y := core64 x
  let n := normalizedRadicand64 x
  let q := normalizedSignificand64 y
  0x3ff0000000000000 ≤ y && y ≤ 0x4000000000000000 &&
    (2 * q - 1) ^ 2 < 4 * n && 4 * n < (2 * q + 1) ^ 2

end VerifiedSqrt.Sqrt
