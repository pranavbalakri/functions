module

public import VerifiedSqrt.Arm.Scalar32

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

public def core32 (x : UInt32) : UInt32 :=
  let y₀ := (rsqrtEstimate32 false x).bits
  let y₁ := (mul32 false y₀ (rsqrtStep32 false (mul32 false x y₀).bits y₀).bits).bits
  let y₂ := (mul32 false y₁ (rsqrtStep32 false (mul32 false x y₁).bits y₁).bits).bits
  let s := (mul32 false x y₂).bits
  let h := (mul32 false y₂ 0x3f000000).bits
  let r := (mulAdd32 false (s ^^^ 0x80000000) s x).bits
  (mulAdd32 false r h s).bits

public def algorithm32 (dn : Bool) (x : UInt32) : UInt32 := Id.run do
  if isZero32 x || x == 0x7f800000 then return x
  if sign32 x || isNaN32 x then return (rsqrtEstimate32 dn x).bits
  let subnormal := exponent32 x == 0
  let x := if subnormal then (mul32 false x 0x57800000).bits else x
  let e := (exponent32 x : Int) - 127
  let k := e / 2 - if subnormal then 24 else 0
  let z := UInt32.ofNat (fraction32 x + (127 + (e % 2).toNat) * 2 ^ 23)
  let q := core32 z
  return UInt32.ofNat ((q.toNat : Int) + k * 2 ^ 23).toNat

public def normalizedRadicand32 (x : UInt32) : Nat :=
  (2 ^ 23 + fraction32 x) * 2 ^ (23 + exponent32 x - 127)

public def normalizedSignificand32 (y : UInt32) : Nat :=
  if y == 0x40000000 then 2 ^ 24 else 2 ^ 23 + fraction32 y

public def coreCertificate32 (x : UInt32) : Bool :=
  let y := core32 x
  let n := normalizedRadicand32 x
  let q := normalizedSignificand32 y
  0x3f800000 ≤ y && y ≤ 0x40000000 &&
    (2 * q - 1) ^ 2 < 4 * n && 4 * n < (2 * q + 1) ^ 2

end VerifiedSqrt.Sqrt
