module

public import VerifiedSqrt.Float.Dyadic
public import VerifiedSqrt.Arm.Estimate

@[expose] public section

namespace VerifiedSqrt.Arm

public structure FPResult where
  bits : UInt32
  flags : UInt32 := 0
deriving Repr, DecidableEq

public def sign32 (x : UInt32) : Bool := x &&& 0x80000000 != 0
public def exponent32 (x : UInt32) : Nat := ((x >>> 23) &&& 255).toNat
public def fraction32 (x : UInt32) : Nat := (x &&& 0x7fffff).toNat
public def isNaN32 (x : UInt32) : Bool := exponent32 x == 255 && fraction32 x != 0
public def isSNaN32 (x : UInt32) : Bool := isNaN32 x && x &&& 0x400000 == 0
public def isInf32 (x : UInt32) : Bool := x &&& 0x7fffffff == 0x7f800000
public def isZero32 (x : UInt32) : Bool := x &&& 0x7fffffff == 0
public def signed32 (s : Bool) (n : Nat) : UInt32 :=
  UInt32.ofNat n ||| if s then 0x80000000 else 0

public def unpack32 (x : UInt32) : Dyadic :=
  let e := exponent32 x
  let m := fraction32 x + if e == 0 then 0 else 2 ^ 23
  ⟨if sign32 x then -(m : Int) else m, (max e 1 : Nat) - (150 : Int)⟩

public def round32 (v : Dyadic) : FPResult := Id.run do
  let n := v.coefficient.natAbs
  let s := v.coefficient < 0
  if n == 0 then return ⟨0, 0⟩
  let top := (n.log2 : Int) + v.exponent
  let e := max (top - 23) (-149)
  let (q, inexact) := if e > v.exponent then
      roundShiftEven n (e - v.exponent).toNat
    else (n * 2 ^ (v.exponent - e).toNat, false)
  let underflow := top < -126 && inexact
  let mut biased := (e + 150).toNat
  let mut mantissa := q
  if mantissa < 2 ^ 23 then biased := 0
  if mantissa ≥ 2 ^ 24 then
    mantissa := mantissa / 2
    biased := biased + 1
  if biased ≥ 255 then return ⟨signed32 s 0x7f800000, 20⟩
  return ⟨signed32 s (biased * 2 ^ 23 + mantissa % 2 ^ 23),
    (if inexact then 16 else 0) ||| (if underflow then 8 else 0)⟩

public def processNaN32 (dn : Bool) (x : UInt32) : FPResult :=
  ⟨if dn then 0x7fc00000 else x ||| 0x400000, if isSNaN32 x then 1 else 0⟩

public def processNaNs32 (dn : Bool) (xs : List UInt32) : Option FPResult :=
  match xs.find? isSNaN32 with
  | some x => some (processNaN32 dn x)
  | none => (xs.find? isNaN32).map (processNaN32 dn)

public def mul32 (dn : Bool) (a b : UInt32) : FPResult :=
  match processNaNs32 dn [a, b] with
  | some r => r
  | none =>
    let s := sign32 a != sign32 b
    if (isInf32 a && isZero32 b) || (isZero32 a && isInf32 b) then ⟨0x7fc00000, 1⟩
    else if isInf32 a || isInf32 b then ⟨signed32 s 0x7f800000, 0⟩
    else if isZero32 a || isZero32 b then ⟨signed32 s 0, 0⟩
    else round32 ((unpack32 a).mul (unpack32 b))

public def mulAdd32 (dn : Bool) (a b c : UInt32) : FPResult :=
  let invalidProduct := (isInf32 a && isZero32 b) || (isZero32 a && isInf32 b)
  if isNaN32 c && !isSNaN32 c && invalidProduct then ⟨0x7fc00000, 1⟩ else
  match processNaNs32 dn [c, a, b] with
  | some r => r
  | none =>
    let sp := sign32 a != sign32 b
    let ip := isInf32 a || isInf32 b
    if invalidProduct || (isInf32 c && ip && sign32 c != sp) then ⟨0x7fc00000, 1⟩
    else if isInf32 c then ⟨c, 0⟩
    else if ip then ⟨signed32 sp 0x7f800000, 0⟩
    else if isZero32 c && (isZero32 a || isZero32 b) && sign32 c == sp then
      ⟨signed32 sp 0, 0⟩
    else round32 ((unpack32 c).add ((unpack32 a).mul (unpack32 b)))

public def rsqrtEstimate32 (dn : Bool) (x : UInt32) : FPResult := Id.run do
  if isNaN32 x then return processNaN32 dn x
  if isZero32 x then return ⟨signed32 (sign32 x) 0x7f800000, 2⟩
  if sign32 x then return ⟨0x7fc00000, 1⟩
  if isInf32 x then return ⟨0, 0⟩
  let mut e : Int := exponent32 x
  let mut f := fraction32 x
  if e == 0 then
    let shift := 23 - f.log2
    f := (f * 2 ^ shift) % 2 ^ 23
    e := 1 - (shift : Int)
  let scaled := if e % 2 == 0 then 256 + f / 2 ^ 15 else 128 + f / 2 ^ 16
  let estimate := recipSqrtTable[scaled - 128]!
  return ⟨UInt32.ofNat (((380 - e) / 2).toNat * 2 ^ 23 + (estimate % 256) * 2 ^ 15), 0⟩

public def rsqrtStep32 (dn : Bool) (a b : UInt32) : FPResult :=
  let a := a ^^^ 0x80000000
  match processNaNs32 dn [a, b] with
  | some r => r
  | none =>
    if (isInf32 a && isZero32 b) || (isZero32 a && isInf32 b) then ⟨0x3fc00000, 0⟩
    else if isInf32 a || isInf32 b then ⟨signed32 (sign32 a != sign32 b) 0x7f800000, 0⟩
    else round32 ((Dyadic.add ⟨3, 0⟩ ((unpack32 a).mul (unpack32 b))).half)

public def eval32 (op : Nat) (dn : Bool) (a b c : UInt32) : FPResult :=
  match op with
  | 0 => rsqrtEstimate32 dn a
  | 1 => rsqrtStep32 dn a b
  | 2 => mul32 dn a b
  | 3 => mulAdd32 dn a b c
  | 4 => mulAdd32 dn (a ^^^ 0x80000000) b c
  | 5 => mulAdd32 dn a b (c ^^^ 0x80000000)
  | _ => mulAdd32 dn (a ^^^ 0x80000000) b (c ^^^ 0x80000000)

end VerifiedSqrt.Arm
