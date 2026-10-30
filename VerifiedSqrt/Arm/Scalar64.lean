module

public import VerifiedSqrt.Float.Dyadic
public import VerifiedSqrt.Arm.Estimate

@[expose] public section

namespace VerifiedSqrt.Arm

public structure FPResult64 where
  bits : UInt64
  flags : UInt32 := 0
deriving Repr, DecidableEq

public def sign64 (x : UInt64) : Bool := x &&& 0x8000000000000000 != 0
public def exponent64 (x : UInt64) : Nat := ((x >>> 52) &&& 2047).toNat
public def fraction64 (x : UInt64) : Nat := (x &&& 0x000fffffffffffff).toNat
public def isNaN64 (x : UInt64) : Bool := exponent64 x == 2047 && fraction64 x != 0
public def isSNaN64 (x : UInt64) : Bool := isNaN64 x && x &&& 0x0008000000000000 == 0
public def isInf64 (x : UInt64) : Bool := x &&& 0x7fffffffffffffff == 0x7ff0000000000000
public def isZero64 (x : UInt64) : Bool := x &&& 0x7fffffffffffffff == 0
public def signed64 (s : Bool) (n : Nat) : UInt64 :=
  UInt64.ofNat n ||| if s then 0x8000000000000000 else 0

public def unpack64 (x : UInt64) : Dyadic :=
  let e := exponent64 x
  let m := fraction64 x + if e == 0 then 0 else 2 ^ 52
  ⟨if sign64 x then -(m : Int) else m, (max e 1 : Nat) - (1075 : Int)⟩

public def round64 (v : Dyadic) : FPResult64 := Id.run do
  let n := v.coefficient.natAbs
  let s := v.coefficient < 0
  if n == 0 then return ⟨0, 0⟩
  let top := (n.log2 : Int) + v.exponent
  let e := max (top - 52) (-1074)
  let (q, inexact) := if e > v.exponent then
      roundShiftEven n (e - v.exponent).toNat
    else (n * 2 ^ (v.exponent - e).toNat, false)
  let underflow := top < -1022 && inexact
  let mut biased := (e + 1075).toNat
  let mut mantissa := q
  if mantissa < 2 ^ 52 then biased := 0
  if mantissa ≥ 2 ^ 53 then
    mantissa := mantissa / 2
    biased := biased + 1
  if biased ≥ 2047 then return ⟨signed64 s 0x7ff0000000000000, 20⟩
  return ⟨signed64 s (biased * 2 ^ 52 + mantissa % 2 ^ 52),
    (if inexact then 16 else 0) ||| (if underflow then 8 else 0)⟩

public def processNaN64 (dn : Bool) (x : UInt64) : FPResult64 :=
  ⟨if dn then 0x7ff8000000000000 else x ||| 0x0008000000000000, if isSNaN64 x then 1 else 0⟩

public def processNaNs64 (dn : Bool) (xs : List UInt64) : Option FPResult64 :=
  match xs.find? isSNaN64 with
  | some x => some (processNaN64 dn x)
  | none => (xs.find? isNaN64).map (processNaN64 dn)

public def mul64 (dn : Bool) (a b : UInt64) : FPResult64 :=
  match processNaNs64 dn [a, b] with
  | some r => r
  | none =>
    let s := sign64 a != sign64 b
    if (isInf64 a && isZero64 b) || (isZero64 a && isInf64 b) then ⟨0x7ff8000000000000, 1⟩
    else if isInf64 a || isInf64 b then ⟨signed64 s 0x7ff0000000000000, 0⟩
    else if isZero64 a || isZero64 b then ⟨signed64 s 0, 0⟩
    else round64 ((unpack64 a).mul (unpack64 b))

public def mulAdd64 (dn : Bool) (a b c : UInt64) : FPResult64 :=
  let invalidProduct := (isInf64 a && isZero64 b) || (isZero64 a && isInf64 b)
  if isNaN64 c && !isSNaN64 c && invalidProduct then ⟨0x7ff8000000000000, 1⟩ else
  match processNaNs64 dn [c, a, b] with
  | some r => r
  | none =>
    let sp := sign64 a != sign64 b
    let ip := isInf64 a || isInf64 b
    if invalidProduct || (isInf64 c && ip && sign64 c != sp) then ⟨0x7ff8000000000000, 1⟩
    else if isInf64 c then ⟨c, 0⟩
    else if ip then ⟨signed64 sp 0x7ff0000000000000, 0⟩
    else if isZero64 c && (isZero64 a || isZero64 b) && sign64 c == sp then
      ⟨signed64 sp 0, 0⟩
    else round64 ((unpack64 c).add ((unpack64 a).mul (unpack64 b)))

public def rsqrtEstimate64 (dn : Bool) (x : UInt64) : FPResult64 := Id.run do
  if isNaN64 x then return processNaN64 dn x
  if isZero64 x then return ⟨signed64 (sign64 x) 0x7ff0000000000000, 2⟩
  if sign64 x then return ⟨0x7ff8000000000000, 1⟩
  if isInf64 x then return ⟨0, 0⟩
  let mut e : Int := exponent64 x
  let mut f := fraction64 x
  if e == 0 then
    let shift := 52 - f.log2
    f := (f * 2 ^ shift) % 2 ^ 52
    e := 1 - (shift : Int)
  let scaled := if e % 2 == 0 then 256 + f / 2 ^ 44 else 128 + f / 2 ^ 45
  let estimate := recipSqrtTable[scaled - 128]!
  return ⟨UInt64.ofNat (((3068 - e) / 2).toNat * 2 ^ 52 + (estimate % 256) * 2 ^ 44), 0⟩

public def rsqrtStep64 (dn : Bool) (a b : UInt64) : FPResult64 :=
  let a := a ^^^ 0x8000000000000000
  match processNaNs64 dn [a, b] with
  | some r => r
  | none =>
    if (isInf64 a && isZero64 b) || (isZero64 a && isInf64 b) then ⟨0x3ff8000000000000, 0⟩
    else if isInf64 a || isInf64 b then ⟨signed64 (sign64 a != sign64 b) 0x7ff0000000000000, 0⟩
    else round64 ((Dyadic.add ⟨3, 0⟩ ((unpack64 a).mul (unpack64 b))).half)

public def eval64 (op : Nat) (dn : Bool) (a b c : UInt64) : FPResult64 :=
  match op with
  | 0 => rsqrtEstimate64 dn a
  | 1 => rsqrtStep64 dn a b
  | 2 => mul64 dn a b
  | 3 => mulAdd64 dn a b c
  | 4 => mulAdd64 dn (a ^^^ 0x8000000000000000) b c
  | 5 => mulAdd64 dn a b (c ^^^ 0x8000000000000000)
  | _ => mulAdd64 dn (a ^^^ 0x8000000000000000) b (c ^^^ 0x8000000000000000)

end VerifiedSqrt.Arm
