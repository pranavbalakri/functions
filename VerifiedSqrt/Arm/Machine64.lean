module

public import VerifiedSqrt.Arm.Machine
public import VerifiedSqrt.Arm.Scalar64
public import VerifiedSqrt.Arm.Sqrt64Code

@[expose] public section

namespace VerifiedSqrt.Arm

def Machine.readD (s : Machine) (n : Nat) : UInt64 := UInt64.ofNat s.v[n]!.toNat

def Machine.writeD (s : Machine) (n : Nat) (w : UInt64) : Machine :=
  {s with v := s.v.set! n (BitVec.ofNat 128 w.toNat)}

def Machine.writeFP64 (s : Machine) (n : Nat) (r : FPResult64) : Machine :=
  {s.writeD n r.bits with fpsr := s.fpsr ||| r.flags}

def multiplyHigh64 (a b : UInt64) : UInt64 := UInt64.ofNat (a.toNat * b.toNat / 2 ^ 64)

def step64 (word : UInt32) (s : Machine) : Option Machine :=
  let d := field word 0 5
  let n := field word 5 5
  let m := field word 16 5
  let a := field word 10 5
  let next := {s with pc := s.pc + 4}
  let dn := s.fpcr &&& 0x02000000 != 0
  if !supportedControls s.fpcr then none
  else if word &&& 0xfffffc00 == 0x9e660000 then some (next.writeX d (s.readD n))
  else if word &&& 0xfffffc00 == 0x9e670000 then some (next.writeD d (s.readX n))
  else if word &&& 0xffffffe0 == 0x1e6c1000 then some (next.writeD d 0x3fe0000000000000)
  else if word &&& 0xfffffc00 == 0x7ee1d800 then
    some (next.writeFP64 d (rsqrtEstimate64 dn (s.readD n)))
  else if word &&& 0xffe0fc00 == 0x5ee0fc00 then
    some (next.writeFP64 d (rsqrtStep64 dn (s.readD n) (s.readD m)))
  else if word &&& 0xffe0fc00 == 0x1e600800 then
    some (next.writeFP64 d (mul64 dn (s.readD n) (s.readD m)))
  else if word &&& 0xffc00000 == 0x1f400000 then
    let na := field word 21 1 != 0
    let nn := (field word 15 1 != 0) != na
    let x := s.readD n ^^^ if nn then 0x8000000000000000 else 0
    let z := s.readD a ^^^ if na then 0x8000000000000000 else 0
    some (next.writeFP64 d (mulAdd64 dn x (s.readD m) z))
  else if word &&& 0xffc00000 == 0x92400000 && field word 16 6 == 0 &&
      field word 10 6 < 63 && d != 31 then
    let mask := UInt64.ofNat (2 ^ (field word 10 6 + 1) - 1)
    some (next.writeX d (s.readX n &&& mask))
  else if word &&& 0xff800000 == 0xd2800000 || word &&& 0xff800000 == 0x92800000 then
    let bits := UInt64.ofNat (field word 5 16 * 2 ^ (16 * field word 21 2))
    some (next.writeX d (if word &&& 0x40000000 == 0 then ~~~bits else bits))
  else if word &&& 0xffc00000 == 0xd3400000 then
    let r := field word 16 6
    let t := field word 10 6
    if r ≤ t then
      some (next.writeX d (UInt64.ofNat ((s.readX n).toNat / 2 ^ r % 2 ^ (t - r + 1))))
    else none
  else if (word &&& 0xff800000 == 0x91000000 || word &&& 0xff800000 == 0xd1000000) &&
      n != 31 && d != 31 then
    let imm := UInt64.ofNat (field word 10 12 * 2 ^ (12 * field word 22 1))
    let value := if word &&& 0x40000000 == 0 then s.readX n + imm else s.readX n - imm
    some (next.writeX d value)
  else if word &&& 0xffe00000 == 0x8b000000 || word &&& 0xffe00000 == 0xaa000000 then
    let rhs := s.readX m <<< UInt64.ofNat (field word 10 6)
    let value := if word &&& 0xffe00000 == 0x8b000000 then s.readX n + rhs else s.readX n ||| rhs
    some (next.writeX d value)
  else if word &&& 0xffe00000 == 0x4b000000 && field word 10 6 < 32 then
    some (next.writeW d (s.readW n - (s.readW m <<< UInt32.ofNat (field word 10 6))))
  else if word &&& 0xffe0fc00 == 0x9ac02400 then
    some (next.writeX d (s.readX n >>> (s.readX m &&& 63)))
  else if word &&& 0xffe0fc00 == 0x9b007c00 then
    some (next.writeX d (s.readX n * s.readX m))
  else if word &&& 0xffe0fc00 == 0x9bc07c00 then
    some (next.writeX d (multiplyHigh64 (s.readX n) (s.readX m)))
  else if word &&& 0xfe000000 == 0xb4000000 then
    let taken := (s.readX d != 0) == (field word 24 1 != 0)
    some {next with pc := if taken then branchPC s.pc (4 * signedField word 5 19) else next.pc}
  else if word &&& 0xfe000000 == 0xb6000000 then
    let bit := 32 + field word 19 5
    let set := (s.readX d >>> UInt64.ofNat bit) &&& 1 != 0
    let taken := set == (field word 24 1 != 0)
    some {next with pc := if taken then branchPC s.pc (4 * signedField word 5 14) else next.pc}
  else step word s

def run64 (code : Array UInt32) (base returnPC : UInt64) : Nat → Machine → Option Machine
  | 0, s => if s.pc == returnPC then some s else none
  | fuel + 1, s => do
    if s.pc == returnPC then return s
    if s.pc.toNat % 4 != 0 then none else do
      let word ← code[(s.pc - base).toNat / 4]?
      let next ← step64 word s
      run64 code base returnPC fuel next

def initial64 (dn : Bool) (x : UInt64) : Machine :=
  let s := Machine.writeD {} 0 x
  {s with x := s.x.set! 30 4096, fpcr := if dn then 0x02000000 else 0}

def sqrt64Fuel : Nat := 2 ^ 58

def machine64 (dn : Bool) (x : UInt64) : Option UInt64 :=
  (run64 sqrt64Code 0 4096 sqrt64Fuel (initial64 dn x)).map (fun s => s.readD 0)

end VerifiedSqrt.Arm
