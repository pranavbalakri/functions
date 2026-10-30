module

public import VerifiedSqrt.Arm.Scalar32
public import VerifiedSqrt.Arm.Sqrt32Code

@[expose] public section

namespace VerifiedSqrt.Arm

public structure Machine where
  x : Array UInt64 := Array.replicate 32 0
  v : Array (BitVec 128) := Array.replicate 32 0
  pc : UInt64 := 0
  fpcr : UInt32 := 0
  fpsr : UInt32 := 0
  negative : Bool := false
  zero : Bool := false
  carry : Bool := false
  overflow : Bool := false

public def field (w : UInt32) (lo width : Nat) : Nat :=
  (w.toNat / 2 ^ lo) % 2 ^ width

public def signedField (w : UInt32) (lo width : Nat) : Int :=
  let n := field w lo width
  if n < 2 ^ (width - 1) then n else (n : Int) - (2 : Int) ^ width

public def Machine.readX (s : Machine) (n : Nat) : UInt64 :=
  if n == 31 then 0 else s.x[n]!

public def Machine.readW (s : Machine) (n : Nat) : UInt32 := (s.readX n).toUInt32

public def Machine.writeW (s : Machine) (n : Nat) (w : UInt32) : Machine :=
  if n == 31 then s else { s with x := s.x.set! n w.toUInt64 }

public def Machine.readS (s : Machine) (n : Nat) : UInt32 := UInt32.ofNat s.v[n]!.toNat

public def Machine.writeS (s : Machine) (n : Nat) (w : UInt32) : Machine :=
  { s with v := s.v.set! n (BitVec.ofNat 128 w.toNat) }

public def Machine.writeFP (s : Machine) (n : Nat) (r : FPResult) : Machine :=
  { s.writeS n r.bits with fpsr := s.fpsr ||| r.flags }

public def branchPC (pc : UInt64) (offset : Int) : UInt64 :=
  UInt64.ofNat (((pc.toNat : Int) + offset) % (2 ^ 64)).toNat

public def supportedControls (fpcr : UInt32) : Bool := fpcr &&& 0x01c09f07 == 0

public def step (word : UInt32) (s : Machine) : Option Machine :=
  let d := field word 0 5
  let n := field word 5 5
  let m := field word 16 5
  let a := field word 10 5
  let next := { s with pc := s.pc + 4 }
  let dn := s.fpcr &&& 0x02000000 != 0
  if !supportedControls s.fpcr then none
  else if word &&& 0xfffffc00 == 0x1e260000 then some (next.writeW d (s.readS n))
  else if word &&& 0xfffffc00 == 0x1e270000 then some (next.writeS d (s.readW n))
  else if word &&& 0xffffffe0 == 0x1e2c1000 then some (next.writeS d 0x3f000000)
  else if word &&& 0xfffffc00 == 0x7ea1d800 then
    some (next.writeFP d (rsqrtEstimate32 dn (s.readS n)))
  else if word &&& 0xffe0fc00 == 0x5ea0fc00 then
    some (next.writeFP d (rsqrtStep32 dn (s.readS n) (s.readS m)))
  else if word &&& 0xffe0fc00 == 0x1e200800 then
    some (next.writeFP d (mul32 dn (s.readS n) (s.readS m)))
  else if word &&& 0xffc00000 == 0x1f000000 then
    let na := field word 21 1 != 0
    let nn := (field word 15 1 != 0) != na
    let x := s.readS n ^^^ if nn then 0x80000000 else 0
    let z := s.readS a ^^^ if na then 0x80000000 else 0
    some (next.writeFP d (mulAdd32 dn x (s.readS m) z))
  else if word &&& 0xffc00000 == 0x12000000 && field word 16 6 == 0 && field word 10 6 < 31 then
    let mask := UInt32.ofNat (2 ^ (field word 10 6 + 1) - 1)
    some (next.writeW d (s.readW n &&& mask))
  else if (word &&& 0xff800000 == 0x52800000 || word &&& 0xff800000 == 0x12800000) &&
      field word 21 2 < 2 then
    let bits := UInt32.ofNat (field word 5 16 * 2 ^ (16 * field word 21 2))
    some (next.writeW d (if word &&& 0x40000000 == 0 then ~~~bits else bits))
  else if word &&& 0xffc00000 == 0x53000000 then
    let r := field word 16 6
    let t := field word 10 6
    if r ≤ t && t < 32 then
      some (next.writeW d (UInt32.ofNat ((s.readW n).toNat / 2 ^ r % 2 ^ (t - r + 1))))
    else none
  else if word &&& 0xffc00000 == 0x13000000 && field word 10 6 == 31 && field word 16 6 < 32 then
    let x := s.readW n
    let signed : Int := if sign32 x then (x.toNat : Int) - 2 ^ 32 else x.toNat
    let value := signed / (2 : Int) ^ field word 16 6
    some (next.writeW d (UInt32.ofNat (value % 2 ^ 32).toNat))
  else if word &&& 0xff800000 == 0x11000000 || word &&& 0xff800000 == 0x51000000 then
    let imm := UInt32.ofNat (field word 10 12 * 2 ^ (12 * field word 22 1))
    let value := if word &&& 0x40000000 == 0 then s.readW n + imm else s.readW n - imm
    some (next.writeW d value)
  else if (word &&& 0xffe00000 == 0x0b000000 || word &&& 0xffe00000 == 0x2a000000) &&
      field word 10 6 < 32 then
    let rhs := s.readW m <<< UInt32.ofNat (field word 10 6)
    let value := if word &&& 0xffe00000 == 0x0b000000 then s.readW n + rhs else s.readW n ||| rhs
    some (next.writeW d value)
  else if word &&& 0xffe0001f == 0x6b00001f && field word 10 6 < 32 then
    let lhs := s.readW n
    let rhs := s.readW m <<< UInt32.ofNat (field word 10 6)
    let result := lhs - rhs
    some { next with
      negative := sign32 result
      zero := result == 0
      carry := lhs ≥ rhs
      overflow := (sign32 lhs != sign32 rhs) && (sign32 result != sign32 lhs) }
  else if word &&& 0xfe000000 == 0x34000000 then
    let taken := (s.readW d != 0) == (field word 24 1 != 0)
    some { next with pc := if taken then branchPC s.pc (4 * signedField word 5 19) else next.pc }
  else if word &&& 0xfe000000 == 0x36000000 then
    let bit := field word 19 5
    let set := (s.readW d >>> UInt32.ofNat bit) &&& 1 != 0
    let taken := set == (field word 24 1 != 0)
    some { next with pc := if taken then branchPC s.pc (4 * signedField word 5 14) else next.pc }
  else if word &&& 0xff000010 == 0x54000000 then
    let cond := field word 0 4
    if cond != 0 && cond != 8 then none else
    let taken := if cond == 0 then s.zero else s.carry && !s.zero
    some { next with pc := if taken then branchPC s.pc (4 * signedField word 5 19) else next.pc }
  else if word &&& 0xfffffc1f == 0xd65f0000 then some { s with pc := s.readX n }
  else none

public def run (code : Array UInt32) (returnPC : UInt64) : Nat → Machine → Option Machine
  | 0, s => if s.pc == returnPC then some s else none
  | fuel + 1, s => do
    if s.pc == returnPC then return s
    if s.pc.toNat % 4 != 0 then none else do
      let word ← code[s.pc.toNat / 4]?
      let next ← step word s
      run code returnPC fuel next

public def initial32 (dn : Bool) (x : UInt32) : Machine :=
  let s := Machine.writeS {} 0 x
  { s with
    x := s.x.set! 30 4096
    fpcr := if dn then 0x02000000 else 0 }

public def machine32 (dn : Bool) (x : UInt32) : Option UInt32 :=
  (run sqrt32Code 4096 43 (initial32 dn x)).map (fun s => s.readS 0)

end VerifiedSqrt.Arm
