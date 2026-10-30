import VerifiedSqrt.Arm.Machine

open VerifiedSqrt.Arm

def word64 (data : ByteArray) (i : Nat) : UInt64 := Id.run do
  let mut value : UInt64 := 0
  for j in [:8] do
    value := value ||| (data[i + j]!.toUInt64 <<< UInt64.ofNat (8 * j))
  return value

def vector128 (data : ByteArray) (i : Nat) : BitVec 128 :=
  BitVec.ofNat 128 ((word64 data i).toNat + (word64 data (i + 8)).toNat * 2 ^ 64)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: checkScalarState oracle.bin")
  let input ← IO.FS.Handle.mk path .read
  let words : Array UInt32 := #[0x1e260020, 0x1e270020, 0x1e2c1000, 0x7ea1d820,
    0x5ea2fc20, 0x1e220820, 0x1f020c20, 0x1f028c20, 0x1f228c20, 0x1f220c20]
  let mut count := 0
  let mut counts := Array.replicate 10 0
  repeat
    let data ← input.read (128 * 8192)
    if data.isEmpty then break
    if data.size % 128 != 0 then throw (IO.userError "truncated record")
    for i in [:data.size / 128] do
      let j := 128 * i
      let op := (word64 data j).toNat
      let dn := word64 data (j + 8)
      let before := vector128 data (j + 64)
      let xbefore := word64 data (j + 80)
      let initialFlags := word64 data (j + 88)
      let expectedX := word64 data (j + 96)
      let expectedV := vector128 data (j + 104)
      let expectedFlags := word64 data (j + 120)
      if op ≥ 10 || dn > 1 || initialFlags &&& 0x00000000fffffff0 != 0 ||
          expectedFlags &&& 0x00000000fffffff0 != 0 then
        throw (IO.userError "invalid record")
      let s : Machine := {
        x := (Array.replicate 32 xbefore).set! 1 (word64 data (j + 16))
        v := (((Array.replicate 32 before).set! 1 (vector128 data (j + 16))).set! 2
          (vector128 data (j + 32))).set! 3 (vector128 data (j + 48))
        pc := 1024
        fpcr := dn.toUInt32 <<< 25
        fpsr := (initialFlags >>> 32).toUInt32
        negative := initialFlags &&& 8 != 0
        zero := initialFlags &&& 4 != 0
        carry := initialFlags &&& 2 != 0
        overflow := initialFlags &&& 1 != 0 }
      let some after := step words[op]! s
        | throw (IO.userError s!"decode failed: row={count} op={op}")
      let actualFlags : UInt64 := (after.fpsr.toUInt64 <<< 32) |||
        (if after.negative then 8 else 0) ||| (if after.zero then 4 else 0) |||
        (if after.carry then 2 else 0) ||| (if after.overflow then 1 else 0)
      if after.x != s.x.set! 0 expectedX || after.v != s.v.set! 0 expectedV ||
          actualFlags != expectedFlags || after.pc != 1028 || after.fpcr != s.fpcr then
        throw (IO.userError s!"row={count} op={op} DN={dn} X0={after.readX 0}/{expectedX} V0={after.v[0]!}/{expectedV} flags={actualFlags}/{expectedFlags} pc={after.pc}")
      count := count + 1
      counts := counts.modify op (· + 1)
  IO.println s!"PASS scalar_rows={count} per_op={counts} full_SIMD_GPR_flags_and_PC=true"
