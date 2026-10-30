import VerifiedSqrt.Arm.Machine64

open VerifiedSqrt.Arm

def word64 (data : ByteArray) (i : Nat) : UInt64 := Id.run do
  let mut value : UInt64 := 0
  for j in [:8] do
    value := value ||| (data[i + j]!.toUInt64 <<< UInt64.ofNat (8 * j))
  return value

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: checkInteger64 oracle.bin")
  let input ← IO.FS.Handle.mk path .read
  let words : Array UInt32 := #[
    0x9240f820, 0x9240cc20, 0xd2effe00, 0xd2e8d200,
    0xd2e00200, 0xd2e7fc00, 0xd374f820, 0x91000420,
    0xd1000420, 0x8b020020, 0x8b02d020, 0xaa02d020,
    0x4b020020, 0x9ac22420, 0x9b027c20, 0x9bc27c20,
    0xb4000041, 0xb5000041, 0xb7f80041, 0xb6f80041,
    0x12800680, 0x510ffc20, 0x110ffc20, 0x510f2420,
    0x52800800]
  let mut count := 0
  let mut counts := Array.replicate words.size 0
  repeat
    let data ← input.read (64 * 16384)
    if data.isEmpty then break
    if data.size % 64 != 0 then throw (IO.userError "truncated record")
    for i in [:data.size / 64] do
      let j := 64 * i
      let op := (word64 data j).toNat
      let a := word64 data (j + 8)
      let b := word64 data (j + 16)
      let before := word64 data (j + 24)
      let initialFlags := word64 data (j + 32)
      let expected := word64 data (j + 40)
      let flags := word64 data (j + 48)
      let taken := word64 data (j + 56)
      if op ≥ words.size || initialFlags > 15 || flags > 15 || taken > 1 then
        throw (IO.userError "invalid record")
      let s : Machine := {
        x := (((Array.replicate 32 before).set! 1 a).set! 2 b).set! 30 b
        v := Array.replicate 32 (BitVec.ofNat 128 (a.toNat * 2 ^ 64 + b.toNat))
        pc := 1024
        negative := initialFlags &&& 8 != 0
        zero := initialFlags &&& 4 != 0
        carry := initialFlags &&& 2 != 0
        overflow := initialFlags &&& 1 != 0 }
      let some after := step64 words[op]! s
        | throw (IO.userError s!"decode failed: row={count} op={op}")
      let actualFlags : UInt64 := (if after.negative then 8 else 0) |||
        (if after.zero then 4 else 0) ||| (if after.carry then 2 else 0) |||
        (if after.overflow then 1 else 0)
      let expectedPC := if taken == 1 then 1032 else 1028
      if after.x != s.x.set! 0 expected || actualFlags != flags ||
          after.pc != expectedPC ||
          after.v != s.v || after.fpcr != s.fpcr || after.fpsr != s.fpsr then
        throw (IO.userError s!"row={count} op={op} a={a} b={b} result={after.readX 0}/{expected} flags={actualFlags}/{flags} pc={after.pc}")
      count := count + 1
      counts := counts.modify op (· + 1)
  IO.println s!"PASS integer_rows={count} per_op={counts} registers_flags_and_PC=true"
