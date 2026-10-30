import VerifiedSqrt.Arm.Machine64
import VerifiedSqrt.Sqrt.Algorithm64

open VerifiedSqrt.Arm VerifiedSqrt.Sqrt

def word (data : ByteArray) (i : Nat) : UInt64 := Id.run do
  let mut value : UInt64 := 0
  for j in [:8] do
    value := value ||| (data[i + j]!.toUInt64 <<< UInt64.ofNat (8 * j))
  return value

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: checkMachine64 oracle.bin")
  let input ← IO.FS.Handle.mk path .read
  let mut count := 0
  repeat
    let data ← input.read (32 * 32768)
    if data.isEmpty then break
    if data.size % 32 != 0 then throw (IO.userError "truncated record")
    for i in [:data.size / 32] do
      let j := i * 32
      let dn := word data j != 0
      let x := word data (j + 8)
      let expected := word data (j + 16)
      let flags := word data (j + 24)
      let some state := run64 sqrt64Code 0 4096 sqrt64Fuel (initial64 dn x)
        | throw (IO.userError s!"machine failed: row={count} input={x}")
      let got := state.readD 0
      let algorithm := algorithm64 dn x
      if got != expected || got != algorithm || state.fpsr.toUInt64 != flags then
        throw (IO.userError s!"row={count} DN={dn} input={x} machine={got}/{state.fpsr} algorithm={algorithm} hardware={expected}/{flags}")
      count := count + 1
  IO.println s!"PASS machine_rows={count} algorithm_hardware_and_FPSR=true"
