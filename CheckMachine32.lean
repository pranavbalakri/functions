import VerifiedSqrt.Arm.Machine
import VerifiedSqrt.Sqrt.Algorithm32

open VerifiedSqrt.Arm VerifiedSqrt.Sqrt

def word (data : ByteArray) (i : Nat) : UInt32 :=
  data[i]!.toUInt32 ||| (data[i + 1]!.toUInt32 <<< 8) |||
  (data[i + 2]!.toUInt32 <<< 16) ||| (data[i + 3]!.toUInt32 <<< 24)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: checkMachine32 oracle.bin")
  let input ← IO.FS.Handle.mk path .read
  let mut count := 0
  repeat
    let data ← input.read (16 * 32768)
    if data.isEmpty then break
    if data.size % 16 != 0 then throw (IO.userError "truncated record")
    for i in [:data.size / 16] do
      let j := i * 16
      let dn := word data j != 0
      let x := word data (j + 4)
      let expected := word data (j + 8)
      let flags := word data (j + 12)
      let some state := run sqrt32Code 4096 43 (initial32 dn x)
        | throw (IO.userError s!"machine failed: row={count} input={x}")
      let got := state.readS 0
      let algorithm := algorithm32 dn x
      if got != expected || got != algorithm || state.fpsr != flags then
        throw (IO.userError s!"row={count} DN={dn} input={x} machine={got}/{state.fpsr} algorithm={algorithm} hardware={expected}/{flags}")
      count := count + 1
  IO.println s!"PASS machine_rows={count} algorithm_hardware_and_FPSR=true"
