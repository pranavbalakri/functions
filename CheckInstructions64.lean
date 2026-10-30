import VerifiedSqrt.Arm.Scalar64

open VerifiedSqrt.Arm

def word (data : ByteArray) (i : Nat) : UInt64 := Id.run do
  let mut value : UInt64 := 0
  for j in [:8] do
    value := value ||| (data[i + j]!.toUInt64 <<< UInt64.ofNat (8 * j))
  return value

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: checkInstructions64 oracle.bin")
  let input ← IO.FS.Handle.mk path .read
  let mut count := 0
  let mut counts := Array.replicate 7 0
  repeat
    let data ← input.read (64 * 16384)
    if data.isEmpty then break
    if data.size % 64 != 0 then throw (IO.userError "truncated record")
    for i in [:data.size / 64] do
      let j := 64 * i
      let op := (word data j).toNat
      if op ≥ 7 || (word data (j + 8)).toNat > 1 || word data (j + 56) != 0 then
        throw (IO.userError "invalid record")
      let dn := word data (j + 8) != 0
      let a := word data (j + 16)
      let b := word data (j + 24)
      let c := word data (j + 32)
      let expected := word data (j + 40)
      let flags := word data (j + 48)
      let result := eval64 op dn a b c
      if result.bits != expected || result.flags.toUInt64 != flags then
        throw (IO.userError s!"row={count} op={op} DN={dn} a={a} b={b} c={c} model={result.bits}/{result.flags} hardware={expected}/{flags}")
      count := count + 1
      counts := counts.modify op (· + 1)
  IO.println s!"PASS rows={count} per_op={counts} results_and_FPSR=true"
