import VerifiedSqrt.Arm.Scalar32

open VerifiedSqrt.Arm

def word (data : ByteArray) (i : Nat) : UInt32 :=
  data[i]!.toUInt32 ||| (data[i + 1]!.toUInt32 <<< 8) |||
  (data[i + 2]!.toUInt32 <<< 16) ||| (data[i + 3]!.toUInt32 <<< 24)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: checkInstructions oracle.bin")
  let input ← IO.FS.Handle.mk path .read
  let mut count := 0
  let mut counts := Array.replicate 7 0
  repeat
    let data ← input.read (32 * 32768)
    if data.isEmpty then break
    if data.size % 32 != 0 then throw (IO.userError "truncated record")
    for i in [:data.size / 32] do
      let j := 32 * i
      let op := (word data j).toNat
      if op ≥ 7 || (word data (j + 4)).toNat > 1 || word data (j + 28) != 0 then
        throw (IO.userError "invalid record")
      let dn := word data (j + 4) != 0
      let a := word data (j + 8)
      let b := word data (j + 12)
      let c := word data (j + 16)
      let expected := word data (j + 20)
      let flags := word data (j + 24)
      let result := eval32 op dn a b c
      if result.bits != expected || result.flags != flags then
        throw (IO.userError s!"row={count} op={op} DN={dn} a={a} b={b} c={c} model={result.bits}/{result.flags} hardware={expected}/{flags}")
      count := count + 1
      counts := counts.modify op (· + 1)
  IO.println s!"PASS rows={count} per_op={counts} results_and_FPSR=true"
