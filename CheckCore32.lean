import VerifiedSqrt.Sqrt.Algorithm32

open VerifiedSqrt.Sqrt

def main : IO Unit := do
  for i in [:2 ^ 24] do
    let x := UInt32.ofNat (0x3f800000 + i)
    if !coreCertificate32 x then
      throw (IO.userError s!"certificate failed: input={x} output={core32 x}")
  IO.println "PASS normalized_inputs=16777216 exact_integer_midpoint_certificates=true"
