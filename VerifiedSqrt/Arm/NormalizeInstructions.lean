module

public import VerifiedSqrt.Arm.SetupInstructions
public import VerifiedSqrt.Arm.SignedWord32

public section

namespace VerifiedSqrt.Arm

attribute [local cbv_opaque] Machine.readW Machine.writeW Machine.readX Machine.writeX
  Machine.readS Machine.writeS Machine.writeFP supportedControls branchPC
  UInt32.add UInt32.sub UInt32.shiftLeft UInt64.add sign32 Int.ediv Int.emod Int.toNat

private theorem shift_zero32 (w : UInt32) : UInt32.shiftLeft w ⟨0#32⟩ = w :=
  UInt32.shiftLeft_zero

theorem step_unbias_exponent (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x5101fc21 s = some (s.advanceW 1 (s.readW 1 - 127)) := by
  unfold step
  rw [hc]
  cbv

theorem step_halve_exponent (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x13017c22 s = some (s.advanceW 2 (UInt32.ofInt (signedWord32 (s.readW 1) / 2))) := by
  unfold step
  rw [hc]
  cbv

theorem step_save_exponent (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x0b020084 s = some (s.advanceW 4 (s.readW 4 + s.readW 2)) := by
  unfold step
  rw [hc]
  cbv
  simp only [shift_zero32]

theorem step_exponent_parity (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x12000021 s = some (s.advanceW 1 (s.readW 1 &&& 1)) := by
  unfold step
  rw [hc]
  cbv

theorem step_bias_parity (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x1101fc21 s = some (s.advanceW 1 (s.readW 1 + 127)) := by
  unfold step
  rw [hc]
  cbv

theorem step_normalize_bits (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x2a015c00 s = some (s.advanceW 0 (s.readW 0 ||| (s.readW 1 <<< 23))) := by
  unfold step
  rw [hc]
  cbv

end VerifiedSqrt.Arm
