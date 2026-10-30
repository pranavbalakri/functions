module

public import VerifiedSqrt.Arm.InstructionProof

public section

namespace VerifiedSqrt.Arm

attribute [local cbv_opaque] Machine.readW Machine.writeW Machine.readX Machine.writeX
  Machine.readS Machine.writeS Machine.writeFP supportedControls branchPC
  UInt32.add UInt32.sub UInt32.shiftLeft UInt64.add
  UInt64.shiftLeft UInt32.toUInt64

private theorem shift_zero32 (w : UInt32) : UInt32.shiftLeft w ⟨0#32⟩ = w :=
  UInt32.shiftLeft_zero

theorem step_setup_exponent (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x53177802 s = some (s.advanceW 2 (UInt32.ofNat ((s.readW 0).toNat / 2 ^ 23 % 256))) := by
  unfold step
  rw [hc]
  cbv

theorem step_setup_shift (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x51019842 s = some (s.advanceW 2 (s.readW 2 - 102)) := by
  unfold step
  rw [hc]
  cbv

theorem step_setup_fraction (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x12005803 s = some (s.advanceW 3 (s.readW 0 &&& 0x7fffff)) := by
  unfold step
  rw [hc]
  cbv

theorem step_setup_hidden_bit (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x52a01001 s = some (s.advanceW 1 0x800000) := by
  unfold step
  rw [hc]
  cbv

theorem step_setup_significand (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x0b010063 s = some (s.advanceW 3 (s.readW 3 + s.readW 1)) := by
  unfold step
  rw [hc]
  cbv
  simp only [shift_zero32]

theorem step_setup_radicand (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x9ac22063 s = some (s.advanceX 3 (s.readX 3 <<< (s.readX 2 &&& 63))) := by
  unfold step
  rw [hc]
  cbv

theorem step_scalar_to_word (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x1e260000 s = some (s.advanceW 0 (s.readS 0)) := by
  unfold step
  rw [hc]
  cbv

theorem step_setup_seed_fraction (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x12005800 s = some (s.advanceW 0 (s.readW 0 &&& 0x7fffff)) := by
  unfold step
  rw [hc]
  cbv

end VerifiedSqrt.Arm
