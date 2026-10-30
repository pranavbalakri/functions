module

public import VerifiedSqrt.Arm.SetupInstructions

public section

namespace VerifiedSqrt.Arm

attribute [local cbv_opaque] Machine.readW Machine.writeW Machine.readX Machine.writeX
  Machine.readS Machine.writeS Machine.writeFP supportedControls branchPC
  UInt32.add UInt32.sub UInt32.shiftLeft UInt32.shiftRight UInt64.add sign32
  rsqrtEstimate32 mul32

private theorem shift_zero32 (w : UInt32) : UInt32.shiftLeft w ⟨0#32⟩ = w :=
  UInt32.shiftLeft_zero

theorem step_input_magnitude (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x12007801 s = some (s.advanceW 1 (s.readW 0 &&& 0x7fffffff)) := by
  unfold step
  rw [hc]
  cbv

theorem step_input_zero (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x34000741 s = some {s with
      pc := if s.readW 1 == 0 then branchPC s.pc 232 else s.pc + 4} := by
  unfold step
  rw [hc]
  cbv
  simp only [Bool.rec_eq]
  split <;> rfl

theorem step_input_sign (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x37f80740 s = some {s with
      pc := if (s.readW 0 >>> 31) &&& 1 != 0 then branchPC s.pc 232 else s.pc + 4} := by
  unfold step
  rw [hc]
  cbv

theorem step_input_infinity (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x52aff002 s = some (s.advanceW 2 0x7f800000) := by
  unfold step
  rw [hc]
  cbv

theorem step_input_compare (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x6b02001f s = some {s with
      pc := s.pc + 4
      negative := sign32 (s.readW 0 - s.readW 2)
      zero := s.readW 0 - s.readW 2 == 0
      carry := s.readW 0 ≥ s.readW 2
      overflow := (sign32 (s.readW 0) != sign32 (s.readW 2)) &&
        (sign32 (s.readW 0 - s.readW 2) != sign32 (s.readW 0))} := by
  unfold step
  rw [hc]
  cbv
  simp only [shift_zero32]

theorem step_input_equal (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x540006c0 s = some {s with
      pc := if s.zero then branchPC s.pc 216 else s.pc + 4} := by
  unfold step
  rw [hc]
  cbv

theorem step_input_higher (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x540006c8 s = some {s with
      pc := if s.carry && !s.zero then branchPC s.pc 216 else s.pc + 4} := by
  unfold step
  rw [hc]
  cbv

theorem step_special_estimate (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x7ea1d800 s = some (({s with pc := s.pc + 4} : Machine).writeFP 0
      (rsqrtEstimate32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0))) := by
  unfold step
  rw [hc]
  cbv

theorem step_scale_zero (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x52800004 s = some (s.advanceW 4 0) := by
  unfold step
  rw [hc]
  cbv

theorem step_input_exponent (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x53177801 s = some (s.advanceW 1
      (UInt32.ofNat ((s.readW 0).toNat / 2 ^ 23 % 256))) := by
  unfold step
  rw [hc]
  cbv

theorem step_input_normal (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x350000e1 s = some {s with
      pc := if s.readW 1 != 0 then branchPC s.pc 28 else s.pc + 4} := by
  unfold step
  rw [hc]
  cbv

theorem step_scale_bits (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x52aaf002 s = some (s.advanceW 2 0x57800000) := by
  unfold step
  rw [hc]
  cbv

theorem step_scale_scalar (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x1e270041 s = some (s.advanceS 1 (s.readW 2)) := by
  unfold step
  rw [hc]
  cbv

theorem step_scale_multiply (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x1e210800 s = some (({s with pc := s.pc + 4} : Machine).writeFP 0
      (mul32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0) (s.readS 1))) := by
  unfold step
  rw [hc]
  cbv

theorem step_scale_exponent (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x128002e4 s = some (s.advanceW 4 (UInt32.ofInt (-24))) := by
  unfold step
  rw [hc]
  cbv

end VerifiedSqrt.Arm
