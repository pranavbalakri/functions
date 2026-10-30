module

public import VerifiedSqrt.Arm.Registers

public section

namespace VerifiedSqrt.Arm

attribute [local cbv_opaque] Machine.readW Machine.writeW Machine.readX Machine.writeX
  Machine.readS Machine.writeS Machine.writeFP supportedControls branchPC
  UInt32.add UInt32.sub UInt32.shiftLeft UInt64.add UInt64.sub UInt64.mul
  UInt64.shiftLeft UInt64.shiftRight UInt32.toUInt64

private theorem shift_zero32 (w : UInt32) : UInt32.shiftLeft w ⟨0#32⟩ = w :=
  UInt32.shiftLeft_zero

private theorem shift_zero64 (w : UInt64) : UInt64.shiftLeft w ⟨0#64⟩ = w :=
  UInt64.shiftLeft_zero

theorem step_double_candidate (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x0b000002 s =
      some (({s with pc := s.pc + 4} : Machine).writeW 2 (s.readW 0 + s.readW 0)) := by
  unfold step
  rw [hc]
  cbv
  simp only [shift_zero32]

theorem step_lower_midpoint (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x51000442 s =
      some (({s with pc := s.pc + 4} : Machine).writeW 2 (s.readW 2 - 1)) := by
  unfold step
  rw [hc]
  cbv

theorem step_upper_midpoint (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x11000442 s =
      some (({s with pc := s.pc + 4} : Machine).writeW 2 (s.readW 2 + 1)) := by
  unfold step
  rw [hc]
  cbv

theorem step_square_midpoint (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x9ba27c42 s =
      some (({s with pc := s.pc + 4} : Machine).writeX 2
        ((s.readW 2).toUInt64 * (s.readW 2).toUInt64)) := by
  unfold step
  rw [hc]
  cbv

theorem step_compare_midpoint (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0xeb02007f s = some { s with
      pc := s.pc + 4
      negative := (s.readX 3 - s.readX 2) >>> 63 != 0
      zero := s.readX 3 - s.readX 2 == 0
      carry := s.readX 3 ≥ s.readX 2
      overflow := ((s.readX 3 >>> 63 != 0) != (s.readX 2 >>> 63 != 0)) &&
        (((s.readX 3 - s.readX 2) >>> 63 != 0) != (s.readX 3 >>> 63 != 0)) } := by
  unfold step
  rw [hc]
  cbv
  simp only [shift_zero64]

theorem step_branch_lower (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x540001a3 s = some { s with
      pc := if !s.carry then branchPC s.pc 52 else s.pc + 4 } := by
  unfold step
  rw [hc]
  cbv

theorem step_branch_upper (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x54000148 s = some { s with
      pc := if s.carry && !s.zero then branchPC s.pc 40 else s.pc + 4 } := by
  unfold step
  rw [hc]
  cbv

theorem step_decrement_candidate (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x51000400 s =
      some (({s with pc := s.pc + 4} : Machine).writeW 0 (s.readW 0 - 1)) := by
  unfold step
  rw [hc]
  cbv

theorem step_increment_candidate (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x11000400 s =
      some (({s with pc := s.pc + 4} : Machine).writeW 0 (s.readW 0 + 1)) := by
  unfold step
  rw [hc]
  cbv

theorem step_back_lower (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x17ffffee s = some { s with pc := branchPC s.pc (-72) } := by
  unfold step
  rw [hc]
  cbv

theorem step_back_upper (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x17ffffec s = some { s with pc := branchPC s.pc (-80) } := by
  unfold step
  rw [hc]
  cbv

end VerifiedSqrt.Arm
