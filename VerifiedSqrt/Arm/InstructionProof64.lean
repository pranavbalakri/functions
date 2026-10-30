module

public import VerifiedSqrt.Arm.Registers
public import VerifiedSqrt.Arm.Machine64

public section

namespace VerifiedSqrt.Arm

attribute [local cbv_opaque] Machine.readW Machine.writeW Machine.readX Machine.writeX
  Machine.readS Machine.writeS Machine.writeFP Machine.readD Machine.writeD Machine.writeFP64
  supportedControls branchPC multiplyHigh64 UInt32.add UInt32.sub UInt32.shiftLeft
  UInt64.add UInt64.sub UInt64.mul UInt64.shiftLeft UInt64.shiftRight UInt32.toUInt64

private theorem shift_zero64 (w : UInt64) : UInt64.shiftLeft w ⟨0#64⟩ = w :=
  UInt64.shiftLeft_zero

theorem step64_double_candidate (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x8b000002 s =
      some (({s with pc := s.pc + 4} : Machine).writeX 2 (s.readX 0 + s.readX 0)) := by
  unfold step64
  rw [hc]
  cbv
  simp only [shift_zero64]

theorem step64_lower_midpoint (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xd1000442 s =
      some (({s with pc := s.pc + 4} : Machine).writeX 2 (s.readX 2 - 1)) := by
  unfold step64
  rw [hc]
  cbv

theorem step64_upper_midpoint (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x91000442 s =
      some (({s with pc := s.pc + 4} : Machine).writeX 2 (s.readX 2 + 1)) := by
  unfold step64
  rw [hc]
  cbv

theorem step64_square_high (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9bc27c46 s =
      some (({s with pc := s.pc + 4} : Machine).writeX 6 (multiplyHigh64 (s.readX 2) (s.readX 2))) := by
  unfold step64
  rw [hc]
  cbv

theorem step64_square_low (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9b027c42 s =
      some (({s with pc := s.pc + 4} : Machine).writeX 2 (s.readX 2 * s.readX 2)) := by
  unfold step64
  rw [hc]
  cbv

end VerifiedSqrt.Arm
