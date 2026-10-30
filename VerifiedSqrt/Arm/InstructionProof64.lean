module

public import VerifiedSqrt.Arm.Trace64
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

theorem step64_compare_high (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xeb0600bf s = some (compare64State s (s.readX 5) (s.readX 6)) := by
  unfold step64 step compare64State
  rw [hc]
  cbv
  simp only [shift_zero64]

theorem step64_compare_low (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xeb02007f s = some (compare64State s (s.readX 3) (s.readX 2)) := by
  unfold step64 step compare64State
  rw [hc]
  cbv
  simp only [shift_zero64]

theorem step64_lo80 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x54000283 s = some {s with pc := if !s.carry then branchPC s.pc 80 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_hi12 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x54000068 s = some {s with pc := if s.carry && !s.zero then branchPC s.pc 12 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_lo68 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x54000223 s = some {s with pc := if !s.carry then branchPC s.pc 68 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_hi52 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x540001a8 s = some {s with pc := if s.carry && !s.zero then branchPC s.pc 52 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_lo12 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x54000063 s = some {s with pc := if !s.carry then branchPC s.pc 12 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_hi40 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x54000148 s = some {s with pc := if s.carry && !s.zero then branchPC s.pc 40 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_decrement (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xd1000400 s = some (s.advanceX 0 (s.readX 0 - 1)) := by
  unfold step64 Machine.advanceX
  rw [hc]
  cbv

theorem step64_increment (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x91000400 s = some (s.advanceX 0 (s.readX 0 + 1)) := by
  unfold step64 Machine.advanceX
  rw [hc]
  cbv

theorem step64_back_down (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x17ffffe6 s = some {s with pc := branchPC s.pc (-104)} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_back_up (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x17ffffe4 s = some {s with pc := branchPC s.pc (-112)} := by
  unfold step64 step
  rw [hc]
  cbv

end VerifiedSqrt.Arm
