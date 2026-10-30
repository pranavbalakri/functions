module

public import VerifiedSqrt.Arm.Setup64
public import VerifiedSqrt.Arm.Return64

public section

namespace VerifiedSqrt.Arm

attribute [local cbv_opaque] Machine.readW Machine.writeW Machine.readX Machine.writeX
  Machine.readD Machine.writeD Machine.writeFP64 supportedControls branchPC
  UInt32.add UInt32.sub UInt32.shiftLeft UInt32.shiftRight UInt64.add UInt64.sub UInt64.shiftLeft UInt64.shiftRight
  rsqrtEstimate64 mul64

private theorem shift_zero64 (w : UInt64) : UInt64.shiftLeft w ⟨0#64⟩ = w :=
  UInt64.shiftLeft_zero

theorem step64_input_magnitude (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9240f801 s = some (s.advanceX 1 (s.readX 0 &&& 0x7fffffffffffffff)) := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_input_zero (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xb4000901 s = some {s with
      pc := if s.readX 1 == 0 then branchPC s.pc 288 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv
  simp only [Bool.rec_eq]
  split <;> rfl

theorem step64_input_sign (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xb7f80900 s = some {s with
      pc := if (s.readX 0 >>> 63) &&& 1 != 0 then branchPC s.pc 288 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_input_infinity (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xd2effe02 s = some (s.advanceX 2 0x7ff0000000000000) := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_input_compare (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xeb02001f s = some {s with
      pc := s.pc + 4
      negative := ((s.readX 0 - s.readX 2) >>> 63 != 0)
      zero := s.readX 0 - s.readX 2 == 0
      carry := s.readX 0 ≥ s.readX 2
      overflow := ((s.readX 0 >>> 63 != 0) != (s.readX 2 >>> 63 != 0)) &&
        (((s.readX 0 - s.readX 2) >>> 63 != 0) != (s.readX 0 >>> 63 != 0))} := by
  unfold step64 step
  rw [hc]
  cbv
  simp only [shift_zero64]

theorem step64_input_equal (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x54000880 s = some {s with
      pc := if s.zero then branchPC s.pc 272 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_input_higher (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x54000888 s = some {s with
      pc := if s.carry && !s.zero then branchPC s.pc 272 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_special_estimate (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x7ee1d800 s = some (({s with pc := s.pc + 4} : Machine).writeFP64 0
      (rsqrtEstimate64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0))) := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_scale_zero (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x52800004 s = some (s.advanceW 4 0) := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_input_exponent (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xd374f801 s = some (s.advanceX 1
      (UInt64.ofNat ((s.readX 0).toNat / 2 ^ 52 % 2048))) := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_input_normal (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xb50000e1 s = some {s with
      pc := if s.readX 1 != 0 then branchPC s.pc 28 else s.pc + 4} := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_scale_bits (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xd2e8d202 s = some (s.advanceX 2 0x4690000000000000) := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_scale_scalar (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9e670041 s = some (s.advanceD 1 (s.readX 2)) := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_scale_multiply (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x1e610800 s = some (({s with pc := s.pc + 4} : Machine).writeFP64 0
      (mul64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0) (s.readD 1))) := by
  unfold step64 step
  rw [hc]
  cbv

theorem step64_scale_exponent (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x12800684 s = some (s.advanceW 4 (UInt32.ofInt (-53))) := by
  unfold step64 step
  rw [hc]
  cbv

end VerifiedSqrt.Arm
