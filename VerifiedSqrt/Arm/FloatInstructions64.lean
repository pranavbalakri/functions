module

public import VerifiedSqrt.Arm.Registers64
public import VerifiedSqrt.Arm.FloatInstructions
public import VerifiedSqrt.Arm.Trace64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem floatFrame_writeD (s : Machine) (d : Nat) (hd : d < 6) (w : UInt64) :
    FloatFrame s (({s with pc := s.pc + 4} : Machine).writeD d w) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [Machine.writeD]
  · intro r hr
    exact Machine.vector_writeD_ne _ d r (by omega) w

theorem floatFrame_writeFP64 (s : Machine) (d : Nat) (hd : d < 6) (v : FPResult64) :
    FloatFrame s (({s with pc := s.pc + 4} : Machine).writeFP64 d v) := by
  have h := floatFrame_writeD s d hd v.bits
  exact ⟨h.registers, h.fpcr, h.size, h.vectors⟩

attribute [local cbv_opaque] Machine.readW Machine.writeW Machine.readX Machine.writeX
  Machine.readD Machine.writeD Machine.writeFP64 supportedControls branchPC
  UInt64.add rsqrtEstimate64 rsqrtStep64 mul64 mulAdd64 UInt64.xor

private theorem xor_zero64 (w : UInt64) : UInt64.xor w 0 = w :=
  UInt64.xor_zero

theorem step64_float_half (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x1e6c1005 s = some (({s with pc := s.pc + 4} : Machine).writeD 5 (0x3fe0000000000000)) := by
  unfold step64
  rw [hc]
  cbv

theorem progress64_float_half (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step64 0x1e6c1005 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step64_float_half s hc, rfl, floatFrame_writeD s 5 (by decide) _⟩

theorem step64_float_estimate (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x7ee1d801 s = some (({s with pc := s.pc + 4} : Machine).writeFP64 1 (rsqrtEstimate64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0))) := by
  unfold step64
  rw [hc]
  cbv

theorem progress64_float_estimate (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step64 0x7ee1d801 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step64_float_estimate s hc, rfl, floatFrame_writeFP64 s 1 (by decide) _⟩

theorem step64_float_product (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x1e610802 s = some (({s with pc := s.pc + 4} : Machine).writeFP64 2 (mul64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0) (s.readD 1))) := by
  unfold step64
  rw [hc]
  cbv

theorem progress64_float_product (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step64 0x1e610802 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step64_float_product s hc, rfl, floatFrame_writeFP64 s 2 (by decide) _⟩

theorem step64_float_step (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x5ee1fc42 s = some (({s with pc := s.pc + 4} : Machine).writeFP64 2 (rsqrtStep64 (s.fpcr &&& 0x02000000 != 0) (s.readD 2) (s.readD 1))) := by
  unfold step64
  rw [hc]
  cbv

theorem progress64_float_step (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step64 0x5ee1fc42 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step64_float_step s hc, rfl, floatFrame_writeFP64 s 2 (by decide) _⟩

theorem step64_float_refine (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x1e620821 s = some (({s with pc := s.pc + 4} : Machine).writeFP64 1 (mul64 (s.fpcr &&& 0x02000000 != 0) (s.readD 1) (s.readD 2))) := by
  unfold step64
  rw [hc]
  cbv

theorem progress64_float_refine (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step64 0x1e620821 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step64_float_refine s hc, rfl, floatFrame_writeFP64 s 1 (by decide) _⟩

theorem step64_float_half_estimate (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x1e650823 s = some (({s with pc := s.pc + 4} : Machine).writeFP64 3 (mul64 (s.fpcr &&& 0x02000000 != 0) (s.readD 1) (s.readD 5))) := by
  unfold step64
  rw [hc]
  cbv

theorem progress64_float_half_estimate (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step64 0x1e650823 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step64_float_half_estimate s hc, rfl, floatFrame_writeFP64 s 3 (by decide) _⟩

theorem step64_float_residual (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x1f428044 s = some (({s with pc := s.pc + 4} : Machine).writeFP64 4 (mulAdd64 (s.fpcr &&& 0x02000000 != 0) (s.readD 2 ^^^ 0x8000000000000000) (s.readD 2) (s.readD 0))) := by
  unfold step64
  rw [hc]
  cbv
  simp only [xor_zero64]

theorem progress64_float_residual (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step64 0x1f428044 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step64_float_residual s hc, rfl, floatFrame_writeFP64 s 4 (by decide) _⟩

theorem step64_float_correction (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x1f430880 s = some (({s with pc := s.pc + 4} : Machine).writeFP64 0 (mulAdd64 (s.fpcr &&& 0x02000000 != 0) (s.readD 4) (s.readD 3) (s.readD 2))) := by
  unfold step64
  rw [hc]
  cbv
  simp only [xor_zero64]

theorem progress64_float_correction (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step64 0x1f430880 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step64_float_correction s hc, rfl, floatFrame_writeFP64 s 0 (by decide) _⟩

end VerifiedSqrt.Arm
