module

public import VerifiedSqrt.Arm.Registers

@[expose] public section

namespace VerifiedSqrt.Arm

structure FloatFrame (s t : Machine) : Prop where
  registers : t.x = s.x
  fpcr : t.fpcr = s.fpcr
  size : t.v.size = s.v.size
  vectors : ∀ r, 6 ≤ r → t.v[r]! = s.v[r]!

theorem FloatFrame.trans {s t u : Machine} (h : FloatFrame s t) (k : FloatFrame t u) :
    FloatFrame s u :=
  ⟨k.registers.trans h.registers, k.fpcr.trans h.fpcr, k.size.trans h.size,
    fun r hr => (k.vectors r hr).trans (h.vectors r hr)⟩

theorem floatFrame_writeS (s : Machine) (d : Nat) (hd : d < 6) (w : UInt32) :
    FloatFrame s (({s with pc := s.pc + 4} : Machine).writeS d w) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [Machine.writeS]
  · intro r hr
    exact Machine.vector_writeS_ne _ d r (by omega) w

theorem floatFrame_writeFP (s : Machine) (d : Nat) (hd : d < 6) (v : FPResult) :
    FloatFrame s (({s with pc := s.pc + 4} : Machine).writeFP d v) := by
  have h := floatFrame_writeS s d hd v.bits
  exact ⟨h.registers, h.fpcr, h.size, h.vectors⟩

attribute [local cbv_opaque] Machine.readW Machine.writeW Machine.readX Machine.writeX
  Machine.readS Machine.writeS Machine.writeFP supportedControls branchPC
  UInt64.add rsqrtEstimate32 rsqrtStep32 mul32 mulAdd32 UInt32.xor

private theorem xor_zero32 (w : UInt32) : UInt32.xor w 0 = w :=
  UInt32.xor_zero

theorem step_float_half (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x1e2c1005 s = some (({s with pc := s.pc + 4} : Machine).writeS 5 (0x3f000000)) := by
  unfold step
  rw [hc]
  cbv

theorem progress_float_half (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step 0x1e2c1005 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step_float_half s hc, rfl, floatFrame_writeS s 5 (by decide) _⟩

theorem step_float_estimate (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x7ea1d801 s = some (({s with pc := s.pc + 4} : Machine).writeFP 1 (rsqrtEstimate32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0))) := by
  unfold step
  rw [hc]
  cbv

theorem progress_float_estimate (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step 0x7ea1d801 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step_float_estimate s hc, rfl, floatFrame_writeFP s 1 (by decide) _⟩

theorem step_float_product (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x1e210802 s = some (({s with pc := s.pc + 4} : Machine).writeFP 2 (mul32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0) (s.readS 1))) := by
  unfold step
  rw [hc]
  cbv

theorem progress_float_product (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step 0x1e210802 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step_float_product s hc, rfl, floatFrame_writeFP s 2 (by decide) _⟩

theorem step_float_step (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x5ea1fc42 s = some (({s with pc := s.pc + 4} : Machine).writeFP 2 (rsqrtStep32 (s.fpcr &&& 0x02000000 != 0) (s.readS 2) (s.readS 1))) := by
  unfold step
  rw [hc]
  cbv

theorem progress_float_step (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step 0x5ea1fc42 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step_float_step s hc, rfl, floatFrame_writeFP s 2 (by decide) _⟩

theorem step_float_refine (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x1e220821 s = some (({s with pc := s.pc + 4} : Machine).writeFP 1 (mul32 (s.fpcr &&& 0x02000000 != 0) (s.readS 1) (s.readS 2))) := by
  unfold step
  rw [hc]
  cbv

theorem progress_float_refine (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step 0x1e220821 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step_float_refine s hc, rfl, floatFrame_writeFP s 1 (by decide) _⟩

theorem step_float_half_estimate (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x1e250823 s = some (({s with pc := s.pc + 4} : Machine).writeFP 3 (mul32 (s.fpcr &&& 0x02000000 != 0) (s.readS 1) (s.readS 5))) := by
  unfold step
  rw [hc]
  cbv

theorem progress_float_half_estimate (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step 0x1e250823 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step_float_half_estimate s hc, rfl, floatFrame_writeFP s 3 (by decide) _⟩

theorem step_float_residual (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x1f028044 s = some (({s with pc := s.pc + 4} : Machine).writeFP 4 (mulAdd32 (s.fpcr &&& 0x02000000 != 0) (s.readS 2 ^^^ 0x80000000) (s.readS 2) (s.readS 0))) := by
  unfold step
  rw [hc]
  cbv
  simp only [xor_zero32]

theorem progress_float_residual (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step 0x1f028044 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step_float_residual s hc, rfl, floatFrame_writeFP s 4 (by decide) _⟩

theorem step_float_correction (s : Machine) (hc : supportedControls s.fpcr = true) :
    step 0x1f030880 s = some (({s with pc := s.pc + 4} : Machine).writeFP 0 (mulAdd32 (s.fpcr &&& 0x02000000 != 0) (s.readS 4) (s.readS 3) (s.readS 2))) := by
  unfold step
  rw [hc]
  cbv
  simp only [xor_zero32]

theorem progress_float_correction (s : Machine) (hc : supportedControls s.fpcr = true) :
    ∃ t, step 0x1f030880 s = some t ∧ t.pc = s.pc + 4 ∧ FloatFrame s t := by
  refine ⟨_, step_float_correction s hc, rfl, floatFrame_writeFP s 0 (by decide) _⟩

end VerifiedSqrt.Arm
