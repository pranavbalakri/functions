module

public import VerifiedSqrt.Arm.InputInstructions64
public import VerifiedSqrt.Arm.Execution64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem return64_one (s : Machine) (hc : supportedControls s.fpcr = true)
    (ha : s.pc.toNat % 4 = 0) (hf : sqrt64Code[s.pc.toNat / 4]? = some 0xd65f03c0)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    run64 sqrt64Code 0 (s.readX 30) 1 s = some {s with pc := s.readX 30} := by
  have hne : s.pc ≠ s.readX 30 := by
    intro h
    rw [h, hstop] at hf
    contradiction
  rw [run64_step _ _ _ 0 _ _ 0xd65f03c0 hne ha (by simpa only [UInt64.sub_zero] using hf) (step64_return s hc)]
  exact run64_at_stop _ _ _ _ _ rfl

theorem special_body64_correct (s : Machine) (hpc : s.pc = 300)
    (hc : supportedControls s.fpcr = true) (hs : s.v.size = 32)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code 0 (s.readX 30) 2 s = some t ∧ t.pc = s.readX 30 ∧
      t.readD 0 = (rsqrtEstimate64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0)).bits ∧
      t.fpcr = s.fpcr ∧ (∀ r, t.readX r = s.readX r) ∧
      (∀ r, r ≠ 0 → t.v[r]! = s.v[r]!) := by
  let u := s.advanceFP64 0 (rsqrtEstimate64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0))
  have hp : u.pc = 304 := by
    dsimp only [u]
    rw [Machine.advanceFP64_pc, hpc]
    decide +kernel
  have hcu : supportedControls u.fpcr = true := hc
  have hlink : u.readX 30 = s.readX 30 := by
    dsimp only [u]
    rw [Machine.readX_advanceFP64]
  have hr := return64_one u hcu (by rw [hp]; decide +kernel)
    (by rw [hp]; decide +kernel) (by rw [hlink]; exact hstop)
  rw [hlink] at hr
  have hf : sqrt64Code[s.pc.toNat / 4]? = some 0x7ee1d800 := by rw [hpc]; decide +kernel
  have hne : s.pc ≠ s.readX 30 := by
    intro h
    rw [h, hstop] at hf
    contradiction
  refine ⟨{u with pc := s.readX 30}, ?_, rfl, ?_, rfl, ?_, ?_⟩
  · rw [run64_step _ _ _ 1 _ u 0x7ee1d800 hne (by rw [hpc]; decide +kernel)
      (by simpa only [UInt64.sub_zero] using hf) (step64_special_estimate s hc)]
    exact hr
  · exact Machine.readD_advanceFP64_same s 0 (by decide) hs
      (rsqrtEstimate64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0))
  · intro r
    exact Machine.readX_advanceFP64 s 0 r
      (rsqrtEstimate64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0))
  · intro r hr
    exact Machine.vector_advanceFP64_ne s 0 r (Ne.symm hr)
      (rsqrtEstimate64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0))

end VerifiedSqrt.Arm
