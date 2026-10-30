module

public import VerifiedSqrt.Arm.InputInstructions
public import VerifiedSqrt.Arm.Execution

@[expose] public section

namespace VerifiedSqrt.Arm

theorem return_one (s : Machine) (hc : supportedControls s.fpcr = true)
    (ha : s.pc.toNat % 4 = 0) (hf : sqrt32Code[s.pc.toNat / 4]? = some 0xd65f03c0)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    run sqrt32Code (s.readX 30) 1 s = some {s with pc := s.readX 30} := by
  have hne : s.pc ≠ s.readX 30 := by
    intro h
    rw [h, hstop] at hf
    contradiction
  rw [run_step _ _ 0 _ _ 0xd65f03c0 hne ha hf (step_return s hc)]
  exact run_at_stop _ _ _ _ rfl

theorem special_body_correct (s : Machine) (hpc : s.pc = 244)
    (hc : supportedControls s.fpcr = true) (hs : s.v.size = 32)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) 2 s = some t ∧ t.pc = s.readX 30 ∧
      t.readS 0 = (rsqrtEstimate32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0)).bits ∧
      t.fpcr = s.fpcr ∧ (∀ r, t.readX r = s.readX r) ∧
      (∀ r, r ≠ 0 → t.v[r]! = s.v[r]!) := by
  let u := s.advanceFP 0 (rsqrtEstimate32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0))
  have hp : u.pc = 248 := by
    dsimp only [u]
    rw [Machine.advanceFP_pc, hpc]
    decide +kernel
  have hcu : supportedControls u.fpcr = true := hc
  have hlink : u.readX 30 = s.readX 30 := by
    dsimp only [u]
    rw [Machine.readX_advanceFP]
  have hr := return_one u hcu (by rw [hp]; decide +kernel)
    (by rw [hp]; decide +kernel) (by rw [hlink]; exact hstop)
  rw [hlink] at hr
  have hf : sqrt32Code[s.pc.toNat / 4]? = some 0x7ea1d800 := by rw [hpc]; decide +kernel
  have hne : s.pc ≠ s.readX 30 := by
    intro h
    rw [h, hstop] at hf
    contradiction
  refine ⟨{u with pc := s.readX 30}, ?_, rfl, ?_, rfl, ?_, ?_⟩
  · rw [run_step _ _ 1 _ u 0x7ea1d800 hne (by rw [hpc]; decide +kernel)
      hf (step_special_estimate s hc)]
    exact hr
  · exact Machine.readS_advanceFP_same s 0 (by decide) hs
      (rsqrtEstimate32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0))
  · intro r
    exact Machine.readX_advanceFP s 0 r
      (rsqrtEstimate32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0))
  · intro r hr
    exact Machine.vector_advanceFP_ne s 0 r (Ne.symm hr)
      (rsqrtEstimate32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0))

end VerifiedSqrt.Arm
