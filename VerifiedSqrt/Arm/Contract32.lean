module

public import VerifiedSqrt.Arm.Classify32
public import VerifiedSqrt.Arm.SpecialReturn32
public import VerifiedSqrt.Sqrt.Correctness32

@[expose] public section

namespace VerifiedSqrt.Arm

structure SqrtContract32 (s t : Machine) : Prop where
  pc : t.pc = s.readX 30
  value : t.readS 0 = Sqrt.algorithm32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0)
  fpcr : t.fpcr = s.fpcr
  registers : ∀ r, 5 ≤ r → r < 31 → t.readX r = s.readX r
  vectors : ∀ r, 6 ≤ r → t.v[r]! = s.v[r]!

theorem input_return_correct (s u : Machine) (fuel : Nat)
    (hc : supportedControls s.fpcr = true) (hf : InputState s u) (hp : u.pc = 240)
    (hr : run sqrt32Code 240 fuel s = some u)
    (hvalue : Sqrt.algorithm32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0) = s.readS 0)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (fuel + 1) s = some t ∧ SqrtContract32 s t := by
  have hcu : supportedControls u.fpcr = true := by rw [hf.fpcr]; exact hc
  have hlink := hf.registers 30 (by decide) (by decide)
  have ht := return_one u hcu (by rw [hp]; decide +kernel)
    (by rw [hp]; decide +kernel) (by rw [hlink]; exact hstop)
  rw [hlink] at ht
  refine ⟨{u with pc := s.readX 30}, run_compose _ _ _ _ _ _ _ _ hstop hr ht,
    ⟨rfl, hf.scalar.trans hvalue.symm, hf.fpcr, ?_, ?_⟩⟩
  · intro r hr hr'
    exact hf.registers r (by omega) hr'
  · intro r _
    exact congrArg (fun v => v[r]!) hf.vectors

theorem input_special_correct (s u : Machine) (fuel : Nat)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hf : InputState s u) (hp : u.pc = 244) (hr : run sqrt32Code 244 fuel s = some u)
    (hvalue : Sqrt.algorithm32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0) =
      (rsqrtEstimate32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0)).bits)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (fuel + 2) s = some t ∧ SqrtContract32 s t := by
  have hcu : supportedControls u.fpcr = true := by rw [hf.fpcr]; exact hc
  have hlink := hf.registers 30 (by decide) (by decide)
  obtain ⟨t, ht, hpt, hvt, hft, hregs, hvec⟩ := special_body_correct u hp hcu
    (hf.wellFormed hs).2 (by rw [hlink]; exact hstop)
  rw [hlink] at ht hpt
  rw [hf.fpcr, hf.scalar] at hvt
  refine ⟨t, run_compose _ _ _ _ _ _ _ _ hstop hr ht,
    ⟨hpt, hvt.trans hvalue.symm, hft.trans hf.fpcr, ?_, ?_⟩⟩
  · intro r hr hr'
    exact (hregs r).trans (hf.registers r (by omega) hr')
  · intro r hr
    exact (hvec r (by omega)).trans (congrArg (fun v => v[r]!) hf.vectors)

end VerifiedSqrt.Arm
