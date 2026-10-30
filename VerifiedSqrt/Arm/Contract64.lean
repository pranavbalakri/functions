module

public import VerifiedSqrt.Arm.Classify64
public import VerifiedSqrt.Arm.SpecialReturn64
public import VerifiedSqrt.Sqrt.Correctness64

@[expose] public section

namespace VerifiedSqrt.Arm

structure SqrtContract64 (s t : Machine) : Prop where
  pc : t.pc = s.readX 30
  value : t.readD 0 = Sqrt.algorithm64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0)
  fpcr : t.fpcr = s.fpcr
  registers : ∀ r, 7 ≤ r → r < 31 → t.readX r = s.readX r
  vectors : ∀ r, 6 ≤ r → t.v[r]! = s.v[r]!

theorem input_return64_correct (s u : Machine) (fuel : Nat)
    (hc : supportedControls s.fpcr = true) (hf : InputState64 s u) (hp : u.pc = 296)
    (hr : run64 sqrt64Code 0 296 fuel s = some u)
    (hvalue : Sqrt.algorithm64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0) = s.readD 0)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code 0 (s.readX 30) (fuel + 1) s = some t ∧ SqrtContract64 s t := by
  have hcu : supportedControls u.fpcr = true := by rw [hf.fpcr]; exact hc
  have hlink := hf.registers 30 (by decide) (by decide)
  have ht := return64_one u hcu (by rw [hp]; decide +kernel)
    (by rw [hp]; decide +kernel) (by rw [hlink]; exact hstop)
  rw [hlink] at ht
  refine ⟨{u with pc := s.readX 30}, run64_compose _ _ _ _ _ _ _ _ _ (by simpa only [UInt64.sub_zero] using hstop) hr ht,
    ⟨rfl, hf.scalar.trans hvalue.symm, hf.fpcr, ?_, ?_⟩⟩
  · intro r hr hr'
    exact hf.registers r (by omega) hr'
  · intro r _
    exact congrArg (fun v => v[r]!) hf.vectors

theorem input_special64_correct (s u : Machine) (fuel : Nat)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hf : InputState64 s u) (hp : u.pc = 300) (hr : run64 sqrt64Code 0 300 fuel s = some u)
    (hvalue : Sqrt.algorithm64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0) =
      (rsqrtEstimate64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0)).bits)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code 0 (s.readX 30) (fuel + 2) s = some t ∧ SqrtContract64 s t := by
  have hcu : supportedControls u.fpcr = true := by rw [hf.fpcr]; exact hc
  have hlink := hf.registers 30 (by decide) (by decide)
  obtain ⟨t, ht, hpt, hvt, hft, hregs, hvec⟩ := special_body64_correct u hp hcu
    (hf.wellFormed hs).2 (by rw [hlink]; exact hstop)
  rw [hlink] at ht hpt
  rw [hf.fpcr, hf.scalar] at hvt
  refine ⟨t, run64_compose _ _ _ _ _ _ _ _ _ (by simpa only [UInt64.sub_zero] using hstop) hr ht,
    ⟨hpt, hvt.trans hvalue.symm, hft.trans hf.fpcr, ?_, ?_⟩⟩
  · intro r hr hr'
    exact (hregs r).trans (hf.registers r (by omega) hr')
  · intro r hr
    exact (hvec r (by omega)).trans (congrArg (fun v => v[r]!) hf.vectors)

end VerifiedSqrt.Arm
