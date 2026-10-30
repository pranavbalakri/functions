module

public import VerifiedSqrt.Arm.Estimate32
public import VerifiedSqrt.Arm.SetupReturn32
public import VerifiedSqrt.Sqrt.Correctness32

@[expose] public section

namespace VerifiedSqrt.Arm

theorem normalized_body_correct (s : Machine) (k : Int)
    (lo : 0x3f800000 ≤ (s.readW 0).toNat) (hi : (s.readW 0).toNat < 0x40800000)
    (klo : -125 ≤ k) (khi : k ≤ 126) (hpc : s.pc = 100)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hk : s.readW 4 = UInt32.ofInt k)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (12 * 2 ^ 23 + 36) s = some t ∧
      t.pc = s.readX 30 ∧ t.readS 0 = Sqrt.rescale32 (Sqrt.core32 (s.readW 0)) k ∧
      t.fpcr = s.fpcr ∧ (∀ r, 4 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨u, hu, hpcu, hf⟩ := estimate_run s hpc hc
  have hsu : u.WellFormed := ⟨by rw [hf.registers]; exact hs.1, hf.size.trans hs.2⟩
  have hcu : supportedControls u.fpcr = true := by rw [hf.fpcr]; exact hc
  have hw0 := Machine.readW_congr u s hf.registers 0
  have hw4 := Machine.readW_congr u s hf.registers 4
  have hlink := Machine.readX_congr u s hf.registers 30
  obtain ⟨t, ht, hpt, hvalue, hfc, _, hregs, hvec⟩ :=
    setup_return_correct u k (by rw [hw0]; exact lo) (by rw [hw0]; exact hi)
      klo khi hpcu hcu hsu (hw4.trans hk) (by rw [hlink]; exact hstop)
  rw [hlink] at ht hpt
  rw [hw0] at hvalue
  refine ⟨t, ?_, hpt, hvalue, hfc.trans hf.fpcr, ?_, ?_⟩
  · exact run_compose sqrt32Code 148 (s.readX 30) 12 (12 * 2 ^ 23 + 24)
      s u t hstop hu ht
  · intro r hr hr'
    exact (hregs r hr hr').trans (Machine.readX_congr u s hf.registers r)
  · intro r hr
    exact (hvec r (by omega)).trans (hf.vectors r hr)

theorem normalized_body_rounds (s : Machine) (k : Int)
    (lo : 0x3f800000 ≤ (s.readW 0).toNat) (hi : (s.readW 0).toNat < 0x40800000)
    (klo : -125 ≤ k) (khi : k ≤ 126) (hpc : s.pc = 100)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hk : s.readW 4 = UInt32.ofInt k)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (12 * 2 ^ 23 + 36) s = some t ∧
      t.pc = s.readX 30 ∧
      RoundsToNearestEven32 (Real.sqrt (unpack32 (s.readW 0)).toReal * (2 : ℝ) ^ k) (t.readS 0) := by
  obtain ⟨t, ht, hpt, hvalue, _⟩ := normalized_body_correct s k lo hi klo khi hpc hc hs hk hstop
  refine ⟨t, ht, hpt, ?_⟩
  rw [hvalue]
  have hb := Sqrt.correctedCore32_bounds (s.readW 0) lo hi
  have hr := Sqrt.rescale32_bounds _ k hb.1 hb.2 klo khi
  have hf := positive_finite32_classify _ hr.1 hr.2
  apply roundsToNearestEven32_of_strict _ _ hf.2.2.2.2.2
  exact Sqrt.scaledCore32_strict_nearest (s.readW 0) k lo hi klo khi

end VerifiedSqrt.Arm
