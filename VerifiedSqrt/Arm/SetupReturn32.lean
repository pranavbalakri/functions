module

public import VerifiedSqrt.Arm.Setup32
public import VerifiedSqrt.Arm.CorrectionReturn32

@[expose] public section

namespace VerifiedSqrt.Arm

theorem setup_return_correct (s : Machine) (k : Int)
    (lo : 0x3f800000 ≤ (s.readW 0).toNat) (hi : (s.readW 0).toNat < 0x40800000)
    (klo : -125 ≤ k) (khi : k ≤ 126) (hpc : s.pc = 148)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hk : s.readW 4 = UInt32.ofInt k)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (12 * 2 ^ 23 + 24) s = some t ∧
      t.pc = s.readX 30 ∧ t.readS 0 = Sqrt.rescale32 (Sqrt.core32 (s.readW 0)) k ∧
      t.fpcr = s.fpcr ∧ t.fpsr = s.fpsr ∧
      (∀ r, 4 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, r ≠ 0 → t.v[r]! = s.v[r]!) := by
  let u := setup9 s
  have hp := setup_properties s
  have hsu : u.WellFormed := ⟨hp.2.2.2.1.trans hs.1, by change (setup9 s).v.size = 32; rw [hp.2.2.1]; exact hs.2⟩
  have hcu : supportedControls u.fpcr = true := by change supportedControls (setup9 s).fpcr = true; rw [hp.1]; exact hc
  have hlu : u.readX 30 = s.readX 30 := hp.2.2.2.2 30 (by decide) (by decide)
  have hku : u.readW 4 = UInt32.ofInt k :=
    (congrArg UInt64.toUInt32 (hp.2.2.2.2 4 (by decide) (by decide))).trans hk
  have hpcu : u.pc = 184 := by
    dsimp [u, setup9, setup8, setup7, setup6, setup5, setup4, setup3, setup2, setup1]
    simp only [Machine.advanceW_pc, Machine.advanceX_pc, hpc]
    decide +kernel
  have hbounds := setup_seed_bounds s hs.1
  obtain ⟨t, ht, hpt, hvalue, hfc, hfs, hregs, hvec⟩ :=
    correction_return_correct (s.readW 0) k lo hi klo khi u hpcu hcu hsu
      (setup_radicand_value s hs.1 lo hi) hbounds.1 hbounds.2 hku (by rw [hlu]; exact hstop)
  rw [hlu] at ht hpt
  refine ⟨t, ?_, hpt, hvalue, hfc.trans hp.1, hfs.trans hp.2.1, ?_, ?_⟩
  · exact run_compose sqrt32Code 184 (s.readX 30) 9 (12 * 2 ^ 23 + 15)
      s u t hstop (setup_run s hpc hc) ht
  · intro r hr hr'
    exact (hregs r hr' (by omega) (by omega) (by omega)).trans (hp.2.2.2.2 r hr hr')
  · intro r hr
    rw [hvec r hr]
    change (setup9 s).v[r]! = _
    rw [hp.2.2.1]

end VerifiedSqrt.Arm
