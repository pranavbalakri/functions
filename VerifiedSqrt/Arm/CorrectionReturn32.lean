module

public import VerifiedSqrt.Arm.CorrectionTermination
public import VerifiedSqrt.Arm.Return32

@[expose] public section

namespace VerifiedSqrt.Arm

theorem correction_return_correct (x : UInt32) (k : Int)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000)
    (klo : -125 ≤ k) (khi : k ≤ 126) (s : Machine)
    (hpc : s.pc = 184) (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hn : (s.readX 3).toNat = 4 * Sqrt.normalizedRadicand32 x)
    (qlo : 2 ^ 23 ≤ (s.readW 0).toNat) (qhi : (s.readW 0).toNat ≤ 2 ^ 24)
    (hk : s.readW 4 = UInt32.ofInt k)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (12 * 2 ^ 23 + 15) s = some t ∧
      t.pc = s.readX 30 ∧ t.readS 0 = Sqrt.rescale32 (Sqrt.core32 x) k ∧
      t.fpcr = s.fpcr ∧ t.fpsr = s.fpsr ∧
      (∀ r, r < 31 → r ≠ 0 → r ≠ 1 → r ≠ 2 → t.readX r = s.readX r) ∧
      (∀ r, r ≠ 0 → t.v[r]! = s.v[r]!) := by
  obtain ⟨u, hu, hpcu, hqu, hframe⟩ :=
    normalized_correction_loop_correct x lo hi s hpc hc hs.1 hn qlo qhi
  have hsu : u.WellFormed := ⟨hframe.size.trans hs.1, by rw [hframe.vectors]; exact hs.2⟩
  have hcu : supportedControls u.fpcr = true := by rw [hframe.fpcr]; exact hc
  have hku : u.readW 4 = UInt32.ofInt k :=
    (congrArg UInt64.toUInt32 (hframe.registers 4 (by decide) (by decide) (by decide))).trans hk
  have hlu : u.readX 30 = s.readX 30 := hframe.registers 30 (by decide) (by decide) (by decide)
  have hstopu : sqrt32Code[(u.readX 30).toNat / 4]? = none := by rw [hlu]; exact hstop
  have hret := return_run u hpcu hcu hstopu
  rw [hlu] at hret
  refine ⟨returnedState u, ?_, (return_link u).trans hlu,
    return_correct x k lo hi klo khi u hsu hqu hku, hframe.fpcr, hframe.fpsr, ?_, ?_⟩
  · exact run_compose sqrt32Code 224 (s.readX 30) (12 * 2 ^ 23 + 10) 5
      s u (returnedState u) hstop hu hret
  · intro r hr h0 h1 h2
    exact (return_other_register u r hr h0 h1).trans (hframe.registers r hr h0 h2)
  · intro r hr
    rw [return_other_vector u r hr, hframe.vectors]

end VerifiedSqrt.Arm
