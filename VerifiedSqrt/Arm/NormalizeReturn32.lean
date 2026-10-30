module

public import VerifiedSqrt.Arm.Normalize32
public import VerifiedSqrt.Arm.NormalizedBody32

@[expose] public section

namespace VerifiedSqrt.Arm

theorem normalization_return_correct (s : Machine) (k : Int)
    (klo : -125 ≤ k + Sqrt.rootExponent32 (s.readW 0))
    (khi : k + Sqrt.rootExponent32 (s.readW 0) ≤ 126)
    (hpc : s.pc = 68) (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (he : s.readW 1 = UInt32.ofNat (exponent32 (s.readW 0)))
    (hk : s.readW 4 = UInt32.ofInt k)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (12 * 2 ^ 23 + 44) s = some t ∧
      t.pc = s.readX 30 ∧
      t.readS 0 = Sqrt.rescale32 (Sqrt.core32 (Sqrt.normalizedInput32 (s.readW 0)))
        (k + Sqrt.rootExponent32 (s.readW 0)) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 5 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨hfc, _, hxs, hvs, hregs, hvec⟩ := normalize_properties s
  have hsu : (normalize8 s).WellFormed := ⟨hxs.trans hs.1, hvs.trans hs.2⟩
  have hcu : supportedControls (normalize8 s).fpcr = true := by rw [hfc]; exact hc
  have hw := normalize_word s hs.1 he
  have hb := Sqrt.normalizedInput32_bounds (s.readW 0)
  have hlink := hregs 30 (by decide) (by decide)
  obtain ⟨t, ht, hpt, hvalue, hft, hrt, hvt⟩ :=
    normalized_body_correct (normalize8 s) (k + Sqrt.rootExponent32 (s.readW 0))
      (by rw [hw]; exact hb.1) (by rw [hw]; exact hb.2) klo khi
      (normalize_pc s hpc) hcu hsu (normalize_exponent s hs.1 k he hk)
      (by rw [hlink]; exact hstop)
  rw [hlink] at ht hpt
  rw [hw] at hvalue
  refine ⟨t, ?_, hpt, hvalue, hft.trans hfc, ?_, ?_⟩
  · exact run_compose sqrt32Code 100 (s.readX 30) 8 (12 * 2 ^ 23 + 36)
      s (normalize8 s) t hstop (normalize_run s hpc hc) ht
  · intro r hr hr'
    exact (hrt r (by omega) hr').trans (hregs r hr hr')
  · intro r hr
    exact (hvt r hr).trans (hvec r (by omega))

end VerifiedSqrt.Arm
