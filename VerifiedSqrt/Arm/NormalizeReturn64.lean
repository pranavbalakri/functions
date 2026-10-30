module

public import VerifiedSqrt.Arm.Normalize64
public import VerifiedSqrt.Arm.NormalizedBody64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem normalization64_return_correct (s : Machine) (e : Int)
    (lo : -1021 ≤ e + Sqrt.rootExponent64 (s.readX 0))
    (hi : e + Sqrt.rootExponent64 (s.readX 0) ≤ 1022)
    (hpc : s.pc = 68) (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (he : s.readW 1 = UInt32.ofNat (exponent64 (s.readX 0)))
    (hk : s.readW 4 = UInt32.ofInt e)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code 0 (s.readX 30) (20 * 2 ^ 52 + 58) s = some t ∧
      t.pc = s.readX 30 ∧
      t.readD 0 = Sqrt.rescale64 (Sqrt.core64 (Sqrt.normalizedInput64 (s.readX 0)))
        (e + Sqrt.rootExponent64 (s.readX 0)) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 7 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨hfc, _, hxs, hvs, hregs, hvec⟩ := normalize64_properties s
  have hsu : (normalize64_8 s).WellFormed := ⟨hxs.trans hs.1, hvs.trans hs.2⟩
  have hcu : supportedControls (normalize64_8 s).fpcr = true := by rw [hfc]; exact hc
  have hw := normalize64_word s hs.1 he
  have hb := Sqrt.normalizedInput64_bounds (s.readX 0)
  have hlink := hregs 30 (by decide) (by decide)
  obtain ⟨n, t, hn, ht, hpt, hvalue, hft, hrt, hvt⟩ :=
    normalized_body64_correct (normalize64_8 s) (e + Sqrt.rootExponent64 (s.readX 0))
      (by rw [hw]; exact hb.1) (by rw [hw]; exact hb.2) lo hi
      (normalize64_pc s hpc) hcu hsu (normalize64_exponent s hs.1 e he hk)
  rw [hlink] at hpt
  rw [hw] at hvalue
  have hrun := ((normalize64_trace s hpc hc).trans ht).run hpt
    (by simpa only [UInt64.sub_zero] using hstop)
  refine ⟨t, run64_of_le_fuel _ _ _ _ _ _ _ (by omega) hrun,
    hpt, hvalue, hft.trans hfc, ?_, ?_⟩
  · intro r hr hr'
    exact (hrt r hr hr').trans (hregs r (by omega) hr')
  · intro r hr
    exact (hvt r hr).trans (hvec r (by omega))

end VerifiedSqrt.Arm
