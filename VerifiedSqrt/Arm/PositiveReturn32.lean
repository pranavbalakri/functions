module

public import VerifiedSqrt.Arm.Prepare32
public import VerifiedSqrt.Arm.NormalizeReturn32

@[expose] public section

namespace VerifiedSqrt.Arm

theorem positive_normal_return (s : Machine) (dn : Bool)
    (lo : 0 < (s.readW 0).toNat) (hi : (s.readW 0).toNat < 0x7f800000)
    (he : 0 < exponent32 (s.readW 0)) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (12 * 2 ^ 23 + 53) s = some t ∧
      t.pc = s.readX 30 ∧ t.readS 0 = Sqrt.algorithm32 dn (s.readW 0) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 5 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨hf, _, hxs, hv, hregs⟩ := prepared_properties s 68
  have hsu : (prepared s 68).WellFormed := ⟨hxs.trans hs.1, by rw [hv]; exact hs.2⟩
  have hcu : supportedControls (prepared s 68).fpcr = true := by rw [hf]; exact hc
  have hw := prepared_word s 68
  have hlink := hregs 30 (by decide) (by decide)
  have hcl := positive_finite32_classify (s.readW 0) lo hi
  have hk := Sqrt.rootExponent32_bounds (s.readW 0) he hcl.2.2.2.2.2
  obtain ⟨t, ht, hp, hvalue, hft, hrt, hvt⟩ := normalization_return_correct (prepared s 68) 0
    (by rw [hw]; omega) (by rw [hw]; omega) rfl hcu hsu
    (prepared_exponent s 68 hs.1) (prepared_scale s 68 hs.1)
    (by rw [hlink]; exact hstop)
  rw [hlink] at ht hp
  rw [hw, Int.zero_add] at hvalue
  have hrun := run_compose sqrt32Code 68 (s.readX 30) 3 (12 * 2 ^ 23 + 44)
    s (prepared s 68) t hstop (prepare_normal_run s hpc hc hs.1 (by omega)) ht
  refine ⟨t, run_add_fuel _ _ _ 6 _ _ hrun, hp, ?_, hft.trans hf, ?_, ?_⟩
  · rw [Sqrt.algorithm32_normal dn (s.readW 0) lo hi he]
    exact hvalue
  · intro r hr hr'
    exact (hrt r hr hr').trans (hregs r hr hr')
  · intro r hr
    exact (hvt r hr).trans (congrArg (fun v => v[r]!) hv)

theorem positive_subnormal_return (s : Machine) (dn : Bool)
    (lo : 0 < (s.readW 0).toNat) (hi : (s.readW 0).toNat < 2 ^ 23)
    (hinput : s.readW 0 = s.readS 0) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (12 * 2 ^ 23 + 53) s = some t ∧
      t.pc = s.readX 30 ∧ t.readS 0 = Sqrt.algorithm32 dn (s.readW 0) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 5 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨hfp, _, hxp, hvp, hrp⟩ := prepared_properties s 44
  have hsp : (prepared s 44).WellFormed := ⟨hxp.trans hs.1, by rw [hvp]; exact hs.2⟩
  obtain ⟨hfu, hxu, hvu, hru, hvectors⟩ := scale_properties (prepared s 44)
  have hsu : (scale6 (prepared s 44)).WellFormed := ⟨hxu.trans hsp.1, hvu.trans hsp.2⟩
  have hcu : supportedControls (scale6 (prepared s 44)).fpcr = true := by
    rw [hfu, hfp]; exact hc
  have hw : (scale6 (prepared s 44)).readW 0 = Sqrt.scaleSubnormal32 (s.readW 0) := by
    rw [scale_word_subnormal (prepared s 44) hsp
      (by rw [prepared_scalar, ← hinput]; exact lo)
      (by rw [prepared_scalar, ← hinput]; exact hi), prepared_scalar, ← hinput]
  have hlink := (hru 30 (by decide) (by decide)).trans (hrp 30 (by decide) (by decide))
  have hscaled := Sqrt.scaleSubnormal32_properties (s.readW 0) lo hi
  have hk := Sqrt.rootExponent32_bounds (Sqrt.scaleSubnormal32 (s.readW 0))
    (by omega) (by omega)
  obtain ⟨t, ht, hp, hvalue, hft, hrt, hvt⟩ :=
    normalization_return_correct (scale6 (prepared s 44)) (-24)
      (by rw [hw]; omega) (by rw [hw]; omega) (scale_pc _ rfl) hcu hsu
      (scale_exponent _ hsp.1) (scale_saved_exponent _ hsp.1)
      (by rw [hlink]; exact hstop)
  rw [hlink] at ht hp
  rw [hw] at hvalue
  have he : exponent32 (s.readW 0) = 0 := by rw [exponent32_eq_div]; omega
  refine ⟨t, ?_, hp, ?_, hft.trans (hfu.trans hfp), ?_, ?_⟩
  · exact run_compose sqrt32Code 68 (s.readX 30) 9 (12 * 2 ^ 23 + 44)
      s (scale6 (prepared s 44)) t hstop (prepare_subnormal_run s hpc hc hs.1 he) ht
  · rw [Sqrt.algorithm32_subnormal dn (s.readW 0) lo hi]
    simpa only [Int.sub_eq_add_neg, Int.add_comm (-24)] using hvalue
  · intro r hr hr'
    exact (hrt r hr hr').trans ((hru r hr hr').trans (hrp r hr hr'))
  · intro r hr
    exact (hvt r hr).trans ((hvectors r (by omega)).trans (congrArg (fun v => v[r]!) hvp))

theorem positive_body_correct (s : Machine) (dn : Bool)
    (lo : 0 < (s.readW 0).toNat) (hi : (s.readW 0).toNat < 0x7f800000)
    (hinput : s.readW 0 = s.readS 0) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (12 * 2 ^ 23 + 53) s = some t ∧
      t.pc = s.readX 30 ∧ t.readS 0 = Sqrt.algorithm32 dn (s.readW 0) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 5 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  by_cases he : exponent32 (s.readW 0) = 0
  · have hsmall : (s.readW 0).toNat < 2 ^ 23 := by rw [exponent32_eq_div] at he; omega
    exact positive_subnormal_return s dn lo hsmall hinput hpc hc hs hstop
  · exact positive_normal_return s dn lo hi (by omega) hpc hc hs hstop

end VerifiedSqrt.Arm
