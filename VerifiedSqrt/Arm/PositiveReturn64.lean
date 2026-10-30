module

public import VerifiedSqrt.Arm.Prepare64
public import VerifiedSqrt.Arm.NormalizeReturn64
public import VerifiedSqrt.Sqrt.Correctness64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem positive_normal64_return (s : Machine) (dn : Bool)
    (lo : 0 < (s.readX 0).toNat) (hi : (s.readX 0).toNat < 0x7ff0000000000000)
    (he : 0 < exponent64 (s.readX 0)) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code 0 (s.readX 30) (20 * 2 ^ 52 + 67) s = some t ∧
      t.pc = s.readX 30 ∧ t.readD 0 = Sqrt.algorithm64 dn (s.readX 0) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 7 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨hf, _, hxs, hv, hregs⟩ := prepared64_properties s 68
  have hsu : (prepared64 s 68).WellFormed := ⟨hxs.trans hs.1, by rw [hv]; exact hs.2⟩
  have hcu : supportedControls (prepared64 s 68).fpcr = true := by rw [hf]; exact hc
  have hw := prepared64_word s 68
  have hlink := hregs 30 (by decide) (by decide)
  have hcl := positive_finite64_classify (s.readX 0) lo hi
  have hk := Sqrt.rootExponent64_bounds (s.readX 0) he hcl.2.2.2.2.2
  obtain ⟨t, ht, hp, hvalue, hft, hrt, hvt⟩ := normalization64_return_correct (prepared64 s 68) 0
    (by rw [hw]; omega) (by rw [hw]; omega) rfl hcu hsu
    (prepared64_exponent s 68 hs.1) (prepared64_scale s 68 hs.1)
    (by rw [hlink]; exact hstop)
  rw [hlink] at ht hp
  rw [hw, Int.zero_add] at hvalue
  have hrun := run64_compose sqrt64Code 0 68 (s.readX 30) 3 (20 * 2 ^ 52 + 58)
    s (prepared64 s 68) t (by simpa only [UInt64.sub_zero] using hstop) (prepare64_normal_run s hpc hc hs.1 (by omega)) ht
  refine ⟨t, run64_add_fuel _ _ _ _ 6 _ _ hrun, hp, ?_, hft.trans hf, ?_, ?_⟩
  · rw [Sqrt.algorithm64_normal dn (s.readX 0) lo hi he]
    exact hvalue
  · intro r hr hr'
    exact (hrt r hr hr').trans (hregs r (by omega) hr')
  · intro r hr
    exact (hvt r hr).trans (congrArg (fun v => v[r]!) hv)

theorem positive_subnormal64_return (s : Machine) (dn : Bool)
    (lo : 0 < (s.readX 0).toNat) (hi : (s.readX 0).toNat < 2 ^ 52)
    (hinput : s.readX 0 = s.readD 0) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code 0 (s.readX 30) (20 * 2 ^ 52 + 67) s = some t ∧
      t.pc = s.readX 30 ∧ t.readD 0 = Sqrt.algorithm64 dn (s.readX 0) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 7 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨hfp, _, hxp, hvp, hrp⟩ := prepared64_properties s 44
  have hsp : (prepared64 s 44).WellFormed := ⟨hxp.trans hs.1, by rw [hvp]; exact hs.2⟩
  obtain ⟨hfu, hxu, hvu, hru, hvectors⟩ := scale64_properties (prepared64 s 44)
  have hsu : (scale64_6 (prepared64 s 44)).WellFormed := ⟨hxu.trans hsp.1, hvu.trans hsp.2⟩
  have hcu : supportedControls (scale64_6 (prepared64 s 44)).fpcr = true := by
    rw [hfu, hfp]; exact hc
  have hw : (scale64_6 (prepared64 s 44)).readX 0 = Sqrt.scaleSubnormal64 (s.readX 0) := by
    rw [scale64_word_subnormal (prepared64 s 44) hsp
      (by rw [prepared64_scalar, ← hinput]; exact lo)
      (by rw [prepared64_scalar, ← hinput]; exact hi), prepared64_scalar, ← hinput]
  have hlink := (hru 30 (by decide) (by decide)).trans (hrp 30 (by decide) (by decide))
  have hscaled := Sqrt.scaleSubnormal64_properties (s.readX 0) lo hi
  have hk := Sqrt.rootExponent64_bounds (Sqrt.scaleSubnormal64 (s.readX 0))
    (by omega) (by omega)
  obtain ⟨t, ht, hp, hvalue, hft, hrt, hvt⟩ :=
    normalization64_return_correct (scale64_6 (prepared64 s 44)) (-53)
      (by rw [hw]; omega) (by rw [hw]; omega) (scale64_pc _ rfl) hcu hsu
      (scale64_exponent _ hsp.1) (scale64_saved_exponent _ hsp.1)
      (by rw [hlink]; exact hstop)
  rw [hlink] at ht hp
  rw [hw] at hvalue
  have he : exponent64 (s.readX 0) = 0 := by rw [exponent64_eq_div]; omega
  refine ⟨t, ?_, hp, ?_, hft.trans (hfu.trans hfp), ?_, ?_⟩
  · exact run64_compose sqrt64Code 0 68 (s.readX 30) 9 (20 * 2 ^ 52 + 58)
      s (scale64_6 (prepared64 s 44)) t (by simpa only [UInt64.sub_zero] using hstop) (prepare64_subnormal_run s hpc hc hs.1 he) ht
  · rw [Sqrt.algorithm64_subnormal dn (s.readX 0) lo hi]
    simpa only [Int.sub_eq_add_neg, Int.add_comm (-53)] using hvalue
  · intro r hr hr'
    exact (hrt r hr hr').trans ((hru r (by omega) hr').trans (hrp r (by omega) hr'))
  · intro r hr
    exact (hvt r hr).trans ((hvectors r (by omega)).trans (congrArg (fun v => v[r]!) hvp))

theorem positive_body64_correct (s : Machine) (dn : Bool)
    (lo : 0 < (s.readX 0).toNat) (hi : (s.readX 0).toNat < 0x7ff0000000000000)
    (hinput : s.readX 0 = s.readD 0) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code 0 (s.readX 30) (20 * 2 ^ 52 + 67) s = some t ∧
      t.pc = s.readX 30 ∧ t.readD 0 = Sqrt.algorithm64 dn (s.readX 0) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 7 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  by_cases he : exponent64 (s.readX 0) = 0
  · have hsmall : (s.readX 0).toNat < 2 ^ 52 := by rw [exponent64_eq_div] at he; omega
    exact positive_subnormal64_return s dn lo hsmall hinput hpc hc hs hstop
  · exact positive_normal64_return s dn lo hi (by omega) hpc hc hs hstop

end VerifiedSqrt.Arm
