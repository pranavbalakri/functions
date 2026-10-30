module

public import VerifiedSqrt.Arm.Contract32
public import VerifiedSqrt.Arm.PositiveReturn32

@[expose] public section

namespace VerifiedSqrt.Arm

theorem machine_algorithm32 (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (12 * 2 ^ 23 + 61) s = some t ∧ SqrtContract32 s t := by
  by_cases hz : isZero32 (s.readS 0) = true
  · obtain ⟨t, ht, hf⟩ := input_return_correct s {input2 s with pc := 240} 3 hc
      ((input2_state s hs.1).withPC 240) rfl (input_zero_run s hpc hc hs.1 hz)
      (Sqrt.algorithm32_zero _ _ hz) hstop
    exact ⟨t, run_of_le_fuel _ _ _ _ _ _ (by decide) ht, hf⟩
  have hz : isZero32 (s.readS 0) = false := Bool.eq_false_iff.mpr hz
  by_cases hinf : s.readS 0 = 0x7f800000
  · obtain ⟨t, ht, hf⟩ := input_return_correct s {input6 s with pc := 240} 7 hc
      ((input6_state s hs.1).withPC 240) rfl (input_infinity_run s hpc hc hs.1 hinf)
      (by rw [hinf]; exact Sqrt.algorithm32_infinity _) hstop
    exact ⟨t, run_of_le_fuel _ _ _ _ _ _ (by decide) ht, hf⟩
  by_cases hn : sign32 (s.readS 0) = true
  · have hvalue : Sqrt.algorithm32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0) =
        (rsqrtEstimate32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0)).bits := by
      simp [Sqrt.algorithm32, hz, hinf, hn]
    obtain ⟨t, ht, hf⟩ := input_special_correct s {input2 s with pc := 244} 4 hc hs
      ((input2_state s hs.1).withPC 244) rfl (input_negative_run s hpc hc hs.1 hz hn)
      hvalue hstop
    exact ⟨t, run_of_le_fuel _ _ _ _ _ _ (by decide) ht, hf⟩
  have hn : sign32 (s.readS 0) = false := Bool.eq_false_iff.mpr hn
  by_cases hsmall : (s.readS 0).toNat < 0x7f800000
  · have hlo : 0 < (s.readS 0).toNat := by
      have hb := (sign32_false_iff (s.readS 0)).mp hn
      have hz' : (s.readS 0).toNat % 2 ^ 31 ≠ 0 := by
        intro h
        have hc := (isZero32_iff (s.readS 0)).mpr h
        simp [hz] at hc
      omega
    have hless : ¬s.readS 0 ≥ 0x7f800000 := by
      intro h
      have h := UInt32.le_iff_toNat_le.mp h
      change 0x7f800000 ≤ (s.readS 0).toNat at h
      omega
    have hprefix := input_unequal_run s 32 (by decide) hpc hc hs.1 hz hn hinf
      (by rw [ite_eq_right hless])
    have hf := (input6_state s hs.1).withPC 32
    have hcu : supportedControls ({input6 s with pc := 32} : Machine).fpcr = true := by
      rw [hf.fpcr]; exact hc
    have hlink := hf.registers 30 (by decide) (by decide)
    obtain ⟨t, ht, hp, hvalue, hft, hregs, hvec⟩ := positive_body_correct
      {input6 s with pc := 32} (s.fpcr &&& 0x02000000 != 0)
      (by rw [hf.input]; exact hlo) (by rw [hf.input]; exact hsmall)
      (hf.input.trans hf.scalar.symm) rfl hcu (hf.wellFormed hs)
      (by rw [hlink]; exact hstop)
    rw [hlink] at ht hp
    rw [hf.input] at hvalue
    refine ⟨t, run_compose sqrt32Code 32 (s.readX 30) 8 (12 * 2 ^ 23 + 53)
      s {input6 s with pc := 32} t hstop hprefix ht,
      ⟨hp, hvalue, hft.trans hf.fpcr, ?_, ?_⟩⟩
    · intro r hr hr'
      exact (hregs r hr hr').trans (hf.registers r (by omega) hr')
    · intro r hr
      exact (hvec r hr).trans (congrArg (fun v => v[r]!) hf.vectors)
  · have hge : s.readS 0 ≥ 0x7f800000 := by
      apply UInt32.le_iff_toNat_le.mpr
      change 0x7f800000 ≤ (s.readS 0).toNat
      omega
    have hne : (s.readS 0).toNat ≠ 0x7f800000 := by
      intro h
      exact hinf (UInt32.toNat_inj.mp h)
    have hnan : isNaN32 (s.readS 0) = true := by
      apply (isNaN32_iff (s.readS 0)).mpr
      have hb := (sign32_false_iff (s.readS 0)).mp hn
      omega
    have hvalue : Sqrt.algorithm32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0) =
        (rsqrtEstimate32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0)).bits := by
      simp [Sqrt.algorithm32, hz, hinf, hn, hnan]
    have hprefix := input_unequal_run s 244 (by decide) hpc hc hs.1 hz hn hinf
      (by rw [ite_eq_left hge])
    obtain ⟨t, ht, hf⟩ := input_special_correct s {input6 s with pc := 244} 8 hc hs
      ((input6_state s hs.1).withPC 244) rfl hprefix hvalue hstop
    exact ⟨t, run_of_le_fuel _ _ _ _ _ _ (by decide) ht, hf⟩

theorem machine_sqrt32_correct (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run sqrt32Code (s.readX 30) (12 * 2 ^ 23 + 61) s = some t ∧
      t.pc = s.readX 30 ∧ Sqrt.SqrtSpec32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0) (t.readS 0) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 5 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨t, ht, hf⟩ := machine_algorithm32 s hpc hc hs hstop
  refine ⟨t, ht, hf.pc, ?_, hf.fpcr, hf.registers, hf.vectors⟩
  rw [hf.value]
  exact Sqrt.algorithm32_correct _ _

end VerifiedSqrt.Arm
