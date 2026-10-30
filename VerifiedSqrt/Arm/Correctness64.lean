module

public import VerifiedSqrt.Arm.Contract64
public import VerifiedSqrt.Arm.PositiveReturn64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem machine_algorithm64 (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code 0 (s.readX 30) (20 * 2 ^ 52 + 75) s = some t ∧ SqrtContract64 s t := by
  by_cases hz : isZero64 (s.readD 0) = true
  · obtain ⟨t, ht, hf⟩ := input_return64_correct s {input64_2 s with pc := 296} 3 hc
      ((input64_2_state s hs.1).withPC 296) rfl (input64_zero_run s hpc hc hs.1 hz)
      (Sqrt.algorithm64_zero _ _ hz) hstop
    exact ⟨t, run64_of_le_fuel _ _ _ _ _ _ _ (by decide) ht, hf⟩
  have hz : isZero64 (s.readD 0) = false := Bool.eq_false_iff.mpr hz
  by_cases hinf : s.readD 0 = 0x7ff0000000000000
  · obtain ⟨t, ht, hf⟩ := input_return64_correct s {input64_6 s with pc := 296} 7 hc
      ((input64_6_state s hs.1).withPC 296) rfl (input64_infinity_run s hpc hc hs.1 hinf)
      (by rw [hinf]; exact Sqrt.algorithm64_infinity _) hstop
    exact ⟨t, run64_of_le_fuel _ _ _ _ _ _ _ (by decide) ht, hf⟩
  by_cases hn : sign64 (s.readD 0) = true
  · have hvalue : Sqrt.algorithm64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0) =
        (rsqrtEstimate64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0)).bits := by
      simp [Sqrt.algorithm64, hz, hinf, hn]
    obtain ⟨t, ht, hf⟩ := input_special64_correct s {input64_2 s with pc := 300} 4 hc hs
      ((input64_2_state s hs.1).withPC 300) rfl (input64_negative_run s hpc hc hs.1 hz hn)
      hvalue hstop
    exact ⟨t, run64_of_le_fuel _ _ _ _ _ _ _ (by decide) ht, hf⟩
  have hn : sign64 (s.readD 0) = false := Bool.eq_false_iff.mpr hn
  by_cases hsmall : (s.readD 0).toNat < 0x7ff0000000000000
  · have hlo : 0 < (s.readD 0).toNat := by
      have hb := (sign64_false_iff (s.readD 0)).mp hn
      have hz' : (s.readD 0).toNat % 2 ^ 63 ≠ 0 := by
        intro h
        have hc := (isZero64_iff (s.readD 0)).mpr h
        simp [hz] at hc
      omega
    have hless : ¬s.readD 0 ≥ 0x7ff0000000000000 := by
      intro h
      have h := UInt64.le_iff_toNat_le.mp h
      change 0x7ff0000000000000 ≤ (s.readD 0).toNat at h
      omega
    have hprefix := input64_unequal_run s 32 (by decide) hpc hc hs.1 hz hn hinf
      (by rw [ite_eq_right hless])
    have hf := (input64_6_state s hs.1).withPC 32
    have hcu : supportedControls ({input64_6 s with pc := 32} : Machine).fpcr = true := by
      rw [hf.fpcr]; exact hc
    have hlink := hf.registers 30 (by decide) (by decide)
    obtain ⟨t, ht, hp, hvalue, hft, hregs, hvec⟩ := positive_body64_correct
      {input64_6 s with pc := 32} (s.fpcr &&& 0x02000000 != 0)
      (by rw [hf.input]; exact hlo) (by rw [hf.input]; exact hsmall)
      (hf.input.trans hf.scalar.symm) rfl hcu (hf.wellFormed hs)
      (by rw [hlink]; exact hstop)
    rw [hlink] at ht hp
    rw [hf.input] at hvalue
    refine ⟨t, run64_compose sqrt64Code 0 32 (s.readX 30) 8 (20 * 2 ^ 52 + 67)
      s {input64_6 s with pc := 32} t (by simpa only [UInt64.sub_zero] using hstop) hprefix ht,
      ⟨hp, hvalue, hft.trans hf.fpcr, ?_, ?_⟩⟩
    · intro r hr hr'
      exact (hregs r hr hr').trans (hf.registers r (by omega) hr')
    · intro r hr
      exact (hvec r hr).trans (congrArg (fun v => v[r]!) hf.vectors)
  · have hge : s.readD 0 ≥ 0x7ff0000000000000 := by
      apply UInt64.le_iff_toNat_le.mpr
      change 0x7ff0000000000000 ≤ (s.readD 0).toNat
      omega
    have hne : (s.readD 0).toNat ≠ 0x7ff0000000000000 := by
      intro h
      exact hinf (UInt64.toNat_inj.mp h)
    have hnan : isNaN64 (s.readD 0) = true := by
      apply (isNaN64_iff (s.readD 0)).mpr
      have hb := (sign64_false_iff (s.readD 0)).mp hn
      omega
    have hvalue : Sqrt.algorithm64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0) =
        (rsqrtEstimate64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0)).bits := by
      simp [Sqrt.algorithm64, hz, hinf, hn, hnan]
    have hprefix := input64_unequal_run s 300 (by decide) hpc hc hs.1 hz hn hinf
      (by rw [ite_eq_left hge])
    obtain ⟨t, ht, hf⟩ := input_special64_correct s {input64_6 s with pc := 300} 8 hc hs
      ((input64_6_state s hs.1).withPC 300) rfl hprefix hvalue hstop
    exact ⟨t, run64_of_le_fuel _ _ _ _ _ _ _ (by decide) ht, hf⟩

theorem machine_sqrt64_correct (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code 0 (s.readX 30) (20 * 2 ^ 52 + 75) s = some t ∧
      t.pc = s.readX 30 ∧ Sqrt.SqrtSpec64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0) (t.readD 0) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 7 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨t, ht, hf⟩ := machine_algorithm64 s hpc hc hs hstop
  refine ⟨t, ht, hf.pc, ?_, hf.fpcr, hf.registers, hf.vectors⟩
  rw [hf.value]
  exact Sqrt.algorithm64_correct _ _

end VerifiedSqrt.Arm
