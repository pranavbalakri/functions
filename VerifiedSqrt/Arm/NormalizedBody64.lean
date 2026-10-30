module

public import VerifiedSqrt.Arm.Estimate64
public import VerifiedSqrt.Arm.Setup64
public import VerifiedSqrt.Arm.CorrectionTermination64
public import VerifiedSqrt.Arm.Return64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem normalized_body64_correct (s : Machine) (e : Int)
    (lo : 0x3ff0000000000000 ≤ (s.readX 0).toNat)
    (hi : (s.readX 0).toNat < 0x4010000000000000)
    (elo : -1021 ≤ e) (ehi : e ≤ 1022) (hpc : s.pc = 100)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (he : s.readW 4 = UInt32.ofInt e) :
    ∃ n t, n ≤ 20 * 2 ^ 52 + 50 ∧ Steps64 sqrt64Code 0 n s t ∧
      t.pc = s.readX 30 ∧ t.readD 0 = Sqrt.rescale64 (Sqrt.core64 (s.readX 0)) e ∧
      t.fpcr = s.fpcr ∧ (∀ r, 7 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨u, hu, hpu, hfu⟩ := estimate64_trace s hpc hc
  have hsu : u.WellFormed := ⟨by rw [hfu.registers]; exact hs.1, hfu.size.trans hs.2⟩
  have hcu : supportedControls u.fpcr = true := by rw [hfu.fpcr]; exact hc
  have hx (r : Nat) : u.readX r = s.readX r := Machine.readX_congr u s hfu.registers r
  have hlo : 0x3ff0000000000000 ≤ (u.readX 0).toNat := by rw [hx]; exact lo
  have hhi : (u.readX 0).toNat < 0x4010000000000000 := by rw [hx]; exact hi
  obtain ⟨v, hv⟩ : ∃ v, setup64_12 u = v := ⟨_, rfl⟩
  have hfv : IntegerFrame [0, 1, 2, 3, 5, 6] u v := by rw [← hv]; exact setup64_properties u
  have htrace : Steps64 sqrt64Code 0 12 u v := by rw [← hv]; exact setup64_trace u hpu hcu
  have hcv : supportedControls v.fpcr = true := by rw [hfv.fpcr]; exact hcu
  have hsv : v.WellFormed := ⟨hfv.size.trans hsu.1, by rw [hfv.vectors]; exact hsu.2⟩
  have hpv : v.pc = 208 := by
    rw [← hv]
    simp only [setup64_12, setup64_11, setup64_10, setup64_9, setup64_8,
      setup64_7, setup64_6, setup64_5, setup64_4, setup64_3, setup64_2, setup64_1,
      Machine.advanceW_pc, Machine.advanceX_pc, hpu]
    decide +kernel
  have hb := setup64_seed_bounds u hsu.1
  rw [hv] at hb
  have hn := setup64_radicand_value u hsu.1 hlo hhi
  rw [hv] at hn
  obtain ⟨k, w, hk, hw, hpw, hqw, hfw⟩ := normalized_correction_loop64_correct
    (u.readX 0) hlo hhi v hpv hcv hsv.1 hn hb.1 hb.2
  have hfw' : IntegerFrame [0, 1, 2, 3, 5, 6] v w := hfw.widen (by intro r hr; simp at hr ⊢; tauto)
  have hf := hfv.trans hfw'
  have hcw : supportedControls w.fpcr = true := by rw [hf.fpcr]; exact hcu
  have hsw : w.WellFormed := ⟨hf.size.trans hsu.1, by rw [hf.vectors]; exact hsu.2⟩
  have hew : w.readW 4 = UInt32.ofInt e := by
    change (w.readX 4).toUInt32 = _
    rw [hf.registers 4 (by decide) (by decide), hx]
    exact he
  have hlw : w.readX 30 = s.readX 30 :=
    (hf.registers 30 (by decide) (by decide)).trans (hx 30)
  refine ⟨15 + (12 + (k + 5)), returned64State w, by omega,
    hu.trans (htrace.trans (hw.trans (return64_trace w hpw hcw))),
    (return64_link w).trans hlw, ?_, hf.fpcr.trans hfu.fpcr, ?_, ?_⟩
  · rw [return64_correct (u.readX 0) e hlo hhi elo ehi w hsw hqw hew, hx]
  · intro r hr hr'
    exact (return64_other_register w r hr' (by omega) (by omega)).trans
      ((hf.registers r hr' (by simp; omega)).trans (hx r))
  · intro r hr
    rw [return64_other_vector w r (by omega), hf.vectors]
    exact hfu.vectors r hr

theorem normalized_body64_run (s : Machine) (e : Int)
    (lo : 0x3ff0000000000000 ≤ (s.readX 0).toNat)
    (hi : (s.readX 0).toNat < 0x4010000000000000)
    (elo : -1021 ≤ e) (ehi : e ≤ 1022) (hpc : s.pc = 100)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (he : s.readW 4 = UInt32.ofInt e)
    (hstop : sqrt64Code[(s.readX 30).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code 0 (s.readX 30) (20 * 2 ^ 52 + 50) s = some t ∧
      t.pc = s.readX 30 ∧ t.readD 0 = Sqrt.rescale64 (Sqrt.core64 (s.readX 0)) e ∧
      t.fpcr = s.fpcr ∧ (∀ r, 7 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  obtain ⟨n, t, hn, ht, hp, hv, hf⟩ := normalized_body64_correct s e lo hi elo ehi hpc hc hs he
  exact ⟨t, run64_of_le_fuel _ _ _ _ _ _ _ hn
    (ht.run hp (by simpa only [UInt64.sub_zero] using hstop)), hp, hv, hf⟩

end VerifiedSqrt.Arm
