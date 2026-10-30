module

public import VerifiedSqrt.Arm.CorrectionFrame
public import VerifiedSqrt.Sqrt.Correction32

@[expose] public section

namespace VerifiedSqrt.Arm

open Sqrt

theorem correction_loop_correct (n r fuel : Nat) (hr : IntegerRootCertificate n r)
    (rlo : 2 ^ 23 ≤ r) (rhi : r ≤ 2 ^ 24) (s : Machine)
    (hpc : s.pc = 184) (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hn : (s.readX 3).toNat = 4 * n)
    (qlo : 2 ^ 23 ≤ (s.readW 0).toNat) (qhi : (s.readW 0).toNat ≤ 2 ^ 24)
    (hd : (s.readW 0).toNat - r + (r - (s.readW 0).toNat) ≤ fuel) :
    ∃ t, run sqrt32Code 224 (12 * fuel + 10) s = some t ∧
      t.pc = 224 ∧ (t.readW 0).toNat = r ∧ CorrectionFrame s t := by
  induction fuel using Nat.strong_induction_on generalizing s with
  | h fuel ih =>
    have hlframe := lower_test_frame s
    have hlctrl : supportedControls (lowerTestState s).fpcr = true := by
      rw [hlframe.2.2.1]
      exact hc
    have hlsize : (lowerTestState s).x.size = 32 := hlframe.2.2.2.trans hs
    have hln : ((lowerTestState s).readX 3).toNat = 4 * n := by rw [hlframe.1, hn]
    have hlpc := lower_test_pc s hs n hn (by omega) qhi
    by_cases hlow : 4 * n < (2 * (s.readW 0).toNat - 1) ^ 2
    · have hqr := (integerRootCertificate_lower_test hr _).mp hlow
      have hpos : 0 < fuel := by omega
      have hpc' : (lowerTestState s).pc = 252 := by simpa only [hlow, ite_true] using hlpc
      let t := adjustLoopState (lowerTestState s) ((lowerTestState s).readW 0 - 1)
      have ht := adjust_loop_frame (lowerTestState s) ((lowerTestState s).readW 0 - 1) hlsize
      have hq : (t.readW 0).toNat = (s.readW 0).toNat - 1 := by
        change ((adjustLoopState _ _).readW 0).toNat = _
        rw [ht.1, hlframe.2.1, UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (s.readW 0).toNat; omega)]
        rfl
      have htc : supportedControls t.fpcr = true := by
        change supportedControls (adjustLoopState _ _).fpcr = true
        rw [ht.2.2.1]
        exact hlctrl
      have hts : t.x.size = 32 := ht.2.2.2.trans hlsize
      have htn : (t.readX 3).toNat = 4 * n := by
        change ((adjustLoopState _ _).readX 3).toNat = _
        rw [ht.2.1, hln]
      obtain ⟨u, hu, hpu, hqu, hfu⟩ := ih (fuel - 1) (by omega) t rfl htc hts htn
        (by rw [hq]; omega) (by rw [hq]; omega) (by rw [hq]; omega)
      refine ⟨u, ?_, hpu, hqu, (frame_lower_test s).trans ((frame_adjust _ _).trans hfu)⟩
      rw [show 12 * fuel + 10 = ((12 * (fuel - 1) + 10 + 5) + 2) + 5 by omega,
        lower_test_run s hpc hc, decrement_run _ hpc' hlctrl]
      exact run_add_fuel _ _ _ 5 t u hu
    · have hpc' : (lowerTestState s).pc = 204 := by simpa only [hlow, ite_false] using hlpc
      have hu := upper_test_frame (lowerTestState s)
      have hupc := upper_test_pc (lowerTestState s) hlsize n hln (by rw [hlframe.2.1]; exact qhi)
      have huq : (upperTestState (lowerTestState s)).readW 0 = s.readW 0 := hu.2.1.trans hlframe.2.1
      have hun : ((upperTestState (lowerTestState s)).readX 3).toNat = 4 * n := by rw [hu.1, hln]
      have huc : supportedControls (upperTestState (lowerTestState s)).fpcr = true := by
        rw [hu.2.2.1]
        exact hlctrl
      have hus : (upperTestState (lowerTestState s)).x.size = 32 := hu.2.2.2.trans hlsize
      rw [hlframe.2.1] at hupc
      by_cases hupp : (2 * (s.readW 0).toNat + 1) ^ 2 < 4 * n
      · have hqr := (integerRootCertificate_upper_test hr _).mp hupp
        have hpos : 0 < fuel := by omega
        have hpc'' : (upperTestState (lowerTestState s)).pc = 260 := by
          simpa only [hupp, ite_true] using hupc
        let t := adjustLoopState (upperTestState (lowerTestState s))
          ((upperTestState (lowerTestState s)).readW 0 + 1)
        have ht := adjust_loop_frame (upperTestState (lowerTestState s))
          ((upperTestState (lowerTestState s)).readW 0 + 1) hus
        have hq : (t.readW 0).toNat = (s.readW 0).toNat + 1 := by
          change ((adjustLoopState _ _).readW 0).toNat = _
          rw [ht.1, huq, UInt32.toNat_add]
          change ((s.readW 0).toNat + 1) % 2 ^ 32 = _
          exact Nat.mod_eq_of_lt (by omega)
        have htc : supportedControls t.fpcr = true := by
          change supportedControls (adjustLoopState _ _).fpcr = true
          rw [ht.2.2.1]
          exact huc
        have hts : t.x.size = 32 := ht.2.2.2.trans hus
        have htn : (t.readX 3).toNat = 4 * n := by
          change ((adjustLoopState _ _).readX 3).toNat = _
          rw [ht.2.1, hun]
        obtain ⟨u, hrun, hpu, hqu, hfu⟩ := ih (fuel - 1) (by omega) t rfl htc hts htn
          (by rw [hq]; omega) (by rw [hq]; omega) (by rw [hq]; omega)
        refine ⟨u, ?_, hpu, hqu, (frame_lower_test s).trans
          ((frame_upper_test _).trans ((frame_adjust _ _).trans hfu))⟩
        rw [show 12 * fuel + 10 = (((12 * (fuel - 1) + 10) + 2) + 5) + 5 by omega,
          lower_test_run s hpc hc, upper_test_run _ hpc' hlctrl,
          increment_run _ hpc'' huc]
        exact hrun
      · have hstop : (upperTestState (lowerTestState s)).pc = 224 := by
          simpa only [hupp, ite_false] using hupc
        have hq : (s.readW 0).toNat = r := by
          rw [integerRootCertificate_lower_test hr] at hlow
          rw [integerRootCertificate_upper_test hr] at hupp
          omega
        refine ⟨upperTestState (lowerTestState s), ?_, hstop, ?_,
          (frame_lower_test s).trans (frame_upper_test _)⟩
        · rw [show 12 * fuel + 10 = ((12 * fuel) + 5) + 5 by omega,
            lower_test_run s hpc hc, upper_test_run _ hpc' hlctrl]
          exact run_at_stop _ _ _ _ hstop
        · rw [huq, hq]

theorem normalized_correction_loop_correct (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) (s : Machine)
    (hpc : s.pc = 184) (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hn : (s.readX 3).toNat = 4 * normalizedRadicand32 x)
    (qlo : 2 ^ 23 ≤ (s.readW 0).toNat) (qhi : (s.readW 0).toNat ≤ 2 ^ 24) :
    ∃ t, run sqrt32Code 224 (12 * 2 ^ 23 + 10) s = some t ∧
      t.pc = 224 ∧ (t.readW 0).toNat = correctedSignificand32 x ∧ CorrectionFrame s t := by
  have hn' := normalized32_radicand_bounds x lo hi
  have hr := roundedIntegerRoot_certificate (normalizedRadicand32 x) (by omega)
  have hb := roundedIntegerRoot32_bounds x lo hi
  rw [correctedSignificand32_eq x lo hi]
  exact correction_loop_correct _ _ _ hr hb.1 hb.2 s hpc hc hs hn qlo qhi (by omega)

end VerifiedSqrt.Arm
