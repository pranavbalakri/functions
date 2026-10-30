module

public import VerifiedSqrt.Arm.CorrectionStage64
public import VerifiedSqrt.Sqrt.Correction64

@[expose] public section

namespace VerifiedSqrt.Arm

open Sqrt

theorem IntegerFrame.correction64 {s t : Machine} (h : IntegerFrame [2, 6] s t) :
    IntegerFrame [0, 2, 6] s t := h.widen (by intro r hr; simp at hr ⊢; tauto)

theorem correction_loop64_correct (n r fuel : Nat) (hr : IntegerRootCertificate n r)
    (rlo : 2 ^ 52 ≤ r) (rhi : r ≤ 2 ^ 53) (s : Machine)
    (hpc : s.pc = 208) (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hn : wideValue (s.readX 5) (s.readX 3) = 4 * n)
    (qlo : 2 ^ 52 ≤ (s.readX 0).toNat) (qhi : (s.readX 0).toNat ≤ 2 ^ 53)
    (hd : (s.readX 0).toNat - r + (r - (s.readX 0).toNat) ≤ fuel) :
    ∃ k t, k ≤ 20 * fuel + 18 ∧ Steps64 sqrt64Code 0 k s t ∧
      t.pc = 280 ∧ (t.readX 0).toNat = r ∧ IntegerFrame [0, 2, 6] s t := by
  induction fuel using Nat.strong_induction_on generalizing s with
  | h fuel ih =>
    obtain ⟨a, l, ha, hl, hfl, hpl⟩ := lower_test64_trace s hpc hc hs n hn (by omega) qhi
    have hlq : l.readX 0 = s.readX 0 := hfl.registers 0 (by decide) (by decide)
    have hlc : supportedControls l.fpcr = true := by rw [hfl.fpcr]; exact hc
    have hls : l.x.size = 32 := hfl.size.trans hs
    have hln : wideValue (l.readX 5) (l.readX 3) = 4 * n := by
      rw [hfl.registers 5 (by decide) (by decide), hfl.registers 3 (by decide) (by decide), hn]
    by_cases hlow : 4 * n < (2 * (s.readX 0).toNat - 1) ^ 2
    · have hqr := (integerRootCertificate_lower_test hr _).mp hlow
      have hp : l.pc = 308 := by simpa only [hlow, ite_true] using hpl
      let t := adjust64State l (l.readX 0 - 1)
      have hf := adjust64_frame l (l.readX 0 - 1)
      have hq : (t.readX 0).toNat = (s.readX 0).toNat - 1 := by
        rw [adjust64_value l _ hls, hlq,
          UInt64.toNat_sub_of_le _ _ (by change 1 ≤ (s.readX 0).toNat; omega)]
        rfl
      have htc : supportedControls t.fpcr = true := by rw [hf.fpcr]; exact hlc
      have hts : t.x.size = 32 := hf.size.trans hls
      have htn : wideValue (t.readX 5) (t.readX 3) = 4 * n := by
        rw [hf.registers 5 (by decide) (by decide), hf.registers 3 (by decide) (by decide), hln]
      obtain ⟨b, u, hb, hu, hpu, hqu, hfu⟩ := ih (fuel - 1) (by omega) t rfl htc hts htn
        (by rw [hq]; omega) (by rw [hq]; omega) (by rw [hq]; omega)
      exact ⟨a + (2 + b), u, by omega, hl.trans ((decrement64_trace l hp hlc).trans hu),
        hpu, hqu, hfl.correction64.trans (hf.trans hfu)⟩
    · have hp : l.pc = 244 := by simpa only [hlow, ite_false] using hpl
      obtain ⟨b, u, hb, hu, hfu, hpu⟩ := upper_test64_trace l hp hlc hls n hln (by rw [hlq]; exact qhi)
      rw [hlq] at hpu
      have huq : u.readX 0 = s.readX 0 := (hfu.registers 0 (by decide) (by decide)).trans hlq
      have huc : supportedControls u.fpcr = true := by rw [hfu.fpcr]; exact hlc
      have hus : u.x.size = 32 := hfu.size.trans hls
      have hun : wideValue (u.readX 5) (u.readX 3) = 4 * n := by
        rw [hfu.registers 5 (by decide) (by decide), hfu.registers 3 (by decide) (by decide), hln]
      by_cases hupp : (2 * (s.readX 0).toNat + 1) ^ 2 < 4 * n
      · have hqr := (integerRootCertificate_upper_test hr _).mp hupp
        have hp' : u.pc = 316 := by simpa only [hupp, ite_true] using hpu
        let t := adjust64State u (u.readX 0 + 1)
        have hf := adjust64_frame u (u.readX 0 + 1)
        have hq : (t.readX 0).toNat = (s.readX 0).toNat + 1 := by
          rw [adjust64_value u _ hus, huq, UInt64.toNat_add]
          change ((s.readX 0).toNat + 1) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have htc : supportedControls t.fpcr = true := by rw [hf.fpcr]; exact huc
        have hts : t.x.size = 32 := hf.size.trans hus
        have htn : wideValue (t.readX 5) (t.readX 3) = 4 * n := by
          rw [hf.registers 5 (by decide) (by decide), hf.registers 3 (by decide) (by decide), hun]
        obtain ⟨c, v, hv, hrun, hpv, hqv, hfv⟩ := ih (fuel - 1) (by omega) t rfl htc hts htn
          (by rw [hq]; omega) (by rw [hq]; omega) (by rw [hq]; omega)
        exact ⟨a + (b + (2 + c)), v, by omega,
          hl.trans (hu.trans ((increment64_trace u hp' huc).trans hrun)), hpv, hqv,
          hfl.correction64.trans (hfu.correction64.trans (hf.trans hfv))⟩
      · have hstop : u.pc = 280 := by simpa only [hupp, ite_false] using hpu
        have hq : (s.readX 0).toNat = r := by
          rw [integerRootCertificate_lower_test hr] at hlow
          rw [integerRootCertificate_upper_test hr] at hupp
          omega
        exact ⟨a + b, u, by omega, hl.trans hu, hstop, by rw [huq, hq],
          hfl.correction64.trans hfu.correction64⟩

theorem normalized_correction_loop64_correct (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) (s : Machine)
    (hpc : s.pc = 208) (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hn : wideValue (s.readX 5) (s.readX 3) = 4 * normalizedRadicand64 x)
    (qlo : 2 ^ 52 ≤ (s.readX 0).toNat) (qhi : (s.readX 0).toNat ≤ 2 ^ 53) :
    ∃ k t, k ≤ 20 * 2 ^ 52 + 18 ∧ Steps64 sqrt64Code 0 k s t ∧
      t.pc = 280 ∧ (t.readX 0).toNat = correctedSignificand64 x ∧
      IntegerFrame [0, 2, 6] s t := by
  have hn' := normalized64_radicand_bounds x lo hi
  have hr := roundedIntegerRoot_certificate (normalizedRadicand64 x) (by omega)
  have hb := roundedIntegerRoot64_bounds x lo hi
  rw [correctedSignificand64_eq x lo hi]
  exact correction_loop64_correct _ _ _ hr hb.1 hb.2 s hpc hc hs hn qlo qhi (by omega)

end VerifiedSqrt.Arm
