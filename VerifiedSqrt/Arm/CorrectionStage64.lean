module

public import VerifiedSqrt.Arm.Comparison64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem lower_test64_trace (s : Machine) (hpc : s.pc = 208)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32) (n : Nat)
    (hn : wideValue (s.readX 5) (s.readX 3) = 4 * n) (lo : 0 < (s.readX 0).toNat)
    (hi : (s.readX 0).toNat ≤ 2 ^ 53) :
    ∃ k t, k ≤ 9 ∧ Steps64 sqrt64Code 0 k s t ∧ IntegerFrame [2, 6] s t ∧
      t.pc = if 4 * n < (2 * (s.readX 0).toNat - 1) ^ 2 then 308 else 244 := by
  let a := lowerSquare64State s
  have hf : IntegerFrame [2, 6] s a := lower_square64_frame s
  have hpa : a.pc = 224 := by
    change ((s.pc + 4 + 4) + 4) + 4 = 224
    rw [hpc]
    decide +kernel
  have hca : supportedControls a.fpcr = true := by rw [hf.fpcr]; exact hc
  obtain ⟨k, hk, ht⟩ := run64_steps _ _ _ _ _ _ (lower_square64_block s hpc hc)
  obtain ⟨m, t, hm, hrun, hft, hp⟩ := lower_compare64_trace a hpa hca
  have hn' : wideValue (a.readX 5) (a.readX 3) = 4 * n := by
    rw [hf.registers 5 (by decide) (by decide), hf.registers 3 (by decide) (by decide)]
    exact hn
  have hv := lower_square64_block_value s hs lo hi
  have he : wideLess (a.readX 5) (a.readX 3) (a.readX 6) (a.readX 2) = decide (4 * n < (2 * (s.readX 0).toNat - 1) ^ 2) := by
    apply Bool.eq_iff_iff.mpr
    rw [wideLess_exact, decide_eq_true_eq, hn', hv]
  rw [he] at hp
  refine ⟨k + m, t, by omega, ht.trans hrun,
    hf.trans (hft.widen (by intro r hr; simp at hr)), ?_⟩
  simpa only [decide_eq_true_eq] using hp

theorem upper_test64_trace (s : Machine) (hpc : s.pc = 244)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32) (n : Nat)
    (hn : wideValue (s.readX 5) (s.readX 3) = 4 * n)
    (hi : (s.readX 0).toNat ≤ 2 ^ 53) :
    ∃ k t, k ≤ 9 ∧ Steps64 sqrt64Code 0 k s t ∧ IntegerFrame [2, 6] s t ∧
      t.pc = if (2 * (s.readX 0).toNat + 1) ^ 2 < 4 * n then 316 else 280 := by
  let a := upperSquare64State s
  have hf : IntegerFrame [2, 6] s a := upper_square64_frame s
  have hpa : a.pc = 260 := by
    change ((s.pc + 4 + 4) + 4) + 4 = 260
    rw [hpc]
    decide +kernel
  have hca : supportedControls a.fpcr = true := by rw [hf.fpcr]; exact hc
  obtain ⟨k, hk, ht⟩ := run64_steps _ _ _ _ _ _ (upper_square64_block s hpc hc)
  obtain ⟨m, t, hm, hrun, hft, hp⟩ := upper_compare64_trace a hpa hca
  have hn' : wideValue (a.readX 5) (a.readX 3) = 4 * n := by
    rw [hf.registers 5 (by decide) (by decide), hf.registers 3 (by decide) (by decide)]
    exact hn
  have hv := upper_square64_block_value s hs hi
  have he : wideLess (a.readX 6) (a.readX 2) (a.readX 5) (a.readX 3) = decide ((2 * (s.readX 0).toNat + 1) ^ 2 < 4 * n) := by
    apply Bool.eq_iff_iff.mpr
    rw [wideLess_exact, decide_eq_true_eq, hn', hv]
  rw [he] at hp
  refine ⟨k + m, t, by omega, ht.trans hrun,
    hf.trans (hft.widen (by intro r hr; simp at hr)), ?_⟩
  simpa only [decide_eq_true_eq] using hp

def adjust64State (s : Machine) (q : UInt64) : Machine :=
  {s.writeX 0 q with pc := 208}

theorem adjust64_value (s : Machine) (q : UInt64) (hs : s.x.size = 32) :
    (adjust64State s q).readX 0 = q := Machine.readX_writeX_same _ 0 (by decide) hs _

theorem adjust64_frame (s : Machine) (q : UInt64) : IntegerFrame [0, 2, 6] s (adjust64State s q) :=
  (IntegerFrame.writeX _ s 0 (by decide) (by decide) q).trans (IntegerFrame.pc _ _ _)

theorem decrement64_trace (s : Machine) (hpc : s.pc = 308)
    (hc : supportedControls s.fpcr = true) :
    Steps64 sqrt64Code 0 2 s (adjust64State s (s.readX 0 - 1)) := by
  let t := s.advanceX 0 (s.readX 0 - 1)
  have hp : t.pc = 312 := by rw [Machine.advanceX_pc, hpc]; decide +kernel
  have h1 : Steps64 sqrt64Code 0 1 s t := Steps64.single
    (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) (step64_decrement s hc)
  have h2 : Steps64 sqrt64Code 0 1 t (adjust64State s (s.readX 0 - 1)) := by
    apply Steps64.single (word := 0x17ffffe6)
      (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel)
    rw [step64_back_down t hc]
    have hb : branchPC t.pc (-104) = 208 := by rw [hp]; decide +kernel
    rw [hb]
    rfl
  exact h1.trans h2

theorem increment64_trace (s : Machine) (hpc : s.pc = 316)
    (hc : supportedControls s.fpcr = true) :
    Steps64 sqrt64Code 0 2 s (adjust64State s (s.readX 0 + 1)) := by
  let t := s.advanceX 0 (s.readX 0 + 1)
  have hp : t.pc = 320 := by rw [Machine.advanceX_pc, hpc]; decide +kernel
  have h1 : Steps64 sqrt64Code 0 1 s t := Steps64.single
    (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) (step64_increment s hc)
  have h2 : Steps64 sqrt64Code 0 1 t (adjust64State s (s.readX 0 + 1)) := by
    apply Steps64.single (word := 0x17ffffe4)
      (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel)
    rw [step64_back_up t hc]
    have hb : branchPC t.pc (-112) = 208 := by rw [hp]; decide +kernel
    rw [hb]
    rfl
  exact h1.trans h2

end VerifiedSqrt.Arm
