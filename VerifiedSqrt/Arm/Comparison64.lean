module

public import VerifiedSqrt.Arm.CorrectionBlock64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem compare64_low_condition (s : Machine) (a b : UInt64) :
    (!(compare64State s a b).carry) = decide (a < b) := by
  change (!decide (b.toNat ≤ a.toNat)) = decide (a.toNat < b.toNat)
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, decide_eq_true_eq]
  omega

theorem compare64_high_condition (s : Machine) (a b : UInt64) :
    ((compare64State s a b).carry && !(compare64State s a b).zero) = decide (b < a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [compare64State, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    beq_iff_eq, decide_eq_true_eq]
  rw [UInt64.sub_eq_iff_eq_add, UInt64.zero_add, ← UInt64.toNat_inj]
  change (b.toNat ≤ a.toNat ∧ ¬a.toNat = b.toNat) ↔ b.toNat < a.toNat
  omega

theorem lower_compare64_trace (s : Machine) (hpc : s.pc = 224)
    (hc : supportedControls s.fpcr = true) :
    ∃ n t, n ≤ 5 ∧ Steps64 sqrt64Code 0 n s t ∧ IntegerFrame [] s t ∧
      t.pc = if wideLess (s.readX 5) (s.readX 3) (s.readX 6) (s.readX 2) then 308 else 244 := by
  let b := compare64State s (s.readX 5) (s.readX 6)
  have hpb : b.pc = 228 := by
    change s.pc + 4 = 228
    rw [hpc]
    decide +kernel
  have h1 : Steps64 sqrt64Code 0 1 s b := Steps64.single
    (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) (step64_compare_high s hc)
  have hf : (!b.carry) = decide (s.readX 5 < s.readX 6) := compare64_low_condition s _ _
  by_cases hl : s.readX 5 < s.readX 6
  · let t : Machine := {b with pc := 308}
    have h2 : Steps64 sqrt64Code 0 1 b t := by
      apply Steps64.single (word := 0x54000283)
        (by rw [hpb]; decide +kernel) (by rw [hpb]; decide +kernel)
      rw [step64_lo80 b hc]
      have ht : branchPC b.pc 80 = 308 := by rw [hpb]; decide +kernel
      simp only [hf, hl, decide_true, ite_true, ht]
      rfl
    refine ⟨2, t, by omega, h1.trans h2,
      ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, ?_⟩
    simp [t, wideLess, hl]
  let c : Machine := {b with pc := 232}
  have hpcC : c.pc = 232 := rfl
  have h2 : Steps64 sqrt64Code 0 1 b c := by
    apply Steps64.single (word := 0x54000283)
      (by rw [hpb]; decide +kernel) (by rw [hpb]; decide +kernel)
    rw [step64_lo80 b hc]
    have ht : b.pc + 4 = 232 := by rw [hpb]; decide +kernel
    simp only [hf, hl, decide_false, Bool.false_eq_true, ite_false, ht]
    rfl
  have hg : (c.carry && !c.zero) = decide (s.readX 6 < s.readX 5) := compare64_high_condition s _ _
  by_cases hh : s.readX 6 < s.readX 5
  · let t : Machine := {c with pc := 244}
    have h3 : Steps64 sqrt64Code 0 1 c t := by
      apply Steps64.single (word := 0x54000068) (by rw [hpcC]; decide +kernel) (by rw [hpcC]; decide +kernel)
      rw [step64_hi12 c hc]
      have ht : branchPC c.pc 12 = 244 := by rw [hpcC]; decide +kernel
      simp only [hg, hh, decide_true, ite_true, ht]
      rfl
    refine ⟨3, t, by omega, (h1.trans h2).trans h3,
      ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, ?_⟩
    have hne : s.readX 5 ≠ s.readX 6 := by
      intro he
      rw [he] at hh
      exact Nat.lt_irrefl _ hh
    simp [t, wideLess, hl, hne]
  have heq : s.readX 5 = s.readX 6 := by
    apply UInt64.toNat_inj.mp
    change ¬ (s.readX 5).toNat < (s.readX 6).toNat at hl
    change ¬ (s.readX 6).toNat < (s.readX 5).toNat at hh
    omega
  let d : Machine := {c with pc := 236}
  have h3 : Steps64 sqrt64Code 0 1 c d := by
    apply Steps64.single (word := 0x54000068) (by rw [hpcC]; decide +kernel) (by rw [hpcC]; decide +kernel)
    rw [step64_hi12 c hc]
    simp only [hg, hh, decide_false, Bool.false_eq_true, ite_false]
    rfl
  have hpcD : d.pc = 236 := rfl
  let e := compare64State d (d.readX 3) (d.readX 2)
  have hpe : e.pc = 240 := rfl
  have h4 : Steps64 sqrt64Code 0 1 d e := Steps64.single
    (by rw [hpcD]; decide +kernel) (by rw [hpcD]; decide +kernel) (step64_compare_low d hc)
  let t : Machine := {e with pc := if !e.carry then 308 else 244}
  have h5 : Steps64 sqrt64Code 0 1 e t := by
    apply Steps64.single (word := 0x54000223)
      (by rw [hpe]; decide +kernel) (by rw [hpe]; decide +kernel)
    rw [step64_lo68 e hc]
    have ht : branchPC e.pc 68 = 308 := by rw [hpe]; decide +kernel
    have hn : e.pc + 4 = 244 := by rw [hpe]; decide +kernel
    rw [ht, hn]
  refine ⟨5, t, by omega, (((h1.trans h2).trans h3).trans h4).trans h5,
    ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, ?_⟩
  change (if !e.carry then 308 else 244) = _
  rw [compare64_low_condition]
  change (if decide (s.readX 3 < s.readX 2) then 308 else 244) = _
  simp [wideLess, heq]

theorem upper_compare64_trace (s : Machine) (hpc : s.pc = 260)
    (hc : supportedControls s.fpcr = true) :
    ∃ n t, n ≤ 5 ∧ Steps64 sqrt64Code 0 n s t ∧ IntegerFrame [] s t ∧
      t.pc = if wideLess (s.readX 6) (s.readX 2) (s.readX 5) (s.readX 3) then 316 else 280 := by
  let b := compare64State s (s.readX 5) (s.readX 6)
  have hpb : b.pc = 264 := by
    change s.pc + 4 = 264
    rw [hpc]
    decide +kernel
  have h1 : Steps64 sqrt64Code 0 1 s b := Steps64.single
    (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) (step64_compare_high s hc)
  have hf : (b.carry && !b.zero) = decide (s.readX 6 < s.readX 5) := compare64_high_condition s _ _
  by_cases hl : s.readX 6 < s.readX 5
  · let t : Machine := {b with pc := 316}
    have h2 : Steps64 sqrt64Code 0 1 b t := by
      apply Steps64.single (word := 0x540001a8)
        (by rw [hpb]; decide +kernel) (by rw [hpb]; decide +kernel)
      rw [step64_hi52 b hc]
      have ht : branchPC b.pc 52 = 316 := by rw [hpb]; decide +kernel
      simp only [hf, hl, decide_true, ite_true, ht]
      rfl
    refine ⟨2, t, by omega, h1.trans h2,
      ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, ?_⟩
    simp [t, wideLess, hl]
  let c : Machine := {b with pc := 268}
  have hpcC : c.pc = 268 := rfl
  have h2 : Steps64 sqrt64Code 0 1 b c := by
    apply Steps64.single (word := 0x540001a8)
      (by rw [hpb]; decide +kernel) (by rw [hpb]; decide +kernel)
    rw [step64_hi52 b hc]
    have ht : b.pc + 4 = 268 := by rw [hpb]; decide +kernel
    simp only [hf, hl, decide_false, Bool.false_eq_true, ite_false, ht]
    rfl
  have hg : (!c.carry) = decide (s.readX 5 < s.readX 6) := compare64_low_condition s _ _
  by_cases hh : s.readX 5 < s.readX 6
  · let t : Machine := {c with pc := 280}
    have h3 : Steps64 sqrt64Code 0 1 c t := by
      apply Steps64.single (word := 0x54000063) (by rw [hpcC]; decide +kernel) (by rw [hpcC]; decide +kernel)
      rw [step64_lo12 c hc]
      have ht : branchPC c.pc 12 = 280 := by rw [hpcC]; decide +kernel
      simp only [hg, hh, decide_true, ite_true, ht]
      rfl
    refine ⟨3, t, by omega, (h1.trans h2).trans h3,
      ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, ?_⟩
    have hne : s.readX 5 ≠ s.readX 6 := by
      intro he
      rw [he] at hh
      exact Nat.lt_irrefl _ hh
    simp [t, wideLess, hl, Ne.symm hne]
  have heq : s.readX 5 = s.readX 6 := by
    apply UInt64.toNat_inj.mp
    change ¬ (s.readX 6).toNat < (s.readX 5).toNat at hl
    change ¬ (s.readX 5).toNat < (s.readX 6).toNat at hh
    omega
  let d : Machine := {c with pc := 272}
  have h3 : Steps64 sqrt64Code 0 1 c d := by
    apply Steps64.single (word := 0x54000063) (by rw [hpcC]; decide +kernel) (by rw [hpcC]; decide +kernel)
    rw [step64_lo12 c hc]
    simp only [hg, hh, decide_false, Bool.false_eq_true, ite_false]
    rfl
  have hpcD : d.pc = 272 := rfl
  let e := compare64State d (d.readX 3) (d.readX 2)
  have hpe : e.pc = 276 := rfl
  have h4 : Steps64 sqrt64Code 0 1 d e := Steps64.single
    (by rw [hpcD]; decide +kernel) (by rw [hpcD]; decide +kernel) (step64_compare_low d hc)
  let t : Machine := {e with pc := if e.carry && !e.zero then 316 else 280}
  have h5 : Steps64 sqrt64Code 0 1 e t := by
    apply Steps64.single (word := 0x54000148)
      (by rw [hpe]; decide +kernel) (by rw [hpe]; decide +kernel)
    rw [step64_hi40 e hc]
    have ht : branchPC e.pc 40 = 316 := by rw [hpe]; decide +kernel
    have hn : e.pc + 4 = 280 := by rw [hpe]; decide +kernel
    rw [ht, hn]
  refine ⟨5, t, by omega, (((h1.trans h2).trans h3).trans h4).trans h5,
    ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, ?_⟩
  change (if e.carry && !e.zero then 316 else 280) = _
  rw [compare64_high_condition]
  change (if decide (s.readX 2 < s.readX 3) then 316 else 280) = _
  simp [wideLess, heq]

end VerifiedSqrt.Arm
