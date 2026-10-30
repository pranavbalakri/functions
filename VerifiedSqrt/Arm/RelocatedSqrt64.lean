module

public import VerifiedSqrt.Arm.RelocatedExecution64
public import VerifiedSqrt.Arm.Sqrt64Invariants
public import VerifiedSqrt.Arm.Correctness64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem sqrt64_relocated_correct (base : UInt64) (s : Machine)
    (hb : base.toNat % 4 = 0) (hpc : s.pc = base)
    (hc : supportedControls s.fpcr = true) (hs : s.WellFormed)
    (hstop : sqrt64Code[(s.readX 30 - base).toNat / 4]? = none) :
    ∃ t, run64 sqrt64Code base (s.readX 30) (20 * 2 ^ 52 + 75) s = some t ∧
      t.pc = s.readX 30 ∧ Sqrt.SqrtSpec64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0) (t.readD 0) ∧
      t.fpcr = s.fpcr ∧ (∀ r, 7 ≤ r → r < 31 → t.readX r = s.readX r) ∧
      (∀ r, 6 ≤ r → t.v[r]! = s.v[r]!) := by
  let u := s.relocate (-base)
  have hsu : u.WellFormed := ⟨(Machine.relocate_size (-base) s).trans hs.1, hs.2⟩
  have hcu : supportedControls u.fpcr = true := hc
  have hpu : u.pc = 0 := by
    dsimp only [u]
    rw [Machine.relocate_pc, hpc, UInt64.add_left_neg]
  have hlu : u.readX 30 = s.readX 30 - base := by
    dsimp only [u]
    rw [Machine.readX_relocate_link (-base) s hs.1, UInt64.add_comm, UInt64.add_neg_eq_sub]
  have hstopu : sqrt64Code[(u.readX 30).toNat / 4]? = none := by rw [hlu]; exact hstop
  obtain ⟨v, hr, hpv, hspec, hfc, hregs, hvec⟩ := machine_sqrt64_correct u hpu hcu hsu hstopu
  have hsv : v.x.size = 32 := (run64_invariants _ sqrt64_step_invariants _ _ _ _ _ hr).1.trans hsu.1
  have hstart : u.relocate base = s := Machine.relocate_inverse base s hs.1
  have hlink : base + u.readX 30 = s.readX 30 := by
    rw [hlu, UInt64.add_comm, UInt64.sub_add_cancel]
  have hrun := run64_relocate sqrt64Code sqrt64_step_relocate sqrt64_step_invariants base (u.readX 30) hb
    (20 * 2 ^ 52 + 75) u v hcu hsu.1 hr
  rw [hstart, hlink] at hrun
  refine ⟨v.relocate base, hrun, ?_, ?_, hfc, ?_, ?_⟩
  · rw [Machine.relocate_pc, hpv, hlink]
  · exact hspec
  · intro r hr hr'
    by_cases he : r = 30
    · subst r
      rw [Machine.readX_relocate_link base v hsv, hregs 30 hr hr', hlink]
    · rw [Machine.readX_relocate base v r he, hregs r hr hr']
      exact Machine.readX_relocate (-base) s r he
  · intro r hr
    exact hvec r hr

end VerifiedSqrt.Arm
