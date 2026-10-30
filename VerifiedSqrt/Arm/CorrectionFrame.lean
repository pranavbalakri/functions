module

public import VerifiedSqrt.Arm.CorrectionLoop

@[expose] public section

namespace VerifiedSqrt.Arm

structure CorrectionFrame (s t : Machine) : Prop where
  fpcr : t.fpcr = s.fpcr
  fpsr : t.fpsr = s.fpsr
  vectors : t.v = s.v
  size : t.x.size = s.x.size
  registers : ∀ r, r < 31 → r ≠ 0 → r ≠ 2 → t.readX r = s.readX r

theorem CorrectionFrame.trans {s t u : Machine}
    (h : CorrectionFrame s t) (k : CorrectionFrame t u) : CorrectionFrame s u :=
  ⟨k.fpcr.trans h.fpcr, k.fpsr.trans h.fpsr, k.vectors.trans h.vectors,
    k.size.trans h.size, fun r hr h0 h2 => (k.registers r hr h0 h2).trans (h.registers r hr h0 h2)⟩

theorem frame_pc (s : Machine) (pc : UInt64) : CorrectionFrame s {s with pc := pc} :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

theorem frame_writeW (s : Machine) (d : Nat) (hd : d = 0 ∨ d = 2) (w : UInt32) :
    CorrectionFrame s (s.writeW d w) := by
  have hlt : d < 31 := by omega
  have hne : d ≠ 31 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Machine.writeW, hne]
  · simp [Machine.writeW, hne]
  · simp [Machine.writeW, hne]
  · simp [Machine.writeW, hne]
  · intro r hr h0 h2
    exact Machine.readX_writeW_ne s d r hlt hr (by omega) w

theorem frame_writeX (s : Machine) (d : Nat) (hd : d = 0 ∨ d = 2) (w : UInt64) :
    CorrectionFrame s (s.writeX d w) := by
  have hlt : d < 31 := by omega
  have hne : d ≠ 31 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Machine.writeX, hne]
  · simp [Machine.writeX, hne]
  · simp [Machine.writeX, hne]
  · simp [Machine.writeX, hne]
  · intro r hr h0 h2
    exact Machine.readX_writeX_ne s d r hlt hr (by omega) w

theorem frame_compare (s : Machine) : CorrectionFrame s (compareState s) :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

theorem frame_double (s : Machine) : CorrectionFrame s (doubleState s) :=
  (frame_pc s _).trans (frame_writeW _ 2 (Or.inr rfl) _)

theorem frame_lower_test (s : Machine) : CorrectionFrame s (lowerTestState s) := by
  have h1 : CorrectionFrame (doubleState s) (lowerState s) :=
    (frame_pc _ _).trans (frame_writeW _ 2 (Or.inr rfl) _)
  have h2 : CorrectionFrame (lowerState s) (lowerSquareState s) :=
    (frame_pc _ _).trans (frame_writeX _ 2 (Or.inr rfl) _)
  exact (frame_double s).trans (h1.trans (h2.trans ((frame_compare _).trans (frame_pc _ _))))

theorem frame_upper_test (s : Machine) : CorrectionFrame s (upperTestState s) := by
  have h1 : CorrectionFrame (doubleState s) (upperState s) :=
    (frame_pc _ _).trans (frame_writeW _ 2 (Or.inr rfl) _)
  have h2 : CorrectionFrame (upperState s) (upperSquareState s) :=
    (frame_pc _ _).trans (frame_writeX _ 2 (Or.inr rfl) _)
  exact (frame_double s).trans (h1.trans (h2.trans ((frame_compare _).trans (frame_pc _ _))))

theorem frame_adjust (s : Machine) (q : UInt32) : CorrectionFrame s (adjustLoopState s q) :=
  (frame_writeW s 0 (Or.inl rfl) q).trans (frame_pc _ 184)

end VerifiedSqrt.Arm
