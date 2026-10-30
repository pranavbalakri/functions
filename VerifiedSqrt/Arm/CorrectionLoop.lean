module

public import VerifiedSqrt.Arm.CorrectionBlock

@[expose] public section

namespace VerifiedSqrt.Arm

def compareState (s : Machine) : Machine := { s with
  pc := s.pc + 4
  negative := (s.readX 3 - s.readX 2) >>> 63 != 0
  zero := s.readX 3 - s.readX 2 == 0
  carry := s.readX 3 ≥ s.readX 2
  overflow := ((s.readX 3 >>> 63 != 0) != (s.readX 2 >>> 63 != 0)) &&
    (((s.readX 3 - s.readX 2) >>> 63 != 0) != (s.readX 3 >>> 63 != 0)) }

def lowerTestState (s : Machine) : Machine :=
  let t := compareState (lowerSquareState s)
  { t with pc := if !t.carry then 252 else 204 }

theorem lower_test_run (s : Machine) (hpc : s.pc = 184)
    (hc : supportedControls s.fpcr = true) (fuel : Nat) :
    run sqrt32Code 224 (fuel + 5) s = run sqrt32Code 224 fuel (lowerTestState s) := by
  have hp1 : (doubleState s).pc = 188 := by
    change s.pc + 4 = 188
    rw [hpc]
    decide +kernel
  have hp2 : (lowerState s).pc = 192 := by
    change (doubleState s).pc + 4 = 192
    rw [hp1]
    decide +kernel
  have hp3 : (lowerSquareState s).pc = 196 := by
    change (lowerState s).pc + 4 = 196
    rw [hp2]
    decide +kernel
  have hp4 : (compareState (lowerSquareState s)).pc = 200 := by
    change (lowerSquareState s).pc + 4 = 200
    rw [hp3]
    decide +kernel
  have hstep : step 0x540001a3 (compareState (lowerSquareState s)) = some (lowerTestState s) := by
    rw [step_branch_lower (compareState (lowerSquareState s)) hc]
    simp only [lowerTestState, hp4]
    rfl
  calc
    run sqrt32Code 224 (fuel + 5) s = run sqrt32Code 224 (fuel + 4) (doubleState s) :=
      run_step _ _ _ _ _ 0x0b000002
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step_double_candidate s hc)
    _ = run sqrt32Code 224 (fuel + 3) (lowerState s) :=
      run_step _ _ _ _ _ 0x51000442
        (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
        (by rw [hp1]; decide +kernel) (step_lower_midpoint (doubleState s) hc)
    _ = run sqrt32Code 224 (fuel + 2) (lowerSquareState s) :=
      run_step _ _ _ _ _ 0x9ba27c42
        (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
        (by rw [hp2]; decide +kernel) (step_square_midpoint (lowerState s) hc)
    _ = run sqrt32Code 224 (fuel + 1) (compareState (lowerSquareState s)) :=
      run_step _ _ _ _ _ 0xeb02007f
        (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel)
        (by rw [hp3]; decide +kernel) (step_compare_midpoint (lowerSquareState s) hc)
    _ = run sqrt32Code 224 fuel (lowerTestState s) :=
      run_step _ _ _ _ _ 0x540001a3
        (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel)
        (by rw [hp4]; decide +kernel) hstep

theorem lower_square_frame (s : Machine) :
    (lowerSquareState s).readX 3 = s.readX 3 ∧
      (lowerSquareState s).readW 0 = s.readW 0 := by
  have hf (i : Nat) (hi : i < 31) (hne : 2 ≠ i) :
      (lowerSquareState s).readX i = s.readX i := by
    unfold lowerSquareState
    rw [Machine.readX_writeX_ne _ 2 i (by decide) hi hne]
    change (lowerState s).readX i = s.readX i
    unfold lowerState
    rw [Machine.readX_writeW_ne _ 2 i (by decide) hi hne]
    change (doubleState s).readX i = s.readX i
    unfold doubleState
    rw [Machine.readX_writeW_ne _ 2 i (by decide) hi hne]
    rfl
  exact ⟨hf 3 (by decide) (by decide), congrArg UInt64.toUInt32 (hf 0 (by decide) (by decide))⟩

theorem lower_test_pc (s : Machine) (hs : s.x.size = 32) (n : Nat)
    (hn : (s.readX 3).toNat = 4 * n)
    (lo : 0 < (s.readW 0).toNat) (hi : (s.readW 0).toNat ≤ 2 ^ 24) :
    (lowerTestState s).pc =
      if 4 * n < (2 * (s.readW 0).toNat - 1) ^ 2 then 252 else 204 := by
  have hv := lower_square_block_value s hs lo hi
  have hf := (lower_square_frame s).1
  have hcarry : (compareState (lowerSquareState s)).carry = true ↔
      (2 * (s.readW 0).toNat - 1) ^ 2 ≤ 4 * n := by
    change decide ((lowerSquareState s).readX 3 ≥ (lowerSquareState s).readX 2) = true ↔ _
    rw [decide_eq_true_eq]
    change ((lowerSquareState s).readX 2).toNat ≤ ((lowerSquareState s).readX 3).toNat ↔ _
    rw [hv, hf, hn]
  change (if !(compareState (lowerSquareState s)).carry then 252 else 204) = _
  by_cases hl : 4 * n < (2 * (s.readW 0).toNat - 1) ^ 2
  · have hc : (compareState (lowerSquareState s)).carry = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have h := hcarry.mp h
      omega
    simp only [hc, Bool.not_false, ite_true, hl]
  · have hc : (compareState (lowerSquareState s)).carry = true := hcarry.mpr (by omega)
    simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false, hl]

theorem lower_test_frame (s : Machine) :
    (lowerTestState s).readX 3 = s.readX 3 ∧
      (lowerTestState s).readW 0 = s.readW 0 ∧
      (lowerTestState s).fpcr = s.fpcr ∧ (lowerTestState s).x.size = s.x.size := by
  have hf := lower_square_frame s
  have hx : (lowerTestState s).x = (lowerSquareState s).x := rfl
  refine ⟨(Machine.readX_congr _ _ hx 3).trans hf.1,
    (Machine.readW_congr _ _ hx 0).trans hf.2, rfl, ?_⟩
  have h1 : (doubleState s).x.size = s.x.size := by simp [doubleState, Machine.writeW]
  have h2 : (lowerState s).x.size = (doubleState s).x.size := by simp [lowerState, Machine.writeW]
  have h3 : (lowerSquareState s).x.size = (lowerState s).x.size := by
    simp [lowerSquareState, Machine.writeX]
  rw [hx]
  exact h3.trans (h2.trans h1)


def upperState (s : Machine) : Machine :=
  let t := doubleState s
  ({t with pc := t.pc + 4} : Machine).writeW 2 (t.readW 2 + 1)

def upperSquareState (s : Machine) : Machine :=
  let t := upperState s
  ({t with pc := t.pc + 4} : Machine).writeX 2
    ((t.readW 2).toUInt64 * (t.readW 2).toUInt64)

def upperTestState (s : Machine) : Machine :=
  let t := compareState (upperSquareState s)
  { t with pc := if t.carry && !t.zero then 260 else 224 }

theorem upper_test_run (s : Machine) (hpc : s.pc = 204)
    (hc : supportedControls s.fpcr = true) (fuel : Nat) :
    run sqrt32Code 224 (fuel + 5) s = run sqrt32Code 224 fuel (upperTestState s) := by
  have hp1 : (doubleState s).pc = 208 := by
    change s.pc + 4 = 208
    rw [hpc]
    decide +kernel
  have hp2 : (upperState s).pc = 212 := by
    change (doubleState s).pc + 4 = 212
    rw [hp1]
    decide +kernel
  have hp3 : (upperSquareState s).pc = 216 := by
    change (upperState s).pc + 4 = 216
    rw [hp2]
    decide +kernel
  have hp4 : (compareState (upperSquareState s)).pc = 220 := by
    change (upperSquareState s).pc + 4 = 220
    rw [hp3]
    decide +kernel
  have hstep : step 0x54000148 (compareState (upperSquareState s)) = some (upperTestState s) := by
    rw [step_branch_upper (compareState (upperSquareState s)) hc]
    simp only [upperTestState, hp4]
    rfl
  calc
    run sqrt32Code 224 (fuel + 5) s = run sqrt32Code 224 (fuel + 4) (doubleState s) :=
      run_step _ _ _ _ _ 0x0b000002
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step_double_candidate s hc)
    _ = run sqrt32Code 224 (fuel + 3) (upperState s) :=
      run_step _ _ _ _ _ 0x11000442
        (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
        (by rw [hp1]; decide +kernel) (step_upper_midpoint (doubleState s) hc)
    _ = run sqrt32Code 224 (fuel + 2) (upperSquareState s) :=
      run_step _ _ _ _ _ 0x9ba27c42
        (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
        (by rw [hp2]; decide +kernel) (step_square_midpoint (upperState s) hc)
    _ = run sqrt32Code 224 (fuel + 1) (compareState (upperSquareState s)) :=
      run_step _ _ _ _ _ 0xeb02007f
        (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel)
        (by rw [hp3]; decide +kernel) (step_compare_midpoint (upperSquareState s) hc)
    _ = run sqrt32Code 224 fuel (upperTestState s) :=
      run_step _ _ _ _ _ 0x54000148
        (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel)
        (by rw [hp4]; decide +kernel) hstep

theorem upper_square_frame (s : Machine) :
    (upperSquareState s).readX 3 = s.readX 3 ∧
      (upperSquareState s).readW 0 = s.readW 0 := by
  have hf (i : Nat) (hi : i < 31) (hne : 2 ≠ i) :
      (upperSquareState s).readX i = s.readX i := by
    unfold upperSquareState
    rw [Machine.readX_writeX_ne _ 2 i (by decide) hi hne]
    change (upperState s).readX i = s.readX i
    unfold upperState
    rw [Machine.readX_writeW_ne _ 2 i (by decide) hi hne]
    change (doubleState s).readX i = s.readX i
    unfold doubleState
    rw [Machine.readX_writeW_ne _ 2 i (by decide) hi hne]
    rfl
  exact ⟨hf 3 (by decide) (by decide), congrArg UInt64.toUInt32 (hf 0 (by decide) (by decide))⟩


theorem upper_square_block_value (s : Machine) (hs : s.x.size = 32)
    (hi : (s.readW 0).toNat ≤ 2 ^ 24) :
    ((upperSquareState s).readX 2).toNat = (2 * (s.readW 0).toNat + 1) ^ 2 := by
  have hs1 : (doubleState s).x.size = 32 := by
    simpa [doubleState, Machine.writeW] using hs
  have hs2 : (upperState s).x.size = 32 := by
    simpa [upperState, Machine.writeW] using hs1
  have hr1 : (doubleState s).readW 2 = s.readW 0 + s.readW 0 :=
    Machine.readW_writeW_same _ 2 (by decide) hs _
  have hr2 : (upperState s).readW 2 = (doubleState s).readW 2 + 1 :=
    Machine.readW_writeW_same _ 2 (by decide) hs1 _
  have hr3 : (upperSquareState s).readX 2 =
      ((upperState s).readW 2).toUInt64 * ((upperState s).readW 2).toUInt64 :=
    Machine.readX_writeX_same _ 2 (by decide) hs2 _
  rw [hr3, hr2, hr1]
  exact upper_midpoint_square_exact _ hi


theorem upper_test_pc (s : Machine) (hs : s.x.size = 32) (n : Nat)
    (hn : (s.readX 3).toNat = 4 * n) (hi : (s.readW 0).toNat ≤ 2 ^ 24) :
    (upperTestState s).pc =
      if (2 * (s.readW 0).toNat + 1) ^ 2 < 4 * n then 260 else 224 := by
  have hv := upper_square_block_value s hs hi
  have hf := (upper_square_frame s).1
  have hcarry : (compareState (upperSquareState s)).carry = true ↔
      (2 * (s.readW 0).toNat + 1) ^ 2 ≤ 4 * n := by
    change decide ((upperSquareState s).readX 3 ≥ (upperSquareState s).readX 2) = true ↔ _
    rw [decide_eq_true_eq]
    change ((upperSquareState s).readX 2).toNat ≤ ((upperSquareState s).readX 3).toNat ↔ _
    rw [hv, hf, hn]
  have hzero : (compareState (upperSquareState s)).zero = true ↔
      4 * n = (2 * (s.readW 0).toNat + 1) ^ 2 := by
    change ((upperSquareState s).readX 3 - (upperSquareState s).readX 2 == 0) = true ↔ _
    rw [beq_iff_eq, UInt64.sub_eq_iff_eq_add, UInt64.zero_add, ← UInt64.toNat_inj, hv, hf, hn]
  have hcond : ((compareState (upperSquareState s)).carry &&
      !(compareState (upperSquareState s)).zero) = true ↔
      (2 * (s.readW 0).toNat + 1) ^ 2 < 4 * n := by
    rw [Bool.and_eq_true_iff, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, hcarry, hzero]
    omega
  change (if (compareState (upperSquareState s)).carry &&
    !(compareState (upperSquareState s)).zero then 260 else 224) = _
  by_cases ht : (2 * (s.readW 0).toNat + 1) ^ 2 < 4 * n
  · have hc := hcond.mpr ht
    simp only [hc, ite_true, ht]
  · have hc : ((compareState (upperSquareState s)).carry &&
        !(compareState (upperSquareState s)).zero) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact ht (hcond.mp h)
    simp only [hc, Bool.false_eq_true, ite_false, ht]

theorem upper_test_frame (s : Machine) :
    (upperTestState s).readX 3 = s.readX 3 ∧
      (upperTestState s).readW 0 = s.readW 0 ∧
      (upperTestState s).fpcr = s.fpcr ∧ (upperTestState s).x.size = s.x.size := by
  have hf := upper_square_frame s
  have hx : (upperTestState s).x = (upperSquareState s).x := rfl
  refine ⟨(Machine.readX_congr _ _ hx 3).trans hf.1,
    (Machine.readW_congr _ _ hx 0).trans hf.2, rfl, ?_⟩
  have h1 : (doubleState s).x.size = s.x.size := by simp [doubleState, Machine.writeW]
  have h2 : (upperState s).x.size = (doubleState s).x.size := by simp [upperState, Machine.writeW]
  have h3 : (upperSquareState s).x.size = (upperState s).x.size := by
    simp [upperSquareState, Machine.writeX]
  rw [hx]
  exact h3.trans (h2.trans h1)


def adjustStepState (s : Machine) (q : UInt32) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeW 0 q

def adjustLoopState (s : Machine) (q : UInt32) : Machine :=
  { s.writeW 0 q with pc := 184 }

theorem decrement_run (s : Machine) (hpc : s.pc = 252)
    (hc : supportedControls s.fpcr = true) (fuel : Nat) :
    run sqrt32Code 224 (fuel + 2) s =
      run sqrt32Code 224 fuel (adjustLoopState s (s.readW 0 - 1)) := by
  have hp : (adjustStepState s (s.readW 0 - 1)).pc = 256 := by
    change s.pc + 4 = 256
    rw [hpc]
    decide +kernel
  have hb : step 0x17ffffee (adjustStepState s (s.readW 0 - 1)) =
      some (adjustLoopState s (s.readW 0 - 1)) := by
    rw [step_back_lower (adjustStepState s (s.readW 0 - 1)) hc, hp]
    rfl
  calc
    run sqrt32Code 224 (fuel + 2) s =
        run sqrt32Code 224 (fuel + 1) (adjustStepState s (s.readW 0 - 1)) :=
      run_step _ _ _ _ _ 0x51000400
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step_decrement_candidate s hc)
    _ = run sqrt32Code 224 fuel (adjustLoopState s (s.readW 0 - 1)) :=
      run_step _ _ _ _ _ 0x17ffffee
        (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel)
        (by rw [hp]; decide +kernel) hb

theorem increment_run (s : Machine) (hpc : s.pc = 260)
    (hc : supportedControls s.fpcr = true) (fuel : Nat) :
    run sqrt32Code 224 (fuel + 2) s =
      run sqrt32Code 224 fuel (adjustLoopState s (s.readW 0 + 1)) := by
  have hp : (adjustStepState s (s.readW 0 + 1)).pc = 264 := by
    change s.pc + 4 = 264
    rw [hpc]
    decide +kernel
  have hb : step 0x17ffffec (adjustStepState s (s.readW 0 + 1)) =
      some (adjustLoopState s (s.readW 0 + 1)) := by
    rw [step_back_upper (adjustStepState s (s.readW 0 + 1)) hc, hp]
    rfl
  calc
    run sqrt32Code 224 (fuel + 2) s =
        run sqrt32Code 224 (fuel + 1) (adjustStepState s (s.readW 0 + 1)) :=
      run_step _ _ _ _ _ 0x11000400
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step_increment_candidate s hc)
    _ = run sqrt32Code 224 fuel (adjustLoopState s (s.readW 0 + 1)) :=
      run_step _ _ _ _ _ 0x17ffffec
        (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel)
        (by rw [hp]; decide +kernel) hb

theorem adjust_loop_frame (s : Machine) (q : UInt32) (hs : s.x.size = 32) :
    (adjustLoopState s q).readW 0 = q ∧
      (adjustLoopState s q).readX 3 = s.readX 3 ∧
      (adjustLoopState s q).fpcr = s.fpcr ∧ (adjustLoopState s q).x.size = s.x.size := by
  have hx : (adjustLoopState s q).x = (s.writeW 0 q).x := rfl
  refine ⟨(Machine.readW_congr _ _ hx 0).trans (Machine.readW_writeW_same s 0 (by decide) hs q),
    (Machine.readX_congr _ _ hx 3).trans (Machine.readX_writeW_ne s 0 3 (by decide) (by decide) (by decide) q),
    rfl, ?_⟩
  simp [adjustLoopState, Machine.writeW]

end VerifiedSqrt.Arm
