module

public import VerifiedSqrt.Arm.Scale32

@[expose] public section

namespace VerifiedSqrt.Arm

def prepare1 (s : Machine) : Machine := s.advanceW 4 0

def prepare2 (s : Machine) : Machine :=
  let s := prepare1 s
  s.advanceW 1 (UInt32.ofNat ((s.readW 0).toNat / 2 ^ 23 % 256))

def prepared (s : Machine) (pc : UInt64) : Machine := {prepare2 s with pc := pc}

theorem prepare_two (s : Machine) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (fuel : Nat) :
    run sqrt32Code 68 (fuel + 2) s = run sqrt32Code 68 fuel (prepare2 s) := by
  have hp1 : (prepare1 s).pc = 36 := by rw [prepare1, Machine.advanceW_pc, hpc]; decide +kernel
  have hc1 : supportedControls (prepare1 s).fpcr = true := by
    rw [prepare1, Machine.advanceW_fpcr]; exact hc
  calc
    _ = run sqrt32Code 68 (fuel + 1) (prepare1 s) :=
      run_step _ _ _ _ _ 0x52800004
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step_scale_zero s hc)
    _ = _ := run_step _ _ _ _ _ 0x53177801
      (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
      (by rw [hp1]; decide +kernel) (step_input_exponent (prepare1 s) hc1)

theorem prepare2_pc (s : Machine) (hpc : s.pc = 32) : (prepare2 s).pc = 40 := by
  rw [prepare2, Machine.advanceW_pc, prepare1, Machine.advanceW_pc, hpc]
  decide +kernel

theorem prepare2_fpcr (s : Machine) : (prepare2 s).fpcr = s.fpcr := by
  rw [prepare2, Machine.advanceW_fpcr, prepare1, Machine.advanceW_fpcr]

theorem prepare2_exponent (s : Machine) (hs : s.x.size = 32) :
    (prepare2 s).readW 1 = UInt32.ofNat (exponent32 (s.readW 0)) := by
  simp [prepare2, prepare1, Machine.readW_advanceW_same, Machine.readW_advanceW_ne,
    Machine.advanceW_size, hs, exponent32_eq_div]

theorem prepare_normal_run (s : Machine) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (he : exponent32 (s.readW 0) ≠ 0) :
    run sqrt32Code 68 3 s = some (prepared s 68) := by
  have hp := prepare2_pc s hpc
  have hc2 : supportedControls (prepare2 s).fpcr = true := by rw [prepare2_fpcr]; exact hc
  have hn : UInt32.ofNat (exponent32 (s.readW 0)) ≠ 0 := by
    intro h
    have hn := congrArg UInt32.toNat h
    have hb := exponent32_lt (s.readW 0)
    rw [UInt32.toNat_ofNat'] at hn
    change exponent32 (s.readW 0) % 2 ^ 32 = 0 at hn
    omega
  have hb : step 0x350000e1 (prepare2 s) = some (prepared s 68) := by
    rw [step_input_normal _ hc2, prepare2_exponent s hs, hp]
    simp only [bne_iff_ne]
    rw [ite_eq_left hn]
    rfl
  rw [prepare_two s hpc hc 1,
    run_step _ _ 0 _ _ 0x350000e1 (by rw [hp]; decide +kernel)
      (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel) hb]
  exact run_at_stop _ _ _ _ rfl

theorem prepare_subnormal_run (s : Machine) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (he : exponent32 (s.readW 0) = 0) :
    run sqrt32Code 68 9 s = some (scale6 (prepared s 44)) := by
  have hp := prepare2_pc s hpc
  have hc2 : supportedControls (prepare2 s).fpcr = true := by rw [prepare2_fpcr]; exact hc
  have hb : step 0x350000e1 (prepare2 s) = some (prepared s 44) := by
    rw [step_input_normal _ hc2, prepare2_exponent s hs, he, hp]
    rfl
  rw [prepare_two s hpc hc 7,
    run_step _ _ 6 _ _ 0x350000e1 (by rw [hp]; decide +kernel)
      (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel) hb]
  exact scale_run (prepared s 44) rfl hc2

theorem prepared_word (s : Machine) (pc : UInt64) : (prepared s pc).readW 0 = s.readW 0 := by
  change (prepare2 s).readW 0 = _
  simp [prepare2, prepare1, Machine.readW_advanceW_ne]

theorem prepared_scalar (s : Machine) (pc : UInt64) : (prepared s pc).readS 0 = s.readS 0 := by
  change (prepare2 s).readS 0 = _
  simp only [prepare2, prepare1, Machine.readS_advanceW]

theorem prepared_exponent (s : Machine) (pc : UInt64) (hs : s.x.size = 32) :
    (prepared s pc).readW 1 = UInt32.ofNat (exponent32 ((prepared s pc).readW 0)) := by
  rw [prepared_word]
  exact prepare2_exponent s hs

theorem prepared_scale (s : Machine) (pc : UInt64) (hs : s.x.size = 32) :
    (prepared s pc).readW 4 = UInt32.ofInt 0 := by
  change (prepare2 s).readW 4 = _
  simp only [prepare2, prepare1, Machine.readW_advanceW_same, Machine.readW_advanceW_ne,
    hs, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  decide +kernel

theorem prepared_properties (s : Machine) (pc : UInt64) :
    (prepared s pc).fpcr = s.fpcr ∧ (prepared s pc).fpsr = s.fpsr ∧
      (prepared s pc).x.size = s.x.size ∧ (prepared s pc).v = s.v ∧
      ∀ r, 5 ≤ r → r < 31 → (prepared s pc).readX r = s.readX r := by
  refine ⟨prepare2_fpcr s, ?_, ?_, ?_, ?_⟩
  · change (prepare2 s).fpsr = _
    simp only [prepare2, prepare1, Machine.advanceW_fpsr]
  · change (prepare2 s).x.size = _
    simp only [prepare2, prepare1, Machine.advanceW_size]
  · change (prepare2 s).v = _
    simp only [prepare2, prepare1, Machine.advanceW_vectors]
  · intro r hr hr'
    change (prepare2 s).readX r = _
    have h1 : 1 ≠ r := by omega
    have h4 : 4 ≠ r := by omega
    simp [prepare2, prepare1, Machine.readX_advanceW_ne, hr', h1, h4]

end VerifiedSqrt.Arm
