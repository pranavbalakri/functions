module

public import VerifiedSqrt.Arm.InputInstructions
public import VerifiedSqrt.Arm.NaNControl32
public import VerifiedSqrt.Arm.Execution
public import VerifiedSqrt.Sqrt.Subnormal32

@[expose] public section

namespace VerifiedSqrt.Arm

def scale1 (s : Machine) : Machine :=
  s.advanceW 2 0x57800000

def scale2 (s : Machine) : Machine :=
  let s := scale1 s
  s.advanceS 1 (s.readW 2)

def scale3 (s : Machine) : Machine :=
  let s := scale2 s
  s.advanceFP 0 (mul32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0) (s.readS 1))

def scale4 (s : Machine) : Machine :=
  let s := scale3 s
  s.advanceW 0 (s.readS 0)

def scale5 (s : Machine) : Machine :=
  let s := scale4 s
  s.advanceW 1 (UInt32.ofNat ((s.readW 0).toNat / 2 ^ 23 % 256))

def scale6 (s : Machine) : Machine :=
  let s := scale5 s
  s.advanceW 4 (UInt32.ofInt (-24))

theorem scale_run (s : Machine) (hpc : s.pc = 44)
    (hc : supportedControls s.fpcr = true) :
    run sqrt32Code 68 6 s = some (scale6 s) := by
  have hp1 : (scale1 s).pc = 48 := by
    rw [scale1, Machine.advanceW_pc, hpc]
    decide +kernel
  have hc1 : supportedControls (scale1 s).fpcr = true := by
    rw [scale1, Machine.advanceW_fpcr]
    exact hc
  have hp2 : (scale2 s).pc = 52 := by
    rw [scale2, Machine.advanceS_pc, hp1]
    decide +kernel
  have hc2 : supportedControls (scale2 s).fpcr = true := by
    rw [scale2, Machine.advanceS_fpcr]
    exact hc1
  have hp3 : (scale3 s).pc = 56 := by
    rw [scale3, Machine.advanceFP_pc, hp2]
    decide +kernel
  have hc3 : supportedControls (scale3 s).fpcr = true := by
    rw [scale3, Machine.advanceFP_fpcr]
    exact hc2
  have hp4 : (scale4 s).pc = 60 := by
    rw [scale4, Machine.advanceW_pc, hp3]
    decide +kernel
  have hc4 : supportedControls (scale4 s).fpcr = true := by
    rw [scale4, Machine.advanceW_fpcr]
    exact hc3
  have hp5 : (scale5 s).pc = 64 := by
    rw [scale5, Machine.advanceW_pc, hp4]
    decide +kernel
  have hc5 : supportedControls (scale5 s).fpcr = true := by
    rw [scale5, Machine.advanceW_fpcr]
    exact hc4
  have hp6 : (scale6 s).pc = 68 := by
    rw [scale6, Machine.advanceW_pc, hp5]
    decide +kernel
  calc
    run sqrt32Code 68 6 s = run sqrt32Code 68 5 (scale1 s) :=
      run_step _ _ _ _ _ 0x52aaf002
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step_scale_bits s hc)
    _ = run sqrt32Code 68 4 (scale2 s) :=
      run_step _ _ _ _ _ 0x1e270041
        (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
        (by rw [hp1]; decide +kernel) (step_scale_scalar (scale1 s) hc1)
    _ = run sqrt32Code 68 3 (scale3 s) :=
      run_step _ _ _ _ _ 0x1e210800
        (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
        (by rw [hp2]; decide +kernel) (step_scale_multiply (scale2 s) hc2)
    _ = run sqrt32Code 68 2 (scale4 s) :=
      run_step _ _ _ _ _ 0x1e260000
        (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel)
        (by rw [hp3]; decide +kernel) (step_scalar_to_word (scale3 s) hc3)
    _ = run sqrt32Code 68 1 (scale5 s) :=
      run_step _ _ _ _ _ 0x53177801
        (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel)
        (by rw [hp4]; decide +kernel) (step_input_exponent (scale4 s) hc4)
    _ = run sqrt32Code 68 0 (scale6 s) :=
      run_step _ _ _ _ _ 0x128002e4
        (by rw [hp5]; decide +kernel) (by rw [hp5]; decide +kernel)
        (by rw [hp5]; decide +kernel) (step_scale_exponent (scale5 s) hc5)
    _ = some (scale6 s) := run_at_stop _ _ _ _ hp6

attribute [local simp] Machine.advanceW_size Machine.advanceW_vectors Machine.advanceW_fpcr
  Machine.advanceS_registers Machine.advanceS_vector_size Machine.advanceS_fpcr
  Machine.advanceFP_registers Machine.advanceFP_vector_size Machine.advanceFP_fpcr
  Machine.readW_advanceW_same Machine.readW_advanceW_ne Machine.readX_advanceW_ne
  Machine.readW_advanceS Machine.readW_advanceFP Machine.readX_advanceS Machine.readX_advanceFP
  Machine.readS_advanceW Machine.readS_advanceS_same Machine.readS_advanceS_ne
  Machine.readS_advanceFP_same

theorem scale_pc (s : Machine) (hpc : s.pc = 44) : (scale6 s).pc = 68 := by
  simp only [scale6, scale5, scale4, scale3, scale2, scale1,
    Machine.advanceW_pc, Machine.advanceS_pc, Machine.advanceFP_pc, hpc]
  decide +kernel

theorem scale_word (s : Machine) (hs : s.WellFormed) :
    (scale6 s).readW 0 = (mul32 (s.fpcr &&& 0x02000000 != 0) (s.readS 0) 0x57800000).bits := by
  simp [scale6, scale5, scale4, scale3, scale2, scale1, hs.1, hs.2]

theorem scale_word_subnormal (s : Machine) (hs : s.WellFormed)
    (lo : 0 < (s.readS 0).toNat) (hi : (s.readS 0).toNat < 2 ^ 23) :
    (scale6 s).readW 0 = Sqrt.scaleSubnormal32 (s.readS 0) := by
  have hn := (positive_finite32_classify (s.readS 0) lo (by omega)).2.2.1
  rw [scale_word s hs, mul32_dn_independent _ _ _ hn (by decide +kernel)]
  rfl

theorem scale_exponent (s : Machine) (hs : s.x.size = 32) :
    (scale6 s).readW 1 = UInt32.ofNat (exponent32 ((scale6 s).readW 0)) := by
  simp [scale6, scale5, scale4, scale3, scale2, scale1, exponent32_eq_div, hs]

theorem scale_saved_exponent (s : Machine) (hs : s.x.size = 32) :
    (scale6 s).readW 4 = UInt32.ofInt (-24) := by
  simp [scale6, scale5, scale4, scale3, scale2, scale1, hs]

theorem scale_properties (s : Machine) :
    (scale6 s).fpcr = s.fpcr ∧ (scale6 s).x.size = s.x.size ∧
      (scale6 s).v.size = s.v.size ∧
      (∀ r, 5 ≤ r → r < 31 → (scale6 s).readX r = s.readX r) ∧
      (∀ r, 2 ≤ r → (scale6 s).v[r]! = s.v[r]!) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [scale6, scale5, scale4, scale3, scale2, scale1,
      Machine.advanceW_fpcr, Machine.advanceS_fpcr, Machine.advanceFP_fpcr]
  · simp only [scale6, scale5, scale4, scale3, scale2, scale1,
      Machine.advanceW_size, Machine.advanceS_registers, Machine.advanceFP_registers]
  · simp only [scale6, scale5, scale4, scale3, scale2, scale1,
      Machine.advanceW_vectors, Machine.advanceS_vector_size, Machine.advanceFP_vector_size]
  · intro r hr hr'
    have h0 : 0 ≠ r := by omega
    have h1 : 1 ≠ r := by omega
    have h2 : 2 ≠ r := by omega
    have h4 : 4 ≠ r := by omega
    simp [scale6, scale5, scale4, scale3, scale2, scale1, hr', h0, h1, h2, h4]
  · intro r hr
    have h0 : 0 ≠ r := by omega
    have h1 : 1 ≠ r := by omega
    simp only [scale6, scale5, scale4, scale3, scale2, scale1,
      Machine.advanceW_vectors, Machine.vector_advanceS_ne _ _ _ h1,
      Machine.vector_advanceFP_ne _ _ _ h0]

end VerifiedSqrt.Arm
