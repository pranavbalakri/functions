module

public import VerifiedSqrt.Arm.InputInstructions64
public import VerifiedSqrt.Arm.NaNControl64
public import VerifiedSqrt.Arm.Execution64
public import VerifiedSqrt.Sqrt.Subnormal64

@[expose] public section

namespace VerifiedSqrt.Arm

def scale64_1 (s : Machine) : Machine :=
  s.advanceX 2 0x4690000000000000

def scale64_2 (s : Machine) : Machine :=
  let s := scale64_1 s
  s.advanceD 1 (s.readX 2)

def scale64_3 (s : Machine) : Machine :=
  let s := scale64_2 s
  s.advanceFP64 0 (mul64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0) (s.readD 1))

def scale64_4 (s : Machine) : Machine :=
  let s := scale64_3 s
  s.advanceX 0 (s.readD 0)

def scale64_5 (s : Machine) : Machine :=
  let s := scale64_4 s
  s.advanceX 1 (UInt64.ofNat ((s.readX 0).toNat / 2 ^ 52 % 2048))

def scale64_6 (s : Machine) : Machine :=
  let s := scale64_5 s
  s.advanceW 4 (UInt32.ofInt (-53))

theorem scale64_run (s : Machine) (hpc : s.pc = 44)
    (hc : supportedControls s.fpcr = true) :
    run64 sqrt64Code 0 68 6 s = some (scale64_6 s) := by
  have hp1 : (scale64_1 s).pc = 48 := by
    rw [scale64_1, Machine.advanceX_pc, hpc]
    decide +kernel
  have hc1 : supportedControls (scale64_1 s).fpcr = true := by
    rw [scale64_1, Machine.advanceX_fpcr]
    exact hc
  have hp2 : (scale64_2 s).pc = 52 := by
    rw [scale64_2, Machine.advanceD_pc, hp1]
    decide +kernel
  have hc2 : supportedControls (scale64_2 s).fpcr = true := by
    rw [scale64_2, Machine.advanceD_fpcr]
    exact hc1
  have hp3 : (scale64_3 s).pc = 56 := by
    rw [scale64_3, Machine.advanceFP64_pc, hp2]
    decide +kernel
  have hc3 : supportedControls (scale64_3 s).fpcr = true := by
    rw [scale64_3, Machine.advanceFP64_fpcr]
    exact hc2
  have hp4 : (scale64_4 s).pc = 60 := by
    rw [scale64_4, Machine.advanceX_pc, hp3]
    decide +kernel
  have hc4 : supportedControls (scale64_4 s).fpcr = true := by
    rw [scale64_4, Machine.advanceX_fpcr]
    exact hc3
  have hp5 : (scale64_5 s).pc = 64 := by
    rw [scale64_5, Machine.advanceX_pc, hp4]
    decide +kernel
  have hc5 : supportedControls (scale64_5 s).fpcr = true := by
    rw [scale64_5, Machine.advanceX_fpcr]
    exact hc4
  have hp6 : (scale64_6 s).pc = 68 := by
    rw [scale64_6, Machine.advanceW_pc, hp5]
    decide +kernel
  calc
    run64 sqrt64Code 0 68 6 s = run64 sqrt64Code 0 68 5 (scale64_1 s) :=
      run64_step _ _ _ _ _ _ 0xd2e8d202
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step64_scale_bits s hc)
    _ = run64 sqrt64Code 0 68 4 (scale64_2 s) :=
      run64_step _ _ _ _ _ _ 0x9e670041
        (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
        (by rw [hp1]; decide +kernel) (step64_scale_scalar (scale64_1 s) hc1)
    _ = run64 sqrt64Code 0 68 3 (scale64_3 s) :=
      run64_step _ _ _ _ _ _ 0x1e610800
        (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
        (by rw [hp2]; decide +kernel) (step64_scale_multiply (scale64_2 s) hc2)
    _ = run64 sqrt64Code 0 68 2 (scale64_4 s) :=
      run64_step _ _ _ _ _ _ 0x9e660000
        (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel)
        (by rw [hp3]; decide +kernel) (step64_setup_10 (scale64_3 s) hc3)
    _ = run64 sqrt64Code 0 68 1 (scale64_5 s) :=
      run64_step _ _ _ _ _ _ 0xd374f801
        (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel)
        (by rw [hp4]; decide +kernel) (step64_input_exponent (scale64_4 s) hc4)
    _ = run64 sqrt64Code 0 68 0 (scale64_6 s) :=
      run64_step _ _ _ _ _ _ 0x12800684
        (by rw [hp5]; decide +kernel) (by rw [hp5]; decide +kernel)
        (by rw [hp5]; decide +kernel) (step64_scale_exponent (scale64_5 s) hc5)
    _ = some (scale64_6 s) := run64_at_stop _ _ _ _ _ hp6

attribute [local simp] Machine.readW_advanceW_ne Machine.advanceW_size Machine.advanceW_vectors Machine.advanceW_fpcr Machine.readW_advanceW_same Machine.readW_advanceX_ne Machine.readW_advanceX_same Machine.readX_advanceW_ne Machine.readD_advanceW
  Machine.advanceX_size Machine.advanceX_vectors Machine.advanceX_fpcr
  Machine.advanceD_registers Machine.advanceD_vector_size Machine.advanceD_fpcr
  Machine.advanceFP64_registers Machine.advanceFP64_vector_size Machine.advanceFP64_fpcr
  Machine.readX_advanceX_same Machine.readX_advanceX_ne Machine.readX_advanceX_ne
  Machine.readX_advanceD Machine.readX_advanceFP64 Machine.readX_advanceD Machine.readX_advanceFP64
  Machine.readD_advanceX Machine.readD_advanceD_same Machine.readD_advanceD_ne
  Machine.readD_advanceFP64_same

theorem scale64_pc (s : Machine) (hpc : s.pc = 44) : (scale64_6 s).pc = 68 := by
  simp only [scale64_6, scale64_5, scale64_4, scale64_3, scale64_2, scale64_1,
    Machine.advanceW_pc, Machine.advanceX_pc, Machine.advanceD_pc, Machine.advanceFP64_pc, hpc]
  decide +kernel

theorem scale64_word (s : Machine) (hs : s.WellFormed) :
    (scale64_6 s).readX 0 = (mul64 (s.fpcr &&& 0x02000000 != 0) (s.readD 0) 0x4690000000000000).bits := by
  simp [scale64_6, scale64_5, scale64_4, scale64_3, scale64_2, scale64_1, hs.1, hs.2]

theorem scale64_word_subnormal (s : Machine) (hs : s.WellFormed)
    (lo : 0 < (s.readD 0).toNat) (hi : (s.readD 0).toNat < 2 ^ 52) :
    (scale64_6 s).readX 0 = Sqrt.scaleSubnormal64 (s.readD 0) := by
  have hn := (positive_finite64_classify (s.readD 0) lo (by omega)).2.2.1
  rw [scale64_word s hs, mul64_dn_independent _ _ _ hn (by decide +kernel)]
  rfl

theorem scale64_exponent (s : Machine) (hs : s.x.size = 32) :
    (scale64_6 s).readW 1 = UInt32.ofNat (exponent64 ((scale64_6 s).readX 0)) := by
  simp [scale64_6, scale64_5, scale64_4, scale64_3, scale64_2, scale64_1, exponent64_eq_div, hs]

theorem scale64_saved_exponent (s : Machine) (hs : s.x.size = 32) :
    (scale64_6 s).readW 4 = UInt32.ofInt (-53) := by
  simp [scale64_6, scale64_5, scale64_4, scale64_3, scale64_2, scale64_1, hs]

theorem scale64_properties (s : Machine) :
    (scale64_6 s).fpcr = s.fpcr ∧ (scale64_6 s).x.size = s.x.size ∧
      (scale64_6 s).v.size = s.v.size ∧
      (∀ r, 5 ≤ r → r < 31 → (scale64_6 s).readX r = s.readX r) ∧
      (∀ r, 2 ≤ r → (scale64_6 s).v[r]! = s.v[r]!) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [scale64_6, scale64_5, scale64_4, scale64_3, scale64_2, scale64_1,
      Machine.advanceW_fpcr, Machine.advanceX_fpcr, Machine.advanceD_fpcr, Machine.advanceFP64_fpcr]
  · simp only [scale64_6, scale64_5, scale64_4, scale64_3, scale64_2, scale64_1,
      Machine.advanceW_size, Machine.advanceX_size, Machine.advanceD_registers, Machine.advanceFP64_registers]
  · simp only [scale64_6, scale64_5, scale64_4, scale64_3, scale64_2, scale64_1,
      Machine.advanceW_vectors, Machine.advanceX_vectors, Machine.advanceD_vector_size, Machine.advanceFP64_vector_size]
  · intro r hr hr'
    have h0 : 0 ≠ r := by omega
    have h1 : 1 ≠ r := by omega
    have h2 : 2 ≠ r := by omega
    have h4 : 4 ≠ r := by omega
    simp [scale64_6, scale64_5, scale64_4, scale64_3, scale64_2, scale64_1, hr', h0, h1, h2, h4]
  · intro r hr
    have h0 : 0 ≠ r := by omega
    have h1 : 1 ≠ r := by omega
    simp only [scale64_6, scale64_5, scale64_4, scale64_3, scale64_2, scale64_1,
      Machine.advanceW_vectors, Machine.advanceX_vectors, Machine.vector_advanceD_ne _ _ _ h1,
      Machine.vector_advanceFP64_ne _ _ _ h0]

end VerifiedSqrt.Arm
