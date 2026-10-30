module

public import VerifiedSqrt.Arm.Scale64

@[expose] public section

namespace VerifiedSqrt.Arm

def prepare64_1 (s : Machine) : Machine := s.advanceW 4 0

def prepare64_2 (s : Machine) : Machine :=
  let s := prepare64_1 s
  s.advanceX 1 (UInt64.ofNat ((s.readX 0).toNat / 2 ^ 52 % 2048))

def prepared64 (s : Machine) (pc : UInt64) : Machine := {prepare64_2 s with pc := pc}

theorem prepare64_two (s : Machine) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (fuel : Nat) :
    run64 sqrt64Code 0 68 (fuel + 2) s = run64 sqrt64Code 0 68 fuel (prepare64_2 s) := by
  have hp1 : (prepare64_1 s).pc = 36 := by rw [prepare64_1, Machine.advanceW_pc, hpc]; decide +kernel
  have hc1 : supportedControls (prepare64_1 s).fpcr = true := by
    rw [prepare64_1, Machine.advanceW_fpcr]; exact hc
  calc
    _ = run64 sqrt64Code 0 68 (fuel + 1) (prepare64_1 s) :=
      run64_step _ _ _ _ _ _ 0x52800004
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step64_scale_zero s hc)
    _ = _ := run64_step _ _ _ _ _ _ 0xd374f801
      (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
      (by rw [hp1]; decide +kernel) (step64_input_exponent (prepare64_1 s) hc1)

theorem prepare64_2_pc (s : Machine) (hpc : s.pc = 32) : (prepare64_2 s).pc = 40 := by
  rw [prepare64_2, Machine.advanceX_pc, prepare64_1, Machine.advanceW_pc, hpc]
  decide +kernel

theorem prepare64_2_fpcr (s : Machine) : (prepare64_2 s).fpcr = s.fpcr := by
  rw [prepare64_2, Machine.advanceX_fpcr, prepare64_1, Machine.advanceW_fpcr]

theorem prepare64_2_exponent (s : Machine) (hs : s.x.size = 32) :
    (prepare64_2 s).readX 1 = UInt64.ofNat (exponent64 (s.readX 0)) := by
  simp [prepare64_2, prepare64_1, Machine.readX_advanceX_same,
    Machine.advanceW_size, Machine.readX_advanceW_ne, hs, exponent64_eq_div]

theorem prepare64_normal_run (s : Machine) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (he : exponent64 (s.readX 0) ≠ 0) :
    run64 sqrt64Code 0 68 3 s = some (prepared64 s 68) := by
  have hp := prepare64_2_pc s hpc
  have hc2 : supportedControls (prepare64_2 s).fpcr = true := by rw [prepare64_2_fpcr]; exact hc
  have hn : UInt64.ofNat (exponent64 (s.readX 0)) ≠ 0 := by
    intro h
    have hn := congrArg UInt64.toNat h
    have hb := exponent64_lt (s.readX 0)
    rw [UInt64.toNat_ofNat'] at hn
    change exponent64 (s.readX 0) % 2 ^ 64 = 0 at hn
    omega
  have hb : step64 0xb50000e1 (prepare64_2 s) = some (prepared64 s 68) := by
    rw [step64_input_normal _ hc2, prepare64_2_exponent s hs, hp]
    simp only [bne_iff_ne]
    rw [ite_eq_left hn]
    rfl
  rw [prepare64_two s hpc hc 1,
    run64_step _ _ _ 0 _ _ 0xb50000e1 (by rw [hp]; decide +kernel)
      (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel) hb]
  exact run64_at_stop _ _ _ _ _ rfl

theorem prepare64_subnormal_run (s : Machine) (hpc : s.pc = 32)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (he : exponent64 (s.readX 0) = 0) :
    run64 sqrt64Code 0 68 9 s = some (scale64_6 (prepared64 s 44)) := by
  have hp := prepare64_2_pc s hpc
  have hc2 : supportedControls (prepare64_2 s).fpcr = true := by rw [prepare64_2_fpcr]; exact hc
  have hb : step64 0xb50000e1 (prepare64_2 s) = some (prepared64 s 44) := by
    rw [step64_input_normal _ hc2, prepare64_2_exponent s hs, he, hp]
    rfl
  rw [prepare64_two s hpc hc 7,
    run64_step _ _ _ 6 _ _ 0xb50000e1 (by rw [hp]; decide +kernel)
      (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel) hb]
  exact scale64_run (prepared64 s 44) rfl hc2

theorem prepared64_word (s : Machine) (pc : UInt64) : (prepared64 s pc).readX 0 = s.readX 0 := by
  change (prepare64_2 s).readX 0 = _
  simp [prepare64_2, prepare64_1, Machine.readX_advanceX_ne, Machine.readX_advanceW_ne]

theorem prepared64_scalar (s : Machine) (pc : UInt64) : (prepared64 s pc).readD 0 = s.readD 0 := by
  change (prepare64_2 s).readD 0 = _
  simp only [prepare64_2, prepare64_1, Machine.readD_advanceX, Machine.readD_advanceW]

theorem prepared64_exponent (s : Machine) (pc : UInt64) (hs : s.x.size = 32) :
    (prepared64 s pc).readW 1 = UInt32.ofNat (exponent64 ((prepared64 s pc).readX 0)) := by
  rw [prepared64_word]
  change ((prepare64_2 s).readX 1).toUInt32 = _
  rw [prepare64_2_exponent s hs, UInt64.toUInt32_ofNat']

theorem prepared64_scale (s : Machine) (pc : UInt64) (hs : s.x.size = 32) :
    (prepared64 s pc).readW 4 = UInt32.ofInt 0 := by
  change (prepare64_2 s).readW 4 = _
  simp only [prepare64_2, prepare64_1, Machine.readW_advanceW_same, Machine.readW_advanceX_ne,
    hs, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  decide +kernel

theorem prepared64_properties (s : Machine) (pc : UInt64) :
    (prepared64 s pc).fpcr = s.fpcr ∧ (prepared64 s pc).fpsr = s.fpsr ∧
      (prepared64 s pc).x.size = s.x.size ∧ (prepared64 s pc).v = s.v ∧
      ∀ r, 5 ≤ r → r < 31 → (prepared64 s pc).readX r = s.readX r := by
  refine ⟨prepare64_2_fpcr s, ?_, ?_, ?_, ?_⟩
  · change (prepare64_2 s).fpsr = _
    simp only [prepare64_2, prepare64_1, Machine.advanceX_fpsr, Machine.advanceW_fpsr]
  · change (prepare64_2 s).x.size = _
    simp only [prepare64_2, prepare64_1, Machine.advanceX_size, Machine.advanceW_size]
  · change (prepare64_2 s).v = _
    simp only [prepare64_2, prepare64_1, Machine.advanceX_vectors, Machine.advanceW_vectors]
  · intro r hr hr'
    change (prepare64_2 s).readX r = _
    have h1 : 1 ≠ r := by omega
    have h4 : 4 ≠ r := by omega
    simp [prepare64_2, prepare64_1, Machine.readX_advanceX_ne, Machine.readX_advanceW_ne, hr', h1, h4]

end VerifiedSqrt.Arm
