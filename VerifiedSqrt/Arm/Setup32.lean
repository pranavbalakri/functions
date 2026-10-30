module

public import VerifiedSqrt.Arm.SetupInstructions
public import VerifiedSqrt.Arm.Execution
public import VerifiedSqrt.Sqrt.Correction32

@[expose] public section

namespace VerifiedSqrt.Arm

def setup1 (s : Machine) : Machine :=
  s.advanceW 2 (UInt32.ofNat ((s.readW 0).toNat / 2 ^ 23 % 256))

def setup2 (s : Machine) : Machine :=
  let s := setup1 s
  s.advanceW 2 (s.readW 2 - 102)

def setup3 (s : Machine) : Machine :=
  let s := setup2 s
  s.advanceW 3 (s.readW 0 &&& 0x7fffff)

def setup4 (s : Machine) : Machine :=
  let s := setup3 s
  s.advanceW 1 (0x800000)

def setup5 (s : Machine) : Machine :=
  let s := setup4 s
  s.advanceW 3 (s.readW 3 + s.readW 1)

def setup6 (s : Machine) : Machine :=
  let s := setup5 s
  s.advanceX 3 (s.readX 3 <<< (s.readX 2 &&& 63))

def setup7 (s : Machine) : Machine :=
  let s := setup6 s
  s.advanceW 0 (s.readS 0)

def setup8 (s : Machine) : Machine :=
  let s := setup7 s
  s.advanceW 0 (s.readW 0 &&& 0x7fffff)

def setup9 (s : Machine) : Machine :=
  let s := setup8 s
  s.advanceW 0 (s.readW 0 + s.readW 1)

theorem setup_run (s : Machine) (hpc : s.pc = 148)
    (hc : supportedControls s.fpcr = true) :
    run sqrt32Code 184 9 s = some (setup9 s) := by
  have hp1 : (setup1 s).pc = 152 := by
    rw [setup1, Machine.advanceW_pc, hpc]
    decide +kernel
  have hc1 : supportedControls (setup1 s).fpcr = true := by
    rw [setup1, Machine.advanceW_fpcr]
    exact hc
  have hp2 : (setup2 s).pc = 156 := by
    rw [setup2, Machine.advanceW_pc, hp1]
    decide +kernel
  have hc2 : supportedControls (setup2 s).fpcr = true := by
    rw [setup2, Machine.advanceW_fpcr]
    exact hc1
  have hp3 : (setup3 s).pc = 160 := by
    rw [setup3, Machine.advanceW_pc, hp2]
    decide +kernel
  have hc3 : supportedControls (setup3 s).fpcr = true := by
    rw [setup3, Machine.advanceW_fpcr]
    exact hc2
  have hp4 : (setup4 s).pc = 164 := by
    rw [setup4, Machine.advanceW_pc, hp3]
    decide +kernel
  have hc4 : supportedControls (setup4 s).fpcr = true := by
    rw [setup4, Machine.advanceW_fpcr]
    exact hc3
  have hp5 : (setup5 s).pc = 168 := by
    rw [setup5, Machine.advanceW_pc, hp4]
    decide +kernel
  have hc5 : supportedControls (setup5 s).fpcr = true := by
    rw [setup5, Machine.advanceW_fpcr]
    exact hc4
  have hp6 : (setup6 s).pc = 172 := by
    rw [setup6, Machine.advanceX_pc, hp5]
    decide +kernel
  have hc6 : supportedControls (setup6 s).fpcr = true := by
    rw [setup6, Machine.advanceX_fpcr]
    exact hc5
  have hp7 : (setup7 s).pc = 176 := by
    rw [setup7, Machine.advanceW_pc, hp6]
    decide +kernel
  have hc7 : supportedControls (setup7 s).fpcr = true := by
    rw [setup7, Machine.advanceW_fpcr]
    exact hc6
  have hp8 : (setup8 s).pc = 180 := by
    rw [setup8, Machine.advanceW_pc, hp7]
    decide +kernel
  have hc8 : supportedControls (setup8 s).fpcr = true := by
    rw [setup8, Machine.advanceW_fpcr]
    exact hc7
  have hp9 : (setup9 s).pc = 184 := by
    rw [setup9, Machine.advanceW_pc, hp8]
    decide +kernel
  have hc9 : supportedControls (setup9 s).fpcr = true := by
    rw [setup9, Machine.advanceW_fpcr]
    exact hc8
  calc
    run sqrt32Code 184 9 s = run sqrt32Code 184 8 (setup1 s) :=
      run_step _ _ _ _ _ 0x53177802
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step_setup_exponent s hc)
    _ = run sqrt32Code 184 7 (setup2 s) :=
      run_step _ _ _ _ _ 0x51019842
        (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
        (by rw [hp1]; decide +kernel) (step_setup_shift (setup1 s) hc1)
    _ = run sqrt32Code 184 6 (setup3 s) :=
      run_step _ _ _ _ _ 0x12005803
        (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
        (by rw [hp2]; decide +kernel) (step_setup_fraction (setup2 s) hc2)
    _ = run sqrt32Code 184 5 (setup4 s) :=
      run_step _ _ _ _ _ 0x52a01001
        (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel)
        (by rw [hp3]; decide +kernel) (step_setup_hidden_bit (setup3 s) hc3)
    _ = run sqrt32Code 184 4 (setup5 s) :=
      run_step _ _ _ _ _ 0x0b010063
        (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel)
        (by rw [hp4]; decide +kernel) (step_setup_significand (setup4 s) hc4)
    _ = run sqrt32Code 184 3 (setup6 s) :=
      run_step _ _ _ _ _ 0x9ac22063
        (by rw [hp5]; decide +kernel) (by rw [hp5]; decide +kernel)
        (by rw [hp5]; decide +kernel) (step_setup_radicand (setup5 s) hc5)
    _ = run sqrt32Code 184 2 (setup7 s) :=
      run_step _ _ _ _ _ 0x1e260000
        (by rw [hp6]; decide +kernel) (by rw [hp6]; decide +kernel)
        (by rw [hp6]; decide +kernel) (step_scalar_to_word (setup6 s) hc6)
    _ = run sqrt32Code 184 1 (setup8 s) :=
      run_step _ _ _ _ _ 0x12005800
        (by rw [hp7]; decide +kernel) (by rw [hp7]; decide +kernel)
        (by rw [hp7]; decide +kernel) (step_setup_seed_fraction (setup7 s) hc7)
    _ = run sqrt32Code 184 0 (setup9 s) :=
      run_step _ _ _ _ _ 0x0b010000
        (by rw [hp8]; decide +kernel) (by rw [hp8]; decide +kernel)
        (by rw [hp8]; decide +kernel) (step_add_result_bias (setup8 s) hc8)
    _ = some (setup9 s) := run_at_stop _ _ _ _ hp9

attribute [local simp] Machine.advanceW_size Machine.advanceX_size
  Machine.readW_advanceW_same Machine.readW_advanceW_ne Machine.readX_advanceW_same
  Machine.readX_advanceW_ne Machine.readX_advanceX_same Machine.readX_advanceX_ne
  Machine.readW_advanceX_ne Machine.readS_advanceW Machine.readS_advanceX

theorem setup_seed (s : Machine) (hs : s.x.size = 32) :
    (setup9 s).readW 0 = (s.readS 0 &&& 0x7fffff) + (0x800000 : UInt32) := by
  simp [setup1, setup2, setup3, setup4, setup5, setup6, setup7, setup8, setup9, hs]

theorem setup_radicand (s : Machine) (hs : s.x.size = 32) :
    (setup9 s).readX 3 =
      ((s.readW 0 &&& 0x7fffff) + (0x800000 : UInt32)).toUInt64 <<<
        ((UInt32.ofNat ((s.readW 0).toNat / 2 ^ 23 % 256) - 102).toUInt64 &&& 63) := by
  simp [setup1, setup2, setup3, setup4, setup5, setup6, setup7, setup8, setup9, hs]

theorem masked_significand_nat (w : UInt32) :
    ((w &&& 0x7fffff) + (0x800000 : UInt32)).toNat = fraction32 w + 2 ^ 23 := by
  have hf := fraction32_lt w
  rw [UInt32.toNat_add, show (w &&& 0x7fffff).toNat = fraction32 w from rfl,
    show (0x800000 : UInt32).toNat = 8388608 from rfl]
  omega

theorem setup_seed_bounds (s : Machine) (hs : s.x.size = 32) :
    2 ^ 23 ≤ ((setup9 s).readW 0).toNat ∧ ((setup9 s).readW 0).toNat ≤ 2 ^ 24 := by
  have hf := fraction32_lt (s.readS 0)
  rw [setup_seed s hs, masked_significand_nat]
  omega

theorem setup_radicand_value (s : Machine) (hs : s.x.size = 32)
    (lo : 0x3f800000 ≤ (s.readW 0).toNat) (hi : (s.readW 0).toNat < 0x40800000) :
    ((setup9 s).readX 3).toNat = 4 * Sqrt.normalizedRadicand32 (s.readW 0) := by
  have hf := fraction32_lt (s.readW 0)
  have hm := masked_significand_nat (s.readW 0)
  rw [setup_radicand s hs, ← exponent32_eq_div]
  rcases Sqrt.normalized32_exponent (s.readW 0) lo hi with he | he
  · rw [he]
    have hshift : (UInt32.ofNat 127 - 102).toUInt64 &&& 63 = 25 := by decide +kernel
    rw [hshift, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, hm]
    change ((fraction32 (s.readW 0) + 2 ^ 23) <<< 25) % 2 ^ 64 = _
    rw [Nat.shiftLeft_eq]
    norm_num [Sqrt.normalizedRadicand32, he]
    omega
  · rw [he]
    have hshift : (UInt32.ofNat 128 - 102).toUInt64 &&& 63 = 26 := by decide +kernel
    rw [hshift, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, hm]
    change ((fraction32 (s.readW 0) + 2 ^ 23) <<< 26) % 2 ^ 64 = _
    rw [Nat.shiftLeft_eq]
    norm_num [Sqrt.normalizedRadicand32, he]
    omega

theorem setup_properties (s : Machine) :
    (setup9 s).fpcr = s.fpcr ∧ (setup9 s).fpsr = s.fpsr ∧
      (setup9 s).v = s.v ∧ (setup9 s).x.size = s.x.size ∧
      ∀ r, 4 ≤ r → r < 31 → (setup9 s).readX r = s.readX r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [setup9, setup8, setup7, setup6, setup5, setup4, setup3, setup2, setup1,
      Machine.advanceW_fpcr, Machine.advanceX_fpcr]
  · simp only [setup9, setup8, setup7, setup6, setup5, setup4, setup3, setup2, setup1,
      Machine.advanceW_fpsr, Machine.advanceX_fpsr]
  · simp only [setup9, setup8, setup7, setup6, setup5, setup4, setup3, setup2, setup1,
      Machine.advanceW_vectors, Machine.advanceX_vectors]
  · simp [setup9, setup8, setup7, setup6, setup5, setup4, setup3, setup2, setup1]
  · intro r hlo hhi
    have h0 : 0 ≠ r := by omega
    have h1 : 1 ≠ r := by omega
    have h2 : 2 ≠ r := by omega
    have h3 : 3 ≠ r := by omega
    simp [setup9, setup8, setup7, setup6, setup5, setup4, setup3, setup2, setup1,
      hhi, h0, h1, h2, h3]

end VerifiedSqrt.Arm
