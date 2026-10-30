module

public import VerifiedSqrt.Arm.NormalizeInstructions
public import VerifiedSqrt.Arm.NormalizeArithmetic32
public import VerifiedSqrt.Arm.Execution

@[expose] public section

namespace VerifiedSqrt.Arm

def normalize1 (s : Machine) : Machine :=
  s.advanceW 1 (s.readW 1 - 127)

def normalize2 (s : Machine) : Machine :=
  let s := normalize1 s
  s.advanceW 2 (UInt32.ofInt (signedWord32 (s.readW 1) / 2))

def normalize3 (s : Machine) : Machine :=
  let s := normalize2 s
  s.advanceW 4 (s.readW 4 + s.readW 2)

def normalize4 (s : Machine) : Machine :=
  let s := normalize3 s
  s.advanceW 1 (s.readW 1 &&& 1)

def normalize5 (s : Machine) : Machine :=
  let s := normalize4 s
  s.advanceW 1 (s.readW 1 + 127)

def normalize6 (s : Machine) : Machine :=
  let s := normalize5 s
  s.advanceW 0 (s.readW 0 &&& 0x7fffff)

def normalize7 (s : Machine) : Machine :=
  let s := normalize6 s
  s.advanceW 0 (s.readW 0 ||| (s.readW 1 <<< 23))

def normalize8 (s : Machine) : Machine :=
  let s := normalize7 s
  s.advanceS 0 (s.readW 0)

theorem normalize_run (s : Machine) (hpc : s.pc = 68)
    (hc : supportedControls s.fpcr = true) :
    run sqrt32Code 100 8 s = some (normalize8 s) := by
  have hp1 : (normalize1 s).pc = 72 := by
    rw [normalize1, Machine.advanceW_pc, hpc]
    decide +kernel
  have hc1 : supportedControls (normalize1 s).fpcr = true := by
    rw [normalize1, Machine.advanceW_fpcr]
    exact hc
  have hp2 : (normalize2 s).pc = 76 := by
    rw [normalize2, Machine.advanceW_pc, hp1]
    decide +kernel
  have hc2 : supportedControls (normalize2 s).fpcr = true := by
    rw [normalize2, Machine.advanceW_fpcr]
    exact hc1
  have hp3 : (normalize3 s).pc = 80 := by
    rw [normalize3, Machine.advanceW_pc, hp2]
    decide +kernel
  have hc3 : supportedControls (normalize3 s).fpcr = true := by
    rw [normalize3, Machine.advanceW_fpcr]
    exact hc2
  have hp4 : (normalize4 s).pc = 84 := by
    rw [normalize4, Machine.advanceW_pc, hp3]
    decide +kernel
  have hc4 : supportedControls (normalize4 s).fpcr = true := by
    rw [normalize4, Machine.advanceW_fpcr]
    exact hc3
  have hp5 : (normalize5 s).pc = 88 := by
    rw [normalize5, Machine.advanceW_pc, hp4]
    decide +kernel
  have hc5 : supportedControls (normalize5 s).fpcr = true := by
    rw [normalize5, Machine.advanceW_fpcr]
    exact hc4
  have hp6 : (normalize6 s).pc = 92 := by
    rw [normalize6, Machine.advanceW_pc, hp5]
    decide +kernel
  have hc6 : supportedControls (normalize6 s).fpcr = true := by
    rw [normalize6, Machine.advanceW_fpcr]
    exact hc5
  have hp7 : (normalize7 s).pc = 96 := by
    rw [normalize7, Machine.advanceW_pc, hp6]
    decide +kernel
  have hc7 : supportedControls (normalize7 s).fpcr = true := by
    rw [normalize7, Machine.advanceW_fpcr]
    exact hc6
  have hp8 : (normalize8 s).pc = 100 := by
    rw [normalize8, Machine.advanceS_pc, hp7]
    decide +kernel
  calc
    run sqrt32Code 100 8 s = run sqrt32Code 100 7 (normalize1 s) :=
      run_step _ _ _ _ _ 0x5101fc21
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step_unbias_exponent s hc)
    _ = run sqrt32Code 100 6 (normalize2 s) :=
      run_step _ _ _ _ _ 0x13017c22
        (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
        (by rw [hp1]; decide +kernel) (step_halve_exponent (normalize1 s) hc1)
    _ = run sqrt32Code 100 5 (normalize3 s) :=
      run_step _ _ _ _ _ 0x0b020084
        (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
        (by rw [hp2]; decide +kernel) (step_save_exponent (normalize2 s) hc2)
    _ = run sqrt32Code 100 4 (normalize4 s) :=
      run_step _ _ _ _ _ 0x12000021
        (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel)
        (by rw [hp3]; decide +kernel) (step_exponent_parity (normalize3 s) hc3)
    _ = run sqrt32Code 100 3 (normalize5 s) :=
      run_step _ _ _ _ _ 0x1101fc21
        (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel)
        (by rw [hp4]; decide +kernel) (step_bias_parity (normalize4 s) hc4)
    _ = run sqrt32Code 100 2 (normalize6 s) :=
      run_step _ _ _ _ _ 0x12005800
        (by rw [hp5]; decide +kernel) (by rw [hp5]; decide +kernel)
        (by rw [hp5]; decide +kernel) (step_setup_seed_fraction (normalize5 s) hc5)
    _ = run sqrt32Code 100 1 (normalize7 s) :=
      run_step _ _ _ _ _ 0x2a015c00
        (by rw [hp6]; decide +kernel) (by rw [hp6]; decide +kernel)
        (by rw [hp6]; decide +kernel) (step_normalize_bits (normalize6 s) hc6)
    _ = run sqrt32Code 100 0 (normalize8 s) :=
      run_step _ _ _ _ _ 0x1e270000
        (by rw [hp7]; decide +kernel) (by rw [hp7]; decide +kernel)
        (by rw [hp7]; decide +kernel) (step_result_to_scalar (normalize7 s) hc7)
    _ = some (normalize8 s) := run_at_stop _ _ _ _ hp8

attribute [local simp] Machine.advanceW_size Machine.readW_advanceW_same
  Machine.readW_advanceW_ne Machine.readX_advanceW_ne

theorem normalize_pc (s : Machine) (hpc : s.pc = 68) : (normalize8 s).pc = 100 := by
  simp only [normalize8, Machine.advanceS_pc, normalize7, normalize6, normalize5,
    normalize4, normalize3, normalize2, normalize1, Machine.advanceW_pc, hpc]
  decide +kernel

theorem normalize_word (s : Machine) (hs : s.x.size = 32)
    (he : s.readW 1 = UInt32.ofNat (exponent32 (s.readW 0))) :
    (normalize8 s).readW 0 = Sqrt.normalizedInput32 (s.readW 0) := by
  rw [normalize8, Machine.readW_advanceS]
  simp only [normalize7, normalize6, normalize5, normalize4, normalize3, normalize2,
    normalize1]
  simp only [Machine.readW_advanceW_same, Machine.readW_advanceW_ne,
    Machine.advanceW_size, hs, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  rw [he]
  exact word32_normalized_input (s.readW 0)

theorem normalize_exponent (s : Machine) (hs : s.x.size = 32) (k : Int)
    (he : s.readW 1 = UInt32.ofNat (exponent32 (s.readW 0)))
    (hk : s.readW 4 = UInt32.ofInt k) :
    (normalize8 s).readW 4 = UInt32.ofInt (k + Sqrt.rootExponent32 (s.readW 0)) := by
  rw [normalize8, Machine.readW_advanceS]
  simp only [normalize7, normalize6, normalize5, normalize4, normalize3, normalize2,
    normalize1]
  simp only [Machine.readW_advanceW_same, Machine.readW_advanceW_ne,
    Machine.advanceW_size, hs, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  rw [he, hk, word32_root_exponent, UInt32.ofInt_add]

theorem normalize_scalar (s : Machine) (hs : s.WellFormed)
    (he : s.readW 1 = UInt32.ofNat (exponent32 (s.readW 0))) :
    (normalize8 s).readS 0 = Sqrt.normalizedInput32 (s.readW 0) := by
  have hv : (normalize7 s).v.size = 32 := by
    simpa only [normalize7, normalize6, normalize5, normalize4, normalize3, normalize2,
      normalize1, Machine.advanceW_vectors] using hs.2
  rw [normalize8, Machine.readS_advanceS_same (normalize7 s) 0 (by decide) hv]
  simpa only [normalize8, Machine.readW_advanceS] using normalize_word s hs.1 he

theorem normalize_properties (s : Machine) :
    (normalize8 s).fpcr = s.fpcr ∧ (normalize8 s).fpsr = s.fpsr ∧
      (normalize8 s).x.size = s.x.size ∧ (normalize8 s).v.size = s.v.size ∧
      (∀ r, 5 ≤ r → r < 31 → (normalize8 s).readX r = s.readX r) ∧
      (∀ r, r ≠ 0 → (normalize8 s).v[r]! = s.v[r]!) := by
  have hx : (normalize8 s).x = (normalize7 s).x := by
    rw [normalize8, Machine.advanceS_registers]
  have hv : (normalize7 s).v = s.v := by
    simp only [normalize7, normalize6, normalize5, normalize4, normalize3, normalize2,
      normalize1, Machine.advanceW_vectors]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [normalize8, Machine.advanceS_fpcr]
    simp only [normalize7, normalize6, normalize5, normalize4, normalize3, normalize2,
      normalize1, Machine.advanceW_fpcr]
  · rw [normalize8, Machine.advanceS_fpsr]
    simp only [normalize7, normalize6, normalize5, normalize4, normalize3, normalize2,
      normalize1, Machine.advanceW_fpsr]
  · rw [hx]
    simp only [normalize7, normalize6, normalize5, normalize4, normalize3, normalize2,
      normalize1, Machine.advanceW_size]
  · rw [normalize8, Machine.advanceS_vector_size, hv]
  · intro r hr hr'
    rw [normalize8, Machine.readX_advanceS]
    have h0 : 0 ≠ r := by omega
    have h1 : 1 ≠ r := by omega
    have h2 : 2 ≠ r := by omega
    have h4 : 4 ≠ r := by omega
    simp [normalize7, normalize6, normalize5, normalize4, normalize3, normalize2,
      normalize1, hr', h0, h1, h2, h4]
  · intro r hr
    rw [normalize8, Machine.vector_advanceS_ne _ 0 r (Ne.symm hr)]
    exact congrArg (fun v => v[r]!) hv

end VerifiedSqrt.Arm
