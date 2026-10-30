module

public import VerifiedSqrt.Arm.Return64
public import VerifiedSqrt.Arm.NormalizeArithmetic64

@[expose] public section

namespace VerifiedSqrt.Arm

attribute [local cbv_opaque] Machine.readW Machine.writeW Machine.readX Machine.writeX
  Machine.readD Machine.writeD supportedControls UInt32.add UInt32.sub UInt32.shiftLeft
  UInt64.add UInt64.shiftLeft sign32 Int.ediv Int.emod Int.toNat

private theorem shiftZero32 (w : UInt32) : UInt32.shiftLeft w ⟨0#32⟩ = w := UInt32.shiftLeft_zero

def normalize64_1 (s : Machine) : Machine :=
  s.advanceW 1 (s.readW 1 - 1023)

theorem step64_normalize_1 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x510ffc21 s = some (s.advanceW 1 (s.readW 1 - 1023)) := by
  unfold step64 step
  rw [hc]
  cbv

def normalize64_2 (s : Machine) : Machine :=
  let s := normalize64_1 s
  s.advanceW 2 (UInt32.ofInt (signedWord32 (s.readW 1) / 2))

theorem step64_normalize_2 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x13017c22 s = some (s.advanceW 2 (UInt32.ofInt (signedWord32 (s.readW 1) / 2))) := by
  unfold step64 step
  rw [hc]
  cbv

def normalize64_3 (s : Machine) : Machine :=
  let s := normalize64_2 s
  s.advanceW 4 (s.readW 4 + s.readW 2)

theorem step64_normalize_3 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x0b020084 s = some (s.advanceW 4 (s.readW 4 + s.readW 2)) := by
  unfold step64 step
  rw [hc]
  cbv
  simp only [shiftZero32]

def normalize64_4 (s : Machine) : Machine :=
  let s := normalize64_3 s
  s.advanceW 1 (s.readW 1 &&& 1)

theorem step64_normalize_4 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x12000021 s = some (s.advanceW 1 (s.readW 1 &&& 1)) := by
  unfold step64 step
  rw [hc]
  cbv

def normalize64_5 (s : Machine) : Machine :=
  let s := normalize64_4 s
  s.advanceW 1 (s.readW 1 + 1023)

theorem step64_normalize_5 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x110ffc21 s = some (s.advanceW 1 (s.readW 1 + 1023)) := by
  unfold step64 step
  rw [hc]
  cbv

def normalize64_6 (s : Machine) : Machine :=
  let s := normalize64_5 s
  s.advanceX 0 (s.readX 0 &&& 0xfffffffffffff)

theorem step64_normalize_6 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9240cc00 s = some (s.advanceX 0 (s.readX 0 &&& 0xfffffffffffff)) := by
  unfold step64 step
  rw [hc]
  cbv

def normalize64_7 (s : Machine) : Machine :=
  let s := normalize64_6 s
  s.advanceX 0 (s.readX 0 ||| (s.readX 1 <<< 52))

theorem step64_normalize_7 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xaa01d000 s = some (s.advanceX 0 (s.readX 0 ||| (s.readX 1 <<< 52))) := by
  unfold step64 step
  rw [hc]
  cbv

def normalize64_8 (s : Machine) : Machine :=
  let s := normalize64_7 s
  s.advanceD 0 (s.readX 0)

theorem step64_normalize_8 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9e670000 s = some (s.advanceD 0 (s.readX 0)) := by
  unfold step64 step
  rw [hc]
  cbv

theorem normalize64_trace (s : Machine) (hpc : s.pc = 68)
    (hc : supportedControls s.fpcr = true) :
    Steps64 sqrt64Code 0 8 s (normalize64_8 s) := by
  have hp1 : (normalize64_1 s).pc = 72 := by
    rw [normalize64_1, Machine.advanceW_pc, hpc]
    decide +kernel
  have hc1 : supportedControls (normalize64_1 s).fpcr = true := by
    rw [normalize64_1, Machine.advanceW_fpcr]
    exact hc
  have ht1 : Steps64 sqrt64Code 0 1 s (normalize64_1 s) := Steps64.single
    (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) (step64_normalize_1 s hc)
  have hp2 : (normalize64_2 s).pc = 76 := by
    rw [normalize64_2, Machine.advanceW_pc, hp1]
    decide +kernel
  have hc2 : supportedControls (normalize64_2 s).fpcr = true := by
    rw [normalize64_2, Machine.advanceW_fpcr]
    exact hc1
  have ht2 : Steps64 sqrt64Code 0 1 (normalize64_1 s) (normalize64_2 s) := Steps64.single
    (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel) (step64_normalize_2 (normalize64_1 s) hc1)
  have hp3 : (normalize64_3 s).pc = 80 := by
    rw [normalize64_3, Machine.advanceW_pc, hp2]
    decide +kernel
  have hc3 : supportedControls (normalize64_3 s).fpcr = true := by
    rw [normalize64_3, Machine.advanceW_fpcr]
    exact hc2
  have ht3 : Steps64 sqrt64Code 0 1 (normalize64_2 s) (normalize64_3 s) := Steps64.single
    (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel) (step64_normalize_3 (normalize64_2 s) hc2)
  have hp4 : (normalize64_4 s).pc = 84 := by
    rw [normalize64_4, Machine.advanceW_pc, hp3]
    decide +kernel
  have hc4 : supportedControls (normalize64_4 s).fpcr = true := by
    rw [normalize64_4, Machine.advanceW_fpcr]
    exact hc3
  have ht4 : Steps64 sqrt64Code 0 1 (normalize64_3 s) (normalize64_4 s) := Steps64.single
    (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel) (step64_normalize_4 (normalize64_3 s) hc3)
  have hp5 : (normalize64_5 s).pc = 88 := by
    rw [normalize64_5, Machine.advanceW_pc, hp4]
    decide +kernel
  have hc5 : supportedControls (normalize64_5 s).fpcr = true := by
    rw [normalize64_5, Machine.advanceW_fpcr]
    exact hc4
  have ht5 : Steps64 sqrt64Code 0 1 (normalize64_4 s) (normalize64_5 s) := Steps64.single
    (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel) (step64_normalize_5 (normalize64_4 s) hc4)
  have hp6 : (normalize64_6 s).pc = 92 := by
    rw [normalize64_6, Machine.advanceX_pc, hp5]
    decide +kernel
  have hc6 : supportedControls (normalize64_6 s).fpcr = true := by
    rw [normalize64_6, Machine.advanceX_fpcr]
    exact hc5
  have ht6 : Steps64 sqrt64Code 0 1 (normalize64_5 s) (normalize64_6 s) := Steps64.single
    (by rw [hp5]; decide +kernel) (by rw [hp5]; decide +kernel) (step64_normalize_6 (normalize64_5 s) hc5)
  have hp7 : (normalize64_7 s).pc = 96 := by
    rw [normalize64_7, Machine.advanceX_pc, hp6]
    decide +kernel
  have hc7 : supportedControls (normalize64_7 s).fpcr = true := by
    rw [normalize64_7, Machine.advanceX_fpcr]
    exact hc6
  have ht7 : Steps64 sqrt64Code 0 1 (normalize64_6 s) (normalize64_7 s) := Steps64.single
    (by rw [hp6]; decide +kernel) (by rw [hp6]; decide +kernel) (step64_normalize_7 (normalize64_6 s) hc6)
  have hp8 : (normalize64_8 s).pc = 100 := by
    rw [normalize64_8, Machine.advanceD_pc, hp7]
    decide +kernel
  have ht8 : Steps64 sqrt64Code 0 1 (normalize64_7 s) (normalize64_8 s) := Steps64.single
    (by rw [hp7]; decide +kernel) (by rw [hp7]; decide +kernel) (step64_normalize_8 (normalize64_7 s) hc7)
  exact ht1.trans (ht2.trans (ht3.trans (ht4.trans (ht5.trans (ht6.trans (ht7.trans (ht8)))))))

attribute [local simp] Machine.advanceW_size Machine.readW_advanceW_same
  Machine.readW_advanceW_ne Machine.readX_advanceW_ne Machine.readX_advanceX_ne Machine.readW_advanceX_ne

theorem normalize64_pc (s : Machine) (hpc : s.pc = 68) : (normalize64_8 s).pc = 100 := by
  simp only [normalize64_8, Machine.advanceD_pc, normalize64_7, normalize64_6, normalize64_5,
    normalize64_4, normalize64_3, normalize64_2, normalize64_1, Machine.advanceW_pc, Machine.advanceX_pc, hpc]
  decide +kernel

theorem normalize64_word (s : Machine) (hs : s.x.size = 32)
    (he : s.readW 1 = UInt32.ofNat (exponent64 (s.readX 0))) :
    (normalize64_8 s).readX 0 = Sqrt.normalizedInput64 (s.readX 0) := by
  rw [normalize64_8, Machine.readX_advanceD]
  simp only [normalize64_7, normalize64_6, normalize64_5, normalize64_4, normalize64_3, normalize64_2,
    normalize64_1]
  simp only [Machine.readW_advanceW_same, Machine.readW_advanceW_ne,
    Machine.advanceW_size, Machine.advanceX_size, Machine.readX_advanceX_ne, Machine.readX_advanceX_same, Machine.readX_advanceW_same, Machine.readX_advanceW_ne, hs, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  rw [he]
  exact word64_normalized_input (s.readX 0)

theorem normalize64_exponent (s : Machine) (hs : s.x.size = 32) (k : Int)
    (he : s.readW 1 = UInt32.ofNat (exponent64 (s.readX 0)))
    (hk : s.readW 4 = UInt32.ofInt k) :
    (normalize64_8 s).readW 4 = UInt32.ofInt (k + Sqrt.rootExponent64 (s.readX 0)) := by
  rw [normalize64_8, Machine.readW_advanceD]
  simp only [normalize64_7, normalize64_6, normalize64_5, normalize64_4, normalize64_3, normalize64_2,
    normalize64_1]
  simp only [Machine.readW_advanceW_same, Machine.readW_advanceW_ne,
    Machine.advanceW_size, Machine.readX_advanceX_ne, Machine.readX_advanceX_same, Machine.readX_advanceW_same, Machine.readX_advanceW_ne, Machine.readW_advanceX_ne, hs, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  rw [he, hk, word64_root_exponent, UInt32.ofInt_add]

theorem normalize64_scalar (s : Machine) (hs : s.WellFormed)
    (he : s.readW 1 = UInt32.ofNat (exponent64 (s.readX 0))) :
    (normalize64_8 s).readD 0 = Sqrt.normalizedInput64 (s.readX 0) := by
  have hv : (normalize64_7 s).v.size = 32 := by
    simpa only [normalize64_7, normalize64_6, normalize64_5, normalize64_4, normalize64_3, normalize64_2,
      normalize64_1, Machine.advanceW_vectors, Machine.advanceX_vectors] using hs.2
  rw [normalize64_8, Machine.readD_advanceD_same (normalize64_7 s) 0 (by decide) hv]
  simpa only [normalize64_8, Machine.readX_advanceD] using normalize64_word s hs.1 he

theorem normalize64_properties (s : Machine) :
    (normalize64_8 s).fpcr = s.fpcr ∧ (normalize64_8 s).fpsr = s.fpsr ∧
      (normalize64_8 s).x.size = s.x.size ∧ (normalize64_8 s).v.size = s.v.size ∧
      (∀ r, 5 ≤ r → r < 31 → (normalize64_8 s).readX r = s.readX r) ∧
      (∀ r, r ≠ 0 → (normalize64_8 s).v[r]! = s.v[r]!) := by
  have hx : (normalize64_8 s).x = (normalize64_7 s).x := by
    rw [normalize64_8, Machine.advanceD_registers]
  have hv : (normalize64_7 s).v = s.v := by
    simp only [normalize64_7, normalize64_6, normalize64_5, normalize64_4, normalize64_3, normalize64_2,
      normalize64_1, Machine.advanceW_vectors, Machine.advanceX_vectors]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [normalize64_8, Machine.advanceD_fpcr]
    simp only [normalize64_7, normalize64_6, normalize64_5, normalize64_4, normalize64_3, normalize64_2,
      normalize64_1, Machine.advanceW_fpcr, Machine.advanceX_fpcr]
  · rw [normalize64_8, Machine.advanceD_fpsr]
    simp only [normalize64_7, normalize64_6, normalize64_5, normalize64_4, normalize64_3, normalize64_2,
      normalize64_1, Machine.advanceW_fpsr, Machine.advanceX_fpsr]
  · rw [hx]
    simp only [normalize64_7, normalize64_6, normalize64_5, normalize64_4, normalize64_3, normalize64_2,
      normalize64_1, Machine.advanceW_size, Machine.advanceX_size]
  · rw [normalize64_8, Machine.advanceD_vector_size, hv]
  · intro r hr hr'
    rw [normalize64_8, Machine.readX_advanceD]
    have h0 : 0 ≠ r := by omega
    have h1 : 1 ≠ r := by omega
    have h2 : 2 ≠ r := by omega
    have h4 : 4 ≠ r := by omega
    simp [normalize64_7, normalize64_6, normalize64_5, normalize64_4, normalize64_3, normalize64_2,
      normalize64_1, hr', h0, h1, h2, h4]
  · intro r hr
    rw [normalize64_8, Machine.vector_advanceD_ne _ 0 r (Ne.symm hr)]
    exact congrArg (fun v => v[r]!) hv

end VerifiedSqrt.Arm
