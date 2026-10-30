module

public import VerifiedSqrt.Arm.Execution
public import VerifiedSqrt.Arm.InstructionProof
public import VerifiedSqrt.Arm.Word32
public import VerifiedSqrt.Sqrt.Normalization32

@[expose] public section

namespace VerifiedSqrt.Arm

def biasState (s : Machine) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeW 1 0x3f000000

def encodeState (s : Machine) : Machine :=
  let t := biasState s
  ({t with pc := t.pc + 4} : Machine).writeW 0 (t.readW 0 + t.readW 1)

def rescaleState (s : Machine) : Machine :=
  let t := encodeState s
  ({t with pc := t.pc + 4} : Machine).writeW 0 (t.readW 0 + (t.readW 4 <<< 23))

def scalarResultState (s : Machine) : Machine :=
  let t := rescaleState s
  ({t with pc := t.pc + 4} : Machine).writeS 0 (t.readW 0)

def returnedState (s : Machine) : Machine :=
  let t := scalarResultState s
  {t with pc := t.readX 30}

theorem return_registers (s : Machine) (hs : s.x.size = 32) :
    (rescaleState s).readW 0 = s.readW 0 + (0x3f000000 : UInt32) + (s.readW 4 <<< 23) := by
  have h1 : (biasState s).x.size = 32 := by simpa [biasState, Machine.writeW] using hs
  have h2 : (encodeState s).x.size = 32 := by simpa [encodeState, Machine.writeW] using h1
  have hr1 : (biasState s).readW 1 = 0x3f000000 :=
    Machine.readW_writeW_same _ 1 (by decide) hs _
  have hr0 : (biasState s).readW 0 = s.readW 0 :=
    congrArg UInt64.toUInt32 (Machine.readX_writeW_ne _ 1 0 (by decide) (by decide) (by decide) _)
  have hr4 : (encodeState s).readW 4 = s.readW 4 := by
    have h : (encodeState s).readX 4 = (biasState s).readX 4 :=
      Machine.readX_writeW_ne _ 0 4 (by decide) (by decide) (by decide) _
    have h' : (biasState s).readX 4 = s.readX 4 :=
      Machine.readX_writeW_ne _ 1 4 (by decide) (by decide) (by decide) _
    exact congrArg UInt64.toUInt32 (h.trans h')
  have hr2 : (encodeState s).readW 0 = (biasState s).readW 0 + (biasState s).readW 1 :=
    Machine.readW_writeW_same _ 0 (by decide) h1 _
  have hr3 : (rescaleState s).readW 0 = (encodeState s).readW 0 + ((encodeState s).readW 4 <<< 23) :=
    Machine.readW_writeW_same _ 0 (by decide) h2 _
  rw [hr3, hr2, hr0, hr1, hr4]

theorem return_link (s : Machine) : (scalarResultState s).readX 30 = s.readX 30 := by
  change (rescaleState s).readX 30 = s.readX 30
  unfold rescaleState
  rw [Machine.readX_writeW_ne _ 0 30 (by decide) (by decide) (by decide)]
  change (encodeState s).readX 30 = s.readX 30
  unfold encodeState
  rw [Machine.readX_writeW_ne _ 0 30 (by decide) (by decide) (by decide)]
  change (biasState s).readX 30 = s.readX 30
  unfold biasState
  rw [Machine.readX_writeW_ne _ 1 30 (by decide) (by decide) (by decide)]
  rfl

theorem return_value (s : Machine) (hs : s.WellFormed) :
    (returnedState s).readS 0 = s.readW 0 + (0x3f000000 : UInt32) + (s.readW 4 <<< 23) := by
  have hv : (rescaleState s).v.size = 32 := hs.2
  have h : (scalarResultState s).readS 0 = (rescaleState s).readW 0 :=
    Machine.readS_writeS_same _ 0 (by decide) hv _
  change (scalarResultState s).readS 0 = _
  rw [h, return_registers s hs.1]

theorem return_run (s : Machine) (hpc : s.pc = 224)
    (hc : supportedControls s.fpcr = true)
    (hstop : sqrt32Code[(s.readX 30).toNat / 4]? = none) :
    run sqrt32Code (s.readX 30) 5 s = some (returnedState s) := by
  have hp1 : (biasState s).pc = 228 := by
    change s.pc + 4 = 228
    rw [hpc]
    decide +kernel
  have hp2 : (encodeState s).pc = 232 := by
    change (biasState s).pc + 4 = 232
    rw [hp1]
    decide +kernel
  have hp3 : (rescaleState s).pc = 236 := by
    change (encodeState s).pc + 4 = 236
    rw [hp2]
    decide +kernel
  have hp4 : (scalarResultState s).pc = 240 := by
    change (rescaleState s).pc + 4 = 240
    rw [hp3]
    decide +kernel
  have hn (pc : UInt64) (word : UInt32) (h : sqrt32Code[pc.toNat / 4]? = some word) : pc ≠ s.readX 30 := by
    intro he
    rw [he, hstop] at h
    contradiction
  calc
    run sqrt32Code (s.readX 30) 5 s = run sqrt32Code (s.readX 30) 4 (biasState s) :=
      run_step _ _ _ _ _ 0x52a7e001
        (hn _ 0x52a7e001 (by rw [hpc]; decide +kernel)) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step_result_bias s hc)
    _ = run sqrt32Code (s.readX 30) 3 (encodeState s) :=
      run_step _ _ _ _ _ 0x0b010000
        (hn _ 0x0b010000 (by rw [hp1]; decide +kernel)) (by rw [hp1]; decide +kernel)
        (by rw [hp1]; decide +kernel) (step_add_result_bias (biasState s) hc)
    _ = run sqrt32Code (s.readX 30) 2 (rescaleState s) :=
      run_step _ _ _ _ _ 0x0b045c00
        (hn _ 0x0b045c00 (by rw [hp2]; decide +kernel)) (by rw [hp2]; decide +kernel)
        (by rw [hp2]; decide +kernel) (step_add_result_exponent (encodeState s) hc)
    _ = run sqrt32Code (s.readX 30) 1 (scalarResultState s) :=
      run_step _ _ _ _ _ 0x1e270000
        (hn _ 0x1e270000 (by rw [hp3]; decide +kernel)) (by rw [hp3]; decide +kernel)
        (by rw [hp3]; decide +kernel) (step_result_to_scalar (rescaleState s) hc)
    _ = run sqrt32Code (s.readX 30) 0 (returnedState s) :=
      run_step _ _ _ _ _ 0xd65f03c0
        (hn _ 0xd65f03c0 (by rw [hp4]; decide +kernel)) (by rw [hp4]; decide +kernel)
        (by rw [hp4]; decide +kernel) (step_return (scalarResultState s) hc)
    _ = some (returnedState s) := run_at_stop _ _ _ _ (return_link s)

theorem return_other_register (s : Machine) (r : Nat) (hr : r < 31)
    (h0 : r ≠ 0) (h1 : r ≠ 1) : (returnedState s).readX r = s.readX r := by
  change (rescaleState s).readX r = s.readX r
  unfold rescaleState
  rw [Machine.readX_writeW_ne _ 0 r (by decide) hr (Ne.symm h0)]
  change (encodeState s).readX r = s.readX r
  unfold encodeState
  rw [Machine.readX_writeW_ne _ 0 r (by decide) hr (Ne.symm h0)]
  change (biasState s).readX r = s.readX r
  unfold biasState
  rw [Machine.readX_writeW_ne _ 1 r (by decide) hr (Ne.symm h1)]
  rfl

theorem return_other_vector (s : Machine) (r : Nat) (h : r ≠ 0) :
    (returnedState s).v[r]! = s.v[r]! := by
  exact Machine.vector_writeS_ne _ 0 r (Ne.symm h) _

theorem return_correct (x : UInt32) (k : Int)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000)
    (klo : -125 ≤ k) (khi : k ≤ 126) (s : Machine) (hs : s.WellFormed)
    (hq : (s.readW 0).toNat = Sqrt.correctedSignificand32 x)
    (hk : s.readW 4 = UInt32.ofInt k) :
    (returnedState s).readS 0 = Sqrt.rescale32 (Sqrt.core32 x) k := by
  have hb := Sqrt.correctedCore32_bounds x lo hi
  have hq' : s.readW 0 = UInt32.ofNat (Sqrt.correctedSignificand32 x) := by
    rw [← hq, UInt32.ofNat_toNat]
  have he : s.readW 0 + (0x3f000000 : UInt32) = Sqrt.core32 x := by
    rw [hq', Sqrt.core32]
    change UInt32.ofNat _ + UInt32.ofNat _ = _
    rw [← UInt32.ofNat_add]
    exact congrArg UInt32.ofNat (Nat.add_comm _ _)
  rw [return_value s hs, he, hk]
  exact word32_add_shift23 _ k (by omega)

end VerifiedSqrt.Arm
