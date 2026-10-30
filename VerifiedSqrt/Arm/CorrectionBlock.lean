module

public import VerifiedSqrt.Arm.Execution
public import VerifiedSqrt.Arm.InstructionProof
public import VerifiedSqrt.Arm.IntegerArithmetic

@[expose] public section

namespace VerifiedSqrt.Arm

def doubleState (s : Machine) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeW 2 (s.readW 0 + s.readW 0)

def lowerState (s : Machine) : Machine :=
  let t := doubleState s
  ({t with pc := t.pc + 4} : Machine).writeW 2 (t.readW 2 - 1)

def lowerSquareState (s : Machine) : Machine :=
  let t := lowerState s
  ({t with pc := t.pc + 4} : Machine).writeX 2
    ((t.readW 2).toUInt64 * (t.readW 2).toUInt64)

theorem lower_square_block (s : Machine) (hpc : s.pc = 184)
    (hc : supportedControls s.fpcr = true) :
    run sqrt32Code 196 3 s = some (lowerSquareState s) := by
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
  have hc1 : supportedControls (doubleState s).fpcr = true := hc
  have hc2 : supportedControls (lowerState s).fpcr = true := hc
  calc
    run sqrt32Code 196 3 s = run sqrt32Code 196 2 (doubleState s) :=
      run_step _ _ _ _ _ 0x0b000002
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step_double_candidate s hc)
    _ = run sqrt32Code 196 1 (lowerState s) :=
      run_step _ _ _ _ _ 0x51000442
        (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
        (by rw [hp1]; decide +kernel) (step_lower_midpoint _ hc1)
    _ = run sqrt32Code 196 0 (lowerSquareState s) :=
      run_step _ _ _ _ _ 0x9ba27c42
        (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
        (by rw [hp2]; decide +kernel) (step_square_midpoint _ hc2)
    _ = some (lowerSquareState s) := run_at_stop _ _ _ _ hp3

theorem lower_square_block_value (s : Machine) (hs : s.x.size = 32)
    (lo : 0 < (s.readW 0).toNat) (hi : (s.readW 0).toNat ≤ 2 ^ 24) :
    ((lowerSquareState s).readX 2).toNat = (2 * (s.readW 0).toNat - 1) ^ 2 := by
  have hs1 : (doubleState s).x.size = 32 := by
    simpa [doubleState, Machine.writeW] using hs
  have hs2 : (lowerState s).x.size = 32 := by
    simpa [lowerState, Machine.writeW] using hs1
  have hr1 : (doubleState s).readW 2 = s.readW 0 + s.readW 0 :=
    Machine.readW_writeW_same _ 2 (by decide) hs _
  have hr2 : (lowerState s).readW 2 = (doubleState s).readW 2 - 1 :=
    Machine.readW_writeW_same _ 2 (by decide) hs1 _
  have hr3 : (lowerSquareState s).readX 2 =
      ((lowerState s).readW 2).toUInt64 * ((lowerState s).readW 2).toUInt64 :=
    Machine.readX_writeX_same _ 2 (by decide) hs2 _
  rw [hr3, hr2, hr1]
  exact lower_midpoint_square_exact _ lo hi

end VerifiedSqrt.Arm
