module

public import VerifiedSqrt.Arm.Execution64
public import VerifiedSqrt.Arm.InstructionProof64
public import VerifiedSqrt.Arm.WideArithmetic

@[expose] public section

namespace VerifiedSqrt.Arm

def double64State (s : Machine) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeX 2 (s.readX 0 + s.readX 0)

def lower64State (s : Machine) : Machine :=
  let t := double64State s
  ({t with pc := t.pc + 4} : Machine).writeX 2 (t.readX 2 - 1)

def lowerHigh64State (s : Machine) : Machine :=
  let t := lower64State s
  ({t with pc := t.pc + 4} : Machine).writeX 6 (multiplyHigh64 (t.readX 2) (t.readX 2))

def lowerSquare64State (s : Machine) : Machine :=
  let t := lowerHigh64State s
  ({t with pc := t.pc + 4} : Machine).writeX 2 (t.readX 2 * t.readX 2)

theorem lower_square64_block (s : Machine) (hpc : s.pc = 208)
    (hc : supportedControls s.fpcr = true) :
    run64 sqrt64Code 0 224 4 s = some (lowerSquare64State s) := by
  have hp1 : (double64State s).pc = 212 := by
    change s.pc + 4 = 212
    rw [hpc]
    decide +kernel
  have hp2 : (lower64State s).pc = 216 := by
    change (double64State s).pc + 4 = 216
    rw [hp1]
    decide +kernel
  have hp3 : (lowerHigh64State s).pc = 220 := by
    change (lower64State s).pc + 4 = 220
    rw [hp2]
    decide +kernel
  have hp4 : (lowerSquare64State s).pc = 224 := by
    change (lowerHigh64State s).pc + 4 = 224
    rw [hp3]
    decide +kernel
  calc
    run64 sqrt64Code 0 224 4 s = run64 sqrt64Code 0 224 3 (double64State s) :=
      run64_step _ _ _ _ _ _ 0x8b000002
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
        (by rw [hpc]; decide +kernel) (step64_double_candidate s hc)
    _ = run64 sqrt64Code 0 224 2 (lower64State s) :=
      run64_step _ _ _ _ _ _ 0xd1000442
        (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
        (by rw [hp1]; decide +kernel) (step64_lower_midpoint _ hc)
    _ = run64 sqrt64Code 0 224 1 (lowerHigh64State s) :=
      run64_step _ _ _ _ _ _ 0x9bc27c46
        (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
        (by rw [hp2]; decide +kernel) (step64_square_high _ hc)
    _ = run64 sqrt64Code 0 224 0 (lowerSquare64State s) :=
      run64_step _ _ _ _ _ _ 0x9b027c42
        (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel)
        (by rw [hp3]; decide +kernel) (step64_square_low _ hc)
    _ = some (lowerSquare64State s) := run64_at_stop _ _ _ _ _ hp4

theorem lower_square64_block_value (s : Machine) (hs : s.x.size = 32)
    (lo : 0 < (s.readX 0).toNat) (hi : (s.readX 0).toNat ≤ 2 ^ 53) :
    wideValue ((lowerSquare64State s).readX 6) ((lowerSquare64State s).readX 2) =
      (2 * (s.readX 0).toNat - 1) ^ 2 := by
  have hs1 : (double64State s).x.size = 32 := by
    simpa [double64State, Machine.writeX] using hs
  have hs2 : (lower64State s).x.size = 32 := by
    simpa [lower64State, Machine.writeX] using hs1
  have hs3 : (lowerHigh64State s).x.size = 32 := by
    simpa [lowerHigh64State, Machine.writeX] using hs2
  have hr1 : (double64State s).readX 2 = s.readX 0 + s.readX 0 :=
    Machine.readX_writeX_same _ 2 (by decide) hs _
  have hr2 : (lower64State s).readX 2 = (double64State s).readX 2 - 1 :=
    Machine.readX_writeX_same _ 2 (by decide) hs1 _
  have hr3 : (lowerHigh64State s).readX 6 =
      multiplyHigh64 ((lower64State s).readX 2) ((lower64State s).readX 2) :=
    Machine.readX_writeX_same _ 6 (by decide) hs2 _
  have hr4 : (lowerHigh64State s).readX 2 = (lower64State s).readX 2 :=
    Machine.readX_writeX_ne _ 6 2 (by decide) (by decide) (by decide) _
  have hr5 : (lowerSquare64State s).readX 2 =
      (lowerHigh64State s).readX 2 * (lowerHigh64State s).readX 2 :=
    Machine.readX_writeX_same _ 2 (by decide) hs3 _
  have hr6 : (lowerSquare64State s).readX 6 = (lowerHigh64State s).readX 6 :=
    Machine.readX_writeX_ne _ 2 6 (by decide) (by decide) (by decide) _
  rw [hr6, hr5, hr4, hr3, hr2, hr1]
  exact lower_midpoint_square128_exact _ lo hi

end VerifiedSqrt.Arm
