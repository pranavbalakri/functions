module

public import VerifiedSqrt.Arm.Registers
public import VerifiedSqrt.Arm.Machine64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem Machine.vector_writeD_same (s : Machine) (d : Nat) (hd : d < 32)
    (hs : s.v.size = 32) (w : UInt64) :
    (s.writeD d w).v[d]! = BitVec.ofNat 128 w.toNat := by
  exact Array.getElem!_set!_self s.v d _ (by omega)

theorem Machine.readD_writeD_same (s : Machine) (d : Nat) (hd : d < 32)
    (hs : s.v.size = 32) (w : UInt64) : (s.writeD d w).readD d = w := by
  simp only [Machine.readD, Machine.vector_writeD_same s d hd hs,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show w.toNat < 2 ^ 128 by have hw := w.toNat_lt; omega)]
  simp

theorem Machine.vector_writeD_ne (s : Machine) (d r : Nat) (hne : d ≠ r) (w : UInt64) :
    (s.writeD d w).v[r]! = s.v[r]! :=
  Array.getElem!_set!_ne s.v d r _ hne

theorem Machine.writeD_wellFormed (s : Machine) (h : s.WellFormed) (d : Nat) (w : UInt64) :
    (s.writeD d w).WellFormed := by
  simpa [Machine.WellFormed, Machine.writeD] using h

def Machine.advanceD (s : Machine) (d : Nat) (w : UInt64) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeD d w

theorem Machine.advanceD_pc (s : Machine) (d : Nat) (w : UInt64) :
    (s.advanceD d w).pc = s.pc + 4 := rfl

theorem Machine.advanceD_registers (s : Machine) (d : Nat) (w : UInt64) :
    (s.advanceD d w).x = s.x := rfl

theorem Machine.advanceD_fpcr (s : Machine) (d : Nat) (w : UInt64) :
    (s.advanceD d w).fpcr = s.fpcr := rfl

theorem Machine.advanceD_fpsr (s : Machine) (d : Nat) (w : UInt64) :
    (s.advanceD d w).fpsr = s.fpsr := rfl

theorem Machine.advanceD_vector_size (s : Machine) (d : Nat) (w : UInt64) :
    (s.advanceD d w).v.size = s.v.size := by
  simp [Machine.advanceD, Machine.writeD]

theorem Machine.readW_advanceD (s : Machine) (d r : Nat) (w : UInt64) :
    (s.advanceD d w).readW r = s.readW r := rfl

theorem Machine.readX_advanceD (s : Machine) (d r : Nat) (w : UInt64) :
    (s.advanceD d w).readX r = s.readX r := rfl

theorem Machine.readD_advanceD_same (s : Machine) (d : Nat) (hd : d < 32)
    (hs : s.v.size = 32) (w : UInt64) : (s.advanceD d w).readD d = w :=
  Machine.readD_writeD_same ({s with pc := s.pc + 4} : Machine) d hd hs w

theorem Machine.vector_advanceD_ne (s : Machine) (d r : Nat) (hne : d ≠ r) (w : UInt64) :
    (s.advanceD d w).v[r]! = s.v[r]! :=
  Machine.vector_writeD_ne _ d r hne w

theorem Machine.readD_advanceD_ne (s : Machine) (d r : Nat) (hne : d ≠ r) (w : UInt64) :
    (s.advanceD d w).readD r = s.readD r := by
  simp only [Machine.readD, Machine.vector_advanceD_ne s d r hne w]

def Machine.advanceFP64 (s : Machine) (d : Nat) (w : FPResult64) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeFP64 d w

theorem Machine.advanceFP64_pc (s : Machine) (d : Nat) (w : FPResult64) :
    (s.advanceFP64 d w).pc = s.pc + 4 := rfl

theorem Machine.advanceFP64_registers (s : Machine) (d : Nat) (w : FPResult64) :
    (s.advanceFP64 d w).x = s.x := rfl

theorem Machine.advanceFP64_fpcr (s : Machine) (d : Nat) (w : FPResult64) :
    (s.advanceFP64 d w).fpcr = s.fpcr := rfl

theorem Machine.advanceFP64_vector_size (s : Machine) (d : Nat) (w : FPResult64) :
    (s.advanceFP64 d w).v.size = s.v.size := by
  simp [Machine.advanceFP64, Machine.writeFP64, Machine.writeD]

theorem Machine.readW_advanceFP64 (s : Machine) (d r : Nat) (w : FPResult64) :
    (s.advanceFP64 d w).readW r = s.readW r := rfl

theorem Machine.readX_advanceFP64 (s : Machine) (d r : Nat) (w : FPResult64) :
    (s.advanceFP64 d w).readX r = s.readX r := rfl

theorem Machine.readD_advanceFP64_same (s : Machine) (d : Nat) (hd : d < 32)
    (hs : s.v.size = 32) (w : FPResult64) : (s.advanceFP64 d w).readD d = w.bits :=
  Machine.readD_writeD_same ({s with pc := s.pc + 4} : Machine) d hd hs w.bits

theorem Machine.vector_advanceFP64_ne (s : Machine) (d r : Nat) (hne : d ≠ r) (w : FPResult64) :
    (s.advanceFP64 d w).v[r]! = s.v[r]! :=
  Machine.vector_writeD_ne _ d r hne w.bits

theorem Machine.readD_advanceW (s : Machine) (d r : Nat) (w : UInt32) :
    (s.advanceW d w).readD r = s.readD r := by
  simp only [Machine.readD, Machine.advanceW_vectors]

theorem Machine.readD_advanceX (s : Machine) (d r : Nat) (w : UInt64) :
    (s.advanceX d w).readD r = s.readD r := by
  simp only [Machine.readD, Machine.advanceX_vectors]

theorem Machine.readW_advanceX_same (s : Machine) (d : Nat) (hd : d < 31)
    (hs : s.x.size = 32) (w : UInt64) : (s.advanceX d w).readW d = w.toUInt32 :=
  congrArg UInt64.toUInt32 (Machine.readX_advanceX_same s d hd hs w)

end VerifiedSqrt.Arm
