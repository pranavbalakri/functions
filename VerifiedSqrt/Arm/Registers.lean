module

public import VerifiedSqrt.Arm.Machine

@[expose] public section

namespace VerifiedSqrt.Arm

def Machine.WellFormed (s : Machine) : Prop := s.x.size = 32 ∧ s.v.size = 32

theorem Machine.readX_congr (s t : Machine) (h : s.x = t.x) (r : Nat) :
    s.readX r = t.readX r := by
  simp only [Machine.readX, h]

theorem Machine.readW_congr (s t : Machine) (h : s.x = t.x) (r : Nat) :
    s.readW r = t.readW r := by
  exact congrArg UInt64.toUInt32 (Machine.readX_congr s t h r)

theorem Machine.readX_writeX_same (s : Machine) (d : Nat) (hd : d < 31)
    (hs : s.x.size = 32) (w : UInt64) : (s.writeX d w).readX d = w := by
  have hn : d ≠ 31 := by omega
  simpa only [Machine.writeX, Machine.readX, beq_iff_eq, ite_eq_right hn] using
    Array.getElem!_set!_self s.x d w (by omega)

theorem Machine.readX_writeW_same (s : Machine) (d : Nat) (hd : d < 31)
    (hs : s.x.size = 32) (w : UInt32) : (s.writeW d w).readX d = w.toUInt64 := by
  have hn : d ≠ 31 := by omega
  simpa only [Machine.writeW, Machine.readX, beq_iff_eq, ite_eq_right hn] using
    Array.getElem!_set!_self s.x d w.toUInt64 (by omega)

theorem Machine.readW_writeW_same (s : Machine) (d : Nat) (hd : d < 31)
    (hs : s.x.size = 32) (w : UInt32) : (s.writeW d w).readW d = w := by
  simp only [Machine.readW, Machine.readX_writeW_same s d hd hs]
  simp

theorem Machine.readX_writeX_ne (s : Machine) (d r : Nat) (hd : d < 31)
    (hr : r < 31) (hne : d ≠ r) (w : UInt64) :
    (s.writeX d w).readX r = s.readX r := by
  have hd' : d ≠ 31 := by omega
  have hr' : r ≠ 31 := by omega
  simpa only [Machine.writeX, Machine.readX, beq_iff_eq, ite_eq_right hd',
    ite_eq_right hr'] using Array.getElem!_set!_ne s.x d r w hne

theorem Machine.readX_writeW_ne (s : Machine) (d r : Nat) (hd : d < 31)
    (hr : r < 31) (hne : d ≠ r) (w : UInt32) :
    (s.writeW d w).readX r = s.readX r := by
  have hd' : d ≠ 31 := by omega
  have hr' : r ≠ 31 := by omega
  simpa only [Machine.writeW, Machine.readX, beq_iff_eq, ite_eq_right hd',
    ite_eq_right hr'] using Array.getElem!_set!_ne s.x d r w.toUInt64 hne

theorem Machine.vector_writeS_same (s : Machine) (d : Nat) (hd : d < 32)
    (hs : s.v.size = 32) (w : UInt32) :
    (s.writeS d w).v[d]! = BitVec.ofNat 128 w.toNat := by
  exact Array.getElem!_set!_self s.v d _ (by omega)

theorem Machine.readS_writeS_same (s : Machine) (d : Nat) (hd : d < 32)
    (hs : s.v.size = 32) (w : UInt32) : (s.writeS d w).readS d = w := by
  simp only [Machine.readS, Machine.vector_writeS_same s d hd hs,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show w.toNat < 2 ^ 128 by have hw := w.toNat_lt; omega)]
  simp

theorem Machine.vector_writeS_ne (s : Machine) (d r : Nat) (hne : d ≠ r) (w : UInt32) :
    (s.writeS d w).v[r]! = s.v[r]! :=
  Array.getElem!_set!_ne s.v d r _ hne

theorem Machine.writeW_wellFormed (s : Machine) (h : s.WellFormed) (d : Nat) (w : UInt32) :
    (s.writeW d w).WellFormed := by
  simp only [Machine.writeW]
  split
  · exact h
  · simpa [Machine.WellFormed] using h

theorem Machine.writeX_wellFormed (s : Machine) (h : s.WellFormed) (d : Nat) (w : UInt64) :
    (s.writeX d w).WellFormed := by
  simp only [Machine.writeX]
  split
  · exact h
  · simpa [Machine.WellFormed] using h

theorem Machine.writeS_wellFormed (s : Machine) (h : s.WellFormed) (d : Nat) (w : UInt32) :
    (s.writeS d w).WellFormed := by
  simpa [Machine.WellFormed, Machine.writeS] using h

def Machine.advanceW (s : Machine) (d : Nat) (w : UInt32) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeW d w

def Machine.advanceX (s : Machine) (d : Nat) (w : UInt64) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeX d w

def Machine.advanceS (s : Machine) (d : Nat) (w : UInt32) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeS d w

theorem Machine.advanceS_pc (s : Machine) (d : Nat) (w : UInt32) :
    (s.advanceS d w).pc = s.pc + 4 := rfl

theorem Machine.advanceS_registers (s : Machine) (d : Nat) (w : UInt32) :
    (s.advanceS d w).x = s.x := rfl

theorem Machine.advanceS_fpcr (s : Machine) (d : Nat) (w : UInt32) :
    (s.advanceS d w).fpcr = s.fpcr := rfl

theorem Machine.advanceS_fpsr (s : Machine) (d : Nat) (w : UInt32) :
    (s.advanceS d w).fpsr = s.fpsr := rfl

theorem Machine.advanceS_vector_size (s : Machine) (d : Nat) (w : UInt32) :
    (s.advanceS d w).v.size = s.v.size := by
  simp [Machine.advanceS, Machine.writeS]

theorem Machine.readW_advanceS (s : Machine) (d r : Nat) (w : UInt32) :
    (s.advanceS d w).readW r = s.readW r := rfl

theorem Machine.readX_advanceS (s : Machine) (d r : Nat) (w : UInt32) :
    (s.advanceS d w).readX r = s.readX r := rfl

theorem Machine.readS_advanceS_same (s : Machine) (d : Nat) (hd : d < 32)
    (hs : s.v.size = 32) (w : UInt32) : (s.advanceS d w).readS d = w :=
  Machine.readS_writeS_same ({s with pc := s.pc + 4} : Machine) d hd hs w

theorem Machine.vector_advanceS_ne (s : Machine) (d r : Nat) (hne : d ≠ r) (w : UInt32) :
    (s.advanceS d w).v[r]! = s.v[r]! :=
  Machine.vector_writeS_ne _ d r hne w

theorem Machine.readS_advanceS_ne (s : Machine) (d r : Nat) (hne : d ≠ r) (w : UInt32) :
    (s.advanceS d w).readS r = s.readS r := by
  simp only [Machine.readS, Machine.vector_advanceS_ne s d r hne w]

def Machine.advanceFP (s : Machine) (d : Nat) (w : FPResult) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeFP d w

theorem Machine.advanceFP_pc (s : Machine) (d : Nat) (w : FPResult) :
    (s.advanceFP d w).pc = s.pc + 4 := rfl

theorem Machine.advanceFP_registers (s : Machine) (d : Nat) (w : FPResult) :
    (s.advanceFP d w).x = s.x := rfl

theorem Machine.advanceFP_fpcr (s : Machine) (d : Nat) (w : FPResult) :
    (s.advanceFP d w).fpcr = s.fpcr := rfl

theorem Machine.advanceFP_vector_size (s : Machine) (d : Nat) (w : FPResult) :
    (s.advanceFP d w).v.size = s.v.size := by
  simp [Machine.advanceFP, Machine.writeFP, Machine.writeS]

theorem Machine.readW_advanceFP (s : Machine) (d r : Nat) (w : FPResult) :
    (s.advanceFP d w).readW r = s.readW r := rfl

theorem Machine.readX_advanceFP (s : Machine) (d r : Nat) (w : FPResult) :
    (s.advanceFP d w).readX r = s.readX r := rfl

theorem Machine.readS_advanceFP_same (s : Machine) (d : Nat) (hd : d < 32)
    (hs : s.v.size = 32) (w : FPResult) : (s.advanceFP d w).readS d = w.bits :=
  Machine.readS_writeS_same ({s with pc := s.pc + 4} : Machine) d hd hs w.bits

theorem Machine.vector_advanceFP_ne (s : Machine) (d r : Nat) (hne : d ≠ r) (w : FPResult) :
    (s.advanceFP d w).v[r]! = s.v[r]! :=
  Machine.vector_writeS_ne _ d r hne w.bits

theorem Machine.advanceW_pc (s : Machine) (d : Nat) (w : UInt32) :
    (s.advanceW d w).pc = s.pc + 4 := by
  by_cases hd : d = 31 <;> simp [Machine.advanceW, Machine.writeW, hd]

theorem Machine.advanceX_pc (s : Machine) (d : Nat) (w : UInt64) :
    (s.advanceX d w).pc = s.pc + 4 := by
  by_cases hd : d = 31 <;> simp [Machine.advanceX, Machine.writeX, hd]

theorem Machine.advanceW_size (s : Machine) (d : Nat) (w : UInt32) :
    (s.advanceW d w).x.size = s.x.size := by
  by_cases hd : d = 31 <;> simp [Machine.advanceW, Machine.writeW, hd]

theorem Machine.advanceX_size (s : Machine) (d : Nat) (w : UInt64) :
    (s.advanceX d w).x.size = s.x.size := by
  by_cases hd : d = 31 <;> simp [Machine.advanceX, Machine.writeX, hd]

theorem Machine.advanceW_fpcr (s : Machine) (d : Nat) (w : UInt32) :
    (s.advanceW d w).fpcr = s.fpcr := by
  by_cases hd : d = 31 <;> simp [Machine.advanceW, Machine.writeW, hd]

theorem Machine.advanceX_fpcr (s : Machine) (d : Nat) (w : UInt64) :
    (s.advanceX d w).fpcr = s.fpcr := by
  by_cases hd : d = 31 <;> simp [Machine.advanceX, Machine.writeX, hd]

theorem Machine.readW_advanceW_same (s : Machine) (d : Nat) (hd : d < 31)
    (hs : s.x.size = 32) (w : UInt32) : (s.advanceW d w).readW d = w :=
  Machine.readW_writeW_same ({s with pc := s.pc + 4} : Machine) d hd hs w

theorem Machine.readX_advanceW_same (s : Machine) (d : Nat) (hd : d < 31)
    (hs : s.x.size = 32) (w : UInt32) : (s.advanceW d w).readX d = w.toUInt64 :=
  Machine.readX_writeW_same ({s with pc := s.pc + 4} : Machine) d hd hs w

theorem Machine.readW_advanceW_ne (s : Machine) (d r : Nat) (hd : d < 31)
    (hr : r < 31) (hne : d ≠ r) (w : UInt32) : (s.advanceW d w).readW r = s.readW r :=
  congrArg UInt64.toUInt32 (Machine.readX_writeW_ne _ d r hd hr hne w)

theorem Machine.readX_advanceW_ne (s : Machine) (d r : Nat) (hd : d < 31)
    (hr : r < 31) (hne : d ≠ r) (w : UInt32) : (s.advanceW d w).readX r = s.readX r :=
  Machine.readX_writeW_ne _ d r hd hr hne w

theorem Machine.readX_advanceX_same (s : Machine) (d : Nat) (hd : d < 31)
    (hs : s.x.size = 32) (w : UInt64) : (s.advanceX d w).readX d = w :=
  Machine.readX_writeX_same ({s with pc := s.pc + 4} : Machine) d hd hs w

theorem Machine.readW_advanceX_ne (s : Machine) (d r : Nat) (hd : d < 31)
    (hr : r < 31) (hne : d ≠ r) (w : UInt64) : (s.advanceX d w).readW r = s.readW r :=
  congrArg UInt64.toUInt32 (Machine.readX_writeX_ne _ d r hd hr hne w)

theorem Machine.readX_advanceX_ne (s : Machine) (d r : Nat) (hd : d < 31)
    (hr : r < 31) (hne : d ≠ r) (w : UInt64) : (s.advanceX d w).readX r = s.readX r :=
  Machine.readX_writeX_ne _ d r hd hr hne w

theorem Machine.advanceW_vectors (s : Machine) (d : Nat) (w : UInt32) :
    (s.advanceW d w).v = s.v := by
  by_cases hd : d = 31 <;> simp [Machine.advanceW, Machine.writeW, hd]

theorem Machine.advanceX_vectors (s : Machine) (d : Nat) (w : UInt64) :
    (s.advanceX d w).v = s.v := by
  by_cases hd : d = 31 <;> simp [Machine.advanceX, Machine.writeX, hd]

theorem Machine.advanceW_fpsr (s : Machine) (d : Nat) (w : UInt32) :
    (s.advanceW d w).fpsr = s.fpsr := by
  by_cases hd : d = 31 <;> simp [Machine.advanceW, Machine.writeW, hd]

theorem Machine.advanceX_fpsr (s : Machine) (d : Nat) (w : UInt64) :
    (s.advanceX d w).fpsr = s.fpsr := by
  by_cases hd : d = 31 <;> simp [Machine.advanceX, Machine.writeX, hd]

theorem Machine.readS_advanceW (s : Machine) (d r : Nat) (w : UInt32) :
    (s.advanceW d w).readS r = s.readS r := by
  simp only [Machine.readS, Machine.advanceW_vectors]

theorem Machine.readS_advanceX (s : Machine) (d r : Nat) (w : UInt64) :
    (s.advanceX d w).readS r = s.readS r := by
  simp only [Machine.readS, Machine.advanceX_vectors]

end VerifiedSqrt.Arm
