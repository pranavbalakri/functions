module

public import VerifiedSqrt.Arm.Machine

@[expose] public section

namespace VerifiedSqrt.Arm

def Machine.WellFormed (s : Machine) : Prop := s.x.size = 32 ∧ s.v.size = 32

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

end VerifiedSqrt.Arm
