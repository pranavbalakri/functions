module

public import VerifiedSqrt.Arm.Registers

@[expose] public section

namespace VerifiedSqrt.Arm

def Machine.relocate (base : UInt64) (s : Machine) : Machine :=
  {s with pc := base + s.pc, x := s.x.set! 30 (base + s.readX 30)}

theorem Machine.relocate_pc (base : UInt64) (s : Machine) :
    (s.relocate base).pc = base + s.pc := rfl

theorem Machine.relocate_size (base : UInt64) (s : Machine) :
    (s.relocate base).x.size = s.x.size := by simp [Machine.relocate]

theorem Machine.relocate_vectors (base : UInt64) (s : Machine) :
    (s.relocate base).v = s.v := rfl

theorem Machine.relocate_fpcr (base : UInt64) (s : Machine) :
    (s.relocate base).fpcr = s.fpcr := rfl

theorem Machine.relocate_fpsr (base : UInt64) (s : Machine) :
    (s.relocate base).fpsr = s.fpsr := rfl

theorem Machine.relocate_negative (base : UInt64) (s : Machine) :
    (s.relocate base).negative = s.negative := rfl

theorem Machine.relocate_zero (base : UInt64) (s : Machine) :
    (s.relocate base).zero = s.zero := rfl

theorem Machine.relocate_carry (base : UInt64) (s : Machine) :
    (s.relocate base).carry = s.carry := rfl

theorem Machine.relocate_overflow (base : UInt64) (s : Machine) :
    (s.relocate base).overflow = s.overflow := rfl

theorem Machine.readX_relocate (base : UInt64) (s : Machine) (r : Nat) (hr : r ≠ 30) :
    (s.relocate base).readX r = s.readX r := by
  simp only [Machine.readX, Machine.relocate]
  rw [Array.getElem!_set!_ne _ 30 r _ (Ne.symm hr)]

theorem Machine.readW_relocate (base : UInt64) (s : Machine) (r : Nat) (hr : r ≠ 30) :
    (s.relocate base).readW r = s.readW r := by
  simp only [Machine.readW, Machine.readX_relocate base s r hr]

theorem Machine.readS_relocate (base : UInt64) (s : Machine) (r : Nat) :
    (s.relocate base).readS r = s.readS r := rfl

theorem Machine.readX_relocate_link (base : UInt64) (s : Machine) (hs : s.x.size = 32) :
    (s.relocate base).readX 30 = base + s.readX 30 := by
  simp only [Machine.readX, Machine.relocate, show (30 == 31) = false from rfl,
    Bool.false_eq_true, ite_false]
  exact Array.getElem!_set!_self _ 30 _ (by omega)

theorem Machine.relocate_withPC (base : UInt64) (s : Machine) (pc : UInt64) :
    ({s with pc := pc} : Machine).relocate base = {s.relocate base with pc := base + pc} := rfl

theorem Machine.relocate_writeW (base : UInt64) (s : Machine) (r : Nat) (hr : r < 30)
    (w : UInt32) : (s.writeW r w).relocate base = (s.relocate base).writeW r w := by
  have h31 : r ≠ 31 := by omega
  have h30 : r ≠ 30 := by omega
  have hlink := Machine.readX_writeW_ne s r 30 (by omega) (by decide) h30 w
  unfold Machine.relocate
  rw [hlink]
  simp only [Machine.writeW, beq_iff_eq, ite_eq_right h31]
  congr 1
  exact Array.setIfInBounds_comm _ _ h30

theorem Machine.relocate_writeX (base : UInt64) (s : Machine) (r : Nat) (hr : r < 30)
    (w : UInt64) : (s.writeX r w).relocate base = (s.relocate base).writeX r w := by
  have h31 : r ≠ 31 := by omega
  have h30 : r ≠ 30 := by omega
  have hlink := Machine.readX_writeX_ne s r 30 (by omega) (by decide) h30 w
  unfold Machine.relocate
  rw [hlink]
  simp only [Machine.writeX, beq_iff_eq, ite_eq_right h31]
  congr 1
  exact Array.setIfInBounds_comm _ _ h30

theorem Machine.relocate_writeS (base : UInt64) (s : Machine) (r : Nat) (w : UInt32) :
    (s.writeS r w).relocate base = (s.relocate base).writeS r w := rfl

theorem Machine.relocate_writeFP (base : UInt64) (s : Machine) (r : Nat) (w : FPResult) :
    (s.writeFP r w).relocate base = (s.relocate base).writeFP r w := rfl

theorem Machine.relocate_flags (base : UInt64) (s : Machine) (pc : UInt64) (n z c v : Bool) :
    ({s with pc := pc, negative := n, zero := z, carry := c, overflow := v} : Machine).relocate base =
      {s.relocate base with pc := base + pc, negative := n, zero := z, carry := c, overflow := v} := rfl

theorem word64_ofInt_toNat (w : UInt64) : UInt64.ofInt (w.toNat : Int) = w := by
  rw [UInt64.ofInt, Int.toNat_emod (by omega) (by decide)]
  change UInt64.ofNat (w.toNat % 2 ^ 64) = w
  rw [UInt64.ofNat_mod_size, UInt64.ofNat_toNat]

theorem branchPC_relocate (base pc : UInt64) (offset : Int) :
    branchPC (base + pc) offset = base + branchPC pc offset := by
  change UInt64.ofInt (((base + pc).toNat : Int) + offset) =
    base + UInt64.ofInt ((pc.toNat : Int) + offset)
  rw [UInt64.ofInt_add, UInt64.ofInt_add, word64_ofInt_toNat, word64_ofInt_toNat,
    UInt64.add_assoc]

theorem aligned_relocate (base pc : UInt64) (hb : base.toNat % 4 = 0) :
    (base + pc).toNat % 4 = pc.toNat % 4 := by
  rw [UInt64.toNat_add]
  change ((base.toNat + pc.toNat) % 2 ^ 64) % 4 = pc.toNat % 4
  omega

theorem Machine.relocate_zero_base (s : Machine) (hs : s.x.size = 32) : s.relocate 0 = s := by
  have hi : 30 < s.x.size := by omega
  have hx : s.x.set! 30 (s.readX 30) = s.x := by
    change s.x.setIfInBounds 30 s.x[30]! = s.x
    simp [Array.setIfInBounds, hi, getElem!_pos]
  simp only [Machine.relocate, UInt64.zero_add, hx]

theorem Machine.relocate_add (a b : UInt64) (s : Machine) (hs : s.x.size = 32) :
    (s.relocate b).relocate a = s.relocate (a + b) := by
  have hlink := Machine.readX_relocate_link b s hs
  conv => lhs; rw [Machine.relocate]
  rw [hlink]
  simp only [Machine.relocate, Array.set!_eq_setIfInBounds,
    Array.setIfInBounds_setIfInBounds, UInt64.add_assoc]

theorem Machine.relocate_inverse (base : UInt64) (s : Machine) (hs : s.x.size = 32) :
    (s.relocate (-base)).relocate base = s := by
  rw [Machine.relocate_add base (-base) s hs, UInt64.add_neg_eq_sub,
    UInt64.sub_self, Machine.relocate_zero_base s hs]

end VerifiedSqrt.Arm
