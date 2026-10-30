module

public import Std

@[expose] public section

namespace VerifiedSqrt.Arm

theorem word32_ofInt_nonneg (n : Int) (hn : 0 ≤ n) :
    UInt32.ofInt n = UInt32.ofNat n.toNat := by
  rw [UInt32.ofInt, Int.toNat_emod hn (by decide)]
  change UInt32.ofNat (n.toNat % 2 ^ 32) = UInt32.ofNat n.toNat
  exact UInt32.ofNat_mod_size

theorem word32_ofInt_nat (n : Nat) : UInt32.ofInt (n : Int) = UInt32.ofNat n := by
  rw [word32_ofInt_nonneg _ (by omega), Int.toNat_natCast]

theorem word32_ofInt_toNat (w : UInt32) : UInt32.ofInt (w.toNat : Int) = w := by
  rw [word32_ofInt_nat, UInt32.ofNat_toNat]

theorem word32_shift23 (w : UInt32) : w <<< 23 = w * 0x800000 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_mul]
  change (w.toNat <<< 23) % 2 ^ 32 = (w.toNat * 2 ^ 23) % 2 ^ 32
  rw [Nat.shiftLeft_eq]

theorem word32_shift23_ofInt (k : Int) :
    UInt32.ofInt k <<< 23 = UInt32.ofInt (k * 2 ^ 23) := by
  rw [word32_shift23, UInt32.ofInt_mul]
  rfl

theorem word32_add_shift23 (q : UInt32) (k : Int)
    (hn : 0 ≤ (q.toNat : Int) + k * 2 ^ 23) :
    q + (UInt32.ofInt k <<< 23) = UInt32.ofNat ((q.toNat : Int) + k * 2 ^ 23).toNat := by
  calc
    q + (UInt32.ofInt k <<< 23) = UInt32.ofInt (q.toNat : Int) + UInt32.ofInt (k * 2 ^ 23) := by
      rw [word32_ofInt_toNat, word32_shift23_ofInt]
    _ = UInt32.ofInt ((q.toNat : Int) + k * 2 ^ 23) := (UInt32.ofInt_add _ _).symm
    _ = _ := word32_ofInt_nonneg _ hn

end VerifiedSqrt.Arm
