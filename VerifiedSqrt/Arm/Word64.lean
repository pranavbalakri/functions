module

public import VerifiedSqrt.Arm.SignedWord32

@[expose] public section

namespace VerifiedSqrt.Arm

theorem word64_ofInt_nonneg (n : Int) (hn : 0 ≤ n) :
    UInt64.ofInt n = UInt64.ofNat n.toNat := by
  rw [UInt64.ofInt, Int.toNat_emod hn (by decide)]
  change UInt64.ofNat (n.toNat % 2 ^ 64) = UInt64.ofNat n.toNat
  exact UInt64.ofNat_mod_size

theorem word64_ofInt_nat (n : Nat) : UInt64.ofInt (n : Int) = UInt64.ofNat n := by
  rw [word64_ofInt_nonneg _ (by omega), Int.toNat_natCast]

theorem word64_ofInt_toNat (w : UInt64) : UInt64.ofInt (w.toNat : Int) = w := by
  rw [word64_ofInt_nat, UInt64.ofNat_toNat]

theorem word64_shift52 (w : UInt64) : w <<< 52 = w * 0x10000000000000 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_mul]
  change (w.toNat <<< 52) % 2 ^ 64 = (w.toNat * 2 ^ 52) % 2 ^ 64
  rw [Nat.shiftLeft_eq]

theorem word64_shift52_ofInt (k : Int) :
    UInt64.ofInt k <<< 52 = UInt64.ofInt (k * 2 ^ 52) := by
  rw [word64_shift52, UInt64.ofInt_mul]
  rfl

theorem word64_add_shift52 (q : UInt64) (k : Int)
    (hn : 0 ≤ (q.toNat : Int) + k * 2 ^ 52) :
    q + (UInt64.ofInt k <<< 52) = UInt64.ofNat ((q.toNat : Int) + k * 2 ^ 52).toNat := by
  calc
    q + (UInt64.ofInt k <<< 52) = UInt64.ofInt (q.toNat : Int) + UInt64.ofInt (k * 2 ^ 52) := by
      rw [word64_ofInt_toNat, word64_shift52_ofInt]
    _ = UInt64.ofInt ((q.toNat : Int) + k * 2 ^ 52) := (UInt64.ofInt_add _ _).symm
    _ = _ := word64_ofInt_nonneg _ hn

theorem word64_shift52_low32 (w : UInt64) (k : Int)
    (hk : w.toUInt32 = UInt32.ofInt k) :
    w <<< 52 = UInt64.ofInt k <<< 52 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_shiftLeft]
  change (w.toNat <<< 52) % 2 ^ 64 = ((UInt64.ofInt k).toNat <<< 52) % 2 ^ 64
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have hw := congrArg UInt32.toNat hk
  rw [UInt64.toNat_toUInt32, word32_ofInt_bits] at hw
  have hb : (UInt64.ofInt k).toNat = (k % 2 ^ 64).toNat := by
    have h0 : 0 ≤ k % 2 ^ 64 := Int.emod_nonneg _ (by decide)
    have h1 : k % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by decide)
    unfold UInt64.ofInt
    rw [UInt64.toNat_ofNat']
    omega
  rw [hb]
  have h0 : 0 ≤ k % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h1 : 0 ≤ k % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  omega

end VerifiedSqrt.Arm
