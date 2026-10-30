module

public import VerifiedSqrt.Arm.SignedWord32
public import VerifiedSqrt.Sqrt.Normalization64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem word64_unbiased_exponent (x : UInt64) :
    UInt32.ofNat (exponent64 x) - 1023 = UInt32.ofInt ((exponent64 x : Int) - 1023) := by
  rw [word32_ofInt_sub, word32_ofInt_nat]
  rfl

theorem word64_root_exponent (x : UInt64) :
    signedWord32 (UInt32.ofNat (exponent64 x) - 1023) / 2 = Sqrt.rootExponent64 x := by
  have he := exponent64_lt x
  rw [word64_unbiased_exponent, signedWord32_ofInt _ (by omega) (by omega)]
  rfl

theorem word64_normalized_input (x : UInt64) :
    (x &&& (0xfffffffffffff : UInt64)) |||
      ((((UInt32.ofNat (exponent64 x) - 1023) &&& 1) + 1023).toUInt64 <<< 52) =
        Sqrt.normalizedInput64 x := by
  rw [word64_unbiased_exponent, word32_ofInt_parity]
  let p := (((exponent64 x : Int) - 1023) % 2).toNat
  have hp : p ≤ 1 := by dsimp [p]; omega
  have hf := fraction64_lt x
  have ha : (UInt32.ofNat p + 1023).toNat = p + 1023 := by
    rw [UInt32.toNat_add, UInt32.toNat_ofNat']
    change (p % 2 ^ 32 + 1023) % 2 ^ 32 = _
    omega
  have hb : ((UInt32.ofNat p + 1023).toUInt64 <<< 52).toNat = (p + 1023) * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, ha]
    change ((p + 1023) <<< 52) % 2 ^ 64 = _
    rw [Nat.shiftLeft_eq]
    omega
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or, hb]
  change fraction64 x ||| ((p + 1023) * 2 ^ 52) = (Sqrt.normalizedInput64 x).toNat
  rw [Nat.or_comm, Nat.mul_comm (p + 1023), ← Nat.two_pow_add_eq_or_of_lt hf]
  unfold Sqrt.normalizedInput64
  rw [UInt64.toNat_ofNat']
  change 2 ^ 52 * (p + 1023) + fraction64 x =
    (fraction64 x + (1023 + p) * 2 ^ 52) % 2 ^ 64
  omega

end VerifiedSqrt.Arm
