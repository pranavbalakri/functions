module

public import VerifiedSqrt.Arm.SignedWord32
public import VerifiedSqrt.Sqrt.Normalization32

@[expose] public section

namespace VerifiedSqrt.Arm

theorem word32_unbiased_exponent (x : UInt32) :
    UInt32.ofNat (exponent32 x) - 127 = UInt32.ofInt ((exponent32 x : Int) - 127) := by
  rw [word32_ofInt_sub, word32_ofInt_nat]
  rfl

theorem word32_root_exponent (x : UInt32) :
    signedWord32 (UInt32.ofNat (exponent32 x) - 127) / 2 = Sqrt.rootExponent32 x := by
  have he := exponent32_lt x
  rw [word32_unbiased_exponent, signedWord32_ofInt _ (by omega) (by omega)]
  rfl

theorem word32_normalized_input (x : UInt32) :
    (x &&& (0x7fffff : UInt32)) |||
      ((((UInt32.ofNat (exponent32 x) - 127) &&& 1) + 127) <<< 23) =
        Sqrt.normalizedInput32 x := by
  rw [word32_unbiased_exponent, word32_ofInt_parity]
  let p := (((exponent32 x : Int) - 127) % 2).toNat
  have hp : p ≤ 1 := by dsimp [p]; omega
  have hf := fraction32_lt x
  have ha : (UInt32.ofNat p + 127).toNat = p + 127 := by
    rw [UInt32.toNat_add, UInt32.toNat_ofNat']
    change (p % 2 ^ 32 + 127) % 2 ^ 32 = _
    omega
  have hb : ((UInt32.ofNat p + 127) <<< 23).toNat = (p + 127) * 2 ^ 23 := by
    rw [UInt32.toNat_shiftLeft, ha]
    change ((p + 127) <<< 23) % 2 ^ 32 = _
    rw [Nat.shiftLeft_eq]
    omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_or, hb]
  change fraction32 x ||| ((p + 127) * 2 ^ 23) = (Sqrt.normalizedInput32 x).toNat
  rw [Nat.or_comm, Nat.mul_comm (p + 127), ← Nat.two_pow_add_eq_or_of_lt hf]
  unfold Sqrt.normalizedInput32
  rw [UInt32.toNat_ofNat']
  change 2 ^ 23 * (p + 127) + fraction32 x =
    (fraction32 x + (127 + p) * 2 ^ 23) % 2 ^ 32
  omega

end VerifiedSqrt.Arm
