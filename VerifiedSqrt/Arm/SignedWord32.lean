module

public import VerifiedSqrt.Arm.Classification32
public import VerifiedSqrt.Arm.Word32

@[expose] public section

namespace VerifiedSqrt.Arm

def signedWord32 (w : UInt32) : Int :=
  if sign32 w then (w.toNat : Int) - 2 ^ 32 else w.toNat

theorem word32_ofInt_bits (n : Int) :
    (UInt32.ofInt n).toNat = (n % 2 ^ 32).toNat := by
  have h0 : 0 ≤ n % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h1 : n % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  unfold UInt32.ofInt
  rw [UInt32.toNat_ofNat']
  omega

theorem signedWord32_ofInt (n : Int) (lo : -(2 ^ 31) ≤ n) (hi : n < 2 ^ 31) :
    signedWord32 (UInt32.ofInt n) = n := by
  have hb := word32_ofInt_bits n
  by_cases hn : 0 ≤ n
  · have hm : n % 2 ^ 32 = n := Int.emod_eq_of_lt hn (by omega)
    rw [hm] at hb
    have hs := sign32_false_of_lt (UInt32.ofInt n) (by omega)
    simp only [signedWord32, hs, Bool.false_eq_true, ite_false, hb]
    omega
  · have hm : n % 2 ^ 32 = n + 2 ^ 32 := by omega
    rw [hm] at hb
    have hs := sign32_true_of_ge (UInt32.ofInt n) (by omega)
    simp only [signedWord32, hs, ite_true, hb]
    omega

theorem word32_ofInt_parity (n : Int) :
    UInt32.ofInt n &&& 1 = UInt32.ofNat (n % 2).toNat := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_ofNat']
  change (UInt32.ofInt n).toNat &&& (2 ^ 1 - 1) = (n % 2).toNat % 2 ^ 32
  rw [Nat.and_two_pow_sub_one_eq_mod, word32_ofInt_bits]
  have h0 : 0 ≤ n % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h1 : n % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  omega

theorem word32_ofInt_sub (m n : Int) :
    UInt32.ofInt (m - n) = UInt32.ofInt m - UInt32.ofInt n := by
  rw [Int.sub_eq_add_neg, UInt32.ofInt_add, UInt32.ofInt_neg, UInt32.sub_eq_add_neg]

end VerifiedSqrt.Arm
