module

public import VerifiedSqrt.Arm.Machine64

@[expose] public section

namespace VerifiedSqrt.Arm

def wideValue (hi lo : UInt64) : Nat := hi.toNat * 2 ^ 64 + lo.toNat

def wideLess (ahi alo bhi blo : UInt64) : Bool := ahi < bhi || (ahi == bhi && alo < blo)

theorem multiplyHigh64_toNat (a b : UInt64) :
    (multiplyHigh64 a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  rw [multiplyHigh64, UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 64)).mpr
    (Nat.mul_lt_mul_of_lt_of_lt a.toNat_lt b.toNat_lt)

theorem wideValue_product (a b : UInt64) :
    wideValue (multiplyHigh64 a b) (a * b) = a.toNat * b.toNat := by
  rw [wideValue, multiplyHigh64_toNat, UInt64.toNat_mul]
  change (a.toNat * b.toNat / 2 ^ 64) * 2 ^ 64 + (a.toNat * b.toNat) % 2 ^ 64 = _
  omega

theorem wideValue_ofNat (n : Nat) (hn : n < 2 ^ 128) :
    wideValue (UInt64.ofNat (n / 2 ^ 64)) (UInt64.ofNat n) = n := by
  have hd : n / 2 ^ 64 < 2 ^ 64 := by omega
  simp only [wideValue, UInt64.toNat_ofNat']
  change (n / 2 ^ 64) % 2 ^ 64 * 2 ^ 64 + n % 2 ^ 64 = n
  rw [Nat.mod_eq_of_lt hd]
  omega

theorem wideLess_exact (ahi alo bhi blo : UInt64) :
    wideLess ahi alo bhi blo = true ↔ wideValue ahi alo < wideValue bhi blo := by
  simp only [wideLess, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, ← UInt64.toNat_inj, wideValue]
  change (ahi.toNat < bhi.toNat ∨ ahi.toNat = bhi.toNat ∧ alo.toNat < blo.toNat) ↔ _
  have ha := alo.toNat_lt
  have hb := blo.toNat_lt
  omega

theorem double_candidate64_exact (q : UInt64) (hi : q.toNat ≤ 2 ^ 53) :
    (q + q).toNat = 2 * q.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

theorem lower_midpoint64_exact (q : UInt64) (lo : 0 < q.toNat) (hi : q.toNat ≤ 2 ^ 53) :
    (q + q - 1).toNat = 2 * q.toNat - 1 := by
  have hh : (1 : UInt64) ≤ q + q := by
    change 1 ≤ (q + q).toNat
    rw [double_candidate64_exact q hi]
    omega
  rw [UInt64.toNat_sub_of_le _ _ hh, double_candidate64_exact q hi]
  rfl

theorem upper_midpoint64_exact (q : UInt64) (hi : q.toNat ≤ 2 ^ 53) :
    (q + q + 1).toNat = 2 * q.toNat + 1 := by
  rw [UInt64.toNat_add, double_candidate64_exact q hi]
  change (2 * q.toNat + 1) % 2 ^ 64 = _
  exact Nat.mod_eq_of_lt (by omega)

theorem lower_midpoint_square128_exact (q : UInt64)
    (lo : 0 < q.toNat) (hi : q.toNat ≤ 2 ^ 53) :
    wideValue (multiplyHigh64 (q + q - 1) (q + q - 1))
      ((q + q - 1) * (q + q - 1)) = (2 * q.toNat - 1) ^ 2 := by
  rw [wideValue_product, lower_midpoint64_exact q lo hi]
  exact (Nat.pow_two _).symm

theorem upper_midpoint_square128_exact (q : UInt64) (hi : q.toNat ≤ 2 ^ 53) :
    wideValue (multiplyHigh64 (q + q + 1) (q + q + 1))
      ((q + q + 1) * (q + q + 1)) = (2 * q.toNat + 1) ^ 2 := by
  rw [wideValue_product, upper_midpoint64_exact q hi]
  exact (Nat.pow_two _).symm

theorem lower_comparison128_exact (n : Nat) (hn : n < 2 ^ 106) (q : UInt64)
    (lo : 0 < q.toNat) (hi : q.toNat ≤ 2 ^ 53) :
    wideLess (UInt64.ofNat (4 * n / 2 ^ 64)) (UInt64.ofNat (4 * n))
      (multiplyHigh64 (q + q - 1) (q + q - 1)) ((q + q - 1) * (q + q - 1)) = true ↔
      4 * n < (2 * q.toNat - 1) ^ 2 := by
  rw [wideLess_exact, wideValue_ofNat _ (by omega), lower_midpoint_square128_exact q lo hi]

theorem upper_comparison128_exact (n : Nat) (hn : n < 2 ^ 106) (q : UInt64)
    (hi : q.toNat ≤ 2 ^ 53) :
    wideLess (multiplyHigh64 (q + q + 1) (q + q + 1)) ((q + q + 1) * (q + q + 1))
      (UInt64.ofNat (4 * n / 2 ^ 64)) (UInt64.ofNat (4 * n)) = true ↔
      (2 * q.toNat + 1) ^ 2 < 4 * n := by
  rw [wideLess_exact, upper_midpoint_square128_exact q hi, wideValue_ofNat _ (by omega)]

end VerifiedSqrt.Arm
