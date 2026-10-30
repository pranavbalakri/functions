module

public import Std

@[expose] public section

namespace VerifiedSqrt.Arm

theorem umull_exact (a b : UInt32) :
    (a.toUInt64 * b.toUInt64).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  apply Nat.mod_eq_of_lt
  calc
    a.toNat * b.toNat ≤ 2 ^ 32 * b.toNat :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt a.toNat_lt)
    _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_left b.toNat_lt (by decide)
    _ = 2 ^ 64 := by decide

theorem double_candidate_exact (q : UInt32) (hi : q.toNat ≤ 2 ^ 24) :
    (q + q).toNat = 2 * q.toNat := by
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

theorem lower_midpoint_exact (q : UInt32) (lo : 0 < q.toNat) (hi : q.toNat ≤ 2 ^ 24) :
    (q + q - 1).toNat = 2 * q.toNat - 1 := by
  have hh : (1 : UInt32) ≤ q + q := by
    change 1 ≤ (q + q).toNat
    rw [double_candidate_exact q hi]
    omega
  rw [UInt32.toNat_sub_of_le _ _ hh, double_candidate_exact q hi]
  rfl

theorem upper_midpoint_exact (q : UInt32) (hi : q.toNat ≤ 2 ^ 24) :
    (q + q + 1).toNat = 2 * q.toNat + 1 := by
  rw [UInt32.toNat_add, double_candidate_exact q hi]
  change (2 * q.toNat + 1) % 2 ^ 32 = _
  exact Nat.mod_eq_of_lt (by omega)

theorem lower_midpoint_square_exact (q : UInt32)
    (lo : 0 < q.toNat) (hi : q.toNat ≤ 2 ^ 24) :
    ((q + q - 1).toUInt64 * (q + q - 1).toUInt64).toNat = (2 * q.toNat - 1) ^ 2 := by
  rw [umull_exact, lower_midpoint_exact q lo hi]
  exact (Nat.pow_two _).symm

theorem upper_midpoint_square_exact (q : UInt32) (hi : q.toNat ≤ 2 ^ 24) :
    ((q + q + 1).toUInt64 * (q + q + 1).toUInt64).toNat = (2 * q.toNat + 1) ^ 2 := by
  rw [umull_exact, upper_midpoint_exact q hi]
  exact (Nat.pow_two _).symm

theorem scaled_radicand_exact (n : Nat) (hi : n < 2 ^ 48) :
    (UInt64.ofNat (4 * n)).toNat = 4 * n := by
  apply Nat.mod_eq_of_lt
  omega

theorem lower_comparison_exact (n : Nat) (hn : n < 2 ^ 48) (q : UInt32)
    (lo : 0 < q.toNat) (hi : q.toNat ≤ 2 ^ 24) :
    UInt64.ofNat (4 * n) < (q + q - 1).toUInt64 * (q + q - 1).toUInt64 ↔
      4 * n < (2 * q.toNat - 1) ^ 2 := by
  change (UInt64.ofNat (4 * n)).toNat <
    ((q + q - 1).toUInt64 * (q + q - 1).toUInt64).toNat ↔ _
  rw [scaled_radicand_exact n hn, lower_midpoint_square_exact q lo hi]

theorem upper_comparison_exact (n : Nat) (hn : n < 2 ^ 48) (q : UInt32)
    (hi : q.toNat ≤ 2 ^ 24) :
    (q + q + 1).toUInt64 * (q + q + 1).toUInt64 < UInt64.ofNat (4 * n) ↔
      (2 * q.toNat + 1) ^ 2 < 4 * n := by
  change ((q + q + 1).toUInt64 * (q + q + 1).toUInt64).toNat <
    (UInt64.ofNat (4 * n)).toNat ↔ _
  rw [scaled_radicand_exact n hn, upper_midpoint_square_exact q hi]

end VerifiedSqrt.Arm
