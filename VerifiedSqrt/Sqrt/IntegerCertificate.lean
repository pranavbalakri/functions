module

public import VerifiedSqrt.Float.Real
public import VerifiedSqrt.Float.Rounding
public import VerifiedSqrt.Sqrt.IntegerCorrection

@[expose] public section

namespace VerifiedSqrt.Sqrt

def IntegerRootCertificate (n q : Nat) : Prop :=
  0 < q ∧ (2 * q - 1) ^ 2 < 4 * n ∧ 4 * n < (2 * q + 1) ^ 2

def roundedIntegerRoot (n : Nat) : Nat :=
  let q := n.sqrt
  if (2 * q + 1) ^ 2 < 4 * n then q + 1 else q

theorem odd_square_ne_four_mul (n q : Nat) : (2 * q + 1) ^ 2 ≠ 4 * n := by
  have he : (2 * q + 1) ^ 2 = 4 * (q * q + q) + 1 := by ring
  omega

theorem roundedIntegerRoot_certificate (n : Nat) (hn : 0 < n) :
    IntegerRootCertificate n (roundedIntegerRoot n) := by
  have hlo := Nat.sqrt_le n
  have hhi := Nat.lt_succ_sqrt n
  have hp := Nat.sqrt_pos.mpr hn
  have hne := odd_square_ne_four_mul n n.sqrt
  simp only [roundedIntegerRoot, IntegerRootCertificate]
  split
  · rename_i h
    have hs : 2 * (n.sqrt + 1) - 1 = 2 * n.sqrt + 1 := by omega
    rw [hs]
    exact ⟨by omega, h, by nlinarith⟩
  · rename_i h
    have hs : 2 * n.sqrt - 1 + 1 = 2 * n.sqrt := by omega
    exact ⟨hp, by nlinarith, by omega⟩

theorem integerRootCertificate_nearest {n q : Nat} (h : IntegerRootCertificate n q) :
    NearestEvenInteger (Real.sqrt n) q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast h.1
  have hsub : 1 ≤ 2 * q := by have hq := h.1; omega
  have hlo : ((2 * q - 1) ^ 2 : Nat) < (4 * n : ℝ) := by exact_mod_cast h.2.1
  have hhi : (4 * n : ℝ) < (2 * q + 1) ^ 2 := by exact_mod_cast h.2.2
  push_cast [Nat.cast_sub hsub] at hlo
  have hb := midpoint_certificate n q (by positivity) hqR hlo hhi
  apply nearestEvenInteger_of_lt
  simp only [Int.cast_natCast]
  exact abs_lt.mpr ⟨by linarith [hb.2], by linarith [hb.1]⟩

theorem integerRootCertificate_unique {n q : Nat} (hn : 0 < n)
    (h : IntegerRootCertificate n q) : q = roundedIntegerRoot n := by
  have he := nearestEvenInteger_unique (integerRootCertificate_nearest h)
    (integerRootCertificate_nearest (roundedIntegerRoot_certificate n hn))
  exact_mod_cast he

theorem integerRootCertificate_lower_test {n r : Nat}
    (h : IntegerRootCertificate n r) (q : Nat) :
    4 * n < (2 * q - 1) ^ 2 ↔ r < q := by
  constructor
  · intro ht
    by_contra hn
    have he : (2 * q - 1) ^ 2 ≤ (2 * r - 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hr := h.2.1
    omega
  · intro ht
    have he : (2 * r + 1) ^ 2 ≤ (2 * q - 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    exact h.2.2.trans_le he

theorem integerRootCertificate_upper_test {n r : Nat}
    (h : IntegerRootCertificate n r) (q : Nat) :
    (2 * q + 1) ^ 2 < 4 * n ↔ q < r := by
  constructor
  · intro ht
    by_contra hn
    have he : (2 * r + 1) ^ 2 ≤ (2 * q + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hr := h.2.2
    omega
  · intro ht
    have he : (2 * q + 1) ^ 2 ≤ (2 * r - 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    exact he.trans_lt h.2.1

theorem correctIntegerRoot_eq {n r : Nat} (h : IntegerRootCertificate n r)
    (fuel q : Nat) (hf : q - r + (r - q) ≤ fuel) :
    correctIntegerRoot n fuel q = r := by
  induction fuel generalizing q with
  | zero => simp only [correctIntegerRoot]; omega
  | succ fuel ih =>
    simp only [correctIntegerRoot, integerRootCertificate_lower_test h,
      integerRootCertificate_upper_test h]
    split
    · rename_i hq
      exact ih _ (by omega)
    · rename_i hq
      split
      · rename_i hq'
        exact ih _ (by omega)
      · omega

theorem correctIntegerRoot_certificate (n q fuel : Nat) (hn : 0 < n)
    (hf : q - roundedIntegerRoot n + (roundedIntegerRoot n - q) ≤ fuel) :
    IntegerRootCertificate n (correctIntegerRoot n fuel q) := by
  have hc := roundedIntegerRoot_certificate n hn
  rw [correctIntegerRoot_eq hc fuel q hf]
  exact hc

end VerifiedSqrt.Sqrt
