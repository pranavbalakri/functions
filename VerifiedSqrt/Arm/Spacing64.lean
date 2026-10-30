module

public import VerifiedSqrt.Arm.Encoding64
public import VerifiedSqrt.Float.Rounding

@[expose] public section

namespace VerifiedSqrt.Arm

theorem binade64_lower (e : Nat) :
    (2 : ℝ) ^ 52 * (2 : ℝ) ^ ((e : Int) - 1075) = (2 : ℝ) ^ ((e : Int) - 1023) := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

theorem binade64_upper (e : Nat) :
    (2 : ℝ) ^ 53 * (2 : ℝ) ^ ((e : Int) - 1075) = (2 : ℝ) ^ ((e : Int) - 1022) := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

theorem unpack64_below_binade (x : UInt64) (e : Nat) (elo : 2 ≤ e) (ehi : e ≤ 2045)
    (hx : x.toNat < e * 2 ^ 52) :
    (unpack64 x).toReal ≤ (2 : ℝ) ^ ((e : Int) - 1023) := by
  have hs := sign64_false_of_lt x (by omega)
  have he : exponent64 x < e := by rw [exponent64_eq_div]; omega
  have hf := fraction64_lt x
  let m := fraction64 x + if exponent64 x == 0 then 0 else 2 ^ 52
  have hm : (m : ℝ) ≤ 2 ^ 53 := by
    have : m ≤ 2 ^ 53 := by dsimp [m]; split <;> omega
    exact_mod_cast this
  have hp : (2 : ℝ) ^ ((max (exponent64 x) 1 : Nat) - (1075 : Int)) ≤
      (2 : ℝ) ^ ((e : Int) - 1076) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hv : (unpack64 x).toReal =
      (m : ℝ) * (2 : ℝ) ^ ((max (exponent64 x) 1 : Nat) - (1075 : Int)) := by
    simp [unpack64, Dyadic.toReal, hs, m]
  rw [hv]
  have hb := mul_le_mul hm hp (by positivity) (by positivity)
  have heq : (2 : ℝ) ^ 53 * (2 : ℝ) ^ ((e : Int) - 1076) =
      (2 : ℝ) ^ ((e : Int) - 1023) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [heq] at hb
  exact hb

theorem unpack64_above_binade (x : UInt64) (e : Nat) (elo : 2 ≤ e)
    (lo : (e + 1) * 2 ^ 52 ≤ x.toNat) (hi : x.toNat < 2 ^ 63) :
    (2 : ℝ) ^ ((e : Int) - 1022) ≤ (unpack64 x).toReal := by
  have hs := sign64_false_of_lt x hi
  have he : e + 1 ≤ exponent64 x := by rw [exponent64_eq_div]; omega
  rw [unpack64_positive_normal x hs (by omega)]
  have hm : (2 ^ 52 : ℝ) ≤ ((2 ^ 52 + fraction64 x : Nat) : ℝ) := by norm_num
  have hp : (2 : ℝ) ^ ((e : Int) - 1074) ≤
      (2 : ℝ) ^ ((exponent64 x : Int) - 1075) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hb := mul_le_mul hm hp (by positivity) (by positivity)
  have heq : (2 : ℝ) ^ 52 * (2 : ℝ) ^ ((e : Int) - 1074) =
      (2 : ℝ) ^ ((e : Int) - 1022) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [heq] at hb
  exact hb

theorem grid64_between (x : UInt64) (e : Nat) (elo : 2 ≤ e) (ehi : e ≤ 2045)
    (lo : (2 : ℝ) ^ ((e : Int) - 1023) ≤ (unpack64 x).toReal)
    (hi : (unpack64 x).toReal ≤ (2 : ℝ) ^ ((e : Int) - 1022)) :
    ∃ z : Int, (unpack64 x).toReal = (z : ℝ) * (2 : ℝ) ^ ((e : Int) - 1075) := by
  by_cases hl : (unpack64 x).toReal = (2 : ℝ) ^ ((e : Int) - 1023)
  · refine ⟨2 ^ 52, ?_⟩
    convert hl.trans (binade64_lower e).symm using 1; norm_num
  by_cases hh : (unpack64 x).toReal = (2 : ℝ) ^ ((e : Int) - 1022)
  · refine ⟨2 ^ 53, ?_⟩
    convert hh.trans (binade64_upper e).symm using 1; norm_num
  have hs : x.toNat < 2 ^ 63 := by
    by_contra hn
    have hn := unpack64_nonpos_of_sign x (sign64_true_of_ge x (by omega))
    have hp : (0 : ℝ) < 2 ^ ((e : Int) - 1023) := by positivity
    linarith
  have hb1 : e * 2 ^ 52 ≤ x.toNat := by
    by_contra hn
    have hraw : x.toNat < e * 2 ^ 52 := Nat.lt_of_not_ge hn
    have hb := unpack64_below_binade x e elo ehi hraw
    exact hl (le_antisymm hb lo)
  have hb2 : x.toNat < (e + 1) * 2 ^ 52 := by
    by_contra hn
    have hraw : (e + 1) * 2 ^ 52 ≤ x.toNat := Nat.le_of_not_gt hn
    have hb := unpack64_above_binade x e elo hraw hs
    exact hh (le_antisymm hi hb)
  have he : exponent64 x = e := by rw [exponent64_eq_div]; omega
  refine ⟨2 ^ 52 + fraction64 x, ?_⟩
  rw [unpack64_positive_normal _ (sign64_false_of_lt x hs) (by omega), he]
  push_cast
  rfl

end VerifiedSqrt.Arm
