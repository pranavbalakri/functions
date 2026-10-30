module

public import VerifiedSqrt.Arm.Encoding32
public import VerifiedSqrt.Float.Rounding

@[expose] public section

namespace VerifiedSqrt.Arm

theorem binade32_lower (e : Nat) :
    (2 : ℝ) ^ 23 * (2 : ℝ) ^ ((e : Int) - 150) = (2 : ℝ) ^ ((e : Int) - 127) := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

theorem binade32_upper (e : Nat) :
    (2 : ℝ) ^ 24 * (2 : ℝ) ^ ((e : Int) - 150) = (2 : ℝ) ^ ((e : Int) - 126) := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

theorem unpack32_below_binade (x : UInt32) (e : Nat) (elo : 2 ≤ e) (ehi : e ≤ 253)
    (hx : x.toNat < e * 2 ^ 23) :
    (unpack32 x).toReal ≤ (2 : ℝ) ^ ((e : Int) - 127) := by
  have hs := sign32_false_of_lt x (by omega)
  have he : exponent32 x < e := by rw [exponent32_eq_div]; omega
  have hf := fraction32_lt x
  let m := fraction32 x + if exponent32 x == 0 then 0 else 2 ^ 23
  have hm : (m : ℝ) ≤ 2 ^ 24 := by
    have : m ≤ 2 ^ 24 := by dsimp [m]; split <;> omega
    exact_mod_cast this
  have hp : (2 : ℝ) ^ ((max (exponent32 x) 1 : Nat) - (150 : Int)) ≤
      (2 : ℝ) ^ ((e : Int) - 151) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hv : (unpack32 x).toReal =
      (m : ℝ) * (2 : ℝ) ^ ((max (exponent32 x) 1 : Nat) - (150 : Int)) := by
    simp [unpack32, Dyadic.toReal, hs, m]
  rw [hv]
  have hb := mul_le_mul hm hp (by positivity) (by positivity)
  have heq : (2 : ℝ) ^ 24 * (2 : ℝ) ^ ((e : Int) - 151) =
      (2 : ℝ) ^ ((e : Int) - 127) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [heq] at hb
  exact hb

theorem unpack32_above_binade (x : UInt32) (e : Nat) (elo : 2 ≤ e)
    (lo : (e + 1) * 2 ^ 23 ≤ x.toNat) (hi : x.toNat < 2 ^ 31) :
    (2 : ℝ) ^ ((e : Int) - 126) ≤ (unpack32 x).toReal := by
  have hs := sign32_false_of_lt x hi
  have he : e + 1 ≤ exponent32 x := by rw [exponent32_eq_div]; omega
  rw [unpack32_positive_normal x hs (by omega)]
  have hm : (2 ^ 23 : ℝ) ≤ ((2 ^ 23 + fraction32 x : Nat) : ℝ) := by norm_num
  have hp : (2 : ℝ) ^ ((e : Int) - 149) ≤
      (2 : ℝ) ^ ((exponent32 x : Int) - 150) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hb := mul_le_mul hm hp (by positivity) (by positivity)
  have heq : (2 : ℝ) ^ 23 * (2 : ℝ) ^ ((e : Int) - 149) =
      (2 : ℝ) ^ ((e : Int) - 126) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [heq] at hb
  exact hb

theorem grid32_between (x : UInt32) (e : Nat) (elo : 2 ≤ e) (ehi : e ≤ 253)
    (lo : (2 : ℝ) ^ ((e : Int) - 127) ≤ (unpack32 x).toReal)
    (hi : (unpack32 x).toReal ≤ (2 : ℝ) ^ ((e : Int) - 126)) :
    ∃ z : Int, (unpack32 x).toReal = (z : ℝ) * (2 : ℝ) ^ ((e : Int) - 150) := by
  by_cases hl : (unpack32 x).toReal = (2 : ℝ) ^ ((e : Int) - 127)
  · refine ⟨2 ^ 23, ?_⟩
    convert hl.trans (binade32_lower e).symm using 1; norm_num
  by_cases hh : (unpack32 x).toReal = (2 : ℝ) ^ ((e : Int) - 126)
  · refine ⟨2 ^ 24, ?_⟩
    convert hh.trans (binade32_upper e).symm using 1; norm_num
  have hs : x.toNat < 2 ^ 31 := by
    by_contra hn
    have hn := unpack32_nonpos_of_sign x (sign32_true_of_ge x (by omega))
    have hp : (0 : ℝ) < 2 ^ ((e : Int) - 127) := by positivity
    linarith
  have hb1 : e * 2 ^ 23 ≤ x.toNat := by
    by_contra hn
    have hraw : x.toNat < e * 2 ^ 23 := Nat.lt_of_not_ge hn
    have hb := unpack32_below_binade x e elo ehi hraw
    exact hl (le_antisymm hb lo)
  have hb2 : x.toNat < (e + 1) * 2 ^ 23 := by
    by_contra hn
    have hraw : (e + 1) * 2 ^ 23 ≤ x.toNat := Nat.le_of_not_gt hn
    have hb := unpack32_above_binade x e elo hraw hs
    exact hh (le_antisymm hi hb)
  have he : exponent32 x = e := by rw [exponent32_eq_div]; omega
  refine ⟨2 ^ 23 + fraction32 x, ?_⟩
  rw [unpack32_positive_normal _ (sign32_false_of_lt x hs) (by omega), he]
  push_cast
  rfl

end VerifiedSqrt.Arm
