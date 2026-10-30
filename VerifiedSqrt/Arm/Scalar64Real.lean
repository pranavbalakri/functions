module

public import VerifiedSqrt.Arm.Scalar64
public import VerifiedSqrt.Float.DyadicReal

@[expose] public section

namespace VerifiedSqrt.Arm

theorem fraction64_eq_mod (x : UInt64) : fraction64 x = x.toNat % 2 ^ 52 := by
  simp only [fraction64, UInt64.toNat_and]
  change x.toNat &&& (2 ^ 52 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem exponent64_eq_div (x : UInt64) : exponent64 x = x.toNat / 2 ^ 52 % 2048 := by
  simp only [exponent64, UInt64.toNat_and, UInt64.toNat_shiftRight]
  change (x.toNat >>> 52) &&& (2 ^ 11 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fraction64_lt (x : UInt64) : fraction64 x < 2 ^ 52 := by
  rw [fraction64_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem exponent64_lt (x : UInt64) : exponent64 x < 2048 := by
  rw [exponent64_eq_div]
  exact Nat.mod_lt _ (by decide)

theorem sign64_false_of_lt (x : UInt64) (h : x.toNat < 2 ^ 63) : sign64 x = false := by
  have hh : x &&& 0x8000000000000000 = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and]
    change x.toNat &&& 2 ^ 63 = 0
    have hb : x.toNat &&& 2 ^ 63 < 2 ^ 63 := lt_of_le_of_lt Nat.and_le_left h
    rw [← Nat.mod_eq_of_lt hb, Nat.and_mod_two_pow]
    simp
  simp [sign64, hh]

theorem unpack64_positive_normal (x : UInt64) (hs : sign64 x = false)
    (he : 0 < exponent64 x) :
    (unpack64 x).toReal =
      ((2 ^ 52 + fraction64 x : Nat) : ℝ) * (2 : ℝ) ^ ((exponent64 x : Int) - 1075) := by
  simp [unpack64, Dyadic.toReal, hs, Nat.ne_of_gt he,
    max_eq_left (by omega : 1 ≤ exponent64 x),
    Nat.add_comm]

theorem sign64_true_of_ge (x : UInt64) (h : 2 ^ 63 ≤ x.toNat) : sign64 x = true := by
  have ht : x.toNat.testBit 63 = true :=
    Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h x.toNat_lt
  have hn : x &&& 0x8000000000000000 ≠ 0 := by
    intro he
    have hb := congrArg (fun w : UInt64 => w.toNat.testBit 63) he
    simp only [UInt64.toNat_and] at hb
    change (x.toNat &&& 2 ^ 63).testBit 63 = (0 : Nat).testBit 63 at hb
    rw [Nat.testBit_and, ht, Nat.testBit_two_pow_self] at hb
    contradiction
  simpa [sign64] using hn

theorem unpack64_nonpos_of_sign (x : UInt64) (hs : sign64 x = true) :
    (unpack64 x).toReal ≤ 0 := by
  simp only [unpack64, Dyadic.toReal, hs, ite_true, Int.cast_neg,
    Int.cast_natCast]
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (by positivity)
  · positivity

theorem unpack64_le_one (x : UInt64) (h : x.toNat < 0x3ff0000000000000) :
    (unpack64 x).toReal ≤ 1 := by
  have hs := sign64_false_of_lt x (by omega)
  have he : exponent64 x ≤ 1022 := by rw [exponent64_eq_div]; norm_num; omega
  have hf := fraction64_lt x
  let m := fraction64 x + if exponent64 x == 0 then 0 else 2 ^ 52
  have hm : (m : ℝ) ≤ 2 ^ 53 := by
    have : m ≤ 2 ^ 53 := by dsimp [m]; split <;> omega
    exact_mod_cast this
  have hp : (2 : ℝ) ^ ((max (exponent64 x) 1 : Nat) - (1075 : Int)) ≤
      (2 : ℝ) ^ (-53 : Int) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hv : (unpack64 x).toReal =
      (m : ℝ) * (2 : ℝ) ^ ((max (exponent64 x) 1 : Nat) - (1075 : Int)) := by
    simp [unpack64, Dyadic.toReal, hs, m]
  rw [hv]
  have hh := mul_le_mul hm hp (by positivity) (by positivity)
  norm_num at hh
  simpa using hh

theorem unpack64_ge_two (x : UInt64) (lo : 0x4000000000000000 ≤ x.toNat)
    (hi : x.toNat < 2 ^ 63) : 2 ≤ (unpack64 x).toReal := by
  have hs := sign64_false_of_lt x hi
  have he : 1024 ≤ exponent64 x := by rw [exponent64_eq_div]; norm_num at *; omega
  rw [unpack64_positive_normal x hs (by omega)]
  have hm : (2 ^ 52 : ℝ) ≤ ((2 ^ 52 + fraction64 x : Nat) : ℝ) := by
    norm_num
  have hp : (2 : ℝ) ^ (-51 : Int) ≤ (2 : ℝ) ^ ((exponent64 x : Int) - 1075) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hh := mul_le_mul hm hp (by positivity) (by positivity)
  norm_num at hh
  simpa using hh

end VerifiedSqrt.Arm
