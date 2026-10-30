module

public import VerifiedSqrt.Arm.Scalar32
public import VerifiedSqrt.Float.DyadicReal

@[expose] public section

namespace VerifiedSqrt.Arm

theorem fraction32_eq_mod (x : UInt32) : fraction32 x = x.toNat % 2 ^ 23 := by
  simp only [fraction32, UInt32.toNat_and]
  change x.toNat &&& (2 ^ 23 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem exponent32_eq_div (x : UInt32) : exponent32 x = x.toNat / 2 ^ 23 % 256 := by
  simp only [exponent32, UInt32.toNat_and, UInt32.toNat_shiftRight]
  change (x.toNat >>> 23) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fraction32_lt (x : UInt32) : fraction32 x < 2 ^ 23 := by
  rw [fraction32_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem exponent32_lt (x : UInt32) : exponent32 x < 256 := by
  rw [exponent32_eq_div]
  exact Nat.mod_lt _ (by decide)

theorem sign32_false_of_lt (x : UInt32) (h : x.toNat < 2 ^ 31) : sign32 x = false := by
  have hh : x &&& 0x80000000 = 0 := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_and]
    change x.toNat &&& 2 ^ 31 = 0
    have hb : x.toNat &&& 2 ^ 31 < 2 ^ 31 := lt_of_le_of_lt Nat.and_le_left h
    rw [← Nat.mod_eq_of_lt hb, Nat.and_mod_two_pow]
    simp
  simp [sign32, hh]

theorem unpack32_positive_normal (x : UInt32) (hs : sign32 x = false)
    (he : 0 < exponent32 x) :
    (unpack32 x).toReal =
      ((2 ^ 23 + fraction32 x : Nat) : ℝ) * (2 : ℝ) ^ ((exponent32 x : Int) - 150) := by
  simp [unpack32, Dyadic.toReal, hs, Nat.ne_of_gt he,
    max_eq_left (by omega : 1 ≤ exponent32 x),
    Nat.add_comm]

theorem sign32_true_of_ge (x : UInt32) (h : 2 ^ 31 ≤ x.toNat) : sign32 x = true := by
  have ht : x.toNat.testBit 31 = true :=
    Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h x.toNat_lt
  have hn : x &&& 0x80000000 ≠ 0 := by
    intro he
    have hb := congrArg (fun w : UInt32 => w.toNat.testBit 31) he
    simp only [UInt32.toNat_and] at hb
    change (x.toNat &&& 2 ^ 31).testBit 31 = (0 : Nat).testBit 31 at hb
    rw [Nat.testBit_and, ht, Nat.testBit_two_pow_self] at hb
    contradiction
  simpa [sign32] using hn

theorem unpack32_nonpos_of_sign (x : UInt32) (hs : sign32 x = true) :
    (unpack32 x).toReal ≤ 0 := by
  simp only [unpack32, Dyadic.toReal, hs, ite_true, Int.cast_neg,
    Int.cast_natCast]
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (by positivity)
  · positivity

theorem unpack32_le_one (x : UInt32) (h : x.toNat < 0x3f800000) :
    (unpack32 x).toReal ≤ 1 := by
  have hs := sign32_false_of_lt x (by omega)
  have he : exponent32 x ≤ 126 := by rw [exponent32_eq_div]; norm_num; omega
  have hf := fraction32_lt x
  let m := fraction32 x + if exponent32 x == 0 then 0 else 2 ^ 23
  have hm : (m : ℝ) ≤ 2 ^ 24 := by
    have : m ≤ 2 ^ 24 := by dsimp [m]; split <;> omega
    exact_mod_cast this
  have hp : (2 : ℝ) ^ ((max (exponent32 x) 1 : Nat) - (150 : Int)) ≤
      (2 : ℝ) ^ (-24 : Int) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hv : (unpack32 x).toReal =
      (m : ℝ) * (2 : ℝ) ^ ((max (exponent32 x) 1 : Nat) - (150 : Int)) := by
    simp [unpack32, Dyadic.toReal, hs, m]
  rw [hv]
  have hh := mul_le_mul hm hp (by positivity) (by positivity)
  norm_num at hh
  simpa using hh

theorem unpack32_ge_two (x : UInt32) (lo : 0x40000000 ≤ x.toNat)
    (hi : x.toNat < 2 ^ 31) : 2 ≤ (unpack32 x).toReal := by
  have hs := sign32_false_of_lt x hi
  have he : 128 ≤ exponent32 x := by rw [exponent32_eq_div]; norm_num at *; omega
  rw [unpack32_positive_normal x hs (by omega)]
  have hm : (2 ^ 23 : ℝ) ≤ ((2 ^ 23 + fraction32 x : Nat) : ℝ) := by
    norm_num
  have hp : (2 : ℝ) ^ (-22 : Int) ≤ (2 : ℝ) ^ ((exponent32 x : Int) - 150) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hh := mul_le_mul hm hp (by positivity) (by positivity)
  norm_num at hh
  simpa using hh

end VerifiedSqrt.Arm
