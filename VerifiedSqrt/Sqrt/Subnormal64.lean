module

public import VerifiedSqrt.Arm.ExactScaling64
public import VerifiedSqrt.Sqrt.Normalization64

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

def scaleSubnormal64 (x : UInt64) : UInt64 := (mul64 false x 0x4690000000000000).bits

theorem unpack64_subnormal (x : UInt64) (hi : x.toNat < 2 ^ 52) :
    unpack64 x = ⟨x.toNat, -1074⟩ := by
  have hs := sign64_false_of_lt x (by omega)
  have he : exponent64 x = 0 := by rw [exponent64_eq_div]; omega
  have hf : fraction64 x = x.toNat := by rw [fraction64_eq_mod]; exact Nat.mod_eq_of_lt hi
  simp [unpack64, hs, he, hf]

theorem scaleSubnormal64_encode (x : UInt64) (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 52) :
    scaleSubnormal64 x = encode64 (x.toNat.log2 + 55)
      (normalizedCoefficient64 x.toNat - 2 ^ 52) := by
  obtain ⟨hs, hz, hn, hinf, _, _⟩ := positive_finite64_classify x lo (by omega)
  have hsn : isSNaN64 x = false := by simp [isSNaN64, hn]
  have hcNaN : isNaN64 0x4690000000000000 = false := by decide +kernel
  have hcSNaN : isSNaN64 0x4690000000000000 = false := by decide +kernel
  have hcZero : isZero64 0x4690000000000000 = false := by decide +kernel
  have hcInf : isInf64 0x4690000000000000 = false := by decide +kernel
  have hcUnpack : unpack64 0x4690000000000000 = ⟨2 ^ 52, 54⟩ := by decide +kernel
  have hp : (unpack64 x).mul (unpack64 0x4690000000000000) =
      ⟨(x.toNat * 2 ^ 52 : Nat), -1020⟩ := by
    rw [unpack64_subnormal x hi, hcUnpack]
    simp [Dyadic.mul]
  simp only [scaleSubnormal64, mul64, processNaNs64, List.find?, hsn, hcSNaN,
    hn, hcNaN, hz, hcZero, hinf, hcInf]
  simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none,
    Bool.or_self, Bool.and_false]
  rw [hp, round64_subnormal_product x.toNat lo hi]

theorem scaleSubnormal64_properties (x : UInt64) (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 52) :
    sign64 (scaleSubnormal64 x) = false ∧
      55 ≤ exponent64 (scaleSubnormal64 x) ∧ exponent64 (scaleSubnormal64 x) ≤ 106 := by
  have hl : x.toNat.log2 ≤ 51 := by
    have h := (Nat.log2_lt (by omega : x.toNat ≠ 0)).mpr hi
    omega
  have hb := normalizedCoefficient64_bounds x.toNat lo (by omega)
  rw [scaleSubnormal64_encode x lo hi,
    encode64_sign _ _ (by omega) (by omega), encode64_exponent _ _ (by omega) (by omega)]
  exact ⟨rfl, by omega, by omega⟩

theorem scaleSubnormal64_value (x : UInt64) (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 52) :
    (unpack64 (scaleSubnormal64 x)).toReal = (unpack64 x).toReal * (2 : ℝ) ^ 106 := by
  have hl : x.toNat.log2 ≤ 51 := by
    have h := (Nat.log2_lt (by omega : x.toNat ≠ 0)).mpr hi
    omega
  have hb := normalizedCoefficient64_bounds x.toNat lo (by omega)
  have hm := normalizedCoefficient64_mul x.toNat lo (by omega)
  have hmR : (normalizedCoefficient64 x.toNat : ℝ) * (2 : ℝ) ^ x.toNat.log2 =
      (x.toNat : ℝ) * (2 : ℝ) ^ 52 := by exact_mod_cast hm
  rw [scaleSubnormal64_encode x lo hi,
    encode64_value _ _ (by omega) (by omega) (by omega),
    show 2 ^ 52 + (normalizedCoefficient64 x.toNat - 2 ^ 52) =
      normalizedCoefficient64 x.toNat by omega,
    unpack64_subnormal x hi]
  have he : ((x.toNat.log2 + 55 : Nat) : Int) - 1075 = (x.toNat.log2 : Int) + -1020 := by omega
  rw [he, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, ← mul_assoc, hmR]
  simp only [Dyadic.toReal, Int.cast_natCast, mul_assoc]
  rw [← zpow_natCast, ← zpow_natCast,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rfl

theorem scaleSubnormal64_root (x : UInt64) (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 52) :
    Real.sqrt (unpack64 x).toReal =
      Real.sqrt (unpack64 (scaleSubnormal64 x)).toReal * (2 : ℝ) ^ (-53 : Int) := by
  have hx : 0 ≤ (unpack64 x).toReal := by rw [unpack64_subnormal x hi]; simp [Dyadic.toReal]
  rw [scaleSubnormal64_value x lo hi, Real.sqrt_mul hx,
    show (2 : ℝ) ^ 106 = ((2 : ℝ) ^ 53) ^ 2 by norm_num,
    Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  norm_num
  ring

theorem subnormal_normalized_root64 (x : UInt64) (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 52) :
    Real.sqrt (unpack64 x).toReal =
      Real.sqrt (unpack64 (normalizedInput64 (scaleSubnormal64 x))).toReal *
        (2 : ℝ) ^ (rootExponent64 (scaleSubnormal64 x) - 53) := by
  have hp := scaleSubnormal64_properties x lo hi
  rw [scaleSubnormal64_root x lo hi, normalizedInput64_root _ hp.1 (by omega),
    mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rfl

end VerifiedSqrt.Sqrt
