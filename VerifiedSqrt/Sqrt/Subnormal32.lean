module

public import VerifiedSqrt.Arm.ExactScaling32
public import VerifiedSqrt.Sqrt.Normalization32

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

def scaleSubnormal32 (x : UInt32) : UInt32 := (mul32 false x 0x57800000).bits

theorem unpack32_subnormal (x : UInt32) (hi : x.toNat < 2 ^ 23) :
    unpack32 x = ⟨x.toNat, -149⟩ := by
  have hs := sign32_false_of_lt x (by omega)
  have he : exponent32 x = 0 := by rw [exponent32_eq_div]; omega
  have hf : fraction32 x = x.toNat := by rw [fraction32_eq_mod]; exact Nat.mod_eq_of_lt hi
  simp [unpack32, hs, he, hf]

theorem scaleSubnormal32_encode (x : UInt32) (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 23) :
    scaleSubnormal32 x = encode32 (x.toNat.log2 + 26)
      (normalizedCoefficient32 x.toNat - 2 ^ 23) := by
  obtain ⟨hs, hz, hn, hinf, _, _⟩ := positive_finite32_classify x lo (by omega)
  have hsn : isSNaN32 x = false := by simp [isSNaN32, hn]
  have hcNaN : isNaN32 0x57800000 = false := by decide +kernel
  have hcSNaN : isSNaN32 0x57800000 = false := by decide +kernel
  have hcZero : isZero32 0x57800000 = false := by decide +kernel
  have hcInf : isInf32 0x57800000 = false := by decide +kernel
  have hcUnpack : unpack32 0x57800000 = ⟨2 ^ 23, 25⟩ := by decide +kernel
  have hp : (unpack32 x).mul (unpack32 0x57800000) =
      ⟨(x.toNat * 2 ^ 23 : Nat), -124⟩ := by
    rw [unpack32_subnormal x hi, hcUnpack]
    simp [Dyadic.mul]
  simp only [scaleSubnormal32, mul32, processNaNs32, List.find?, hsn, hcSNaN,
    hn, hcNaN, hz, hcZero, hinf, hcInf]
  simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none,
    Bool.or_self, Bool.and_false]
  rw [hp, round32_subnormal_product x.toNat lo hi]

theorem scaleSubnormal32_properties (x : UInt32) (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 23) :
    sign32 (scaleSubnormal32 x) = false ∧
      26 ≤ exponent32 (scaleSubnormal32 x) ∧ exponent32 (scaleSubnormal32 x) ≤ 48 := by
  have hl : x.toNat.log2 ≤ 22 := by
    have h := (Nat.log2_lt (by omega : x.toNat ≠ 0)).mpr hi
    omega
  have hb := normalizedCoefficient32_bounds x.toNat lo (by omega)
  rw [scaleSubnormal32_encode x lo hi,
    encode32_sign _ _ (by omega) (by omega), encode32_exponent _ _ (by omega) (by omega)]
  exact ⟨rfl, by omega, by omega⟩

theorem scaleSubnormal32_value (x : UInt32) (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 23) :
    (unpack32 (scaleSubnormal32 x)).toReal = (unpack32 x).toReal * (2 : ℝ) ^ 48 := by
  have hl : x.toNat.log2 ≤ 22 := by
    have h := (Nat.log2_lt (by omega : x.toNat ≠ 0)).mpr hi
    omega
  have hb := normalizedCoefficient32_bounds x.toNat lo (by omega)
  have hm := normalizedCoefficient32_mul x.toNat lo (by omega)
  have hmR : (normalizedCoefficient32 x.toNat : ℝ) * (2 : ℝ) ^ x.toNat.log2 =
      (x.toNat : ℝ) * (2 : ℝ) ^ 23 := by exact_mod_cast hm
  rw [scaleSubnormal32_encode x lo hi,
    encode32_value _ _ (by omega) (by omega) (by omega),
    show 2 ^ 23 + (normalizedCoefficient32 x.toNat - 2 ^ 23) =
      normalizedCoefficient32 x.toNat by omega,
    unpack32_subnormal x hi]
  have he : ((x.toNat.log2 + 26 : Nat) : Int) - 150 = (x.toNat.log2 : Int) + -124 := by omega
  rw [he, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, ← mul_assoc, hmR]
  norm_num [Dyadic.toReal]
  ring

theorem scaleSubnormal32_root (x : UInt32) (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 23) :
    Real.sqrt (unpack32 x).toReal =
      Real.sqrt (unpack32 (scaleSubnormal32 x)).toReal * (2 : ℝ) ^ (-24 : Int) := by
  have hx : 0 ≤ (unpack32 x).toReal := by rw [unpack32_subnormal x hi]; simp [Dyadic.toReal]
  rw [scaleSubnormal32_value x lo hi, Real.sqrt_mul hx,
    show (2 : ℝ) ^ 48 = ((2 : ℝ) ^ 24) ^ 2 by norm_num,
    Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  norm_num
  ring

theorem subnormal_normalized_root (x : UInt32) (lo : 0 < x.toNat) (hi : x.toNat < 2 ^ 23) :
    Real.sqrt (unpack32 x).toReal =
      Real.sqrt (unpack32 (normalizedInput32 (scaleSubnormal32 x))).toReal *
        (2 : ℝ) ^ (rootExponent32 (scaleSubnormal32 x) - 24) := by
  have hp := scaleSubnormal32_properties x lo hi
  rw [scaleSubnormal32_root x lo hi, normalizedInput32_root _ hp.1 (by omega),
    mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rfl

end VerifiedSqrt.Sqrt
