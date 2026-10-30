module

public import VerifiedSqrt.Arm.Encoding64
public import VerifiedSqrt.Sqrt.Correction64

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

def rootExponent64 (x : UInt64) : Int := ((exponent64 x : Int) - 1023) / 2

def normalizedInput64 (x : UInt64) : UInt64 :=
  UInt64.ofNat (fraction64 x +
    (1023 + (((exponent64 x : Int) - 1023) % 2).toNat) * 2 ^ 52)

def rescale64 (q : UInt64) (k : Int) : UInt64 :=
  UInt64.ofNat ((q.toNat : Int) + k * 2 ^ 52).toNat

theorem normalizedInput64_encode (x : UInt64) :
    normalizedInput64 x =
      encode64 (1023 + (((exponent64 x : Int) - 1023) % 2).toNat) (fraction64 x) := by
  unfold normalizedInput64 encode64
  exact congrArg UInt64.ofNat (Nat.add_comm _ _)

theorem normalizedInput64_bounds (x : UInt64) :
    0x3ff0000000000000 ≤ (normalizedInput64 x).toNat ∧
      (normalizedInput64 x).toNat < 0x4010000000000000 := by
  have hf := fraction64_lt x
  have hp : (((exponent64 x : Int) - 1023) % 2).toNat ≤ 1 := by omega
  rw [normalizedInput64_encode, encode64_bits _ _ (by omega) hf]
  omega

theorem rootExponent64_bounds (x : UInt64) (lo : 0 < exponent64 x)
    (hi : exponent64 x < 2047) : -511 ≤ rootExponent64 x ∧ rootExponent64 x ≤ 511 := by
  dsimp [rootExponent64]
  omega

theorem normalizedInput64_value (x : UInt64) (hs : sign64 x = false)
    (he : 0 < exponent64 x) :
    (unpack64 x).toReal = (unpack64 (normalizedInput64 x)).toReal *
      (2 : ℝ) ^ (2 * rootExponent64 x) := by
  have hf := fraction64_lt x
  have hp : (((exponent64 x : Int) - 1023) % 2).toNat ≤ 1 := by omega
  rw [unpack64_positive_normal x hs he, normalizedInput64_encode,
    encode64_value _ _ (by omega) (by omega) hf, mul_assoc,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hx : (exponent64 x : Int) - 1075 =
      ((1023 + (((exponent64 x : Int) - 1023) % 2).toNat : Nat) : Int) - 1075 +
        2 * rootExponent64 x := by
    dsimp [rootExponent64]
    omega
  rw [hx]

theorem normalizedInput64_root (x : UInt64) (hs : sign64 x = false)
    (he : 0 < exponent64 x) :
    Real.sqrt (unpack64 x).toReal =
      Real.sqrt (unpack64 (normalizedInput64 x)).toReal * (2 : ℝ) ^ rootExponent64 x := by
  have hb := normalizedInput64_bounds x
  have hz : 0 ≤ (unpack64 (normalizedInput64 x)).toReal := by
    rw [normalized64_value _ hb.1 hb.2]
    positivity
  rw [normalizedInput64_value x hs he, Real.sqrt_mul hz]
  have hp : (2 : ℝ) ^ (2 * rootExponent64 x) = ((2 : ℝ) ^ rootExponent64 x) ^ 2 := by
    rw [show 2 * rootExponent64 x = rootExponent64 x + rootExponent64 x by omega,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), pow_two]
  rw [hp, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

theorem normalizedSignificand64_bounds (q : UInt64) :
    2 ^ 52 ≤ normalizedSignificand64 q ∧ normalizedSignificand64 q ≤ 2 ^ 53 := by
  have hf := fraction64_lt q
  simp only [normalizedSignificand64]
  split <;> omega

theorem normalized64_bits (q : UInt64)
    (lo : 0x3ff0000000000000 ≤ q.toNat) (hi : q.toNat ≤ 0x4000000000000000) :
    q.toNat = 1022 * 2 ^ 52 + normalizedSignificand64 q := by
  by_cases hq : q = 0x4000000000000000
  · subst q
    decide +kernel
  · have hn : q.toNat ≠ 0x4000000000000000 := by
      intro h
      exact hq (UInt64.toNat_inj.mp h)
    simp only [normalizedSignificand64, beq_iff_eq, ite_eq_right hq, fraction64_eq_mod]
    omega

theorem rescale64_encode (q : UInt64) (k : Int)
    (qlo : 0x3ff0000000000000 ≤ q.toNat) (qhi : q.toNat ≤ 0x4000000000000000)
    (klo : -1021 ≤ k) (khi : k ≤ 1022) :
    rescale64 q k = encodeSignificand64 (k + 1023).toNat (normalizedSignificand64 q) := by
  have hb := normalized64_bits q qlo qhi
  unfold rescale64 encodeSignificand64
  exact congrArg UInt64.ofNat (by omega)

theorem rescale64_value (q : UInt64) (k : Int)
    (qlo : 0x3ff0000000000000 ≤ q.toNat) (qhi : q.toNat ≤ 0x4000000000000000)
    (klo : -1021 ≤ k) (khi : k ≤ 1022) :
    (unpack64 (rescale64 q k)).toReal =
      (normalizedSignificand64 q : ℝ) * (2 : ℝ) ^ (k - 52) := by
  have hb := normalizedSignificand64_bounds q
  rw [rescale64_encode q k qlo qhi klo khi,
    encodeSignificand64_value _ _ (by omega) (by omega) hb.1 hb.2]
  have he : ((k + 1023).toNat : Int) - 1075 = k - 52 := by omega
  rw [he]

theorem rescale64_bounds (q : UInt64) (k : Int)
    (qlo : 0x3ff0000000000000 ≤ q.toNat) (qhi : q.toNat ≤ 0x4000000000000000)
    (klo : -1021 ≤ k) (khi : k ≤ 1022) :
    0 < (rescale64 q k).toNat ∧ (rescale64 q k).toNat < 0x7ff0000000000000 := by
  have hb := normalizedSignificand64_bounds q
  rw [rescale64_encode q k qlo qhi klo khi,
    encodeSignificand64_bits _ _ (by omega) hb.2]
  omega

end VerifiedSqrt.Sqrt
