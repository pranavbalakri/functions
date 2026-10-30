module

public import VerifiedSqrt.Arm.Encoding32
public import VerifiedSqrt.Sqrt.Correction32

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

def rootExponent32 (x : UInt32) : Int := ((exponent32 x : Int) - 127) / 2

def normalizedInput32 (x : UInt32) : UInt32 :=
  UInt32.ofNat (fraction32 x +
    (127 + (((exponent32 x : Int) - 127) % 2).toNat) * 2 ^ 23)

def rescale32 (q : UInt32) (k : Int) : UInt32 :=
  UInt32.ofNat ((q.toNat : Int) + k * 2 ^ 23).toNat

theorem normalizedInput32_encode (x : UInt32) :
    normalizedInput32 x =
      encode32 (127 + (((exponent32 x : Int) - 127) % 2).toNat) (fraction32 x) := by
  unfold normalizedInput32 encode32
  exact congrArg UInt32.ofNat (Nat.add_comm _ _)

theorem normalizedInput32_bounds (x : UInt32) :
    0x3f800000 ≤ (normalizedInput32 x).toNat ∧
      (normalizedInput32 x).toNat < 0x40800000 := by
  have hf := fraction32_lt x
  have hp : (((exponent32 x : Int) - 127) % 2).toNat ≤ 1 := by omega
  rw [normalizedInput32_encode, encode32_bits _ _ (by omega) hf]
  omega

theorem rootExponent32_bounds (x : UInt32) (lo : 0 < exponent32 x)
    (hi : exponent32 x < 255) : -63 ≤ rootExponent32 x ∧ rootExponent32 x ≤ 63 := by
  dsimp [rootExponent32]
  omega

theorem normalizedInput32_value (x : UInt32) (hs : sign32 x = false)
    (he : 0 < exponent32 x) :
    (unpack32 x).toReal = (unpack32 (normalizedInput32 x)).toReal *
      (2 : ℝ) ^ (2 * rootExponent32 x) := by
  have hf := fraction32_lt x
  have hp : (((exponent32 x : Int) - 127) % 2).toNat ≤ 1 := by omega
  rw [unpack32_positive_normal x hs he, normalizedInput32_encode,
    encode32_value _ _ (by omega) (by omega) hf, mul_assoc,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hx : (exponent32 x : Int) - 150 =
      ((127 + (((exponent32 x : Int) - 127) % 2).toNat : Nat) : Int) - 150 +
        2 * rootExponent32 x := by
    dsimp [rootExponent32]
    omega
  rw [hx]

theorem normalizedInput32_root (x : UInt32) (hs : sign32 x = false)
    (he : 0 < exponent32 x) :
    Real.sqrt (unpack32 x).toReal =
      Real.sqrt (unpack32 (normalizedInput32 x)).toReal * (2 : ℝ) ^ rootExponent32 x := by
  have hb := normalizedInput32_bounds x
  have hz : 0 ≤ (unpack32 (normalizedInput32 x)).toReal := by
    rw [normalized32_value _ hb.1 hb.2]
    positivity
  rw [normalizedInput32_value x hs he, Real.sqrt_mul hz]
  have hp : (2 : ℝ) ^ (2 * rootExponent32 x) = ((2 : ℝ) ^ rootExponent32 x) ^ 2 := by
    rw [show 2 * rootExponent32 x = rootExponent32 x + rootExponent32 x by omega,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), pow_two]
  rw [hp, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

theorem normalizedSignificand32_bounds (q : UInt32) :
    2 ^ 23 ≤ normalizedSignificand32 q ∧ normalizedSignificand32 q ≤ 2 ^ 24 := by
  have hf := fraction32_lt q
  simp only [normalizedSignificand32]
  split <;> omega

theorem normalized32_bits (q : UInt32)
    (lo : 0x3f800000 ≤ q.toNat) (hi : q.toNat ≤ 0x40000000) :
    q.toNat = 126 * 2 ^ 23 + normalizedSignificand32 q := by
  by_cases hq : q = 0x40000000
  · subst q
    decide +kernel
  · have hn : q.toNat ≠ 0x40000000 := by
      intro h
      exact hq (UInt32.toNat_inj.mp h)
    simp only [normalizedSignificand32, beq_iff_eq, ite_eq_right hq, fraction32_eq_mod]
    omega

theorem rescale32_encode (q : UInt32) (k : Int)
    (qlo : 0x3f800000 ≤ q.toNat) (qhi : q.toNat ≤ 0x40000000)
    (klo : -125 ≤ k) (khi : k ≤ 126) :
    rescale32 q k = encodeSignificand32 (k + 127).toNat (normalizedSignificand32 q) := by
  have hb := normalized32_bits q qlo qhi
  unfold rescale32 encodeSignificand32
  exact congrArg UInt32.ofNat (by omega)

theorem rescale32_value (q : UInt32) (k : Int)
    (qlo : 0x3f800000 ≤ q.toNat) (qhi : q.toNat ≤ 0x40000000)
    (klo : -125 ≤ k) (khi : k ≤ 126) :
    (unpack32 (rescale32 q k)).toReal =
      (normalizedSignificand32 q : ℝ) * (2 : ℝ) ^ (k - 23) := by
  have hb := normalizedSignificand32_bounds q
  rw [rescale32_encode q k qlo qhi klo khi,
    encodeSignificand32_value _ _ (by omega) (by omega) hb.1 hb.2]
  have he : ((k + 127).toNat : Int) - 150 = k - 23 := by omega
  rw [he]

end VerifiedSqrt.Sqrt
