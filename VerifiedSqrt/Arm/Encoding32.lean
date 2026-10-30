module

public import VerifiedSqrt.Arm.Scalar32Real
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace VerifiedSqrt.Arm

def encode32 (e f : Nat) : UInt32 := UInt32.ofNat (e * 2 ^ 23 + f)

theorem encode32_bits (e f : Nat) (he : e < 256) (hf : f < 2 ^ 23) :
    (encode32 e f).toNat = e * 2 ^ 23 + f := by
  rw [encode32, UInt32.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  omega

theorem encode32_fraction (e f : Nat) (he : e < 256) (hf : f < 2 ^ 23) :
    fraction32 (encode32 e f) = f := by
  rw [fraction32_eq_mod, encode32_bits e f he hf]
  omega

theorem encode32_exponent (e f : Nat) (he : e < 256) (hf : f < 2 ^ 23) :
    exponent32 (encode32 e f) = e := by
  rw [exponent32_eq_div, encode32_bits e f he hf]
  omega

theorem encode32_sign (e f : Nat) (he : e < 256) (hf : f < 2 ^ 23) :
    sign32 (encode32 e f) = false := by
  apply sign32_false_of_lt
  rw [encode32_bits e f he hf]
  omega

theorem encode32_value (e f : Nat) (lo : 0 < e) (hi : e < 256) (hf : f < 2 ^ 23) :
    (unpack32 (encode32 e f)).toReal =
      ((2 ^ 23 + f : Nat) : ℝ) * (2 : ℝ) ^ ((e : Int) - 150) := by
  rw [unpack32_positive_normal _ (encode32_sign e f hi hf)
    (by rw [encode32_exponent e f hi hf]; exact lo),
    encode32_exponent e f hi hf, encode32_fraction e f hi hf]

theorem positive32_bits (x : UInt32) (h : x.toNat < 2 ^ 31) :
    x.toNat = exponent32 x * 2 ^ 23 + fraction32 x := by
  rw [exponent32_eq_div, fraction32_eq_mod]
  omega

def encodeSignificand32 (e q : Nat) : UInt32 := UInt32.ofNat ((e - 1) * 2 ^ 23 + q)

theorem encodeSignificand32_bits (e q : Nat) (he : e ≤ 253) (hq : q ≤ 2 ^ 24) :
    (encodeSignificand32 e q).toNat = (e - 1) * 2 ^ 23 + q := by
  rw [encodeSignificand32, UInt32.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  omega

theorem encodeSignificand32_value (e q : Nat) (elo : 0 < e) (ehi : e ≤ 253)
    (qlo : 2 ^ 23 ≤ q) (qhi : q ≤ 2 ^ 24) :
    (unpack32 (encodeSignificand32 e q)).toReal =
      (q : ℝ) * (2 : ℝ) ^ ((e : Int) - 150) := by
  by_cases hq : q = 2 ^ 24
  · subst q
    have he : encodeSignificand32 e (2 ^ 24) = encode32 (e + 1) 0 := by
      unfold encodeSignificand32 encode32
      exact congrArg UInt32.ofNat (by omega)
    rw [he, encode32_value _ _ (by omega) (by omega) (by decide)]
    have hp : ((e + 1 : Nat) : Int) - 150 = (e : Int) - 150 + 1 := by omega
    rw [hp, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  · have he : encodeSignificand32 e q = encode32 e (q - 2 ^ 23) := by
      unfold encodeSignificand32 encode32
      exact congrArg UInt32.ofNat (by omega)
    rw [he, encode32_value _ _ elo (by omega) (by omega)]
    rw [show 2 ^ 23 + (q - 2 ^ 23) = q by omega]

theorem encodeSignificand32_finite (e q : Nat) (elo : 0 < e) (ehi : e ≤ 253)
    (qlo : 2 ^ 23 ≤ q) (qhi : q ≤ 2 ^ 24) :
    sign32 (encodeSignificand32 e q) = false ∧
      exponent32 (encodeSignificand32 e q) < 255 := by
  have hb := encodeSignificand32_bits e q ehi qhi
  constructor
  · apply sign32_false_of_lt
    omega
  · rw [exponent32_eq_div, hb]
    omega

end VerifiedSqrt.Arm
