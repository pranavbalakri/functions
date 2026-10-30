module

public import VerifiedSqrt.Arm.Scalar64Real
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace VerifiedSqrt.Arm

def encode64 (e f : Nat) : UInt64 := UInt64.ofNat (e * 2 ^ 52 + f)

theorem encode64_bits (e f : Nat) (he : e < 2048) (hf : f < 2 ^ 52) :
    (encode64 e f).toNat = e * 2 ^ 52 + f := by
  rw [encode64, UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  omega

theorem encode64_fraction (e f : Nat) (he : e < 2048) (hf : f < 2 ^ 52) :
    fraction64 (encode64 e f) = f := by
  rw [fraction64_eq_mod, encode64_bits e f he hf]
  omega

theorem encode64_exponent (e f : Nat) (he : e < 2048) (hf : f < 2 ^ 52) :
    exponent64 (encode64 e f) = e := by
  rw [exponent64_eq_div, encode64_bits e f he hf]
  omega

theorem encode64_sign (e f : Nat) (he : e < 2048) (hf : f < 2 ^ 52) :
    sign64 (encode64 e f) = false := by
  apply sign64_false_of_lt
  rw [encode64_bits e f he hf]
  omega

theorem encode64_value (e f : Nat) (lo : 0 < e) (hi : e < 2048) (hf : f < 2 ^ 52) :
    (unpack64 (encode64 e f)).toReal =
      ((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ ((e : Int) - 1075) := by
  rw [unpack64_positive_normal _ (encode64_sign e f hi hf)
    (by rw [encode64_exponent e f hi hf]; exact lo),
    encode64_exponent e f hi hf, encode64_fraction e f hi hf]

theorem positive64_bits (x : UInt64) (h : x.toNat < 2 ^ 63) :
    x.toNat = exponent64 x * 2 ^ 52 + fraction64 x := by
  rw [exponent64_eq_div, fraction64_eq_mod]
  omega

def encodeSignificand64 (e q : Nat) : UInt64 := UInt64.ofNat ((e - 1) * 2 ^ 52 + q)

theorem encodeSignificand64_bits (e q : Nat) (he : e ≤ 2045) (hq : q ≤ 2 ^ 53) :
    (encodeSignificand64 e q).toNat = (e - 1) * 2 ^ 52 + q := by
  rw [encodeSignificand64, UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  omega

theorem encodeSignificand64_value (e q : Nat) (elo : 0 < e) (ehi : e ≤ 2045)
    (qlo : 2 ^ 52 ≤ q) (qhi : q ≤ 2 ^ 53) :
    (unpack64 (encodeSignificand64 e q)).toReal =
      (q : ℝ) * (2 : ℝ) ^ ((e : Int) - 1075) := by
  by_cases hq : q = 2 ^ 53
  · subst q
    have he : encodeSignificand64 e (2 ^ 53) = encode64 (e + 1) 0 := by
      unfold encodeSignificand64 encode64
      exact congrArg UInt64.ofNat (by omega)
    rw [he, encode64_value _ _ (by omega) (by omega) (by decide)]
    have hp : ((e + 1 : Nat) : Int) - 1075 = (e : Int) - 1075 + 1 := by omega
    rw [hp, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  · have he : encodeSignificand64 e q = encode64 e (q - 2 ^ 52) := by
      unfold encodeSignificand64 encode64
      exact congrArg UInt64.ofNat (by omega)
    rw [he, encode64_value _ _ elo (by omega) (by omega)]
    rw [show 2 ^ 52 + (q - 2 ^ 52) = q by omega]

theorem encodeSignificand64_finite (e q : Nat) (elo : 0 < e) (ehi : e ≤ 2045)
    (qlo : 2 ^ 52 ≤ q) (qhi : q ≤ 2 ^ 53) :
    sign64 (encodeSignificand64 e q) = false ∧
      exponent64 (encodeSignificand64 e q) < 2047 := by
  have hb := encodeSignificand64_bits e q ehi qhi
  constructor
  · apply sign64_false_of_lt
    omega
  · rw [exponent64_eq_div, hb]
    omega

end VerifiedSqrt.Arm
