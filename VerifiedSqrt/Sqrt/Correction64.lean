module

public import VerifiedSqrt.Sqrt.Encoding64
public import VerifiedSqrt.Sqrt.IntegerCertificate

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

theorem normalized64_radicand_bounds (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) :
    2 ^ 104 ≤ normalizedRadicand64 x ∧ normalizedRadicand64 x < 2 ^ 106 := by
  have hf := fraction64_lt x
  rcases normalized64_exponent x lo hi with he | he <;>
    simp only [normalizedRadicand64, he] <;> norm_num at * <;> omega

theorem roundedIntegerRoot64_bounds (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) :
    2 ^ 52 ≤ roundedIntegerRoot (normalizedRadicand64 x) ∧
      roundedIntegerRoot (normalizedRadicand64 x) ≤ 2 ^ 53 := by
  have hb := normalized64_radicand_bounds x lo hi
  have hlo : 2 ^ 52 ≤ (normalizedRadicand64 x).sqrt :=
    Nat.le_sqrt.mpr (by norm_num at *; exact hb.1)
  have hhi : (normalizedRadicand64 x).sqrt < 2 ^ 53 :=
    Nat.sqrt_lt.mpr (by norm_num at *; exact hb.2)
  simp only [roundedIntegerRoot]
  split <;> omega

theorem correctedSignificand64_eq (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) :
    correctedSignificand64 x = roundedIntegerRoot (normalizedRadicand64 x) := by
  have hb := normalized64_radicand_bounds x lo hi
  have hr := roundedIntegerRoot64_bounds x lo hi
  have hq := fraction64_lt (estimateCore64 x)
  apply correctIntegerRoot_eq (roundedIntegerRoot_certificate _ (by omega))
  omega

theorem normalizedSignificand64_encode (q : Nat) (lo : 2 ^ 52 ≤ q) (hi : q ≤ 2 ^ 53) :
    normalizedSignificand64 (UInt64.ofNat (0x3fe0000000000000 + q)) = q := by
  have hn : 0x3fe0000000000000 + q < 2 ^ 64 := by omega
  by_cases hq : q = 2 ^ 53
  · subst q
    decide
  · have he : UInt64.ofNat (0x3fe0000000000000 + q) ≠ 0x4000000000000000 := by
      intro he
      have hb := congrArg UInt64.toNat he
      simp only [UInt64.toNat_ofNat] at hb
      change (0x3fe0000000000000 + q) % 2 ^ 64 = 0x4000000000000000 at hb
      rw [Nat.mod_eq_of_lt hn] at hb
      omega
    simp only [normalizedSignificand64, beq_iff_eq, ite_eq_right he, fraction64_eq_mod]
    change 2 ^ 52 + ((0x3fe0000000000000 + q) % 2 ^ 64) % 2 ^ 52 = q
    rw [Nat.mod_eq_of_lt hn]
    norm_num at *
    omega

theorem correctedCore64_bounds (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) :
    0x3ff0000000000000 ≤ (core64 x).toNat ∧
      (core64 x).toNat ≤ 0x4000000000000000 := by
  have hb := roundedIntegerRoot64_bounds x lo hi
  simp only [core64, correctedSignificand64_eq x lo hi]
  change 0x3ff0000000000000 ≤ (0x3fe0000000000000 + _) % 2 ^ 64 ∧ _
  norm_num at *
  omega

theorem correctedCore64_certificate (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) :
    IntegerRootCertificate (normalizedRadicand64 x)
      (normalizedSignificand64 (core64 x)) := by
  have hb := normalized64_radicand_bounds x lo hi
  have hr := roundedIntegerRoot64_bounds x lo hi
  rw [core64, correctedSignificand64_eq x lo hi,
    normalizedSignificand64_encode _ hr.1 hr.2]
  exact roundedIntegerRoot_certificate _ (by omega)

theorem core64_certificate (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) :
    coreCertificate64 x = true := by
  have hb := correctedCore64_bounds x lo hi
  have hc := correctedCore64_certificate x lo hi
  simp only [coreCertificate64, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hb.1, hb.2⟩, hc.2.1⟩, hc.2.2⟩

theorem coreCorrect64 : CoreCorrect64 := by
  intro i
  let x := UInt64.ofNat (0x3ff0000000000000 + i.val)
  have hn : x.toNat = 0x3ff0000000000000 + i.val := by
    apply Nat.mod_eq_of_lt
    have hi := i.isLt
    omega
  exact core64_certificate x (by omega) (by have hi := i.isLt; omega)

theorem normalizedCore64_correct (x : UInt64)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000) (y : UInt64)
    (hne : (unpack64 (core64 x)).toReal ≠ (unpack64 y).toReal) :
    |(unpack64 (core64 x)).toReal - Real.sqrt (unpack64 x).toReal| <
      |(unpack64 y).toReal - Real.sqrt (unpack64 x).toReal| :=
  certificate64_result_unique_float x lo hi (core64_certificate x lo hi) y hne

end VerifiedSqrt.Sqrt
