module

public import VerifiedSqrt.Sqrt.Encoding32
public import VerifiedSqrt.Sqrt.IntegerCertificate

@[expose] public section

namespace VerifiedSqrt.Sqrt

open Arm

theorem normalized32_radicand_bounds (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) :
    2 ^ 46 ≤ normalizedRadicand32 x ∧ normalizedRadicand32 x < 2 ^ 48 := by
  have hf := fraction32_lt x
  rcases normalized32_exponent x lo hi with he | he <;>
    simp only [normalizedRadicand32, he] <;> norm_num at * <;> omega

theorem roundedIntegerRoot32_bounds (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) :
    2 ^ 23 ≤ roundedIntegerRoot (normalizedRadicand32 x) ∧
      roundedIntegerRoot (normalizedRadicand32 x) ≤ 2 ^ 24 := by
  have hb := normalized32_radicand_bounds x lo hi
  have hlo : 2 ^ 23 ≤ (normalizedRadicand32 x).sqrt :=
    Nat.le_sqrt.mpr (by norm_num at *; exact hb.1)
  have hhi : (normalizedRadicand32 x).sqrt < 2 ^ 24 :=
    Nat.sqrt_lt.mpr (by norm_num at *; exact hb.2)
  simp only [roundedIntegerRoot]
  split <;> omega

theorem correctedSignificand32_eq (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) :
    correctedSignificand32 x = roundedIntegerRoot (normalizedRadicand32 x) := by
  have hb := normalized32_radicand_bounds x lo hi
  have hr := roundedIntegerRoot32_bounds x lo hi
  have hq := fraction32_lt (estimateCore32 x)
  apply correctIntegerRoot_eq (roundedIntegerRoot_certificate _ (by omega))
  omega

theorem normalizedSignificand32_encode (q : Nat) (lo : 2 ^ 23 ≤ q) (hi : q ≤ 2 ^ 24) :
    normalizedSignificand32 (UInt32.ofNat (0x3f000000 + q)) = q := by
  have hn : 0x3f000000 + q < 2 ^ 32 := by omega
  by_cases hq : q = 2 ^ 24
  · subst q
    decide
  · have he : UInt32.ofNat (0x3f000000 + q) ≠ 0x40000000 := by
      intro he
      have hb := congrArg UInt32.toNat he
      simp only [UInt32.toNat_ofNat] at hb
      change (0x3f000000 + q) % 2 ^ 32 = 0x40000000 at hb
      rw [Nat.mod_eq_of_lt hn] at hb
      omega
    simp only [normalizedSignificand32, beq_iff_eq, ite_eq_right he, fraction32_eq_mod]
    change 2 ^ 23 + ((0x3f000000 + q) % 2 ^ 32) % 2 ^ 23 = q
    rw [Nat.mod_eq_of_lt hn]
    norm_num at *
    omega

theorem correctedCore32_bounds (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) :
    0x3f800000 ≤ (core32 x).toNat ∧
      (core32 x).toNat ≤ 0x40000000 := by
  have hb := roundedIntegerRoot32_bounds x lo hi
  simp only [core32, correctedSignificand32_eq x lo hi]
  change 0x3f800000 ≤ (0x3f000000 + _) % 2 ^ 32 ∧ _
  norm_num at *
  omega

theorem correctedCore32_certificate (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) :
    IntegerRootCertificate (normalizedRadicand32 x)
      (normalizedSignificand32 (core32 x)) := by
  have hb := normalized32_radicand_bounds x lo hi
  have hr := roundedIntegerRoot32_bounds x lo hi
  rw [core32, correctedSignificand32_eq x lo hi,
    normalizedSignificand32_encode _ hr.1 hr.2]
  exact roundedIntegerRoot_certificate _ (by omega)

theorem core32_certificate (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) :
    coreCertificate32 x = true := by
  have hb := correctedCore32_bounds x lo hi
  have hc := correctedCore32_certificate x lo hi
  simp only [coreCertificate32, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hb.1, hb.2⟩, hc.2.1⟩, hc.2.2⟩

theorem coreCorrect32 : CoreCorrect32 := by
  intro i
  let x := UInt32.ofNat (0x3f800000 + i.val)
  have hn : x.toNat = 0x3f800000 + i.val := by
    apply Nat.mod_eq_of_lt
    have hi := i.isLt
    omega
  exact core32_certificate x (by omega) (by have hi := i.isLt; omega)

theorem normalizedCore32_correct (x : UInt32)
    (lo : 0x3f800000 ≤ x.toNat) (hi : x.toNat < 0x40800000) (y : UInt32)
    (hne : (unpack32 (core32 x)).toReal ≠ (unpack32 y).toReal) :
    |(unpack32 (core32 x)).toReal - Real.sqrt (unpack32 x).toReal| <
      |(unpack32 y).toReal - Real.sqrt (unpack32 x).toReal| :=
  certificate32_result_unique_float x lo hi (core32_certificate x lo hi) y hne

end VerifiedSqrt.Sqrt
