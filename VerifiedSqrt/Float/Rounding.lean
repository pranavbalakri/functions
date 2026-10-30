module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import VerifiedSqrt.Float.Dyadic

@[expose] public section

namespace VerifiedSqrt

def NearestEvenInteger (x : ℝ) (q : ℤ) : Prop :=
  (∀ z : ℤ, |(q : ℝ) - x| ≤ |(z : ℝ) - x|) ∧
    (|(q : ℝ) - x| = 1 / 2 → q % 2 = 0)

theorem nearestInteger_of_half (x : ℝ) (q : ℤ)
    (h : |(q : ℝ) - x| ≤ 1 / 2) :
    ∀ z : ℤ, |(q : ℝ) - x| ≤ |(z : ℝ) - x| := by
  intro z
  rcases lt_trichotomy z q with hz | rfl | hz
  · have hstep : (z : ℝ) + 1 ≤ q := by exact_mod_cast hz
    have hbounds := abs_le.mp h
    rw [abs_of_nonpos (show (z : ℝ) - x ≤ 0 by linarith)]
    exact (abs_le.mpr ⟨by linarith, by linarith⟩)
  · exact le_rfl
  · have hstep : (q : ℝ) + 1 ≤ z := by exact_mod_cast hz
    have hbounds := abs_le.mp h
    rw [abs_of_nonneg (show 0 ≤ (z : ℝ) - x by linarith)]
    exact (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem nearestEvenInteger_half {x : ℝ} {q : ℤ} (h : NearestEvenInteger x q) :
    |(q : ℝ) - x| ≤ 1 / 2 := by
  have hlo := h.1 (q - 1)
  have hhi := h.1 (q + 1)
  push_cast at hlo hhi
  have hlo2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hlo
  have hhi2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hhi
  simp only [sq_abs] at hlo2 hhi2
  apply abs_le.mpr
  constructor <;> nlinarith

theorem nearestEvenInteger_unique {x : ℝ} {q r : ℤ}
    (hq : NearestEvenInteger x q) (hr : NearestEvenInteger x r) : q = r := by
  have hqb := abs_le.mp (nearestEvenInteger_half hq)
  have hrb := abs_le.mp (nearestEvenInteger_half hr)
  have hdist : q - 1 ≤ r ∧ r ≤ q + 1 := by
    exact_mod_cast (show (q : ℝ) - 1 ≤ r ∧ (r : ℝ) ≤ q + 1 by
      constructor <;> linarith)
  rcases lt_trichotomy q r with h | h | h
  · have he : r = q + 1 := by omega
    have heR : (r : ℝ) = q + 1 := by exact_mod_cast he
    have hqt := hq.2 (by rw [abs_of_nonpos (by linarith : (q : ℝ) - x ≤ 0)]; linarith)
    have hrt := hr.2 (by rw [abs_of_nonneg (by linarith : 0 ≤ (r : ℝ) - x)]; linarith)
    omega
  · exact h
  · have he : q = r + 1 := by omega
    have heR : (q : ℝ) = r + 1 := by exact_mod_cast he
    have hqt := hq.2 (by rw [abs_of_nonneg (by linarith : 0 ≤ (q : ℝ) - x)]; linarith)
    have hrt := hr.2 (by rw [abs_of_nonpos (by linarith : (r : ℝ) - x ≤ 0)]; linarith)
    omega

theorem nearestEvenInteger_neg {x : ℝ} {q : ℤ} (h : NearestEvenInteger x q) :
    NearestEvenInteger (-x) (-q) := by
  have hn (a b : ℝ) : |-a - -b| = |a - b| := by
    rw [neg_sub_neg, abs_sub_comm]
  constructor
  · intro z
    calc
      |((-q : ℤ) : ℝ) - -x| = |(q : ℝ) - x| := by rw [Int.cast_neg, hn]
      _ ≤ |((-z : ℤ) : ℝ) - x| := h.1 (-z)
      _ = |(z : ℝ) - -x| := by
        rw [Int.cast_neg, show -(z : ℝ) - x = -((z : ℝ) - -x) by ring, abs_neg]
  · intro ht
    have hq : q % 2 = 0 := h.2 (by simpa only [Int.cast_neg, hn] using ht)
    omega

theorem nearestEvenInteger_self (q : ℤ) : NearestEvenInteger (q : ℝ) q := by
  constructor
  · intro z
    simp
  · simp

theorem nearestEvenInteger_of_lt {x : ℝ} {q : ℤ}
    (h : |(q : ℝ) - x| < 1 / 2) : NearestEvenInteger x q := by
  exact ⟨nearestInteger_of_half x q (le_of_lt h), fun ht => by linarith⟩

theorem nearestInteger_strict_of_lt {x : ℝ} {q z : ℤ}
    (h : |(q : ℝ) - x| < 1 / 2) (hne : q ≠ z) :
    |(q : ℝ) - x| < |(z : ℝ) - x| := by
  have hb := abs_lt.mp h
  rcases lt_or_gt_of_ne hne with hz | hz
  · have hstep : (q : ℝ) + 1 ≤ z := by exact_mod_cast hz
    rw [abs_of_nonneg (by linarith : 0 ≤ (z : ℝ) - x)]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · have hstep : (z : ℝ) + 1 ≤ q := by exact_mod_cast hz
    rw [abs_of_nonpos (by linarith : (z : ℝ) - x ≤ 0)]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem roundShiftEven_bounds (n k : Nat) :
    let q := (roundShiftEven n k).1
    let d := 2 ^ k
    2 * n ≤ (2 * q + 1) * d ∧
    2 * q * d ≤ 2 * n + d ∧
    (2 * n = (2 * q + 1) * d ∨ 2 * q * d = 2 * n + d → q % 2 = 0) := by
  dsimp
  by_cases hk : k = 0
  · subst k
    simp [roundShiftEven]
  · have hd : 0 < 2 ^ k := by positivity
    have hr := Nat.mod_lt n hd
    have hr0 := Nat.zero_le (n % 2 ^ k)
    have he := Nat.div_add_mod n (2 ^ k)
    have hp := Nat.mod_two_eq_zero_or_one (n / 2 ^ k)
    simp only [roundShiftEven, ite_eq_right hk, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true, beq_iff_eq]
    split
    · rename_i h
      constructor
      · nlinarith
      constructor
      · rcases h with h | h <;> nlinarith
      · intro ht
        have heq : 2 * (n % 2 ^ k) = 2 ^ k := by rcases ht with ht | ht <;> nlinarith
        have hodd : n / 2 ^ k % 2 = 1 := by omega
        omega
    · rename_i h
      simp only [Nat.add_zero]
      constructor
      · have hle : 2 * (n % 2 ^ k) ≤ 2 ^ k := by omega
        nlinarith
      constructor
      · nlinarith
      · intro ht
        have heq : 2 * (n % 2 ^ k) = 2 ^ k := by rcases ht with ht | ht <;> nlinarith
        omega

theorem roundShiftEven_nearest (n k : Nat) :
    NearestEvenInteger ((n : ℝ) / (2 : ℝ) ^ k) (roundShiftEven n k).1 := by
  let q := (roundShiftEven n k).1
  let d := 2 ^ k
  have hd : (0 : ℝ) < d := by dsimp [d]; positivity
  have hb := roundShiftEven_bounds n k
  change 2 * n ≤ (2 * q + 1) * d ∧ 2 * q * d ≤ 2 * n + d ∧ _ at hb
  have hlo : (2 * q : ℝ) * d ≤ 2 * n + d := by exact_mod_cast hb.2.1
  have hhi : (2 * n : ℝ) ≤ (2 * q + 1) * d := by exact_mod_cast hb.1
  have hdq : (n : ℝ) / d * d = n := div_mul_cancel₀ _ (ne_of_gt hd)
  have herr : |(q : ℝ) - (n : ℝ) / d| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  change NearestEvenInteger ((n : ℝ) / (2 : ℝ) ^ k) (q : ℤ)
  rw [show (2 : ℝ) ^ k = (d : ℝ) by simp [d]]
  constructor
  · exact nearestInteger_of_half _ _ (by simpa using herr)
  · intro ht
    have ht' : |(q : ℝ) - (n : ℝ) / d| = 1 / 2 := by simpa using ht
    have heq : 2 * n = (2 * q + 1) * d ∨ 2 * q * d = 2 * n + d := by
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp ht' with h | h
      · right
        have : (2 * q : ℝ) * d = 2 * n + d := by nlinarith
        exact_mod_cast this
      · left
        have : (2 * n : ℝ) = (2 * q + 1) * d := by nlinarith
        exact_mod_cast this
    exact_mod_cast hb.2.2 heq

theorem roundShiftEven_inexact (n k : Nat) :
    (roundShiftEven n k).2 = (n % 2 ^ k != 0) := by
  by_cases hk : k = 0
  · subst k
    simp [roundShiftEven, Nat.mod_one]
  · simp [roundShiftEven, hk]

end VerifiedSqrt
