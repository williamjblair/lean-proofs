import Research.CharacteristicTaylor
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable def fourthPhase (k : ℕ) (s t : ℝ) : Option (Fin (k + 1)) → ℝ
  | none => t * fourthWhitenedNewY k
  | some q => s * fourthWhitenedX k q + t * fourthWhitenedY k q

lemma fourthPhase_abs_le_one (k : ℕ) (s t : ℝ)
    (hst : (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ)) ≤ 1)
    (i : Option (Fin (k + 1))) : |fourthPhase k s t i| ≤ 1 := by
  cases i with
  | none => exact fourthNewPhase_abs_le_one k hst
  | some q => exact fourthOldPhase_abs_le_one (Fin.le_last q) hst

lemma fourthPhase_fintype_sq_sum (k : ℕ) (s t : ℝ) :
    (∑ i : Option (Fin (k + 1)), fourthPhase k s t i ^ 2) = s ^ 2 + t ^ 2 := by
  rw [Fintype.sum_option]
  change (t * fourthWhitenedNewY k) ^ 2 +
      (∑ q : Fin (k + 1),
        (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2) = s ^ 2 + t ^ 2
  have hsumEq :
      (∑ q : Fin (k + 1),
        (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2) =
      ∑ q ∈ Finset.range (k + 1),
        (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2 :=
    Fin.sum_univ_eq_sum_range
      (fun q : ℕ ↦ (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2) (k + 1)
  rw [hsumEq]
  nlinarith [fourthPhase_sq_sum k s t]

lemma fourthPhase_sq_le (k : ℕ) (s t : ℝ) (i : Option (Fin (k + 1))) :
    fourthPhase k s t i ^ 2 ≤
      (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ)) := by
  cases i with
  | none =>
      change (t * fourthWhitenedNewY k) ^ 2 ≤ _
      have hnew := fourthNewLeverage_le k
      change fourthVarianceA k / fourthDet k ≤ 12 / (k + 1 : ℝ) at hnew
      rw [← fourthWhitenedNewY_sq] at hnew
      have ht : t ^ 2 ≤ s ^ 2 + t ^ 2 := by nlinarith [sq_nonneg s]
      calc
        _ = t ^ 2 * fourthWhitenedNewY k ^ 2 := by ring
        _ ≤ (s ^ 2 + t ^ 2) * fourthWhitenedNewY k ^ 2 := by
          exact mul_le_mul_of_nonneg_right ht (sq_nonneg _)
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left hnew (by positivity)
  | some q =>
      change (s * fourthWhitenedX k q + t * fourthWhitenedY k q) ^ 2 ≤ _
      have hphase := linear_phase_sq_le s t (fourthWhitenedX k q) (fourthWhitenedY k q)
      have hlev := fourthOldLeverage_le (Fin.le_last q)
      rw [← fourthWhitened_norm_sq_eq_leverage] at hlev
      exact hphase.trans (mul_le_mul_of_nonneg_left hlev (by positivity))

lemma fourthPhase_fourth_sum_le (k : ℕ) (s t : ℝ) :
    (∑ i : Option (Fin (k + 1)), fourthPhase k s t i ^ 4) ≤
      (12 / (k + 1 : ℝ)) * (s ^ 2 + t ^ 2) ^ 2 := by
  let M : ℝ := (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  calc
    (∑ i : Option (Fin (k + 1)), fourthPhase k s t i ^ 4) =
        ∑ i : Option (Fin (k + 1)),
          fourthPhase k s t i ^ 2 * fourthPhase k s t i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i : Option (Fin (k + 1)), M * fourthPhase k s t i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (fourthPhase_sq_le k s t i) (sq_nonneg _)
    _ = M * ∑ i : Option (Fin (k + 1)), fourthPhase k s t i ^ 2 := by
      rw [Finset.mul_sum]
    _ = M * (s ^ 2 + t ^ 2) := by rw [fourthPhase_fintype_sq_sum]
    _ = (12 / (k + 1 : ℝ)) * (s ^ 2 + t ^ 2) ^ 2 := by
      dsimp [M]
      ring

/-- Explicit bounded-frequency Gaussian approximation for the full fourth characteristic product.
The error is fourth order in the dual radius and `O(1/k)`. -/
lemma fourthCharacteristicProduct_taylor (k : ℕ) (s t : ℝ)
    (hst : (s ^ 2 + t ^ 2) * (12 / (k + 1 : ℝ)) ≤ 1) :
    |Real.cos (t * fourthWhitenedNewY k) *
        (∏ q : Fin (k + 1),
          Real.cos (s * fourthWhitenedX k q + t * fourthWhitenedY k q)) -
      Real.exp (-(s ^ 2 + t ^ 2) / 2)| ≤
        (3 / (k + 1 : ℝ)) * (s ^ 2 + t ^ 2) ^ 2 := by
  have hgeneric := abs_cos_prod_sub_gaussian_prod
    (fourthPhase k s t) (fourthPhase_abs_le_one k s t hst)
  have hcos : (∏ i : Option (Fin (k + 1)), Real.cos (fourthPhase k s t i)) =
      Real.cos (t * fourthWhitenedNewY k) *
        ∏ q : Fin (k + 1),
          Real.cos (s * fourthWhitenedX k q + t * fourthWhitenedY k q) := by
    rw [Fintype.prod_option]
    rfl
  have hgauss : (∏ i : Option (Fin (k + 1)),
      Real.exp (-(fourthPhase k s t i ^ 2) / 2)) =
      Real.exp (-(s ^ 2 + t ^ 2) / 2) := by
    rw [← Real.exp_sum]
    congr 1
    calc
      (∑ i : Option (Fin (k + 1)), -(fourthPhase k s t i ^ 2) / 2) =
          (-1 / 2 : ℝ) * ∑ i : Option (Fin (k + 1)), fourthPhase k s t i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = -(s ^ 2 + t ^ 2) / 2 := by
        rw [fourthPhase_fintype_sq_sum]
        ring
  rw [hcos, hgauss] at hgeneric
  calc
    _ ≤ (1 / 4 : ℝ) *
        ∑ i : Option (Fin (k + 1)), fourthPhase k s t i ^ 4 := hgeneric
    _ ≤ (1 / 4 : ℝ) *
        ((12 / (k + 1 : ℝ)) * (s ^ 2 + t ^ 2) ^ 2) := by
      gcongr
      exact fourthPhase_fourth_sum_le k s t
    _ = (3 / (k + 1 : ℝ)) * (s ^ 2 + t ^ 2) ^ 2 := by ring

end Erdos521
