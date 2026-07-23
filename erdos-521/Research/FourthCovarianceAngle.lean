import Research.FourthCovarianceExact
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable def fourthVarianceA (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k + 1), (Nat.choose (l + 3) 3 : ℝ) ^ 2

noncomputable def fourthIncrementVarianceB (k : ℕ) : ℝ :=
  1 + ∑ l ∈ Finset.range (k + 1), (Nat.choose (l + 3) 2 : ℝ) ^ 2

noncomputable def fourthIncrementCovarianceC (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k + 1),
    (Nat.choose (l + 3) 3 : ℝ) * Nat.choose (l + 3) 2

lemma fourthVarianceA_formula (k : ℕ) :
    fourthVarianceA k =
      (k + 1 : ℝ) * (k + 2 : ℝ) * (k + 3 : ℝ) * (k + 4 : ℝ) *
        (2 * k + 5 : ℝ) * (5 * (k : ℝ) ^ 2 + 25 * k + 21) / 2520 :=
  sum_choose_add_three_sq k

lemma fourthIncrementVarianceB_formula (k : ℕ) :
    fourthIncrementVarianceB k = 1 +
      (k + 1 : ℝ) *
        (3 * (k : ℝ) ^ 4 + 42 * (k : ℝ) ^ 3 + 223 * (k : ℝ) ^ 2 +
          542 * k + 540) / 60 := by
  rw [fourthIncrementVarianceB, sum_choose_add_three_two_sq]

lemma fourthIncrementCovarianceC_formula (k : ℕ) :
    fourthIncrementCovarianceC k =
      (k + 1 : ℝ) * (k + 2 : ℝ) * (k + 3 : ℝ) * (k + 4 : ℝ) *
        (5 * (k : ℝ) ^ 2 + 31 * k + 45) / 360 :=
  sum_choose_add_three_mul k

/-- Exact Gram determinant of the fourth-sum coefficient vector and its one-step increment. -/
lemma fourth_covariance_determinant_formula (k : ℕ) :
    fourthVarianceA k * fourthIncrementVarianceB k -
        fourthIncrementCovarianceC k ^ 2 =
      (k + 1 : ℝ) * (k + 2 : ℝ) ^ 2 * (k + 3 : ℝ) ^ 2 *
        (k + 4 : ℝ) ^ 2 * (k + 5 : ℝ) *
        (5 * (k : ℝ) ^ 4 + 60 * (k : ℝ) ^ 3 + 259 * (k : ℝ) ^ 2 +
          474 * k + 315) / 907200 := by
  rw [fourthVarianceA_formula, fourthIncrementVarianceB_formula,
    fourthIncrementCovarianceC_formula]
  ring

lemma fourth_covariance_determinant_pos (k : ℕ) :
    0 < fourthVarianceA k * fourthIncrementVarianceB k -
      fourthIncrementCovarianceC k ^ 2 := by
  rw [fourth_covariance_determinant_formula]
  positivity

/-- The squared sine of the angle between adjacent fourth-sum coefficient vectors is at most
`(3/(5(k+1)))²`.  This is an exact finite inequality, not merely its `7/20` asymptotic. -/
lemma fourth_covariance_angle_sq_bound (k : ℕ) :
    25 * (k + 1 : ℝ) ^ 2 *
        (fourthVarianceA k * fourthIncrementVarianceB k -
          fourthIncrementCovarianceC k ^ 2) ≤
      9 * fourthVarianceA k *
        (fourthVarianceA k + 2 * fourthIncrementCovarianceC k +
          fourthIncrementVarianceB k) := by
  have hid :
      9 * fourthVarianceA k *
          (fourthVarianceA k + 2 * fourthIncrementCovarianceC k +
            fourthIncrementVarianceB k) -
        25 * (k + 1 : ℝ) ^ 2 *
          (fourthVarianceA k * fourthIncrementVarianceB k -
            fourthIncrementCovarianceC k ^ 2) =
      (k + 1 : ℝ) * (k + 2 : ℝ) ^ 2 * (k + 3 : ℝ) ^ 2 *
        (k + 4 : ℝ) ^ 2 * (k + 5 : ℝ) *
        (25 * (k : ℝ) ^ 6 + 3950 * (k : ℝ) ^ 5 + 49935 * (k : ℝ) ^ 4 +
          249520 * (k : ℝ) ^ 3 + 595391 * (k : ℝ) ^ 2 +
          671286 * k + 282240) / 6350400 := by
    rw [fourthVarianceA_formula, fourthIncrementVarianceB_formula,
      fourthIncrementCovarianceC_formula]
    ring
  have hnonneg : 0 ≤
      (k + 1 : ℝ) * (k + 2 : ℝ) ^ 2 * (k + 3 : ℝ) ^ 2 *
        (k + 4 : ℝ) ^ 2 * (k + 5 : ℝ) *
        (25 * (k : ℝ) ^ 6 + 3950 * (k : ℝ) ^ 5 + 49935 * (k : ℝ) ^ 4 +
          249520 * (k : ℝ) ^ 3 + 595391 * (k : ℝ) ^ 2 +
          671286 * k + 282240) / 6350400 := by
    positivity
  linarith

end Erdos521
