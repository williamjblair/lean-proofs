import Research.FourthCoefficientGeometry
import Mathlib.Tactic

namespace Erdos521

noncomputable def fourthOldLeverageNumerator (k q : ℕ) : ℝ :=
  fourthIncrementVarianceB k * fourthCoefficientA q ^ 2 -
    2 * fourthIncrementCovarianceC k * fourthCoefficientA q * fourthCoefficientB q +
    fourthVarianceA k * fourthCoefficientB q ^ 2

noncomputable def fourthOldLeverage (k q : ℕ) : ℝ :=
  fourthOldLeverageNumerator k q /
    (fourthVarianceA k * fourthIncrementVarianceB k -
      fourthIncrementCovarianceC k ^ 2)

lemma fourthOldLeverageNumerator_nonneg (k q : ℕ) :
    0 ≤ fourthOldLeverageNumerator k q := by
  have hA : 0 < fourthVarianceA k := by
    rw [fourthVarianceA_formula]
    positivity
  have hD := fourth_covariance_determinant_pos k
  have hs : 0 ≤ (fourthVarianceA k * fourthCoefficientB q -
      fourthIncrementCovarianceC k * fourthCoefficientA q) ^ 2 := sq_nonneg _
  have hid : fourthVarianceA k * fourthOldLeverageNumerator k q =
      (fourthVarianceA k * fourthCoefficientB q -
        fourthIncrementCovarianceC k * fourthCoefficientA q) ^ 2 +
      (fourthVarianceA k * fourthIncrementVarianceB k -
        fourthIncrementCovarianceC k ^ 2) * fourthCoefficientA q ^ 2 := by
    unfold fourthOldLeverageNumerator
    ring
  have hmul : 0 ≤ fourthVarianceA k * fourthOldLeverageNumerator k q := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left hA).mp hmul

/-- Every old standardized coefficient vector has squared norm (statistical leverage) at most
`12/(k+1)`.  This is the exact regularity estimate needed by a bivariate triangular-array CLT. -/
lemma fourthOldLeverage_mul_bound {k q : ℕ} (hq : q ≤ k) :
    (k + 1 : ℝ) * fourthOldLeverageNumerator k q ≤
      12 * (fourthVarianceA k * fourthIncrementVarianceB k -
        fourthIncrementCovarianceC k ^ 2) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [← sub_nonneg]
  unfold fourthOldLeverageNumerator
  rw [fourth_covariance_determinant_formula,
    fourthVarianceA_formula, fourthIncrementVarianceB_formula,
    fourthIncrementCovarianceC_formula,
    fourthCoefficientA_formula, fourthCoefficientB_formula]
  push_cast
  ring_nf
  positivity

lemma fourthOldLeverage_le {k q : ℕ} (hq : q ≤ k) :
    fourthOldLeverage k q ≤ 12 / (k + 1 : ℝ) := by
  have hD := fourth_covariance_determinant_pos k
  have hk : (0 : ℝ) < k + 1 := by positivity
  unfold fourthOldLeverage
  apply (div_le_div_iff₀ hD hk).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using fourthOldLeverage_mul_bound hq

/-- The new `(0,1)` coefficient vector obeys the same leverage bound. -/
lemma fourthNewLeverage_le (k : ℕ) :
    fourthVarianceA k /
      (fourthVarianceA k * fourthIncrementVarianceB k -
        fourthIncrementCovarianceC k ^ 2) ≤ 12 / (k + 1 : ℝ) := by
  have hD := fourth_covariance_determinant_pos k
  have hk : (0 : ℝ) < k + 1 := by positivity
  apply (div_le_div_iff₀ hD hk).2
  rw [← sub_nonneg]
  rw [fourth_covariance_determinant_formula, fourthVarianceA_formula]
  push_cast
  ring_nf
  positivity

end Erdos521
