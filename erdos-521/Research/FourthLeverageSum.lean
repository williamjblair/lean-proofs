import Research.FourthLeverage
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

lemma fourthOldLeverageNumerator_sum (k : ℕ) :
    (∑ q ∈ Finset.range (k + 1), fourthOldLeverageNumerator k q) +
      fourthVarianceA k =
    2 * (fourthVarianceA k * fourthIncrementVarianceB k -
      fourthIncrementCovarianceC k ^ 2) := by
  unfold fourthOldLeverageNumerator fourthVarianceA fourthIncrementVarianceB
    fourthIncrementCovarianceC fourthCoefficientA fourthCoefficientB
  let s := Finset.range (k + 1)
  let a : ℕ → ℝ := fun q ↦ Nat.choose (q + 3) 3
  let b : ℕ → ℝ := fun q ↦ Nat.choose (q + 3) 2
  let A : ℝ := ∑ q ∈ s, (a q) ^ 2
  let B : ℝ := ∑ q ∈ s, (b q) ^ 2
  let C : ℝ := ∑ q ∈ s, a q * b q
  change (∑ q ∈ s, ((1 + B) * a q ^ 2 - 2 * C * a q * b q + A * b q ^ 2)) + A =
    2 * (A * (1 + B) - C ^ 2)
  have hA : (∑ q ∈ s, (1 + B) * a q ^ 2) = (1 + B) * A := by
    rw [← Finset.mul_sum]
  have hB : (∑ q ∈ s, A * b q ^ 2) = A * B := by
    rw [← Finset.mul_sum]
  have hC : (∑ q ∈ s, 2 * C * a q * b q) = 2 * C * C := by
    calc
      _ = ∑ q ∈ s, (2 * C) * (a q * b q) := by
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = 2 * C * C := by rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hA, hB, hC]
  ring

/-- The old and new standardized coefficient leverages sum exactly to the ambient dimension two. -/
lemma fourthLeverage_sum (k : ℕ) :
    (∑ q ∈ Finset.range (k + 1), fourthOldLeverage k q) +
      fourthVarianceA k /
        (fourthVarianceA k * fourthIncrementVarianceB k -
          fourthIncrementCovarianceC k ^ 2) = 2 := by
  have hD := fourth_covariance_determinant_pos k
  unfold fourthOldLeverage
  rw [← Finset.sum_div]
  rw [← add_div, fourthOldLeverageNumerator_sum]
  field_simp

/-- The total fourth-order leverage quantity is `O(1/k)` with explicit constant 24. -/
lemma fourthLeverage_sq_sum_le (k : ℕ) :
    (∑ q ∈ Finset.range (k + 1), (fourthOldLeverage k q) ^ 2) +
      (fourthVarianceA k /
        (fourthVarianceA k * fourthIncrementVarianceB k -
          fourthIncrementCovarianceC k ^ 2)) ^ 2 ≤
      24 / (k + 1 : ℝ) := by
  let M : ℝ := 12 / (k + 1 : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hold (q : ℕ) (hq : q ∈ Finset.range (k + 1)) :
      (fourthOldLeverage k q) ^ 2 ≤ M * fourthOldLeverage k q := by
    have hqk : q ≤ k := by have := Finset.mem_range.mp hq; omega
    have h0 := fourthOldLeverageNumerator_nonneg k q
    have hD := fourth_covariance_determinant_pos k
    have hlev0 : 0 ≤ fourthOldLeverage k q := div_nonneg h0 hD.le
    have hlevM : fourthOldLeverage k q ≤ M := fourthOldLeverage_le hqk
    nlinarith
  have hnew0 : 0 ≤ fourthVarianceA k /
      (fourthVarianceA k * fourthIncrementVarianceB k -
        fourthIncrementCovarianceC k ^ 2) := by
    exact div_nonneg (by rw [fourthVarianceA_formula]; positivity)
      (fourth_covariance_determinant_pos k).le
  have hnewM : fourthVarianceA k /
      (fourthVarianceA k * fourthIncrementVarianceB k -
        fourthIncrementCovarianceC k ^ 2) ≤ M := fourthNewLeverage_le k
  calc
    _ ≤ (∑ q ∈ Finset.range (k + 1), M * fourthOldLeverage k q) +
        M * (fourthVarianceA k /
          (fourthVarianceA k * fourthIncrementVarianceB k -
            fourthIncrementCovarianceC k ^ 2)) := by
      exact add_le_add (Finset.sum_le_sum fun q hq ↦ hold q hq) (by nlinarith)
    _ = M * ((∑ q ∈ Finset.range (k + 1), fourthOldLeverage k q) +
        fourthVarianceA k /
          (fourthVarianceA k * fourthIncrementVarianceB k -
            fourthIncrementCovarianceC k ^ 2)) := by
      rw [mul_add, Finset.mul_sum]
    _ = M * 2 := by rw [fourthLeverage_sum]
    _ = 24 / (k + 1 : ℝ) := by dsimp [M]; ring

end Erdos521
