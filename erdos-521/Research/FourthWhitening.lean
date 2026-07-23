import Research.FourthLeverageSum
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable def fourthDet (k : ℕ) : ℝ :=
  fourthVarianceA k * fourthIncrementVarianceB k -
    fourthIncrementCovarianceC k ^ 2

noncomputable def fourthWhitenedX (k q : ℕ) : ℝ :=
  fourthCoefficientA q / Real.sqrt (fourthVarianceA k)

noncomputable def fourthWhitenedY (k q : ℕ) : ℝ :=
  (fourthVarianceA k * fourthCoefficientB q -
    fourthIncrementCovarianceC k * fourthCoefficientA q) /
      Real.sqrt (fourthVarianceA k * fourthDet k)

noncomputable def fourthWhitenedNewY (k : ℕ) : ℝ :=
  fourthVarianceA k / Real.sqrt (fourthVarianceA k * fourthDet k)

lemma fourthDet_pos (k : ℕ) : 0 < fourthDet k :=
  fourth_covariance_determinant_pos k

lemma fourthVarianceA_pos' (k : ℕ) : 0 < fourthVarianceA k := by
  rw [fourthVarianceA_formula]
  positivity

lemma fourthWhitenedX_sq (k q : ℕ) :
    fourthWhitenedX k q ^ 2 = fourthCoefficientA q ^ 2 / fourthVarianceA k := by
  unfold fourthWhitenedX
  have hA := fourthVarianceA_pos' k
  rw [div_pow, Real.sq_sqrt hA.le]

lemma fourthWhitenedY_sq (k q : ℕ) :
    fourthWhitenedY k q ^ 2 =
      (fourthVarianceA k * fourthCoefficientB q -
        fourthIncrementCovarianceC k * fourthCoefficientA q) ^ 2 /
      (fourthVarianceA k * fourthDet k) := by
  unfold fourthWhitenedY
  have hAD : 0 ≤ fourthVarianceA k * fourthDet k :=
    mul_nonneg (fourthVarianceA_pos' k).le (fourthDet_pos k).le
  rw [div_pow, Real.sq_sqrt hAD]

lemma fourthWhitenedNewY_sq (k : ℕ) :
    fourthWhitenedNewY k ^ 2 =
      fourthVarianceA k / fourthDet k := by
  unfold fourthWhitenedNewY
  have hA := fourthVarianceA_pos' k
  have hD := fourthDet_pos k
  rw [div_pow, Real.sq_sqrt (mul_nonneg hA.le hD.le)]
  field_simp

lemma fourthWhitened_norm_sq_eq_leverage (k q : ℕ) :
    fourthWhitenedX k q ^ 2 + fourthWhitenedY k q ^ 2 =
      fourthOldLeverage k q := by
  rw [fourthWhitenedX_sq, fourthWhitenedY_sq]
  unfold fourthOldLeverage fourthDet
  have hA := fourthVarianceA_pos' k
  have hD := fourth_covariance_determinant_pos k
  field_simp
  unfold fourthOldLeverageNumerator
  ring

/-- The covariance-normalized old vectors plus the new vector have unit first-coordinate variance. -/
lemma fourthWhitened_cov_xx (k : ℕ) :
    (∑ q ∈ Finset.range (k + 1), fourthWhitenedX k q ^ 2) = 1 := by
  simp_rw [fourthWhitenedX_sq]
  rw [← Finset.sum_div]
  change fourthVarianceA k / fourthVarianceA k = 1
  exact div_self (fourthVarianceA_pos' k).ne'

/-- Their cross covariance vanishes. -/
lemma fourthWhitened_cov_xy (k : ℕ) :
    (∑ q ∈ Finset.range (k + 1),
      fourthWhitenedX k q * fourthWhitenedY k q) = 0 := by
  unfold fourthWhitenedX fourthWhitenedY
  have hA := fourthVarianceA_pos' k
  have hD := fourthDet_pos k
  have hsA : Real.sqrt (fourthVarianceA k) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hsAD : Real.sqrt (fourthVarianceA k * fourthDet k) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos hA hD)).ne'
  have hnum : (∑ q ∈ Finset.range (k + 1),
      fourthCoefficientA q *
        (fourthVarianceA k * fourthCoefficientB q -
          fourthIncrementCovarianceC k * fourthCoefficientA q)) = 0 := by
    calc
      _ = ∑ q ∈ Finset.range (k + 1),
          (fourthVarianceA k *
              (fourthCoefficientA q * fourthCoefficientB q) -
            fourthIncrementCovarianceC k * fourthCoefficientA q ^ 2) := by
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = fourthVarianceA k *
          (∑ q ∈ Finset.range (k + 1),
            fourthCoefficientA q * fourthCoefficientB q) -
        fourthIncrementCovarianceC k *
          (∑ q ∈ Finset.range (k + 1), fourthCoefficientA q ^ 2) := by
        rw [Finset.sum_sub_distrib]
        simp_rw [← Finset.mul_sum]
      _ = fourthVarianceA k * fourthIncrementCovarianceC k -
          fourthIncrementCovarianceC k * fourthVarianceA k := by rfl
      _ = 0 := by ring
  simp_rw [div_mul_div_comm]
  rw [← Finset.sum_div]
  change (∑ q ∈ Finset.range (k + 1),
      fourthCoefficientA q *
        (fourthVarianceA k * fourthCoefficientB q -
          fourthIncrementCovarianceC k * fourthCoefficientA q)) /
      (Real.sqrt (fourthVarianceA k) *
        Real.sqrt (fourthVarianceA k * fourthDet k)) = 0
  rw [hnum, zero_div]

/-- Their second-coordinate variance, including the new vector, is one. -/
lemma fourthWhitened_cov_yy (k : ℕ) :
    (∑ q ∈ Finset.range (k + 1), fourthWhitenedY k q ^ 2) +
      fourthWhitenedNewY k ^ 2 = 1 := by
  simp_rw [fourthWhitenedY_sq]
  rw [fourthWhitenedNewY_sq, ← Finset.sum_div]
  have hA := fourthVarianceA_pos' k
  have hD := fourthDet_pos k
  rw [show fourthVarianceA k / fourthDet k =
      fourthVarianceA k ^ 2 / (fourthVarianceA k * fourthDet k) by field_simp]
  rw [← add_div]
  apply (div_eq_one_iff_eq (mul_ne_zero hA.ne' hD.ne')).2
  unfold fourthDet
  unfold fourthVarianceA fourthIncrementVarianceB fourthIncrementCovarianceC
    fourthCoefficientA fourthCoefficientB
  let s := Finset.range (k + 1)
  let a : ℕ → ℝ := fun q ↦ Nat.choose (q + 3) 3
  let b : ℕ → ℝ := fun q ↦ Nat.choose (q + 3) 2
  let A : ℝ := ∑ q ∈ s, (a q) ^ 2
  let B : ℝ := ∑ q ∈ s, (b q) ^ 2
  let C : ℝ := ∑ q ∈ s, a q * b q
  change (∑ q ∈ s, (A * b q - C * a q) ^ 2) + A ^ 2 =
    A * (A * (1 + B) - C ^ 2)
  calc
    _ = (∑ q ∈ s,
        (A ^ 2 * b q ^ 2 - 2 * A * C * (a q * b q) + C ^ 2 * a q ^ 2)) +
        A ^ 2 := by
      apply congrArg (fun z : ℝ ↦ z + A ^ 2)
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = A ^ 2 * B - 2 * A * C * C + C ^ 2 * A + A ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp_rw [← Finset.mul_sum]
      rfl
    _ = A * (A * (1 + B) - C ^ 2) := by ring

end Erdos521
