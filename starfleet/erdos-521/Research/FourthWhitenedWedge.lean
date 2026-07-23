import Research.FourthWhitening
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable def fourthOldLinearSum (k : ℕ) (e : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.range (k + 1), fourthCoefficientA q * e q

noncomputable def fourthIncrementLinearSum (k : ℕ) (e : ℕ → ℝ) (z : ℝ) : ℝ :=
  z + ∑ q ∈ Finset.range (k + 1), fourthCoefficientB q * e q

noncomputable def fourthWhitenedLinearX (k : ℕ) (e : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.range (k + 1), fourthWhitenedX k q * e q

noncomputable def fourthWhitenedLinearY (k : ℕ) (e : ℕ → ℝ) (z : ℝ) : ℝ :=
  fourthWhitenedNewY k * z +
    ∑ q ∈ Finset.range (k + 1), fourthWhitenedY k q * e q

lemma fourthWhitenedLinearX_reconstruct (k : ℕ) (e : ℕ → ℝ) :
    Real.sqrt (fourthVarianceA k) * fourthWhitenedLinearX k e =
      fourthOldLinearSum k e := by
  unfold fourthWhitenedLinearX fourthWhitenedX fourthOldLinearSum
  have hs : Real.sqrt (fourthVarianceA k) ≠ 0 :=
    (Real.sqrt_pos.2 (fourthVarianceA_pos' k)).ne'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  field_simp

lemma fourthWhitenedLinearY_reconstruct (k : ℕ) (e : ℕ → ℝ) (z : ℝ) :
    Real.sqrt (fourthVarianceA k * fourthDet k) * fourthWhitenedLinearY k e z =
      fourthVarianceA k * fourthIncrementLinearSum k e z -
        fourthIncrementCovarianceC k * fourthOldLinearSum k e := by
  unfold fourthWhitenedLinearY fourthWhitenedNewY fourthWhitenedY
    fourthIncrementLinearSum fourthOldLinearSum
  have hs : Real.sqrt (fourthVarianceA k * fourthDet k) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (fourthVarianceA_pos' k) (fourthDet_pos k))).ne'
  rw [mul_add, Finset.mul_sum]
  field_simp
  calc
    _ = fourthVarianceA k * z +
        ∑ q ∈ Finset.range (k + 1),
          (fourthVarianceA k * (fourthCoefficientB q * e q) -
            fourthIncrementCovarianceC k * (fourthCoefficientA q * e q)) := by
      apply congrArg (fun x : ℝ ↦ fourthVarianceA k * z + x)
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = fourthVarianceA k * z +
        ((∑ q ∈ Finset.range (k + 1),
            fourthVarianceA k * (fourthCoefficientB q * e q)) -
          ∑ q ∈ Finset.range (k + 1),
            fourthIncrementCovarianceC k * (fourthCoefficientA q * e q)) := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      ring

/-- In exact identity-covariance coordinates, the adjacent fourth-sum crossing event is a narrow
wedge with normal `(A+C,sqrt(det))`. -/
lemma fourth_crossing_product_whitened (k : ℕ) (e : ℕ → ℝ) (z : ℝ) :
    fourthOldLinearSum k e *
        (fourthOldLinearSum k e + fourthIncrementLinearSum k e z) =
      fourthWhitenedLinearX k e *
        ((fourthVarianceA k + fourthIncrementCovarianceC k) *
            fourthWhitenedLinearX k e +
          Real.sqrt (fourthDet k) * fourthWhitenedLinearY k e z) := by
  let A := fourthVarianceA k
  let C := fourthIncrementCovarianceC k
  let D := fourthDet k
  let X := fourthOldLinearSum k e
  let I := fourthIncrementLinearSum k e z
  let U := fourthWhitenedLinearX k e
  let W := fourthWhitenedLinearY k e z
  let sA := Real.sqrt A
  let sD := Real.sqrt D
  have hA : 0 < A := fourthVarianceA_pos' k
  have hD : 0 < D := fourthDet_pos k
  have hsA : sA ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hsA2 : sA ^ 2 = A := Real.sq_sqrt hA.le
  have hX : sA * U = X := fourthWhitenedLinearX_reconstruct k e
  have hY0 := fourthWhitenedLinearY_reconstruct k e z
  have hsAD : Real.sqrt (A * D) = sA * sD := Real.sqrt_mul hA.le D
  have hY : sA * sD * W = A * I - C * X := by
    rw [← hsAD]
    exact hY0
  rw [← hX] at hY
  have hbracket : sA * I - C * U - sD * W = 0 := by
    apply (mul_left_cancel₀ hsA)
    linear_combination -hY + I * hsA2
  have hsolve : sD * W = sA * I - C * U := by linarith
  change X * (X + I) = U * ((A + C) * U + sD * W)
  rw [← hX, hsolve]
  linear_combination (U ^ 2) * hsA2

lemma fourth_crossing_iff_whitened (k : ℕ) (e : ℕ → ℝ) (z : ℝ) :
    fourthOldLinearSum k e *
        (fourthOldLinearSum k e + fourthIncrementLinearSum k e z) ≤ 0 ↔
      fourthWhitenedLinearX k e *
        ((fourthVarianceA k + fourthIncrementCovarianceC k) *
            fourthWhitenedLinearX k e +
          Real.sqrt (fourthDet k) * fourthWhitenedLinearY k e z) ≤ 0 := by
  rw [fourth_crossing_product_whitened]

end Erdos521
