import Research.FourthWhitenedGlobalDecay
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic

open scoped BigOperators Matrix
open MeasureTheory

namespace Erdos521

noncomputable def fourthWhiteningMatrix (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt (fourthVarianceA k),
      fourthIncrementCovarianceC k / Real.sqrt (fourthVarianceA k);
    0, Real.sqrt (fourthDet k) / Real.sqrt (fourthVarianceA k)]

lemma fourthWhiteningMatrix_mulVec_zero (k : ℕ) (x : Fin 2 → ℝ) :
    (fourthWhiteningMatrix k).mulVec x 0 =
      Real.sqrt (fourthVarianceA k) * x 0 +
        fourthIncrementCovarianceC k / Real.sqrt (fourthVarianceA k) * x 1 := by
  simp [fourthWhiteningMatrix, Matrix.mulVec, Fin.sum_univ_two]
  rfl

lemma fourthWhiteningMatrix_mulVec_one (k : ℕ) (x : Fin 2 → ℝ) :
    (fourthWhiteningMatrix k).mulVec x 1 =
      Real.sqrt (fourthDet k) / Real.sqrt (fourthVarianceA k) * x 1 := by
  simp [fourthWhiteningMatrix, Matrix.mulVec, Fin.sum_univ_two]
  exact Or.inl rfl

lemma fourthWhiteningMatrix_det (k : ℕ) :
    (fourthWhiteningMatrix k).det = Real.sqrt (fourthDet k) := by
  rw [fourthWhiteningMatrix, Matrix.det_fin_two_of]
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hsA : Real.sqrt (fourthVarianceA k) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  field_simp
  ring

lemma fourthWhiteningMatrix_det_pos (k : ℕ) :
    0 < (fourthWhiteningMatrix k).det := by
  rw [fourthWhiteningMatrix_det]
  exact Real.sqrt_pos.2 (fourthDet_pos k)

lemma fourthWhiteningMatrix_det_ne_zero (k : ℕ) :
    (fourthWhiteningMatrix k).det ≠ 0 := (fourthWhiteningMatrix_det_pos k).ne'

/-- The product Gaussian integral on two real coordinates. -/
lemma integral_fin_two_gaussian (b : ℝ) (hb : 0 < b) :
    (∫ x : Fin 2 → ℝ, Real.exp (-b * (x 0 ^ 2 + x 1 ^ 2))) = Real.pi / b := by
  have hpoint (x : Fin 2 → ℝ) :
      Real.exp (-b * (x 0 ^ 2 + x 1 ^ 2)) =
        ∏ i : Fin 2, Real.exp (-b * (x i) ^ 2) := by
    rw [Fin.prod_univ_two, ← Real.exp_add]
    congr 1
    ring
  calc
    (∫ x : Fin 2 → ℝ, Real.exp (-b * (x 0 ^ 2 + x 1 ^ 2))) =
        ∫ x : Fin 2 → ℝ, ∏ i : Fin 2, Real.exp (-b * (x i) ^ 2) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∏ i : Fin 2, ∫ x : ℝ, Real.exp (-b * x ^ 2) :=
      integral_fintype_prod_volume_eq_prod
        (fun _i : Fin 2 ↦ fun x : ℝ ↦ Real.exp (-b * x ^ 2))
    _ = Real.pi / b := by
      simp only [Fin.prod_univ_two]
      have hpib : 0 ≤ Real.pi / b := (div_pos Real.pi_pos hb).le
      rw [← sq, integral_gaussian, Real.sq_sqrt hpib]

/-- Exact full-plane Gaussian change of variables under the fourth covariance-whitening matrix. -/
lemma integral_fourthWhiteningMatrix_gaussian (k : ℕ) (b : ℝ) (hb : 0 < b) :
    (∫ x : Fin 2 → ℝ,
      Real.exp (-b * (((fourthWhiteningMatrix k).mulVec x 0) ^ 2 +
        ((fourthWhiteningMatrix k).mulVec x 1) ^ 2))) =
      (Real.sqrt (fourthDet k))⁻¹ * (Real.pi / b) := by
  let M := fourthWhiteningMatrix k
  let f : (Fin 2 → ℝ) → ℝ := fun y ↦ Real.exp (-b * (y 0 ^ 2 + y 1 ^ 2))
  have hM := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (fourthWhiteningMatrix_det_ne_zero k)
  have hmeas : AEMeasurable (Matrix.toLin' M : (Fin 2 → ℝ) → (Fin 2 → ℝ)) volume :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable.aemeasurable
  have hf : AEStronglyMeasurable f
      (Measure.map (Matrix.toLin' M : (Fin 2 → ℝ) → (Fin 2 → ℝ)) volume) := by
    fun_prop
  have hmap := integral_map hmeas hf
  rw [hM, integral_smul_measure] at hmap
  have hdet : (M.det) = Real.sqrt (fourthDet k) := fourthWhiteningMatrix_det k
  have hsD : 0 < Real.sqrt (fourthDet k) := Real.sqrt_pos.2 (fourthDet_pos k)
  have hfactor : (ENNReal.ofReal |M.det⁻¹|).toReal =
      (Real.sqrt (fourthDet k))⁻¹ := by
    rw [hdet, abs_of_pos (inv_pos.mpr hsD), ENNReal.toReal_ofReal]
    exact (inv_pos.mpr hsD).le
  rw [hfactor, integral_fin_two_gaussian b hb] at hmap
  simpa [M, f, Matrix.toLin'_apply] using hmap.symm

end Erdos521
