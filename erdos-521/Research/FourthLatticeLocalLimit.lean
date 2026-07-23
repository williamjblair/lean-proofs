import Research.FourthLatticeFourierInversion
import Mathlib.Tactic

open scoped BigOperators Matrix ComplexConjugate
open MeasureTheory

namespace Erdos521

/-- Integer coefficient vectors for the old fourth-integrated sum and its one-step increment. -/
def fourthSignedIntegerVector (k : ℕ) : Option (Fin (k + 1)) → Fin 2 → ℤ
  | none, j => if j = 0 then 0 else 1
  | some q, j => if j = 0 then fourthIntegerA q else fourthIntegerB q

lemma fourthSignedIntegerVector_phase (k : ℕ) (x : Fin 2 → ℝ)
    (i : Option (Fin (k + 1))) :
    (∑ j : Fin 2, x j * (fourthSignedIntegerVector k i j : ℝ)) =
      fourthOriginalPhase k (x 0) (x 1) i := by
  cases i with
  | none =>
      simp [fourthSignedIntegerVector, fourthOriginalPhase, Fin.sum_univ_two]
  | some q =>
      simp [fourthSignedIntegerVector, fourthOriginalPhase, Fin.sum_univ_two,
        fourthIntegerA, fourthIntegerB, fourthCoefficientA, fourthCoefficientB]

lemma signedIntCharacteristic_fourthSignedIntegerVector (k : ℕ) (x : Fin 2 → ℝ) :
    signedIntCharacteristic (fourthSignedIntegerVector k) x =
      (fourthOriginalCharacteristicProduct k (x 0) (x 1) : ℂ) := by
  unfold signedIntCharacteristic fourthOriginalCharacteristicProduct
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  exact_mod_cast fourthSignedIntegerVector_phase k x i

noncomputable def fourthLatticeAtomProbability (k : ℕ) (d : Fin 2 → ℤ) : ℝ :=
  signedIntAtomProbability (fourthSignedIntegerVector k) d

noncomputable def fourthGaussianCellAtom (k : ℕ) (d : Fin 2 → ℤ) : ℂ :=
  (1 / Real.pi ^ 2 : ℂ) *
    ∫ x : Fin 2 → ℝ in fourthDualCell,
      (Real.exp (-(fourthWhiteningRadiusSq k x) / 2) : ℂ) *
        Complex.exp (-Complex.I *
          (∑ j : Fin 2, x j *
            (signedIntLatticeTarget (fourthSignedIntegerVector k) d j : ℝ)))

lemma fourthLatticeAtomProbability_fourier_inversion (k : ℕ) (d : Fin 2 → ℤ) :
    (fourthLatticeAtomProbability k d : ℂ) =
      (1 / Real.pi ^ 2 : ℂ) *
        ∫ x : Fin 2 → ℝ in fourthDualCell,
          (fourthOriginalCharacteristicProduct k (x 0) (x 1) : ℂ) *
            Complex.exp (-Complex.I *
              (∑ j : Fin 2, x j *
                (signedIntLatticeTarget (fourthSignedIntegerVector k) d j : ℝ))) := by
  unfold fourthLatticeAtomProbability
  rw [signedIntAtomProbability_fourier_inversion]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [signedIntCharacteristic_fourthSignedIntegerVector]

/-- The explicit right side of F-086. -/
noncomputable def fourthFourierL1ErrorBound (N : ℕ) : ℝ :=
  (6144 / (N + 2 + 1 : ℝ)) * (Real.sqrt (fourthDet (N + 2)))⁻¹ *
      (Real.pi / (1 / (2 * Real.pi ^ 2))) +
    (Real.pi ^ 2 * fourthMacroscopicDecay N +
      Real.exp (-(fourthGlobalRadialRate / 2) * fourthTaylorRadius N) *
        ((Real.sqrt (fourthDet (N + 2)))⁻¹ *
          (Real.pi / (fourthGlobalRadialRate / 2))) +
      Real.exp (-(1 / 4 : ℝ) * fourthTaylorRadius N) *
        ((Real.sqrt (fourthDet (N + 2)))⁻¹ * (Real.pi / (1 / 4 : ℝ))))

lemma integral_fourthOriginalCharacteristicProduct_full_error_le_bound
    (N : ℕ) (hN : 21 ≤ N) :
    (∫ x in fourthDualCell,
      |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2)|) ≤
      fourthFourierL1ErrorBound N := by
  exact integral_fourthOriginalCharacteristicProduct_full_error N hN

/-- F-086 and exact lattice inversion give a uniform atomwise comparison with the covariance
Gaussian Fourier integral over the fundamental cell. -/
lemma fourthLatticeAtomProbability_sub_gaussianCellAtom
    (N : ℕ) (hN : 21 ≤ N) (d : Fin 2 → ℤ) :
    ‖(fourthLatticeAtomProbability (N + 2) d : ℂ) -
        fourthGaussianCellAtom (N + 2) d‖ ≤
      (1 / Real.pi ^ 2 : ℝ) * fourthFourierL1ErrorBound N := by
  let phase : (Fin 2 → ℝ) → ℂ := fun x ↦
    Complex.exp (-Complex.I *
      (∑ j : Fin 2, x j *
        (signedIntLatticeTarget (fourthSignedIntegerVector (N + 2)) d j : ℝ)))
  let f : (Fin 2 → ℝ) → ℂ := fun x ↦
    (fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1) : ℂ) * phase x
  let g : (Fin 2 → ℝ) → ℂ := fun x ↦
    (Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2) : ℂ) * phase x
  have hphaseCont : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hfCont : Continuous f := by
    dsimp [f]
    exact (Complex.continuous_ofReal.comp
      (continuous_fourthOriginalCharacteristicProduct_pi (N + 2))).mul hphaseCont
  have hgCont : Continuous g := by
    dsimp [g]
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp
        ((continuous_fourthWhiteningRadiusSq (N + 2)).neg.div_const 2))).mul hphaseCont
  have hf : IntegrableOn f fourthDualCell volume :=
    hfCont.continuousOn.integrableOn_compact isCompact_fourthDualCell
  have hg : IntegrableOn g fourthDualCell volume :=
    hgCont.continuousOn.integrableOn_compact isCompact_fourthDualCell
  have hphase (x : Fin 2 → ℝ) : ‖phase x‖ = 1 := by
    dsimp [phase]
    rw [Complex.norm_exp]
    simp
  rw [fourthLatticeAtomProbability_fourier_inversion]
  unfold fourthGaussianCellAtom
  change ‖(1 / Real.pi ^ 2 : ℂ) * (∫ x in fourthDualCell, f x) -
      (1 / Real.pi ^ 2 : ℂ) * (∫ x in fourthDualCell, g x)‖ ≤ _
  rw [← mul_sub, ← integral_sub hf hg, norm_mul]
  calc
    ‖(1 / Real.pi ^ 2 : ℂ)‖ *
        ‖∫ x in fourthDualCell, f x - g x‖ ≤
      ‖(1 / Real.pi ^ 2 : ℂ)‖ *
        ∫ x in fourthDualCell, ‖f x - g x‖ := by
          gcongr
          exact norm_integral_le_integral_norm _
    _ = (1 / Real.pi ^ 2 : ℝ) *
        ∫ x in fourthDualCell,
          |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1) -
            Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2)| := by
      congr 1
      · rw [Complex.norm_div, norm_one, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      · apply integral_congr_ae
        filter_upwards [] with x
        dsimp [f, g]
        rw [← sub_mul, norm_mul, hphase, mul_one]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / Real.pi ^ 2 : ℝ) * fourthFourierL1ErrorBound N := by
      exact mul_le_mul_of_nonneg_left
        (integral_fourthOriginalCharacteristicProduct_full_error_le_bound N hN)
        (by positivity)

end Erdos521
