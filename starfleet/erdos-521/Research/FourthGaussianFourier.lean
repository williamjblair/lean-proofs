import Research.FourthLatticeLocalLimit
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic

open scoped BigOperators Matrix ComplexConjugate
open MeasureTheory

namespace Erdos521

/-- Primal coordinates dual to the covariance whitening map. -/
noncomputable def fourthPrimalWhitening (k : ℕ) (y : Fin 2 → ℝ) : Fin 2 → ℝ
  | 0 => y 0 / Real.sqrt (fourthVarianceA k)
  | 1 => (fourthVarianceA k * y 1 - fourthIncrementCovarianceC k * y 0) /
      Real.sqrt (fourthVarianceA k * fourthDet k)

lemma fourthPrimalWhitening_dot_whiteningMatrix (k : ℕ)
    (y x : Fin 2 → ℝ) :
    (∑ j : Fin 2, fourthPrimalWhitening k y j *
      ((fourthWhiteningMatrix k).mulVec x j)) =
      ∑ j : Fin 2, y j * x j := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two,
    fourthWhiteningMatrix_mulVec_zero, fourthWhiteningMatrix_mulVec_one]
  simp only [fourthPrimalWhitening]
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hD : 0 < fourthDet k := fourthDet_pos k
  have hsA : Real.sqrt (fourthVarianceA k) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hsD : Real.sqrt (fourthDet k) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  rw [Real.sqrt_mul hA.le (fourthDet k)]
  field_simp
  rw [Real.sq_sqrt hA.le]
  ring

lemma integral_standardGaussian_fourier_fin_two (w : Fin 2 → ℝ) :
    (∫ u : Fin 2 → ℝ,
      (Real.exp (-(u 0 ^ 2 + u 1 ^ 2) / 2) : ℂ) *
        Complex.exp (-Complex.I * (∑ j : Fin 2, w j * u j))) =
      (2 * Real.pi : ℂ) *
        Complex.exp (-(∑ j : Fin 2, w j ^ 2) / 2) := by
  let b : ℂ := 1 / 2
  let c : Fin 2 → ℂ := fun j ↦ -Complex.I * (w j : ℂ)
  have hb : 0 < b.re := by norm_num [b]
  have hformula := GaussianFourier.integral_cexp_neg_mul_sum_add (ι := Fin 2) hb c
  have hpoint (u : Fin 2 → ℝ) :
      (Real.exp (-(u 0 ^ 2 + u 1 ^ 2) / 2) : ℂ) *
          Complex.exp (-Complex.I * (∑ j : Fin 2, w j * u j)) =
        Complex.exp (-b * ∑ j : Fin 2, (u j : ℂ) ^ 2 +
          ∑ j : Fin 2, c j * u j) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [Fin.sum_univ_two]
    dsimp [b, c]
    push_cast
    ring
  rw [show (∫ u : Fin 2 → ℝ,
      (Real.exp (-(u 0 ^ 2 + u 1 ^ 2) / 2) : ℂ) *
        Complex.exp (-Complex.I * (∑ j : Fin 2, w j * u j))) =
      ∫ u : Fin 2 → ℝ, Complex.exp (-b * ∑ j : Fin 2, (u j : ℂ) ^ 2 +
        ∑ j : Fin 2, c j * u j) by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint]
  rw [hformula]
  simp only [Fintype.card_fin]
  have hp : (Real.pi : ℂ) / b = 2 * Real.pi := by
    dsimp [b]
    push_cast
    ring
  rw [hp]
  norm_num
  congr 1
  dsimp [b, c]
  push_cast
  simp [mul_pow, Complex.I_sq]
  ring

/-- The full-plane Gaussian Fourier coefficient associated with a primal lattice point. -/
noncomputable def fourthGaussianFullAtom (k : ℕ) (y : Fin 2 → ℝ) : ℝ :=
  (2 / (Real.pi * Real.sqrt (fourthDet k))) *
    Real.exp (-(∑ j : Fin 2, fourthPrimalWhitening k y j ^ 2) / 2)

lemma fourthGaussianFullAtom_fourier (k : ℕ) (y : Fin 2 → ℝ) :
    (fourthGaussianFullAtom k y : ℂ) =
      (1 / Real.pi ^ 2 : ℂ) *
        ∫ x : Fin 2 → ℝ,
          (Real.exp (-(fourthWhiteningRadiusSq k x) / 2) : ℂ) *
            Complex.exp (-Complex.I * (∑ j : Fin 2, x j * y j)) := by
  let M := fourthWhiteningMatrix k
  let w := fourthPrimalWhitening k y
  let f : (Fin 2 → ℝ) → ℂ := fun u ↦
    (Real.exp (-(u 0 ^ 2 + u 1 ^ 2) / 2) : ℂ) *
      Complex.exp (-Complex.I * (∑ j : Fin 2, w j * u j))
  have hM := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (fourthWhiteningMatrix_det_ne_zero k)
  have hmeas : AEMeasurable (Matrix.toLin' M : (Fin 2 → ℝ) → (Fin 2 → ℝ)) volume :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable.aemeasurable
  have hf : AEStronglyMeasurable f
      (Measure.map (Matrix.toLin' M : (Fin 2 → ℝ) → (Fin 2 → ℝ)) volume) := by
    dsimp [f, w]
    fun_prop
  have hmap := integral_map hmeas hf
  rw [hM, integral_smul_measure] at hmap
  have hdet : M.det = Real.sqrt (fourthDet k) := fourthWhiteningMatrix_det k
  have hsD : 0 < Real.sqrt (fourthDet k) := Real.sqrt_pos.2 (fourthDet_pos k)
  have hfactor : (ENNReal.ofReal |M.det⁻¹|).toReal =
      (Real.sqrt (fourthDet k))⁻¹ := by
    rw [hdet, abs_of_pos (inv_pos.mpr hsD), ENNReal.toReal_ofReal]
    exact (inv_pos.mpr hsD).le
  rw [hfactor, integral_standardGaussian_fourier_fin_two w] at hmap
  have hcomp (x : Fin 2 → ℝ) :
      f ((Matrix.toLin' M) x) =
        (Real.exp (-(fourthWhiteningRadiusSq k x) / 2) : ℂ) *
          Complex.exp (-Complex.I * (∑ j : Fin 2, x j * y j)) := by
    dsimp [f, w, M, Matrix.toLin'_apply, fourthWhiteningRadiusSq]
    rw [fourthPrimalWhitening_dot_whiteningMatrix]
    have hdot : (∑ j : Fin 2, y j * x j) = ∑ j : Fin 2, x j * y j := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hdot]
  rw [show (∫ x : Fin 2 → ℝ,
      (Real.exp (-(fourthWhiteningRadiusSq k x) / 2) : ℂ) *
        Complex.exp (-Complex.I * (∑ j : Fin 2, x j * y j))) =
      ∫ x : Fin 2 → ℝ, f ((Matrix.toLin' M) x) by
        apply integral_congr_ae
        filter_upwards [] with x
        exact (hcomp x).symm]
  rw [← hmap]
  unfold fourthGaussianFullAtom
  dsimp [w]
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsDC : (Real.sqrt (fourthDet k) : ℂ) ≠ 0 := by exact_mod_cast hsD.ne'
  field_simp

/-- Completing the square in the first coordinate gives a lower bound by the residual variance
in the increment direction. -/
lemma fourthWhiteningRadiusSq_ge_det_div_A_mul_sq_one (k : ℕ) (x : Fin 2 → ℝ) :
    fourthDet k / fourthVarianceA k * x 1 ^ 2 ≤ fourthWhiteningRadiusSq k x := by
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hsq : 0 ≤ fourthVarianceA k *
      (x 0 + fourthIncrementCovarianceC k / fourthVarianceA k * x 1) ^ 2 := by
    positivity
  calc
    fourthDet k / fourthVarianceA k * x 1 ^ 2 ≤
        fourthDet k / fourthVarianceA k * x 1 ^ 2 +
          fourthVarianceA k *
            (x 0 + fourthIncrementCovarianceC k / fourthVarianceA k * x 1) ^ 2 :=
      le_add_of_nonneg_right hsq
    _ = fourthWhiteningRadiusSq k x := by
      rw [fourthWhiteningRadiusSq_eq_original_sq_sum,
        fourthOriginalPhase_sq_sum]
      unfold fourthDet
      field_simp
      ring

/-- Completing the square in the second coordinate gives the symmetric residual lower bound. -/
lemma fourthWhiteningRadiusSq_ge_det_div_B_mul_sq_zero (k : ℕ) (x : Fin 2 → ℝ) :
    fourthDet k / fourthIncrementVarianceB k * x 0 ^ 2 ≤
      fourthWhiteningRadiusSq k x := by
  have hB : 0 < fourthIncrementVarianceB k := by
    unfold fourthIncrementVarianceB
    positivity
  have hsq : 0 ≤ fourthIncrementVarianceB k *
      (x 1 + fourthIncrementCovarianceC k / fourthIncrementVarianceB k * x 0) ^ 2 := by
    positivity
  calc
    fourthDet k / fourthIncrementVarianceB k * x 0 ^ 2 ≤
        fourthDet k / fourthIncrementVarianceB k * x 0 ^ 2 +
          fourthIncrementVarianceB k *
            (x 1 + fourthIncrementCovarianceC k / fourthIncrementVarianceB k * x 0) ^ 2 :=
      le_add_of_nonneg_right hsq
    _ = fourthWhiteningRadiusSq k x := by
      rw [fourthWhiteningRadiusSq_eq_original_sq_sum,
        fourthOriginalPhase_sq_sum]
      unfold fourthDet
      field_simp
      ring

noncomputable def fourthDualGaussianEscapeRadius (k : ℕ) : ℝ :=
  (fourthDet k / (fourthVarianceA k + fourthIncrementVarianceB k)) *
    (Real.pi ^ 2 / 4)

lemma fourthDualGaussianEscapeRadius_pos (k : ℕ) :
    0 < fourthDualGaussianEscapeRadius k := by
  unfold fourthDualGaussianEscapeRadius
  have hB : 0 < fourthIncrementVarianceB k := by
    unfold fourthIncrementVarianceB
    positivity
  exact mul_pos
    (div_pos (fourthDet_pos k) (add_pos (fourthVarianceA_pos' k) hB))
    (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num))

lemma fourthDualGaussianEscapeRadius_le_of_not_mem (k : ℕ) (x : Fin 2 → ℝ)
    (hx : x ∉ fourthDualCell) :
    fourthDualGaussianEscapeRadius k ≤ fourthWhiteningRadiusSq k x := by
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hB : 0 < fourthIncrementVarianceB k := by
    unfold fourthIncrementVarianceB
    positivity
  have hD : 0 < fourthDet k := fourthDet_pos k
  have hden : 0 < fourthVarianceA k + fourthIncrementVarianceB k := by positivity
  rw [mem_fourthDualCell_iff, not_and_or] at hx
  rcases hx with hx | hx
  · have habs : Real.pi / 2 < |x 0| := lt_of_not_ge hx
    have hsq0 : (Real.pi / 2) ^ 2 ≤ |x 0| ^ 2 :=
      (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 habs.le
    have hsq : (Real.pi / 2) ^ 2 ≤ x 0 ^ 2 := by
      simpa only [sq_abs] using hsq0
    have hfrac : fourthDet k /
        (fourthVarianceA k + fourthIncrementVarianceB k) ≤
        fourthDet k / fourthIncrementVarianceB k := by
      apply (div_le_div_iff₀ hden hB).2
      nlinarith
    calc
      fourthDualGaussianEscapeRadius k =
          (fourthDet k / (fourthVarianceA k + fourthIncrementVarianceB k)) *
            (Real.pi / 2) ^ 2 := by
        unfold fourthDualGaussianEscapeRadius
        ring
      _ ≤ (fourthDet k / fourthIncrementVarianceB k) * x 0 ^ 2 := by
        exact mul_le_mul hfrac hsq (by positivity) (by positivity)
      _ ≤ fourthWhiteningRadiusSq k x :=
        fourthWhiteningRadiusSq_ge_det_div_B_mul_sq_zero k x
  · have habs : Real.pi / 2 < |x 1| := lt_of_not_ge hx
    have hsq0 : (Real.pi / 2) ^ 2 ≤ |x 1| ^ 2 :=
      (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 habs.le
    have hsq : (Real.pi / 2) ^ 2 ≤ x 1 ^ 2 := by
      simpa only [sq_abs] using hsq0
    have hfrac : fourthDet k /
        (fourthVarianceA k + fourthIncrementVarianceB k) ≤
        fourthDet k / fourthVarianceA k := by
      apply (div_le_div_iff₀ hden hA).2
      nlinarith
    calc
      fourthDualGaussianEscapeRadius k =
          (fourthDet k / (fourthVarianceA k + fourthIncrementVarianceB k)) *
            (Real.pi / 2) ^ 2 := by
        unfold fourthDualGaussianEscapeRadius
        ring
      _ ≤ (fourthDet k / fourthVarianceA k) * x 1 ^ 2 := by
        exact mul_le_mul hfrac hsq (by positivity) (by positivity)
      _ ≤ fourthWhiteningRadiusSq k x :=
        fourthWhiteningRadiusSq_ge_det_div_A_mul_sq_one k x

/-- The covariance Gaussian has an exponentially small Fourier tail outside the fundamental
lattice cell. -/
lemma integral_fourthGaussian_compl_dualCell (k : ℕ) :
    (∫ x in fourthDualCellᶜ,
      Real.exp (-(fourthWhiteningRadiusSq k x) / 2)) ≤
      Real.exp (-(1 / 4 : ℝ) * fourthDualGaussianEscapeRadius k) *
        ((Real.sqrt (fourthDet k))⁻¹ * (Real.pi / (1 / 4 : ℝ))) := by
  let f : (Fin 2 → ℝ) → ℝ := fun x ↦
    Real.exp (-(fourthWhiteningRadiusSq k x) / 2)
  let C : ℝ := Real.exp (-(1 / 4 : ℝ) * fourthDualGaussianEscapeRadius k)
  let g : (Fin 2 → ℝ) → ℝ := fun x ↦
    C * Real.exp (-(1 / 4 : ℝ) * fourthWhiteningRadiusSq k x)
  have hs : MeasurableSet fourthDualCellᶜ := measurableSet_fourthDualCell.compl
  have hgfull : Integrable g :=
    (integrable_fourthWhiteningMatrix_gaussian k (1 / 4) (by norm_num)).const_mul C
  have hfg : ∀ x ∈ fourthDualCellᶜ, f x ≤ g x := by
    intro x hx
    dsimp [f, g, C]
    have ht := exp_neg_mul_radius_tail (b := (1 / 2 : ℝ))
      (R := fourthDualGaussianEscapeRadius k) (by norm_num)
      (fourthDualGaussianEscapeRadius_le_of_not_mem k x hx)
    convert ht using 1 <;> ring
  have hfmeas : AEStronglyMeasurable f (volume.restrict fourthDualCellᶜ) := by
    apply Continuous.aestronglyMeasurable
    dsimp [f]
    exact Real.continuous_exp.comp
      ((continuous_fourthWhiteningRadiusSq k).neg.div_const 2)
  have hf : IntegrableOn f fourthDualCellᶜ volume := by
    apply hgfull.integrableOn.mono' hfmeas
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hfg x hx
  calc
    (∫ x in fourthDualCellᶜ,
      Real.exp (-(fourthWhiteningRadiusSq k x) / 2)) = ∫ x in fourthDualCellᶜ, f x := rfl
    _ ≤ ∫ x in fourthDualCellᶜ, g x := setIntegral_mono_on hf hgfull.integrableOn hs hfg
    _ ≤ ∫ x, g x := setIntegral_le_integral hgfull
      (Filter.Eventually.of_forall fun x ↦ mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = C * ((Real.sqrt (fourthDet k))⁻¹ * (Real.pi / (1 / 4 : ℝ))) := by
      rw [show (∫ x, g x) = C * ∫ x : Fin 2 → ℝ,
          Real.exp (-(1 / 4 : ℝ) * fourthWhiteningRadiusSq k x) by
        exact integral_const_mul C _]
      rw [show (∫ x : Fin 2 → ℝ,
          Real.exp (-(1 / 4 : ℝ) * fourthWhiteningRadiusSq k x)) =
          (Real.sqrt (fourthDet k))⁻¹ * (Real.pi / (1 / 4 : ℝ)) by
        simpa [fourthWhiteningRadiusSq] using
          integral_fourthWhiteningMatrix_gaussian k (1 / 4) (by norm_num)]
    _ = _ := rfl

noncomputable def fourthGaussianFourierTailBound (k : ℕ) : ℝ :=
  (1 / Real.pi ^ 2) *
    (Real.exp (-(1 / 4 : ℝ) * fourthDualGaussianEscapeRadius k) *
      ((Real.sqrt (fourthDet k))⁻¹ * (Real.pi / (1 / 4 : ℝ))))

lemma fourthGaussianCellAtom_sub_fullAtom (k : ℕ) (d : Fin 2 → ℤ) :
    ‖fourthGaussianCellAtom k d -
        (fourthGaussianFullAtom k
          (fun j ↦ (signedIntLatticeTarget (fourthSignedIntegerVector k) d j : ℝ)) : ℂ)‖ ≤
      fourthGaussianFourierTailBound k := by
  let y : Fin 2 → ℝ := fun j ↦
    (signedIntLatticeTarget (fourthSignedIntegerVector k) d j : ℝ)
  let h : (Fin 2 → ℝ) → ℂ := fun x ↦
    (Real.exp (-(fourthWhiteningRadiusSq k x) / 2) : ℂ) *
      Complex.exp (-Complex.I * (∑ j : Fin 2, x j * y j))
  have hhCont : Continuous h := by
    dsimp [h, y]
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp
        ((continuous_fourthWhiteningRadiusSq k).neg.div_const 2))).mul (by fun_prop)
  have hnorm (x : Fin 2 → ℝ) :
      ‖h x‖ = Real.exp (-(fourthWhiteningRadiusSq k x) / 2) := by
    dsimp [h]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    simp
  have hnormInt : Integrable (fun x ↦ ‖h x‖) := by
    apply (integrable_fourthWhiteningMatrix_gaussian k (1 / 2) (by norm_num)).congr
    filter_upwards [] with x
    rw [hnorm]
    congr 1
    ring
  have hh : Integrable h :=
    (integrable_norm_iff hhCont.aestronglyMeasurable).mp hnormInt
  have hsplit := integral_add_compl measurableSet_fourthDualCell hh
  rw [fourthGaussianFullAtom_fourier]
  unfold fourthGaussianCellAtom
  change ‖(1 / Real.pi ^ 2 : ℂ) * (∫ x in fourthDualCell, h x) -
      (1 / Real.pi ^ 2 : ℂ) * (∫ x, h x)‖ ≤ _
  have heq :
      (1 / Real.pi ^ 2 : ℂ) * (∫ x in fourthDualCell, h x) -
        (1 / Real.pi ^ 2 : ℂ) * (∫ x, h x) =
      -((1 / Real.pi ^ 2 : ℂ) * (∫ x in fourthDualCellᶜ, h x)) := by
    rw [← hsplit]
    ring
  rw [heq, norm_neg, norm_mul]
  calc
    ‖(1 / Real.pi ^ 2 : ℂ)‖ * ‖∫ x in fourthDualCellᶜ, h x‖ ≤
        (1 / Real.pi ^ 2 : ℝ) *
          ∫ x in fourthDualCellᶜ,
            Real.exp (-(fourthWhiteningRadiusSq k x) / 2) := by
      have hc : ‖(1 / Real.pi ^ 2 : ℂ)‖ = (1 / Real.pi ^ 2 : ℝ) := by
        rw [Complex.norm_div, norm_one, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [hc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        ‖∫ x in fourthDualCellᶜ, h x‖ ≤ ∫ x in fourthDualCellᶜ, ‖h x‖ :=
          norm_integral_le_integral_norm _
        _ = ∫ x in fourthDualCellᶜ,
            Real.exp (-(fourthWhiteningRadiusSq k x) / 2) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hnorm x
    _ ≤ (1 / Real.pi ^ 2 : ℝ) *
        (Real.exp (-(1 / 4 : ℝ) * fourthDualGaussianEscapeRadius k) *
          ((Real.sqrt (fourthDet k))⁻¹ * (Real.pi / (1 / 4 : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left (integral_fourthGaussian_compl_dualCell k)
        (by positivity)
    _ = fourthGaussianFourierTailBound k := rfl

/-- Uniform full-plane Gaussian local limit at every point of the affine support lattice. -/
lemma fourthLatticeAtomProbability_sub_gaussianFullAtom
    (N : ℕ) (hN : 21 ≤ N) (d : Fin 2 → ℤ) :
    ‖(fourthLatticeAtomProbability (N + 2) d : ℂ) -
        (fourthGaussianFullAtom (N + 2)
          (fun j ↦ (signedIntLatticeTarget
            (fourthSignedIntegerVector (N + 2)) d j : ℝ)) : ℂ)‖ ≤
      (1 / Real.pi ^ 2 : ℝ) * fourthFourierL1ErrorBound N +
        fourthGaussianFourierTailBound (N + 2) := by
  calc
    ‖(fourthLatticeAtomProbability (N + 2) d : ℂ) -
        (fourthGaussianFullAtom (N + 2)
          (fun j ↦ (signedIntLatticeTarget
            (fourthSignedIntegerVector (N + 2)) d j : ℝ)) : ℂ)‖ ≤
      ‖(fourthLatticeAtomProbability (N + 2) d : ℂ) -
          fourthGaussianCellAtom (N + 2) d‖ +
        ‖fourthGaussianCellAtom (N + 2) d -
          (fourthGaussianFullAtom (N + 2)
            (fun j ↦ (signedIntLatticeTarget
              (fourthSignedIntegerVector (N + 2)) d j : ℝ)) : ℂ)‖ := by
      simpa only [dist_eq_norm] using
        dist_triangle
          (fourthLatticeAtomProbability (N + 2) d : ℂ)
          (fourthGaussianCellAtom (N + 2) d)
          (fourthGaussianFullAtom (N + 2)
            (fun j ↦ (signedIntLatticeTarget
              (fourthSignedIntegerVector (N + 2)) d j : ℝ)) : ℂ)
    _ ≤ (1 / Real.pi ^ 2 : ℝ) * fourthFourierL1ErrorBound N +
        fourthGaussianFourierTailBound (N + 2) :=
      add_le_add (fourthLatticeAtomProbability_sub_gaussianCellAtom N hN d)
        (fourthGaussianCellAtom_sub_fullAtom (N + 2) d)

end Erdos521
