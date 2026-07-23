import Research.FourthWhiteningJacobian
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

open scoped BigOperators Matrix
open MeasureTheory

namespace Erdos521

noncomputable def fourthWhiteningRadiusSq (k : ℕ) (x : Fin 2 → ℝ) : ℝ :=
  ((fourthWhiteningMatrix k).mulVec x 0) ^ 2 +
    ((fourthWhiteningMatrix k).mulVec x 1) ^ 2

lemma fourthWhiteningMatrix_inverseT (k : ℕ) (x : Fin 2 → ℝ) :
    fourthWhitenedToOriginalT k ((fourthWhiteningMatrix k).mulVec x 0)
      ((fourthWhiteningMatrix k).mulVec x 1) = x 1 := by
  rw [fourthWhiteningMatrix_mulVec_one]
  unfold fourthWhitenedToOriginalT
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hD : 0 < fourthDet k := fourthDet_pos k
  have hsA : Real.sqrt (fourthVarianceA k) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hsD : Real.sqrt (fourthDet k) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  rw [Real.sqrt_mul hA.le (fourthDet k)]
  field_simp
  rw [Real.sq_sqrt hA.le]
  ring

lemma fourthWhiteningMatrix_inverseS (k : ℕ) (x : Fin 2 → ℝ) :
    fourthWhitenedToOriginalS k ((fourthWhiteningMatrix k).mulVec x 0)
      ((fourthWhiteningMatrix k).mulVec x 1) = x 0 := by
  rw [fourthWhiteningMatrix_mulVec_zero, fourthWhiteningMatrix_mulVec_one]
  unfold fourthWhitenedToOriginalS
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hD : 0 < fourthDet k := fourthDet_pos k
  have hsA : Real.sqrt (fourthVarianceA k) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  have hsD : Real.sqrt (fourthDet k) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  rw [Real.sqrt_mul hA.le (fourthDet k)]
  field_simp
  rw [Real.sq_sqrt hA.le]
  ring

lemma fourthWhitenedProduct_matrix_eq_original (k : ℕ) (x : Fin 2 → ℝ) :
    fourthWhitenedCharacteristicProduct k ((fourthWhiteningMatrix k).mulVec x 0)
      ((fourthWhiteningMatrix k).mulVec x 1) =
        fourthOriginalCharacteristicProduct k (x 0) (x 1) := by
  rw [fourthWhitenedCharacteristicProduct_eq_original,
    fourthWhiteningMatrix_inverseS, fourthWhiteningMatrix_inverseT]

lemma fourthWhiteningRadiusSq_eq_original_sq_sum (k : ℕ) (x : Fin 2 → ℝ) :
    fourthWhiteningRadiusSq k x =
      ∑ i : Option (Fin (k + 1)), fourthOriginalPhase k (x 0) (x 1) i ^ 2 := by
  have h := fourthOriginalPhase_transformed_sq_sum k
    ((fourthWhiteningMatrix k).mulVec x 0) ((fourthWhiteningMatrix k).mulVec x 1)
  rw [fourthWhiteningMatrix_inverseS, fourthWhiteningMatrix_inverseT] at h
  exact h.symm

noncomputable def fourthDualCell : Set (Fin 2 → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Icc (-Real.pi / 2) (Real.pi / 2)

lemma mem_fourthDualCell_iff (x : Fin 2 → ℝ) :
    x ∈ fourthDualCell ↔ |x 0| ≤ Real.pi / 2 ∧ |x 1| ≤ Real.pi / 2 := by
  simp only [fourthDualCell, Set.mem_univ_pi, Set.mem_Icc]
  constructor
  · intro h
    constructor
    · rw [abs_le]
      simpa [neg_div] using h (0 : Fin 2)
    · rw [abs_le]
      simpa [neg_div] using h (1 : Fin 2)
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · simpa [neg_div] using (abs_le.1 h0)
    · simpa [neg_div] using (abs_le.1 h1)

lemma measurableSet_fourthDualCell : MeasurableSet fourthDualCell := by
  exact MeasurableSet.univ_pi (fun _ ↦ measurableSet_Icc)

lemma volume_fourthDualCell : volume fourthDualCell = ENNReal.ofReal (Real.pi ^ 2) := by
  rw [fourthDualCell, volume_pi, Measure.pi_pi, Fin.prod_univ_two]
  simp only [Real.volume_Icc, ENNReal.ofReal_sub]
  have hp : 0 ≤ Real.pi := Real.pi_pos.le
  rw [show Real.pi / 2 - -Real.pi / 2 = Real.pi by ring]
  rw [← pow_two, ← ENNReal.ofReal_pow hp]

/-- The polynomial factor in F-069 can be absorbed by weakening its Gaussian exponent. -/
lemma radial_fourth_power_mul_exp_bound (r2 : ℝ) (hr2 : 0 ≤ r2) :
    r2 ^ 2 * Real.exp (-(1 / Real.pi ^ 2) * r2) ≤
      2048 * Real.exp (-(1 / (2 * Real.pi ^ 2)) * r2) := by
  let y : ℝ := r2 / (2 * Real.pi ^ 2)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hseries := Real.pow_div_factorial_le_exp y hy 2
  norm_num at hseries
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hpi4 : Real.pi ^ 4 ≤ 4 ^ 4 := pow_le_pow_left₀ hpi0 hpi 4
  have hpoly : r2 ^ 2 ≤ 2048 * Real.exp y := by
    have hyid : r2 = 2 * Real.pi ^ 2 * y := by
      dsimp [y]
      field_simp [Real.pi_ne_zero]
    have hc : 8 * Real.pi ^ 4 ≤ 2048 := by nlinarith
    calc
      r2 ^ 2 = (8 * Real.pi ^ 4) * (y ^ 2 / 2) := by rw [hyid]; ring
      _ ≤ (8 * Real.pi ^ 4) * Real.exp y :=
        mul_le_mul_of_nonneg_left hseries (by positivity)
      _ ≤ 2048 * Real.exp y :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos y).le
  have hm := mul_le_mul_of_nonneg_right hpoly
    (Real.exp_pos (-(1 / Real.pi ^ 2) * r2)).le
  calc
    r2 ^ 2 * Real.exp (-(1 / Real.pi ^ 2) * r2) ≤
        (2048 * Real.exp y) * Real.exp (-(1 / Real.pi ^ 2) * r2) := hm
    _ = 2048 * Real.exp (-(1 / (2 * Real.pi ^ 2)) * r2) := by
      rw [show 2048 * Real.exp y * Real.exp (-(1 / Real.pi ^ 2) * r2) =
        2048 * (Real.exp y * Real.exp (-(1 / Real.pi ^ 2) * r2)) by ring,
        ← Real.exp_add]
      congr 1
      dsimp [y]
      field_simp [Real.pi_ne_zero]
      ring

/-- F-069 in the original dual coordinates, with the quartic factor absorbed into a
slightly wider Gaussian. -/
lemma fourthOriginalCharacteristicProduct_central_error
    (k : ℕ) (hk : 23 ≤ k) (x : Fin 2 → ℝ)
    (hcentral : fourthWhiteningRadiusSq k x * (12 / (k + 1 : ℝ)) ≤ 1) :
    |fourthOriginalCharacteristicProduct k (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq k x) / 2)| ≤
      (6144 / (k + 1 : ℝ)) *
        Real.exp (-(1 / (2 * Real.pi ^ 2)) * fourthWhiteningRadiusSq k x) := by
  let u := (fourthWhiteningMatrix k).mulVec x 0
  let v := (fourthWhiteningMatrix k).mulVec x 1
  have ht := fourthCharacteristicProduct_damped_taylor k hk u v (by
    simpa [u, v, fourthWhiteningRadiusSq] using hcentral)
  change |fourthWhitenedCharacteristicProduct k u v -
      Real.exp (-(u ^ 2 + v ^ 2) / 2)| ≤ _ at ht
  have hr : 0 ≤ fourthWhiteningRadiusSq k x := by
    dsimp [fourthWhiteningRadiusSq]
    positivity
  have hp := radial_fourth_power_mul_exp_bound (fourthWhiteningRadiusSq k x) hr
  have hkpos : 0 < (k + 1 : ℝ) := by positivity
  rw [show fourthOriginalCharacteristicProduct k (x 0) (x 1) =
      fourthWhitenedCharacteristicProduct k u v by
        symm
        simpa [u, v] using fourthWhitenedProduct_matrix_eq_original k x]
  change |fourthWhitenedCharacteristicProduct k u v -
      Real.exp (-(fourthWhiteningRadiusSq k x) / 2)| ≤ _
  calc
    _ ≤ ((3 / (k + 1 : ℝ)) * (fourthWhiteningRadiusSq k x) ^ 2) *
        Real.exp (-(1 / Real.pi ^ 2) * fourthWhiteningRadiusSq k x) := by
      simpa [u, v, fourthWhiteningRadiusSq] using ht
    _ = (3 / (k + 1 : ℝ)) *
        ((fourthWhiteningRadiusSq k x) ^ 2 *
          Real.exp (-(1 / Real.pi ^ 2) * fourthWhiteningRadiusSq k x)) := by ring
    _ ≤ (3 / (k + 1 : ℝ)) *
        (2048 * Real.exp (-(1 / (2 * Real.pi ^ 2)) *
          fourthWhiteningRadiusSq k x)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (6144 / (k + 1 : ℝ)) *
        Real.exp (-(1 / (2 * Real.pi ^ 2)) * fourthWhiteningRadiusSq k x) := by ring

lemma integrable_fin_two_gaussian' (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Fin 2 → ℝ ↦ Real.exp (-b * (x 0 ^ 2 + x 1 ^ 2))) := by
  have hprod : Integrable (fun x : Fin 2 → ℝ ↦
      ∏ i : Fin 2, Real.exp (-b * (x i) ^ 2)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (fun _ ↦ integrable_exp_neg_mul_sq hb)
  apply hprod.congr
  filter_upwards [] with x
  rw [Fin.prod_univ_two, ← Real.exp_add]
  congr 1
  ring

lemma integrable_fourthWhiteningMatrix_gaussian (k : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Fin 2 → ℝ ↦
      Real.exp (-b * fourthWhiteningRadiusSq k x)) := by
  let M := fourthWhiteningMatrix k
  let f : (Fin 2 → ℝ) → ℝ := fun y ↦ Real.exp (-b * (y 0 ^ 2 + y 1 ^ 2))
  have hf : Integrable f := integrable_fin_two_gaussian' b hb
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (fourthWhiteningMatrix_det_ne_zero k)
  have hfmap : Integrable f
      (Measure.map (Matrix.toLin' M : (Fin 2 → ℝ) → (Fin 2 → ℝ)) volume) := by
    rw [hmap]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  have hmeas : AEMeasurable (Matrix.toLin' M : (Fin 2 → ℝ) → (Fin 2 → ℝ)) volume :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable.aemeasurable
  have hc := hfmap.comp_aemeasurable hmeas
  simpa [M, f, Matrix.toLin'_apply, fourthWhiteningRadiusSq, Function.comp_def] using hc

noncomputable def fourthCentralRegion (k : ℕ) : Set (Fin 2 → ℝ) :=
  {x | fourthWhiteningRadiusSq k x * (12 / (k + 1 : ℝ)) ≤ 1}

lemma continuous_fourthWhiteningRadiusSq (k : ℕ) :
    Continuous (fourthWhiteningRadiusSq k) := by
  unfold fourthWhiteningRadiusSq
  fun_prop

lemma continuous_fourthOriginalCharacteristicProduct_pi (k : ℕ) :
    Continuous (fun x : Fin 2 → ℝ ↦
      fourthOriginalCharacteristicProduct k (x 0) (x 1)) := by
  unfold fourthOriginalCharacteristicProduct
  apply continuous_finset_prod
  intro i hi
  cases i with
  | none => simp [fourthOriginalPhase]; fun_prop
  | some q => simp [fourthOriginalPhase]; fun_prop

lemma fourthOriginalCharacteristicProduct_abs_le_one (k : ℕ) (s t : ℝ) :
    |fourthOriginalCharacteristicProduct k s t| ≤ 1 := by
  unfold fourthOriginalCharacteristicProduct
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ ↦ abs_nonneg _) (fun i _ ↦ Real.abs_cos_le_one _)

lemma measurableSet_fourthCentralRegion (k : ℕ) : MeasurableSet (fourthCentralRegion k) := by
  unfold fourthCentralRegion
  apply measurableSet_le
  · exact ((continuous_fourthWhiteningRadiusSq k).mul continuous_const).measurable
  · fun_prop

/-- The central part of the Fourier `L¹` error is explicitly `O(1/k)` after whitening. -/
lemma integral_fourthOriginalCharacteristicProduct_central_error
    (k : ℕ) (hk : 23 ≤ k) :
    (∫ x in fourthDualCell ∩ fourthCentralRegion k,
      |fourthOriginalCharacteristicProduct k (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq k x) / 2)|) ≤
      (6144 / (k + 1 : ℝ)) * (Real.sqrt (fourthDet k))⁻¹ *
        (Real.pi / (1 / (2 * Real.pi ^ 2))) := by
  let s : Set (Fin 2 → ℝ) := fourthDualCell ∩ fourthCentralRegion k
  let f : (Fin 2 → ℝ) → ℝ := fun x ↦
    |fourthOriginalCharacteristicProduct k (x 0) (x 1) -
      Real.exp (-(fourthWhiteningRadiusSq k x) / 2)|
  let b : ℝ := 1 / (2 * Real.pi ^ 2)
  let C : ℝ := 6144 / (k + 1 : ℝ)
  let g : (Fin 2 → ℝ) → ℝ := fun x ↦ C * Real.exp (-b * fourthWhiteningRadiusSq k x)
  have hb : 0 < b := by dsimp [b]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : MeasurableSet s :=
    measurableSet_fourthDualCell.inter (measurableSet_fourthCentralRegion k)
  have hgfull : Integrable g :=
    (integrable_fourthWhiteningMatrix_gaussian k b hb).const_mul C
  have hfg : ∀ x ∈ s, f x ≤ g x := by
    intro x hx
    exact fourthOriginalCharacteristicProduct_central_error k hk x hx.2
  have hfmeas : AEStronglyMeasurable f (volume.restrict s) := by
    apply Continuous.aestronglyMeasurable
    dsimp [f]
    apply Continuous.abs
    apply (continuous_fourthOriginalCharacteristicProduct_pi k).sub
    exact Real.continuous_exp.comp
      ((continuous_fourthWhiteningRadiusSq k).neg.div_const 2)
  have hf : IntegrableOn f s volume := by
    apply hgfull.integrableOn.mono' hfmeas
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hfg x hx
  calc
    (∫ x in fourthDualCell ∩ fourthCentralRegion k,
      |fourthOriginalCharacteristicProduct k (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq k x) / 2)|) = ∫ x in s, f x := rfl
    _ ≤ ∫ x in s, g x := setIntegral_mono_on hf hgfull.integrableOn hs hfg
    _ ≤ ∫ x, g x := setIntegral_le_integral hgfull
      (Filter.Eventually.of_forall fun x ↦ mul_nonneg hC (Real.exp_pos _).le)
    _ = C * ((Real.sqrt (fourthDet k))⁻¹ * (Real.pi / b)) := by
      rw [show (∫ x, g x) = C * ∫ x : Fin 2 → ℝ,
          Real.exp (-b * fourthWhiteningRadiusSq k x) by
            exact integral_const_mul C _]
      rw [show (∫ x : Fin 2 → ℝ, Real.exp (-b * fourthWhiteningRadiusSq k x)) =
          (Real.sqrt (fourthDet k))⁻¹ * (Real.pi / b) by
        simpa [fourthWhiteningRadiusSq] using
          integral_fourthWhiteningMatrix_gaussian k b hb]
    _ = (6144 / (k + 1 : ℝ)) * (Real.sqrt (fourthDet k))⁻¹ *
        (Real.pi / (1 / (2 * Real.pi ^ 2))) := by
      dsimp [C, b]
      ring

/-- Outside a radial threshold, one half of a Gaussian exponent can be extracted uniformly. -/
lemma exp_neg_mul_radius_tail {b R r2 : ℝ} (hb : 0 ≤ b) (hR : R ≤ r2) :
    Real.exp (-b * r2) ≤ Real.exp (-(b / 2) * R) * Real.exp (-(b / 2) * r2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma exp_neg_mul_min_le_add (c a b : ℝ) :
    Real.exp (-c * min a b) ≤ Real.exp (-c * a) + Real.exp (-c * b) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [min_eq_right hba]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

noncomputable def fourthMacroscopicDecay (N : ℕ) : ℝ :=
  Real.exp (-(2 / Real.pi ^ 2) * ((N : ℝ) / 100000000000000000000))

noncomputable def fourthGlobalRadialRate : ℝ :=
  2 / (3000000000 * Real.pi ^ 2)

noncomputable def fourthTaylorRadius (N : ℕ) : ℝ :=
  (N + 3 : ℝ) / 12

lemma fourthGlobalRadialRate_pos : 0 < fourthGlobalRadialRate := by
  unfold fourthGlobalRadialRate
  positivity

/-- On the noncentral part of the fundamental dual cell, the characteristic/Gaussian
error is bounded by one macroscopic exponential and two integrable radial tails. -/
lemma fourthOriginalCharacteristicProduct_noncentral_error
    (N : ℕ) (hN : 20 ≤ N) (x : Fin 2 → ℝ)
    (hx : x ∈ fourthDualCell \ fourthCentralRegion (N + 2)) :
    |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2)| ≤
      fourthMacroscopicDecay N +
        Real.exp (-(fourthGlobalRadialRate / 2) * fourthTaylorRadius N) *
          Real.exp (-(fourthGlobalRadialRate / 2) *
            fourthWhiteningRadiusSq (N + 2) x) +
        Real.exp (-(1 / 4 : ℝ) * fourthTaylorRadius N) *
          Real.exp (-(1 / 4 : ℝ) * fourthWhiteningRadiusSq (N + 2) x) := by
  have hcell := (mem_fourthDualCell_iff x).1 hx.1
  have hglobal := fourthOriginalCharacteristicProduct_global_decay N hN
    (x 0) (x 1) hcell.1 hcell.2
  rw [← fourthWhiteningRadiusSq_eq_original_sq_sum] at hglobal
  have hsplit := exp_neg_mul_min_le_add (2 / Real.pi ^ 2)
    ((N : ℝ) / 100000000000000000000)
    (fourthWhiteningRadiusSq (N + 2) x / 3000000000)
  have hprod : |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1)| ≤
      fourthMacroscopicDecay N +
        Real.exp (-fourthGlobalRadialRate * fourthWhiteningRadiusSq (N + 2) x) := by
    apply hglobal.trans
    rw [fourthMacroscopicDecay]
    have hrate : -(2 / Real.pi ^ 2) *
        (fourthWhiteningRadiusSq (N + 2) x / 3000000000) =
        -fourthGlobalRadialRate * fourthWhiteningRadiusSq (N + 2) x := by
      unfold fourthGlobalRadialRate
      field_simp [Real.pi_ne_zero]
    rw [← hrate]
    exact hsplit
  have hden : 0 < (N + 3 : ℝ) := by positivity
  have hnot : ¬ fourthWhiteningRadiusSq (N + 2) x *
      (12 / (N + 2 + 1 : ℝ)) ≤ 1 := by
    simpa [fourthCentralRegion] using hx.2
  have hgt : 1 < fourthWhiteningRadiusSq (N + 2) x *
      (12 / (N + 2 + 1 : ℝ)) := lt_of_not_ge hnot
  have hgt' : (N + 3 : ℝ) < fourthWhiteningRadiusSq (N + 2) x * 12 := by
    have hrewrite : (N + 2 + 1 : ℝ) = (N + 3 : ℝ) := by push_cast; ring
    rw [hrewrite] at hgt
    have : 1 < (fourthWhiteningRadiusSq (N + 2) x * 12) / (N + 3 : ℝ) := by
      convert hgt using 1 <;> ring
    simpa using (lt_div_iff₀ hden).1 this
  have hR : fourthTaylorRadius N ≤ fourthWhiteningRadiusSq (N + 2) x := by
    unfold fourthTaylorRadius
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12)).2
    exact hgt'.le
  have htail1 := exp_neg_mul_radius_tail fourthGlobalRadialRate_pos.le hR
  have htail2 := exp_neg_mul_radius_tail (b := (1 / 2 : ℝ)) (by norm_num) hR
  calc
    |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2)| ≤
      |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1)| +
        |Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2)| := abs_sub _ _
    _ = |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1)| +
        Real.exp (-(1 / 2 : ℝ) * fourthWhiteningRadiusSq (N + 2) x) := by
      rw [abs_of_pos (Real.exp_pos _)]
      congr 2
      ring
    _ ≤ fourthMacroscopicDecay N +
        Real.exp (-fourthGlobalRadialRate * fourthWhiteningRadiusSq (N + 2) x) +
        Real.exp (-(1 / 2 : ℝ) * fourthWhiteningRadiusSq (N + 2) x) :=
      add_le_add hprod le_rfl
    _ ≤ fourthMacroscopicDecay N +
        (Real.exp (-(fourthGlobalRadialRate / 2) * fourthTaylorRadius N) *
          Real.exp (-(fourthGlobalRadialRate / 2) *
            fourthWhiteningRadiusSq (N + 2) x)) +
        (Real.exp (-((1 / 2 : ℝ) / 2) * fourthTaylorRadius N) *
          Real.exp (-((1 / 2 : ℝ) / 2) *
            fourthWhiteningRadiusSq (N + 2) x)) :=
      add_le_add (add_le_add le_rfl htail1) htail2
    _ = _ := by ring_nf

/-- The full noncentral Fourier `L¹` error has an explicit exponentially small bound. -/
lemma integral_fourthOriginalCharacteristicProduct_noncentral_error
    (N : ℕ) (hN : 20 ≤ N) :
    (∫ x in fourthDualCell \ fourthCentralRegion (N + 2),
      |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2)|) ≤
      Real.pi ^ 2 * fourthMacroscopicDecay N +
        Real.exp (-(fourthGlobalRadialRate / 2) * fourthTaylorRadius N) *
          ((Real.sqrt (fourthDet (N + 2)))⁻¹ *
            (Real.pi / (fourthGlobalRadialRate / 2))) +
        Real.exp (-(1 / 4 : ℝ) * fourthTaylorRadius N) *
          ((Real.sqrt (fourthDet (N + 2)))⁻¹ *
            (Real.pi / (1 / 4 : ℝ))) := by
  let s : Set (Fin 2 → ℝ) := fourthDualCell \ fourthCentralRegion (N + 2)
  let f : (Fin 2 → ℝ) → ℝ := fun x ↦
    |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1) -
      Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2)|
  let E₀ : ℝ := fourthMacroscopicDecay N
  let E₁ : ℝ := Real.exp (-(fourthGlobalRadialRate / 2) * fourthTaylorRadius N)
  let E₂ : ℝ := Real.exp (-(1 / 4 : ℝ) * fourthTaylorRadius N)
  let b₁ : ℝ := fourthGlobalRadialRate / 2
  let b₂ : ℝ := 1 / 4
  let g₀ : (Fin 2 → ℝ) → ℝ := fun _ ↦ E₀
  let g₁ : (Fin 2 → ℝ) → ℝ := fun x ↦
    E₁ * Real.exp (-b₁ * fourthWhiteningRadiusSq (N + 2) x)
  let g₂ : (Fin 2 → ℝ) → ℝ := fun x ↦
    E₂ * Real.exp (-b₂ * fourthWhiteningRadiusSq (N + 2) x)
  let g : (Fin 2 → ℝ) → ℝ := fun x ↦ g₀ x + g₁ x + g₂ x
  have hs : MeasurableSet s :=
    measurableSet_fourthDualCell.diff (measurableSet_fourthCentralRegion (N + 2))
  have hsubset : s ⊆ fourthDualCell := Set.diff_subset
  have hvolcell : volume fourthDualCell ≠ ⊤ := by
    rw [volume_fourthDualCell]
    exact ENNReal.ofReal_ne_top
  have hvols : volume s ≠ ⊤ := by
    exact ne_of_lt ((measure_mono hsubset).trans_lt (lt_top_iff_ne_top.2 hvolcell))
  have hb₁ : 0 < b₁ := by dsimp [b₁]; exact half_pos fourthGlobalRadialRate_pos
  have hb₂ : 0 < b₂ := by norm_num [b₂]
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; exact (Real.exp_pos _).le
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; exact (Real.exp_pos _).le
  have hE₂ : 0 ≤ E₂ := by dsimp [E₂]; exact (Real.exp_pos _).le
  have hg₀ : IntegrableOn g₀ s volume := integrableOn_const hvols
  have hg₀cell : IntegrableOn g₀ fourthDualCell volume := integrableOn_const hvolcell
  have hg₁full : Integrable g₁ :=
    (integrable_fourthWhiteningMatrix_gaussian (N + 2) b₁ hb₁).const_mul E₁
  have hg₂full : Integrable g₂ :=
    (integrable_fourthWhiteningMatrix_gaussian (N + 2) b₂ hb₂).const_mul E₂
  have hg₁ : IntegrableOn g₁ s volume := hg₁full.integrableOn
  have hg₂ : IntegrableOn g₂ s volume := hg₂full.integrableOn
  have hg : IntegrableOn g s volume := (hg₀.add hg₁).add hg₂
  have hfg : ∀ x ∈ s, f x ≤ g x := by
    intro x hx
    simpa [f, g, g₀, g₁, g₂, E₀, E₁, E₂, b₁, b₂] using
      fourthOriginalCharacteristicProduct_noncentral_error N hN x hx
  have hfmeas : AEStronglyMeasurable f (volume.restrict s) := by
    apply Continuous.aestronglyMeasurable
    dsimp [f]
    apply Continuous.abs
    apply (continuous_fourthOriginalCharacteristicProduct_pi (N + 2)).sub
    exact Real.continuous_exp.comp
      ((continuous_fourthWhiteningRadiusSq (N + 2)).neg.div_const 2)
  have hf : IntegrableOn f s volume := by
    apply hg.mono' hfmeas
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hfg x hx
  have hmain : (∫ x in s, f x) ≤ ∫ x in s, g x :=
    setIntegral_mono_on hf hg hs hfg
  have hsplit : (∫ x in s, g x) =
      (∫ x in s, g₀ x) + (∫ x in s, g₁ x) + (∫ x in s, g₂ x) := by
    dsimp only [g]
    calc
      (∫ x in s, g₀ x + g₁ x + g₂ x) =
          (∫ x in s, g₀ x + g₁ x) + ∫ x in s, g₂ x :=
        integral_add (hg₀.add hg₁) hg₂
      _ = (∫ x in s, g₀ x) + (∫ x in s, g₁ x) + (∫ x in s, g₂ x) := by
        rw [integral_add hg₀ hg₁]
  have hg₀bound : (∫ x in s, g₀ x) ≤ Real.pi ^ 2 * E₀ := by
    calc
      (∫ x in s, g₀ x) ≤ ∫ x in fourthDualCell, g₀ x :=
        setIntegral_mono_set hg₀cell
          (Filter.Eventually.of_forall fun x ↦ hE₀)
          (Filter.Eventually.of_forall fun x hx ↦ hsubset hx)
      _ = Real.pi ^ 2 * E₀ := by
        rw [show (∫ x in fourthDualCell, g₀ x) =
            ∫ _x : Fin 2 → ℝ in fourthDualCell, E₀ by rfl,
          setIntegral_const]
        change (volume fourthDualCell).toReal * E₀ = Real.pi ^ 2 * E₀
        rw [volume_fourthDualCell, ENNReal.toReal_ofReal (sq_nonneg Real.pi)]
  have hg₁bound : (∫ x in s, g₁ x) ≤
      E₁ * ((Real.sqrt (fourthDet (N + 2)))⁻¹ * (Real.pi / b₁)) := by
    calc
      (∫ x in s, g₁ x) ≤ ∫ x, g₁ x := setIntegral_le_integral hg₁full
        (Filter.Eventually.of_forall fun x ↦ mul_nonneg hE₁ (Real.exp_pos _).le)
      _ = E₁ * ((Real.sqrt (fourthDet (N + 2)))⁻¹ * (Real.pi / b₁)) := by
        rw [show (∫ x, g₁ x) = E₁ * ∫ x : Fin 2 → ℝ,
            Real.exp (-b₁ * fourthWhiteningRadiusSq (N + 2) x) by
              exact integral_const_mul E₁ _]
        rw [show (∫ x : Fin 2 → ℝ,
            Real.exp (-b₁ * fourthWhiteningRadiusSq (N + 2) x)) =
            (Real.sqrt (fourthDet (N + 2)))⁻¹ * (Real.pi / b₁) by
          simpa [fourthWhiteningRadiusSq] using
            integral_fourthWhiteningMatrix_gaussian (N + 2) b₁ hb₁]
  have hg₂bound : (∫ x in s, g₂ x) ≤
      E₂ * ((Real.sqrt (fourthDet (N + 2)))⁻¹ * (Real.pi / b₂)) := by
    calc
      (∫ x in s, g₂ x) ≤ ∫ x, g₂ x := setIntegral_le_integral hg₂full
        (Filter.Eventually.of_forall fun x ↦ mul_nonneg hE₂ (Real.exp_pos _).le)
      _ = E₂ * ((Real.sqrt (fourthDet (N + 2)))⁻¹ * (Real.pi / b₂)) := by
        rw [show (∫ x, g₂ x) = E₂ * ∫ x : Fin 2 → ℝ,
            Real.exp (-b₂ * fourthWhiteningRadiusSq (N + 2) x) by
              exact integral_const_mul E₂ _]
        rw [show (∫ x : Fin 2 → ℝ,
            Real.exp (-b₂ * fourthWhiteningRadiusSq (N + 2) x)) =
            (Real.sqrt (fourthDet (N + 2)))⁻¹ * (Real.pi / b₂) by
          simpa [fourthWhiteningRadiusSq] using
            integral_fourthWhiteningMatrix_gaussian (N + 2) b₂ hb₂]
  rw [hsplit] at hmain
  calc
    (∫ x in fourthDualCell \ fourthCentralRegion (N + 2),
      |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2)|) =
        ∫ x in s, f x := rfl
    _ ≤ (∫ x in s, g₀ x) + (∫ x in s, g₁ x) + (∫ x in s, g₂ x) := hmain
    _ ≤ Real.pi ^ 2 * E₀ +
        E₁ * ((Real.sqrt (fourthDet (N + 2)))⁻¹ * (Real.pi / b₁)) +
        E₂ * ((Real.sqrt (fourthDet (N + 2)))⁻¹ * (Real.pi / b₂)) :=
      add_le_add (add_le_add hg₀bound hg₁bound) hg₂bound
    _ = _ := by rfl

lemma integrableOn_fourthOriginalCharacteristicProduct_error_cell (k : ℕ) :
    IntegrableOn (fun x : Fin 2 → ℝ ↦
      |fourthOriginalCharacteristicProduct k (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq k x) / 2)|) fourthDualCell volume := by
  have hvolcell : volume fourthDualCell ≠ ⊤ := by
    rw [volume_fourthDualCell]
    exact ENNReal.ofReal_ne_top
  have hconst : IntegrableOn (fun _x : Fin 2 → ℝ ↦ (2 : ℝ)) fourthDualCell volume :=
    integrableOn_const hvolcell
  have hmeas : AEStronglyMeasurable (fun x : Fin 2 → ℝ ↦
      |fourthOriginalCharacteristicProduct k (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq k x) / 2)|)
      (volume.restrict fourthDualCell) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.abs
    apply (continuous_fourthOriginalCharacteristicProduct_pi k).sub
    exact Real.continuous_exp.comp ((continuous_fourthWhiteningRadiusSq k).neg.div_const 2)
  apply hconst.mono' hmeas
  filter_upwards [] with x
  have hp := fourthOriginalCharacteristicProduct_abs_le_one k (x 0) (x 1)
  have hr : 0 ≤ fourthWhiteningRadiusSq k x := by
    unfold fourthWhiteningRadiusSq
    positivity
  have he : Real.exp (-(fourthWhiteningRadiusSq k x) / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    linarith
  calc
    ‖|fourthOriginalCharacteristicProduct k (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq k x) / 2)|‖ =
      |fourthOriginalCharacteristicProduct k (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq k x) / 2)| :=
      Real.norm_of_nonneg (abs_nonneg _)
    _ ≤
      |fourthOriginalCharacteristicProduct k (x 0) (x 1)| +
        |Real.exp (-(fourthWhiteningRadiusSq k x) / 2)| := abs_sub _ _
    _ = |fourthOriginalCharacteristicProduct k (x 0) (x 1)| +
        Real.exp (-(fourthWhiteningRadiusSq k x) / 2) := by
      rw [abs_of_pos (Real.exp_pos _)]
    _ ≤ 2 := by linarith

/-- Quantitative `L¹` local-CLT control on the full fundamental dual cell. -/
lemma integral_fourthOriginalCharacteristicProduct_full_error
    (N : ℕ) (hN : 21 ≤ N) :
    (∫ x in fourthDualCell,
      |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1) -
        Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2)|) ≤
      (6144 / (N + 2 + 1 : ℝ)) * (Real.sqrt (fourthDet (N + 2)))⁻¹ *
        (Real.pi / (1 / (2 * Real.pi ^ 2))) +
      (Real.pi ^ 2 * fourthMacroscopicDecay N +
        Real.exp (-(fourthGlobalRadialRate / 2) * fourthTaylorRadius N) *
          ((Real.sqrt (fourthDet (N + 2)))⁻¹ *
            (Real.pi / (fourthGlobalRadialRate / 2))) +
        Real.exp (-(1 / 4 : ℝ) * fourthTaylorRadius N) *
          ((Real.sqrt (fourthDet (N + 2)))⁻¹ *
            (Real.pi / (1 / 4 : ℝ)))) := by
  let f : (Fin 2 → ℝ) → ℝ := fun x ↦
    |fourthOriginalCharacteristicProduct (N + 2) (x 0) (x 1) -
      Real.exp (-(fourthWhiteningRadiusSq (N + 2) x) / 2)|
  let c := fourthDualCell ∩ fourthCentralRegion (N + 2)
  let r := fourthDualCell \ fourthCentralRegion (N + 2)
  have hfcell : IntegrableOn f fourthDualCell volume :=
    integrableOn_fourthOriginalCharacteristicProduct_error_cell (N + 2)
  have hfc : IntegrableOn f c volume := hfcell.mono_set Set.inter_subset_left
  have hfr : IntegrableOn f r volume := hfcell.mono_set Set.diff_subset
  have hrmeas : MeasurableSet r :=
    measurableSet_fourthDualCell.diff (measurableSet_fourthCentralRegion (N + 2))
  have hdisj : Disjoint c r := by
    rw [Set.disjoint_left]
    rintro x ⟨hxcell, hxcentral⟩ ⟨_hxcell, hxnotcentral⟩
    exact hxnotcentral hxcentral
  have hsplit := setIntegral_union hdisj hrmeas hfc hfr
  have hunion : c ∪ r = fourthDualCell := Set.inter_union_diff _ _
  rw [hunion] at hsplit
  have hcentral := integral_fourthOriginalCharacteristicProduct_central_error
    (N + 2) (by omega : 23 ≤ N + 2)
  have hnoncentral := integral_fourthOriginalCharacteristicProduct_noncentral_error N
    (by omega : 20 ≤ N)
  have hcentral' : (∫ x in c, f x) ≤
      (6144 / (N + 2 + 1 : ℝ)) * (Real.sqrt (fourthDet (N + 2)))⁻¹ *
        (Real.pi / (1 / (2 * Real.pi ^ 2))) := by
    simpa [c, f, Nat.cast_add, Nat.cast_ofNat] using hcentral
  have hnoncentral' : (∫ x in r, f x) ≤
      Real.pi ^ 2 * fourthMacroscopicDecay N +
        Real.exp (-(fourthGlobalRadialRate / 2) * fourthTaylorRadius N) *
          ((Real.sqrt (fourthDet (N + 2)))⁻¹ *
            (Real.pi / (fourthGlobalRadialRate / 2))) +
        Real.exp (-(1 / 4 : ℝ) * fourthTaylorRadius N) *
          ((Real.sqrt (fourthDet (N + 2)))⁻¹ *
            (Real.pi / (1 / 4 : ℝ))) := by
    simpa [r, f] using hnoncentral
  change (∫ x in fourthDualCell, f x) ≤ _
  rw [hsplit]
  exact add_le_add hcentral' hnoncentral'

end Erdos521
