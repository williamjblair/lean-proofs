import Research.FourthCovarianceAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace Erdos521

noncomputable def fourthAngleSine (k : ℕ) : ℝ :=
  Real.sqrt ((fourthVarianceA k * fourthIncrementVarianceB k -
      fourthIncrementCovarianceC k ^ 2) /
    (fourthVarianceA k *
      (fourthVarianceA k + 2 * fourthIncrementCovarianceC k +
        fourthIncrementVarianceB k)))

noncomputable def fourthGaussianCrossingKernel (k : ℕ) : ℝ :=
  Real.arcsin (fourthAngleSine k) / Real.pi

lemma fourthVarianceA_pos (k : ℕ) : 0 < fourthVarianceA k := by
  rw [fourthVarianceA_formula]
  positivity

lemma fourthIncrementVarianceB_pos (k : ℕ) : 0 < fourthIncrementVarianceB k := by
  unfold fourthIncrementVarianceB
  positivity

lemma fourthIncrementCovarianceC_nonneg (k : ℕ) : 0 ≤ fourthIncrementCovarianceC k := by
  unfold fourthIncrementCovarianceC
  positivity

lemma fourthAdjacentVariance_pos (k : ℕ) :
    0 < fourthVarianceA k + 2 * fourthIncrementCovarianceC k +
      fourthIncrementVarianceB k := by
  have := fourthVarianceA_pos k
  have := fourthIncrementVarianceB_pos k
  have := fourthIncrementCovarianceC_nonneg k
  positivity

lemma fourthAngleSine_nonneg (k : ℕ) : 0 ≤ fourthAngleSine k :=
  Real.sqrt_nonneg _

lemma fourthAngleSine_sq (k : ℕ) :
    fourthAngleSine k ^ 2 =
      (fourthVarianceA k * fourthIncrementVarianceB k -
          fourthIncrementCovarianceC k ^ 2) /
        (fourthVarianceA k *
          (fourthVarianceA k + 2 * fourthIncrementCovarianceC k +
            fourthIncrementVarianceB k)) := by
  unfold fourthAngleSine
  rw [Real.sq_sqrt]
  exact div_nonneg (fourth_covariance_determinant_pos k).le
    (mul_nonneg (fourthVarianceA_pos k).le (fourthAdjacentVariance_pos k).le)

lemma fourthAngleSine_le (k : ℕ) :
    fourthAngleSine k ≤ (3 : ℝ) / (5 * (k + 1 : ℝ)) := by
  have hden : 0 < fourthVarianceA k *
      (fourthVarianceA k + 2 * fourthIncrementCovarianceC k +
        fourthIncrementVarianceB k) :=
    mul_pos (fourthVarianceA_pos k) (fourthAdjacentVariance_pos k)
  have hangle := fourth_covariance_angle_sq_bound k
  have hsq : fourthAngleSine k ^ 2 ≤ ((3 : ℝ) / (5 * (k + 1 : ℝ))) ^ 2 := by
    rw [fourthAngleSine_sq]
    apply (div_le_iff₀ hden).2
    have hk : (0 : ℝ) < k + 1 := by positivity
    field_simp
    nlinarith
  have hrhs : 0 ≤ (3 : ℝ) / (5 * (k + 1 : ℝ)) := by
    exact div_nonneg (by norm_num) (by positivity)
  exact (sq_le_sq₀ (fourthAngleSine_nonneg k) hrhs).mp hsq

lemma fourthAngleSine_le_one (k : ℕ) : fourthAngleSine k ≤ 1 := by
  calc
    fourthAngleSine k ≤ (3 : ℝ) / (5 * (k + 1 : ℝ)) := fourthAngleSine_le k
    _ ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * (k + 1))).2
      have hk0 : (0 : ℝ) ≤ k := by positivity
      nlinarith

lemma arcsin_le_fiftyone_fiftieths {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 10) :
    Real.arcsin x ≤ (51 : ℝ) / 50 * x := by
  let y := Real.arcsin x
  have hx1 : x ≤ 1 := hx.trans (by norm_num)
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact Real.arcsin_nonneg.mpr hx0
  have hyPi : y ≤ Real.pi / 2 * x := by
    apply (Real.arcsin_le_iff_le_sin ⟨by linarith, hx1⟩ ?_).2
    · exact Real.le_sin_mul hx0 hx1
    · constructor
      · have hnonneg : 0 ≤ Real.pi / 2 * x :=
          mul_nonneg (by positivity) hx0
        linarith [Real.pi_pos]
      · have hnonneg : 0 ≤ Real.pi / 2 := by positivity
        nlinarith
  have hy : y ≤ 1 / 5 := by
    have hp := Real.pi_lt_four
    nlinarith
  have hsiny : Real.sin y = x := by
    dsimp [y]
    exact Real.sin_arcsin (by linarith) hx1
  by_cases hyzero : y = 0
  · have hxzero : x = 0 := by rw [← hsiny, hyzero, Real.sin_zero]
    simp [hxzero]
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyzero)
    have hsin := Real.sin_gt_sub_cube hypos (hy.trans (by norm_num))
    rw [hsiny] at hsin
    have hycube : y ^ 3 / 4 ≤ y / 100 := by
      nlinarith [sq_nonneg y]
    nlinarith

/-- The exact Gaussian angular benchmark is uniformly below `0.204/(k+1)` from `k=5` onward. -/
lemma fourthGaussianCrossingKernel_le (k : ℕ) (hk : 5 ≤ k) :
    fourthGaussianCrossingKernel k ≤ (51 : ℝ) / (250 * (k + 1 : ℝ)) := by
  have hs0 := fourthAngleSine_nonneg k
  have hs := fourthAngleSine_le k
  have hs10 : fourthAngleSine k ≤ (1 : ℝ) / 10 := by
    apply hs.trans
    have hk' : (6 : ℝ) ≤ k + 1 := by exact_mod_cast Nat.add_le_add_right hk 1
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * (k + 1))).2
    nlinarith
  have hasin := arcsin_le_fiftyone_fiftieths hs0 hs10
  have hp := Real.pi_gt_three
  unfold fourthGaussianCrossingKernel
  have hp0 := Real.pi_pos
  apply (div_le_iff₀ hp0).2
  calc
    Real.arcsin (fourthAngleSine k) ≤ (51 : ℝ) / 50 * fourthAngleSine k := hasin
    _ ≤ (51 : ℝ) / 50 * ((3 : ℝ) / (5 * (k + 1 : ℝ))) := by gcongr
    _ ≤ ((51 : ℝ) / (250 * (k + 1 : ℝ))) * Real.pi := by
      have hkpos : (0 : ℝ) < k + 1 := by positivity
      field_simp
      nlinarith

end Erdos521
