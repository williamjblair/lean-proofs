import Research.FourthCrossingAsymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Erdos521

/-- The normalized Gaussian term in the lattice crossing estimate is eventually below `0.1915`.
This retains the same finite covariance bound as F-089 but uses convergence of the exponential
correction to one and the certified decimal lower bound on `π`. -/
lemma eventually_fourthGaussianLeading_normalized_sharp :
    ∀ᶠ N : ℕ in atTop,
      (N + 3 : ℝ) *
        (Real.exp (fourthIncrementGaussianRate (N + 2)) *
          (Real.sqrt (fourthDet (N + 2)) /
            (Real.pi * fourthVarianceA (N + 2)))) ≤ (383 : ℝ) / 2000 := by
  have hexp_tendsto : Tendsto
      (fun N : ℕ ↦ Real.exp (fourthIncrementGaussianRate (N + 2)))
      atTop (𝓝 1) := by
    change Tendsto (Real.exp ∘
      (fun N : ℕ ↦ fourthIncrementGaussianRate (N + 2))) atTop (𝓝 1)
    exact Real.tendsto_exp_nhds_zero_nhds_one.comp
      tendsto_fourthIncrementGaussianRate_zero
  have hexp : ∀ᶠ N : ℕ in atTop,
      Real.exp (fourthIncrementGaussianRate (N + 2)) < (1001 : ℝ) / 1000 :=
    hexp_tendsto.eventually_lt_const (by norm_num)
  filter_upwards [hexp, eventually_ge_atTop (102 : ℕ)] with N hexpN hN
  have hratio0 := fourth_sqrtDet_div_varianceA_le (N + 2) (by omega)
  have hratio : Real.sqrt (fourthDet (N + 2)) / fourthVarianceA (N + 2) ≤
      (3 : ℝ) / (5 * (N + 3 : ℝ)) := by
    convert hratio0 using 1 <;> push_cast <;> ring
  have hx : 0 < (N + 3 : ℝ) := by positivity
  have hkernel : (N + 3 : ℝ) *
      (Real.sqrt (fourthDet (N + 2)) /
        (Real.pi * fourthVarianceA (N + 2))) ≤
      (3 : ℝ) / (5 * Real.pi) := by
    calc
      (N + 3 : ℝ) * (Real.sqrt (fourthDet (N + 2)) /
          (Real.pi * fourthVarianceA (N + 2))) =
        ((N + 3 : ℝ) / Real.pi) *
          (Real.sqrt (fourthDet (N + 2)) / fourthVarianceA (N + 2)) := by
            field_simp
      _ ≤ ((N + 3 : ℝ) / Real.pi) * (3 / (5 * (N + 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (3 : ℝ) / (5 * Real.pi) := by field_simp
  have hkernel_nonneg : 0 ≤ (N + 3 : ℝ) *
      (Real.sqrt (fourthDet (N + 2)) /
        (Real.pi * fourthVarianceA (N + 2))) := by
    have hA : 0 < fourthVarianceA (N + 2) := fourthVarianceA_pos' _
    positivity
  have hnumeric : (1001 : ℝ) / 1000 * (3 / (5 * Real.pi)) ≤ 383 / 2000 := by
    rw [show (1001 : ℝ) / 1000 * (3 / (5 * Real.pi)) =
        ((3003 : ℝ) / 1000) / (5 * Real.pi) by ring]
    apply (div_le_iff₀ (show (0 : ℝ) < 5 * Real.pi by positivity)).2
    have hpi := Real.pi_gt_d2
    norm_num at hpi ⊢
    nlinarith
  calc
    (N + 3 : ℝ) *
        (Real.exp (fourthIncrementGaussianRate (N + 2)) *
          (Real.sqrt (fourthDet (N + 2)) /
            (Real.pi * fourthVarianceA (N + 2)))) =
      Real.exp (fourthIncrementGaussianRate (N + 2)) *
        ((N + 3 : ℝ) * (Real.sqrt (fourthDet (N + 2)) /
          (Real.pi * fourthVarianceA (N + 2)))) := by ring
    _ ≤ (1001 / 1000 : ℝ) *
        ((N + 3 : ℝ) * (Real.sqrt (fourthDet (N + 2)) /
          (Real.pi * fourthVarianceA (N + 2)))) :=
      mul_le_mul_of_nonneg_right hexpN.le hkernel_nonneg
    _ ≤ (1001 / 1000 : ℝ) * (3 / (5 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hkernel (by norm_num)
    _ ≤ (383 : ℝ) / 2000 := hnumeric

/-- Sharpened iid fourth-crossing estimate: the normalized one-sided crossing probability is
ultimately at most `0.192`, close to its Gaussian limit `≈0.188315`. -/
lemma eventually_fourthSignedCrossing_rate_sharp :
    ∀ᶠ N : ℕ in atTop,
      fourthSignedCrossingProbability (N + 2) ≤
        (24 : ℝ) / (125 * (N + 3 : ℝ)) := by
  have hrem : ∀ᶠ N : ℕ in atTop,
      (N + 3 : ℝ) *
        (8 * (fourthIncrementL1 (N + 2) + 1 : ℝ) /
          (Real.pi * Real.sqrt (fourthDet (N + 2))) +
        (((2 * fourthCrossingCutoff N + 1 : ℕ) : ℝ) ^ 2 *
          fourthFullAtomError N) +
        2 * Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2)))) < (1 : ℝ) / 2000 :=
    tendsto_fourthNormalizedRemainder_zero.eventually_lt_const (by norm_num)
  filter_upwards [eventually_fourthGaussianLeading_normalized_sharp, hrem,
    eventually_ge_atTop (21 : ℕ)] with N hlead hremN hN
  have hmaster := fourthSignedCrossingProbability_le_explicit N
    (fourthCrossingCutoff N) hN
  have hx : 0 < (N + 3 : ℝ) := by positivity
  have hnorm : (N + 3 : ℝ) * fourthSignedCrossingProbability (N + 2) ≤
      (24 : ℝ) / 125 := by
    calc
      (N + 3 : ℝ) * fourthSignedCrossingProbability (N + 2) ≤
        (N + 3 : ℝ) *
          (Real.exp (fourthIncrementGaussianRate (N + 2)) *
              (Real.sqrt (fourthDet (N + 2)) /
                (Real.pi * fourthVarianceA (N + 2))) +
            (8 * (fourthIncrementL1 (N + 2) + 1 : ℝ) /
              (Real.pi * Real.sqrt (fourthDet (N + 2))) +
            (((2 * fourthCrossingCutoff N + 1 : ℕ) : ℝ) ^ 2 *
              fourthFullAtomError N) +
            2 * Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
              (2 * fourthIncrementVarianceB (N + 2))))) := by
        gcongr
        linarith
      _ = (N + 3 : ℝ) *
          (Real.exp (fourthIncrementGaussianRate (N + 2)) *
            (Real.sqrt (fourthDet (N + 2)) /
              (Real.pi * fourthVarianceA (N + 2)))) +
          (N + 3 : ℝ) *
            (8 * (fourthIncrementL1 (N + 2) + 1 : ℝ) /
              (Real.pi * Real.sqrt (fourthDet (N + 2))) +
            (((2 * fourthCrossingCutoff N + 1 : ℕ) : ℝ) ^ 2 *
              fourthFullAtomError N) +
            2 * Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
              (2 * fourthIncrementVarianceB (N + 2)))) := by ring
      _ ≤ (24 : ℝ) / 125 := by nlinarith
  apply (le_div_iff₀ (mul_pos (by norm_num) hx)).2
  nlinarith

end Erdos521
