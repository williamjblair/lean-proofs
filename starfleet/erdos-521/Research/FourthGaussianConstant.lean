import Research.FourthCrossingAnalyticSplit
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace Erdos521

/-- Exact determinant ratio of the limiting covariance matrix for a fourth-integrated walk and
its one-step increment. -/
lemma fourthGaussian_covariance_ratio :
    (((1 : ℝ) / 252) * ((1 : ℝ) / 20) - ((1 : ℝ) / 72) ^ 2) /
        ((1 : ℝ) / 252) ^ 2 = (7 : ℝ) / 20 := by
  norm_num

lemma sqrt_seven_twentieths_lt : Real.sqrt ((7 : ℝ) / 20) < (74 : ℝ) / 125 := by
  have hnonneg : 0 ≤ (7 : ℝ) / 20 := by norm_num
  have hs := Real.sq_sqrt hnonneg
  have hsqrt := Real.sqrt_nonneg ((7 : ℝ) / 20)
  nlinarith

/-- The predicted two-sided iid logarithmic crossing constant has strict room below the `0.378`
constant in F-047. -/
lemma two_mul_sqrt_seven_twentieths_div_pi_lt :
    2 * Real.sqrt ((7 : ℝ) / 20) / Real.pi < (189 : ℝ) / 500 := by
  have hp := Real.pi_pos
  have hs := sqrt_seven_twentieths_lt
  apply (div_lt_iff₀ hp).2
  have hpi := Real.pi_gt_d20
  calc
    2 * Real.sqrt ((7 : ℝ) / 20) < (148 : ℝ) / 125 := by nlinarith
    _ < (189 : ℝ) / 500 * Real.pi := by
      norm_num at hpi ⊢
      nlinarith

end Erdos521
