import Research.FourthCentralStrip
import Research.FourthCrossingAsymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

open Filter Topology
open scoped BigOperators

namespace Erdos521

lemma fourthVarianceA_lower_power (k : ℕ) :
    (k + 1 : ℝ) ^ 7 / 252 ≤ fourthVarianceA k := by
  rw [fourthVarianceA_formula]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2520)).2
  norm_num
  rw [← sub_nonneg]
  ring_nf
  positivity

lemma fourthSqrtVarianceA_lower_power (k : ℕ) :
    (k + 1 : ℝ) ^ 3 * Real.sqrt (k + 1 : ℝ) / 16 ≤
      Real.sqrt (fourthVarianceA k) := by
  have hA := fourthVarianceA_lower_power k
  have hx : 0 ≤ (k + 1 : ℝ) := by positivity
  rw [Real.le_sqrt (by positivity) (fourthVarianceA_pos' k).le]
  rw [div_pow, mul_pow, Real.sq_sqrt hx]
  have hscale : (k + 1 : ℝ) ^ 7 / 256 ≤ (k + 1 : ℝ) ^ 7 / 252 := by
    gcongr
    norm_num
  calc
    ((k + 1 : ℝ) ^ 3) ^ 2 * (k + 1 : ℝ) / 16 ^ 2 =
        (k + 1 : ℝ) ^ 7 / 256 := by ring
    _ ≤ (k + 1 : ℝ) ^ 7 / 252 := hscale
    _ ≤ fourthVarianceA k := hA

lemma fourthDet_div_varianceA_le_increment (k : ℕ) :
    fourthDet k / fourthVarianceA k ≤ fourthIncrementVarianceB k := by
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  apply (div_le_iff₀ hA).2
  rw [fourthDet]
  nlinarith [sq_nonneg (fourthIncrementCovarianceC k)]

lemma fourthTransverseScale_le (k : ℕ) :
    Real.sqrt (2 * fourthDet k / fourthVarianceA k) ≤
      7 * (k + 1 : ℝ) ^ 2 * Real.sqrt (k + 1 : ℝ) := by
  let x : ℝ := k + 1
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hratio : 2 * fourthDet k / fourthVarianceA k ≤ 48 * x ^ 5 := by
    have h := fourthDet_div_varianceA_le_increment k
    have hB := fourthIncrementVarianceB_upper_power k
    calc
      2 * fourthDet k / fourthVarianceA k =
          2 * (fourthDet k / fourthVarianceA k) := by ring
      _ ≤ 2 * fourthIncrementVarianceB k := by gcongr
      _ ≤ 48 * x ^ 5 := by dsimp [x]; linarith
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [mul_pow, mul_pow, Real.sq_sqrt hx]
    dsimp [x] at hratio ⊢
    nlinarith [sq_nonneg ((k + 1 : ℝ) ^ 2)]

lemma fourthTransverseInverse_eq_halfScale (k : ℕ) :
    1 / (2 * (fourthVarianceA k / (2 * fourthDet k)) *
      Real.sqrt (2 * fourthDet k / fourthVarianceA k)) =
      Real.sqrt (2 * fourthDet k / fourthVarianceA k) / 2 := by
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hD : 0 < fourthDet k := fourthDet_pos k
  have harg : 0 < 2 * fourthDet k / fourthVarianceA k := by positivity
  have hs : Real.sqrt (2 * fourthDet k / fourthVarianceA k) ≠ 0 :=
    (Real.sqrt_pos.2 harg).ne'
  have hs2 := Real.sq_sqrt harg.le
  field_simp at hs2 ⊢
  nlinarith

/-- A coarse but scale-sharp Gaussian strip bound. -/
lemma fourthGaussianStripMass_le_coarse (k T : ℕ) :
    fourthGaussianStripMass k T ≤
      1000000 * ((2 * T + 1 : ℕ) : ℝ) /
        ((k + 1 : ℝ) ^ 3 * Real.sqrt (k + 1 : ℝ)) := by
  have hmain := fourthGaussianStripMass_le k T
  have hD := fourthSqrtDet_lower_power k
  have hL := fourthTransverseScale_le k
  have hinv := fourthTransverseInverse_eq_halfScale k
  have hx : 1 ≤ (k + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hsx : 1 ≤ Real.sqrt (k + 1 : ℝ) := Real.one_le_sqrt.mpr hx
  have hx3 : 1 ≤ (k + 1 : ℝ) ^ 3 := one_le_pow₀ hx
  have hden : 0 < (k + 1 : ℝ) ^ 3 * Real.sqrt (k + 1 : ℝ) := by positivity
  have hpi : 2 ≤ Real.pi := Real.two_le_pi
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hsD : 0 < Real.sqrt (fourthDet k) := Real.sqrt_pos.2 (fourthDet_pos k)
  have hx6 : 0 < (k + 1 : ℝ) ^ 6 := by positivity
  have hpref : 2 / (Real.pi * Real.sqrt (fourthDet k)) ≤
      2000 / ((k + 1 : ℝ) ^ 6) := by
    have hfirst : 2 / (Real.pi * Real.sqrt (fourthDet k)) ≤
        1 / Real.sqrt (fourthDet k) := by
      rw [show 2 / (Real.pi * Real.sqrt (fourthDet k)) =
        (2 / Real.pi) / Real.sqrt (fourthDet k) by ring]
      apply (div_le_div_iff_of_pos_right hsD).2
      apply (div_le_iff₀ Real.pi_pos).2
      nlinarith
    have hsecond : 1 / Real.sqrt (fourthDet k) ≤
        2000 / ((k + 1 : ℝ) ^ 6) := by
      rw [div_le_div_iff₀ hsD hx6]
      nlinarith
    exact hfirst.trans hsecond
  rw [hinv] at hmain
  calc
    fourthGaussianStripMass k T ≤
      ((2 * T + 1 : ℕ) : ℝ) *
        (2 / (Real.pi * Real.sqrt (fourthDet k))) *
        (Real.exp 1 * 2 *
          (1 + Real.sqrt (2 * fourthDet k / fourthVarianceA k) / 2)) := hmain
    _ ≤ ((2 * T + 1 : ℕ) : ℝ) *
        (2000 / ((k + 1 : ℝ) ^ 6)) *
        (3 * 2 * (1 + (7 * (k + 1 : ℝ) ^ 2 * Real.sqrt (k + 1 : ℝ)) / 2)) := by
      have hinner : Real.exp 1 * 2 *
          (1 + Real.sqrt (2 * fourthDet k / fourthVarianceA k) / 2) ≤
          3 * 2 * (1 + 7 * (k + 1 : ℝ) ^ 2 * Real.sqrt (k + 1 : ℝ) / 2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right he.le (by norm_num))
          (by linarith [hL]) (by positivity) (by positivity)
      calc
        ((2 * T + 1 : ℕ) : ℝ) *
            (2 / (Real.pi * Real.sqrt (fourthDet k))) *
            (Real.exp 1 * 2 *
              (1 + Real.sqrt (2 * fourthDet k / fourthVarianceA k) / 2)) =
          ((2 * T + 1 : ℕ) : ℝ) *
            ((2 / (Real.pi * Real.sqrt (fourthDet k))) *
              (Real.exp 1 * 2 *
                (1 + Real.sqrt (2 * fourthDet k / fourthVarianceA k) / 2))) := by ring
        _ ≤ ((2 * T + 1 : ℕ) : ℝ) *
            ((2000 / ((k + 1 : ℝ) ^ 6)) *
              (3 * 2 * (1 + 7 * (k + 1 : ℝ) ^ 2 *
                Real.sqrt (k + 1 : ℝ) / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hpref hinner (by positivity) (by positivity)
        _ = _ := by ring
    _ ≤ 1000000 * ((2 * T + 1 : ℕ) : ℝ) /
        ((k + 1 : ℝ) ^ 3 * Real.sqrt (k + 1 : ℝ)) := by
      have hs_le : Real.sqrt (k + 1 : ℝ) ≤ (k + 1 : ℝ) ^ 3 := by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · nlinarith [show 1 ≤ (k + 1 : ℝ) ^ 5 from one_le_pow₀ hx]
      have hroot : (k + 1 : ℝ) ^ 3 * Real.sqrt (k + 1 : ℝ) ≤
          (k + 1 : ℝ) ^ 6 := by
        nlinarith [mul_le_mul_of_nonneg_left hs_le (by positivity : 0 ≤ (k + 1 : ℝ) ^ 3)]
      apply (le_div_iff₀ hden).2
      field_simp
      ring_nf
      rw [show (1 + (k : ℝ)) = (k + 1 : ℝ) by ring,
        Real.sq_sqrt (by positivity : 0 ≤ (k + 1 : ℝ))]
      nlinarith

end Erdos521
