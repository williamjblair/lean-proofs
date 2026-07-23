import Research.FourthCrossingLocalLimitBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

open Filter Topology
open scoped BigOperators

namespace Erdos521

lemma fourthDet_lower_power (k : ℕ) :
    (k + 1 : ℝ) ^ 12 / 4000000 ≤ fourthDet k := by
  rw [fourthDet, fourth_covariance_determinant_formula, ← sub_nonneg]
  ring_nf
  positivity

lemma fourthSqrtDet_lower_power (k : ℕ) :
    (k + 1 : ℝ) ^ 6 / 2000 ≤ Real.sqrt (fourthDet k) := by
  have hD := fourthDet_lower_power k
  rw [Real.le_sqrt (by positivity) (fourthDet_pos k).le]
  convert hD using 1 <;> ring

lemma fourthVarianceA_upper_power (k : ℕ) :
    fourthVarianceA k ≤ 100 * (k + 1 : ℝ) ^ 7 := by
  rw [fourthVarianceA_formula, ← sub_nonneg]
  ring_nf
  positivity

lemma fourthIncrementVarianceB_upper_power (k : ℕ) :
    fourthIncrementVarianceB k ≤ 24 * (k + 1 : ℝ) ^ 5 := by
  rw [fourthIncrementVarianceB_formula, ← sub_nonneg]
  ring_nf
  positivity

lemma fourthVariance_sum_upper_power (k : ℕ) :
    fourthVarianceA k + fourthIncrementVarianceB k ≤
      124 * (k + 1 : ℝ) ^ 7 := by
  have hA := fourthVarianceA_upper_power k
  have hB := fourthIncrementVarianceB_upper_power k
  have hp : (k + 1 : ℝ) ^ 5 ≤ (k + 1 : ℝ) ^ 7 := by
    apply pow_le_pow_right₀
    · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    · omega
  nlinarith

lemma fourthIncrementL1_eq_choose (k : ℕ) :
    fourthIncrementL1 k = Nat.choose (k + 4) 3 := by
  induction k with
  | zero => norm_num [fourthIncrementL1]
  | succ k ih =>
      unfold fourthIncrementL1 at ih ⊢
      rw [Finset.sum_range_succ]
      have hp : Nat.choose (k + 1 + 4) 3 =
          Nat.choose (k + 4) 2 + Nat.choose (k + 4) 3 := by
        rw [show k + 1 + 4 = (k + 4) + 1 by omega, Nat.choose_succ_succ']
      rw [show k + 1 + 3 = k + 4 by omega, hp]
      omega

lemma fourthIncrementL1_upper_power (k : ℕ) :
    (fourthIncrementL1 k : ℝ) ≤ (k + 4 : ℝ) ^ 3 := by
  rw [fourthIncrementL1_eq_choose]
  exact_mod_cast Nat.choose_le_pow (k + 4) 3

noncomputable def fourthCrossingCutoff (N : ℕ) : ℕ :=
  Nat.ceil ((N + 3 : ℝ) ^ ((8 : ℝ) / 3))

lemma fourthCrossingCutoff_lower (N : ℕ) :
    (N + 3 : ℝ) ^ ((8 : ℝ) / 3) ≤ (fourthCrossingCutoff N : ℝ) := by
  exact Nat.le_ceil _

lemma fourthCrossingCutoff_upper (N : ℕ) :
    (fourthCrossingCutoff N : ℝ) ≤
      2 * (N + 3 : ℝ) ^ ((8 : ℝ) / 3) := by
  have hx0 : 0 ≤ (N + 3 : ℝ) ^ ((8 : ℝ) / 3) :=
    Real.rpow_nonneg (by positivity) _
  have hc := Nat.ceil_lt_add_one hx0
  have hx1 : (1 : ℝ) ≤ N + 3 := by
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hone : 1 ≤ (N + 3 : ℝ) ^ ((8 : ℝ) / 3) :=
    Real.one_le_rpow hx1 (by norm_num)
  exact le_trans hc.le (by linarith)

lemma fourthCrossingCutoff_sq_lower (N : ℕ) :
    (N + 3 : ℝ) ^ ((16 : ℝ) / 3) ≤ (fourthCrossingCutoff N : ℝ) ^ 2 := by
  have h := fourthCrossingCutoff_lower N
  calc
    _ = ((N + 3 : ℝ) ^ ((8 : ℝ) / 3)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) h 2

lemma fourthCrossingCutoff_sq_upper (N : ℕ) :
    (fourthCrossingCutoff N : ℝ) ^ 2 ≤
      4 * (N + 3 : ℝ) ^ ((16 : ℝ) / 3) := by
  have h := fourthCrossingCutoff_upper N
  calc
    _ ≤ (2 * (N + 3 : ℝ) ^ ((8 : ℝ) / 3)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h 2
    _ = _ := by
      rw [mul_pow]
      norm_num
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num

lemma tendsto_fourthScale_atTop :
    Tendsto (fun N : ℕ ↦ (N + 3 : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

lemma tendsto_fourthScale_rpow_exp (s c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ ↦
      (N + 3 : ℝ) ^ s * Real.exp (-c * (N + 3 : ℝ))) atTop (𝓝 0) :=
  (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s c hc).comp
    tendsto_fourthScale_atTop

lemma fourthInvSqrtDet_upper (N : ℕ) :
    (Real.sqrt (fourthDet (N + 2)))⁻¹ ≤
      2000 * ((N + 3 : ℝ) ^ 6)⁻¹ := by
  have hs0 := fourthSqrtDet_lower_power (N + 2)
  have hs : (N + 3 : ℝ) ^ 6 / 2000 ≤ Real.sqrt (fourthDet (N + 2)) := by
    convert hs0 using 1 <;> push_cast <;> ring
  have hlo : 0 < (N + 3 : ℝ) ^ 6 / 2000 := by positivity
  have hhi : 0 < Real.sqrt (fourthDet (N + 2)) :=
    Real.sqrt_pos.2 (fourthDet_pos _)
  calc
    (Real.sqrt (fourthDet (N + 2)))⁻¹ ≤
        ((N + 3 : ℝ) ^ 6 / 2000)⁻¹ := (inv_le_inv₀ hhi hlo).2 hs
    _ = 2000 * ((N + 3 : ℝ) ^ 6)⁻¹ := by
      field_simp

lemma tendsto_fourthInvSqrtDet_zero :
    Tendsto (fun N : ℕ ↦ (Real.sqrt (fourthDet (N + 2)))⁻¹)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    exact fourthInvSqrtDet_upper N
  · have hp : Tendsto (fun N : ℕ ↦ (N + 3 : ℝ) ^ 6) atTop atTop := by
      have hr := (tendsto_rpow_atTop (show (0 : ℝ) < 6 by norm_num)).comp
        tendsto_fourthScale_atTop
      apply hr.congr
      intro N
      simp [Function.comp_apply, Real.rpow_natCast]
    simpa using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hp)

lemma fourthCutoffSq_div_sqrtDet_upper (N : ℕ) :
    (fourthCrossingCutoff N : ℝ) ^ 2 /
        Real.sqrt (fourthDet (N + 2)) ≤
      8000 * (N + 3 : ℝ) ^ (-((2 : ℝ) / 3)) := by
  have hs := fourthCrossingCutoff_sq_upper N
  have hi := fourthInvSqrtDet_upper N
  have hsqrt : 0 < Real.sqrt (fourthDet (N + 2)) :=
    Real.sqrt_pos.2 (fourthDet_pos _)
  calc
    (fourthCrossingCutoff N : ℝ) ^ 2 /
        Real.sqrt (fourthDet (N + 2)) ≤
      (4 * (N + 3 : ℝ) ^ ((16 : ℝ) / 3)) /
        Real.sqrt (fourthDet (N + 2)) :=
      div_le_div_of_nonneg_right hs hsqrt.le
    _ ≤ (4 * (N + 3 : ℝ) ^ ((16 : ℝ) / 3)) *
        (2000 * ((N + 3 : ℝ) ^ 6)⁻¹) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 8000 * (N + 3 : ℝ) ^ (-((2 : ℝ) / 3)) := by
      have hx : 0 < (N + 3 : ℝ) := by positivity
      rw [← Real.rpow_natCast]
      calc
        4 * (N + 3 : ℝ) ^ ((16 : ℝ) / 3) *
            (2000 * ((N + 3 : ℝ) ^ (6 : ℝ))⁻¹) =
            8000 * ((N + 3 : ℝ) ^ ((16 : ℝ) / 3) /
              (N + 3 : ℝ) ^ (6 : ℝ)) := by ring
        _ = _ := by
          rw [← Real.rpow_sub hx]
          norm_num

lemma tendsto_fourthCutoffSq_div_sqrtDet_zero :
    Tendsto (fun N : ℕ ↦
      (fourthCrossingCutoff N : ℝ) ^ 2 /
        Real.sqrt (fourthDet (N + 2))) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    exact fourthCutoffSq_div_sqrtDet_upper N
  · have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 / 3 by norm_num)).comp
      tendsto_fourthScale_atTop
    simpa using tendsto_const_nhds.mul h

lemma tendsto_fourthPolyCutoff_exp (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ ↦
      (N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
        Real.exp (-c * (N + 3 : ℝ))) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    have hs := fourthCrossingCutoff_sq_upper N
    calc
      (N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
          Real.exp (-c * (N + 3 : ℝ)) ≤
        (N + 3 : ℝ) * (4 * (N + 3 : ℝ) ^ ((16 : ℝ) / 3)) *
          Real.exp (-c * (N + 3 : ℝ)) := by gcongr
      _ = 4 * ((N + 3 : ℝ) ^ ((19 : ℝ) / 3) *
          Real.exp (-c * (N + 3 : ℝ))) := by
        rw [show (19 : ℝ) / 3 = 1 + 16 / 3 by ring,
          Real.rpow_add (by positivity), Real.rpow_one]
        ring
  · simpa using tendsto_const_nhds.mul
      (tendsto_fourthScale_rpow_exp ((19 : ℝ) / 3) c hc)

lemma fourthTailExponent_lower (N : ℕ) :
    (N + 3 : ℝ) ^ ((1 : ℝ) / 3) / 48 ≤
      (fourthCrossingCutoff N : ℝ) ^ 2 /
        (2 * fourthIncrementVarianceB (N + 2)) := by
  have hL := fourthCrossingCutoff_sq_lower N
  have hB0 := fourthIncrementVarianceB_upper_power (N + 2)
  have hB : fourthIncrementVarianceB (N + 2) ≤
      24 * (N + 3 : ℝ) ^ 5 := by
    convert hB0 using 1 <;> push_cast <;> ring
  have hBp : 0 < fourthIncrementVarianceB (N + 2) := by
    unfold fourthIncrementVarianceB
    positivity
  apply (le_div_iff₀ (mul_pos (by norm_num) hBp)).2
  calc
    ((N + 3 : ℝ) ^ ((1 : ℝ) / 3) / 48) *
        (2 * fourthIncrementVarianceB (N + 2)) ≤
      ((N + 3 : ℝ) ^ ((1 : ℝ) / 3) / 48) *
        (2 * (24 * (N + 3 : ℝ) ^ 5)) := by gcongr
    _ = (N + 3 : ℝ) ^ ((16 : ℝ) / 3) := by
      have hx : 0 < (N + 3 : ℝ) := by positivity
      calc
        ((N + 3 : ℝ) ^ ((1 : ℝ) / 3) / 48) *
            (2 * (24 * (N + 3 : ℝ) ^ (5 : ℕ))) =
            (N + 3 : ℝ) ^ ((1 : ℝ) / 3) *
              (N + 3 : ℝ) ^ (5 : ℕ) := by ring
        _ = (N + 3 : ℝ) ^ ((1 : ℝ) / 3) *
            (N + 3 : ℝ) ^ (5 : ℝ) := by
          exact congrArg (fun z : ℝ ↦ (N + 3 : ℝ) ^ ((1 : ℝ) / 3) * z)
            (Real.rpow_natCast (N + 3 : ℝ) 5).symm
        _ = (N + 3 : ℝ) ^ ((1 : ℝ) / 3 + 5) :=
          (Real.rpow_add hx _ _).symm
        _ = _ := by norm_num
    _ ≤ _ := hL

lemma fourthTailNormalized_upper (N : ℕ) :
    (N + 3 : ℝ) *
        (2 * Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2)))) ≤
      2 * (N + 3 : ℝ) *
        Real.exp (-((N + 3 : ℝ) ^ ((1 : ℝ) / 3) / 48)) := by
  have h := fourthTailExponent_lower N
  have he : Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
      (2 * fourthIncrementVarianceB (N + 2))) ≤
      Real.exp (-((N + 3 : ℝ) ^ ((1 : ℝ) / 3) / 48)) := by
    apply Real.exp_le_exp.mpr
    calc
      -((fourthCrossingCutoff N : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2)) =
          -((fourthCrossingCutoff N : ℝ) ^ 2 /
            (2 * fourthIncrementVarianceB (N + 2))) := by ring
      _ ≤ -((N + 3 : ℝ) ^ ((1 : ℝ) / 3) / 48) := neg_le_neg h
  calc
    (N + 3 : ℝ) *
        (2 * Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2)))) =
      2 * (N + 3 : ℝ) *
        Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

lemma tendsto_fourthTailNormalized_zero :
    Tendsto (fun N : ℕ ↦
      (N + 3 : ℝ) *
        (2 * Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2))))) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    exact fourthTailNormalized_upper N
  · have hy : Tendsto (fun N : ℕ ↦
        (N + 3 : ℝ) ^ ((1 : ℝ) / 3)) atTop atTop :=
      (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp
        tendsto_fourthScale_atTop
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (3 : ℝ) (1 / 48 : ℝ) (by norm_num)).comp hy
    have ht2 :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 2)).mul ht
    have ht20 : Tendsto (fun N : ℕ ↦ 2 *
        ((fun x : ℝ ↦ x ^ (3 : ℝ) * Real.exp (-(1 / 48 : ℝ) * x))
          ((N + 3 : ℝ) ^ ((1 : ℝ) / 3)))) atTop (𝓝 0) := by
      simpa [Function.comp_apply] using ht2
    apply ht20.congr'
    filter_upwards with N
    have hx : 0 ≤ (N + 3 : ℝ) := by positivity
    rw [← Real.rpow_mul hx]
    norm_num
    ring

lemma fourthDualGaussianEscapeRadius_lower_power (N : ℕ) :
    (N + 3 : ℝ) ^ 5 / 500000000 ≤
      fourthDualGaussianEscapeRadius (N + 2) := by
  have hD0 := fourthDet_lower_power (N + 2)
  have hD : (N + 3 : ℝ) ^ 12 / 4000000 ≤ fourthDet (N + 2) := by
    convert hD0 using 1 <;> push_cast <;> ring
  have hAB0 := fourthVariance_sum_upper_power (N + 2)
  have hAB : fourthVarianceA (N + 2) + fourthIncrementVarianceB (N + 2) ≤
      124 * (N + 3 : ℝ) ^ 7 := by
    convert hAB0 using 1 <;> push_cast <;> ring
  have hABp : 0 < fourthVarianceA (N + 2) +
      fourthIncrementVarianceB (N + 2) := by
    have hA := fourthVarianceA_pos' (N + 2)
    have hB : 0 < fourthIncrementVarianceB (N + 2) := by
      unfold fourthIncrementVarianceB
      positivity
    positivity
  have hratio : (N + 3 : ℝ) ^ 5 / 500000000 ≤
      fourthDet (N + 2) /
        (fourthVarianceA (N + 2) + fourthIncrementVarianceB (N + 2)) := by
    apply (le_div_iff₀ hABp).2
    calc
      ((N + 3 : ℝ) ^ 5 / 500000000) *
          (fourthVarianceA (N + 2) + fourthIncrementVarianceB (N + 2)) ≤
        ((N + 3 : ℝ) ^ 5 / 500000000) *
          (124 * (N + 3 : ℝ) ^ 7) := by gcongr
      _ ≤ (N + 3 : ℝ) ^ 12 / 4000000 := by
        have hp : 0 ≤ (N + 3 : ℝ) ^ 12 := by positivity
        nlinarith
      _ ≤ _ := hD
  unfold fourthDualGaussianEscapeRadius
  have hpi : 1 ≤ Real.pi ^ 2 / 4 := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ fourthDet (N + 2) /
        (fourthVarianceA (N + 2) + fourthIncrementVarianceB (N + 2)) := hratio
    _ ≤ _ := le_mul_of_one_le_right
      (div_nonneg (fourthDet_pos _).le hABp.le) hpi

lemma tendsto_fourthPolyCutoff_gaussianEscape_zero :
    Tendsto (fun N : ℕ ↦
      (N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
        Real.exp (-(1 / 4 : ℝ) * fourthDualGaussianEscapeRadius (N + 2)))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    have hs := fourthCrossingCutoff_sq_upper N
    have hesc := fourthDualGaussianEscapeRadius_lower_power N
    have hx1 : (N + 3 : ℝ) ≤ (N + 3 : ℝ) ^ 5 := by
      calc
        (N + 3 : ℝ) = (N + 3 : ℝ) ^ (1 : ℕ) := by ring
        _ ≤ _ := pow_le_pow_right₀ (by
          have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith) (by omega)
    have hexp : Real.exp (-(1 / 4 : ℝ) *
        fourthDualGaussianEscapeRadius (N + 2)) ≤
        Real.exp (-(1 / 2000000000 : ℝ) * (N + 3 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      (N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
          Real.exp (-(1 / 4 : ℝ) * fourthDualGaussianEscapeRadius (N + 2)) ≤
        (N + 3 : ℝ) * (4 * (N + 3 : ℝ) ^ ((16 : ℝ) / 3)) *
          Real.exp (-(1 / 2000000000 : ℝ) * (N + 3 : ℝ)) := by gcongr
      _ = 4 * ((N + 3 : ℝ) ^ ((19 : ℝ) / 3) *
          Real.exp (-(1 / 2000000000 : ℝ) * (N + 3 : ℝ))) := by
        rw [show (19 : ℝ) / 3 = 1 + 16 / 3 by ring,
          Real.rpow_add (by positivity), Real.rpow_one]
        ring
  · simpa using tendsto_const_nhds.mul
      (tendsto_fourthScale_rpow_exp ((19 : ℝ) / 3)
        (1 / 2000000000 : ℝ) (by norm_num))

lemma tendsto_fourthPolyCutoff_macroscopic_zero :
    Tendsto (fun N : ℕ ↦
      (N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
        fourthMacroscopicDecay N) atTop (𝓝 0) := by
  let c : ℝ := (2 / Real.pi ^ 2) / 200000000000000000000
  have hc : 0 < c := by dsimp [c]; positivity
  apply squeeze_zero'
  · filter_upwards with N
    unfold fourthMacroscopicDecay
    positivity
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
    have hs := fourthCrossingCutoff_sq_upper N
    have hNx : (N + 3 : ℝ) / 2 ≤ (N : ℝ) := by
      have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hexp : fourthMacroscopicDecay N ≤
        Real.exp (-(c / 2) * (N + 3 : ℝ)) := by
      unfold fourthMacroscopicDecay
      apply Real.exp_le_exp.mpr
      dsimp [c]
      have hp : 0 < 2 / Real.pi ^ 2 := by positivity
      nlinarith
    have hmac : 0 ≤ fourthMacroscopicDecay N := by
      unfold fourthMacroscopicDecay
      positivity
    calc
      (N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
          fourthMacroscopicDecay N ≤
        (N + 3 : ℝ) * (4 * (N + 3 : ℝ) ^ ((16 : ℝ) / 3)) *
          fourthMacroscopicDecay N := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (by positivity)) hmac
      _ ≤ (N + 3 : ℝ) * (4 * (N + 3 : ℝ) ^ ((16 : ℝ) / 3)) *
          Real.exp (-(c / 2) * (N + 3 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 4 * ((N + 3 : ℝ) ^ ((19 : ℝ) / 3) *
          Real.exp (-(c / 2) * (N + 3 : ℝ))) := by
        rw [show (19 : ℝ) / 3 = 1 + 16 / 3 by ring,
          Real.rpow_add (by positivity), Real.rpow_one]
        ring
  · simpa using tendsto_const_nhds.mul
      (tendsto_fourthScale_rpow_exp ((19 : ℝ) / 3) (c / 2)
        (div_pos hc (by norm_num)))

lemma tendsto_fourthNormalizedFullAtomError_zero :
    Tendsto (fun N : ℕ ↦
      (N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
        fourthFullAtomError N) atTop (𝓝 0) := by
  let poly : ℕ → ℝ := fun N ↦
    (N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2
  let invD : ℕ → ℝ := fun N ↦ (Real.sqrt (fourthDet (N + 2)))⁻¹
  have hinv : Tendsto invD atTop (𝓝 0) := tendsto_fourthInvSqrtDet_zero
  have h0core := tendsto_fourthCutoffSq_div_sqrtDet_zero
  have h0 : Tendsto (fun N : ℕ ↦ poly N *
      ((1 / Real.pi ^ 2 : ℝ) *
        ((6144 / (N + 3 : ℝ)) * invD N *
          (Real.pi / (1 / (2 * Real.pi ^ 2)))))) atTop (𝓝 0) := by
    let C : ℝ := (1 / Real.pi ^ 2) * 6144 *
      (Real.pi / (1 / (2 * Real.pi ^ 2)))
    have hC : Tendsto (fun N : ℕ ↦ C *
        ((fourthCrossingCutoff N : ℝ) ^ 2 /
          Real.sqrt (fourthDet (N + 2)))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C)).mul h0core
    apply hC.congr'
    filter_upwards with N
    dsimp [poly, invD, C]
    have hx : (N + 3 : ℝ) ≠ 0 := by positivity
    have hs : Real.sqrt (fourthDet (N + 2)) ≠ 0 :=
      (Real.sqrt_pos.2 (fourthDet_pos _)).ne'
    field_simp
  have hmacro : Tendsto (fun N : ℕ ↦ poly N *
      ((1 / Real.pi ^ 2 : ℝ) * (Real.pi ^ 2 * fourthMacroscopicDecay N)))
      atTop (𝓝 0) := by
    have h := tendsto_fourthPolyCutoff_macroscopic_zero
    have hC := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ (1 / Real.pi ^ 2 : ℝ) * Real.pi ^ 2) atTop
      (𝓝 ((1 / Real.pi ^ 2 : ℝ) * Real.pi ^ 2))).mul h
    have hC0 : Tendsto (fun N : ℕ ↦
        ((1 / Real.pi ^ 2 : ℝ) * Real.pi ^ 2) *
          ((N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
            fourthMacroscopicDecay N)) atTop (𝓝 0) := by simpa using hC
    apply hC0.congr'
    filter_upwards with N
    dsimp [poly]
    ring
  let c₁ : ℝ := fourthGlobalRadialRate / 24
  have hc₁ : 0 < c₁ := div_pos fourthGlobalRadialRate_pos (by norm_num)
  have hp₁ := tendsto_fourthPolyCutoff_exp c₁ hc₁
  have hp₁i := hp₁.mul hinv
  have hrad₁ : Tendsto (fun N : ℕ ↦ poly N *
      ((1 / Real.pi ^ 2 : ℝ) *
        (Real.exp (-(fourthGlobalRadialRate / 2) * fourthTaylorRadius N) *
          (invD N * (Real.pi / (fourthGlobalRadialRate / 2))))))
      atTop (𝓝 0) := by
    let C : ℝ := (1 / Real.pi ^ 2) *
      (Real.pi / (fourthGlobalRadialRate / 2))
    have hC := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C)).mul hp₁i
    have hC0 : Tendsto (fun N : ℕ ↦ C *
        (((N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
          Real.exp (-c₁ * (N + 3 : ℝ))) * invD N)) atTop (𝓝 0) := by
      simpa using hC
    apply hC0.congr'
    filter_upwards with N
    dsimp [poly, invD, C, c₁, fourthTaylorRadius]
    ring
  let c₂ : ℝ := 1 / 48
  have hc₂ : 0 < c₂ := by dsimp [c₂]; norm_num
  have hp₂ := tendsto_fourthPolyCutoff_exp c₂ hc₂
  have hp₂i := hp₂.mul hinv
  have hrad₂ : Tendsto (fun N : ℕ ↦ poly N *
      ((1 / Real.pi ^ 2 : ℝ) *
        (Real.exp (-(1 / 4 : ℝ) * fourthTaylorRadius N) *
          (invD N * (Real.pi / (1 / 4 : ℝ)))))) atTop (𝓝 0) := by
    let C : ℝ := (1 / Real.pi ^ 2) * (Real.pi / (1 / 4 : ℝ))
    have hC := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C)).mul hp₂i
    have hC0 : Tendsto (fun N : ℕ ↦ C *
        (((N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
          Real.exp (-c₂ * (N + 3 : ℝ))) * invD N)) atTop (𝓝 0) := by
      simpa using hC
    apply hC0.congr'
    filter_upwards with N
    dsimp [poly, invD, C, c₂, fourthTaylorRadius]
    ring
  have hge := tendsto_fourthPolyCutoff_gaussianEscape_zero
  have hgei := hge.mul hinv
  have hgauss : Tendsto (fun N : ℕ ↦
      poly N * fourthGaussianFourierTailBound (N + 2)) atTop (𝓝 0) := by
    let C : ℝ := (1 / Real.pi ^ 2) * (Real.pi / (1 / 4 : ℝ))
    have hC := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C)).mul hgei
    have hC0 : Tendsto (fun N : ℕ ↦ C *
        (((N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
          Real.exp (-(1 / 4 : ℝ) * fourthDualGaussianEscapeRadius (N + 2))) *
            invD N)) atTop (𝓝 0) := by simpa using hC
    apply hC0.congr'
    filter_upwards with N
    dsimp [poly, invD, C, fourthGaussianFourierTailBound]
    ring
  have hall := (((h0.add hmacro).add hrad₁).add hrad₂).add hgauss
  have hall0 : Tendsto (fun N : ℕ ↦
      poly N * ((1 / Real.pi ^ 2 : ℝ) *
        ((6144 / (N + 3 : ℝ)) * invD N *
          (Real.pi / (1 / (2 * Real.pi ^ 2))))) +
      poly N * ((1 / Real.pi ^ 2 : ℝ) *
        (Real.pi ^ 2 * fourthMacroscopicDecay N)) +
      poly N * ((1 / Real.pi ^ 2 : ℝ) *
        (Real.exp (-(fourthGlobalRadialRate / 2) * fourthTaylorRadius N) *
          (invD N * (Real.pi / (fourthGlobalRadialRate / 2))))) +
      poly N * ((1 / Real.pi ^ 2 : ℝ) *
        (Real.exp (-(1 / 4 : ℝ) * fourthTaylorRadius N) *
          (invD N * (Real.pi / (1 / 4 : ℝ))))) +
      poly N * fourthGaussianFourierTailBound (N + 2)) atTop (𝓝 0) := by
    simpa only [add_zero] using hall
  apply hall0.congr'
  filter_upwards with N
  dsimp [poly]
  unfold fourthFullAtomError fourthFourierL1ErrorBound
  ring

lemma fourthEndpointNormalized_upper (N : ℕ) :
    (N + 3 : ℝ) *
        (8 * (fourthIncrementL1 (N + 2) + 1 : ℝ) /
          (Real.pi * Real.sqrt (fourthDet (N + 2)))) ≤
      48000 / (N + 3 : ℝ) ^ 2 := by
  push_cast
  let x : ℝ := N + 3
  have hx : 0 < x := by dsimp [x]; positivity
  have hL0 := fourthIncrementL1_upper_power (N + 2)
  have hL : (fourthIncrementL1 (N + 2) : ℝ) + 1 ≤ 9 * x ^ 3 := by
    have hshift : (N + 2 + 4 : ℝ) ≤ 2 * x := by
      dsimp [x]
      push_cast
      linarith
    have hp : (N + 2 + 4 : ℝ) ^ 3 ≤ (2 * x) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hshift 3
    rw [show (2 * x) ^ 3 = 8 * x ^ 3 by ring] at hp
    have hx3 : 1 ≤ x ^ 3 := by
      have hx1 : 1 ≤ x := by
        dsimp [x]
        have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      exact one_le_pow₀ hx1
    dsimp [x] at hL0 hp hx3 ⊢
    push_cast at hL0
    linarith
  have hs0 := fourthSqrtDet_lower_power (N + 2)
  have hs : x ^ 6 / 2000 ≤ Real.sqrt (fourthDet (N + 2)) := by
    convert hs0 using 1 <;> dsimp [x] <;> push_cast <;> ring
  have hden : 3 * (x ^ 6 / 2000) ≤
      Real.pi * Real.sqrt (fourthDet (N + 2)) := by
    nlinarith [Real.pi_gt_three, Real.sqrt_pos.2 (fourthDet_pos (N + 2))]
  calc
    x * (8 * ((fourthIncrementL1 (N + 2) : ℝ) + 1) /
        (Real.pi * Real.sqrt (fourthDet (N + 2)))) =
      (x * 8 * ((fourthIncrementL1 (N + 2) : ℝ) + 1)) /
        (Real.pi * Real.sqrt (fourthDet (N + 2))) := by ring
    _ ≤ (x * 8 * (9 * x ^ 3)) / (3 * (x ^ 6 / 2000)) :=
      div_le_div₀ (by positivity) (by gcongr) (by positivity) hden
    _ = 48000 / x ^ 2 := by field_simp; ring

lemma tendsto_fourthEndpointNormalized_zero :
    Tendsto (fun N : ℕ ↦
      (N + 3 : ℝ) *
        (8 * (fourthIncrementL1 (N + 2) + 1 : ℝ) /
          (Real.pi * Real.sqrt (fourthDet (N + 2))))) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    exact fourthEndpointNormalized_upper N
  · have hp : Tendsto (fun N : ℕ ↦ (N + 3 : ℝ) ^ 2) atTop atTop := by
      have hr := (tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).comp
        tendsto_fourthScale_atTop
      apply hr.congr
      intro N
      simp [Function.comp_apply]
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (48000 : ℝ)) atTop (𝓝 48000)).mul
        (tendsto_inv_atTop_zero.comp hp)

lemma fourthIncrementGaussianRate_upper_power (N : ℕ) :
    fourthIncrementGaussianRate (N + 2) ≤
      200000000 / (N + 3 : ℝ) ^ 5 := by
  have hA0 := fourthVarianceA_upper_power (N + 2)
  have hA : fourthVarianceA (N + 2) ≤ 100 * (N + 3 : ℝ) ^ 7 := by
    convert hA0 using 1 <;> push_cast <;> ring
  have hD0 := fourthDet_lower_power (N + 2)
  have hD : (N + 3 : ℝ) ^ 12 / 4000000 ≤ fourthDet (N + 2) := by
    convert hD0 using 1 <;> push_cast <;> ring
  have hx : 0 < (N + 3 : ℝ) := by positivity
  have hDp := fourthDet_pos (N + 2)
  unfold fourthIncrementGaussianRate
  apply (div_le_iff₀ (mul_pos (by norm_num) hDp)).2
  calc
    fourthVarianceA (N + 2) ≤ 100 * (N + 3 : ℝ) ^ 7 := hA
    _ ≤ (200000000 / (N + 3 : ℝ) ^ 5) *
        (2 * fourthDet (N + 2)) := by
      rw [show (200000000 / (N + 3 : ℝ) ^ 5) *
          (2 * fourthDet (N + 2)) =
          (200000000 * (2 * fourthDet (N + 2))) /
            (N + 3 : ℝ) ^ 5 by field_simp]
      apply (le_div_iff₀ (pow_pos hx 5)).2
      calc
        100 * (N + 3 : ℝ) ^ 7 * (N + 3 : ℝ) ^ 5 =
            100 * (N + 3 : ℝ) ^ 12 := by ring
        _ ≤ 200000000 * (2 * fourthDet (N + 2)) := by nlinarith

lemma tendsto_fourthIncrementGaussianRate_zero :
    Tendsto (fun N : ℕ ↦ fourthIncrementGaussianRate (N + 2))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with N
    exact (fourthIncrementGaussianRate_pos _).le
  · filter_upwards with N
    exact fourthIncrementGaussianRate_upper_power N
  · have hp : Tendsto (fun N : ℕ ↦ (N + 3 : ℝ) ^ 5) atTop atTop := by
      have hr := (tendsto_rpow_atTop (show (0 : ℝ) < 5 by norm_num)).comp
        tendsto_fourthScale_atTop
      apply hr.congr
      intro N
      simp [Function.comp_apply]
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (200000000 : ℝ)) atTop
        (𝓝 200000000)).mul (tendsto_inv_atTop_zero.comp hp)

lemma eventually_fourthGaussianLeading_normalized :
    ∀ᶠ N : ℕ in atTop,
      (N + 3 : ℝ) *
        (Real.exp (fourthIncrementGaussianRate (N + 2)) *
          (Real.sqrt (fourthDet (N + 2)) /
            (Real.pi * fourthVarianceA (N + 2)))) ≤ (9 : ℝ) / 35 := by
  have hrate : ∀ᶠ N : ℕ in atTop,
      fourthIncrementGaussianRate (N + 2) < (1 : ℝ) / 4 :=
    tendsto_fourthIncrementGaussianRate_zero.eventually_lt_const (by norm_num)
  filter_upwards [hrate, eventually_ge_atTop (102 : ℕ)] with N hr hN
  have hratio0 := fourth_sqrtDet_div_varianceA_le (N + 2) (by omega)
  have hratio : Real.sqrt (fourthDet (N + 2)) / fourthVarianceA (N + 2) ≤
      (3 : ℝ) / (5 * (N + 3 : ℝ)) := by
    convert hratio0 using 1 <;> push_cast <;> ring
  have hx : 0 < (N + 3 : ℝ) := by positivity
  have hA : 0 < fourthVarianceA (N + 2) := fourthVarianceA_pos' _
  have hpi : 0 < Real.pi := Real.pi_pos
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
      _ ≤ ((N + 3 : ℝ) / Real.pi) *
          (3 / (5 * (N + 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (3 : ℝ) / (5 * Real.pi) := by field_simp
  have hexp : Real.exp (fourthIncrementGaussianRate (N + 2)) ≤ (9 : ℝ) / 7 := by
    calc
      Real.exp (fourthIncrementGaussianRate (N + 2)) ≤ Real.exp (1 / 4 : ℝ) :=
        Real.exp_le_exp.mpr hr.le
      _ ≤ (2 + (1 / 4 : ℝ)) / (2 - (1 / 4 : ℝ)) :=
        Real.exp_le_two_add_div_two_sub (by norm_num) (by norm_num)
      _ = (9 : ℝ) / 7 := by norm_num
  have hpib : (3 : ℝ) / (5 * Real.pi) ≤ 1 / 5 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hpi)).2
    nlinarith [Real.pi_gt_three]
  calc
    (N + 3 : ℝ) *
        (Real.exp (fourthIncrementGaussianRate (N + 2)) *
          (Real.sqrt (fourthDet (N + 2)) /
            (Real.pi * fourthVarianceA (N + 2)))) =
      Real.exp (fourthIncrementGaussianRate (N + 2)) *
        ((N + 3 : ℝ) * (Real.sqrt (fourthDet (N + 2)) /
          (Real.pi * fourthVarianceA (N + 2)))) := by ring
    _ ≤ (9 / 7 : ℝ) *
        ((N + 3 : ℝ) * (Real.sqrt (fourthDet (N + 2)) /
          (Real.pi * fourthVarianceA (N + 2)))) :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ (9 / 7 : ℝ) * ((3 : ℝ) / (5 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hkernel (by norm_num)
    _ ≤ (9 / 7 : ℝ) * (1 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hpib (by norm_num)
    _ = (9 : ℝ) / 35 := by norm_num

lemma tendsto_fourthNormalizedCardAtomError_zero :
    Tendsto (fun N : ℕ ↦
      (N + 3 : ℝ) * (((2 * fourthCrossingCutoff N + 1 : ℕ) : ℝ) ^ 2 *
        fourthFullAtomError N)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (21 : ℕ)] with N hN
    exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _)
      (fourthFullAtomError_nonneg N hN))
  · filter_upwards [eventually_ge_atTop (21 : ℕ)] with N hN
    have hcut : 1 ≤ fourthCrossingCutoff N := by
      have hp : 0 < (N + 3 : ℝ) ^ ((8 : ℝ) / 3) :=
        Real.rpow_pos_of_pos (by positivity) _
      exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.ceil_pos.mpr hp))
    have hcardNat : (2 * fourthCrossingCutoff N + 1) ^ 2 ≤
        9 * fourthCrossingCutoff N ^ 2 := by nlinarith
    have hcard : (((2 * fourthCrossingCutoff N + 1 : ℕ) : ℝ) ^ 2) ≤
        9 * (fourthCrossingCutoff N : ℝ) ^ 2 := by exact_mod_cast hcardNat
    have herr := fourthFullAtomError_nonneg N hN
    calc
      (N + 3 : ℝ) * (((2 * fourthCrossingCutoff N + 1 : ℕ) : ℝ) ^ 2 *
          fourthFullAtomError N) =
        ((N + 3 : ℝ) * fourthFullAtomError N) *
          (((2 * fourthCrossingCutoff N + 1 : ℕ) : ℝ) ^ 2) := by ring
      _ ≤ ((N + 3 : ℝ) * fourthFullAtomError N) *
          (9 * (fourthCrossingCutoff N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcard (mul_nonneg (by positivity) herr)
      _ = 9 * ((N + 3 : ℝ) * (fourthCrossingCutoff N : ℝ) ^ 2 *
          fourthFullAtomError N) := by ring
  · have h9raw :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (9 : ℝ)) atTop (𝓝 9)).mul
        tendsto_fourthNormalizedFullAtomError_zero
    simpa using h9raw

lemma tendsto_fourthNormalizedRemainder_zero :
    Tendsto (fun N : ℕ ↦
      (N + 3 : ℝ) *
        (8 * (fourthIncrementL1 (N + 2) + 1 : ℝ) /
          (Real.pi * Real.sqrt (fourthDet (N + 2))) +
        (((2 * fourthCrossingCutoff N + 1 : ℕ) : ℝ) ^ 2 *
          fourthFullAtomError N) +
        2 * Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2))))) atTop (𝓝 0) := by
  have h := (tendsto_fourthEndpointNormalized_zero.add
    tendsto_fourthNormalizedCardAtomError_zero).add
      tendsto_fourthTailNormalized_zero
  have h0 : Tendsto (fun N : ℕ ↦
      (N + 3 : ℝ) *
          (8 * (fourthIncrementL1 (N + 2) + 1 : ℝ) /
            (Real.pi * Real.sqrt (fourthDet (N + 2)))) +
        (N + 3 : ℝ) * ((((2 * fourthCrossingCutoff N + 1 : ℕ) : ℝ) ^ 2 *
          fourthFullAtomError N)) +
        (N + 3 : ℝ) *
          (2 * Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
            (2 * fourthIncrementVarianceB (N + 2)))) ) atTop (𝓝 0) := by
    simpa only [add_zero] using h
  apply h0.congr'
  filter_upwards with N
  ring

lemma eventually_fourthSignedCrossing_rate :
    ∀ᶠ N : ℕ in atTop,
      fourthSignedCrossingProbability (N + 2) ≤
        (57 : ℝ) / (200 * (N + 3 : ℝ)) := by
  have hrem : ∀ᶠ N : ℕ in atTop,
      (N + 3 : ℝ) *
        (8 * (fourthIncrementL1 (N + 2) + 1 : ℝ) /
          (Real.pi * Real.sqrt (fourthDet (N + 2))) +
        (((2 * fourthCrossingCutoff N + 1 : ℕ) : ℝ) ^ 2 *
          fourthFullAtomError N) +
        2 * Real.exp (-((fourthCrossingCutoff N : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2)))) < (1 : ℝ) / 100 :=
    tendsto_fourthNormalizedRemainder_zero.eventually_lt_const (by norm_num)
  filter_upwards [eventually_fourthGaussianLeading_normalized, hrem,
    eventually_ge_atTop (21 : ℕ)] with N hlead hremN hN
  have hmaster := fourthSignedCrossingProbability_le_explicit N
    (fourthCrossingCutoff N) hN
  have hx : 0 < (N + 3 : ℝ) := by positivity
  have hnorm : (N + 3 : ℝ) * fourthSignedCrossingProbability (N + 2) ≤
      (9 : ℝ) / 35 + 1 / 100 := by
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
      _ ≤ (9 : ℝ) / 35 + 1 / 100 := by linarith
  apply (le_div_iff₀ (mul_pos (by norm_num) hx)).2
  nlinarith

end Erdos521
