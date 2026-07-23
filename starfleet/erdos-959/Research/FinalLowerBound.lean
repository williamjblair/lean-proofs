import Research.ChosenParameters

noncomputable section
open Filter Asymptotics
namespace Erdos959

/-- The explicit positive constant in the final exponent. -/
def finalExponentConstant : ℝ := 1 / 50000

lemma finalExponentConstant_pos : 0 < finalExponentConstant := by
  norm_num [finalExponentConstant]

lemma rpow_gain_of_parameter
    {n h : ℕ} (hn : 2 ≤ n) (hh : 64 ≤ h)
    (hll : 0 < Real.log (Real.log (n : ℝ)))
    (hquant : Real.log n ≤ 2560 * h * Real.log (Real.log n)) :
    (n : ℝ) ^ (1 + finalExponentConstant / Real.log (Real.log n)) ≤
      (n : ℝ) * (2 : ℝ) ^ h / 46080 := by
  let a : ℝ := finalExponentConstant / Real.log (Real.log n)
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have ha : 0 ≤ a := by
    dsimp [a, finalExponentConstant]
    positivity
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) ≤ 0.6931471803).trans Real.log_two_gt_d9.le
  have haterm0 : a * Real.log n ≤ (2560 / 50000 : ℝ) * h := by
    calc
      a * Real.log n ≤ a * (2560 * h * Real.log (Real.log n)) :=
        mul_le_mul_of_nonneg_left hquant ha
      _ = (2560 / 50000 : ℝ) * h := by
        dsimp [a, finalExponentConstant]
        field_simp
  have haterm : a * Real.log n ≤ (h : ℝ) * Real.log 2 / 8 := by
    have hh0 : (0 : ℝ) ≤ h := by positivity
    nlinarith
  have hlogC : Real.log 46080 ≤ 16 * Real.log 2 := by
    have hc : (46080 : ℝ) ≤ (2 : ℝ) ^ 16 := by norm_num
    have hm := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 46080)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ 16) hc
    rw [Real.log_pow] at hm
    norm_num at hm ⊢
    exact hm
  have hlogCsmall : Real.log 46080 ≤ (h : ℝ) * Real.log 2 / 4 := by
    have hlog2nonneg : 0 ≤ Real.log 2 := hlog2.trans' (by norm_num)
    have hhR : (64 : ℝ) ≤ h := by exact_mod_cast hh
    nlinarith
  have hlogCompare : Real.log ((n : ℝ) ^ a) ≤
      Real.log (((2 : ℝ) ^ h) / 46080) := by
    rw [Real.log_rpow hnpos]
    rw [Real.log_div (by positivity : (2 : ℝ) ^ h ≠ 0) (by norm_num : (46080 : ℝ) ≠ 0),
      Real.log_pow]
    have hlog2nonneg : 0 ≤ Real.log 2 := hlog2.trans' (by norm_num)
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hgain : (n : ℝ) ^ a ≤ ((2 : ℝ) ^ h) / 46080 := by
    have hApos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnpos _
    have hGpos : 0 < ((2 : ℝ) ^ h) / 46080 := by positivity
    calc
      (n : ℝ) ^ a = Real.exp (Real.log ((n : ℝ) ^ a)) :=
        (Real.exp_log hApos).symm
      _ ≤ Real.exp (Real.log (((2 : ℝ) ^ h) / 46080)) :=
        Real.exp_le_exp.mpr hlogCompare
      _ = ((2 : ℝ) ^ h) / 46080 := Real.exp_log hGpos
  rw [show finalExponentConstant / Real.log (Real.log (n : ℝ)) = a by rfl,
    Real.rpow_add hnpos, Real.rpow_one]
  simpa [div_eq_mul_inv, mul_assoc] using
    (mul_le_mul_of_nonneg_left hgain hnpos.le)

/-- Erdős 959 lower bound: for every sufficiently large cardinality, the
extremal top-two distance multiplicity gap is superlinear by the factor
`n^(c/log log n)`, with the explicit constant `c=1/50000`. -/
theorem erdos959_superlinear_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      (n : ℝ) ^ (1 + c / Real.log (Real.log n)) ≤ extremalGap n := by
  obtain ⟨Nparam, hparam⟩ := eventually_asymptotic_parameter_properties
  have htlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp htlog
  obtain ⟨Nll, hNll⟩ := eventually_atTop.1
    (htloglog.eventually (eventually_gt_atTop (0 : ℝ)))
  let N := max 2 (max Nparam Nll)
  refine ⟨finalExponentConstant, finalExponentConstant_pos, N, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left 2 (max Nparam Nll)) hn
  have hnparam : Nparam ≤ n := by
    exact le_trans (le_trans (le_max_left Nparam Nll)
      (le_max_right 2 (max Nparam Nll))) hn
  have hnll : Nll ≤ n := by
    exact le_trans (le_trans (le_max_right Nparam Nll)
      (le_max_right 2 (max Nparam Nll))) hn
  obtain ⟨hh64, hfit, hquant⟩ := hparam n hnparam
  have hll : 0 < Real.log (Real.log (n : ℝ)) := hNll n (by exact_mod_cast hnll)
  have hfinite := adaptive_parameter_gap (m := asymptoticM n) (n := n)
    (by omega : 15 ≤ parameterH (asymptoticM n)) hfit
  have hrpow := rpow_gain_of_parameter hn2 hh64 hll hquant
  have hfiniteR : (n : ℝ) * (2 : ℝ) ^ parameterH (asymptoticM n) ≤
      46080 * (extremalGap n : ℝ) := by exact_mod_cast hfinite
  calc
    (n : ℝ) ^ (1 + finalExponentConstant / Real.log (Real.log n)) ≤
        (n : ℝ) * (2 : ℝ) ^ parameterH (asymptoticM n) / 46080 := hrpow
    _ ≤ (extremalGap n : ℝ) := by
      have : (0 : ℝ) < 46080 := by norm_num
      apply (div_le_iff₀ this).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfiniteR

end Erdos959
