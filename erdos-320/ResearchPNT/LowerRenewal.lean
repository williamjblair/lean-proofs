import ResearchPNT.LowerBins
import Research.LowerAbel

/-! # Unit-coefficient lower renewal inequality -/

open Filter Asymptotics Real

namespace ResearchPNT

/-- Combine the exact product recurrence and discrete Abel transform under a
pointwise compatible-prime estimate. -/
theorem coeffGood_lower_renewal_of_pointwise (N y : ℕ)
    (hlog : 0 < Real.log (N : ℝ)) (hy : 2 ≤ y)
    (hend : 0 ≤ (((N : ℝ) / Real.log N) / y) -
      (65536 ^ y + 1 : ℕ))
    (hpoint : ∀ m ∈ Research.tailCoeffGoodDenominators y,
      ((N : ℝ) / Real.log N) / m - (65536 ^ m + 1 : ℕ) ≤
        ((Research.compatiblePrimeSet N m).card : ℝ)) :
    ((N : ℝ) / Real.log N) *
        ∑ v ∈ Finset.Ico 2 y,
          ((Research.tailCoeffGoodDenominators v).card : ℝ) /
            ((v : ℝ) * (v + 1)) ≤
      ((Research.coeffGoodDenominators N).card : ℝ) := by
  let c : ℝ := (N : ℝ) / Real.log N
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have habel := Research.sum_main_sub_pow_ge_abel c y hc hy (by
    simpa [c] using hend)
  have hsumPoint :
      ∑ m ∈ Research.tailCoeffGoodDenominators y,
          (c / m - (65536 ^ m + 1 : ℕ)) ≤
        ∑ m ∈ Research.tailCoeffGoodDenominators y,
          ((Research.compatiblePrimeSet N m).card : ℝ) := by
    apply Finset.sum_le_sum
    intro m hm
    exact hpoint m hm
  have hnat := Research.sum_tail_compatiblePrimeSet_card_le N y
  have hcast :
      (∑ m ∈ Research.tailCoeffGoodDenominators y,
          ((Research.compatiblePrimeSet N m).card : ℝ)) ≤
        ((Research.coeffGoodDenominators N).card : ℝ) := by
    exact_mod_cast hnat
  exact le_trans habel (le_trans hsumPoint hcast)

/-- The arithmetic-good count satisfies an eventual exact unit-coefficient
lower renewal inequality. -/
theorem eventually_coeffGood_lower_renewal :
    ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) / Real.log N) *
          ∑ v ∈ Finset.Ico 2 (lowerY N),
            ((Research.tailCoeffGoodDenominators v).card : ℝ) /
              ((v : ℝ) * (v + 1)) ≤
        ((Research.coeffGoodDenominators N).card : ℝ) := by
  have hlogTend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_compatiblePrimeSet_card_ge,
    eventually_lowerY_endpoint_nonnegative,
    hlogTend.eventually (eventually_gt_atTop 0)] with N hpoint hend hlog
  apply coeffGood_lower_renewal_of_pointwise N (lowerY N) hlog hend.1 hend.2
  intro m hm
  rw [Research.tailCoeffGoodDenominators, Finset.mem_filter,
    Finset.mem_Icc] at hm
  have hp := hpoint m hm.1.1 hm.1.2
  convert hp using 1 <;> field_simp <;> ring

/-- Stronger form: generated products are never denominator one, so the
renewal output also lies in the tail count. -/
theorem tailGood_lower_renewal_of_pointwise (N y : ℕ)
    (hlog : 0 < Real.log (N : ℝ)) (hy : 2 ≤ y)
    (hend : 0 ≤ (((N : ℝ) / Real.log N) / y) -
      (65536 ^ y + 1 : ℕ))
    (hpoint : ∀ m ∈ Research.tailCoeffGoodDenominators y,
      ((N : ℝ) / Real.log N) / m - (65536 ^ m + 1 : ℕ) ≤
        ((Research.compatiblePrimeSet N m).card : ℝ)) :
    ((N : ℝ) / Real.log N) *
        ∑ v ∈ Finset.Ico 2 y,
          ((Research.tailCoeffGoodDenominators v).card : ℝ) /
            ((v : ℝ) * (v + 1)) ≤
      ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
  let c : ℝ := (N : ℝ) / Real.log N
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have habel := Research.sum_main_sub_pow_ge_abel c y hc hy (by
    simpa [c] using hend)
  have hsumPoint :
      ∑ m ∈ Research.tailCoeffGoodDenominators y,
          (c / m - (65536 ^ m + 1 : ℕ)) ≤
        ∑ m ∈ Research.tailCoeffGoodDenominators y,
          ((Research.compatiblePrimeSet N m).card : ℝ) := by
    apply Finset.sum_le_sum
    intro m hm
    exact hpoint m hm
  have hnat := Research.sum_tail_compatiblePrimeSet_card_le_tail N y
  have hcast :
      (∑ m ∈ Research.tailCoeffGoodDenominators y,
          ((Research.compatiblePrimeSet N m).card : ℝ)) ≤
        ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
    exact_mod_cast hnat
  exact le_trans habel (le_trans hsumPoint hcast)

/-- Eventual unit-coefficient renewal directly for the tail count. -/
theorem eventually_tailGood_lower_renewal :
    ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) / Real.log N) *
          ∑ v ∈ Finset.Ico 2 (lowerY N),
            ((Research.tailCoeffGoodDenominators v).card : ℝ) /
              ((v : ℝ) * (v + 1)) ≤
        ((Research.tailCoeffGoodDenominators N).card : ℝ) := by
  have hlogTend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_compatiblePrimeSet_card_ge,
    eventually_lowerY_endpoint_nonnegative,
    hlogTend.eventually (eventually_gt_atTop 0)] with N hpoint hend hlog
  apply tailGood_lower_renewal_of_pointwise N (lowerY N) hlog hend.1 hend.2
  intro m hm
  rw [Research.tailCoeffGoodDenominators, Finset.mem_filter,
    Finset.mem_Icc] at hm
  have hp := hpoint m hm.1.1 hm.1.2
  convert hp using 1 <;> field_simp <;> ring

#print axioms eventually_coeffGood_lower_renewal
#print axioms eventually_tailGood_lower_renewal

end ResearchPNT
