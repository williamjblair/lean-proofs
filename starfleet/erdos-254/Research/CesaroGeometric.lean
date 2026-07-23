import Mathlib

namespace Erdos254.CesaroGeometric

open Filter Topology
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Cesàro averages of the powers of a nontrivial point of the complex unit
circle tend to zero. -/
theorem tendsto_cesaro_powers_circle_zero
    (z : Circle) (hz : (z : ℂ) ≠ 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, (z : ℂ) ^ n)
      atTop (𝓝 0) := by
  have heps : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  apply NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded heps
  apply isBoundedUnder_of_eventually_le
    (a := 2 / ‖(z : ℂ) - 1‖)
  filter_upwards [] with N
  dsimp only [Function.comp_apply]
  rw [geom_sum_eq hz]
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖(z : ℂ) ^ N - 1‖ ≤ ‖(z : ℂ) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num

/-- The same geometric Cesàro kernel converges to the diagonal indicator. -/
theorem tendsto_cesaro_powers_circle
    (z : Circle) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, (z : ℂ) ^ n)
      atTop (𝓝 (if z = 1 then 1 else 0)) := by
  by_cases hz : z = 1
  · subst z
    simp only [Circle.coe_one, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    symm
    rw [Complex.real_smul]
    push_cast
    exact inv_mul_cancel₀ (show (N : ℂ) ≠ 0 by exact_mod_cast hN.ne')
  · have hz' : (z : ℂ) ≠ 1 := by
      intro h
      apply hz
      exact Subtype.ext h
    simpa [hz] using tendsto_cesaro_powers_circle_zero z hz'

end

end Erdos254.CesaroGeometric
