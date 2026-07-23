import Research.FourthCrossingLattice
import Research.GaussianParitySum
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

lemma fourthPrimalWhitening_sq_sum (k : ℕ) (y : Fin 2 → ℝ) :
    (∑ j : Fin 2, fourthPrimalWhitening k y j ^ 2) =
      (fourthIncrementVarianceB k * y 0 ^ 2 -
          2 * fourthIncrementCovarianceC k * y 0 * y 1 +
          fourthVarianceA k * y 1 ^ 2) / fourthDet k := by
  rw [Fin.sum_univ_two]
  simp only [fourthPrimalWhitening]
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hD : 0 < fourthDet k := fourthDet_pos k
  rw [div_pow, div_pow, Real.sq_sqrt hA.le,
    Real.sq_sqrt (mul_nonneg hA.le hD.le)]
  have hAD : fourthVarianceA k * fourthDet k ≠ 0 :=
    mul_ne_zero hA.ne' hD.ne'
  field_simp [fourthDet, hA.ne', hD.ne', hAD]
  unfold fourthDet
  ring

lemma abs_le_abs_of_crossing {x i : ℝ} (h : x * (x + i) ≤ 0) : |x| ≤ |i| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    by_cases hx0 : x = 0
    · subst x
      simp
    · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hsum : x + i ≤ 0 := by nlinarith
      have hi : i < 0 := by nlinarith
      rw [abs_of_neg hi]
      linarith
  · have hxn : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hxn]
    have hsum : 0 ≤ x + i := by nlinarith
    have hi : 0 < i := by nlinarith
    rw [abs_of_pos hi]
    linarith

lemma fourthPrimalWhitening_sq_sum_ge_increment (k : ℕ) (y : Fin 2 → ℝ)
    (hcross : y 0 * (y 0 + y 1) ≤ 0) :
    fourthVarianceA k / fourthDet k * y 1 ^ 2 ≤
      ∑ j : Fin 2, fourthPrimalWhitening k y j ^ 2 := by
  have hC : 0 ≤ fourthIncrementCovarianceC k := by
    unfold fourthIncrementCovarianceC
    positivity
  have hB : 0 ≤ fourthIncrementVarianceB k := by
    unfold fourthIncrementVarianceB
    positivity
  have hD : 0 < fourthDet k := fourthDet_pos k
  have hxi : y 0 * y 1 ≤ 0 := by nlinarith [sq_nonneg (y 0)]
  rw [fourthPrimalWhitening_sq_sum]
  apply (le_div_iff₀ hD).2
  field_simp
  nlinarith [sq_nonneg (y 0)]

noncomputable def fourthIncrementGaussianRate (k : ℕ) : ℝ :=
  fourthVarianceA k / (2 * fourthDet k)

lemma fourthIncrementGaussianRate_pos (k : ℕ) :
    0 < fourthIncrementGaussianRate k := by
  unfold fourthIncrementGaussianRate
  exact div_pos (fourthVarianceA_pos' k) (mul_pos (by norm_num) (fourthDet_pos k))

/-- On the crossing wedge, the full Gaussian atom is controlled by the increment coordinate
alone. -/
lemma fourthGaussianFullAtom_crossing_le (k : ℕ) (y : Fin 2 → ℤ)
    (hcross : fourthPairCrossing y) :
    fourthGaussianFullAtom k (fun j ↦ (y j : ℝ)) ≤
      (2 / (Real.pi * Real.sqrt (fourthDet k))) *
        Real.exp (-fourthIncrementGaussianRate k * (y 1 : ℝ) ^ 2) := by
  have hcrossR : (y 0 : ℝ) * ((y 0 : ℝ) + (y 1 : ℝ)) ≤ 0 := by
    exact_mod_cast hcross
  have hq := fourthPrimalWhitening_sq_sum_ge_increment k
    (fun j ↦ (y j : ℝ)) hcrossR
  have hcoef : 0 ≤ 2 / (Real.pi * Real.sqrt (fourthDet k)) := by positivity
  unfold fourthGaussianFullAtom
  apply mul_le_mul_of_nonneg_left _ hcoef
  apply Real.exp_le_exp.mpr
  calc
    -(∑ j : Fin 2, fourthPrimalWhitening k (fun j ↦ (y j : ℝ)) j ^ 2) / 2 ≤
        -(fourthVarianceA k / fourthDet k * (y 1 : ℝ) ^ 2) / 2 := by
      linarith
    _ = -fourthIncrementGaussianRate k * (y 1 : ℝ) ^ 2 := by
      unfold fourthIncrementGaussianRate
      ring

/-- Eventually the determinant-to-variance ratio has the sharp simple upper bound needed for the
Gaussian crossing constant. -/
lemma fourth_sqrtDet_div_varianceA_le (k : ℕ) (hk : 104 ≤ k) :
    Real.sqrt (fourthDet k) / fourthVarianceA k ≤
      (3 : ℝ) / (5 * (k + 1 : ℝ)) := by
  have hA : 0 < fourthVarianceA k := fourthVarianceA_pos' k
  have hD : 0 < fourthDet k := fourthDet_pos k
  have hpoly :
      25 * (k + 1 : ℝ) ^ 2 * fourthDet k ≤ 9 * fourthVarianceA k ^ 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hid :
        9 * fourthVarianceA (104 + m) ^ 2 -
          25 * (104 + m + 1 : ℝ) ^ 2 * fourthDet (104 + m) =
        ((m + 105 : ℝ) ^ 2 * (m + 106 : ℝ) ^ 2 *
          (m + 107 : ℝ) ^ 2 * (m + 108 : ℝ) ^ 2 *
          (25 * (m : ℝ) ^ 6 + 13350 * (m : ℝ) ^ 5 +
            2853985 * (m : ℝ) ^ 4 + 305590710 * (m : ℝ) ^ 3 +
            16431352261 * (m : ℝ) ^ 2 + 359466880098 * m +
            325346484096)) / 6350400 := by
      rw [fourthDet, fourth_covariance_determinant_formula,
        fourthVarianceA_formula]
      push_cast
      ring
    have hnonneg : 0 ≤
        ((m + 105 : ℝ) ^ 2 * (m + 106 : ℝ) ^ 2 *
          (m + 107 : ℝ) ^ 2 * (m + 108 : ℝ) ^ 2 *
          (25 * (m : ℝ) ^ 6 + 13350 * (m : ℝ) ^ 5 +
            2853985 * (m : ℝ) ^ 4 + 305590710 * (m : ℝ) ^ 3 +
            16431352261 * (m : ℝ) ^ 2 + 359466880098 * m +
            325346484096)) / 6350400 := by positivity
    push_cast
    linarith
  have hsquare :
      (Real.sqrt (fourthDet k) / fourthVarianceA k) ^ 2 ≤
        ((3 : ℝ) / (5 * (k + 1 : ℝ))) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hD.le]
    have hkpos : (0 : ℝ) < k + 1 := by positivity
    field_simp
    nlinarith
  exact (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) hA.le)
    (by positivity)).mp hsquare

end Erdos521
