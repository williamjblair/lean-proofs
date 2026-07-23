import Research.FourthPhaseDifferenceHierarchy
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

/-- Exact original-coordinate phase-square identity. -/
lemma fourthOriginalPhase_sq_sum (k : ℕ) (s t : ℝ) :
    (∑ i : Option (Fin (k + 1)), fourthOriginalPhase k s t i ^ 2) =
      fourthVarianceA k * s ^ 2 +
        2 * fourthIncrementCovarianceC k * s * t +
        fourthIncrementVarianceB k * t ^ 2 := by
  rw [Fintype.sum_option]
  change t ^ 2 + (∑ q : Fin (k + 1),
      (s * fourthCoefficientA q + t * fourthCoefficientB q) ^ 2) = _
  have hsumEq : (∑ q : Fin (k + 1),
      (s * fourthCoefficientA q + t * fourthCoefficientB q) ^ 2) =
      ∑ q ∈ Finset.range (k + 1),
        (s * fourthCoefficientA q + t * fourthCoefficientB q) ^ 2 :=
    Fin.sum_univ_eq_sum_range
      (fun q : ℕ ↦ (s * fourthCoefficientA q + t * fourthCoefficientB q) ^ 2) (k + 1)
  rw [hsumEq]
  unfold fourthVarianceA fourthIncrementCovarianceC fourthIncrementVarianceB
  simp_rw [show ∀ q : ℕ,
      (s * fourthCoefficientA q + t * fourthCoefficientB q) ^ 2 =
        s ^ 2 * fourthCoefficientA q ^ 2 +
          2 * s * t * (fourthCoefficientA q * fourthCoefficientB q) +
          t ^ 2 * fourthCoefficientB q ^ 2 by intro q; ring]
  simp only [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  unfold fourthCoefficientA fourthCoefficientB
  ring

/-- Whenever all original phases are in one centered half-period, their characteristic product has
full covariance Gaussian decay, without any covariance-ball restriction. -/
lemma fourthOriginalCharacteristicProduct_noWrap_decay (k : ℕ) (s t : ℝ)
    (hphase : ∀ i : Option (Fin (k + 1)),
      |fourthOriginalPhase k s t i| ≤ Real.pi / 2) :
    |fourthOriginalCharacteristicProduct k s t| ≤
      Real.exp (-(2 / Real.pi ^ 2) *
        (fourthVarianceA k * s ^ 2 +
          2 * fourthIncrementCovarianceC k * s * t +
          fourthIncrementVarianceB k * t ^ 2)) := by
  let m : Option (Fin (k + 1)) → ℤ := fun _ ↦ 0
  have hmod := fourthOriginalCharacteristicProduct_modular_decay k s t m (by
    intro i
    simpa [m] using hphase i)
  have hmod' : |fourthOriginalCharacteristicProduct k s t| ≤
      Real.exp (-(2 / Real.pi ^ 2) *
        ∑ i : Option (Fin (k + 1)), fourthOriginalPhase k s t i ^ 2) := by
    simpa only [m, Int.cast_zero, zero_mul, sub_zero] using hmod
  rw [fourthOriginalPhase_sq_sum] at hmod'
  exact hmod'

lemma fourthCoefficientA_mono {q k : ℕ} (hq : q ≤ k) :
    fourthCoefficientA q ≤ fourthCoefficientA k := by
  unfold fourthCoefficientA
  exact_mod_cast Nat.choose_le_choose 3 (by omega : q + 3 ≤ k + 3)

lemma fourthCoefficientB_mono {q k : ℕ} (hq : q ≤ k) :
    fourthCoefficientB q ≤ fourthCoefficientB k := by
  unfold fourthCoefficientB
  exact_mod_cast Nat.choose_le_choose 2 (by omega : q + 3 ≤ k + 3)

/-- A simple anisotropic box condition guarantees that no old phase wraps around `πℤ`. -/
lemma fourthOriginalCharacteristicProduct_box_decay (k : ℕ) (s t : ℝ)
    (ht : |t| ≤ Real.pi / 2)
    (hbox : |s| * fourthCoefficientA k + |t| * fourthCoefficientB k ≤ Real.pi / 2) :
    |fourthOriginalCharacteristicProduct k s t| ≤
      Real.exp (-(2 / Real.pi ^ 2) *
        (fourthVarianceA k * s ^ 2 +
          2 * fourthIncrementCovarianceC k * s * t +
          fourthIncrementVarianceB k * t ^ 2)) := by
  apply fourthOriginalCharacteristicProduct_noWrap_decay
  intro i
  cases i with
  | none => simpa [fourthOriginalPhase] using ht
  | some q =>
      change |s * fourthCoefficientA q + t * fourthCoefficientB q| ≤ Real.pi / 2
      have hA0 : 0 ≤ fourthCoefficientA q := by
        unfold fourthCoefficientA
        positivity
      have hB0 : 0 ≤ fourthCoefficientB q := by
        unfold fourthCoefficientB
        positivity
      have hAk0 : 0 ≤ fourthCoefficientA k := by
        unfold fourthCoefficientA
        positivity
      have hBk0 : 0 ≤ fourthCoefficientB k := by
        unfold fourthCoefficientB
        positivity
      calc
        |s * fourthCoefficientA q + t * fourthCoefficientB q| ≤
            |s * fourthCoefficientA q| + |t * fourthCoefficientB q| := abs_add_le _ _
        _ = |s| * fourthCoefficientA q + |t| * fourthCoefficientB q := by
          rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg hB0]
        _ ≤ |s| * fourthCoefficientA k + |t| * fourthCoefficientB k := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (fourthCoefficientA_mono (Fin.le_last q)) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (fourthCoefficientB_mono (Fin.le_last q)) (abs_nonneg _))
        _ ≤ Real.pi / 2 := hbox

end Erdos521
