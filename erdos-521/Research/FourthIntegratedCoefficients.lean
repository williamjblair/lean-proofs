import Research.ThirdIntegratedCoefficients
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthCoefficientsDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The fourth iterated partial sum of the Rademacher coefficients. -/
def fourthIntegratedRademacherSum (ω : ℕ → Bool) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (k + 1), thirdIntegratedRademacherSum ω r

lemma fourthIntegratedRademacherSum_succ (ω : ℕ → Bool) (k : ℕ) :
    fourthIntegratedRademacherSum ω (k + 1) =
      fourthIntegratedRademacherSum ω k + thirdIntegratedRademacherSum ω (k + 1) := by
  rw [fourthIntegratedRademacherSum, fourthIntegratedRademacherSum]
  simpa [Finset.sum_range_succ] using
    Finset.sum_range_succ (f := fun r ↦ thirdIntegratedRademacherSum ω r) (k + 1)

lemma choose_fourth_difference (n j i : ℕ) (hij : i < j) (hjn : j + 4 ≤ n) :
    (Nat.choose (n - 3 - i) (j - i) : ℝ) -
        Nat.choose (n - 3 - (i + 1)) (j - (i + 1)) =
      Nat.choose (n - 4 - i) (j - i) := by
  have htop : n - 3 - i = (n - 4 - i) + 1 := by omega
  have hbot : j - i = (j - (i + 1)) + 1 := by omega
  have htop' : n - 3 - (i + 1) = n - 4 - i := by omega
  rw [htop, hbot, htop']
  rw [Nat.choose_succ_succ']
  push_cast
  ring

/-- A fourth summation-by-parts step gives another positive Pascal convolution. -/
lemma mobiusPolynomial_coeff_eq_fourthIntegrated (ω : ℕ → Bool) (n j : ℕ)
    (hjn : j + 4 ≤ n) :
    (mobiusPolynomial ω n).coeff j =
      ∑ r ∈ Finset.range (j + 1), fourthIntegratedRademacherSum ω r *
        (Nat.choose (n - 4 - r) (j - r) : ℝ) := by
  rw [mobiusPolynomial_coeff_eq_thirdIntegrated]
  · let A : ℕ → ℝ := fun r ↦ Nat.choose (n - 3 - r) (j - r)
    let T : ℕ → ℝ := thirdIntegratedRademacherSum ω
    let U : ℕ → ℝ := fourthIntegratedRademacherSum ω
    have hparts := Finset.sum_range_by_parts A T (j + 1)
    have hpartial (i : ℕ) : (∑ r ∈ Finset.range (i + 1), T r) = U i := by rfl
    have hAj : A j = 1 := by simp [A]
    have hdiff (i : ℕ) (hi : i ∈ Finset.range j) : A (i + 1) - A i =
        -(Nat.choose (n - 4 - i) (j - i) : ℝ) := by
      have hij : i < j := Finset.mem_range.mp hi
      have h := choose_fourth_difference n j i hij hjn
      dsimp [A]
      linarith
    rw [show j + 1 - 1 = j by omega] at hparts
    simp only [hpartial] at hparts
    calc
      (∑ r ∈ Finset.range (j + 1), T r * A r) =
          ∑ r ∈ Finset.range (j + 1), A r • T r := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [mul_comm]
      _ = A j • U j - ∑ i ∈ Finset.range j, (A (i + 1) - A i) • U i := hparts
      _ = U j + ∑ i ∈ Finset.range j,
          U i * (Nat.choose (n - 4 - i) (j - i) : ℝ) := by
        rw [hAj]
        simp only [one_smul]
        have hs : (∑ i ∈ Finset.range j, (A (i + 1) - A i) • U i) =
            -(∑ i ∈ Finset.range j,
              U i * (Nat.choose (n - 4 - i) (j - i) : ℝ)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hdiff i hi]
          simp [mul_comm]
        rw [hs]
        ring
      _ = ∑ r ∈ Finset.range (j + 1), U r *
          (Nat.choose (n - 4 - r) (j - r) : ℝ) := by
        rw [Finset.sum_range_succ]
        simp
        ring
  · omega

end Erdos521
