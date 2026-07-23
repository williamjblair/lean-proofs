import Research.IntegratedDescartes
import Research.TriangleSums
import Research.WeightedHockey
import Mathlib.Tactic

open Set
open scoped BigOperators

namespace Erdos521

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Ordinary and integrated Rademacher partial sums. -/
def rademacherPartialSum (ω : ℕ → Bool) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), sign (ω i)

def integratedRademacherSum (ω : ℕ → Bool) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (k + 1), rademacherPartialSum ω r

lemma rademacherPartialSum_succ (ω : ℕ → Bool) (k : ℕ) :
    rademacherPartialSum ω (k + 1) = rademacherPartialSum ω k + sign (ω (k + 1)) := by
  rw [rademacherPartialSum, rademacherPartialSum]
  simpa [Finset.sum_range_succ] using
    Finset.sum_range_succ (f := fun i ↦ sign (ω i)) (k + 1)

lemma integratedRademacherSum_succ (ω : ℕ → Bool) (k : ℕ) :
    integratedRademacherSum ω (k + 1) =
      integratedRademacherSum ω k + rademacherPartialSum ω (k + 1) := by
  rw [integratedRademacherSum, integratedRademacherSum]
  simpa [Finset.sum_range_succ] using
    Finset.sum_range_succ (f := fun r ↦ rademacherPartialSum ω r) (k + 1)

lemma integratedRademacherSum_eq_weighted (ω : ℕ → Bool) (k : ℕ) :
    integratedRademacherSum ω k =
      ∑ i ∈ Finset.range (k + 1), (k - i + 1 : ℕ) * sign (ω i) := by
  simp only [integratedRademacherSum, rademacherPartialSum]
  rw [sum_range_triangle_swap]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul]
  rw [Nat.card_Icc]
  have hik : i ≤ k := by
    have := Finset.mem_range.mp hi
    omega
  rw [show k + 1 - i = k - i + 1 by omega]

lemma sign_eq_second_difference_integrated (ω : ℕ → Bool) (k : ℕ) :
    sign (ω (k + 2)) = integratedRademacherSum ω (k + 2) -
      2 * integratedRademacherSum ω (k + 1) + integratedRademacherSum ω k := by
  rw [show k + 2 = (k + 1) + 1 by omega,
    integratedRademacherSum_succ, integratedRademacherSum_succ,
    rademacherPartialSum_succ, rademacherPartialSum_succ]
  rw [rademacherPartialSum_succ]
  ring

/-- Explicit coefficient formula for the Möbius transform. -/
lemma mobiusPolynomial_coeff (ω : ℕ → Bool) (n j : ℕ) :
    (mobiusPolynomial ω n).coeff j =
      ∑ i ∈ Finset.range (min j n + 1),
        sign (ω i) * (Nat.choose (n - i) (j - i) : ℝ) := by
  rw [mobiusPolynomial]
  simp
  have hsub : Finset.range (min j n + 1) ⊆ Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  calc
    (∑ i ∈ Finset.range (n + 1),
        (Polynomial.C (sign (ω i)) * Polynomial.X ^ i *
          (1 + Polynomial.X) ^ (n - i)).coeff j) =
      ∑ i ∈ Finset.range (min j n + 1),
        (Polynomial.C (sign (ω i)) * Polynomial.X ^ i *
          (1 + Polynomial.X) ^ (n - i)).coeff j := by
      symm
      apply Finset.sum_subset hsub
      intro i hi hi'
      have hin : i ≤ n := by
        have := Finset.mem_range.mp hi
        omega
      have hmin : min j n < i := by
        simp only [Finset.mem_range, not_lt] at hi'
        omega
      have hji : j < i := by
        by_cases hjn : j ≤ n
        · rw [min_eq_left hjn] at hmin
          exact hmin
        · rw [min_eq_right (le_of_not_ge hjn)] at hmin
          omega
      rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul',
        if_neg (not_le.mpr hji), mul_zero]
    _ = ∑ i ∈ Finset.range (min j n + 1),
        sign (ω i) * (Nat.choose (n - i) (j - i) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≤ j := by
        have := Finset.mem_range.mp hi
        omega
      rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul',
        if_pos hij, Polynomial.coeff_one_add_X_pow]

lemma mobiusPolynomial_coeff_eq_integrated (ω : ℕ → Bool) (n j : ℕ)
    (hjn : j + 2 ≤ n) :
    (mobiusPolynomial ω n).coeff j =
      ∑ r ∈ Finset.range (j + 1), integratedRademacherSum ω r *
        (Nat.choose (n - 2 - r) (j - r) : ℝ) := by
  rw [mobiusPolynomial_coeff]
  rw [show min j n = j by omega]
  calc
    (∑ i ∈ Finset.range (j + 1),
        sign (ω i) * (Nat.choose (n - i) (j - i) : ℝ)) =
        ∑ i ∈ Finset.range (j + 1),
          ∑ r ∈ Finset.Icc i j,
            (((r - i + 1 : ℕ) : ℝ) * sign (ω i)) *
              (Nat.choose (n - 2 - r) (j - r) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≤ j := by
        have := Finset.mem_range.mp hi
        omega
      rw [← weighted_choose_convolution n i j hij hjn]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ r ∈ Finset.range (j + 1),
          ∑ i ∈ Finset.range (r + 1),
            (((r - i + 1 : ℕ) : ℝ) * sign (ω i)) *
              (Nat.choose (n - 2 - r) (j - r) : ℝ) := by
      rw [sum_range_triangle_swap]
    _ = ∑ r ∈ Finset.range (j + 1), integratedRademacherSum ω r *
        (Nat.choose (n - 2 - r) (j - r) : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [integratedRademacherSum_eq_weighted]
      rw [Finset.sum_mul]

end Erdos521
