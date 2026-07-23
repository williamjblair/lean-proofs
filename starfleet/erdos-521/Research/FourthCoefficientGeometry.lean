import Research.FourthCovarianceAngle
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable def fourthCoefficientA (q : ℕ) : ℝ := Nat.choose (q + 3) 3
noncomputable def fourthCoefficientB (q : ℕ) : ℝ := Nat.choose (q + 3) 2

noncomputable def fourthCoefficientDet (p q : ℕ) : ℝ :=
  fourthCoefficientA p * fourthCoefficientB q -
    fourthCoefficientA q * fourthCoefficientB p

lemma fourthCoefficientA_formula (q : ℕ) :
    fourthCoefficientA q = (q + 1 : ℝ) * (q + 2 : ℝ) * (q + 3 : ℝ) / 6 :=
  choose_add_three_three_real q

lemma fourthCoefficientB_formula (q : ℕ) :
    fourthCoefficientB q = (q + 2 : ℝ) * (q + 3 : ℝ) / 2 := by
  unfold fourthCoefficientB
  rw [show q + 3 = (q + 1) + 2 by omega, choose_add_two_two_real]
  push_cast
  ring

/-- Exact oriented area of two Pascal coefficient vectors.  In particular, their slopes are
strictly ordered and every two distinct vectors are linearly independent. -/
lemma fourthCoefficientDet_formula (p q : ℕ) :
    fourthCoefficientDet p q =
      (p + 2 : ℝ) * (p + 3 : ℝ) * (q + 2 : ℝ) * (q + 3 : ℝ) *
        ((p : ℝ) - q) / 12 := by
  unfold fourthCoefficientDet
  rw [fourthCoefficientA_formula, fourthCoefficientA_formula,
    fourthCoefficientB_formula, fourthCoefficientB_formula]
  push_cast
  ring

lemma fourthCoefficientDet_ne_zero {p q : ℕ} (hpq : p ≠ q) :
    fourthCoefficientDet p q ≠ 0 := by
  rw [fourthCoefficientDet_formula]
  have hpqR : (p : ℝ) - q ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpq)
  positivity

lemma fourthCoefficientDet_zero_new :
    fourthCoefficientA 0 * 1 - 0 * fourthCoefficientB 0 = 1 := by
  norm_num [fourthCoefficientA]

lemma sum_pair_det_sq_identity (s : Finset ℕ) (a b : ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i) ^ 2) =
      2 * (∑ i ∈ s, (a i) ^ 2) * (∑ j ∈ s, (b j) ^ 2) -
        2 * (∑ i ∈ s, a i * b i) ^ 2 := by
  have hprod (f g : ℕ → ℝ) :
      (∑ i ∈ s, ∑ j ∈ s, f i * g j) =
        (∑ i ∈ s, f i) * (∑ j ∈ s, g j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have hfirst :
      (∑ i ∈ s, ∑ j ∈ s, (a i) ^ 2 * (b j) ^ 2) =
        (∑ i ∈ s, (a i) ^ 2) * (∑ j ∈ s, (b j) ^ 2) :=
    hprod (fun i ↦ (a i) ^ 2) (fun j ↦ (b j) ^ 2)
  have hmiddle :
      (∑ i ∈ s, ∑ j ∈ s, 2 * (a i * b i) * (a j * b j)) =
        2 * (∑ i ∈ s, a i * b i) ^ 2 := by
    rw [hprod (fun i ↦ 2 * (a i * b i)) (fun j ↦ a j * b j)]
    rw [← Finset.mul_sum]
    ring
  have hlast :
      (∑ i ∈ s, ∑ j ∈ s, (a j) ^ 2 * (b i) ^ 2) =
        (∑ j ∈ s, (a j) ^ 2) * (∑ i ∈ s, (b i) ^ 2) := by
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, (b i) ^ 2 * (a j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ i ∈ s, (b i) ^ 2) * (∑ j ∈ s, (a j) ^ 2) :=
        hprod (fun i ↦ (b i) ^ 2) (fun j ↦ (a j) ^ 2)
      _ = _ := by ring
  calc
    (∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i) ^ 2) =
        (∑ i ∈ s, ∑ j ∈ s, (a i) ^ 2 * (b j) ^ 2) -
          (∑ i ∈ s, ∑ j ∈ s, 2 * (a i * b i) * (a j * b j)) +
          (∑ i ∈ s, ∑ j ∈ s, (a j) ^ 2 * (b i) ^ 2) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = 2 * (∑ i ∈ s, (a i) ^ 2) * (∑ j ∈ s, (b j) ^ 2) -
        2 * (∑ i ∈ s, a i * b i) ^ 2 := by
      rw [hfirst, hmiddle, hlast]
      ring

/-- Cauchy--Binet decomposition of the exact fourth covariance determinant.  The first sum is
from pairing each old coefficient vector with the new vector `(0,1)`; the double sum records all
old-vector oriented areas. -/
lemma fourth_covariance_determinant_pair_decomposition (k : ℕ) :
    2 * (fourthVarianceA k * fourthIncrementVarianceB k -
      fourthIncrementCovarianceC k ^ 2) =
      2 * ∑ q ∈ Finset.range (k + 1), (fourthCoefficientA q) ^ 2 +
        ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
          (fourthCoefficientDet p q) ^ 2 := by
  have hid := sum_pair_det_sq_identity (Finset.range (k + 1))
    fourthCoefficientA fourthCoefficientB
  unfold fourthVarianceA fourthIncrementVarianceB fourthIncrementCovarianceC
  change 2 * ((∑ l ∈ Finset.range (k + 1), (fourthCoefficientA l) ^ 2) *
      (1 + ∑ l ∈ Finset.range (k + 1), (fourthCoefficientB l) ^ 2) -
      (∑ l ∈ Finset.range (k + 1),
        fourthCoefficientA l * fourthCoefficientB l) ^ 2) = _
  unfold fourthCoefficientDet
  rw [hid]
  ring

end Erdos521
