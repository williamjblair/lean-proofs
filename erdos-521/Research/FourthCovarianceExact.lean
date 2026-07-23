import Research.FourthPairDecomposition
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

lemma choose_add_two_two_real (n : ℕ) :
    (Nat.choose (n + 2) 2 : ℝ) = (n + 1 : ℝ) * (n + 2 : ℝ) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.choose_succ_succ']
      rw [show Nat.choose (n + 2) 1 = n + 2 by simp]
      push_cast at ih ⊢
      rw [ih]
      ring

lemma choose_add_three_three_real (n : ℕ) :
    (Nat.choose (n + 3) 3 : ℝ) =
      (n + 1 : ℝ) * (n + 2 : ℝ) * (n + 3 : ℝ) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 3 = (n + 3) + 1 by omega, Nat.choose_succ_succ']
      push_cast at ih ⊢
      rw [ih, choose_add_two_two_real]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- Exact variance polynomial for the fourth-integrated Rademacher sum at time `k`. -/
lemma sum_choose_add_three_sq (k : ℕ) :
    (∑ l ∈ Finset.range (k + 1), (Nat.choose (l + 3) 3 : ℝ) ^ 2) =
      (k + 1 : ℝ) * (k + 2 : ℝ) * (k + 3 : ℝ) * (k + 4 : ℝ) *
        (2 * k + 5 : ℝ) * (5 * (k : ℝ) ^ 2 + 25 * k + 21) / 2520 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, choose_add_three_three_real]
      push_cast at ih ⊢
      ring

/-- Exact variance polynomial for the one-step increment (apart from its new coefficient). -/
lemma sum_choose_add_three_two_sq (k : ℕ) :
    (∑ l ∈ Finset.range (k + 1), (Nat.choose (l + 3) 2 : ℝ) ^ 2) =
      (k + 1 : ℝ) *
        (3 * (k : ℝ) ^ 4 + 42 * (k : ℝ) ^ 3 + 223 * (k : ℝ) ^ 2 +
          542 * k + 540) / 60 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show k + 1 + 3 = (k + 2) + 2 by omega, choose_add_two_two_real]
      push_cast at ih ⊢
      ring

/-- Exact covariance polynomial between the fourth sum and its one-step increment. -/
lemma sum_choose_add_three_mul (k : ℕ) :
    (∑ l ∈ Finset.range (k + 1),
      (Nat.choose (l + 3) 3 : ℝ) * Nat.choose (l + 3) 2) =
      (k + 1 : ℝ) * (k + 2 : ℝ) * (k + 3 : ℝ) * (k + 4 : ℝ) *
        (5 * (k : ℝ) ^ 2 + 31 * k + 45) / 360 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, choose_add_three_three_real]
      rw [show k + 1 + 3 = (k + 2) + 2 by omega, choose_add_two_two_real]
      push_cast at ih ⊢
      ring

end Erdos521
