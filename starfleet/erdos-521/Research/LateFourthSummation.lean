import Research.AxisOddTwistRotation
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

namespace Erdos521

noncomputable local instance lateFourthSummationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma sum_fourthCrossingIndicator_eq_natCard {α : Type*} [Fintype α]
    (ω : α → ℕ → Bool) (k : ℕ) :
    (∑ x : α, fourthIntegratedCrossingIndicator (ω x) k) =
      Nat.card {x : α //
        fourthIntegratedRademacherSum (ω x) k *
          fourthIntegratedRademacherSum (ω x) (k + 1) ≤ 0} := by
  rw [Nat.card_eq_fintype_card, card_subtype_eq_filter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x hx
  unfold fourthIntegratedCrossingIndicator
  split_ifs <;> rfl

lemma evenFourthIndicator_axisGood_mean_le (s m : ℕ) (hm : 1 ≤ m) :
    (∑ p : AxisGoodPath (s + (m + 1)),
        (fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m) : ℝ)) /
        Nat.card (AxisGoodPath (s + (m + 1))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
        (fourthSignedStripProbability (2 * m)
            (3 * fourthLateCutoff (2 * m - 2)) +
          12 / (2 * m + 1 : ℝ) ^ 4) +
      64 * ((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) *
        Real.exp (-((s : ℝ) + ((m + 1 : ℕ) : ℝ)) / 8) := by
  have h := evenFourthCrossing_axisGood_density_le s m hm
  have hsum : (∑ p : AxisGoodPath (s + (m + 1)),
      fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m)) =
      Nat.card {p : AxisGoodPath (s + (m + 1)) //
        fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m) *
          fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m + 1) ≤ 0} := by
    calc
      _ = ∑ p : AxisGoodPath (s + (m + 1)),
          fourthIntegratedCrossingIndicator (axisWordCoefficients (axisSuffix p)) (2 * m) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (fourthIndicator_axisSuffix_eq p (by omega)).symm
      _ = _ := sum_fourthCrossingIndicator_eq_natCard
        (fun p : AxisGoodPath (s + (m + 1)) ↦ axisWordCoefficients (axisSuffix p)) (2 * m)
  rw [← hsum] at h
  exact_mod_cast h

lemma oddFourthIndicator_axisGood_mean_le (s m : ℕ) (hm : 1 ≤ m) :
    (∑ p : AxisGoodPath (s + (m + 2)),
        (fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m + 1) : ℝ)) /
        Nat.card (AxisGoodPath (s + (m + 2))) ≤
      128 * Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
        (fourthSignedStripProbability (2 * m + 1)
            (3 * fourthLateCutoff (2 * m - 1)) +
          12 / (2 * m + 2 : ℝ) ^ 4) +
      64 * ((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) *
        Real.exp (-((s : ℝ) + ((m + 2 : ℕ) : ℝ)) / 8) := by
  have h := oddFourthCrossing_axisGood_density_le s m hm
  have hsum : (∑ p : AxisGoodPath (s + (m + 2)),
      fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m + 1)) =
      Nat.card {p : AxisGoodPath (s + (m + 2)) //
        fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m + 1) *
          fourthIntegratedRademacherSum (axisWordCoefficients (axisSuffix p)) (2 * m + 2) ≤ 0} := by
    calc
      _ = ∑ p : AxisGoodPath (s + (m + 2)),
          fourthIntegratedCrossingIndicator (axisWordCoefficients (axisSuffix p)) (2 * m + 1) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (fourthIndicator_axisSuffix_eq p (by omega)).symm
      _ = _ := sum_fourthCrossingIndicator_eq_natCard
        (fun p : AxisGoodPath (s + (m + 2)) ↦ axisWordCoefficients (axisSuffix p)) (2 * m + 1)
  rw [← hsum] at h
  exact_mod_cast h

lemma one_div_sqrt_succ_le_two_mul_sqrt_sub (j : ℕ) :
    (1 : ℝ) / Real.sqrt (j + 1 : ℝ) ≤
      2 * (Real.sqrt (j + 1 : ℝ) - Real.sqrt (j : ℝ)) := by
  let a := Real.sqrt (j + 1 : ℝ)
  let b := Real.sqrt (j : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by exact Real.sqrt_nonneg _
  have hba : b ≤ a := by
    dsimp [a, b]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hab : 0 < a + b := by positivity
  have hsqa : a ^ 2 = (j + 1 : ℝ) := by
    dsimp [a]
    rw [Real.sq_sqrt (by positivity)]
  have hsqb : b ^ 2 = (j : ℝ) := by
    dsimp [b]
    rw [Real.sq_sqrt (by positivity)]
  have hid : a - b = 1 / (a + b) := by
    apply (eq_div_iff hab.ne').2
    nlinarith
  have hsum : a + b ≤ 2 * a := by linarith
  have hinv : 1 / a ≤ 2 / (a + b) := by
    apply (div_le_div_iff₀ ha hab).2
    linarith
  change 1 / a ≤ 2 * (a - b)
  rw [hid]
  simpa [div_eq_mul_inv] using hinv

lemma sum_range_one_div_sqrt_succ_le (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 : ℝ) / Real.sqrt (j + 1 : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        2 * (Real.sqrt (j + 1 : ℝ) - Real.sqrt (j : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact one_div_sqrt_succ_le_two_mul_sqrt_sub j
    _ = 2 * Real.sqrt (N : ℝ) := by
      induction N with
      | zero => simp
      | succ N ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast
          ring

lemma sum_range_one_div_sqrt_shift_le (N q c : ℕ) (hq : q ≤ N) (hc : 1 ≤ c) :
    (∑ j ∈ Finset.range q, (1 : ℝ) / Real.sqrt (j + c : ℝ)) ≤
      ∑ j ∈ Finset.range N, (1 : ℝ) / Real.sqrt (j + 1 : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range q, (1 : ℝ) / Real.sqrt (j + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply one_div_le_one_div_of_le (by positivity)
      apply Real.sqrt_le_sqrt
      have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
      push_cast
      linarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hq)
      (by intro i hiN hiq; positivity)

end Erdos521
