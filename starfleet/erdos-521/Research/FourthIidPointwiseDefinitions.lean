import Research.FourthCrossingAnalyticSplitRelaxed
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthIidDefsDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def terminalTwoSidedFourthIndicator {r : ℕ} (w : AxisWord r) (k : ℕ) : ℕ :=
  fourthIntegratedCrossingIndicator (axisWordCoefficients w) k +
    fourthIntegratedCrossingIndicator (oddTwist (axisWordCoefficients w)) k

lemma terminalTwoSidedFourthCount_eq_sum {r : ℕ} (K : ℕ) (w : AxisWord r) :
    terminalTwoSidedFourthCount K w =
      ∑ k ∈ Finset.range K, terminalTwoSidedFourthIndicator w k := by
  unfold terminalTwoSidedFourthCount terminalTwoSidedFourthIndicator
  rw [fourthIntegratedCrossingCount_eq_sum, fourthIntegratedCrossingCount_eq_sum,
    ← Finset.sum_add_distrib]

lemma terminalTwoSidedFourthIndicator_le_two {r : ℕ} (w : AxisWord r) (k : ℕ) :
    terminalTwoSidedFourthIndicator w k ≤ 2 := by
  unfold terminalTwoSidedFourthIndicator fourthIntegratedCrossingIndicator
  split_ifs <;> omega

/-- Exact finite local-limit target: eventually in the edge index, the two-sided Rademacher crossing
probability is at most `0.48/(k+1)`, uniformly in every finite word containing the edge. -/
def IidFourthPointwiseRate : Prop :=
  ∃ K : ℕ, ∀ (r k : ℕ), K ≤ k → k < 2 * r - 1 →
    (∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) /
        (4 : ℝ) ^ r ≤ (12 : ℝ) / (25 * (k + 1 : ℝ))

lemma sum_terminalIndicator_early_le (r K : ℕ) :
    (∑ k ∈ Finset.range K,
      ∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) ≤
      2 * K * (4 : ℝ) ^ r := by
  calc
    (∑ k ∈ Finset.range K,
      ∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) ≤
        ∑ _k ∈ Finset.range K, ∑ _w : AxisWord r, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro w hw
      exact_mod_cast terminalTwoSidedFourthIndicator_le_two w k
    _ = 2 * K * (4 : ℝ) ^ r := by
      have hc : Fintype.card (AxisWord r) = 4 ^ r := card_axisWord r
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.card_univ, hc]
      push_cast
      ring

lemma sum_recip_eq_harmonic (M : ℕ) :
    (∑ k ∈ Finset.range M, (1 : ℝ) / (k + 1 : ℝ)) = (harmonic M : ℝ) := by
  induction M with
  | zero => simp [harmonic_zero]
  | succ M ih =>
      rw [Finset.sum_range_succ, harmonic_succ]
      push_cast
      rw [ih]
      simp [div_eq_mul_inv]

end Erdos521
