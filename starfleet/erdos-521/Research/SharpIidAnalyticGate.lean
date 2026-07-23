import Research.FourthCrossingSharpIid
import Research.HighThresholdFirstMomentGate
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

namespace Erdos521

noncomputable local instance sharpIidSplitDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

set_option maxHeartbeats 5000000 in
/-- F-092 reduces the remaining cone-conditioned analytic budget to a late mean of `0.23 log n`.
Indeed, the early iid mean costs at most `(50/49)·0.385`, and their sum is below `0.623`. -/
theorem erdos_521_negative_of_sharpIid_and_late
    (hlate : ∀ᶠ n : ℕ in atTop,
      (∑ p : AxisGoodPath n,
          (lateAxisFourthCount (earlyFourthCutoff n) p : ℝ)) ≤
        (23 : ℝ) / 100 * Fintype.card (AxisGoodPath n) *
          Real.log (recordDegree n : ℝ)) :
    ¬ Claim := by
  apply erdos_521_negative_of_highThreshold_firstMoment
  filter_upwards [iidFourthSharpEarlyMean, hlate,
    eventually_ge_atTop (100 : ℕ)] with n hiidn hlaten hn
  let r := earlyPairBlock n
  let s := n - r
  let K := earlyFourthCutoff n
  have hrn : r ≤ n := earlyPairBlock_le n (by omega)
  have hsr : s + r = n := by dsimp [s]; omega
  have hKbits : K < 2 * r := earlyFourthCutoff_lt_bits n
  have hKfull : K ≤ 2 * n - 5 := earlyFourthCutoff_le_full n (by omega)
  have hfactor : ((s + r + 1 : ℝ) / (s + 1 : ℝ)) ≤ (50 : ℝ) / 49 := by
    have hf := early_conditioning_factor_le n hn
    have hnum : (s + r + 1 : ℝ) = n + 1 := by exact_mod_cast congrArg (· + 1) hsr
    have hdeneq : (s + 1 : ℝ) = (n - earlyPairBlock n + 1 : ℕ) := by
      dsimp [s, r]
      push_cast
      rfl
    rw [hnum, hdeneq]
    exact hf
  have hiid_nonneg : 0 ≤
      (∑ w : AxisWord r, (terminalTwoSidedFourthCount K w : ℝ)) / (4 : ℝ) ^ r := by
    positivity
  have hterminal := goodPaths_suffix_mean_le_along s r hsr
    (terminalTwoSidedFourthCount K)
  have hterminal' :
      (∑ p : AxisGoodPath n,
        (terminalTwoSidedFourthCount K (axisSuffixAlong s r hsr p) : ℝ)) /
          Fintype.card (AxisGoodPath n) ≤
        ((s + r + 1 : ℝ) / (s + 1 : ℝ)) *
          ((∑ w : AxisWord r, (terminalTwoSidedFourthCount K w : ℝ)) /
            (4 : ℝ) ^ r) := by
    convert hterminal using 1 <;> ring
  have hearly :
      (∑ p : AxisGoodPath n,
        ((fourthIntegratedCrossingCount (axisPathCoefficients p) K +
          fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K : ℕ) : ℝ)) ≤
        (50 : ℝ) / 49 * ((77 : ℝ) / 200 * Real.log (recordDegree n : ℝ)) *
          Fintype.card (AxisGoodPath n) := by
    have hden : (0 : ℝ) < Fintype.card (AxisGoodPath n) := by
      exact_mod_cast card_axisGoodPath_pos n
    have hpoint (p : AxisGoodPath n) :
        ((fourthIntegratedCrossingCount (axisPathCoefficients p) K +
          fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K : ℕ) : ℝ) =
          terminalTwoSidedFourthCount K (axisSuffixAlong s r hsr p) := by
      exact_mod_cast (terminalTwoSidedFourthCount_axisSuffixAlong hsr p hKbits).symm
    have hnorm :
        (∑ p : AxisGoodPath n,
          ((fourthIntegratedCrossingCount (axisPathCoefficients p) K +
            fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K : ℕ) : ℝ)) /
            Fintype.card (AxisGoodPath n) ≤
          (50 : ℝ) / 49 * ((77 : ℝ) / 200 * Real.log (recordDegree n : ℝ)) := by
      calc
        _ = (∑ p : AxisGoodPath n,
            (terminalTwoSidedFourthCount K (axisSuffixAlong s r hsr p) : ℝ)) /
              Fintype.card (AxisGoodPath n) := by
            congr 1
            exact Finset.sum_congr rfl fun p hp ↦ hpoint p
        _ ≤ ((s + r + 1 : ℝ) / (s + 1 : ℝ)) *
            ((∑ w : AxisWord r, (terminalTwoSidedFourthCount K w : ℝ)) /
              (4 : ℝ) ^ r) := hterminal'
        _ ≤ (50 : ℝ) / 49 *
            ((∑ w : AxisWord r, (terminalTwoSidedFourthCount K w : ℝ)) /
              (4 : ℝ) ^ r) := mul_le_mul_of_nonneg_right hfactor hiid_nonneg
        _ ≤ (50 : ℝ) / 49 * ((77 : ℝ) / 200 *
            Real.log (recordDegree n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (by simpa [r, K] using hiidn) (by positivity)
    exact (div_le_iff₀ hden).mp hnorm
  calc
    (∑ p : AxisGoodPath n, (axisFourthCrossingCount p : ℝ)) =
        (∑ p : AxisGoodPath n,
          ((fourthIntegratedCrossingCount (axisPathCoefficients p) K +
            fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K : ℕ) : ℝ)) +
        ∑ p : AxisGoodPath n, (lateAxisFourthCount K p : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [axisFourthCrossingCount_eq_early_add_late p hKfull]
      push_cast
      ring
    _ ≤ (50 : ℝ) / 49 * ((77 : ℝ) / 200 * Real.log (recordDegree n : ℝ)) *
          Fintype.card (AxisGoodPath n) +
        (23 : ℝ) / 100 * Fintype.card (AxisGoodPath n) *
          Real.log (recordDegree n : ℝ) := add_le_add hearly (by simpa [K] using hlaten)
    _ ≤ (623 : ℝ) / 1000 * Fintype.card (AxisGoodPath n) *
          Real.log (recordDegree n : ℝ) := by
      have hcard : 0 ≤ (Fintype.card (AxisGoodPath n) : ℝ) := by positivity
      have hrec : 1 < (recordDegree n : ℝ) := by
        exact_mod_cast (by unfold recordDegree; omega : 1 < recordDegree n)
      have hlog : 0 < Real.log (recordDegree n : ℝ) := Real.log_pos hrec
      nlinarith

end Erdos521
