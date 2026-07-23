import Research.ConeSuffixMoment
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

namespace Erdos521

noncomputable local instance fourthAnalyticSplitDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A small terminal block which still tends to infinity and captures the logarithmic early-scale
crossings. -/
def earlyPairBlock (n : ℕ) : ℕ := n / 100 + 1

/-- Last crossing-count index visible from `earlyPairBlock n` pairs. -/
def earlyFourthCutoff (n : ℕ) : ℕ := 2 * earlyPairBlock n - 1

/-- The iid two-sided fourth-crossing statistic on a terminal axis word. -/
noncomputable def terminalTwoSidedFourthCount {r : ℕ} (K : ℕ) (w : AxisWord r) : ℕ :=
  fourthIntegratedCrossingCount (axisWordCoefficients w) K +
    fourthIntegratedCrossingCount (oddTwist (axisWordCoefficients w)) K

/-- Crossings after the early cutoff and before the root-bound cutoff. -/
noncomputable def lateAxisFourthCount {n : ℕ} (K : ℕ) (p : AxisGoodPath n) : ℕ :=
  (fourthIntegratedCrossingCount (axisPathCoefficients p) (2 * n - 5) -
      fourthIntegratedCrossingCount (axisPathCoefficients p) K) +
    (fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) (2 * n - 5) -
      fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K)

lemma earlyPairBlock_pos (n : ℕ) : 0 < earlyPairBlock n := by
  unfold earlyPairBlock
  omega

lemma earlyFourthCutoff_lt_bits (n : ℕ) :
    earlyFourthCutoff n < 2 * earlyPairBlock n := by
  unfold earlyFourthCutoff
  have := earlyPairBlock_pos n
  omega

lemma earlyPairBlock_le (n : ℕ) (hn : 2 ≤ n) : earlyPairBlock n ≤ n := by
  unfold earlyPairBlock
  omega

lemma earlyFourthCutoff_le_full (n : ℕ) (hn : 3 ≤ n) :
    earlyFourthCutoff n ≤ 2 * n - 5 := by
  unfold earlyFourthCutoff earlyPairBlock
  omega

lemma terminalTwoSidedFourthCount_axisSuffix {s r : ℕ} (p : AxisGoodPath (s + r))
    (K : ℕ) (hK : K < 2 * r) :
    terminalTwoSidedFourthCount K (axisSuffix p) =
      fourthIntegratedCrossingCount (axisPathCoefficients p) K +
        fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K := by
  unfold terminalTwoSidedFourthCount
  congr 1
  · apply fourthIntegratedCrossingCount_eq_of_prefix
    intro i hi
    exact axisSuffix_coefficients_eq_of_lt p (by omega)
  · apply fourthIntegratedCrossingCount_eq_of_prefix
    intro i hi
    unfold oddTwist
    rw [axisSuffix_coefficients_eq_of_lt p (by omega)]

lemma axisFourthCrossingCount_eq_early_add_late {n K : ℕ} (p : AxisGoodPath n)
    (hK : K ≤ 2 * n - 5) :
    axisFourthCrossingCount p =
      (fourthIntegratedCrossingCount (axisPathCoefficients p) K +
        fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K) +
      lateAxisFourthCount K p := by
  unfold axisFourthCrossingCount twoSidedFourthCrossingCount lateAxisFourthCount
  have hmono₁ := fourthIntegratedCrossingCount_mono (axisPathCoefficients p) hK
  have hmono₂ := fourthIntegratedCrossingCount_mono
    (oddTwist (axisPathCoefficients p)) hK
  omega

lemma early_conditioning_factor_le (n : ℕ) (hn : 100 ≤ n) :
    ((n + 1 : ℝ) / (n - earlyPairBlock n + 1 : ℕ)) ≤ (50 : ℝ) / 49 := by
  have hr : earlyPairBlock n ≤ n := earlyPairBlock_le n (by omega)
  have hdenNat : n - earlyPairBlock n + 1 = n - n / 100 := by
    unfold earlyPairBlock
    omega
  rw [hdenNat]
  have hfloor : 100 * (n / 100) ≤ n := Nat.mul_div_le n 100
  have hq : 1 ≤ n / 100 := Nat.le_div_iff_mul_le (by norm_num) |>.2 hn
  have hden : (0 : ℝ) < (n - n / 100 : ℕ) := by
    exact_mod_cast (by omega : 0 < n - n / 100)
  apply (div_le_iff₀ hden).2
  rw [Nat.cast_sub (Nat.div_le_self n 100)]
  push_cast
  have hcast : (100 : ℝ) * (n / 100 : ℕ) ≤ n := by exact_mod_cast hfloor
  have hqcast : (1 : ℝ) ≤ (n / 100 : ℕ) := by exact_mod_cast hq
  nlinarith

/-- Cast the full path along a decomposition `s+r=n` and take its terminal `r` pairs. -/
noncomputable def axisSuffixAlong {n : ℕ} (s r : ℕ) (h : s + r = n)
    (p : AxisGoodPath n) : AxisWord r :=
  axisSuffix (h.symm ▸ p)

lemma terminalTwoSidedFourthCount_axisSuffixAlong {n s r K : ℕ}
    (h : s + r = n) (p : AxisGoodPath n) (hK : K < 2 * r) :
    terminalTwoSidedFourthCount K (axisSuffixAlong s r h p) =
      fourthIntegratedCrossingCount (axisPathCoefficients p) K +
        fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K := by
  subst n
  simpa [axisSuffixAlong] using terminalTwoSidedFourthCount_axisSuffix p K hK

lemma goodPaths_suffix_mean_le_along {n : ℕ} (s r : ℕ) (h : s + r = n)
    (C : AxisWord r → ℕ) :
    (∑ p : AxisGoodPath n, (C (axisSuffixAlong s r h p) : ℝ)) /
        Fintype.card (AxisGoodPath n) ≤
      ((s + r + 1 : ℝ) / (s + 1 : ℝ)) *
        (∑ w : AxisWord r, (C w : ℝ)) / (4 : ℝ) ^ r := by
  subst n
  simpa [axisSuffixAlong] using goodPaths_suffix_mean_le s r C

set_option maxHeartbeats 5000000 in
/-- Exact analytic split gate.  It remains to prove (i) the standard iid logarithmic mean bound
with constant `0.378`, and (ii) that macroscopic cone-conditioned crossings contribute at most
`0.004 log n`. -/
theorem erdos_521_negative_of_fourthCrossing_split
    (hiid : ∀ᶠ n : ℕ in atTop,
      (∑ w : AxisWord (earlyPairBlock n),
          (terminalTwoSidedFourthCount (earlyFourthCutoff n) w : ℝ)) /
          (4 : ℝ) ^ earlyPairBlock n ≤
        (189 : ℝ) / 500 * Real.log (recordDegree n : ℝ))
    (hlate : ∀ᶠ n : ℕ in atTop,
      (∑ p : AxisGoodPath n,
          (lateAxisFourthCount (earlyFourthCutoff n) p : ℝ)) ≤
        (1 : ℝ) / 250 * Fintype.card (AxisGoodPath n) *
          Real.log (recordDegree n : ℝ)) :
    ¬ Claim := by
  apply erdos_521_negative_of_fourthCrossing_firstMoment
  filter_upwards [hiid, hlate, eventually_ge_atTop (100 : ℕ)] with n hiidn hlaten hn
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
        (50 : ℝ) / 49 * ((189 : ℝ) / 500 * Real.log (recordDegree n : ℝ)) *
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
          (50 : ℝ) / 49 * ((189 : ℝ) / 500 * Real.log (recordDegree n : ℝ)) := by
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
        _ ≤ (50 : ℝ) / 49 * ((189 : ℝ) / 500 *
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
    _ ≤ (50 : ℝ) / 49 * ((189 : ℝ) / 500 * Real.log (recordDegree n : ℝ)) *
          Fintype.card (AxisGoodPath n) +
        (1 : ℝ) / 250 * Fintype.card (AxisGoodPath n) *
          Real.log (recordDegree n : ℝ) := add_le_add hearly (by simpa [K] using hlaten)
    _ ≤ (39 : ℝ) / 100 * Fintype.card (AxisGoodPath n) *
          Real.log (recordDegree n : ℝ) := by
      have hcard : 0 ≤ (Fintype.card (AxisGoodPath n) : ℝ) := by positivity
      have hrec : 1 < (recordDegree n : ℝ) := by
        exact_mod_cast (by unfold recordDegree; omega : 1 < recordDegree n)
      have hlog : 0 < Real.log (recordDegree n : ℝ) := Real.log_pos hrec
      nlinarith

end Erdos521
