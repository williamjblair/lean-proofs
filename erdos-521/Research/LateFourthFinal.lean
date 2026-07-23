import Research.LateFourthSummation
import Research.SharpIidAnalyticGate
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

set_option maxHeartbeats 2000000

namespace Erdos521

noncomputable local instance lateFourthFinalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma lateSqrtLog_one_le (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ Real.sqrt (Real.log (2 * n + 1 : ℝ)) := by
  have h := fourthLate_log_one_le (2 * n - 2)
  have heq : 2 * n - 2 + 3 = 2 * n + 1 := by omega
  have heqR : (((2 * n - 2 : ℕ) : ℝ) + 3) = 2 * (n : ℝ) + 1 := by
    exact_mod_cast heq
  apply Real.one_le_sqrt.mpr
  rw [← heqR]
  exact h

lemma lateSqrtLog_mono {d n : ℕ} (hd : 1 ≤ d) (hdn : d ≤ 2 * n + 1) :
    Real.sqrt (Real.log (d : ℝ)) ≤ Real.sqrt (Real.log (2 * n + 1 : ℝ)) := by
  apply Real.sqrt_le_sqrt
  exact Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr (by exact_mod_cast hd))
    (Set.mem_Ioi.mpr (by positivity))
    (by exact_mod_cast hdn)

lemma twelve_div_fourth_le_sqrtLog_div (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    12 / (d : ℝ) ^ 4 ≤ 12 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd4 : (d : ℝ) ≤ (d : ℝ) ^ 4 := by
    calc
      (d : ℝ) = d * 1 := by ring
      _ ≤ d * d ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hdR) (by positivity)
      _ = d ^ 4 := by ring
  have hfirst : (12 : ℝ) / (d : ℝ) ^ 4 ≤ (12 : ℝ) / (d : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ 4)
      (by positivity : (0 : ℝ) < (d : ℝ))).2
    nlinarith
  have hL := lateSqrtLog_one_le n hn
  have hdpos : (0 : ℝ) < d := by positivity
  calc
    _ ≤ (12 : ℝ) / (d : ℝ) := hfirst
    _ ≤ (12 : ℝ) * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / (d : ℝ) := by
      apply div_le_div_of_nonneg_right _ hdpos.le
      nlinarith

lemma evenFourthIndicator_axisGood_simple_le (s m N0 : ℕ) (hm : 1 ≤ m)
    (hN0 : N0 ≤ 2 * m - 2)
    (hstrip : ∀ N, N0 ≤ N →
      fourthSignedStripProbability (N + 2) (3 * fourthLateCutoff N) ≤
        608000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ)) :
    (∑ p : AxisGoodPath (s + (m + 1)),
        (fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m) : ℝ)) /
        Nat.card (AxisGoodPath (s + (m + 1))) ≤
      80000000000 * Real.sqrt (Real.log (2 * (s + (m + 1)) + 1 : ℝ)) *
        Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) /
          (2 * m + 1 : ℝ) +
      64 * ((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) *
        Real.exp (-((s : ℝ) + ((m + 1 : ℕ) : ℝ)) / 8) := by
  have hedge := evenFourthIndicator_axisGood_mean_le s m hm
  have hs := hstrip (2 * m - 2) hN0
  have hN2 : 2 * m - 2 + 2 = 2 * m := by omega
  have hN3 : 2 * m - 2 + 3 = 2 * m + 1 := by omega
  have hN3R : (((2 * m - 2 : ℕ) : ℝ) + 3) = (2 * m + 1 : ℕ) := by
    exact_mod_cast hN3
  rw [hN2, hN3R] at hs
  let n := s + (m + 1)
  let d := 2 * m + 1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hdn : d ≤ 2 * n + 1 := by dsimp [d, n]; omega
  have hlog := lateSqrtLog_mono hd hdn
  have hpoly := twelve_div_fourth_le_sqrtLog_div d n hd hn
  have hbase :
      fourthSignedStripProbability (2 * m) (3 * fourthLateCutoff (2 * m - 2)) +
          12 / (2 * m + 1 : ℝ) ^ 4 ≤
        608000012 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := by
    have hbase' :
        fourthSignedStripProbability (2 * m) (3 * fourthLateCutoff (2 * m - 2)) +
            12 / (d : ℝ) ^ 4 ≤
          608000012 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := by
      have hdpos : (0 : ℝ) < d := by positivity
      have hlogdiv : 608000000 * Real.sqrt (Real.log (d : ℝ)) / d ≤
        608000000 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := by
        apply div_le_div_of_nonneg_right _ hdpos.le
        exact mul_le_mul_of_nonneg_left hlog (by norm_num)
      calc
        _ ≤ 608000000 * Real.sqrt (Real.log (d : ℝ)) / d +
            12 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := add_le_add hs hpoly
        _ ≤ 608000000 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d +
            12 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := add_le_add_left hlogdiv _
        _ = _ := by ring
    simpa [d] using hbase'
  have hfac : 0 ≤ Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) /
      (s + 1 : ℝ)) := Real.sqrt_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) hfac)
  dsimp [n, d] at hscaled ⊢
  have hterm : 0 ≤ Real.sqrt (Real.log (2 * (s + (m + 1)) + 1 : ℝ)) *
      Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) /
        (2 * m + 1 : ℝ) := by positivity
  exact hedge.trans (by
    calc
      _ ≤ 128 * Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
          (608000012 * Real.sqrt (Real.log (2 * (s + (m + 1)) + 1 : ℝ)) /
            (2 * m + 1 : ℝ)) +
        64 * ((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) *
          Real.exp (-((s : ℝ) + ((m + 1 : ℕ) : ℝ)) / 8) := by
        convert add_le_add_left hscaled
          (64 * ((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) *
            Real.exp (-((s : ℝ) + ((m + 1 : ℕ) : ℝ)) / 8)) using 1 <;>
          push_cast <;> rfl
      _ = 77824001536 * Real.sqrt (Real.log (2 * (s + (m + 1)) + 1 : ℝ)) *
          Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) /
            (2 * m + 1 : ℝ) +
        64 * ((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) *
          Real.exp (-((s : ℝ) + ((m + 1 : ℕ) : ℝ)) / 8) := by ring
      _ ≤ _ := by
        have hc := mul_le_mul_of_nonneg_right
          (show (77824001536 : ℝ) ≤ 80000000000 by norm_num) hterm
        have hc' :
            77824001536 * Real.sqrt (Real.log (2 * (s + (m + 1)) + 1 : ℝ)) *
                Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) /
                  (2 * m + 1 : ℝ) ≤
              80000000000 * Real.sqrt (Real.log (2 * (s + (m + 1)) + 1 : ℝ)) *
                Real.sqrt (((s : ℝ) + ((m + 1 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) /
                  (2 * m + 1 : ℝ) := by
          simpa only [div_eq_mul_inv, mul_assoc] using hc
        exact add_le_add_left hc' _)

lemma oddFourthIndicator_axisGood_simple_le (s m N0 : ℕ) (hm : 1 ≤ m)
    (hN0 : N0 ≤ 2 * m - 1)
    (hstrip : ∀ N, N0 ≤ N →
      fourthSignedStripProbability (N + 2) (3 * fourthLateCutoff N) ≤
        608000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ)) :
    (∑ p : AxisGoodPath (s + (m + 2)),
        (fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m + 1) : ℝ)) /
        Nat.card (AxisGoodPath (s + (m + 2))) ≤
      80000000000 * Real.sqrt (Real.log (2 * (s + (m + 2)) + 1 : ℝ)) *
        Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) /
          (2 * m + 2 : ℝ) +
      64 * ((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) *
        Real.exp (-((s : ℝ) + ((m + 2 : ℕ) : ℝ)) / 8) := by
  have hedge := oddFourthIndicator_axisGood_mean_le s m hm
  have hs := hstrip (2 * m - 1) hN0
  have hN2 : 2 * m - 1 + 2 = 2 * m + 1 := by omega
  have hN3 : 2 * m - 1 + 3 = 2 * m + 2 := by omega
  have hN3R : (((2 * m - 1 : ℕ) : ℝ) + 3) = (2 * m + 2 : ℕ) := by
    exact_mod_cast hN3
  rw [hN2, hN3R] at hs
  let n := s + (m + 2)
  let d := 2 * m + 2
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hdn : d ≤ 2 * n + 1 := by dsimp [d, n]; omega
  have hlog := lateSqrtLog_mono hd hdn
  have hpoly := twelve_div_fourth_le_sqrtLog_div d n hd hn
  have hbase :
      fourthSignedStripProbability (2 * m + 1) (3 * fourthLateCutoff (2 * m - 1)) +
          12 / (2 * m + 2 : ℝ) ^ 4 ≤
        608000012 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := by
    have hbase' :
        fourthSignedStripProbability (2 * m + 1) (3 * fourthLateCutoff (2 * m - 1)) +
            12 / (d : ℝ) ^ 4 ≤
          608000012 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := by
      have hdpos : (0 : ℝ) < d := by positivity
      have hlogdiv : 608000000 * Real.sqrt (Real.log (d : ℝ)) / d ≤
        608000000 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := by
        apply div_le_div_of_nonneg_right _ hdpos.le
        exact mul_le_mul_of_nonneg_left hlog (by norm_num)
      calc
        _ ≤ 608000000 * Real.sqrt (Real.log (d : ℝ)) / d +
            12 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := add_le_add hs hpoly
        _ ≤ 608000000 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d +
            12 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) / d := add_le_add_left hlogdiv _
        _ = _ := by ring
    simpa [d] using hbase'
  have hfac : 0 ≤ Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) /
      (s + 1 : ℝ)) := Real.sqrt_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) hfac)
  dsimp [n, d] at hscaled ⊢
  have hterm : 0 ≤ Real.sqrt (Real.log (2 * (s + (m + 2)) + 1 : ℝ)) *
      Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) /
        (2 * m + 2 : ℝ) := by positivity
  exact hedge.trans (by
    calc
      _ ≤ 128 * Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) *
          (608000012 * Real.sqrt (Real.log (2 * (s + (m + 2)) + 1 : ℝ)) /
            (2 * m + 2 : ℝ)) +
        64 * ((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) *
          Real.exp (-((s : ℝ) + ((m + 2 : ℕ) : ℝ)) / 8) := by
        convert add_le_add_left hscaled
          (64 * ((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) *
            Real.exp (-((s : ℝ) + ((m + 2 : ℕ) : ℝ)) / 8)) using 1 <;>
          push_cast <;> rfl
      _ = 77824001536 * Real.sqrt (Real.log (2 * (s + (m + 2)) + 1 : ℝ)) *
          Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) /
            (2 * m + 2 : ℝ) +
        64 * ((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) *
          Real.exp (-((s : ℝ) + ((m + 2 : ℕ) : ℝ)) / 8) := by ring
      _ ≤ _ := by
        have hc := mul_le_mul_of_nonneg_right
          (show (77824001536 : ℝ) ≤ 80000000000 by norm_num) hterm
        have hc' :
            77824001536 * Real.sqrt (Real.log (2 * (s + (m + 2)) + 1 : ℝ)) *
                Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) /
                  (2 * m + 2 : ℝ) ≤
              80000000000 * Real.sqrt (Real.log (2 * (s + (m + 2)) + 1 : ℝ)) *
                Real.sqrt (((s : ℝ) + ((m + 2 : ℕ) : ℝ) + 1) / (s + 1 : ℝ)) /
                  (2 * m + 2 : ℝ) := by
          simpa only [div_eq_mul_inv, mul_assoc] using hc
        exact add_le_add_left hc' _)

noncomputable def evenLateConditioningWeight (n m : ℕ) : ℝ :=
  Real.sqrt ((n + 1 : ℝ) / ((n - m : ℕ) : ℝ)) / (2 * m + 1 : ℝ)

noncomputable def oddLateConditioningWeight (n m : ℕ) : ℝ :=
  Real.sqrt ((n + 1 : ℝ) / ((n - m - 1 : ℕ) : ℝ)) / (2 * m + 2 : ℝ)

lemma earlyPairBlock_fifty_denominator_le (n m : ℕ) (hn : 1 ≤ n)
    (hm : earlyPairBlock n ≤ m) :
    (n : ℝ) / (2 * m + 1 : ℝ) ≤ 50 := by
  have hfloor : n < 100 * earlyPairBlock n := by
    unfold earlyPairBlock
    omega
  have hnat : n ≤ 50 * (2 * m + 1) := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < (2 * m + 1 : ℕ) := by positivity
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ) + 1)]
  exact_mod_cast hnat

lemma evenLateConditioningWeight_le {n m : ℕ} (hn : 1 ≤ n)
    (hm0 : earlyPairBlock n ≤ m) (hmn : m < n) :
    evenLateConditioningWeight n m ≤
      (50 / (n : ℝ)) * Real.sqrt (n + 1 : ℝ) *
        (1 / Real.sqrt ((n - m : ℕ) : ℝ)) := by
  have hratio := earlyPairBlock_fifty_denominator_le n m hn hm0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < (2 * m + 1 : ℕ) := by positivity
  have hinv : (1 : ℝ) / (2 * m + 1 : ℝ) ≤ 50 / n := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ) + 1) hnR]
    have hnat : n ≤ 50 * (2 * m + 1) := by
      have hfloor : n < 100 * earlyPairBlock n := by unfold earlyPairBlock; omega
      omega
    norm_num
    exact_mod_cast hnat
  have hnm : 0 ≤ (((n - m : ℕ) : ℝ)) := by positivity
  rw [evenLateConditioningWeight, Real.sqrt_div (by positivity)]
  calc
    _ = ((1 : ℝ) / (2 * m + 1 : ℝ)) *
        (Real.sqrt (n + 1 : ℝ) / Real.sqrt ((n - m : ℕ) : ℝ)) := by ring
    _ ≤ (50 / (n : ℝ)) *
        (Real.sqrt (n + 1 : ℝ) / Real.sqrt ((n - m : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_right hinv
      positivity
    _ = _ := by ring

lemma oddLateConditioningWeight_le {n m : ℕ} (hn : 1 ≤ n)
    (hm0 : earlyPairBlock n - 1 ≤ m) (hmn : m + 1 < n) :
    oddLateConditioningWeight n m ≤
      (50 / (n : ℝ)) * Real.sqrt (n + 1 : ℝ) *
        (1 / Real.sqrt ((n - m - 1 : ℕ) : ℝ)) := by
  have hm0' : earlyPairBlock n ≤ m + 1 := by omega
  have hratio := earlyPairBlock_fifty_denominator_le n (m + 1) hn hm0'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < (2 * m + 2 : ℕ) := by positivity
  have hnat : n ≤ 50 * (2 * m + 2) := by
    have hfloor : n < 100 * earlyPairBlock n := by unfold earlyPairBlock; omega
    omega
  have hinv : (1 : ℝ) / (2 * m + 2 : ℝ) ≤ 50 / n := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ) + 2) hnR]
    norm_num
    exact_mod_cast hnat
  rw [oddLateConditioningWeight, Real.sqrt_div (by positivity)]
  calc
    _ = ((1 : ℝ) / (2 * m + 2 : ℝ)) *
        (Real.sqrt (n + 1 : ℝ) / Real.sqrt ((n - m - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (50 / (n : ℝ)) *
        (Real.sqrt (n + 1 : ℝ) / Real.sqrt ((n - m - 1 : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_right hinv
      positivity
    _ = _ := by ring

lemma sum_even_inverse_sqrt_reflect (n : ℕ) :
    (∑ m ∈ Finset.range n, (1 : ℝ) / Real.sqrt ((n - m : ℕ) : ℝ)) =
      ∑ j ∈ Finset.range n, (1 : ℝ) / Real.sqrt (j + 1 : ℝ) := by
  have h := Finset.sum_range_reflect
    (fun j ↦ (1 : ℝ) / Real.sqrt (j + 1 : ℝ)) n
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  congr 3
  exact_mod_cast (by omega : n - j = (n - 1 - j) + 1)

lemma sum_odd_inverse_sqrt_reflect (n : ℕ) :
    (∑ m ∈ Finset.range (n - 1),
      (1 : ℝ) / Real.sqrt ((n - m - 1 : ℕ) : ℝ)) =
      ∑ j ∈ Finset.range (n - 1), (1 : ℝ) / Real.sqrt (j + 1 : ℝ) := by
  have h := Finset.sum_range_reflect
    (fun j ↦ (1 : ℝ) / Real.sqrt (j + 1 : ℝ)) (n - 1)
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  congr 3
  exact_mod_cast (by omega : n - j - 1 = (n - 1 - 1 - j) + 1)

lemma evenFourthIndicator_fixedLength_simple_le (n m N0 : ℕ)
    (hm : 1 ≤ m) (hr : m + 1 ≤ n) (hN0 : N0 ≤ 2 * m - 2)
    (hstrip : ∀ N, N0 ≤ N →
      fourthSignedStripProbability (N + 2) (3 * fourthLateCutoff N) ≤
        608000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ)) :
    (∑ p : AxisGoodPath n,
        (fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m) : ℝ)) /
        Nat.card (AxisGoodPath n) ≤
      80000000000 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) *
        evenLateConditioningWeight n m +
      64 * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) := by
  let s := n - (m + 1)
  have hsr : s + (m + 1) = n := by dsimp [s]; omega
  have hsden : s + 1 = n - m := by dsimp [s]; omega
  have h := evenFourthIndicator_axisGood_simple_le s m N0 hm hN0 hstrip
  rw [hsr] at h
  have hsrR : (s : ℝ) + ((m + 1 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hsr
  have hsdenR : (s : ℝ) + 1 = ((n - m : ℕ) : ℝ) := by exact_mod_cast hsden
  push_cast at hsrR
  rw [hsrR, hsdenR] at h
  simpa [evenLateConditioningWeight, hsrR, hsdenR, div_eq_mul_inv, mul_assoc] using h

lemma oddFourthIndicator_fixedLength_simple_le (n m N0 : ℕ)
    (hm : 1 ≤ m) (hr : m + 2 ≤ n) (hN0 : N0 ≤ 2 * m - 1)
    (hstrip : ∀ N, N0 ≤ N →
      fourthSignedStripProbability (N + 2) (3 * fourthLateCutoff N) ≤
        608000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ)) :
    (∑ p : AxisGoodPath n,
        (fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m + 1) : ℝ)) /
        Nat.card (AxisGoodPath n) ≤
      80000000000 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) *
        oddLateConditioningWeight n m +
      64 * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) := by
  let s := n - (m + 2)
  have hsr : s + (m + 2) = n := by dsimp [s]; omega
  have hsden : s + 1 = n - m - 1 := by dsimp [s]; omega
  have h := oddFourthIndicator_axisGood_simple_le s m N0 hm hN0 hstrip
  rw [hsr] at h
  have hsrR : (s : ℝ) + ((m + 2 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hsr
  have hsdenR : (s : ℝ) + 1 = ((n - m - 1 : ℕ) : ℝ) := by exact_mod_cast hsden
  push_cast at hsrR
  rw [hsrR, hsdenR] at h
  simpa [oddLateConditioningWeight, hsrR, hsdenR, div_eq_mul_inv, mul_assoc] using h

lemma sum_Ico_odd_bounds_split {R S : ℕ} (hRS : R ≤ S) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Ico (2 * R + 1) (2 * S + 1), f k) =
      (∑ m ∈ Finset.Ico (R + 1) (S + 1), f (2 * m)) +
        ∑ m ∈ Finset.Ico R S, f (2 * m + 1) := by
  rw [Finset.sum_Ico_eq_sub f (by omega),
    sum_range_two_mul_add_one f S, sum_range_two_mul_add_one f R]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_Ico_eq_sub (fun m ↦ f (2 * m)) (by omega : R + 1 ≤ S + 1),
    Finset.sum_Ico_eq_sub (fun m ↦ f (2 * m + 1)) hRS]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  ring

lemma lateConditioningWeight_sum_le (n : ℕ) (hn : 100 ≤ n) :
    (∑ m ∈ Finset.Ico (earlyPairBlock n) (n - 2),
        evenLateConditioningWeight n m) +
      (∑ m ∈ Finset.Ico (earlyPairBlock n - 1) (n - 3),
        oddLateConditioningWeight n m) ≤ 400 := by
  let C : ℝ := (50 / (n : ℝ)) * Real.sqrt (n + 1 : ℝ)
  have hn1 : 1 ≤ n := by omega
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have heven : (∑ m ∈ Finset.Ico (earlyPairBlock n) (n - 2),
      evenLateConditioningWeight n m) ≤
      C * ∑ m ∈ Finset.range n,
        (1 / Real.sqrt ((n - m : ℕ) : ℝ)) := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico (earlyPairBlock n) (n - 2),
          C * (1 / Real.sqrt ((n - m : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro m hm
        have hm' := Finset.mem_Ico.mp hm
        exact evenLateConditioningWeight_le hn1 hm'.1 (by omega)
      _ ≤ ∑ m ∈ Finset.range n,
          C * (1 / Real.sqrt ((n - m : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢
          omega
        · intro i hi hnot
          positivity
      _ = _ := by rw [Finset.mul_sum]
  have hodd : (∑ m ∈ Finset.Ico (earlyPairBlock n - 1) (n - 3),
      oddLateConditioningWeight n m) ≤
      C * ∑ m ∈ Finset.range (n - 1),
        (1 / Real.sqrt ((n - m - 1 : ℕ) : ℝ)) := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico (earlyPairBlock n - 1) (n - 3),
          C * (1 / Real.sqrt ((n - m - 1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro m hm
        have hm' := Finset.mem_Ico.mp hm
        exact oddLateConditioningWeight_le hn1 hm'.1 (by omega)
      _ ≤ ∑ m ∈ Finset.range (n - 1),
          C * (1 / Real.sqrt ((n - m - 1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢
          omega
        · intro i hi hnot
          positivity
      _ = _ := by rw [Finset.mul_sum]
  rw [sum_even_inverse_sqrt_reflect] at heven
  rw [sum_odd_inverse_sqrt_reflect] at hodd
  have hsumN := sum_range_one_div_sqrt_succ_le n
  have hsumN1 := sum_range_one_div_sqrt_succ_le (n - 1)
  have hsqrtRatio : Real.sqrt (n + 1 : ℝ) * Real.sqrt (n : ℝ) ≤
      2 * (n : ℝ) := by
    have hs1 : Real.sqrt (n + 1 : ℝ) ≤ Real.sqrt (2 * n : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast (by omega : n + 1 ≤ 2 * n)
    have hs2 : Real.sqrt (2 * n : ℝ) * Real.sqrt (n : ℝ) =
        Real.sqrt 2 * (n : ℝ) := by
      rw [Real.sqrt_mul (by positivity)]
      calc
        Real.sqrt 2 * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) =
            Real.sqrt 2 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (by positivity)]
    have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ Real.sqrt (2 * n : ℝ) * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_right hs1 (Real.sqrt_nonneg _)
      _ = Real.sqrt 2 * n := hs2
      _ ≤ 2 * n := mul_le_mul_of_nonneg_right hsqrt2 (by positivity)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hCN : C * (2 * Real.sqrt (n : ℝ)) ≤ 200 := by
    dsimp [C]
    calc
      (50 / (n : ℝ)) * Real.sqrt (n + 1 : ℝ) * (2 * Real.sqrt (n : ℝ)) =
          (100 * (Real.sqrt (n + 1 : ℝ) * Real.sqrt (n : ℝ))) / n := by ring
      _ ≤ 200 := (div_le_iff₀ hnR).2 (by nlinarith [hsqrtRatio])
  have hcastsub : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcastsub] at hsumN1
  have hCN1 : C * (2 * Real.sqrt (n - 1 : ℝ)) ≤ 200 := by
    have hs : Real.sqrt (n - 1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    calc
      _ ≤ C * (2 * Real.sqrt (n : ℝ)) := by gcongr
      _ ≤ 200 := hCN
  calc
    _ ≤ C * (∑ j ∈ Finset.range n, (1 : ℝ) / Real.sqrt (j + 1 : ℝ)) +
        C * (∑ j ∈ Finset.range (n - 1), (1 : ℝ) / Real.sqrt (j + 1 : ℝ)) :=
      add_le_add heven hodd
    _ ≤ C * (2 * Real.sqrt (n : ℝ)) + C * (2 * Real.sqrt (n - 1 : ℝ)) := by
      gcongr
    _ ≤ 400 := by linarith

noncomputable def axisFourthEdgeMean (n k : ℕ) : ℝ :=
  (∑ p : AxisGoodPath n,
    (fourthIntegratedCrossingIndicator (axisPathCoefficients p) k : ℝ)) /
      Nat.card (AxisGoodPath n)

lemma normalized_fourthCrossingCount_sub_eq_edgeSum (n K M : ℕ) (hKM : K ≤ M) :
    (∑ p : AxisGoodPath n,
      ((fourthIntegratedCrossingCount (axisPathCoefficients p) M -
        fourthIntegratedCrossingCount (axisPathCoefficients p) K : ℕ) : ℝ)) /
        Nat.card (AxisGoodPath n) =
      ∑ k ∈ Finset.Ico K M, axisFourthEdgeMean n k := by
  calc
    _ = (∑ p : AxisGoodPath n, ∑ k ∈ Finset.Ico K M,
        (fourthIntegratedCrossingIndicator (axisPathCoefficients p) k : ℝ)) /
          Nat.card (AxisGoodPath n) := by
      apply congrArg (fun z : ℝ ↦ z / Nat.card (AxisGoodPath n))
      apply Finset.sum_congr rfl
      intro p hp
      rw [fourthIntegratedCrossingCount_sub _ hKM]
      push_cast
      rfl
    _ = (∑ k ∈ Finset.Ico K M, ∑ p : AxisGoodPath n,
        (fourthIntegratedCrossingIndicator (axisPathCoefficients p) k : ℝ)) /
          Nat.card (AxisGoodPath n) := by rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_div]
      rfl

lemma normalized_oddTwist_fourthCrossingCount_sub_eq_edgeSum (n K M : ℕ) (hKM : K ≤ M) :
    (∑ p : AxisGoodPath n,
      ((fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) M -
        fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K : ℕ) : ℝ)) /
        Nat.card (AxisGoodPath n) =
      ∑ k ∈ Finset.Ico K M,
        ((∑ p : AxisGoodPath n,
          (fourthIntegratedCrossingIndicator (oddTwist (axisPathCoefficients p)) k : ℝ)) /
            Nat.card (AxisGoodPath n)) := by
  calc
    _ = (∑ p : AxisGoodPath n, ∑ k ∈ Finset.Ico K M,
        (fourthIntegratedCrossingIndicator (oddTwist (axisPathCoefficients p)) k : ℝ)) /
          Nat.card (AxisGoodPath n) := by
      apply congrArg (fun z : ℝ ↦ z / Nat.card (AxisGoodPath n))
      apply Finset.sum_congr rfl
      intro p hp
      rw [fourthIntegratedCrossingCount_sub _ hKM]
      push_cast
      rfl
    _ = (∑ k ∈ Finset.Ico K M, ∑ p : AxisGoodPath n,
        (fourthIntegratedCrossingIndicator (oddTwist (axisPathCoefficients p)) k : ℝ)) /
          Nat.card (AxisGoodPath n) := by rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_div]

noncomputable def oddTwistAxisFourthEdgeMean (n k : ℕ) : ℝ :=
  (∑ p : AxisGoodPath n,
    (fourthIntegratedCrossingIndicator (oddTwist (axisPathCoefficients p)) k : ℝ)) /
      Nat.card (AxisGoodPath n)

lemma even_oddTwistAxisFourthEdgeMean_eq (n m : ℕ) (hr : m + 1 ≤ n) :
    oddTwistAxisFourthEdgeMean n (2 * m) = axisFourthEdgeMean n (2 * m) := by
  let s := n - (m + 1)
  have hsr : s + (m + 1) = n := by dsimp [s]; omega
  have hsum :
      (∑ p : AxisGoodPath (s + (m + 1)),
        (fourthIntegratedCrossingIndicator (oddTwist (axisPathCoefficients p)) (2 * m) : ℝ)) =
      ∑ p : AxisGoodPath (s + (m + 1)),
        (fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m) : ℝ) := by
    calc
      _ = ∑ p : AxisGoodPath (s + (m + 1)),
          (fourthIntegratedCrossingIndicator
            (axisPathCoefficients (rotateAxisGoodPath p)) (2 * m) : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact_mod_cast fourthIndicator_even_oddTwist_rotate (s := s) (r := m + 1)
          (by omega) p
      _ = _ := (rotateAxisGoodEquiv (s + (m + 1))).sum_comp
        (fun p ↦ (fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m) : ℝ))
  rw [hsr] at hsum
  exact congrArg (fun z : ℝ ↦ z / Nat.card (AxisGoodPath n)) hsum

lemma odd_oddTwistAxisFourthEdgeMean_eq (n m : ℕ) (hr : m + 2 ≤ n) :
    oddTwistAxisFourthEdgeMean n (2 * m + 1) = axisFourthEdgeMean n (2 * m + 1) := by
  let s := n - (m + 2)
  have hsr : s + (m + 2) = n := by dsimp [s]; omega
  have hsum :
      (∑ p : AxisGoodPath (s + (m + 2)),
        (fourthIntegratedCrossingIndicator (oddTwist (axisPathCoefficients p)) (2 * m + 1) : ℝ)) =
      ∑ p : AxisGoodPath (s + (m + 2)),
        (fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m + 1) : ℝ) := by
    calc
      _ = ∑ p : AxisGoodPath (s + (m + 2)),
          (fourthIntegratedCrossingIndicator
            (axisPathCoefficients (rotateAxisGoodPath p)) (2 * m + 1) : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact_mod_cast fourthIndicator_odd_oddTwist_rotate (s := s) (r := m + 2)
          (by omega) p
      _ = _ := (rotateAxisGoodEquiv (s + (m + 2))).sum_comp
        (fun p ↦ (fourthIntegratedCrossingIndicator (axisPathCoefficients p) (2 * m + 1) : ℝ))
  rw [hsr] at hsum
  exact congrArg (fun z : ℝ ↦ z / Nat.card (AxisGoodPath n)) hsum

lemma untwistedLateEdgeMean_le (N0 n : ℕ) (hn : 100 ≤ n)
    (hlarge : 100 * (N0 + 2) ≤ n)
    (hstrip : ∀ N, N0 ≤ N →
      fourthSignedStripProbability (N + 2) (3 * fourthLateCutoff N) ≤
        608000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ)) :
    (∑ k ∈ Finset.Ico (earlyFourthCutoff n) (2 * n - 5), axisFourthEdgeMean n k) ≤
      32000000000000 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) +
        128 * (n : ℝ) * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) := by
  let r0 := earlyPairBlock n
  let L := Real.sqrt (Real.log (2 * n + 1 : ℝ))
  let err := 64 * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8)
  have hr0 : 1 ≤ r0 := by dsimp [r0]; exact earlyPairBlock_pos n
  have hrn : r0 ≤ n - 2 := by dsimp [r0, earlyPairBlock]; omega
  have hRS : r0 - 1 ≤ n - 3 := by omega
  have hsplit := sum_Ico_odd_bounds_split (R := r0 - 1) (S := n - 3) hRS
    (axisFourthEdgeMean n)
  have hK : 2 * (r0 - 1) + 1 = earlyFourthCutoff n := by
    dsimp [r0, earlyFourthCutoff]
    omega
  have hM : 2 * (n - 3) + 1 = 2 * n - 5 := by omega
  have hevenEach : ∀ m ∈ Finset.Ico r0 (n - 2),
      axisFourthEdgeMean n (2 * m) ≤
        80000000000 * L * evenLateConditioningWeight n m + err := by
    intro m hmemb
    have hmI := Finset.mem_Ico.mp hmemb
    have hm1 : 1 ≤ m := hr0.trans hmI.1
    have hr : m + 1 ≤ n := by omega
    have hN0 : N0 ≤ 2 * m - 2 := by
      dsimp [r0, earlyPairBlock] at hmI
      have hq : N0 + 2 ≤ n / 100 := by omega
      omega
    simpa [axisFourthEdgeMean, L, err] using
      evenFourthIndicator_fixedLength_simple_le n m N0 hm1 hr hN0 hstrip
  have hoddEach : ∀ m ∈ Finset.Ico (r0 - 1) (n - 3),
      axisFourthEdgeMean n (2 * m + 1) ≤
        80000000000 * L * oddLateConditioningWeight n m + err := by
    intro m hmemb
    have hmI := Finset.mem_Ico.mp hmemb
    have hm1 : 1 ≤ m := by
      dsimp [r0, earlyPairBlock] at hmI
      have hq : N0 + 2 ≤ n / 100 := by omega
      omega
    have hr : m + 2 ≤ n := by omega
    have hN0 : N0 ≤ 2 * m - 1 := by
      dsimp [r0, earlyPairBlock] at hmI
      have hq : N0 + 2 ≤ n / 100 := by omega
      omega
    simpa [axisFourthEdgeMean, L, err] using
      oddFourthIndicator_fixedLength_simple_le n m N0 hm1 hr hN0 hstrip
  have heven : (∑ m ∈ Finset.Ico r0 (n - 2), axisFourthEdgeMean n (2 * m)) ≤
      80000000000 * L *
          (∑ m ∈ Finset.Ico r0 (n - 2), evenLateConditioningWeight n m) +
        (Finset.Ico r0 (n - 2)).card * err := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico r0 (n - 2),
          (80000000000 * L * evenLateConditioningWeight n m + err) := by
        apply Finset.sum_le_sum
        intro m hm
        exact hevenEach m hm
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
  have hodd : (∑ m ∈ Finset.Ico (r0 - 1) (n - 3), axisFourthEdgeMean n (2 * m + 1)) ≤
      80000000000 * L *
          (∑ m ∈ Finset.Ico (r0 - 1) (n - 3), oddLateConditioningWeight n m) +
        (Finset.Ico (r0 - 1) (n - 3)).card * err := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico (r0 - 1) (n - 3),
          (80000000000 * L * oddLateConditioningWeight n m + err) := by
        apply Finset.sum_le_sum
        intro m hm
        exact hoddEach m hm
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
  have hw := lateConditioningWeight_sum_le n hn
  have hcards : (Finset.Ico r0 (n - 2)).card +
      (Finset.Ico (r0 - 1) (n - 3)).card ≤ 2 * n := by
    rw [Nat.card_Ico, Nat.card_Ico]
    omega
  have hrid : r0 - 1 + 1 = r0 := by omega
  have hnid : n - 3 + 1 = n - 2 := by omega
  rw [hrid, hnid] at hsplit
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have herr : 0 ≤ err := by dsimp [err]; positivity
  rw [← hK, ← hM, hsplit]
  calc
    _ ≤ (80000000000 * L *
          (∑ m ∈ Finset.Ico r0 (n - 2), evenLateConditioningWeight n m) +
        (Finset.Ico r0 (n - 2)).card * err) +
      (80000000000 * L *
          (∑ m ∈ Finset.Ico (r0 - 1) (n - 3), oddLateConditioningWeight n m) +
        (Finset.Ico (r0 - 1) (n - 3)).card * err) := add_le_add heven hodd
    _ = 80000000000 * L *
          ((∑ m ∈ Finset.Ico r0 (n - 2), evenLateConditioningWeight n m) +
            ∑ m ∈ Finset.Ico (r0 - 1) (n - 3), oddLateConditioningWeight n m) +
        ((Finset.Ico r0 (n - 2)).card +
          (Finset.Ico (r0 - 1) (n - 3)).card) * err := by push_cast; ring
    _ ≤ 80000000000 * L * 400 + (2 * n : ℕ) * err := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num) hL)
      · apply mul_le_mul_of_nonneg_right _ herr
        exact_mod_cast hcards
    _ = 32000000000000 * L + 128 * (n : ℝ) * (n + 1 : ℝ) *
        Real.exp (-(n : ℝ) / 8) := by
      dsimp [err]
      push_cast
      ring

lemma normalized_oddTwist_fourthCrossingCount_sub_eq_twistEdgeSum
    (n K M : ℕ) (hKM : K ≤ M) :
    (∑ p : AxisGoodPath n,
      ((fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) M -
        fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K : ℕ) : ℝ)) /
        Nat.card (AxisGoodPath n) =
      ∑ k ∈ Finset.Ico K M, oddTwistAxisFourthEdgeMean n k := by
  simpa [oddTwistAxisFourthEdgeMean] using
    normalized_oddTwist_fourthCrossingCount_sub_eq_edgeSum n K M hKM

lemma oddTwistLateEdgeSum_eq (n : ℕ) (hn : 100 ≤ n) :
    (∑ k ∈ Finset.Ico (earlyFourthCutoff n) (2 * n - 5),
      oddTwistAxisFourthEdgeMean n k) =
      ∑ k ∈ Finset.Ico (earlyFourthCutoff n) (2 * n - 5), axisFourthEdgeMean n k := by
  let r0 := earlyPairBlock n
  have hRS : r0 - 1 ≤ n - 3 := by dsimp [r0, earlyPairBlock]; omega
  have hU := sum_Ico_odd_bounds_split (R := r0 - 1) (S := n - 3) hRS
    (axisFourthEdgeMean n)
  have hT := sum_Ico_odd_bounds_split (R := r0 - 1) (S := n - 3) hRS
    (oddTwistAxisFourthEdgeMean n)
  have hrpos : 0 < r0 := by dsimp [r0]; exact earlyPairBlock_pos n
  have hK : 2 * (r0 - 1) + 1 = earlyFourthCutoff n := by
    dsimp [earlyFourthCutoff]
    omega
  have hM : 2 * (n - 3) + 1 = 2 * n - 5 := by omega
  have hrid : r0 - 1 + 1 = r0 := by omega
  have hnid : n - 3 + 1 = n - 2 := by omega
  rw [hrid, hnid, hK, hM] at hU hT
  rw [hT, hU]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    have hmI := Finset.mem_Ico.mp hm
    rw [even_oddTwistAxisFourthEdgeMean_eq n m (by omega)]
  · apply Finset.sum_congr rfl
    intro m hm
    have hmI := Finset.mem_Ico.mp hm
    rw [odd_oddTwistAxisFourthEdgeMean_eq n m (by omega)]

lemma lateAxisFourthMean_normalized_le (N0 n : ℕ) (hn : 100 ≤ n)
    (hlarge : 100 * (N0 + 2) ≤ n)
    (hstrip : ∀ N, N0 ≤ N →
      fourthSignedStripProbability (N + 2) (3 * fourthLateCutoff N) ≤
        608000000 * Real.sqrt (Real.log (N + 3 : ℝ)) / (N + 3 : ℝ)) :
    (∑ p : AxisGoodPath n,
      (lateAxisFourthCount (earlyFourthCutoff n) p : ℝ)) /
        Nat.card (AxisGoodPath n) ≤
      64000000000000 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) +
        256 * (n : ℝ) * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) := by
  let K := earlyFourthCutoff n
  let M := 2 * n - 5
  have hKM : K ≤ M := earlyFourthCutoff_le_full n (by omega)
  have hU := normalized_fourthCrossingCount_sub_eq_edgeSum n K M hKM
  have hT := normalized_oddTwist_fourthCrossingCount_sub_eq_twistEdgeSum n K M hKM
  have htwist := oddTwistLateEdgeSum_eq n hn
  have hbound := untwistedLateEdgeMean_le N0 n hn hlarge hstrip
  have hdecomp :
      (∑ p : AxisGoodPath n, (lateAxisFourthCount K p : ℝ)) /
          Nat.card (AxisGoodPath n) =
        (∑ p : AxisGoodPath n,
          ((fourthIntegratedCrossingCount (axisPathCoefficients p) M -
            fourthIntegratedCrossingCount (axisPathCoefficients p) K : ℕ) : ℝ)) /
            Nat.card (AxisGoodPath n) +
        (∑ p : AxisGoodPath n,
          ((fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) M -
            fourthIntegratedCrossingCount (oddTwist (axisPathCoefficients p)) K : ℕ) : ℝ)) /
            Nat.card (AxisGoodPath n) := by
    unfold lateAxisFourthCount
    dsimp [M]
    push_cast
    rw [Finset.sum_add_distrib]
    ring
  rw [hdecomp, hU, hT, show K = earlyFourthCutoff n from rfl,
    show M = 2 * n - 5 from rfl, htwist]
  nlinarith

lemma recordDegree_tendsto_atTop : Tendsto recordDegree atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b + 1)] with n hn
  unfold recordDegree
  omega

lemma log_recordDegree_tendsto_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (recordDegree n : ℝ)) atTop atTop := by
  apply Real.tendsto_log_atTop.comp
  exact tendsto_natCast_atTop_iff.mpr recordDegree_tendsto_atTop

lemma latePolynomialExp_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      256 * (n : ℝ) * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h2r := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) (1 / 8 : ℝ)
    (by norm_num)).comp hn
  have h1r := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1 / 8 : ℝ)
    (by norm_num)).comp hn
  have h2 : Tendsto (fun n : ℕ ↦
      (n : ℝ) ^ 2 * Real.exp (-(n : ℝ) / 8)) atTop (𝓝 0) := by
    convert h2r using 1
    funext n
    dsimp only [Function.comp_apply]
    rw [Real.rpow_two]
    congr 1
    apply congrArg Real.exp
    ring
  have h1 : Tendsto (fun n : ℕ ↦
      (n : ℝ) * Real.exp (-(n : ℝ) / 8)) atTop (𝓝 0) := by
    convert h1r using 1
    funext n
    dsimp only [Function.comp_apply]
    rw [Real.rpow_one]
    apply congrArg (fun z ↦ (n : ℝ) * Real.exp z)
    ring
  have hsum := h2.add h1
  have hmul := hsum.const_mul (256 : ℝ)
  norm_num at hmul
  convert hmul using 1
  funext n
  ring

lemma lateAnalyticBound_le_log (n : ℕ) (hn : 100 ≤ n)
    (hloglarge : (1280000000000000 : ℝ) ^ 2 ≤
      Real.log (recordDegree n : ℝ))
    (hexp : 256 * (n : ℝ) * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) ≤ 1) :
    64000000000000 * Real.sqrt (Real.log (2 * n + 1 : ℝ)) +
        256 * (n : ℝ) * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) ≤
      (23 : ℝ) / 100 * Real.log (recordDegree n : ℝ) := by
  let x := Real.log (recordDegree n : ℝ)
  let y := Real.sqrt x
  let z := Real.sqrt (Real.log (2 * n + 1 : ℝ))
  have hrec : 1 < (recordDegree n : ℝ) := by
    exact_mod_cast (by unfold recordDegree; omega : 1 < recordDegree n)
  have hx : 0 < x := by dsimp [x]; exact Real.log_pos hrec
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hy2 : y ^ 2 = x := Real.sq_sqrt hx.le
  have harg : (2 * n + 1 : ℝ) ≤ (recordDegree n : ℝ) ^ 2 := by
    unfold recordDegree
    rw [Nat.cast_sub (by omega)]
    push_cast
    have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hlog : Real.log (2 * n + 1 : ℝ) ≤ 2 * x := by
    have hpos : (0 : ℝ) < 2 * n + 1 := by positivity
    have hle := Real.log_le_log hpos harg
    rw [Real.log_pow] at hle
    dsimp [x]
    norm_num at hle ⊢
    exact hle
  have hz2 : z ^ 2 = Real.log (2 * n + 1 : ℝ) := by
    apply Real.sq_sqrt
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * n + 1))
  have hzy : z ≤ 2 * y := by nlinarith
  have hBy : (1280000000000000 : ℝ) ≤ y := by
    dsimp [x] at hy2
    nlinarith
  have hmain : 64000000000000 * z ≤ x / 10 := by
    nlinarith
  have hexp' :
      256 * (n : ℝ) * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) ≤ x / 100 := by
    have hx100 : (100 : ℝ) ≤ x := by
      dsimp [x] at hloglarge ⊢
      nlinarith
    nlinarith
  dsimp [x, z] at hmain hexp' ⊢
  nlinarith

lemma eventually_lateAxisFourthMean_normalized :
    ∀ᶠ n : ℕ in atTop,
      (∑ p : AxisGoodPath n,
        (lateAxisFourthCount (earlyFourthCutoff n) p : ℝ)) /
          Nat.card (AxisGoodPath n) ≤
        (23 : ℝ) / 100 * Real.log (recordDegree n : ℝ) := by
  obtain ⟨N0, hstrip⟩ := (eventually_atTop.1 eventually_fourthSignedLateStrip_rate)
  have hloglarge := (Filter.tendsto_atTop.1 log_recordDegree_tendsto_atTop)
    ((1280000000000000 : ℝ) ^ 2)
  have hexp : ∀ᶠ n : ℕ in atTop,
      256 * (n : ℝ) * (n + 1 : ℝ) * Real.exp (-(n : ℝ) / 8) ≤ 1 := by
    have ht := (tendsto_order.1 latePolynomialExp_tendsto_zero).2 (1 : ℝ) (by norm_num)
    exact ht.mono (fun n hn ↦ hn.le)
  filter_upwards [hloglarge, hexp, eventually_ge_atTop (100 * (N0 + 2))]
    with n hlogn hexpn hn
  have hn100 : 100 ≤ n := by omega
  exact (lateAxisFourthMean_normalized_le N0 n hn100 hn
    (fun N hN ↦ hstrip N hN)).trans (lateAnalyticBound_le_log n hn100 hlogn hexpn)

lemma eventual_lateAxisFourthMean_gate :
    ∀ᶠ n : ℕ in atTop,
      (∑ p : AxisGoodPath n,
          (lateAxisFourthCount (earlyFourthCutoff n) p : ℝ)) ≤
        (23 : ℝ) / 100 * Fintype.card (AxisGoodPath n) *
          Real.log (recordDegree n : ℝ) := by
  filter_upwards [eventually_lateAxisFourthMean_normalized] with n hn
  have hcard : (0 : ℝ) < Nat.card (AxisGoodPath n) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast card_axisGoodPath_pos n
  have h := (div_le_iff₀ hcard).mp hn
  rw [Nat.card_eq_fintype_card] at h
  nlinarith

/-- Negative answer to Erdős Problem 521. -/
theorem erdos_521_negative : ¬ Claim :=
  erdos_521_negative_of_sharpIid_and_late eventual_lateAxisFourthMean_gate

end Erdos521
