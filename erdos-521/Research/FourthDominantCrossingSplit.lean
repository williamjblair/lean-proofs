import Research.FourthPairDecomposition
import Research.DominantCrossingSplit
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable def fourthHorizontalOdd (ω : ℕ → Bool) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ((Nat.choose (2 * (m - j) + 4) 3 +
      Nat.choose (2 * (m - j) + 3) 3 : ℕ) : ℝ) * pairHorizontal ω j

noncomputable def fourthVerticalOdd (ω : ℕ → Bool) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (Nat.choose (2 * (m - j) + 3) 2 : ℝ) * pairVertical ω j

noncomputable def fourthHorizontalEven (ω : ℕ → Bool) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ((Nat.choose (2 * (m - j) + 3) 3 +
      Nat.choose (2 * (m - j) + 2) 3 : ℕ) : ℝ) * pairHorizontal ω j

noncomputable def fourthVerticalEven (ω : ℕ → Bool) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (Nat.choose (2 * (m - j) + 2) 2 : ℝ) * pairVertical ω j

lemma fourthSum_odd_eq_horizontal_sub_vertical (ω : ℕ → Bool) (m : ℕ) :
    fourthIntegratedRademacherSum ω (2 * m + 1) =
      fourthHorizontalOdd ω m - fourthVerticalOdd ω m := by
  rw [fourthIntegratedRademacherSum_odd_pair]
  unfold fourthHorizontalOdd fourthVerticalOdd
  rw [← Finset.sum_sub_distrib]

lemma fourthSum_even_eq_horizontal_sub_vertical (ω : ℕ → Bool) (m : ℕ) :
    fourthIntegratedRademacherSum ω (2 * m) =
      fourthHorizontalEven ω m - fourthVerticalEven ω m := by
  rw [fourthIntegratedRademacherSum_even_pair]
  unfold fourthHorizontalEven fourthVerticalEven
  rw [← Finset.sum_sub_distrib]

/-- At an even edge, a fourth crossing forces a small horizontal cubic form or a large horizontal
quadratic increment / vertical quadratic perturbation. -/
lemma fourth_even_crossing_threshold_split (ω : ℕ → Bool) (m : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hcross : fourthIntegratedRademacherSum ω (2 * m) *
      fourthIntegratedRademacherSum ω (2 * m + 1) ≤ 0) :
    |fourthHorizontalEven ω m| ≤ 2 * T ∨
      T ≤ |fourthHorizontalOdd ω m - fourthHorizontalEven ω m| ∨
      T ≤ |fourthVerticalEven ω m| ∨
      T ≤ |fourthVerticalOdd ω m| := by
  rw [fourthSum_even_eq_horizontal_sub_vertical,
    fourthSum_odd_eq_horizontal_sub_vertical] at hcross
  have h := dominant_crossing_threshold_split
    (H := fourthHorizontalEven ω m)
    (J := fourthHorizontalOdd ω m - fourthHorizontalEven ω m)
    (P := fourthVerticalEven ω m) (P' := fourthVerticalOdd ω m) hT
  apply h
  convert hcross using 1 <;> ring

/-- The analogous split at an odd edge. -/
lemma fourth_odd_crossing_threshold_split (ω : ℕ → Bool) (m : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hcross : fourthIntegratedRademacherSum ω (2 * m + 1) *
      fourthIntegratedRademacherSum ω (2 * m + 2) ≤ 0) :
    |fourthHorizontalOdd ω m| ≤ 2 * T ∨
      T ≤ |fourthHorizontalEven ω (m + 1) - fourthHorizontalOdd ω m| ∨
      T ≤ |fourthVerticalOdd ω m| ∨
      T ≤ |fourthVerticalEven ω (m + 1)| := by
  rw [fourthSum_odd_eq_horizontal_sub_vertical,
    show 2 * m + 2 = 2 * (m + 1) by omega,
    fourthSum_even_eq_horizontal_sub_vertical] at hcross
  have h := dominant_crossing_threshold_split
    (H := fourthHorizontalOdd ω m)
    (J := fourthHorizontalEven ω (m + 1) - fourthHorizontalOdd ω m)
    (P := fourthVerticalOdd ω m) (P' := fourthVerticalEven ω (m + 1)) hT
  apply h
  convert hcross using 1 <;> ring

end Erdos521
