import Research.FourthDominantCrossingSplit
import Mathlib.Tactic

namespace Erdos521

lemma fourthHorizontalEven_small_reduce (ω : ℕ → Bool) (m : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : |fourthHorizontalEven ω m| ≤ 6 * T) :
    |fourthIntegratedRademacherSum ω (2 * m)| ≤ 9 * T ∨
      3 * T ≤ |fourthVerticalEven ω m| := by
  rw [fourthSum_even_eq_horizontal_sub_vertical]
  by_cases hp : 3 * T ≤ |fourthVerticalEven ω m|
  · exact Or.inr hp
  · left
    have hp' : |fourthVerticalEven ω m| < 3 * T := lt_of_not_ge hp
    calc
      |fourthHorizontalEven ω m - fourthVerticalEven ω m| ≤
          |fourthHorizontalEven ω m| + |fourthVerticalEven ω m| := abs_sub _ _
      _ ≤ 9 * T := by linarith

lemma fourthHorizontalOdd_small_reduce (ω : ℕ → Bool) (m : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : |fourthHorizontalOdd ω m| ≤ 6 * T) :
    |fourthIntegratedRademacherSum ω (2 * m + 1)| ≤ 9 * T ∨
      3 * T ≤ |fourthVerticalOdd ω m| := by
  rw [fourthSum_odd_eq_horizontal_sub_vertical]
  by_cases hp : 3 * T ≤ |fourthVerticalOdd ω m|
  · exact Or.inr hp
  · left
    have hp' : |fourthVerticalOdd ω m| < 3 * T := lt_of_not_ge hp
    calc
      |fourthHorizontalOdd ω m - fourthVerticalOdd ω m| ≤
          |fourthHorizontalOdd ω m| + |fourthVerticalOdd ω m| := abs_sub _ _
      _ ≤ 9 * T := by linarith

lemma fourthHorizontal_even_increment_large_reduce (ω : ℕ → Bool) (m : ℕ) {T : ℝ}
    (hlarge : 3 * T ≤ |fourthHorizontalOdd ω m - fourthHorizontalEven ω m|) :
    T ≤ |fourthIntegratedRademacherSum ω (2 * m + 1) -
      fourthIntegratedRademacherSum ω (2 * m)| ∨
    T ≤ |fourthVerticalOdd ω m| ∨ T ≤ |fourthVerticalEven ω m| := by
  rw [fourthSum_odd_eq_horizontal_sub_vertical,
    fourthSum_even_eq_horizontal_sub_vertical]
  by_cases hd : T ≤ |(fourthHorizontalOdd ω m - fourthVerticalOdd ω m) -
      (fourthHorizontalEven ω m - fourthVerticalEven ω m)|
  · exact Or.inl hd
  · by_cases hp' : T ≤ |fourthVerticalOdd ω m|
    · exact Or.inr (Or.inl hp')
    · right; right
      by_contra hp
      push_neg at hp
      have hd' := lt_of_not_ge hd
      have hp'' := lt_of_not_ge hp'
      have htri := abs_add_three
        ((fourthHorizontalOdd ω m - fourthVerticalOdd ω m) -
          (fourthHorizontalEven ω m - fourthVerticalEven ω m))
        (fourthVerticalOdd ω m) (-fourthVerticalEven ω m)
      have hident :
          ((fourthHorizontalOdd ω m - fourthVerticalOdd ω m) -
            (fourthHorizontalEven ω m - fourthVerticalEven ω m)) +
            fourthVerticalOdd ω m + -fourthVerticalEven ω m =
          fourthHorizontalOdd ω m - fourthHorizontalEven ω m := by ring
      rw [hident, abs_neg] at htri
      linarith

lemma fourthHorizontal_odd_increment_large_reduce (ω : ℕ → Bool) (m : ℕ) {T : ℝ}
    (hlarge : 3 * T ≤ |fourthHorizontalEven ω (m + 1) - fourthHorizontalOdd ω m|) :
    T ≤ |fourthIntegratedRademacherSum ω (2 * m + 2) -
      fourthIntegratedRademacherSum ω (2 * m + 1)| ∨
    T ≤ |fourthVerticalEven ω (m + 1)| ∨ T ≤ |fourthVerticalOdd ω m| := by
  rw [show 2 * m + 2 = 2 * (m + 1) by omega,
    fourthSum_even_eq_horizontal_sub_vertical,
    fourthSum_odd_eq_horizontal_sub_vertical]
  by_cases hd : T ≤ |(fourthHorizontalEven ω (m + 1) - fourthVerticalEven ω (m + 1)) -
      (fourthHorizontalOdd ω m - fourthVerticalOdd ω m)|
  · exact Or.inl hd
  · by_cases hp' : T ≤ |fourthVerticalEven ω (m + 1)|
    · exact Or.inr (Or.inl hp')
    · right; right
      by_contra hp
      push_neg at hp
      have hd' := lt_of_not_ge hd
      have hp'' := lt_of_not_ge hp'
      have htri := abs_add_three
        ((fourthHorizontalEven ω (m + 1) - fourthVerticalEven ω (m + 1)) -
          (fourthHorizontalOdd ω m - fourthVerticalOdd ω m))
        (fourthVerticalEven ω (m + 1)) (-fourthVerticalOdd ω m)
      have hident :
          ((fourthHorizontalEven ω (m + 1) - fourthVerticalEven ω (m + 1)) -
            (fourthHorizontalOdd ω m - fourthVerticalOdd ω m)) +
            fourthVerticalEven ω (m + 1) + -fourthVerticalOdd ω m =
          fourthHorizontalEven ω (m + 1) - fourthHorizontalOdd ω m := by ring
      rw [hident, abs_neg] at htri
      linarith

end Erdos521
