import Research.LateFourthEdgeBound
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance axisOddTwistDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma pairHorizontal_oddTwist (ω : ℕ → Bool) (j : ℕ) :
    pairHorizontal (oddTwist ω) j = -pairVertical ω j := by
  unfold pairHorizontal pairVertical
  rw [sign_oddTwist, sign_oddTwist]
  have he : Even (2 * j) := ⟨j, by omega⟩
  have ho : Odd (2 * j + 1) := ⟨j, by omega⟩
  rw [he.neg_one_pow, ho.neg_one_pow]
  ring

lemma pairVertical_oddTwist (ω : ℕ → Bool) (j : ℕ) :
    pairVertical (oddTwist ω) j = -pairHorizontal ω j := by
  unfold pairHorizontal pairVertical
  rw [sign_oddTwist, sign_oddTwist]
  have he : Even (2 * j) := ⟨j, by omega⟩
  have ho : Odd (2 * j + 1) := ⟨j, by omega⟩
  rw [he.neg_one_pow, ho.neg_one_pow]
  ring

lemma pairHorizontal_oddTwist_axisWord {r : ℕ} (w : AxisWord r) (j : Fin r) :
    pairHorizontal (oddTwist (axisWordCoefficients w)) j.val =
      -pairHorizontal (axisWordCoefficients (swapAxisWord w)) j.val := by
  rw [pairHorizontal_oddTwist, pairHorizontal_swapAxisWord]

lemma pairVertical_oddTwist_axisWord {r : ℕ} (w : AxisWord r) (j : Fin r) :
    pairVertical (oddTwist (axisWordCoefficients w)) j.val =
      -pairVertical (axisWordCoefficients (swapAxisWord w)) j.val := by
  rw [pairVertical_oddTwist, pairVertical_swapAxisWord]

lemma fourthHorizontalEven_oddTwist_swap {r m : ℕ} (hm : m < r) (w : AxisWord r) :
    fourthHorizontalEven (oddTwist (axisWordCoefficients w)) m =
      -fourthHorizontalEven (axisWordCoefficients (swapAxisWord w)) m := by
  unfold fourthHorizontalEven
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairHorizontal_oddTwist_axisWord w ⟨j, hjr⟩]
  ring

lemma fourthHorizontalOdd_oddTwist_swap {r m : ℕ} (hm : m < r) (w : AxisWord r) :
    fourthHorizontalOdd (oddTwist (axisWordCoefficients w)) m =
      -fourthHorizontalOdd (axisWordCoefficients (swapAxisWord w)) m := by
  unfold fourthHorizontalOdd
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairHorizontal_oddTwist_axisWord w ⟨j, hjr⟩]
  ring

lemma fourthVerticalEven_oddTwist_swap {r m : ℕ} (hm : m < r) (w : AxisWord r) :
    fourthVerticalEven (oddTwist (axisWordCoefficients w)) m =
      -fourthVerticalEven (axisWordCoefficients (swapAxisWord w)) m := by
  unfold fourthVerticalEven
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairVertical_oddTwist_axisWord w ⟨j, hjr⟩]
  ring

lemma fourthVerticalOdd_oddTwist_swap {r m : ℕ} (hm : m < r) (w : AxisWord r) :
    fourthVerticalOdd (oddTwist (axisWordCoefficients w)) m =
      -fourthVerticalOdd (axisWordCoefficients (swapAxisWord w)) m := by
  unfold fourthVerticalOdd
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j < r := (Finset.mem_range.mp hj).trans_le (by omega)
  rw [pairVertical_oddTwist_axisWord w ⟨j, hjr⟩]
  ring

lemma fourthSum_even_oddTwist_swap {r m : ℕ} (hm : m < r) (w : AxisWord r) :
    fourthIntegratedRademacherSum (oddTwist (axisWordCoefficients w)) (2 * m) =
      -fourthIntegratedRademacherSum (axisWordCoefficients (swapAxisWord w)) (2 * m) := by
  rw [fourthSum_even_eq_horizontal_sub_vertical,
    fourthSum_even_eq_horizontal_sub_vertical,
    fourthHorizontalEven_oddTwist_swap hm,
    fourthVerticalEven_oddTwist_swap hm]
  ring

lemma fourthSum_odd_oddTwist_swap {r m : ℕ} (hm : m < r) (w : AxisWord r) :
    fourthIntegratedRademacherSum (oddTwist (axisWordCoefficients w)) (2 * m + 1) =
      -fourthIntegratedRademacherSum (axisWordCoefficients (swapAxisWord w)) (2 * m + 1) := by
  rw [fourthSum_odd_eq_horizontal_sub_vertical,
    fourthSum_odd_eq_horizontal_sub_vertical,
    fourthHorizontalOdd_oddTwist_swap hm,
    fourthVerticalOdd_oddTwist_swap hm]
  ring

lemma fourthIndicator_even_oddTwist_swap {r m : ℕ} (hm : m < r) (w : AxisWord r) :
    fourthIntegratedCrossingIndicator (oddTwist (axisWordCoefficients w)) (2 * m) =
      fourthIntegratedCrossingIndicator (axisWordCoefficients (swapAxisWord w)) (2 * m) := by
  unfold fourthIntegratedCrossingIndicator
  rw [fourthSum_even_oddTwist_swap hm, fourthSum_odd_oddTwist_swap hm]
  ring_nf

lemma fourthIndicator_odd_oddTwist_swap {r m : ℕ} (hm : m + 1 < r) (w : AxisWord r) :
    fourthIntegratedCrossingIndicator (oddTwist (axisWordCoefficients w)) (2 * m + 1) =
      fourthIntegratedCrossingIndicator (axisWordCoefficients (swapAxisWord w)) (2 * m + 1) := by
  unfold fourthIntegratedCrossingIndicator
  rw [fourthSum_odd_oddTwist_swap (by omega),
    show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
    fourthSum_even_oddTwist_swap hm]
  ring_nf

lemma fourthIndicator_axisSuffix_eq {s r k : ℕ} (p : AxisGoodPath (s + r))
    (hk : k + 1 < 2 * r) :
    fourthIntegratedCrossingIndicator (axisWordCoefficients (axisSuffix p)) k =
      fourthIntegratedCrossingIndicator (axisPathCoefficients p) k := by
  have hpref : ∀ i ≤ k + 1,
      axisWordCoefficients (axisSuffix p) i = axisPathCoefficients p i := by
    intro i hi
    exact axisSuffix_coefficients_eq_of_lt p (by omega)
  have h0 := fourthIntegratedRademacherSum_eq_of_prefix (N := k + 1) hpref (by omega : k ≤ k + 1)
  have h1 := fourthIntegratedRademacherSum_eq_of_prefix (N := k + 1) hpref (le_rfl)
  unfold fourthIntegratedCrossingIndicator
  rw [h0, h1]

lemma fourthIndicator_oddTwist_axisSuffix_eq {s r k : ℕ} (p : AxisGoodPath (s + r))
    (hk : k + 1 < 2 * r) :
    fourthIntegratedCrossingIndicator (oddTwist (axisWordCoefficients (axisSuffix p))) k =
      fourthIntegratedCrossingIndicator (oddTwist (axisPathCoefficients p)) k := by
  have hpref : ∀ i ≤ k + 1,
      oddTwist (axisWordCoefficients (axisSuffix p)) i = oddTwist (axisPathCoefficients p) i := by
    intro i hi
    unfold oddTwist
    rw [axisSuffix_coefficients_eq_of_lt p (by omega)]
  have h0 := fourthIntegratedRademacherSum_eq_of_prefix (N := k + 1) hpref (by omega : k ≤ k + 1)
  have h1 := fourthIntegratedRademacherSum_eq_of_prefix (N := k + 1) hpref (le_rfl)
  unfold fourthIntegratedCrossingIndicator
  rw [h0, h1]

lemma fourthIndicator_even_oddTwist_rotate {s r m : ℕ} (hm : m < r)
    (p : AxisGoodPath (s + r)) :
    fourthIntegratedCrossingIndicator (oddTwist (axisPathCoefficients p)) (2 * m) =
      fourthIntegratedCrossingIndicator (axisPathCoefficients (rotateAxisGoodPath p)) (2 * m) := by
  rw [← fourthIndicator_oddTwist_axisSuffix_eq p (by omega),
    fourthIndicator_even_oddTwist_swap hm,
    ← axisSuffix_rotate,
    fourthIndicator_axisSuffix_eq (rotateAxisGoodPath p) (by omega)]

lemma fourthIndicator_odd_oddTwist_rotate {s r m : ℕ} (hm : m + 1 < r)
    (p : AxisGoodPath (s + r)) :
    fourthIntegratedCrossingIndicator (oddTwist (axisPathCoefficients p)) (2 * m + 1) =
      fourthIntegratedCrossingIndicator (axisPathCoefficients (rotateAxisGoodPath p)) (2 * m + 1) := by
  rw [← fourthIndicator_oddTwist_axisSuffix_eq p (by omega),
    fourthIndicator_odd_oddTwist_swap hm,
    ← axisSuffix_rotate,
    fourthIndicator_axisSuffix_eq (rotateAxisGoodPath p) (by omega)]

end Erdos521
