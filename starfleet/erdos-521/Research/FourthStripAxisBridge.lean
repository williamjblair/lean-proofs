import Research.FourthLateStripRate
import Research.FourthCrossingBridge
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance fourthStripAxisDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthIntegratedStripAxisWords (r k : ℕ) (T : ℝ) :
    Finset (AxisWord r) :=
  Finset.univ.filter fun w ↦
    |fourthIntegratedRademacherSum (axisWordCoefficients w) k| ≤ T

noncomputable def fourthStripPrefixIndicator (k : ℕ) (T : ℝ)
    (y : Fin (k + 2) → Bool) : ℝ :=
  if |(fourthSignedPair k (fourthPrefixSignsEquiv k y) 0 : ℝ)| ≤ T then 1 else 0

lemma fourthStrip_full_eq_prefix (k r : ℕ) (T : ℝ) (h : k + 2 ≤ 2 * r)
    (x : Fin (2 * r) → Bool) :
    (if |fourthIntegratedRademacherSum (extendBits r x) k| ≤ T then (1 : ℝ) else 0) =
      fourthStripPrefixIndicator k T (fourthFullBitsEquiv k r h x).1 := by
  unfold fourthStripPrefixIndicator
  rw [fourthPrefixSigns_fullBits]
  rw [fourthSignedPair_zero_eq_integrated]

lemma sum_fourthStrip_bits_eq_prefix (k r : ℕ) (T : ℝ) (h : k + 2 ≤ 2 * r) :
    (∑ x : Fin (2 * r) → Bool,
      if |fourthIntegratedRademacherSum (extendBits r x) k| ≤ T then (1 : ℝ) else 0) =
      (2 : ℝ) ^ (2 * r - (k + 2)) *
        ∑ y : Fin (k + 2) → Bool, fourthStripPrefixIndicator k T y := by
  calc
    _ = ∑ p : (Fin (k + 2) → Bool) × (Fin (2 * r - (k + 2)) → Bool),
        fourthStripPrefixIndicator k T p.1 := by
      apply Fintype.sum_equiv (fourthFullBitsEquiv k r h)
      intro x
      exact fourthStrip_full_eq_prefix k r T h x
    _ = _ := sum_prod_prefix_function _ _ _

lemma sum_fourthStrip_prefix_eq_signed (k : ℕ) (T : ℝ) :
    (∑ y : Fin (k + 2) → Bool, fourthStripPrefixIndicator k T y) =
      ∑ e : Option (Fin (k + 1)) → Bool,
        if |(fourthSignedPair k e 0 : ℝ)| ≤ T then (1 : ℝ) else 0 := by
  apply Fintype.sum_equiv (fourthPrefixSignsEquiv k)
  intro y
  rfl

/-- Exact axis-word/iid signed-pair equality for a natural small-ball threshold. -/
lemma fourthIntegratedStripAxisWords_density_eq (k r L : ℕ) (h : k + 2 ≤ 2 * r) :
    ((fourthIntegratedStripAxisWords r k (L : ℝ)).card : ℝ) / (4 : ℝ) ^ r =
      fourthSignedStripProbability k L := by
  unfold fourthIntegratedStripAxisWords
  rw [Finset.card_filter]
  push_cast
  have hsum : (∑ w : AxisWord r,
      if |fourthIntegratedRademacherSum (axisWordCoefficients w) k| ≤ (L : ℝ)
        then (1 : ℝ) else 0) =
      ∑ x : Fin (2 * r) → Bool,
        if |fourthIntegratedRademacherSum (extendBits r x) k| ≤ (L : ℝ)
          then (1 : ℝ) else 0 := by
    apply Fintype.sum_equiv (axisWordBitsEquiv r)
    intro w
    rfl
  rw [hsum]
  rw [show (4 : ℝ) ^ r = (2 : ℝ) ^ (2 * r) by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]]
  -- Repeat the prefix factorization without introducing a real-floor issue.
  rw [sum_fourthStrip_bits_eq_prefix k r (L : ℝ) h,
    sum_fourthStrip_prefix_eq_signed]
  unfold fourthSignedStripProbability fourthSignedEventProbability
  have hcard : Fintype.card (Option (Fin (k + 1))) = k + 2 := by simp
  rw [hcard]
  have htotal : k + 2 + (2 * r - (k + 2)) = 2 * r := Nat.add_sub_of_le h
  rw [← htotal, pow_add]
  have hdpos : (0 : ℝ) < (2 : ℝ) ^ (2 * r - (k + 2)) := by positivity
  field_simp
  rw [show k + 2 + (2 * r - (k + 2)) - (k + 2) = 2 * r - (k + 2) by omega]
  simp only [Int.cast_abs]

end Erdos521
