import Research.FourthStripAxisBridge
import Research.FourthThirdCutoffTail
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance fourthIncrementAxisDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthIncrementAxisWords (r k : ℕ) (T : ℝ) :
    Finset (AxisWord r) :=
  Finset.univ.filter fun w ↦ T ≤
    |fourthIntegratedRademacherSum (axisWordCoefficients w) (k + 1) -
      fourthIntegratedRademacherSum (axisWordCoefficients w) k|

noncomputable def fourthIncrementPrefixIndicator (k : ℕ) (T : ℝ)
    (y : Fin (k + 2) → Bool) : ℝ :=
  if T ≤ |(fourthSignedPair k (fourthPrefixSignsEquiv k y) 1 : ℝ)| then 1 else 0

lemma fourthIncrement_full_eq_prefix (k r : ℕ) (T : ℝ) (h : k + 2 ≤ 2 * r)
    (x : Fin (2 * r) → Bool) :
    (if T ≤ |fourthIntegratedRademacherSum (extendBits r x) (k + 1) -
        fourthIntegratedRademacherSum (extendBits r x) k| then (1 : ℝ) else 0) =
      fourthIncrementPrefixIndicator k T (fourthFullBitsEquiv k r h x).1 := by
  unfold fourthIncrementPrefixIndicator
  rw [fourthPrefixSigns_fullBits]
  rw [fourthSignedPair_one_eq_increment]

lemma sum_fourthIncrement_bits_eq_prefix (k r : ℕ) (T : ℝ) (h : k + 2 ≤ 2 * r) :
    (∑ x : Fin (2 * r) → Bool,
      if T ≤ |fourthIntegratedRademacherSum (extendBits r x) (k + 1) -
        fourthIntegratedRademacherSum (extendBits r x) k| then (1 : ℝ) else 0) =
      (2 : ℝ) ^ (2 * r - (k + 2)) *
        ∑ y : Fin (k + 2) → Bool, fourthIncrementPrefixIndicator k T y := by
  calc
    _ = ∑ p : (Fin (k + 2) → Bool) × (Fin (2 * r - (k + 2)) → Bool),
        fourthIncrementPrefixIndicator k T p.1 := by
      apply Fintype.sum_equiv (fourthFullBitsEquiv k r h)
      intro x
      exact fourthIncrement_full_eq_prefix k r T h x
    _ = _ := sum_prod_prefix_function _ _ _

lemma sum_fourthIncrement_prefix_eq_signed (k : ℕ) (T : ℝ) :
    (∑ y : Fin (k + 2) → Bool, fourthIncrementPrefixIndicator k T y) =
      ∑ e : Option (Fin (k + 1)) → Bool,
        if T ≤ |(fourthSignedPair k e 1 : ℝ)| then (1 : ℝ) else 0 := by
  apply Fintype.sum_equiv (fourthPrefixSignsEquiv k)
  intro y
  rfl

lemma fourthIncrementAxisWords_density_eq (k r : ℕ) (T : ℝ) (h : k + 2 ≤ 2 * r) :
    ((fourthIncrementAxisWords r k T).card : ℝ) / (4 : ℝ) ^ r =
      finiteRademacherAbsTailProbability (fourthIncrementWeight k) T := by
  unfold fourthIncrementAxisWords
  rw [Finset.card_filter]
  push_cast
  have hsum : (∑ w : AxisWord r,
      if T ≤ |fourthIntegratedRademacherSum (axisWordCoefficients w) (k + 1) -
        fourthIntegratedRademacherSum (axisWordCoefficients w) k|
        then (1 : ℝ) else 0) =
      ∑ x : Fin (2 * r) → Bool,
        if T ≤ |fourthIntegratedRademacherSum (extendBits r x) (k + 1) -
          fourthIntegratedRademacherSum (extendBits r x) k|
          then (1 : ℝ) else 0 := by
    apply Fintype.sum_equiv (axisWordBitsEquiv r)
    intro w
    rfl
  rw [hsum]
  rw [show (4 : ℝ) ^ r = (2 : ℝ) ^ (2 * r) by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]]
  rw [sum_fourthIncrement_bits_eq_prefix k r T h,
    sum_fourthIncrement_prefix_eq_signed]
  unfold finiteRademacherAbsTailProbability
  have hnum : (∑ e : Option (Fin (k + 1)) → Bool,
      if T ≤ |finiteRademacherRealSum (fourthIncrementWeight k) e| then (1 : ℝ) else 0) =
      ∑ e : Option (Fin (k + 1)) → Bool,
        if T ≤ |(fourthSignedPair k e 1 : ℝ)| then (1 : ℝ) else 0 := by
    apply Fintype.sum_congr
    intro e
    rw [finiteRademacherRealSum_fourthIncrementWeight]
  rw [← hnum]
  have hcard : Fintype.card (Option (Fin (k + 1))) = k + 2 := by simp
  rw [hcard]
  have htotal : k + 2 + (2 * r - (k + 2)) = 2 * r := Nat.add_sub_of_le h
  rw [← htotal, pow_add]
  have hdpos : (0 : ℝ) < (2 : ℝ) ^ (2 * r - (k + 2)) := by positivity
  field_simp
  rw [show k + 2 + (2 * r - (k + 2)) - (k + 2) = 2 * r - (k + 2) by omega]
  congr 1
  apply Finset.sum_congr (by ext e; simp)
  intro e he
  rfl

end Erdos521
