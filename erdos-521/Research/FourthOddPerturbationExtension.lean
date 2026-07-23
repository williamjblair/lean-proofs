import Research.FourthEvenCoordinateEvents
import Mathlib.Tactic

namespace Erdos521

noncomputable local instance fourthOddExtensionDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def oddAxisPrefixWord (m : ℕ) (w : AxisWord (m + 2)) : AxisWord (m + 1) :=
  (axisWordBitsEquiv (m + 1)).symm
    (fourthFullBitsEquiv (2 * m) (m + 2) (by omega) (axisWordBits w)).1

noncomputable def oddAxisSplitEquiv (m : ℕ) :
    AxisWord (m + 2) ≃
      AxisWord (m + 1) × (Fin (2 * (m + 2) - (2 * m + 2)) → Bool) :=
  (axisWordBitsEquiv (m + 2)).trans <|
    (fourthFullBitsEquiv (2 * m) (m + 2) (by omega)).trans <|
      Equiv.prodCongr (axisWordBitsEquiv (m + 1)).symm (Equiv.refl _)

lemma oddAxisSplitEquiv_fst (m : ℕ) (w : AxisWord (m + 2)) :
    (oddAxisSplitEquiv m w).1 = oddAxisPrefixWord m w := rfl

lemma oddAxisPrefix_coefficients (m : ℕ) (w : AxisWord (m + 2)) (i : ℕ)
    (hi : i < 2 * (m + 1)) :
    axisWordCoefficients (oddAxisPrefixWord m w) i = axisWordCoefficients w i := by
  unfold axisWordCoefficients
  rw [extendBits_of_lt _ hi, extendBits_of_lt _ (by omega)]
  have happly := (axisWordBitsEquiv (m + 1)).apply_symm_apply
    (fourthFullBitsEquiv (2 * m) (m + 2) (by omega) (axisWordBits w)).1
  have hbit := congrFun happly ⟨i, hi⟩
  change (axisWordBitsEquiv (m + 1))
      ((axisWordBitsEquiv (m + 1)).symm
        (fourthFullBitsEquiv (2 * m) (m + 2) (by omega) (axisWordBits w)).1)
      ⟨i, hi⟩ = axisWordBits w ⟨i, by omega⟩
  rw [hbit]
  exact fourthFullBitsEquiv_fst (2 * m) (m + 2) (by omega)
    (axisWordBits w) ⟨i, by omega⟩

lemma fourthVerticalOdd_prefix_eq (m : ℕ) (w : AxisWord (m + 2)) :
    fourthVerticalOdd (axisWordCoefficients (oddAxisPrefixWord m w)) m =
      fourthVerticalOdd (axisWordCoefficients w) m := by
  unfold fourthVerticalOdd pairVertical
  apply Finset.sum_congr rfl
  intro j hj
  rw [oddAxisPrefix_coefficients m w (2 * j) (by
      simp only [Finset.mem_range] at hj
      omega),
    oddAxisPrefix_coefficients m w (2 * j + 1) (by
      simp only [Finset.mem_range] at hj
      omega)]

noncomputable def fourthOddPerturbationExtendedWords (m : ℕ) (T : ℝ) :
    Finset (AxisWord (m + 2)) :=
  Finset.univ.filter fun w ↦ T ≤ |fourthVerticalOdd (axisWordCoefficients w) m|

lemma fourthOddPerturbationExtendedWords_density_eq (m : ℕ) (T : ℝ) :
    ((fourthOddPerturbationExtendedWords m T).card : ℝ) / (4 : ℝ) ^ (m + 2) =
      ((fourthOddPerturbationWords m T).card : ℝ) / (4 : ℝ) ^ (m + 1) := by
  unfold fourthOddPerturbationExtendedWords fourthOddPerturbationWords
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  have hsum : (∑ w : AxisWord (m + 2),
      if T ≤ |fourthVerticalOdd (axisWordCoefficients w) m| then (1 : ℝ) else 0) =
      ∑ p : AxisWord (m + 1) ×
          (Fin (2 * (m + 2) - (2 * m + 2)) → Bool),
        if T ≤ |fourthVerticalOdd (axisWordCoefficients p.1) m| then (1 : ℝ) else 0 := by
    apply Fintype.sum_equiv (oddAxisSplitEquiv m)
    intro w
    rw [oddAxisSplitEquiv_fst, fourthVerticalOdd_prefix_eq]
  rw [hsum, Fintype.sum_prod_type]
  rw [show (∑ a : AxisWord (m + 1),
      ∑ _b : Fin (2 * (m + 2) - (2 * m + 2)) → Bool,
        if T ≤ |fourthVerticalOdd (axisWordCoefficients a) m| then (1 : ℝ) else 0) =
      ∑ a : AxisWord (m + 1),
        (2 : ℝ) ^ (2 * (m + 2) - (2 * m + 2)) *
          (if T ≤ |fourthVerticalOdd (axisWordCoefficients a) m| then 1 else 0) by
    apply Finset.sum_congr rfl
    intro a ha
    simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]]
  rw [← Finset.mul_sum]
  have hrem : 2 * (m + 2) - (2 * m + 2) = 2 := by omega
  rw [hrem]
  norm_num [pow_succ]
  ring

end Erdos521
