import Research.IntegratedVariationBound
import Research.RootCountMeasurable
import Mathlib.Tactic

open MeasureTheory

namespace Erdos521

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Count adjacent weak sign crossings, beginning with a preceding value `p`. -/
noncomputable def weakCrossingsFrom : ℝ → List ℝ → ℕ
  | _, [] => 0
  | p, x :: xs => (if p * x ≤ 0 then 1 else 0) + weakCrossingsFrom x xs

/-- Adjacent weak sign crossings of a list; a zero product is deliberately counted. -/
noncomputable def weakCrossingCount : List ℝ → ℕ
  | [] => 0
  | x :: xs => weakCrossingsFrom x xs

lemma signTransitions_le_weakCrossingsFrom (p : ℝ) (l : List ℝ) :
    signTransitions (SignType.sign p) (l.map SignType.sign) ≤ weakCrossingsFrom p l := by
  induction l generalizing p with
  | nil => simp [signTransitions, weakCrossingsFrom]
  | cons x xs ih =>
      have hix := ih x
      have hlip := signTransitions_le_succ (SignType.sign p) 0 (xs.map SignType.sign)
      rcases lt_trichotomy p 0 with hp | hp | hp
      · rcases lt_trichotomy x 0 with hx | hx | hx
        · have hpx : 0 < p * x := mul_pos_of_neg_of_neg hp hx
          simp [signTransitions, weakCrossingsFrom, sign_neg hp, sign_neg hx,
            not_le.mpr hpx] at hix ⊢
          exact hix
        · subst x
          simp [signTransitions, weakCrossingsFrom, sign_neg hp, sign_zero] at hix hlip ⊢
          omega
        · have hpx : p * x < 0 := mul_neg_of_neg_of_pos hp hx
          simp [signTransitions, weakCrossingsFrom, sign_neg hp, sign_pos hx,
            le_of_lt hpx] at hix ⊢
          omega
      · subst p
        by_cases hx0 : x = 0
        · subst x
          simp [signTransitions, weakCrossingsFrom, sign_zero] at hix ⊢
          omega
        · have hsx : SignType.sign x ≠ 0 := sign_eq_zero_iff.not.mpr hx0
          simp [signTransitions, weakCrossingsFrom, sign_zero, hsx] at hix ⊢
          omega
      · rcases lt_trichotomy x 0 with hx | hx | hx
        · have hpx : p * x < 0 := mul_neg_of_pos_of_neg hp hx
          simp [signTransitions, weakCrossingsFrom, sign_pos hp, sign_neg hx,
            le_of_lt hpx] at hix ⊢
          omega
        · subst x
          simp [signTransitions, weakCrossingsFrom, sign_pos hp, sign_zero] at hix hlip ⊢
          omega
        · have hpx : 0 < p * x := mul_pos hp hx
          simp [signTransitions, weakCrossingsFrom, sign_pos hp, sign_pos hx,
            not_le.mpr hpx] at hix ⊢
          exact hix

lemma listSignVariations_le_weakCrossingCount (l : List ℝ) :
    listSignVariations l ≤ weakCrossingCount l := by
  cases l with
  | nil => simp [listSignVariations, weakCrossingCount, signTransitions]
  | cons x xs =>
      unfold listSignVariations weakCrossingCount
      simp only [List.map_cons, signTransitions]
      by_cases hx : SignType.sign x = 0
      · simp only [if_pos hx]
        simpa [sign_eq_zero_iff.mp hx] using signTransitions_le_weakCrossingsFrom x xs
      · simp only [if_neg hx, true_or, if_true, zero_add]
        exact signTransitions_le_weakCrossingsFrom x xs

/-- Weak crossings of the integrated Rademacher walk through time `N`. -/
noncomputable def integratedCrossingCount (ω : ℕ → Bool) (N : ℕ) : ℕ :=
  weakCrossingCount (initialCoefficientList N (integratedRademacherSum ω))

lemma rightRootCount_le_integratedCrossingCount_add_three (ω : ℕ → Bool) (N : ℕ) :
    rightRootCount ω (N + 2) ≤ integratedCrossingCount ω N + 3 := by
  exact (rightRootCount_le_integrated_variations_add_three ω N).trans
    (Nat.add_le_add_right (listSignVariations_le_weakCrossingCount _) 3)

lemma integratedRademacherSum_eq_of_prefix {ω η : ℕ → Bool} {N k : ℕ}
    (h : ∀ i ≤ N, ω i = η i) (hk : k ≤ N) :
    integratedRademacherSum ω k = integratedRademacherSum η k := by
  rw [integratedRademacherSum_eq_weighted, integratedRademacherSum_eq_weighted]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (by have := Finset.mem_range.mp hi; omega)]

lemma integratedCrossingCount_eq_of_prefix {ω η : ℕ → Bool} {N : ℕ}
    (h : ∀ i ≤ N, ω i = η i) :
    integratedCrossingCount ω N = integratedCrossingCount η N := by
  unfold integratedCrossingCount
  apply congrArg weakCrossingCount
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    have hiN : i ≤ N := by
      simp only [initialCoefficientList_length] at hi₁
      omega
    simp only [initialCoefficientList, List.getElem_ofFn]
    exact integratedRademacherSum_eq_of_prefix h hiN

noncomputable def finiteIntegratedCrossingCount (N : ℕ) (x : Fin (N + 1) → Bool) : ℕ :=
  integratedCrossingCount (extendDegreePrefix N x) N

lemma finiteIntegratedCrossingCount_degreePrefix (N : ℕ) (ω : ℕ → Bool) :
    finiteIntegratedCrossingCount N (degreePrefix N ω) = integratedCrossingCount ω N := by
  apply integratedCrossingCount_eq_of_prefix
  intro i hi
  exact extendDegreePrefix_degreePrefix ω hi

lemma measurable_integratedCrossingCount (N : ℕ) :
    Measurable (fun ω : ℕ → Bool ↦ integratedCrossingCount ω N) := by
  have hfinite : Measurable (finiteIntegratedCrossingCount N) := measurable_of_finite _
  have hcomp := hfinite.comp (measurable_degreePrefix N)
  rw [show (fun ω : ℕ → Bool ↦ integratedCrossingCount ω N) =
      finiteIntegratedCrossingCount N ∘ degreePrefix N by
    funext ω
    exact (finiteIntegratedCrossingCount_degreePrefix N ω).symm]
  exact hcomp

end Erdos521
