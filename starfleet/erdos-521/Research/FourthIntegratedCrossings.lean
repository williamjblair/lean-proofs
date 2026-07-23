import Research.FourthIntegratedVariationBound
import Research.CrossingSum
import Mathlib.Tactic

open MeasureTheory

namespace Erdos521

noncomputable local instance fourthCrossingsDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Weak adjacent crossings of the fourth integrated Rademacher walk through time `N`. -/
noncomputable def fourthIntegratedCrossingCount (ω : ℕ → Bool) (N : ℕ) : ℕ :=
  weakCrossingCount (initialCoefficientList N (fourthIntegratedRademacherSum ω))

lemma rightRootCount_le_fourthIntegratedCrossingCount_add_five
    (ω : ℕ → Bool) (N : ℕ) :
    rightRootCount ω (N + 4) ≤ fourthIntegratedCrossingCount ω N + 5 := by
  exact (rightRootCount_le_fourthIntegrated_variations_add_five ω N).trans
    (Nat.add_le_add_right (listSignVariations_le_weakCrossingCount _) 5)

lemma fourthIntegratedRademacherSum_eq_of_prefix {ω η : ℕ → Bool} {N k : ℕ}
    (h : ∀ i ≤ N, ω i = η i) (hk : k ≤ N) :
    fourthIntegratedRademacherSum ω k = fourthIntegratedRademacherSum η k := by
  unfold fourthIntegratedRademacherSum
  apply Finset.sum_congr rfl
  intro r hr
  unfold thirdIntegratedRademacherSum
  apply Finset.sum_congr rfl
  intro q hq
  apply integratedRademacherSum_eq_of_prefix h
  have hrk : r ≤ k := by have := Finset.mem_range.mp hr; omega
  have := Finset.mem_range.mp hq
  omega

lemma fourthIntegratedCrossingCount_eq_of_prefix {ω η : ℕ → Bool} {N : ℕ}
    (h : ∀ i ≤ N, ω i = η i) :
    fourthIntegratedCrossingCount ω N = fourthIntegratedCrossingCount η N := by
  unfold fourthIntegratedCrossingCount
  apply congrArg weakCrossingCount
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    have hiN : i ≤ N := by
      simp only [initialCoefficientList_length] at hi₁
      omega
    simp only [initialCoefficientList, List.getElem_ofFn]
    exact fourthIntegratedRademacherSum_eq_of_prefix h hiN

noncomputable def finiteFourthIntegratedCrossingCount
    (N : ℕ) (x : Fin (N + 1) → Bool) : ℕ :=
  fourthIntegratedCrossingCount (extendDegreePrefix N x) N

lemma finiteFourthIntegratedCrossingCount_degreePrefix (N : ℕ) (ω : ℕ → Bool) :
    finiteFourthIntegratedCrossingCount N (degreePrefix N ω) =
      fourthIntegratedCrossingCount ω N := by
  apply fourthIntegratedCrossingCount_eq_of_prefix
  intro i hi
  exact extendDegreePrefix_degreePrefix ω hi

lemma measurable_fourthIntegratedCrossingCount (N : ℕ) :
    Measurable (fun ω : ℕ → Bool ↦ fourthIntegratedCrossingCount ω N) := by
  have hfinite : Measurable (finiteFourthIntegratedCrossingCount N) := measurable_of_finite _
  have hcomp := hfinite.comp (measurable_degreePrefix N)
  rw [show (fun ω : ℕ → Bool ↦ fourthIntegratedCrossingCount ω N) =
      finiteFourthIntegratedCrossingCount N ∘ degreePrefix N by
    funext ω
    exact (finiteFourthIntegratedCrossingCount_degreePrefix N ω).symm]
  exact hcomp

lemma fourthIntegratedCrossingCount_mono (ω : ℕ → Bool) :
    Monotone (fourthIntegratedCrossingCount ω) := by
  intro N M hNM
  unfold fourthIntegratedCrossingCount
  obtain ⟨r, hr⟩ := initialCoefficientList_prefix hNM (fourthIntegratedRademacherSum ω)
  rw [hr]
  exact weakCrossingCount_append_le _ _

lemma fourthIntegratedCrossingCount_succ (ω : ℕ → Bool) (N : ℕ) :
    fourthIntegratedCrossingCount ω (N + 1) = fourthIntegratedCrossingCount ω N +
      if fourthIntegratedRademacherSum ω N * fourthIntegratedRademacherSum ω (N + 1) ≤ 0
      then 1 else 0 := by
  unfold fourthIntegratedCrossingCount
  rw [initialCoefficientList_succ]
  have hne : initialCoefficientList N (fourthIntegratedRademacherSum ω) ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp
  rw [weakCrossingCount_append_singleton _ _ hne]
  congr 2
  rw [show (initialCoefficientList N (fourthIntegratedRademacherSum ω)).getLastD 0 =
      fourthIntegratedRademacherSum ω N by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    simp only [Option.getD_some]
    unfold initialCoefficientList
    rw [List.getLast_ofFn]
    simp]

noncomputable def fourthIntegratedCrossingIndicator (ω : ℕ → Bool) (k : ℕ) : ℕ :=
  if fourthIntegratedRademacherSum ω k * fourthIntegratedRademacherSum ω (k + 1) ≤ 0
  then 1 else 0

lemma fourthIntegratedCrossingCount_eq_sum (ω : ℕ → Bool) (N : ℕ) :
    fourthIntegratedCrossingCount ω N =
      ∑ k ∈ Finset.range N, fourthIntegratedCrossingIndicator ω k := by
  induction N with
  | zero => simp [fourthIntegratedCrossingCount, initialCoefficientList, weakCrossingCount,
      weakCrossingsFrom]
  | succ N ih =>
      rw [show N + 1 = N + 1 by rfl, fourthIntegratedCrossingCount_succ, ih,
        Finset.sum_range_succ]
      rfl

lemma fourthIntegratedCrossingCount_sub (ω : ℕ → Bool) {N M : ℕ} (hNM : N ≤ M) :
    fourthIntegratedCrossingCount ω M - fourthIntegratedCrossingCount ω N =
      ∑ k ∈ Finset.Ico N M, fourthIntegratedCrossingIndicator ω k := by
  rw [fourthIntegratedCrossingCount_eq_sum, fourthIntegratedCrossingCount_eq_sum]
  have hs := Finset.sum_range_add_sum_Ico (fourthIntegratedCrossingIndicator ω) hNM
  have hle : (∑ k ∈ Finset.range N, fourthIntegratedCrossingIndicator ω k) ≤
      ∑ k ∈ Finset.range M, fourthIntegratedCrossingIndicator ω k := by omega
  apply (Nat.sub_eq_iff_eq_add' hle).2
  exact hs.symm

end Erdos521
