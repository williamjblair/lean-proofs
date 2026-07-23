import Research.ThirdIntegratedVariationBound
import Research.CrossingSum
import Mathlib.Tactic

open MeasureTheory

namespace Erdos521

noncomputable local instance thirdCrossingsDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Weak adjacent crossings of the third integrated Rademacher walk through time `N`. -/
noncomputable def thirdIntegratedCrossingCount (ω : ℕ → Bool) (N : ℕ) : ℕ :=
  weakCrossingCount (initialCoefficientList N (thirdIntegratedRademacherSum ω))

lemma rightRootCount_le_thirdIntegratedCrossingCount_add_four
    (ω : ℕ → Bool) (N : ℕ) :
    rightRootCount ω (N + 3) ≤ thirdIntegratedCrossingCount ω N + 4 := by
  exact (rightRootCount_le_thirdIntegrated_variations_add_four ω N).trans
    (Nat.add_le_add_right (listSignVariations_le_weakCrossingCount _) 4)

lemma thirdIntegratedRademacherSum_eq_of_prefix {ω η : ℕ → Bool} {N k : ℕ}
    (h : ∀ i ≤ N, ω i = η i) (hk : k ≤ N) :
    thirdIntegratedRademacherSum ω k = thirdIntegratedRademacherSum η k := by
  unfold thirdIntegratedRademacherSum
  apply Finset.sum_congr rfl
  intro r hr
  apply integratedRademacherSum_eq_of_prefix h
  have := Finset.mem_range.mp hr
  omega

lemma thirdIntegratedCrossingCount_eq_of_prefix {ω η : ℕ → Bool} {N : ℕ}
    (h : ∀ i ≤ N, ω i = η i) :
    thirdIntegratedCrossingCount ω N = thirdIntegratedCrossingCount η N := by
  unfold thirdIntegratedCrossingCount
  apply congrArg weakCrossingCount
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    have hiN : i ≤ N := by
      simp only [initialCoefficientList_length] at hi₁
      omega
    simp only [initialCoefficientList, List.getElem_ofFn]
    exact thirdIntegratedRademacherSum_eq_of_prefix h hiN

noncomputable def finiteThirdIntegratedCrossingCount
    (N : ℕ) (x : Fin (N + 1) → Bool) : ℕ :=
  thirdIntegratedCrossingCount (extendDegreePrefix N x) N

lemma finiteThirdIntegratedCrossingCount_degreePrefix (N : ℕ) (ω : ℕ → Bool) :
    finiteThirdIntegratedCrossingCount N (degreePrefix N ω) =
      thirdIntegratedCrossingCount ω N := by
  apply thirdIntegratedCrossingCount_eq_of_prefix
  intro i hi
  exact extendDegreePrefix_degreePrefix ω hi

lemma measurable_thirdIntegratedCrossingCount (N : ℕ) :
    Measurable (fun ω : ℕ → Bool ↦ thirdIntegratedCrossingCount ω N) := by
  have hfinite : Measurable (finiteThirdIntegratedCrossingCount N) := measurable_of_finite _
  have hcomp := hfinite.comp (measurable_degreePrefix N)
  rw [show (fun ω : ℕ → Bool ↦ thirdIntegratedCrossingCount ω N) =
      finiteThirdIntegratedCrossingCount N ∘ degreePrefix N by
    funext ω
    exact (finiteThirdIntegratedCrossingCount_degreePrefix N ω).symm]
  exact hcomp

lemma thirdIntegratedCrossingCount_mono (ω : ℕ → Bool) :
    Monotone (thirdIntegratedCrossingCount ω) := by
  intro N M hNM
  unfold thirdIntegratedCrossingCount
  obtain ⟨r, hr⟩ := initialCoefficientList_prefix hNM (thirdIntegratedRademacherSum ω)
  rw [hr]
  exact weakCrossingCount_append_le _ _

lemma thirdIntegratedCrossingCount_succ (ω : ℕ → Bool) (N : ℕ) :
    thirdIntegratedCrossingCount ω (N + 1) = thirdIntegratedCrossingCount ω N +
      if thirdIntegratedRademacherSum ω N * thirdIntegratedRademacherSum ω (N + 1) ≤ 0
      then 1 else 0 := by
  unfold thirdIntegratedCrossingCount
  rw [initialCoefficientList_succ]
  have hne : initialCoefficientList N (thirdIntegratedRademacherSum ω) ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp
  rw [weakCrossingCount_append_singleton _ _ hne]
  congr 2
  rw [show (initialCoefficientList N (thirdIntegratedRademacherSum ω)).getLastD 0 =
      thirdIntegratedRademacherSum ω N by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    simp only [Option.getD_some]
    unfold initialCoefficientList
    rw [List.getLast_ofFn]
    simp]

noncomputable def thirdIntegratedCrossingIndicator (ω : ℕ → Bool) (k : ℕ) : ℕ :=
  if thirdIntegratedRademacherSum ω k * thirdIntegratedRademacherSum ω (k + 1) ≤ 0
  then 1 else 0

lemma thirdIntegratedCrossingCount_eq_sum (ω : ℕ → Bool) (N : ℕ) :
    thirdIntegratedCrossingCount ω N =
      ∑ k ∈ Finset.range N, thirdIntegratedCrossingIndicator ω k := by
  induction N with
  | zero => simp [thirdIntegratedCrossingCount, initialCoefficientList, weakCrossingCount,
      weakCrossingsFrom]
  | succ N ih =>
      rw [show N + 1 = N + 1 by rfl, thirdIntegratedCrossingCount_succ, ih,
        Finset.sum_range_succ]
      rfl

lemma thirdIntegratedCrossingCount_sub (ω : ℕ → Bool) {N M : ℕ} (hNM : N ≤ M) :
    thirdIntegratedCrossingCount ω M - thirdIntegratedCrossingCount ω N =
      ∑ k ∈ Finset.Ico N M, thirdIntegratedCrossingIndicator ω k := by
  rw [thirdIntegratedCrossingCount_eq_sum, thirdIntegratedCrossingCount_eq_sum]
  have hs := Finset.sum_range_add_sum_Ico (thirdIntegratedCrossingIndicator ω) hNM
  have hle : (∑ k ∈ Finset.range N, thirdIntegratedCrossingIndicator ω k) ≤
      ∑ k ∈ Finset.range M, thirdIntegratedCrossingIndicator ω k := by omega
  apply (Nat.sub_eq_iff_eq_add' hle).2
  exact hs.symm

end Erdos521
