import Research.FourthStripLocalLimit
import Mathlib.Tactic

open scoped BigOperators

set_option maxHeartbeats 800000

namespace Erdos521

noncomputable local instance fourthCentralStripDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthCentralStripParameters (k T U : ℕ) : Finset (Fin 2 → ℤ) :=
  (fourthGaussianStripParameters k T).filter fun d ↦
    |signedIntLatticeTarget (fourthSignedIntegerVector k) d 1| ≤ (U : ℤ)

noncomputable def fourthCentralStripProbability (k T U : ℕ) : ℝ :=
  fourthSignedEventProbability k (fun y ↦ |y 0| ≤ (T : ℝ) ∧ |y 1| ≤ (U : ℝ))

lemma fourthCentralStripParameters_card (k T U : ℕ) :
    (fourthCentralStripParameters k T U).card ≤ (2 * T + 1) * (2 * U + 1) := by
  let target := signedIntLatticeTarget (fourthSignedIntegerVector k)
  let box := (Finset.Icc (-(T : ℤ)) (T : ℤ)).product
    (Finset.Icc (-(U : ℤ)) (U : ℤ))
  let f : (Fin 2 → ℤ) → ℤ × ℤ := fun d ↦ (target d 0, target d 1)
  have hmap : Set.MapsTo f (fourthCentralStripParameters k T U) box := by
    intro d hd
    change d ∈ fourthCentralStripParameters k T U at hd
    rw [fourthCentralStripParameters, Finset.mem_filter,
      fourthGaussianStripParameters, Finset.mem_filter] at hd
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hd.1.2),
      Finset.mem_Icc.mpr (abs_le.mp hd.2)⟩
  have hinj : Set.InjOn f (fourthCentralStripParameters k T U) := by
    intro d hd e he h
    apply signedIntLatticeTarget_injective (fourthSignedIntegerVector k)
    apply funext
    rw [Fin.forall_fin_two]
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  calc
    _ ≤ box.card := Finset.card_le_card_of_injOn f hmap hinj
    _ = (2 * T + 1) * (2 * U + 1) := by
      dsimp [box]
      rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
      congr 1 <;> omega

lemma fourthCentralStripProbability_eq_atom_sum (k T U : ℕ) :
    fourthCentralStripProbability k T U =
      ∑ d ∈ fourthCentralStripParameters k T U,
        fourthLatticeAtomProbability k d := by
  unfold fourthCentralStripProbability
  rw [fourthSignedEventProbability_eq_atom_sum]
  calc
    _ = ∑ d ∈ fourthAttainableLatticeParameters k,
        if d ∈ fourthCentralStripParameters k T U
          then fourthLatticeAtomProbability k d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have h0 : (|(signedIntLatticeTarget (fourthSignedIntegerVector k) d 0 : ℝ)| ≤ T) ↔
          |signedIntLatticeTarget (fourthSignedIntegerVector k) d 0| ≤ (T : ℤ) := by
        rw [← Int.cast_abs]
        constructor <;> intro h <;> exact_mod_cast h
      have h1 : (|(signedIntLatticeTarget (fourthSignedIntegerVector k) d 1 : ℝ)| ≤ U) ↔
          |signedIntLatticeTarget (fourthSignedIntegerVector k) d 1| ≤ (U : ℤ) := by
        rw [← Int.cast_abs]
        constructor <;> intro h <;> exact_mod_cast h
      by_cases hz0 : |signedIntLatticeTarget (fourthSignedIntegerVector k) d 0| ≤ (T : ℤ)
      · by_cases hz1 : |signedIntLatticeTarget (fourthSignedIntegerVector k) d 1| ≤ (U : ℤ)
        · have hmem : d ∈ fourthCentralStripParameters k T U := by
            simp [fourthCentralStripParameters, fourthGaussianStripParameters, hd, hz0, hz1]
          simp [hmem, h0.mpr hz0, h1.mpr hz1]
        · have hmem : d ∉ fourthCentralStripParameters k T U := by
            simp [fourthCentralStripParameters, hz1]
          have hr1 : ¬|(signedIntLatticeTarget (fourthSignedIntegerVector k) d 1 : ℝ)| ≤ U :=
            fun h ↦ hz1 (h1.mp h)
          simp [hmem, hr1]
      · have hmem : d ∉ fourthCentralStripParameters k T U := by
          simp [fourthCentralStripParameters, fourthGaussianStripParameters, hz0]
        have hr0 : ¬|(signedIntLatticeTarget (fourthSignedIntegerVector k) d 0 : ℝ)| ≤ T :=
          fun h ↦ hz0 (h0.mp h)
        simp [hmem, hr0]
    _ = _ := by
      rw [← Finset.sum_filter]
      have hsub : fourthCentralStripParameters k T U ⊆
          fourthAttainableLatticeParameters k := by
        intro d hd
        rw [fourthCentralStripParameters, Finset.mem_filter,
          fourthGaussianStripParameters, Finset.mem_filter] at hd
        exact hd.1.1
      have heq : (fourthAttainableLatticeParameters k).filter
          (fun d ↦ d ∈ fourthCentralStripParameters k T U) =
          fourthCentralStripParameters k T U := by
        ext d
        simp only [Finset.mem_filter]
        constructor
        · exact fun h ↦ h.2
        · exact fun h ↦ ⟨hsub h, h⟩
      rw [heq]

lemma fourthCentralStripProbability_le (N T U : ℕ) (hN : 21 ≤ N) :
    fourthCentralStripProbability (N + 2) T U ≤
      fourthGaussianStripMass (N + 2) T +
        (((2 * T + 1) * (2 * U + 1) : ℕ) : ℝ) * fourthFullAtomError N := by
  rw [fourthCentralStripProbability_eq_atom_sum]
  calc
    _ ≤ ∑ d ∈ fourthCentralStripParameters (N + 2) T U,
        (fourthGaussianFullAtom (N + 2) (fun j ↦
          (signedIntLatticeTarget (fourthSignedIntegerVector (N + 2)) d j : ℝ)) +
          fourthFullAtomError N) :=
      Finset.sum_le_sum fun d hd ↦ fourthLatticeAtomProbability_le_fullAtom_add N hN d
    _ = (∑ d ∈ fourthCentralStripParameters (N + 2) T U,
        fourthGaussianFullAtom (N + 2) (fun j ↦
          (signedIntLatticeTarget (fourthSignedIntegerVector (N + 2)) d j : ℝ))) +
        ((fourthCentralStripParameters (N + 2) T U).card : ℝ) *
          fourthFullAtomError N := by rw [Finset.sum_add_distrib]; simp
    _ ≤ fourthGaussianStripMass (N + 2) T +
        ((fourthCentralStripParameters (N + 2) T U).card : ℝ) *
          fourthFullAtomError N := by
      apply add_le_add
      · unfold fourthGaussianStripMass
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [fourthCentralStripParameters, Finset.mem_filter] at hd
          exact hd.1
        · intro d hd hnot
          exact fourthGaussianFullAtom_nonneg _ _
      · exact le_rfl
    _ ≤ fourthGaussianStripMass (N + 2) T +
        (((2 * T + 1) * (2 * U + 1) : ℕ) : ℝ) * fourthFullAtomError N := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast fourthCentralStripParameters_card (N + 2) T U
      · exact fourthFullAtomError_nonneg N hN

lemma fourthSignedStripProbability_split (k T U : ℕ) :
    fourthSignedStripProbability k T ≤
      fourthCentralStripProbability k T U +
        finiteRademacherAbsTailProbability (fourthIncrementWeight k) (U : ℝ) := by
  calc
    fourthSignedStripProbability k T ≤
        fourthCentralStripProbability k T U +
          fourthSignedEventProbability k (fun y ↦ (U : ℝ) ≤ |(y 1 : ℝ)|) := by
      unfold fourthSignedStripProbability fourthCentralStripProbability
      unfold fourthSignedEventProbability
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro e he
      by_cases h0 : |(fourthSignedPair k e 0 : ℝ)| ≤ T
      · by_cases h1 : |(fourthSignedPair k e 1 : ℝ)| ≤ U
        · by_cases ht : (U : ℝ) ≤ |(fourthSignedPair k e 1 : ℝ)| <;>
            simp [h0, h1, ht]
        · have ht : (U : ℝ) ≤ |(fourthSignedPair k e 1 : ℝ)| := le_of_not_ge h1
          simp [h0, h1, ht]
      · by_cases ht : (U : ℝ) ≤ |(fourthSignedPair k e 1 : ℝ)| <;>
          simp [h0, ht]
    _ = _ := by rw [fourthSignedTailEvent_eq]

lemma fourthSignedStripProbability_le_truncated (N T U : ℕ) (hN : 21 ≤ N) :
    fourthSignedStripProbability (N + 2) T ≤
      fourthGaussianStripMass (N + 2) T +
        (((2 * T + 1) * (2 * U + 1) : ℕ) : ℝ) * fourthFullAtomError N +
      2 * Real.exp (-((U : ℝ) ^ 2) /
        (2 * fourthIncrementVarianceB (N + 2))) := by
  calc
    _ ≤ fourthCentralStripProbability (N + 2) T U +
        finiteRademacherAbsTailProbability (fourthIncrementWeight (N + 2)) (U : ℝ) :=
      fourthSignedStripProbability_split _ _ _
    _ ≤ (fourthGaussianStripMass (N + 2) T +
          (((2 * T + 1) * (2 * U + 1) : ℕ) : ℝ) * fourthFullAtomError N) +
        2 * Real.exp (-((U : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2))) :=
      add_le_add (fourthCentralStripProbability_le N T U hN)
        (fourthSignedIncrement_abs_tail (N + 2) U)
    _ = _ := by ring

end Erdos521
