import Research.FourthGaussianStrip
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthStripLocalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthSignedStripProbability (k T : ℕ) : ℝ :=
  fourthSignedEventProbability k (fun y ↦ |y 0| ≤ (T : ℝ))

lemma fourthSignedStripProbability_eq_atom_sum (k T : ℕ) :
    fourthSignedStripProbability k T =
      ∑ d ∈ fourthGaussianStripParameters k T, fourthLatticeAtomProbability k d := by
  unfold fourthSignedStripProbability
  rw [fourthSignedEventProbability_eq_atom_sum]
  calc
    _ = ∑ d ∈ fourthAttainableLatticeParameters k,
        if d ∈ fourthGaussianStripParameters k T
          then fourthLatticeAtomProbability k d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have heq : (|signedIntLatticeTarget (fourthSignedIntegerVector k) d 0| : ℝ) ≤ T ↔
          |signedIntLatticeTarget (fourthSignedIntegerVector k) d 0| ≤ (T : ℤ) := by
        constructor <;> intro h <;> exact_mod_cast h
      by_cases hz : |signedIntLatticeTarget (fourthSignedIntegerVector k) d 0| ≤ (T : ℤ)
      · have hr := heq.mpr hz
        have hmem : d ∈ fourthGaussianStripParameters k T := by
          simp [fourthGaussianStripParameters, hd, hz]
        simp [hmem, hr]
      · have hr : ¬(|signedIntLatticeTarget (fourthSignedIntegerVector k) d 0| : ℝ) ≤ T :=
          fun h ↦ hz (heq.mp h)
        have hmem : d ∉ fourthGaussianStripParameters k T := by
          simp [fourthGaussianStripParameters, hz]
        simp [hmem, hr]
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp [fourthGaussianStripParameters]

lemma fourthGaussianStripParameters_card (k T : ℕ) :
    (fourthGaussianStripParameters k T).card ≤
      (2 * T + 1) * (fourthIncrementL1 k + 1) := by
  let S := fourthGaussianStripParameters k T
  let box := (Finset.Icc (-(T : ℤ)) (T : ℤ)).product
    (Finset.range (fourthIncrementL1 k + 1))
  let target := signedIntLatticeTarget (fourthSignedIntegerVector k)
  let f : (Fin 2 → ℤ) → ℤ × ℕ := fun d ↦
    (target d 0, fourthIncrementMeshIndex k d)
  have hmap : Set.MapsTo f S box := by
    intro d hd
    have hd' := hd
    change d ∈ fourthGaussianStripParameters k T at hd'
    rw [fourthGaussianStripParameters, Finset.mem_filter] at hd'
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hd'.2),
      Finset.mem_range.mpr (fourthIncrementMeshIndex_lt k d hd'.1)⟩
  have hinj : Set.InjOn f S := by
    intro d hd e he h
    apply signedIntLatticeTarget_injective (fourthSignedIntegerVector k)
    apply funext
    rw [Fin.forall_fin_two]
    have h0 : target d 0 = target e 0 := congrArg Prod.fst h
    have hi : fourthIncrementMeshIndex k d = fourthIncrementMeshIndex k e :=
      congrArg Prod.snd h
    have hd' := hd
    have he' := he
    change d ∈ fourthGaussianStripParameters k T at hd'
    change e ∈ fourthGaussianStripParameters k T at he'
    rw [fourthGaussianStripParameters, Finset.mem_filter] at hd' he'
    have h1d := fourthLatticeTarget_one_eq_mesh_int k d hd'.1
    have h1e := fourthLatticeTarget_one_eq_mesh_int k e he'.1
    exact ⟨h0, h1d.trans ((congrArg (fourthIncrementMeshValue k) hi).trans h1e.symm)⟩
  calc
    S.card ≤ box.card := Finset.card_le_card_of_injOn f hmap hinj
    _ = (2 * T + 1) * (fourthIncrementL1 k + 1) := by
      dsimp [box]
      rw [Finset.card_product, Int.card_Icc, Finset.card_range]
      congr 1
      omega

lemma fourthSignedStripProbability_le_explicit (N T : ℕ) (hN : 21 ≤ N) :
    fourthSignedStripProbability (N + 2) T ≤
      fourthGaussianStripMass (N + 2) T +
        (((2 * T + 1) * (fourthIncrementL1 (N + 2) + 1) : ℕ) : ℝ) *
          fourthFullAtomError N := by
  rw [fourthSignedStripProbability_eq_atom_sum]
  calc
    _ ≤ ∑ d ∈ fourthGaussianStripParameters (N + 2) T,
        (fourthGaussianFullAtom (N + 2) (fun j ↦
          (signedIntLatticeTarget (fourthSignedIntegerVector (N + 2)) d j : ℝ)) +
            fourthFullAtomError N) := by
      exact Finset.sum_le_sum fun d hd ↦
        fourthLatticeAtomProbability_le_fullAtom_add N hN d
    _ = fourthGaussianStripMass (N + 2) T +
        ((fourthGaussianStripParameters (N + 2) T).card : ℝ) *
          fourthFullAtomError N := by
      rw [Finset.sum_add_distrib]
      simp [fourthGaussianStripMass]
    _ ≤ fourthGaussianStripMass (N + 2) T +
        (((2 * T + 1) * (fourthIncrementL1 (N + 2) + 1) : ℕ) : ℝ) *
          fourthFullAtomError N := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast fourthGaussianStripParameters_card (N + 2) T
      · exact fourthFullAtomError_nonneg N hN

lemma fourthSignedStripProbability_le_full (N T : ℕ) (hN : 21 ≤ N) :
    fourthSignedStripProbability (N + 2) T ≤
      ((2 * T + 1 : ℕ) : ℝ) *
        (2 / (Real.pi * Real.sqrt (fourthDet (N + 2)))) *
        (Real.exp 1 * 2 *
          (1 + 1 / (2 * (fourthVarianceA (N + 2) / (2 * fourthDet (N + 2))) *
            Real.sqrt (2 * fourthDet (N + 2) / fourthVarianceA (N + 2))))) +
      (((2 * T + 1) * (fourthIncrementL1 (N + 2) + 1) : ℕ) : ℝ) *
        fourthFullAtomError N := by
  exact (fourthSignedStripProbability_le_explicit N T hN).trans
    (add_le_add (fourthGaussianStripMass_le (N + 2) T) (le_refl _))

end Erdos521
