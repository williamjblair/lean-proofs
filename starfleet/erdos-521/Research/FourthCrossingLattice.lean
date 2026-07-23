import Research.FourthGaussianFourier
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthCrossingLatticeDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthSignedPair (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) : Fin 2 → ℤ :=
  signedIntVectorSum (fourthSignedIntegerVector k) e

noncomputable def fourthSignedLatticeParameter (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) : Fin 2 → ℤ :=
  fun j ↦ -signedIntVectorNegativeSum (fourthSignedIntegerVector k) e j

lemma fourthSignedPair_eq_latticeTarget (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) :
    fourthSignedPair k e =
      signedIntLatticeTarget (fourthSignedIntegerVector k)
        (fourthSignedLatticeParameter k e) := by
  funext j
  unfold fourthSignedPair fourthSignedLatticeParameter signedIntLatticeTarget
  rw [signedIntVectorSum_eq_base_sub_two_negative]
  ring

lemma signedIntLatticeTarget_injective {ι : Type*} [Fintype ι]
    (v : ι → Fin 2 → ℤ) :
    Function.Injective (signedIntLatticeTarget v) := by
  intro d₁ d₂ h
  funext j
  have hj := congrFun h j
  unfold signedIntLatticeTarget at hj
  omega

lemma fourthSignedPair_eq_target_iff (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) (d : Fin 2 → ℤ) :
    fourthSignedPair k e = signedIntLatticeTarget (fourthSignedIntegerVector k) d ↔
      fourthSignedLatticeParameter k e = d := by
  rw [fourthSignedPair_eq_latticeTarget]
  exact (signedIntLatticeTarget_injective (fourthSignedIntegerVector k)).eq_iff

noncomputable def fourthAttainableLatticeParameters (k : ℕ) : Finset (Fin 2 → ℤ) :=
  Finset.univ.image (fourthSignedLatticeParameter k)

lemma fourthSignedLatticeParameter_mem (k : ℕ)
    (e : Option (Fin (k + 1)) → Bool) :
    fourthSignedLatticeParameter k e ∈ fourthAttainableLatticeParameters k := by
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩

lemma fourthLatticeAtomProbability_eq_fiber (k : ℕ) (d : Fin 2 → ℤ) :
    fourthLatticeAtomProbability k d =
      (∑ e : Option (Fin (k + 1)) → Bool,
        if fourthSignedLatticeParameter k e = d then (1 : ℝ) else 0) /
        (2 : ℝ) ^ Fintype.card (Option (Fin (k + 1))) := by
  unfold fourthLatticeAtomProbability signedIntAtomProbability
  apply congrArg (fun z : ℝ ↦ z / (2 : ℝ) ^ Fintype.card (Option (Fin (k + 1))))
  apply Finset.sum_congr rfl
  intro e he
  change (if fourthSignedPair k e =
      signedIntLatticeTarget (fourthSignedIntegerVector k) d then (1 : ℝ) else 0) = _
  have hiff := fourthSignedPair_eq_target_iff k e d
  by_cases h : fourthSignedLatticeParameter k e = d
  · simp [h, hiff.mpr h]
  · have hn : ¬ fourthSignedPair k e =
        signedIntLatticeTarget (fourthSignedIntegerVector k) d := fun hs ↦ h (hiff.mp hs)
    simp [h, hn]

/-- Crossing predicate in old-sum/increment coordinates. -/
def fourthPairCrossing (y : Fin 2 → ℤ) : Prop :=
  y 0 * (y 0 + y 1) ≤ 0

noncomputable def fourthSignedCrossingProbability (k : ℕ) : ℝ :=
  (∑ e : Option (Fin (k + 1)) → Bool,
    if fourthPairCrossing (fourthSignedPair k e) then (1 : ℝ) else 0) /
      (2 : ℝ) ^ Fintype.card (Option (Fin (k + 1)))

/-- Exact partition of the finite sign probability into distinct affine-lattice atoms. -/
lemma fourthSignedCrossingProbability_eq_atom_sum (k : ℕ) :
    fourthSignedCrossingProbability k =
      ∑ d ∈ fourthAttainableLatticeParameters k,
        if fourthPairCrossing
            (signedIntLatticeTarget (fourthSignedIntegerVector k) d)
          then fourthLatticeAtomProbability k d else 0 := by
  let E := Option (Fin (k + 1)) → Bool
  let p : E → (Fin 2 → ℤ) := fourthSignedLatticeParameter k
  let I : E → ℝ := fun e ↦ if fourthPairCrossing (fourthSignedPair k e) then 1 else 0
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset E))
    (t := fourthAttainableLatticeParameters k)
    (g := p) (fun e he ↦ fourthSignedLatticeParameter_mem k e) I
  have hinner (d : Fin 2 → ℤ) :
      (∑ e ∈ (Finset.univ : Finset E) with p e = d, I e) =
        if fourthPairCrossing
            (signedIntLatticeTarget (fourthSignedIntegerVector k) d)
          then (∑ e : E, if p e = d then (1 : ℝ) else 0) else 0 := by
    by_cases hd : fourthPairCrossing
        (signedIntLatticeTarget (fourthSignedIntegerVector k) d)
    · rw [if_pos hd]
      calc
        (∑ e ∈ (Finset.univ : Finset E) with p e = d, I e) =
            ∑ e ∈ (Finset.univ : Finset E) with p e = d, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
          have hpair : fourthSignedPair k e =
              signedIntLatticeTarget (fourthSignedIntegerVector k) d := by
            rw [fourthSignedPair_eq_latticeTarget]
            exact congrArg (signedIntLatticeTarget (fourthSignedIntegerVector k)) he
          simp [I, hpair, hd]
        _ = ∑ e : E, if p e = d then (1 : ℝ) else 0 :=
          Finset.sum_filter (fun e : E ↦ p e = d) (fun _e ↦ (1 : ℝ))
    · rw [if_neg hd]
      apply Finset.sum_eq_zero
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      have hpair : fourthSignedPair k e =
          signedIntLatticeTarget (fourthSignedIntegerVector k) d := by
        rw [fourthSignedPair_eq_latticeTarget]
        exact congrArg (signedIntLatticeTarget (fourthSignedIntegerVector k)) he
      simp [I, hpair, hd]
  unfold fourthSignedCrossingProbability
  rw [show (∑ e : Option (Fin (k + 1)) → Bool,
      if fourthPairCrossing (fourthSignedPair k e) then (1 : ℝ) else 0) =
      ∑ e : E, I e by rfl]
  rw [← hfiber]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hinner]
  by_cases hcross : fourthPairCrossing
      (signedIntLatticeTarget (fourthSignedIntegerVector k) d)
  · rw [if_pos hcross, if_pos hcross, fourthLatticeAtomProbability_eq_fiber]
  · rw [if_neg hcross, if_neg hcross, zero_div]

end Erdos521
