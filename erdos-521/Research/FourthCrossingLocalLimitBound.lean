import Research.FourthGaussianCrossingMass
import Mathlib.Tactic

open scoped BigOperators
namespace Erdos521

noncomputable local instance fourthCrossingLocalLimitDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthSignedEventProbability (k : ℕ)
    (P : (Fin 2 → ℤ) → Prop) : ℝ :=
  (∑ e : Option (Fin (k + 1)) → Bool,
    if P (fourthSignedPair k e) then (1 : ℝ) else 0) /
      (2 : ℝ) ^ Fintype.card (Option (Fin (k + 1)))

lemma fourthSignedEventProbability_eq_atom_sum (k : ℕ)
    (P : (Fin 2 → ℤ) → Prop) :
    fourthSignedEventProbability k P =
      ∑ d ∈ fourthAttainableLatticeParameters k,
        if P (signedIntLatticeTarget (fourthSignedIntegerVector k) d)
          then fourthLatticeAtomProbability k d else 0 := by
  let E := Option (Fin (k + 1)) → Bool
  let p : E → (Fin 2 → ℤ) := fourthSignedLatticeParameter k
  let I : E → ℝ := fun e ↦ if P (fourthSignedPair k e) then 1 else 0
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset E))
    (t := fourthAttainableLatticeParameters k)
    (g := p) (fun e he ↦ fourthSignedLatticeParameter_mem k e) I
  have hinner (d : Fin 2 → ℤ) :
      (∑ e ∈ (Finset.univ : Finset E) with p e = d, I e) =
        if P (signedIntLatticeTarget (fourthSignedIntegerVector k) d)
          then (∑ e : E, if p e = d then (1 : ℝ) else 0) else 0 := by
    by_cases hd : P (signedIntLatticeTarget (fourthSignedIntegerVector k) d)
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
  unfold fourthSignedEventProbability
  rw [show (∑ e : Option (Fin (k + 1)) → Bool,
      if P (fourthSignedPair k e) then (1 : ℝ) else 0) = ∑ e : E, I e by rfl]
  rw [← hfiber, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hinner]
  by_cases hP : P (signedIntLatticeTarget (fourthSignedIntegerVector k) d)
  · rw [if_pos hP, if_pos hP, fourthLatticeAtomProbability_eq_fiber]
  · rw [if_neg hP, if_neg hP, zero_div]

noncomputable def fourthCentralCrossingLatticeParameters (k L : ℕ) :
    Finset (Fin 2 → ℤ) :=
  (fourthCrossingLatticeParameters k).filter fun d ↦
    |(signedIntLatticeTarget (fourthSignedIntegerVector k) d 1 : ℝ)| < (L : ℝ)

lemma fourthCentralCrossingLatticeParameters_card (k L : ℕ) :
    (fourthCentralCrossingLatticeParameters k L).card ≤ (2 * L + 1) ^ 2 := by
  let target := signedIntLatticeTarget (fourthSignedIntegerVector k)
  let box := (Finset.Icc (-(L : ℤ)) (L : ℤ)).product
    (Finset.Icc (-(L : ℤ)) (L : ℤ))
  let f : (Fin 2 → ℤ) → ℤ × ℤ := fun d ↦ (target d 0, target d 1)
  have hmap : Set.MapsTo f (fourthCentralCrossingLatticeParameters k L) box := by
    intro d hd
    have hdFin : d ∈ fourthCentralCrossingLatticeParameters k L := hd
    rw [fourthCentralCrossingLatticeParameters, Finset.mem_filter] at hdFin
    have hdCross := hdFin.1
    rw [fourthCrossingLatticeParameters, Finset.mem_filter] at hdCross
    have hcross : fourthPairCrossing (target d) := hdCross.2
    have hcrossR : (target d 0 : ℝ) * ((target d 0 : ℝ) + (target d 1 : ℝ)) ≤ 0 := by
      exact_mod_cast hcross
    have hdom := abs_le_abs_of_crossing hcrossR
    have h1 : |(target d 1 : ℝ)| < (L : ℝ) := by
      simpa [target] using hdFin.2
    have h0 : |(target d 0 : ℝ)| < (L : ℝ) := lt_of_le_of_lt hdom h1
    have bounds (z : ℤ) (hz : |(z : ℝ)| < (L : ℝ)) :
        -(L : ℤ) ≤ z ∧ z ≤ (L : ℤ) := by
      have hb := abs_lt.mp hz
      constructor
      · exact_mod_cast hb.1.le
      · exact_mod_cast hb.2.le
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (bounds _ h0),
      Finset.mem_Icc.mpr (bounds _ h1)⟩
  have hinj : Set.InjOn f (fourthCentralCrossingLatticeParameters k L) := by
    intro d₁ hd₁ d₂ hd₂ heq
    apply signedIntLatticeTarget_injective (fourthSignedIntegerVector k)
    apply funext
    rw [Fin.forall_fin_two]
    exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  calc
    (fourthCentralCrossingLatticeParameters k L).card ≤ box.card :=
      Finset.card_le_card_of_injOn f hmap hinj
    _ = (2 * L + 1) ^ 2 := by
      dsimp [box]
      rw [Finset.card_product, Int.card_Icc]
      have hcard : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
      rw [hcard]
      simp [pow_two]

noncomputable def fourthCentralSignedCrossingProbability (k L : ℕ) : ℝ :=
  fourthSignedEventProbability k (fun y ↦
    fourthPairCrossing y ∧ |(y 1 : ℝ)| < (L : ℝ))

lemma fourthCentralSignedCrossingProbability_eq_atom_sum (k L : ℕ) :
    fourthCentralSignedCrossingProbability k L =
      ∑ d ∈ fourthCentralCrossingLatticeParameters k L,
        fourthLatticeAtomProbability k d := by
  unfold fourthCentralSignedCrossingProbability
  rw [fourthSignedEventProbability_eq_atom_sum]
  calc
    _ = ∑ d ∈ fourthAttainableLatticeParameters k,
        if d ∈ fourthCentralCrossingLatticeParameters k L
          then fourthLatticeAtomProbability k d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [fourthCentralCrossingLatticeParameters,
        fourthCrossingLatticeParameters, hd]
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [fourthCentralCrossingLatticeParameters,
        fourthCrossingLatticeParameters, Finset.mem_filter]
      tauto

lemma fourthSignedTailEvent_eq (k L : ℕ) :
    fourthSignedEventProbability k (fun y ↦ (L : ℝ) ≤ |(y 1 : ℝ)|) =
      finiteRademacherAbsTailProbability (fourthIncrementWeight k) (L : ℝ) := by
  classical
  unfold fourthSignedEventProbability finiteRademacherAbsTailProbability
  simp_rw [finiteRademacherRealSum_fourthIncrementWeight]
  simp only [Finset.sum_boole]
  congr 2
  congr 1
  ext e
  simp

lemma fourthSignedCrossingProbability_split (k L : ℕ) :
    fourthSignedCrossingProbability k ≤
      fourthCentralSignedCrossingProbability k L +
        finiteRademacherAbsTailProbability (fourthIncrementWeight k) (L : ℝ) := by
  calc
    fourthSignedCrossingProbability k ≤
        fourthCentralSignedCrossingProbability k L +
          fourthSignedEventProbability k (fun y ↦
            (L : ℝ) ≤ |(y 1 : ℝ)|) := by
      unfold fourthSignedCrossingProbability fourthCentralSignedCrossingProbability
      unfold fourthSignedEventProbability
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro e he
      by_cases hc : fourthPairCrossing (fourthSignedPair k e)
      · by_cases hl : |(fourthSignedPair k e 1 : ℝ)| < (L : ℝ)
        · have hntail : ¬(L : ℝ) ≤ |(fourthSignedPair k e 1 : ℝ)| := not_le_of_gt hl
          simp [hc, hl, hntail]
        · have htail : (L : ℝ) ≤ |(fourthSignedPair k e 1 : ℝ)| := le_of_not_gt hl
          simp [hc, hl, htail]
      · by_cases htail : (L : ℝ) ≤ |(fourthSignedPair k e 1 : ℝ)|
        · simp [hc, htail]
        · simp [hc, htail]
    _ = _ := by rw [fourthSignedTailEvent_eq]

noncomputable def fourthFullAtomError (N : ℕ) : ℝ :=
  (1 / Real.pi ^ 2 : ℝ) * fourthFourierL1ErrorBound N +
    fourthGaussianFourierTailBound (N + 2)

lemma fourthFullAtomError_nonneg (N : ℕ) (hN : 21 ≤ N) :
    0 ≤ fourthFullAtomError N := by
  have h := fourthLatticeAtomProbability_sub_gaussianFullAtom N hN
    (fun _j ↦ (0 : ℤ))
  exact le_trans (norm_nonneg _) (by simpa [fourthFullAtomError] using h)

lemma fourthLatticeAtomProbability_le_fullAtom_add (N : ℕ) (hN : 21 ≤ N)
    (d : Fin 2 → ℤ) :
    fourthLatticeAtomProbability (N + 2) d ≤
      fourthGaussianFullAtom (N + 2) (fun j ↦
        (signedIntLatticeTarget (fourthSignedIntegerVector (N + 2)) d j : ℝ)) +
        fourthFullAtomError N := by
  have h := fourthLatticeAtomProbability_sub_gaussianFullAtom N hN d
  have habs :
      |fourthLatticeAtomProbability (N + 2) d -
        fourthGaussianFullAtom (N + 2) (fun j ↦
          (signedIntLatticeTarget (fourthSignedIntegerVector (N + 2)) d j : ℝ))| ≤
        fourthFullAtomError N := by
    simpa [fourthFullAtomError, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using h
  linarith [le_abs_self (fourthLatticeAtomProbability (N + 2) d -
    fourthGaussianFullAtom (N + 2) (fun j ↦
      (signedIntLatticeTarget (fourthSignedIntegerVector (N + 2)) d j : ℝ)))]

lemma fourthCentralSignedCrossingProbability_le (N L : ℕ) (hN : 21 ≤ N) :
    fourthCentralSignedCrossingProbability (N + 2) L ≤
      fourthGaussianCrossingMass (N + 2) +
        ((2 * L + 1 : ℕ) : ℝ) ^ 2 * fourthFullAtomError N := by
  let G : (Fin 2 → ℤ) → ℝ := fun d ↦
    fourthGaussianFullAtom (N + 2) (fun j ↦
      (signedIntLatticeTarget (fourthSignedIntegerVector (N + 2)) d j : ℝ))
  have hsubset : fourthCentralCrossingLatticeParameters (N + 2) L ⊆
      fourthCrossingLatticeParameters (N + 2) := by
    intro d hd
    have h := hd
    rw [fourthCentralCrossingLatticeParameters, Finset.mem_filter] at h
    exact h.1
  have hG :
      (∑ d ∈ fourthCentralCrossingLatticeParameters (N + 2) L, G d) ≤
        fourthGaussianCrossingMass (N + 2) := by
    unfold fourthGaussianCrossingMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun d hd hnot ↦ fourthGaussianFullAtom_nonneg _ _)
  have hcardR :
      ((fourthCentralCrossingLatticeParameters (N + 2) L).card : ℝ) ≤
        ((2 * L + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast fourthCentralCrossingLatticeParameters_card (N + 2) L
  rw [fourthCentralSignedCrossingProbability_eq_atom_sum]
  calc
    (∑ d ∈ fourthCentralCrossingLatticeParameters (N + 2) L,
      fourthLatticeAtomProbability (N + 2) d) ≤
        ∑ d ∈ fourthCentralCrossingLatticeParameters (N + 2) L,
          (G d + fourthFullAtomError N) := by
      exact Finset.sum_le_sum fun d hd ↦
        fourthLatticeAtomProbability_le_fullAtom_add N hN d
    _ = (∑ d ∈ fourthCentralCrossingLatticeParameters (N + 2) L, G d) +
        ((fourthCentralCrossingLatticeParameters (N + 2) L).card : ℝ) *
          fourthFullAtomError N := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ fourthGaussianCrossingMass (N + 2) +
        ((2 * L + 1 : ℕ) : ℝ) ^ 2 * fourthFullAtomError N := by
      exact add_le_add hG (mul_le_mul_of_nonneg_right hcardR
        (fourthFullAtomError_nonneg N hN))

lemma fourthSignedCrossingProbability_le_explicit (N L : ℕ) (hN : 21 ≤ N) :
    fourthSignedCrossingProbability (N + 2) ≤
      Real.exp (fourthIncrementGaussianRate (N + 2)) *
          (Real.sqrt (fourthDet (N + 2)) /
            (Real.pi * fourthVarianceA (N + 2))) +
        8 * (fourthIncrementL1 (N + 2) + 1 : ℝ) /
          (Real.pi * Real.sqrt (fourthDet (N + 2))) +
        ((2 * L + 1 : ℕ) : ℝ) ^ 2 * fourthFullAtomError N +
        2 * Real.exp (-((L : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2))) := by
  calc
    fourthSignedCrossingProbability (N + 2) ≤
        fourthCentralSignedCrossingProbability (N + 2) L +
          finiteRademacherAbsTailProbability
            (fourthIncrementWeight (N + 2)) (L : ℝ) :=
      fourthSignedCrossingProbability_split _ _
    _ ≤ (fourthGaussianCrossingMass (N + 2) +
          ((2 * L + 1 : ℕ) : ℝ) ^ 2 * fourthFullAtomError N) +
        2 * Real.exp (-((L : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2))) := by
      exact add_le_add (fourthCentralSignedCrossingProbability_le N L hN)
        (fourthSignedIncrement_abs_tail (N + 2) L)
    _ ≤ (Real.exp (fourthIncrementGaussianRate (N + 2)) *
          (Real.sqrt (fourthDet (N + 2)) /
            (Real.pi * fourthVarianceA (N + 2))) +
        8 * (fourthIncrementL1 (N + 2) + 1 : ℝ) /
          (Real.pi * Real.sqrt (fourthDet (N + 2))) +
          ((2 * L + 1 : ℕ) : ℝ) ^ 2 * fourthFullAtomError N) +
        2 * Real.exp (-((L : ℝ) ^ 2) /
          (2 * fourthIncrementVarianceB (N + 2))) := by
      gcongr
      exact fourthGaussianCrossingMass_le (N + 2)
    _ = _ := by ring

end Erdos521
