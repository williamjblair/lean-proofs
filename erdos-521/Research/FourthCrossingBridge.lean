import Research.FourthCrossingAsymptotics
import Research.WideIidPointwiseGate
import Mathlib.Tactic

open Filter
open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthCrossingBridgeDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def fourthBitsToSigns (k : ℕ) (ω : ℕ → Bool) :
    Option (Fin (k + 1)) → Bool
  | none => ω (k + 1)
  | some q => ω (k - q.val)

lemma fourthIntegratedSum_eq_reversed (ω : ℕ → Bool) (k : ℕ) :
    fourthIntegratedRademacherSum ω k =
      ∑ q : Fin (k + 1),
        (Nat.choose (q.val + 3) 3 : ℝ) * sign (ω (k - q.val)) := by
  rw [fourthIntegratedRademacherSum_eq_weighted_choose]
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin (k + 1),
      (Nat.choose (k - i.val + 3) 3 : ℝ) * sign (ω i.val)) =
      ∑ i : Fin (k + 1),
        (Nat.choose (i.rev.val + 3) 3 : ℝ) * sign (ω (k - i.rev.val)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hsub : k - (k - i.val) = i.val := by omega
      simp [Fin.rev, hsub]
    _ = _ := by
      simpa [finRevEquiv] using Equiv.sum_comp (finRevEquiv (k + 1))
        (fun q : Fin (k + 1) ↦
          (Nat.choose (q.val + 3) 3 : ℝ) * sign (ω (k - q.val)))

lemma fourthIntegratedIncrement_eq_reversed (ω : ℕ → Bool) (k : ℕ) :
    fourthIntegratedRademacherSum ω (k + 1) -
        fourthIntegratedRademacherSum ω k =
      sign (ω (k + 1)) +
        ∑ q : Fin (k + 1),
          (Nat.choose (q.val + 3) 2 : ℝ) * sign (ω (k - q.val)) := by
  rw [fourthIntegratedRademacherSum_eq_weighted_choose,
    fourthIntegratedRademacherSum_eq_weighted_choose]
  rw [Finset.sum_range_succ]
  have hnew :
      (Nat.choose (k + 1 - (k + 1) + 3) 3 : ℝ) * sign (ω (k + 1)) =
        sign (ω (k + 1)) := by norm_num
  rw [hnew]
  have hdiff :
      (∑ i ∈ Finset.range (k + 1),
        ((Nat.choose (k + 1 - i + 3) 3 : ℝ) * sign (ω i) -
          (Nat.choose (k - i + 3) 3 : ℝ) * sign (ω i))) =
      ∑ i ∈ Finset.range (k + 1),
        (Nat.choose (k - i + 3) 2 : ℝ) * sign (ω i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
    have hidx : k + 1 - i + 3 = (k - i + 3) + 1 := by omega
    rw [hidx, show 3 = 2 + 1 by omega, Nat.choose_succ_succ']
    push_cast
    ring
  have hsumdiff :
      (∑ i ∈ Finset.range (k + 1),
        (Nat.choose (k + 1 - i + 3) 3 : ℝ) * sign (ω i)) -
      (∑ i ∈ Finset.range (k + 1),
        (Nat.choose (k - i + 3) 3 : ℝ) * sign (ω i)) =
      ∑ i ∈ Finset.range (k + 1),
        (Nat.choose (k - i + 3) 2 : ℝ) * sign (ω i) := by
    rw [← Finset.sum_sub_distrib]
    exact hdiff
  rw [show
    (∑ i ∈ Finset.range (k + 1),
      (Nat.choose (k + 1 - i + 3) 3 : ℝ) * sign (ω i)) + sign (ω (k + 1)) -
      (∑ i ∈ Finset.range (k + 1),
        (Nat.choose (k - i + 3) 3 : ℝ) * sign (ω i)) =
      ((∑ i ∈ Finset.range (k + 1),
        (Nat.choose (k + 1 - i + 3) 3 : ℝ) * sign (ω i)) -
      (∑ i ∈ Finset.range (k + 1),
        (Nat.choose (k - i + 3) 3 : ℝ) * sign (ω i))) +
        sign (ω (k + 1)) by ring,
    hsumdiff, add_comm]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin (k + 1),
      (Nat.choose (k - i.val + 3) 2 : ℝ) * sign (ω i.val)) =
      ∑ i : Fin (k + 1),
        (Nat.choose (i.rev.val + 3) 2 : ℝ) * sign (ω (k - i.rev.val)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hsub : k - (k - i.val) = i.val := by omega
      simp [Fin.rev, hsub]
    _ = _ := by
      simpa [finRevEquiv] using Equiv.sum_comp (finRevEquiv (k + 1))
        (fun q : Fin (k + 1) ↦
          (Nat.choose (q.val + 3) 2 : ℝ) * sign (ω (k - q.val)))

lemma fourthSignedPair_zero_eq_integrated (ω : ℕ → Bool) (k : ℕ) :
    (fourthSignedPair k (fourthBitsToSigns k ω) 0 : ℝ) =
      fourthIntegratedRademacherSum ω k := by
  rw [fourthIntegratedSum_eq_reversed]
  unfold fourthSignedPair signedIntVectorSum
  rw [Fintype.sum_option]
  simp only [fourthSignedIntegerVector, fourthBitsToSigns]
  push_cast
  simp only [intCast_boolSignInt]
  norm_num [fourthIntegerA]
  apply Finset.sum_congr rfl
  intro q hq
  ring

lemma fourthSignedPair_one_eq_increment (ω : ℕ → Bool) (k : ℕ) :
    (fourthSignedPair k (fourthBitsToSigns k ω) 1 : ℝ) =
      fourthIntegratedRademacherSum ω (k + 1) -
        fourthIntegratedRademacherSum ω k := by
  rw [fourthIntegratedIncrement_eq_reversed]
  unfold fourthSignedPair signedIntVectorSum
  rw [Fintype.sum_option]
  simp only [fourthSignedIntegerVector, fourthBitsToSigns]
  push_cast
  simp only [intCast_boolSignInt]
  norm_num [fourthIntegerB]
  apply Finset.sum_congr rfl
  intro q hq
  ring

lemma fourthPairCrossing_bits_iff (ω : ℕ → Bool) (k : ℕ) :
    fourthPairCrossing (fourthSignedPair k (fourthBitsToSigns k ω)) ↔
      fourthIntegratedRademacherSum ω k *
        fourthIntegratedRademacherSum ω (k + 1) ≤ 0 := by
  unfold fourthPairCrossing
  have h0 := fourthSignedPair_zero_eq_integrated ω k
  have h1 := fourthSignedPair_one_eq_increment ω k
  exact_mod_cast (show
    (fourthSignedPair k (fourthBitsToSigns k ω) 0 : ℝ) *
      ((fourthSignedPair k (fourthBitsToSigns k ω) 0 : ℝ) +
        (fourthSignedPair k (fourthBitsToSigns k ω) 1 : ℝ)) ≤ 0 ↔ _ by
    rw [h0, h1]
    ring_nf)

noncomputable def fourthIndexEquiv (k : ℕ) :
    Fin (k + 2) ≃ Option (Fin (k + 1)) :=
  (finRevEquiv (k + 2)).trans (finSuccEquiv (k + 1))

noncomputable def fourthPrefixSignsEquiv (k : ℕ) :
    (Fin (k + 2) → Bool) ≃ (Option (Fin (k + 1)) → Bool) :=
  Equiv.arrowCongr (fourthIndexEquiv k) (Equiv.refl Bool)

lemma fourthPrefixSignsEquiv_none (k : ℕ) (y : Fin (k + 2) → Bool) :
    fourthPrefixSignsEquiv k y none = y ⟨k + 1, by omega⟩ := by
  simp [fourthPrefixSignsEquiv, fourthIndexEquiv, finRevEquiv,
    finSuccEquiv, finSuccEquiv', Fin.rev]

lemma fourthPrefixSignsEquiv_some (k : ℕ) (y : Fin (k + 2) → Bool)
    (q : Fin (k + 1)) :
    fourthPrefixSignsEquiv k y (some q) = y ⟨k - q.val, by omega⟩ := by
  simp [fourthPrefixSignsEquiv, fourthIndexEquiv, finRevEquiv,
    finSuccEquiv, finSuccEquiv', Fin.rev]

noncomputable def splitFiniteBitsEquiv (m n : ℕ) :
    (Fin (m + n) → Bool) ≃ (Fin m → Bool) × (Fin n → Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) Bool)

noncomputable def fourthFullBitsEquiv (k r : ℕ) (h : k + 2 ≤ 2 * r) :
    (Fin (2 * r) → Bool) ≃
      (Fin (k + 2) → Bool) × (Fin (2 * r - (k + 2)) → Bool) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le h).symm) (Equiv.refl Bool)).trans
    (splitFiniteBitsEquiv (k + 2) (2 * r - (k + 2)))

lemma fourthFullBitsEquiv_fst (k r : ℕ) (h : k + 2 ≤ 2 * r)
    (x : Fin (2 * r) → Bool) (i : Fin (k + 2)) :
    (fourthFullBitsEquiv k r h x).1 i = x ⟨i.val, by omega⟩ := rfl

lemma fourthPrefixSigns_fullBits (k r : ℕ) (h : k + 2 ≤ 2 * r)
    (x : Fin (2 * r) → Bool) :
    fourthPrefixSignsEquiv k (fourthFullBitsEquiv k r h x).1 =
      fourthBitsToSigns k (extendBits r x) := by
  funext i
  cases i with
  | none =>
      rw [fourthPrefixSignsEquiv_none]
      unfold fourthBitsToSigns
      rw [fourthFullBitsEquiv_fst, extendBits_of_lt]
  | some q =>
      rw [fourthPrefixSignsEquiv_some, fourthFullBitsEquiv_fst]
      change x ⟨k - q.val, by omega⟩ = extendBits r x (k - q.val)
      rw [extendBits_of_lt]

lemma fourthIntegratedCrossingIndicator_eq_signed (ω : ℕ → Bool) (k : ℕ) :
    (fourthIntegratedCrossingIndicator ω k : ℝ) =
      if fourthPairCrossing (fourthSignedPair k (fourthBitsToSigns k ω))
        then 1 else 0 := by
  unfold fourthIntegratedCrossingIndicator
  rw [if_congr (fourthPairCrossing_bits_iff ω k) rfl rfl]
  norm_num

noncomputable def fourthPrefixCrossingIndicator (k : ℕ)
    (y : Fin (k + 2) → Bool) : ℝ :=
  if fourthPairCrossing
      (fourthSignedPair k (fourthPrefixSignsEquiv k y)) then 1 else 0

lemma fourthIntegratedIndicator_full_eq_prefix (k r : ℕ)
    (h : k + 2 ≤ 2 * r) (x : Fin (2 * r) → Bool) :
    (fourthIntegratedCrossingIndicator (extendBits r x) k : ℝ) =
      fourthPrefixCrossingIndicator k (fourthFullBitsEquiv k r h x).1 := by
  rw [fourthIntegratedCrossingIndicator_eq_signed]
  unfold fourthPrefixCrossingIndicator
  rw [fourthPrefixSigns_fullBits]

lemma sum_prod_prefix_function (m n : ℕ) (J : (Fin m → Bool) → ℝ) :
    (∑ p : (Fin m → Bool) × (Fin n → Bool), J p.1) =
      (2 : ℝ) ^ n * ∑ y : Fin m → Bool, J y := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  push_cast
  rw [Finset.mul_sum]

lemma sum_fourthIntegratedIndicator_eq_prefix (k r : ℕ)
    (h : k + 2 ≤ 2 * r) :
    (∑ x : Fin (2 * r) → Bool,
      (fourthIntegratedCrossingIndicator (extendBits r x) k : ℝ)) =
      (2 : ℝ) ^ (2 * r - (k + 2)) *
        ∑ y : Fin (k + 2) → Bool, fourthPrefixCrossingIndicator k y := by
  calc
    (∑ x : Fin (2 * r) → Bool,
      (fourthIntegratedCrossingIndicator (extendBits r x) k : ℝ)) =
      ∑ p : (Fin (k + 2) → Bool) × (Fin (2 * r - (k + 2)) → Bool),
        fourthPrefixCrossingIndicator k p.1 := by
      apply Fintype.sum_equiv (fourthFullBitsEquiv k r h)
      intro x
      exact fourthIntegratedIndicator_full_eq_prefix k r h x
    _ = _ := sum_prod_prefix_function _ _ _

lemma sum_fourthPrefixCrossingIndicator_eq_signed (k : ℕ) :
    (∑ y : Fin (k + 2) → Bool, fourthPrefixCrossingIndicator k y) =
      ∑ e : Option (Fin (k + 1)) → Bool,
        if fourthPairCrossing (fourthSignedPair k e) then (1 : ℝ) else 0 := by
  apply Fintype.sum_equiv (fourthPrefixSignsEquiv k)
  intro y
  rfl

lemma fourthMinimalProbability_eq_signed (k : ℕ) :
    (∑ x : Fin (2 * fourthEdgePairLength k) → Bool,
        (fourthIntegratedCrossingIndicator
          (extendBits (fourthEdgePairLength k) x) k : ℝ)) /
        (2 : ℝ) ^ (2 * fourthEdgePairLength k) =
      fourthSignedCrossingProbability k := by
  let r := fourthEdgePairLength k
  let d := 2 * r - (k + 2)
  have h : k + 2 ≤ 2 * r := fourthEdgePairLength_contains k
  rw [sum_fourthIntegratedIndicator_eq_prefix k r h,
    sum_fourthPrefixCrossingIndicator_eq_signed]
  unfold fourthSignedCrossingProbability
  have hcard : Fintype.card (Option (Fin (k + 1))) = k + 2 := by simp
  rw [hcard]
  have hsum : k + 2 + d = 2 * r := Nat.add_sub_of_le h
  rw [← hsum, pow_add]
  have hdpos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  field_simp
  rw [show k + 2 + d - (k + 2) = d by omega]
  ring

theorem iidFourthWideOneSidedRate_proved : IidFourthWideOneSidedRate := by
  rcases (eventually_atTop.1 eventually_fourthSignedCrossing_rate) with ⟨N₀, hN₀⟩
  refine ⟨N₀ + 2, fun k hk ↦ ?_⟩
  have hk2 : 2 ≤ k := by omega
  have hNk : N₀ ≤ k - 2 := by omega
  rw [fourthMinimalProbability_eq_signed]
  have h := hN₀ (k - 2) hNk
  have heq : k - 2 + 2 = k := by omega
  have heq' : (((k - 2 : ℕ) : ℝ) + 3) = ((k : ℝ) + 1) := by
    exact_mod_cast (show k - 2 + 3 = k + 1 by omega)
  rw [heq, heq'] at h
  exact h

 theorem iidFourthWidePointwiseRate_proved : IidFourthWidePointwiseRate :=
  iidFourthWidePointwise_of_oneSided iidFourthWideOneSidedRate_proved

end Erdos521
