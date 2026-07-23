import Research.FourthIidPointwiseDefinitions
import Research.FourthPairDecomposition
import Research.FiniteWordPrefix

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthLengthDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def bitsTwoSidedFourthIndicator {r : ℕ}
    (x : Fin (2 * r) → Bool) (k : ℕ) : ℕ :=
  fourthIntegratedCrossingIndicator (extendBits r x) k +
    fourthIntegratedCrossingIndicator (oddTwist (extendBits r x)) k

lemma sum_axisWord_indicator_eq_bits (r k : ℕ) :
    (∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) =
      ∑ x : Fin (2 * r) → Bool, (bitsTwoSidedFourthIndicator x k : ℝ) := by
  change (∑ w : AxisWord r,
      (bitsTwoSidedFourthIndicator (axisWordBitsEquiv r w) k : ℝ)) = _
  exact Equiv.sum_comp (axisWordBitsEquiv r) (fun x ↦ (bitsTwoSidedFourthIndicator x k : ℝ))

lemma fourthSum_congr_prefix {ω τ : ℕ → Bool} {k : ℕ}
    (h : ∀ i ≤ k, ω i = τ i) :
    fourthIntegratedRademacherSum ω k = fourthIntegratedRademacherSum τ k := by
  rw [fourthIntegratedRademacherSum_eq_weighted_choose,
    fourthIntegratedRademacherSum_eq_weighted_choose]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by
    have := Finset.mem_range.mp hi
    omega
  rw [h i hik]

lemma fourthIndicator_congr_prefix {ω τ : ℕ → Bool} {k : ℕ}
    (h : ∀ i ≤ k + 1, ω i = τ i) :
    fourthIntegratedCrossingIndicator ω k = fourthIntegratedCrossingIndicator τ k := by
  unfold fourthIntegratedCrossingIndicator
  rw [fourthSum_congr_prefix (fun i hi ↦ h i (by omega)),
    fourthSum_congr_prefix h]

/-- Split a word of `2(r+s)` coefficient bits into its first `2r` bits and remaining `2s` bits. -/
def splitPairBitsEquiv (r s : ℕ) :
    (Fin (2 * (r + s)) → Bool) ≃
      ((Fin (2 * r) → Bool) × (Fin (2 * s) → Bool)) :=
  (Equiv.piCongrLeft (fun _ : Fin (2 * (r + s)) ↦ Bool)
    (Fin.castOrderIso (by omega : 2 * r + 2 * s = 2 * (r + s)))).symm.trans
      (splitBoolWordEquiv (2 * r) (2 * s))

@[simp] lemma splitPairBitsEquiv_fst (r s : ℕ) (x : Fin (2 * (r + s)) → Bool)
    (i : Fin (2 * r)) :
    (splitPairBitsEquiv r s x).1 i = x ⟨i.val, by omega⟩ := by
  rfl

lemma extendBits_split_fst {r s : ℕ} (x : Fin (2 * (r + s)) → Bool)
    (i : ℕ) (hi : i < 2 * r) :
    extendBits (r + s) x i =
      extendBits r (splitPairBitsEquiv r s x).1 i := by
  rw [extendBits_of_lt _ (by omega), extendBits_of_lt _ hi]
  rfl

lemma bitsIndicator_split_fst {r s k : ℕ} (x : Fin (2 * (r + s)) → Bool)
    (hk : k + 2 ≤ 2 * r) :
    bitsTwoSidedFourthIndicator x k =
      bitsTwoSidedFourthIndicator (splitPairBitsEquiv r s x).1 k := by
  unfold bitsTwoSidedFourthIndicator
  congr 1
  · apply fourthIndicator_congr_prefix
    intro i hi
    exact extendBits_split_fst x i (by omega)
  · apply fourthIndicator_congr_prefix
    intro i hi
    unfold oddTwist
    rw [extendBits_split_fst x i (by omega)]

/-- Once an edge is contained in a finite iid word, appending independent bits does not change its
crossing probability. -/
lemma iidFourthIndicator_probability_length_independent (r s k : ℕ)
    (hk : k + 2 ≤ 2 * r) :
    (∑ w : AxisWord (r + s), (terminalTwoSidedFourthIndicator w k : ℝ)) /
        (4 : ℝ) ^ (r + s) =
      (∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) /
        (4 : ℝ) ^ r := by
  rw [sum_axisWord_indicator_eq_bits, sum_axisWord_indicator_eq_bits]
  have hsum :
      (∑ x : Fin (2 * (r + s)) → Bool, (bitsTwoSidedFourthIndicator x k : ℝ)) =
        (4 : ℝ) ^ s *
          ∑ y : Fin (2 * r) → Bool, (bitsTwoSidedFourthIndicator y k : ℝ) := by
    calc
      _ = ∑ z : (Fin (2 * r) → Bool) × (Fin (2 * s) → Bool),
          (bitsTwoSidedFourthIndicator z.1 k : ℝ) := by
        rw [← Equiv.sum_comp (splitPairBitsEquiv r s)
          (fun z ↦ (bitsTwoSidedFourthIndicator z.1 k : ℝ))]
        apply Finset.sum_congr rfl
        intro x hx
        rw [bitsIndicator_split_fst x hk]
      _ = (4 : ℝ) ^ s *
          ∑ y : Fin (2 * r) → Bool, (bitsTwoSidedFourthIndicator y k : ℝ) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, nsmul_eq_mul]
        simp
        rw [← Finset.mul_sum]
        congr 1
        rw [pow_mul]
        norm_num
  rw [hsum, pow_add]
  have hr : (0 : ℝ) < 4 ^ r := by positivity
  have hs : (0 : ℝ) < 4 ^ s := by positivity
  field_simp

/-- Smallest paired-word length containing coefficient edge `k`. -/
def fourthEdgePairLength (k : ℕ) : ℕ := (k + 3) / 2

lemma fourthEdgePairLength_contains (k : ℕ) :
    k + 2 ≤ 2 * fourthEdgePairLength k := by
  unfold fourthEdgePairLength
  omega

lemma fourthEdgePairLength_minimal {r k : ℕ} (hk : k + 2 ≤ 2 * r) :
    fourthEdgePairLength k ≤ r := by
  unfold fourthEdgePairLength
  omega

/-- Equivalent one-variable formulation of F-055's local-limit target. -/
def IidFourthMinimalRate : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    (∑ w : AxisWord (fourthEdgePairLength k),
        (terminalTwoSidedFourthIndicator w k : ℝ)) /
        (4 : ℝ) ^ fourthEdgePairLength k ≤
      (12 : ℝ) / (25 * (k + 1 : ℝ))

lemma iidFourthPointwiseRate_iff_minimal :
    IidFourthPointwiseRate ↔ IidFourthMinimalRate := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, fun k hk ↦ hK (fourthEdgePairLength k) k hk ?_⟩
    have := fourthEdgePairLength_contains k
    omega
  · rintro ⟨K, hK⟩
    refine ⟨K, fun r k hk hkr ↦ ?_⟩
    have hcontain : k + 2 ≤ 2 * r := by omega
    have hmin := fourthEdgePairLength_minimal hcontain
    obtain ⟨s, hrs⟩ := Nat.exists_eq_add_of_le hmin
    subst r
    rw [iidFourthIndicator_probability_length_independent
      (fourthEdgePairLength k) s k (fourthEdgePairLength_contains k)]
    exact hK k hk

end Erdos521
