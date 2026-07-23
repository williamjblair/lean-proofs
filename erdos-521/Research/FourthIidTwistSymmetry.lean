import Research.FourthIidLengthIndependence

open scoped BigOperators

namespace Erdos521

noncomputable local instance fourthTwistDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def finiteOddTwist {m : ℕ} (x : Fin m → Bool) : Fin m → Bool :=
  fun i ↦ if Even i.val then x i else !(x i)

lemma finiteOddTwist_involution {m : ℕ} (x : Fin m → Bool) :
    finiteOddTwist (finiteOddTwist x) = x := by
  funext i
  by_cases hi : Even i.val <;> simp [finiteOddTwist, hi]

noncomputable def finiteOddTwistEquiv (m : ℕ) : (Fin m → Bool) ≃ (Fin m → Bool) where
  toFun := finiteOddTwist
  invFun := finiteOddTwist
  left_inv := finiteOddTwist_involution
  right_inv := finiteOddTwist_involution

lemma extendBits_finiteOddTwist {r : ℕ} (x : Fin (2 * r) → Bool) (i : ℕ)
    (hi : i < 2 * r) :
    extendBits r (finiteOddTwist x) i = oddTwist (extendBits r x) i := by
  rw [extendBits_of_lt _ hi]
  unfold finiteOddTwist oddTwist
  rw [extendBits_of_lt _ hi]

lemma fourthIndicator_twist_finite {r k : ℕ} (x : Fin (2 * r) → Bool)
    (hk : k + 2 ≤ 2 * r) :
    fourthIntegratedCrossingIndicator
        (oddTwist (extendBits r (finiteOddTwist x))) k =
      fourthIntegratedCrossingIndicator (extendBits r x) k := by
  apply fourthIndicator_congr_prefix
  intro i hi
  rw [← extendBits_finiteOddTwist (finiteOddTwist x) i (by omega),
    finiteOddTwist_involution]

lemma sum_fourthIndicator_oddTwist_eq (r k : ℕ) (hk : k + 2 ≤ 2 * r) :
    (∑ x : Fin (2 * r) → Bool,
        (fourthIntegratedCrossingIndicator (oddTwist (extendBits r x)) k : ℝ)) =
      ∑ x : Fin (2 * r) → Bool,
        (fourthIntegratedCrossingIndicator (extendBits r x) k : ℝ) := by
  calc
    _ = ∑ x : Fin (2 * r) → Bool,
        (fourthIntegratedCrossingIndicator
          (oddTwist (extendBits r (finiteOddTwistEquiv (2 * r) x))) k : ℝ) := by
      symm
      exact Equiv.sum_comp (finiteOddTwistEquiv (2 * r))
        (fun x ↦ (fourthIntegratedCrossingIndicator (oddTwist (extendBits r x)) k : ℝ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      change (fourthIntegratedCrossingIndicator
        (oddTwist (extendBits r (finiteOddTwist x))) k : ℝ) = _
      rw [fourthIndicator_twist_finite x hk]

/-- Under iid signs the original and odd-twisted edge indicators have exactly equal finite sums. -/
lemma sum_twoSidedFourthIndicator_eq_two_mul (r k : ℕ) (hk : k + 2 ≤ 2 * r) :
    (∑ w : AxisWord r, (terminalTwoSidedFourthIndicator w k : ℝ)) =
      2 * ∑ x : Fin (2 * r) → Bool,
        (fourthIntegratedCrossingIndicator (extendBits r x) k : ℝ) := by
  rw [sum_axisWord_indicator_eq_bits]
  simp_rw [bitsTwoSidedFourthIndicator]
  push_cast
  rw [Finset.sum_add_distrib, sum_fourthIndicator_oddTwist_eq r k hk]
  ring

/-- F-055/F-056's minimal local target is equivalently a one-sided cardinal estimate with constant
`0.24/(k+1)`. -/
def IidFourthMinimalOneSidedRate : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    (∑ x : Fin (2 * fourthEdgePairLength k) → Bool,
        (fourthIntegratedCrossingIndicator
          (extendBits (fourthEdgePairLength k) x) k : ℝ)) /
        (2 : ℝ) ^ (2 * fourthEdgePairLength k) ≤
      (6 : ℝ) / (25 * (k + 1 : ℝ))

lemma iidFourthMinimalRate_iff_oneSided :
    IidFourthMinimalRate ↔ IidFourthMinimalOneSidedRate := by
  constructor <;> rintro ⟨K, hK⟩ <;> refine ⟨K, fun k hk ↦ ?_⟩
  · have h := hK k hk
    rw [sum_twoSidedFourthIndicator_eq_two_mul _ _ (fourthEdgePairLength_contains k)] at h
    rw [show (4 : ℝ) ^ fourthEdgePairLength k =
        (2 : ℝ) ^ (2 * fourthEdgePairLength k) by rw [pow_mul]; norm_num] at h
    have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * fourthEdgePairLength k) := by positivity
    field_simp at h ⊢
    nlinarith
  · have h := hK k hk
    rw [sum_twoSidedFourthIndicator_eq_two_mul _ _ (fourthEdgePairLength_contains k)]
    rw [show (4 : ℝ) ^ fourthEdgePairLength k =
        (2 : ℝ) ^ (2 * fourthEdgePairLength k) by rw [pow_mul]; norm_num]
    have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * fourthEdgePairLength k) := by positivity
    field_simp at h ⊢
    nlinarith

end Erdos521
