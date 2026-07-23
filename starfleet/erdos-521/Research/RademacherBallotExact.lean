import Research.RademacherBallot
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped BigOperators

namespace Erdos521

noncomputable local instance rademacherBallotExactDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma coneTransform_nonneg_of_inCone {z : ℝ × ℝ} (h : InCone z) :
    0 ≤ (coneTransform z).1 ∧ 0 ≤ (coneTransform z).2 := by
  rw [InCone, abs_le] at h
  change 0 ≤ z.1 + z.2 ∧ 0 ≤ z.1 - z.2
  constructor <;> linarith

lemma prefix_sign_nonneg_iff_false_card {α : Type*} [DecidableEq α]
    (A : Finset α) (S : α → Bool) :
    0 ≤ ∑ i ∈ A, sign (S i) ↔
      2 * (A.filter (fun i ↦ S i = false)).card ≤ A.card := by
  rw [sum_sign_eq_card_sub_false]
  constructor
  · intro h
    have hr : (2 * (A.filter (fun i ↦ S i = false)).card : ℝ) ≤ (A.card : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hr
  · intro h
    have hr : (2 * (A.filter (fun i ↦ S i = false)).card : ℝ) ≤ (A.card : ℝ) := by
      exact_mod_cast h
    push_cast at hr ⊢
    linarith

lemma filter_before_rank_card {n : ℕ} (A : Finset (Fin n)) (q : ℕ) (hq : q ≤ A.card) :
    ∃ t ≤ n, (A.filter (fun j ↦ j.val < t)).card = q := by
  by_cases heq : q = A.card
  · refine ⟨n, le_rfl, ?_⟩
    simpa [heq] using A.filter_true_of_mem (fun j hj ↦ j.isLt)
  · have hlt : q < A.card := lt_of_le_of_ne hq heq
    let j : Fin A.card := ⟨q, hlt⟩
    refine ⟨(A.orderEmbOfFin rfl j).val, (A.orderEmbOfFin rfl j).isLt.le, ?_⟩
    simpa [j] using card_filter_lt_orderEmb A j

lemma axisGood_of_finiteAxisWalk_nonneg {n : ℕ} {H : Finset (Fin n)} {S : Fin n → Bool}
    (h : ∀ t ≤ n, 0 ≤ (finiteAxisWalk H S t).1 ∧ 0 ≤ (finiteAxisWalk H S t).2) :
    AxisGood H S := by
  rw [AxisGood]
  constructor
  · rw [scheduleDownEquiv_fst_eq]
    intro q hq
    obtain ⟨t, htle, ht⟩ := filter_before_rank_card H q hq
    have hn := (h t htle).1
    rw [finiteAxisWalk_fst] at hn
    have hs : 0 ≤ ∑ j ∈ H.filter (fun j ↦ j.val < t), sign (S j) := by linarith
    rw [prefix_sign_nonneg_iff_false_card] at hs
    rw [← ht, downPrefix_compressedDown]
    exact hs
  · rw [scheduleDownEquiv_snd_eq]
    intro q hq
    obtain ⟨t, htle, ht⟩ := filter_before_rank_card Hᶜ q hq
    have hn := (h t htle).2
    rw [finiteAxisWalk_snd] at hn
    have hs : 0 ≤ ∑ j ∈ (Hᶜ).filter (fun j ↦ j.val < t), sign (S j) := by linarith
    rw [prefix_sign_nonneg_iff_false_card] at hs
    rw [← ht, downPrefix_compressedDown]
    exact hs

lemma coneRecord_implies_axisGood {n : ℕ} (x : Fin (2 * n) → Bool)
    (hrec : IsConeRecord (rademacherIncrement (extendBits n x)) n) :
    AxisGood (bitsAxisEquiv n x).1 (bitsAxisEquiv n x).2 := by
  apply axisGood_of_finiteAxisWalk_nonneg
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hzero : pathPrefix n 0 = ∅ := by ext j; simp [mem_pathPrefix]
    simp [finiteAxisWalk, hzero]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    let m := n - 1
    let r := t - 1
    have hrm : r ≤ m := by omega
    have hwalk := walk_sub_eq_reverse_suffix
      (rademacherIncrement (extendBits n x)) (m := m) (r := r) hrm
    have hmn : m + 1 = n := by omega
    have hmk : m - r = n - t := by omega
    have hrt : r + 1 = t := by omega
    rw [hmn, hmk, hrt] at hwalk
    have hk : n - t < n := by omega
    have hcone := hrec (n - t) hk
    rw [hwalk] at hcone
    have hnonneg := coneTransform_nonneg_of_inCone hcone
    rw [coneTransform_reverse_sum_eq_axisWalk x ht] at hnonneg
    exact hnonneg

lemma coneRecord_extend_iff_axisGood {n : ℕ} (x : Fin (2 * n) → Bool) :
    IsConeRecord (rademacherIncrement (extendBits n x)) n ↔
      AxisGood (bitsAxisEquiv n x).1 (bitsAxisEquiv n x).2 :=
  ⟨coneRecord_implies_axisGood x, axisGood_implies_coneRecord x⟩

/-- Reindex a bit assignment on `Fin (2n)` as an assignment on the coordinate finset
`range (2n)`. -/
def rangeBitsEquiv (n : ℕ) :
    (Fin (2 * n) → Bool) ≃ ((Finset.range (2 * n) : Finset ℕ) → Bool) where
  toFun := bitsToRangePrefix
  invFun y j := y ⟨j.val, Finset.mem_range.mpr j.isLt⟩
  left_inv x := by funext j; rfl
  right_inv y := by funext j; apply congrArg y; exact Subtype.ext rfl

/-- Good finite coefficient strings are exactly good axis paths. -/
def goodBitsEquivAxisGoodPath (n : ℕ) :
    {x : Fin (2 * n) → Bool // AxisGood (bitsAxisEquiv n x).1 (bitsAxisEquiv n x).2} ≃
      AxisGoodPath n where
  toFun x := ⟨bitsAxisEquiv n x.1, x.property⟩
  invFun p := ⟨(bitsAxisEquiv n).symm p.1, by
    simpa using p.property⟩
  left_inv x := by apply Subtype.ext; exact (bitsAxisEquiv n).symm_apply_apply x.1
  right_inv p := by apply Subtype.ext; exact (bitsAxisEquiv n).apply_symm_apply p.1

lemma recordPrefixImage_eq_goodBits_image (n : ℕ) :
    (fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
        coneRecordEvent n =
      rangeBitsEquiv n ''
        {x : Fin (2 * n) → Bool |
          AxisGood (bitsAxisEquiv n x).1 (bitsAxisEquiv n x).2} := by
  ext y
  constructor
  · rintro ⟨ω, hrec, rfl⟩
    let x : Fin (2 * n) → Bool := fun j ↦ ω j.val
    refine ⟨x, ?_, ?_⟩
    · apply (coneRecord_extend_iff_axisGood x).mp
      apply (isConeRecord_iff_of_prefix (ω := extendBits n x) (η := ω) ?_).mpr hrec
      intro k hk
      simp [x, extendBits, hk]
    · funext i
      rfl
  · rintro ⟨x, hgood, rfl⟩
    refine ⟨extendBits n x, ?_, ?_⟩
    · exact (coneRecord_extend_iff_axisGood x).mpr hgood
    · funext i
      exact extendBits_of_lt x (Finset.mem_range.mp i.property)

lemma card_recordPrefixImage_eq (n : ℕ) :
    ((fun (ω : ℕ → Bool) (i : (Finset.range (2 * n) : Finset ℕ)) ↦ ω i) ''
        coneRecordEvent n).ncard = Fintype.card (AxisGoodPath n) := by
  rw [recordPrefixImage_eq_goodBits_image,
    Set.ncard_image_of_injective _ (rangeBitsEquiv n).injective]
  change Nat.card
      {x : Fin (2 * n) → Bool //
        AxisGood (bitsAxisEquiv n x).1 (bitsAxisEquiv n x).2} = _
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (goodBitsEquivAxisGoodPath n)]

/-- The cone-record probability is exactly the quadrant-survival fraction, not merely bounded
below by it. -/
lemma coneRecordProbability_eq_axisGood_ratio (n : ℕ) :
    coneRecordProbability n =
      (Fintype.card (AxisGoodPath n) : ℝ) / (4 : ℝ) ^ n := by
  rw [coneRecordProbability_eq_prefixCard, card_recordPrefixImage_eq]

end Erdos521
