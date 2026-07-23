import Research.GoodRecordReduction
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos521

noncomputable local instance highRootGateDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

local instance highRootGateFairProbability : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

local instance highRootGateRademacherProbability : IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- Cone records with root ratio at most `0.63`, much closer to the conjectured `2/pi`. -/
def highThresholdLowRootConeRecordEvent (n : ℕ) : Set (ℕ → Bool) :=
  coneRecordEvent n ∩
    {ω | (innerRootCount ω (recordDegree n) : ℝ) /
      Real.log (recordDegree n : ℝ) ≤ (63 : ℝ) / 100}

lemma measurableSet_highThresholdLowRootConeRecordEvent (n : ℕ) :
    MeasurableSet (highThresholdLowRootConeRecordEvent n) := by
  exact (measurableSet_coneRecordEvent n).inter
    (measurableSet_le (measurable_innerRootRatio (recordDegree n)) measurable_const)

lemma highThresholdLowRootConeRecordEvent_subset (n : ℕ) :
    highThresholdLowRootConeRecordEvent n ⊆ coneRecordEvent n := inter_subset_left

lemma sixty_three_hundredths_lt_two_div_pi :
    (63 : ℝ) / 100 < 2 / Real.pi := by
  have hp := Real.pi_pos
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 100) hp).2
  nlinarith [Real.pi_lt_d20]

def paddedHighThresholdLowRootConeRecordEvent (K n : ℕ) : Set (ℕ → Bool) :=
  if n < K then coneRecordEvent n else highThresholdLowRootConeRecordEvent n

lemma measurableSet_paddedHighThresholdLowRootConeRecordEvent (K n : ℕ) :
    MeasurableSet (paddedHighThresholdLowRootConeRecordEvent K n) := by
  unfold paddedHighThresholdLowRootConeRecordEvent
  split_ifs
  · exact measurableSet_coneRecordEvent n
  · exact measurableSet_highThresholdLowRootConeRecordEvent n

lemma paddedHighThresholdLowRootConeRecordEvent_subset (K n : ℕ) :
    paddedHighThresholdLowRootConeRecordEvent K n ⊆ coneRecordEvent n := by
  unfold paddedHighThresholdLowRootConeRecordEvent
  split_ifs
  · exact Subset.rfl
  · exact highThresholdLowRootConeRecordEvent_subset n

/-- One percent eventual relative mass at root ratio `0.63` disproves the claimed `2/pi` limit. -/
theorem erdos_521_negative_of_highThresholdLowRootRecord_mass
    (hmass : ∀ᶠ n : ℕ in atTop,
      coneRecordProbability n ≤
        100 * rademacherMeasure.real (highThresholdLowRootConeRecordEvent n)) :
    ¬ Claim := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hmass
  let G := paddedHighThresholdLowRootConeRecordEvent K
  have hGall : ∀ n, coneRecordProbability n ≤
      100 * rademacherMeasure.real (G n) := by
    intro n
    by_cases hn : n < K
    · change coneRecordProbability n ≤
        100 * rademacherMeasure.real (paddedHighThresholdLowRootConeRecordEvent K n)
      rw [paddedHighThresholdLowRootConeRecordEvent, if_pos hn]
      change coneRecordProbability n ≤ 100 * coneRecordProbability n
      nlinarith [coneRecordProbability_nonneg n]
    · change coneRecordProbability n ≤
        100 * rademacherMeasure.real (paddedHighThresholdLowRootConeRecordEvent K n)
      rw [paddedHighThresholdLowRootConeRecordEvent, if_neg hn]
      exact hK n (Nat.le_of_not_gt hn)
  have hpositive : 0 < rademacherMeasure (eventLimsup G) :=
    positive_eventLimsup_record_subevents
      (fun n ↦ measurableSet_paddedHighThresholdLowRootConeRecordEvent K n)
      (fun n ↦ paddedHighThresholdLowRootConeRecordEvent_subset K n)
      hGall coneRecordPartialSums_tendsto_atTop
  intro hclaim
  obtain ⟨ω, hωG, hωlim⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpositive.ne'
      (ae_restrict_of_ae hclaim)
  have hlarge : ∀ᶠ d : ℕ in atTop,
      (63 : ℝ) / 100 < (realRootCount ω d : ℝ) / Real.log (d : ℝ) :=
    hωlim.eventually (Ioi_mem_nhds sixty_three_hundredths_lt_two_div_pi)
  obtain ⟨L, hL⟩ := eventually_atTop.1 hlarge
  have htail := Set.mem_iInter.mp hωG (max K (L + 1))
  simp only [eventTail, Set.mem_iUnion] at htail
  obtain ⟨n, hn, hnG⟩ := htail
  have hnK : K ≤ n := (le_max_left K (L + 1)).trans hn
  have hnL : L + 1 ≤ n := (le_max_right K (L + 1)).trans hn
  have hnpos : 0 < n := by omega
  have hnlow : ω ∈ highThresholdLowRootConeRecordEvent n := by
    change ω ∈ paddedHighThresholdLowRootConeRecordEvent K n at hnG
    rw [paddedHighThresholdLowRootConeRecordEvent,
      if_neg (Nat.not_lt.mpr hnK)] at hnG
    exact hnG
  let m := n - 1
  have hmn : m + 1 = n := by dsimp [m]; omega
  have hdeg : 2 * m + 1 = recordDegree n := by dsimp [m, recordDegree]; omega
  have hrec : IsConeRecord (rademacherIncrement ω) (m + 1) := by
    rw [hmn]
    exact hnlow.1
  have heq : innerRootCount ω (recordDegree n) = realRootCount ω (recordDegree n) := by
    rw [← hdeg]
    exact coneRecord_innerRootCount_eq hrec
  have hdegreeL : L ≤ recordDegree n := by dsimp [recordDegree]; omega
  have hhigh := hL (recordDegree n) hdegreeL
  have hlow := hnlow.2
  change (innerRootCount ω (recordDegree n) : ℝ) /
      Real.log (recordDegree n : ℝ) ≤ (63 : ℝ) / 100 at hlow
  rw [heq] at hlow
  linarith

end Erdos521
