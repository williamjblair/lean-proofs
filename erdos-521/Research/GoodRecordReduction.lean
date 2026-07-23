import Research.RecordSubeventRecurrence
import Research.RootCountMeasurable
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos521

noncomputable local instance goodRecordDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

local instance goodRecordFairProbability : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

local instance goodRecordRademacherProbability :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- The odd polynomial degree associated to paired-walk record time `n` (with harmless
natural-number totalization at `n=0`). -/
def recordDegree (n : ℕ) : ℕ := 2 * n - 1

lemma measurable_innerRootRatio (n : ℕ) :
    Measurable (fun ω : ℕ → Bool ↦
      (innerRootCount ω n : ℝ) / Real.log (n : ℝ)) := by
  rw [show (fun ω : ℕ → Bool ↦
      (innerRootCount ω n : ℝ) / Real.log (n : ℝ)) =
      fun ω ↦ ((leftRootCount ω n + rightRootCount ω n : ℕ) : ℝ) /
        Real.log (n : ℝ) by
    funext ω
    rw [innerRootCount_eq_left_add_right]]
  exact ((MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
    ((measurable_leftRootCount n).add (measurable_rightRootCount n))).div_const _

/-- A cone record whose associated polynomial already has a local-root ratio at most `3/5`. -/
def lowRootConeRecordEvent (n : ℕ) : Set (ℕ → Bool) :=
  coneRecordEvent n ∩
    {ω | (innerRootCount ω (recordDegree n) : ℝ) /
      Real.log ((recordDegree n : ℕ) : ℝ) ≤ (3 : ℝ) / 5}

lemma measurableSet_lowRootConeRecordEvent (n : ℕ) :
    MeasurableSet (lowRootConeRecordEvent n) := by
  exact (measurableSet_coneRecordEvent n).inter
    (measurableSet_le (measurable_innerRootRatio (recordDegree n)) measurable_const)

lemma lowRootConeRecordEvent_subset (n : ℕ) :
    lowRootConeRecordEvent n ⊆ coneRecordEvent n := inter_subset_left

/-- Pad finitely many early indices by the full record event, so an eventual relative-mass bound
can be fed directly to F-036. -/
def paddedLowRootConeRecordEvent (K n : ℕ) : Set (ℕ → Bool) :=
  if n < K then coneRecordEvent n else lowRootConeRecordEvent n

lemma measurableSet_paddedLowRootConeRecordEvent (K n : ℕ) :
    MeasurableSet (paddedLowRootConeRecordEvent K n) := by
  unfold paddedLowRootConeRecordEvent
  split_ifs
  · exact measurableSet_coneRecordEvent n
  · exact measurableSet_lowRootConeRecordEvent n

lemma paddedLowRootConeRecordEvent_subset (K n : ℕ) :
    paddedLowRootConeRecordEvent K n ⊆ coneRecordEvent n := by
  unfold paddedLowRootConeRecordEvent
  split_ifs
  · exact Subset.rfl
  · exact lowRootConeRecordEvent_subset n

lemma three_fifths_lt_two_div_pi' : (3 : ℝ) / 5 < 2 / Real.pi := by
  have hp := Real.pi_pos
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 5) hp).2
  have hpi := Real.pi_lt_d20
  norm_num at hpi ⊢
  linarith

/-- It is enough that, eventually, at least one percent of the cone-record mass consists of
records with local-root ratio at most `3/5`.  This conditional positive-density gate requires no
almost-sure local strong law and no concentration across degrees. -/
theorem erdos_521_negative_of_lowRootRecord_mass
    (hmass : ∀ᶠ n : ℕ in atTop,
      coneRecordProbability n ≤
        100 * rademacherMeasure.real (lowRootConeRecordEvent n)) :
    ¬ Claim := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hmass
  let G := paddedLowRootConeRecordEvent K
  have hGall : ∀ n, coneRecordProbability n ≤
      100 * rademacherMeasure.real (G n) := by
    intro n
    by_cases hn : n < K
    · change coneRecordProbability n ≤
        100 * rademacherMeasure.real (paddedLowRootConeRecordEvent K n)
      rw [paddedLowRootConeRecordEvent, if_pos hn]
      change coneRecordProbability n ≤ 100 * coneRecordProbability n
      have hq := coneRecordProbability_nonneg n
      nlinarith
    · change coneRecordProbability n ≤
        100 * rademacherMeasure.real (paddedLowRootConeRecordEvent K n)
      rw [paddedLowRootConeRecordEvent, if_neg hn]
      exact hK n (Nat.le_of_not_gt hn)
  have hpositive : 0 < rademacherMeasure (eventLimsup G) :=
    positive_eventLimsup_record_subevents
      (fun n ↦ measurableSet_paddedLowRootConeRecordEvent K n)
      (fun n ↦ paddedLowRootConeRecordEvent_subset K n)
      hGall coneRecordPartialSums_tendsto_atTop
  intro hclaim
  obtain ⟨ω, hωG, hωlim⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpositive.ne'
      (ae_restrict_of_ae hclaim)
  have hlarge : ∀ᶠ d : ℕ in atTop,
      (3 : ℝ) / 5 < (realRootCount ω d : ℝ) / Real.log (d : ℝ) :=
    hωlim.eventually (Ioi_mem_nhds three_fifths_lt_two_div_pi')
  obtain ⟨L, hL⟩ := eventually_atTop.1 hlarge
  have htail := Set.mem_iInter.mp hωG (max K (L + 1))
  simp only [eventTail, Set.mem_iUnion] at htail
  obtain ⟨n, hn, hnG⟩ := htail
  have hnK : K ≤ n := (le_max_left K (L + 1)).trans hn
  have hnL : L + 1 ≤ n := (le_max_right K (L + 1)).trans hn
  have hnpos : 0 < n := by omega
  have hnlow : ω ∈ lowRootConeRecordEvent n := by
    change ω ∈ paddedLowRootConeRecordEvent K n at hnG
    rw [paddedLowRootConeRecordEvent, if_neg (Nat.not_lt.mpr hnK)] at hnG
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
  have hdegreeL : L ≤ recordDegree n := by
    dsimp [recordDegree]
    omega
  have hhigh := hL (recordDegree n) hdegreeL
  have hlow := hnlow.2
  change (innerRootCount ω (recordDegree n) : ℝ) /
      Real.log ((recordDegree n : ℕ) : ℝ) ≤ (3 : ℝ) / 5 at hlow
  rw [heq] at hlow
  linarith

end Erdos521
