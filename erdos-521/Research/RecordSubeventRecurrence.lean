import Research.RademacherRecurrence
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped BigOperators

namespace Erdos521

noncomputable local instance recordSubeventDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

local instance recordSubeventFairProbability : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

local instance recordSubeventRademacherProbability :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- Any measurable subevents carrying at least one percent of every cone-record mass recur on a
set of positive measure.  No correlation estimate for the subevents themselves is needed. -/
lemma positive_eventLimsup_record_subevents
    {G : ℕ → Set (ℕ → Bool)}
    (hG : ∀ n, MeasurableSet (G n))
    (hsub : ∀ n, G n ⊆ coneRecordEvent n)
    (hmass : ∀ n, coneRecordProbability n ≤
      100 * rademacherMeasure.real (G n))
    (hdiv : Tendsto
      (fun N ↦ ∑ i ∈ Finset.range (N + 1), coneRecordProbability i) atTop atTop) :
    0 < rademacherMeasure (eventLimsup G) := by
  apply kochenStone_of_finite_blocks rademacherMeasure hG (C := 50000) (by norm_num)
  intro K
  obtain ⟨N, hKN, hSq, hT⟩ :=
    tailLarge_of_partialSums_tendsto_atTop coneRecordProbability
      coneRecordProbability_nonneg hdiv K
  refine ⟨N, hKN, ?_⟩
  let s := Finset.Icc K N
  let Sg := ∑ i ∈ s, rademacherMeasure.real (G i)
  let Dg := ∑ i ∈ s, ∑ j ∈ s, rademacherMeasure.real (G i ∩ G j)
  let Sq := ∑ i ∈ s, coneRecordProbability i
  let Tq := ∑ i ∈ Finset.range (N + 1), coneRecordProbability i
  change 1 ≤ Sq at hSq
  change Tq ≤ 2 * Sq at hT
  have hSqSg : Sq ≤ 100 * Sg := by
    dsimp [Sq, Sg]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact hmass i
  have hDmono : Dg ≤
      ∑ i ∈ s, ∑ j ∈ s,
        rademacherMeasure.real (coneRecordEvent i ∩ coneRecordEvent j) := by
    dsimp [Dg]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact MeasureTheory.measureReal_mono (by
      intro ω hω
      exact ⟨hsub i hω.1, hsub j hω.2⟩) (by finiteness)
  have hrecord :
      (∑ i ∈ s, ∑ j ∈ s,
        rademacherMeasure.real (coneRecordEvent i ∩ coneRecordEvent j)) ≤
        Sq + 2 * Sq * Tq := by
    exact coneRecord_correlation_bound K N hKN
  have hSg0 : 0 ≤ Sg := by
    dsimp [Sg]
    exact Finset.sum_nonneg fun i hi ↦ measureReal_nonneg
  change 0 < Sg ∧ Dg ≤ 50000 * Sg ^ 2
  constructor
  · nlinarith
  · nlinarith

end Erdos521
