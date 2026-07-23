import Research.GoodRecordReduction
import Research.FourthIntegratedCrossings
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos521

noncomputable local instance fourthMassGateDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

local instance fourthMassGateFairProbability : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

local instance fourthMassGateRademacherProbability :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- The number of fourth-integrated weak crossings on the two coefficient twists relevant to
both halves of `[-1,1]`, at the degree attached to cone-record time `n`. -/
noncomputable def twoSidedFourthCrossingCount (ω : ℕ → Bool) (n : ℕ) : ℕ :=
  fourthIntegratedCrossingCount ω (2 * n - 5) +
    fourthIntegratedCrossingCount (oddTwist ω) (2 * n - 5)

lemma measurable_twoSidedFourthCrossingCount (n : ℕ) :
    Measurable (fun ω : ℕ → Bool ↦ twoSidedFourthCrossingCount ω n) := by
  unfold twoSidedFourthCrossingCount
  exact (measurable_fourthIntegratedCrossingCount _).add
    ((measurable_fourthIntegratedCrossingCount _).comp measurePreserving_oddTwist.measurable)

/-- A cone record whose two fourth-integrated crossing counts, including the ten endpoint costs,
fit under the `3/5` local-root budget. -/
def lowFourthCrossingConeRecordEvent (n : ℕ) : Set (ℕ → Bool) :=
  coneRecordEvent n ∩
    {ω | (twoSidedFourthCrossingCount ω n : ℝ) + 10 ≤
      (3 : ℝ) / 5 * Real.log (recordDegree n : ℝ)}

lemma measurableSet_lowFourthCrossingConeRecordEvent (n : ℕ) :
    MeasurableSet (lowFourthCrossingConeRecordEvent n) := by
  have hmnat : Measurable (fun ω : ℕ → Bool ↦
      (twoSidedFourthCrossingCount ω n : ℝ)) :=
    (MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
      (measurable_twoSidedFourthCrossingCount n)
  exact (measurableSet_coneRecordEvent n).inter
    (measurableSet_le (hmnat.add_const 10) measurable_const)

lemma lowFourthCrossingConeRecordEvent_subset_lowRoot {n : ℕ} (hn : 3 ≤ n) :
    lowFourthCrossingConeRecordEvent n ⊆ lowRootConeRecordEvent n := by
  intro ω hω
  refine ⟨hω.1, ?_⟩
  have hdeg : recordDegree n = (2 * n - 5) + 4 := by
    unfold recordDegree
    omega
  have hright := rightRootCount_le_fourthIntegratedCrossingCount_add_five ω (2 * n - 5)
  have hleft0 := rightRootCount_le_fourthIntegratedCrossingCount_add_five
    (oddTwist ω) (2 * n - 5)
  rw [rightRootCount_oddTwist] at hleft0
  rw [← hdeg] at hright hleft0
  have hinner : innerRootCount ω (recordDegree n) ≤
      twoSidedFourthCrossingCount ω n + 10 := by
    rw [innerRootCount_eq_left_add_right]
    unfold twoSidedFourthCrossingCount
    omega
  have hlog : 0 < Real.log (recordDegree n : ℝ) := by
    apply Real.log_pos
    have : 1 < recordDegree n := by unfold recordDegree; omega
    exact_mod_cast this
  apply (div_le_iff₀ hlog).2
  have hcast : (innerRootCount ω (recordDegree n) : ℝ) ≤
      (twoSidedFourthCrossingCount ω n : ℝ) + 10 := by exact_mod_cast hinner
  calc
    (innerRootCount ω (recordDegree n) : ℝ) ≤
        (twoSidedFourthCrossingCount ω n : ℝ) + 10 := hcast
    _ ≤ (3 : ℝ) / 5 * Real.log (recordDegree n : ℝ) := hω.2

/-- Final analytic gate: it is enough that at least one percent of cone records eventually have
small two-sided fourth-integrated crossing count. -/
theorem erdos_521_negative_of_fourthCrossingRecord_mass
    (hmass : ∀ᶠ n : ℕ in atTop,
      coneRecordProbability n ≤
        100 * rademacherMeasure.real (lowFourthCrossingConeRecordEvent n)) :
    ¬ Claim := by
  apply erdos_521_negative_of_lowRootRecord_mass
  filter_upwards [hmass, eventually_ge_atTop (3 : ℕ)] with n hn hn3
  calc
    coneRecordProbability n ≤
        100 * rademacherMeasure.real (lowFourthCrossingConeRecordEvent n) := hn
    _ ≤ 100 * rademacherMeasure.real (lowRootConeRecordEvent n) := by
      exact mul_le_mul_of_nonneg_left
        (MeasureTheory.measureReal_mono (μ := rademacherMeasure)
          (lowFourthCrossingConeRecordEvent_subset_lowRoot hn3)) (by norm_num)

end Erdos521
