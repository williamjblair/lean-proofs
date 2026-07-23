import Research.AxisPathCylinder
import Research.HighThresholdRootGate
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos521

noncomputable local instance highFourthGateDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

local instance highFourthGateFairProbability : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

local instance highFourthGateRademacherProbability : IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

noncomputable def highThresholdFourthAxisPaths (n : ℕ) : Finset (AxisGoodPath n) :=
  Finset.univ.filter fun p ↦
    (axisFourthCrossingCount p : ℝ) + 10 ≤
      (63 : ℝ) / 100 * Real.log (recordDegree n : ℝ)

/-- The finite-prefix cylinder of cone paths passing the `0.63 log` fourth-crossing budget. -/
def highThresholdFourthCrossingConeRecordEvent (n : ℕ) : Set (ℕ → Bool) :=
  axisPathCylinder n (highThresholdFourthAxisPaths n)

lemma measurableSet_highThresholdFourthCrossingConeRecordEvent (n : ℕ) :
    MeasurableSet (highThresholdFourthCrossingConeRecordEvent n) :=
  measurableSet_axisPathCylinder n _

lemma highThresholdFourthCrossingConeRecordEvent_subset_cone (n : ℕ) :
    highThresholdFourthCrossingConeRecordEvent n ⊆ coneRecordEvent n :=
  axisPathCylinder_subset_coneRecord n _

lemma highThresholdFourthCrossingRecord_measure_eq (n : ℕ) :
    rademacherMeasure.real (highThresholdFourthCrossingConeRecordEvent n) =
      ((highThresholdFourthAxisPaths n).card : ℝ) / (4 : ℝ) ^ n :=
  axisPathCylinder_measure_eq n _

lemma highThresholdFourthCrossing_subset_lowRoot {n : ℕ} (hn : 3 ≤ n) :
    highThresholdFourthCrossingConeRecordEvent n ⊆
      highThresholdLowRootConeRecordEvent n := by
  intro ω hω
  obtain ⟨p, hp, heq⟩ :=
    (mem_axisPathCylinder_iff n (highThresholdFourthAxisPaths n) ω).mp hω
  have hcone := highThresholdFourthCrossingConeRecordEvent_subset_cone n hω
  refine ⟨hcone, ?_⟩
  have hcountEq : axisFourthCrossingCount p = twoSidedFourthCrossingCount ω n := by
    unfold axisFourthCrossingCount
    exact twoSidedFourthCrossingCount_eq_of_prefix hn heq
  have hpBudget : (axisFourthCrossingCount p : ℝ) + 10 ≤
      (63 : ℝ) / 100 * Real.log (recordDegree n : ℝ) := by
    simpa [highThresholdFourthAxisPaths] using hp
  have hdeg : recordDegree n = (2 * n - 5) + 4 := by
    unfold recordDegree
    omega
  have hright := rightRootCount_le_fourthIntegratedCrossingCount_add_five ω (2 * n - 5)
  have hleft := rightRootCount_le_fourthIntegratedCrossingCount_add_five
    (oddTwist ω) (2 * n - 5)
  rw [rightRootCount_oddTwist, ← hdeg] at hleft
  rw [← hdeg] at hright
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
    _ = (axisFourthCrossingCount p : ℝ) + 10 := by rw [hcountEq]
    _ ≤ (63 : ℝ) / 100 * Real.log (recordDegree n : ℝ) := hpBudget

/-- One percent relative mass of the high-threshold crossing cylinder proves `not Claim`. -/
theorem erdos_521_negative_of_highThresholdFourthCrossing_mass
    (hmass : ∀ᶠ n : ℕ in atTop,
      coneRecordProbability n ≤
        100 * rademacherMeasure.real (highThresholdFourthCrossingConeRecordEvent n)) :
    ¬ Claim := by
  apply erdos_521_negative_of_highThresholdLowRootRecord_mass
  filter_upwards [hmass, eventually_ge_atTop (3 : ℕ)] with n hn hn3
  calc
    coneRecordProbability n ≤
        100 * rademacherMeasure.real (highThresholdFourthCrossingConeRecordEvent n) := hn
    _ ≤ 100 * rademacherMeasure.real (highThresholdLowRootConeRecordEvent n) := by
      exact mul_le_mul_of_nonneg_left
        (MeasureTheory.measureReal_mono (μ := rademacherMeasure)
          (highThresholdFourthCrossing_subset_lowRoot hn3)) (by norm_num)

end Erdos521
