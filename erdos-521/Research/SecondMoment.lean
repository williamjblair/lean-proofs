import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos521

section FiniteSecondMoment

variable {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- The finite union of a family of events. -/
def eventUnion (A : ι → Set Ω) (s : Finset ι) : Set Ω := ⋃ i ∈ s, A i

/-- Number (as a real) of events in `s` which occur at `ω`. -/
noncomputable def eventCount (A : ι → Set Ω) (s : Finset ι) (ω : Ω) : ℝ :=
  ∑ i ∈ s, (A i).indicator (fun _ ↦ (1 : ℝ)) ω

lemma measurableSet_eventUnion {A : ι → Set Ω} (s : Finset ι)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) : MeasurableSet (eventUnion A s) := by
  exact Finset.measurableSet_biUnion s hA

lemma measurable_eventCount {A : ι → Set Ω} (s : Finset ι)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) : Measurable (eventCount A s) := by
  apply Finset.measurable_fun_sum
  intro i hi
  exact measurable_const.indicator (hA i hi)

lemma eventCount_nonneg (A : ι → Set Ω) (s : Finset ι) (ω : Ω) :
    0 ≤ eventCount A s ω := by
  apply Finset.sum_nonneg
  intro i hi
  by_cases hω : ω ∈ A i <;> simp [eventCount, hω]

lemma eventCount_le_card (A : ι → Set Ω) (s : Finset ι) (ω : Ω) :
    eventCount A s ω ≤ s.card := by
  rw [eventCount]
  calc
    (∑ i ∈ s, (A i).indicator (fun _ ↦ (1 : ℝ)) ω) ≤ ∑ _i ∈ s, (1 : ℝ) := by
      gcongr with i hi
      by_cases hω : ω ∈ A i <;> simp [hω]
    _ = s.card := by simp

lemma integral_eventCount {A : ι → Set Ω} (s : Finset ι)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    ∫ ω, eventCount A s ω ∂μ = ∑ i ∈ s, μ.real (A i) := by
  change (∫ ω, ∑ i ∈ s, (A i).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) = _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_indicator_one (hA i hi)
  · intro i hi
    exact (integrable_const (1 : ℝ)).indicator (hA i hi)

lemma eventCount_sq (A : ι → Set Ω) (s : Finset ι) (ω : Ω) :
    eventCount A s ω ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).indicator (fun _ ↦ (1 : ℝ)) ω := by
  rw [eventCount, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hiω : ω ∈ A i <;> by_cases hjω : ω ∈ A j <;> simp [hiω, hjω]

lemma integral_eventCount_sq {A : ι → Set Ω} (s : Finset ι)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    ∫ ω, eventCount A s ω ^ 2 ∂μ =
      ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j) := by
  simp_rw [eventCount_sq A s]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact integral_indicator_one ((hA i hi).inter (hA j hj))
    · intro j hj
      exact (integrable_const (1 : ℝ)).indicator ((hA i hi).inter (hA j hj))
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (integrable_const (1 : ℝ)).indicator ((hA i hi).inter (hA j hj))

lemma eventUnion_indicator_mul_count (A : ι → Set Ω) (s : Finset ι) (ω : Ω) :
    (eventUnion A s).indicator (fun _ ↦ (1 : ℝ)) ω * eventCount A s ω =
      eventCount A s ω := by
  by_cases hω : ω ∈ eventUnion A s
  · simp [hω]
  · have hnone : ∀ i ∈ s, ω ∉ A i := by
      intro i hi hmem
      exact hω (Set.mem_iUnion₂.mpr ⟨i, hi, hmem⟩)
    rw [eventCount, Set.indicator_of_notMem hω]
    simp only [zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    simp [hnone i hi]

/-- Finite second-moment (Chung--Erdős) inequality for measurable events. -/
lemma finite_event_second_moment {A : ι → Set Ω} (s : Finset ι)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∑ i ∈ s, μ.real (A i)) ^ 2 ≤
      μ.real (eventUnion A s) *
        (∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)) := by
  let U : Ω → ℝ := (eventUnion A s).indicator (fun _ ↦ (1 : ℝ))
  let X : Ω → ℝ := eventCount A s
  have hUm : Measurable U := measurable_const.indicator (measurableSet_eventUnion s hA)
  have hXm : Measurable X := measurable_eventCount s hA
  have hUmem : MemLp U (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hUm.aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ by
      by_cases hω : ω ∈ eventUnion A s <;> simp [U, hω])
  have hXmem : MemLp X (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hXm.aestronglyMeasurable (s.card : ℝ) (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (eventCount_nonneg A s ω)]
      exact_mod_cast eventCount_le_card A s ω)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun ω ↦ by
      by_cases hω : ω ∈ eventUnion A s <;> simp [U, hω] : 0 ≤ᵐ[μ] U)
    (ae_of_all _ fun ω ↦ eventCount_nonneg A s ω : 0 ≤ᵐ[μ] X) hUmem hXmem
  have hmul : (fun ω ↦ U ω * X ω) = X := by
    funext ω
    exact eventUnion_indicator_mul_count A s ω
  rw [hmul] at hholder
  have hUint : ∫ ω, U ω ^ (2 : ℝ) ∂μ = μ.real (eventUnion A s) := by
    have hpow : (fun ω ↦ U ω ^ (2 : ℝ)) = U := by
      funext ω
      by_cases hω : ω ∈ eventUnion A s <;> simp [U, hω]
    rw [hpow]
    exact integral_indicator_one (measurableSet_eventUnion s hA)
  have hXint : ∫ ω, X ω ^ (2 : ℝ) ∂μ =
      ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j) := by
    have hpow : (fun ω ↦ X ω ^ (2 : ℝ)) = fun ω ↦ X ω ^ (2 : ℕ) := by
      funext ω
      exact Real.rpow_two (X ω)
    rw [hpow]
    exact integral_eventCount_sq μ s hA
  have hU0 : 0 ≤ μ.real (eventUnion A s) := measureReal_nonneg
  have hS0 : 0 ≤ ∑ i ∈ s, μ.real (A i) := by positivity
  have hD0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j) := by positivity
  rw [hUint, hXint, show (1 : ℝ) / 2 = 1 / (2 : ℝ) by norm_num,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  rw [integral_eventCount μ s hA] at hholder
  nlinarith [Real.sq_sqrt hU0, Real.sq_sqrt hD0,
    Real.sqrt_nonneg (μ.real (eventUnion A s)),
    Real.sqrt_nonneg (∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j))]

end FiniteSecondMoment

end Erdos521
