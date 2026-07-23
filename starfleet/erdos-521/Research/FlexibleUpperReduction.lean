import Research.OneSidedReduction
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Erdos521

/-- Any eventual almost-sure local-root upper bound strictly below `2/π` contradicts the proposed
total-root limit once recurrent cone records are available. -/
theorem erdos_521_negative_of_eventual_local_upper {c : ℝ}
    (hc : c < (2 : ℝ) / Real.pi)
    (hlocal : ∀ᵐ ω ∂rademacherMeasure,
      ∀ᶠ n : ℕ in atTop,
        (innerRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ c) :
    ¬ Claim := by
  intro hclaim
  have hboth : ∀ᵐ ω ∂rademacherMeasure,
      Tendsto (fun n : ℕ ↦ (realRootCount ω n : ℝ) / Real.log (n : ℝ))
          atTop (𝓝 ((2 : ℝ) / Real.pi)) ∧
      (∀ᶠ n : ℕ in atTop,
        (innerRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ c) :=
    hclaim.and hlocal
  obtain ⟨ω, hωrec, htotal, hupper⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae positive_infinitelyOftenConeRecords.ne'
      (ae_restrict_of_ae hboth)
  have hlower : ∀ᶠ n : ℕ in atTop,
      c < (realRootCount ω n : ℝ) / Real.log (n : ℝ) :=
    htotal.eventually (Ioi_mem_nhds hc)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hupper.and hlower)
  obtain ⟨m, hmN, hmrec⟩ := hωrec N
  have hmdeg : N ≤ 2 * m + 1 := by omega
  have hinner_m := (hN (2 * m + 1) hmdeg).1
  have htotal_m := (hN (2 * m + 1) hmdeg).2
  rw [← coneRecord_innerRootCount_eq hmrec] at htotal_m
  linarith

lemma left_eventual_upper_of_right_eventual_upper {c : ℝ}
    (h : ∀ᵐ ω ∂rademacherMeasure,
      ∀ᶠ n : ℕ in atTop,
        (rightRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ c) :
    ∀ᵐ ω ∂rademacherMeasure,
      ∀ᶠ n : ℕ in atTop,
        (leftRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ c := by
  have htend : Tendsto oddTwist (ae rademacherMeasure) (ae rademacherMeasure) := by
    simpa only [measurePreserving_oddTwist.map_eq] using
      Measure.tendsto_ae_map measurePreserving_oddTwist.aemeasurable
  filter_upwards [htend.eventually h] with ω hω
  filter_upwards [hω] with n hn
  simpa only [rightRootCount_oddTwist] using hn

/-- A much looser one-sided analytic target than F-021: `0.3` per side still leaves the total
constant `0.6` strictly below `2/π`. -/
def RightUpperThreeTenths : Prop :=
  ∀ᵐ ω ∂rademacherMeasure,
    ∀ᶠ n : ℕ in atTop,
      (rightRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ (3 : ℝ) / 10

lemma local_three_fifths_of_right_three_tenths (h : RightUpperThreeTenths) :
    ∀ᵐ ω ∂rademacherMeasure,
      ∀ᶠ n : ℕ in atTop,
        (innerRootCount ω n : ℝ) / Real.log (n : ℝ) ≤ (3 : ℝ) / 5 := by
  have hleft := left_eventual_upper_of_right_eventual_upper h
  filter_upwards [h, hleft] with ω hright hleftω
  filter_upwards [hright, hleftω] with n hr hl
  rw [innerRootCount_eq_left_add_right]
  push_cast
  rw [add_div]
  linarith

lemma three_fifths_lt_two_div_pi : (3 : ℝ) / 5 < 2 / Real.pi := by
  have hp := Real.pi_pos
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 5) hp).2
  have hpi := Real.pi_lt_d20
  norm_num at hpi ⊢
  linarith

/-- Proving the one-sided `0.3` bound is enough for the exact negative answer. -/
theorem erdos_521_negative_of_right_three_tenths (h : RightUpperThreeTenths) : ¬ Claim :=
  erdos_521_negative_of_eventual_local_upper three_fifths_lt_two_div_pi
    (local_three_fifths_of_right_three_tenths h)

end Erdos521
